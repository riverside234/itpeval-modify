"""Resolve bounded, pinned HOL Light loads in declaration order."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path, PurePosixPath
import re

from ..most_match_pipeline.common import fingerprint, repo_path
from .contracts import ContextConfig, SelectionFailure
from .source_index import Binding, SourceView, _index_files, read_pinned_source

LOAD_PATH = re.compile(r"(?:[A-Za-z0-9_][A-Za-z0-9_.-]*/)*[A-Za-z0-9_][A-Za-z0-9_.-]*\.ml")
SHA256 = re.compile(r"[0-9a-f]{64}")


def logical_path(value):
    if not isinstance(value, str):
        return None
    value = value.removeprefix("./")
    return value if LOAD_PATH.fullmatch(value) else None


def unique_keys(items):
    result = {}
    for name, value in items:
        if name in result:
            raise ValueError("duplicate key in HOL Light load manifest: " + name)
        result[name] = value
    return result


@dataclass(frozen=True)
class LoadFile:
    proof: Path
    proof_sha256: str
    statement: Path | None = None
    statement_sha256: str = ""


class LoadCatalog:
    """Read only exact manifest entries and reuse their parsed source within a run."""

    def __init__(self, config: ContextConfig):
        self.config = config
        path = repo_path(config.source_load_manifest)
        data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_keys)
        if (not isinstance(data, dict) or set(data) != {"version", "root", "files"}
                or type(data["version"]) is not int or data["version"] != 1
                or not isinstance(data["root"], str) or not isinstance(data["files"], dict)):
            raise ValueError("expected version, root and files in HOL Light load manifest")
        self.sha256 = fingerprint(data)
        self.repo = repo_path(".")
        root = repo_path(data["root"])
        self.files = {}
        self.loaded = {}
        for name, item in data["files"].items():
            if logical_path(name) != name or not isinstance(item, dict):
                raise ValueError("invalid HOL Light load manifest entry: " + name)
            required = {"proof", "proof_sha256"}
            if set(item) not in (required, required | {"statement", "statement_sha256"}):
                raise ValueError("invalid proof or statement fields in HOL Light load manifest: " + name)

            def checked(label):
                if (logical_path(item[label]) != item[label] or not isinstance(item[label], str)
                        or not isinstance(item[label + "_sha256"], str)
                        or not SHA256.fullmatch(item[label + "_sha256"])):
                    raise ValueError(f"expected a relative .ml path and SHA-256 for {name} {label}")
                path = repo_path(root / item[label])
                if not path.is_relative_to(root):
                    raise ValueError("HOL Light load manifest path escapes its root: " + name)
                return path, item[label + "_sha256"]

            proof, proof_sha = checked("proof")
            statement, statement_sha = checked("statement") if "statement" in item else (None, "")
            self.files[name] = LoadFile(proof, proof_sha, statement, statement_sha)

    def source(self, entry):
        if entry not in self.loaded:
            proof = read_pinned_source(entry.proof, self.config.max_source_chars, entry.proof_sha256)
            masked = read_pinned_source(entry.statement, self.config.max_source_chars, entry.statement_sha256) \
                if entry.statement is not None else ""
            index, snippets = _index_files(proof, masked, self.config)
            self.loaded[entry] = SourceView(
                index, None, entry.proof.relative_to(self.repo).as_posix(),
                entry.statement.relative_to(self.repo).as_posix() if entry.statement is not None else "",
                entry.proof_sha256, entry.statement_sha256, snippets)
        return self.loaded[entry]


@dataclass(frozen=True)
class Location:
    source: SourceView
    binding: Binding
    scope: int | None = None

    @property
    def identity(self):
        origin = self.source.identity(self.binding)
        # A forced reload can capture different earlier bindings.
        return origin if self.scope is None else fingerprint([origin, self.scope])


@dataclass(frozen=True)
class Slice:
    source: SourceView
    start: int
    stop: int
    chain: tuple[str, ...]


class LoadTimeline:
    """Represent the static global environment as ordered slices of source files.

    A helper resolves its dependencies at its own declaration, so later loads
    and rebindings cannot change the meaning of an earlier proof or alias.
    """

    def __init__(self, source, catalog):
        self.catalog = catalog
        self.config = catalog.config
        self.slices = []
        self.loads = []
        self.attempted = set()
        self.completed = set()
        self.units = {source.proof_path: source}
        self._visit(source, source.root.start, (), (source.proof_sha256,))
        self.root = Location(source, source.root, len(self.slices) - 1)
        self.known = set().union(*(unit.index.bindings for unit in self.units.values()))

    def _visit(self, source, stop, chain, active):
        start = 0
        loads = [load for load in source.index.loads if load["offset"] < stop]
        for i, load in enumerate(loads):
            offset = load["offset"]
            if len(self.loads) >= self.config.max_load_directives:
                self.loads.append({"source_path": source.proof_path, "offset": offset,
                                   "load_chain": list(chain), "status": "load_directive_limit",
                                   "omitted_directives": len(loads) - i})
                break
            self.slices.append(Slice(source, start, offset, chain))
            self._load(source, load, chain, active)
            start = offset
        self.slices.append(Slice(source, start, stop, chain))

    def _load(self, source, load, chain, active):
        logical = logical_path(load["path"])
        event = {**load, "source_path": source.proof_path, "load_chain": [*chain, load["path"]]}
        self.loads.append(event)
        if logical is None:
            event["status"] = "unsupported_load_path" if load["path"] else "unsupported_load"
            return
        entry = self.catalog.files.get(logical)
        if entry is None:
            event["status"] = "unmapped_load"
            return
        event["resolved_path"] = entry.proof.relative_to(self.catalog.repo).as_posix()
        event["proof_sha256"] = entry.proof_sha256
        identity = (PurePosixPath(logical).name, entry.proof_sha256)
        if load["command"] == "needs" and identity in self.completed:
            event["status"] = "already_loaded"
            return
        if entry.proof_sha256 in active:
            event["status"] = "load_cycle"
            return
        if len(chain) >= self.config.max_load_depth:
            event["status"] = "load_depth_limit"
            return
        if entry not in self.attempted and len(self.attempted) >= self.config.max_load_files:
            event["status"] = "load_file_limit"
            return
        self.attempted.add(entry)
        try:
            unit = self.catalog.source(entry)
        except (OSError, ValueError) as exc:
            event["status"] = getattr(exc, "category",
                                      "source_unavailable" if isinstance(exc, OSError) else "unsupported_source")
            event["error"] = str(exc)[:400]
            return
        self.units[unit.proof_path] = unit
        event["status"] = "loaded"
        self._visit(unit, len(unit.index.text), (*chain, logical), (*active, unit.proof_sha256))
        self.completed.add(identity)

    def preceding(self, name, location):
        for scope in range(location.scope, -1, -1):
            part = self.slices[scope]
            end = location.binding.start if scope == location.scope else part.stop
            if end <= part.start:
                continue
            binding = part.source.index.preceding(name, end)
            if binding is not None and binding.start >= part.start:
                return Location(part.source, binding, scope)
        return None

    def provenance(self, location):
        part = self.slices[location.scope]
        return {"source_path": part.source.proof_path, "source_sha256": part.source.proof_sha256,
                "masked_path": part.source.statement_path or None,
                "masked_sha256": part.source.statement_sha256 or None,
                "load_chain": list(part.chain), "source_scope": location.scope}
