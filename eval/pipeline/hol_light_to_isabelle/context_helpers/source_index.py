"""Index explicit references in a pinned most-match HOL Light source file."""

from __future__ import annotations

from bisect import bisect_left
from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path, PurePosixPath

from ..hundred_theorems_pipeline.hol_syntax import phrases, prove_call, tokens
from ..most_match_pipeline.aligned_data import TOPICS
from ..most_match_pipeline.common import DATASET_ROOT, fingerprint, repo_path, sha256
from ..most_match_pipeline.context import source_snippets
from .contracts import ContextConfig, SelectionFailure

DEFINITION_CALLS = {"new_definition", "new_recursive_definition", "define"}
LOAD_CALLS = {"needs", "loadt", "loads"}


@dataclass(frozen=True)
class Binding:
    name: str
    start: int
    end: int
    kind: str
    statement: str = ""
    proof: str = ""
    alias: str = ""


class SourceIndex:
    def __init__(self, text: str, config: ContextConfig):
        self.text = text
        self.bindings = defaultdict(list)
        self.loads = []
        self.opaque_phrases = []
        if len(text) > config.max_source_chars:
            raise SelectionFailure("source_scan_limit", "HOL Light file exceeds max_source_chars")
        for number, phrase in enumerate(phrases(tokens(text)), 1):
            if number > config.max_source_phrases:
                raise SelectionFailure("source_scan_limit", "HOL Light file exceeds max_source_phrases")
            head = phrase[0]
            if head.text in LOAD_CALLS:
                literal = phrase[1].text[1:-1] if len(phrase) == 3 and phrase[1].kind == "string" else None
                self.loads.append({"command": head.text, "path": literal, "offset": head.start,
                                   "status": "unresolved_load" if literal else "unsupported_load"})
            if head.text != "let":
                continue
            equal = next((i for i, item in enumerate(phrase) if item.text == "="), None)
            if equal is None:
                self.opaque_phrases.append(head.start)
                continue
            lhs = phrase[1:equal]
            rhs = phrase[equal + 1:-1]
            end = phrase[-1].end
            if len(lhs) != 1 or lhs[0].kind != "word" or not rhs:
                self.opaque_phrases.append(head.start)
                # A pattern can shadow a prior binding. Treat its possible names as
                # opaque instead of resolving through it to an older declaration.
                names = [item.text for item in lhs if item.kind == "word" and item.text != "rec"]
                for name in dict.fromkeys(names):
                    self.bindings[name].append(Binding(name, head.start, end, "opaque"))
                continue
            name = lhs[0].text
            kind, statement, proof, alias = "opaque", "", "", ""
            if rhs[0].text == "prove":
                try:
                    term, comma, close = prove_call(phrase, equal + 1)
                except ValueError:
                    pass
                else:
                    if close == len(phrase) - 2:
                        statement = phrase[term].text[1:-1].strip()
                        proof = text[phrase[comma].end:phrase[close].start].strip()
                        if statement and proof:
                            kind = "theorem"
            elif rhs[0].text in DEFINITION_CALLS:
                kind = "definition"
            elif len(rhs) == 1 and rhs[0].kind == "word":
                kind, alias = "alias", rhs[0].text
            self.bindings[name].append(Binding(name, head.start, end, kind, statement, proof, alias))
        self.starts = {name: [binding.start for binding in group] for name, group in self.bindings.items()}

    def preceding(self, name, before):
        starts = self.starts.get(name, ())
        at = bisect_left(starts, before)
        return self.bindings[name][at - 1] if at else None

    def resolve(self, name, *, before, root):
        aliases = []
        seen = set()
        for _ in range(9):  # At most eight alias hops, regardless of traversal depth.
            if name == root.name:
                return None, "excluded_target", aliases
            binding = self.preceding(name, before)
            if binding is None:
                if name in seen:
                    return None, "cycle_or_forward_alias", aliases
                return None, "not_yet_bound" if name in self.bindings else "unresolved_reference", aliases
            if binding.kind != "alias":
                status = {"theorem": "resolved_alias" if aliases else "explicit_reference",
                          "definition": "definition_reference", "opaque": "unsupported_binding"}[binding.kind]
                return binding, status, aliases
            if len(aliases) == 8:
                break
            aliases.append(binding.name)
            seen.add(name)
            name, before = binding.alias, binding.start
        return None, "alias_limit", aliases

    def describe(self, binding):
        return {"name": binding.name, "span": [binding.start, binding.end], "kind": binding.kind,
                "declaration_sha256": sha256(self.text[binding.start:binding.end]),
                "statement_sha256": sha256(binding.statement),
                "proof_sha256": sha256(binding.proof)}


@dataclass(frozen=True)
class SourceView:
    index: SourceIndex
    root: Binding
    proof_path: str
    statement_path: str
    proof_sha256: str
    statement_sha256: str
    snippets: tuple

    def identity(self, binding):
        return fingerprint([self.proof_path, self.proof_sha256, binding.start, binding.end])


def _read_source(path: Path, max_chars: int, digest: str):
    if path.stat().st_size > max_chars * 4:
        raise SelectionFailure("source_scan_limit", f"source file exceeds the scan budget: {path.name}")
    text = path.read_text(encoding="utf-8")
    if len(text) > max_chars:
        raise SelectionFailure("source_scan_limit", f"source file exceeds the scan budget: {path.name}")
    if sha256(text) != digest:
        raise SelectionFailure("source_snapshot_mismatch", f"source file changed since extraction: {path.name}")
    return text


@lru_cache(maxsize=4)
def _index_files(proof_text, masked_text, config):
    return SourceIndex(proof_text, config), source_snippets(masked_text)


def load_source(record, config, *, dataset_root=DATASET_ROOT):
    metadata = record["metadata"]
    root = repo_path(dataset_root)
    proof_path = repo_path(PurePosixPath(metadata["hol_light_proof_path"].replace("\\", "/")))
    statement_path = repo_path(PurePosixPath(metadata["hol_light_stmt_path"].replace("\\", "/")))
    allowed = {stem + ".ml" for stem in TOPICS.get(record["topic"], ())}
    if (proof_path.name not in allowed or proof_path.parent != root / "proofs" / "hol-light"
            or statement_path != root / "stmts" / "hol-light" / proof_path.name):
        raise SelectionFailure("source_snapshot_mismatch", "record does not identify an allowed most-match file pair")
    proof_sha = metadata["hol_light_proof_sha256"]
    statement_sha = metadata["raw_hol_light_stmt_sha256"]
    proof_text = _read_source(proof_path, config.max_source_chars, proof_sha)
    masked_text = _read_source(statement_path, config.max_source_chars, statement_sha)
    index, snippets = _index_files(proof_text, masked_text, config)
    name = record["hol_light_target_name"]
    start, end = metadata["hol_light_declaration_span"]
    binding = index.preceding(name, start + 1)
    if (binding is None or binding.kind != "theorem" or (binding.start, binding.end) != (start, end)
            or binding.statement != record["hol_light_statement"] or binding.proof != record["hol_light_proof"]):
        raise SelectionFailure("source_snapshot_mismatch", "selected proof does not match its pinned declaration")
    return SourceView(index, binding, proof_path.relative_to(repo_path(".")).as_posix(),
                      statement_path.relative_to(repo_path(".")).as_posix(), proof_sha, statement_sha, snippets)
