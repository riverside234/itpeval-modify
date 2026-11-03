"""Reusable heaps of exactly the original imports, never dataset declarations.

A ROOT ``sessions`` clause supplies source visibility, not a parent ML heap.
Prebuilding HOL-Analysis therefore does not prevent a HOL-based worker from
recompiling imported Analysis theories. Build one small session per import set
and use that heap as the worker's parent. Isabelle still checks heap freshness.
"""
from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import tempfile
import time

from ..common import fingerprint, repo_path
from ..theory_context import validate_context
from .native_search import NativeFailure, quote, resolve_imports, session_clause, build_diagnostics, build_error
from .runtime import OwnedProcess, RUNTIME_DIR

CACHE_VERSION = "original_imports_v1"


def import_key(resolution):
    # Preserve import order: syntax/merge order is part of the original context.
    return fingerprint({name: resolution[name] for name in ("resolved_imports", "session_dependencies")})


@dataclass(frozen=True)
class ImportParent:
    directory: Path
    session: str
    base_directory: Path
    imports: tuple[str, ...]

    def job_parent(self):
        return (self.base_directory, self.directory), self.session


def prepare_import_parents(config, records, plan, parent, *, directory=None):
    """Build each unique import set once, outside individual target deadlines.

    Source freshness is checked on every invocation by normal ``isabelle build``.
    No target statement, masked prefix, later theorem or completed target theory
    is copied into these heaps. Different import sets are never merged.
    """
    groups = {}
    for row in records:
        context = validate_context(row)
        _, resolution = resolve_imports(context.prefix, config, theory_name=context.theory_name)
        groups.setdefault(import_key(resolution), resolution)
    if not groups:
        return {}, {"ok": True, "import_sets": 0, "sessions": []}
    base_dir, base_session = parent
    parents = {}
    descriptions = []
    for key, resolution in sorted(groups.items()):
        identity = fingerprint({"version": CACHE_VERSION, "base": base_session,
            "resolution": resolution, "session_roots": config.session_roots,
            "threads": plan.dependency_threads})[:20]
        session = "DSP_Imports_" + identity
        folder = repo_path(RUNTIME_DIR) / "import_heaps" / identity
        folder.mkdir(parents=True, exist_ok=True)
        # ROOT options override command-line defaults. Thus threads=1 on a
        # theorem worker cannot invalidate/rebuild this parallel library heap.
        root = ("session " + session + " = " + quote(base_session) + " +\n"
                "  options [document = false, parallel_proofs = 1, threads = " + str(plan.dependency_threads) +
                ", timeout_scale = 1.0]\n" + session_clause(resolution) + "  theories DSP_Imports\n")
        theory = ("theory DSP_Imports imports DSP_Native " +
                  " ".join(quote(name) for name in resolution["resolved_imports"]) + "\nbegin\nend\n")
        for name, text in (("ROOT", root), ("DSP_Imports.thy", theory)):
            destination = folder / name
            if not destination.is_file() or destination.read_text(encoding="utf-8") != text:
                destination.write_text(text, encoding="utf-8")
        parents[key] = ImportParent(folder, session, base_dir, tuple(resolution["resolved_imports"]))
        descriptions.append({"session": session, "directory": str(folder), **resolution})
    if directory is None:
        root = repo_path(RUNTIME_DIR) / "import_builds"
        root.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="build-", dir=root))
    directory.mkdir(parents=True, exist_ok=True)
    command = [str(config.executable), "build", "-b", "-j", str(plan.dependency_jobs),
               "-o", "document=false", "-o", "parallel_proofs=1",
               "-o", "threads=" + str(plan.dependency_threads), "-o", "timeout_scale=1.0"]
    for root in dict.fromkeys([*(repo_path(p) for p in config.session_roots), base_dir,
                              *(p.directory for p in parents.values())]):
        command += ["-d", str(root)]
    command += [p.session for p in parents.values()]
    (directory / "command.json").write_text(json.dumps(command, indent=2) + "\n", encoding="utf-8")
    (directory / "imports.json").write_text(json.dumps(descriptions, indent=2) + "\n", encoding="utf-8")
    print(f"IMPORT HEAPS: {len(parents)} original import sets; jobs={plan.dependency_jobs}, "
          f"threads/session={plan.dependency_threads}. Log: {directory / 'build.log'}", flush=True)
    started = time.monotonic()
    process = OwnedProcess(command, directory=directory, env=config.environment(),
        log_path=directory / "build.log", timeout_s=config.dependency_timeout_s,
        deadline=started + config.dependency_timeout_s)
    try:
        code = process.run()
    except (TimeoutError, OSError) as exc:
        details = build_diagnostics(directory, getattr(getattr(process, "process", None), "returncode", None))
        raise NativeFailure("import_build_error", build_error(str(exc), details), details=details) from exc
    details = build_diagnostics(directory, code)
    if code:
        raise NativeFailure("import_build_error", build_error("original-import heap build failed", details), details=details)
    return parents, {"ok": True, "import_sets": len(parents), "sessions": descriptions,
                    "jobs": plan.dependency_jobs, "threads_per_session": plan.dependency_threads,
                    "duration_seconds": round(time.monotonic() - started, 3), **details}
