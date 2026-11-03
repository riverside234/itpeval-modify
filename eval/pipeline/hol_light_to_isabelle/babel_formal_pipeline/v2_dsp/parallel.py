"""Bounded native jobs, shared setup, cancellation and coordinator-owned outputs."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from dataclasses import asdict, dataclass, replace
import json
import math
import os
from pathlib import Path
import tempfile
from threading import Event
import time

from ..common import repo_path
from .runtime import CANCEL_EVENT, DspConfig, OwnedProcess, RUNTIME_DIR
from .native_search import NativeSearch, NativeFailure, resolve_imports, build_diagnostics, build_error
from .acceptance import PreparedNative

MAX_WORKERS = 60


def available_cpus():
    return len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)


def available_memory_bytes():
    try:
        values = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
        available = int(values["MemAvailable"].split()[0]) * 1024
        # Account for cgroup v2 limits on managed lab/container workers.
        maximum = Path("/sys/fs/cgroup/memory.max")
        current = Path("/sys/fs/cgroup/memory.current")
        if maximum.is_file() and maximum.read_text().strip() != "max":
            available = min(available, max(0, int(maximum.read_text()) - int(current.read_text())))
        return available
    except (OSError, ValueError, KeyError):
        return None


@dataclass(frozen=True)
class ParallelPlan:
    requested_workers: int
    workers: int
    threads_per_worker: int
    available_cpus: int
    memory_per_worker_gb: float
    available_memory_gb: float | None
    dependency_jobs: int = 1
    dependency_threads: int = 1

    def metadata(self):
        return asdict(self)


def plan_parallel(config, *, workers=1, threads_per_worker=None, memory_per_worker_gb=4.0,
                  dependency_jobs=None, dependency_threads=None):
    if isinstance(workers, bool) or not isinstance(workers, int) or not 1 <= workers <= MAX_WORKERS:
        raise ValueError("workers must be an integer between 1 and 60")
    threads = threads_per_worker if threads_per_worker is not None else (1 if workers > 1 else config.threads)
    if isinstance(threads, bool) or not isinstance(threads, int) or threads < 1:
        raise ValueError("threads_per_worker must be a positive integer")
    if (isinstance(memory_per_worker_gb, bool) or not isinstance(memory_per_worker_gb, (int, float))
            or not math.isfinite(memory_per_worker_gb) or memory_per_worker_gb <= 0):
        raise ValueError("memory_per_worker_gb must be finite and positive")
    for name, value in (("dependency_jobs", dependency_jobs), ("dependency_threads", dependency_threads)):
        if value is not None and (isinstance(value, bool) or not isinstance(value, int) or value < 1):
            raise ValueError(name + " must be a positive integer")
    cpus, memory = available_cpus(), available_memory_bytes()
    effective = min(workers, max(1, cpus // threads))
    if memory is not None and workers > 1:
        capacity = int(memory // (memory_per_worker_gb * 1024**3))
        if capacity < 1:
            raise ValueError("available memory is below the requested per-worker reserve")
        effective = min(effective, capacity)
    # A few large session builds need internal parallelism. The theorem workers'
    # single-thread policy must not make HOL-Analysis a single-thread build.
    dep_threads = min(dependency_threads or 8, cpus)
    if memory is not None:
        dep_threads = min(dep_threads, max(1, int(memory // 1024**3)))
    dep_jobs = min(dependency_jobs or 4, MAX_WORKERS, max(1, cpus // dep_threads))
    if memory is not None:
        reserve = max(float(memory_per_worker_gb), float(dep_threads)) * 1024**3
        if memory < reserve:
            raise ValueError("available memory is below the dependency build reserve")
        dep_jobs = min(dep_jobs, max(1, int(memory // reserve)))
    return ParallelPlan(workers, effective, threads, cpus, float(memory_per_worker_gb),
                        round(memory / 1024**3, 2) if memory is not None else None, dep_jobs, dep_threads)


def add_parallel_arguments(parser):
    parser.add_argument("--workers", type=int, default=1, help="Native verification workers, 1..60; effective count is CPU/memory limited")
    parser.add_argument("--threads-per-worker", type=int, help="Default 1 with parallel jobs; otherwise config.threads")
    parser.add_argument("--memory-per-worker-gb", type=float, default=4.0, help="Admission budget per native job, not a hard OS memory limit")
    parser.add_argument("--dependency-jobs", type=int, help="Concurrent dependency sessions (default up to 4; CPU/memory limited)")
    parser.add_argument("--dependency-threads", type=int, help="Threads per dependency session (default up to 8; independent of theorem workers)")


def parallel_options(args):
    return {name: getattr(args, name, None) for name in (
        "workers", "threads_per_worker", "memory_per_worker_gb", "dependency_jobs", "dependency_threads")}


def completed_jobs(function, items, *, workers, on_wait=None):
    """At most workers submissions in flight; only the caller writes shared files.

    Threads supervise isolated external Isabelle/ATP process groups, so Python's
    GIL does not serialize theorem compilation. Ctrl-C stops owned child groups.
    """
    if workers == 1:
        for index, item in enumerate(items):
            yield index, function(item)
        return
    cancel = Event()
    pool = ThreadPoolExecutor(max_workers=workers, thread_name_prefix="isabelle")
    pending = {}
    iterator = iter(enumerate(items))
    def invoke(item):
        token = CANCEL_EVENT.set(cancel)
        try:
            if cancel.is_set():
                raise InterruptedError("native batch cancelled")
            return function(item)
        finally:
            CANCEL_EVENT.reset(token)
    def submit():
        try:
            index, item = next(iterator)
        except StopIteration:
            return False
        pending[pool.submit(invoke, item)] = index
        return True
    try:
        for _ in range(workers):
            if not submit():
                break
        while pending:
            ready, _ = wait(pending, timeout=30 if on_wait else None, return_when=FIRST_COMPLETED)
            if not ready and on_wait:
                on_wait()
            for future in sorted(ready, key=lambda f: pending[f]):
                index = pending.pop(future)
                result = future.result()
                # Refill before coordinator-side checkpoint/serialization work.
                submit()
                yield index, result
    finally:
        cancel.set()
        for future in pending:
            future.cancel()
        pool.shutdown(wait=True, cancel_futures=True)


def prepare_dependencies(config, records, plan, *, directory=None):
    """Build each owning session once before concurrent jobs can update its heap.

    These are dependency sessions, NOT the parent of the proof state. Individual
    jobs still import only the original theory dependencies from the HOL parent.
    """
    sessions = set(config.session_dependencies)
    for record in records:
        from ..theory_context import validate_context
        context = validate_context(record)
        _, resolution = resolve_imports(context.prefix, config, theory_name=context.theory_name)
        sessions.update(resolution["session_dependencies"])
    sessions.discard(config.base_session)
    if not sessions:
        return {"ok": True, "sessions": []}
    if directory is None:
        base = repo_path(RUNTIME_DIR) / "dependency_builds"
        base.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="build-", dir=base))
    directory.mkdir(parents=True, exist_ok=True)
    command = [str(config.executable), "build", "-b", "-j", str(plan.dependency_jobs),
               "-o", "document=false", "-o", "parallel_proofs=1", "-o", "timeout_scale=1.0",
               "-o", "threads=" + str(plan.dependency_threads)]
    for root in config.session_roots:
        command += ["-d", str(repo_path(root))]
    command += sorted(sessions)
    (directory / "command.json").write_text(json.dumps(command, indent=2) + "\n", encoding="utf-8")
    print(f"DEPENDENCIES: jobs={plan.dependency_jobs}, threads/session={plan.dependency_threads}; "
          "Isabelle will reuse current heaps. Log: " + str(directory / "build.log"), flush=True)
    started = time.monotonic()
    code = OwnedProcess(command, directory=directory, env=config.environment(),
        log_path=directory / "build.log", timeout_s=config.dependency_timeout_s,
        deadline=time.monotonic() + config.dependency_timeout_s).run()
    diagnostics = build_diagnostics(directory, code)
    if code:
        raise NativeFailure("import_error", build_error("dependency build failed", diagnostics), details=diagnostics)
    return {"ok": True, "sessions": sorted(sessions), "jobs": plan.dependency_jobs,
            "threads_per_session": plan.dependency_threads, "parallel_proofs": 1,
            "duration_seconds": round(time.monotonic() - started, 3), **diagnostics}


def prepare_batch(config, records, plan):
    config = replace(config, threads=plan.threads_per_worker)
    backend = config.metadata()  # Validate release/settings before any build.
    prepare_dependencies(config, records, plan)
    parent = NativeSearch(config).infrastructure(deadline=time.monotonic() + config.target_timeout_s)
    imports = None
    if any(row.get("source") == "hol-most-match" for row in records):
        from .import_cache import prepare_import_parents
        imports, _ = prepare_import_parents(config, records, plan, parent)
    return config, backend, lambda cfg: PreparedNative(cfg, parent, import_parents=imports)


def gate_records(records, *, config, plan, results_dir, sketch_source, fail_fast=False):
    from ..common import key
    from .preflight import control_record, preflight
    valid = [row for row in records if not row.get("input_error")]
    if not valid:
        return {}
    control_row = control_record("by simp", source=valid[0]["source"], sketch_source=sketch_source)
    config, backend, factory = prepare_batch(config, [*valid, control_row], plan)
    control = preflight(control_row,
        config=config, backend_metadata=backend, results_dir=results_dir, sketch_source=sketch_source,
        native_factory=factory)
    if not control["ok"]:
        raise RuntimeError("native capability controls failed: " + json.dumps(control))
    def check(row):
        return preflight(row, config=config, controls=False, backend_metadata=backend, results_dir=results_dir,
                         sketch_source=sketch_source, native_factory=factory)
    blocked = {}
    for index, result in completed_jobs(check, valid, workers=plan.workers):
        row = valid[index]
        print(f"CONTEXT {'PASS' if result['ok'] else 'FAIL'} {row['topic']}/{row['target_key']}", flush=True)
        if not result["ok"]:
            blocked[key(row)] = {"failure_category": result.get("failure_category") or "context_error",
                                  "error": result.get("error") or "context preflight failed"}
            if fail_fast:
                raise RuntimeError(blocked[key(row)]["error"])
    return blocked
