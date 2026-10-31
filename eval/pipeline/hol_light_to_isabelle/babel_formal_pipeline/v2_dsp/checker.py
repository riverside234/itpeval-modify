"""DSP-style native Isabelle2026 search and independent replay.

Heuristic ordering: albertqjiang/draft_sketch_prove commit 647aa65.
Copyright Sean Welleck, Albert Q. Jiang, Jin Peng Zhou and others.
See UPSTREAM_LICENSE.txt. No PISA runtime is used.
"""
from __future__ import annotations

import tempfile
import time
from pathlib import Path

from ..common import RESULTS_DIR, repo_path
from ..theory_context import normalize_body, validate_context
from .input_contract import clean_record, envelope, input_metadata, mode_of, validate_artifacts, normalize_sketch
from .native_search import NativeFailure, NativeSearch
from .runtime import DspConfig

ProofFailure = NativeFailure  # Preserve the old exception import for callers.

CHECKER_VERSION = "dsp_isabelle2026_native_p1"
HEURISTICS = (
    "by auto", "by simp", "by blast", "by fastforce", "by force", "by eval",
    "by presburger", "by sos", "by arith", "by linarith", "by (auto simp: field_simps)",
)


class Checker:
    def __init__(self, config: DspConfig, *, native_factory=None, results_dir: str = RESULTS_DIR):
        self.config = config
        self.native_factory = native_factory or NativeSearch
        self.results_dir = results_dir

    def directory(self, prefix: str) -> Path:
        base = repo_path(self.results_dir) / "work"
        base.mkdir(parents=True, exist_ok=True)
        return Path(tempfile.mkdtemp(prefix=prefix, dir=base))

    def check_context(self, record: dict, *, backend_metadata: dict | None = None) -> dict:
        context = validate_context(record)  # Raw extracted records need no Draft in either mode.
        backend = backend_metadata or self.config.metadata()
        directory = self.directory("context-")
        result = self.native_factory(self.config).request(
            record, "", directory=directory, action="context", heuristics=(),
            deadline=time.monotonic() + self.config.target_timeout_s)
        if not result["success"]:
            raise NativeFailure(result["failure_category"], result["error"])
        return {"baseline_ok": True, "workdir": str(directory), "backend_metadata": backend,
                **context.metadata, "native_result": result}

    def check(self, record: dict, *, replay_only: bool = False,
              backend_metadata: dict | None = None, force_hammer: bool = False) -> dict:
        mode = mode_of(record)
        result = {**clean_record(record, mode), **envelope(mode), "checker_version": CHECKER_VERSION,
                  "prove_success": False, "replay_verified": False, "verified": False,
                  "verify_error": "", "failure_category": None, "step_results": []}
        started = time.monotonic()
        deadline = started + self.config.target_timeout_s
        stage = "input_error"
        try:
            validate_artifacts([record], mode)
            if record.get("input_error") or record.get("sketch_error"):
                raise NativeFailure(record.get("failure_category") or "sketch_error",
                                    record.get("input_error") or record["sketch_error"])
            result.update(input_metadata(record, mode))
            validate_context(record)
            proof = normalize_body(record.get("isabelle_proof", "")) if replay_only else normalize_sketch(record.get("isabelle_sketch", ""))
            stage = "toolchain_error"
            result["backend_metadata"] = backend_metadata or self.config.metadata()
            directory = self.directory("target-")
            result["workdir"] = str(directory)
            native = self.native_factory(self.config)
            if not replay_only:
                stage = "worker_failure"
                search = native.request(record, proof, directory=directory / "search", action="search",
                                        heuristics=() if force_hammer else HEURISTICS, deadline=deadline)
                result["native_search"] = search
                result["step_results"] = search["step_results"]
                result["prover_settings"] = search.get("prover_settings", {})
                if not search["success"] or not search.get("target_closed"):
                    raise NativeFailure(search.get("failure_category") or "incomplete_proof", search.get("error", "target is open"))
                proof = normalize_body(search["isabelle_proof"])
                result["prove_success"] = True
            result["isabelle_proof"] = proof
            stage = "replay_failure"
            replay = native.replay(record, proof, directory=directory / "replay", deadline=deadline)
            result["native_replay"] = replay
            result.update({k: v for k, v in replay.items() if k in {"replay_theory_path", "replay_log_path"}})
            if not replay["success"]:
                raise NativeFailure("replay_failure", "fresh Isabelle2026 proof build failed; inspect replay log")
            result["prove_success"] = result["replay_verified"] = result["verified"] = True
        except Exception as exc:
            result["verify_error"] = f"{type(exc).__name__}: {exc}"
            result["failure_category"] = (exc.category if isinstance(exc, NativeFailure) else
                "timeout" if isinstance(exc, TimeoutError) else
                "rejected_proof" if isinstance(exc, ValueError) and stage == "input_error" else stage)
        result["verify_duration_seconds"] = round(time.monotonic() - started, 3)
        return result
