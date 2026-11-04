"""DSP-style native Isabelle2026 search and checked target completion.

Heuristic ordering: albertqjiang/draft_sketch_prove commit 647aa65.
Copyright Sean Welleck, Albert Q. Jiang, Jin Peng Zhou and others.
See UPSTREAM_LICENSE.txt. No PISA runtime is used.
"""
from __future__ import annotations

import tempfile
import time
from pathlib import Path

from ..common import RESULTS_DIR, repo_path
from ..theory_context import validate_context
from .input_contract import clean_record, envelope, input_metadata, mode_of, validate_artifacts, normalize_sketch, normalize_proof
from .native_search import NativeFailure, NativeSearch
from .runtime import DspConfig

ProofFailure = NativeFailure  # Preserve the old exception import for callers.

CHECKER_VERSION = "dsp_isabelle2026_native_p12"
HEURISTICS = (
    "by auto", "by simp", "by blast", "by fastforce", "by force", "by eval",
    "by presburger", "by sos", "by arith", "by linarith", "by (auto simp: field_simps)",
    # Direct library rules precede expensive general search. Expand pair binders
    # without simplifying norm(scaleR ...) before matching the triangle rule.
    # simp treats norm_sum as a proposition; it does not resolve unrelated
    # chained facts (e.g. finite p) into the premise-free norm_sum rule.
    "by (simp only: case_prod_beta' norm_sum)",
    "by (simp only: case_prod_beta'; intro sum_mono; force)",
    "by (simp add: case_prod_beta' sum_distrib_left[symmetric] sum_distrib_right[symmetric])",
    # Products of variable terms need order rules or nonlinear arithmetic. Keep
    # the more expensive metis fallback last; a candidate timeout is recoverable.
    # No selected-target fact or completed Isabelle proof is supplied here.
    "by (auto simp: mult.commute intro: mult_left_mono mult_right_mono)",
    "by (simp only: norm_scaleR; metis abs_of_nonneg mult_right_mono mult.commute)",
)


def verification_input(record: dict, mode: str) -> dict:
    """A new check cannot inherit diagnostics or success artifacts from an old job."""
    result = clean_record(record, mode)
    for name in (
        "failed_obligation", "search_summary", "native_search", "native_replay", "native_result", "native_context", "prover_settings", "workdir",
        "search_directory", "build_directory", "build_session", "build_log_path",
        "build_log_excerpt", "build_returncode", "build_metrics", "termination_hint", "parent_session", "replay_theory_path", "replay_log_path",
        "replay_verified", "verification_method", "pisa_result", "dsp_result", "import_resolution", "verify_fingerprint", "verify_duration_seconds", "backend_metadata", "isabelle_proof",
    ):
        result.pop(name, None)
    return result


def failure_obligation(steps: list[dict]) -> dict:
    """Expose the final failed state, without attributing an earlier gap's errors.

    Old workers record synthetic method lines as zero. The preceding source
    command and a failed candidate's goal provide useful diagnostics even for
    those historical traces. Never treat these messages as proof evidence.
    """
    if not steps or steps[-1].get("success"):
        return {}
    last = steps[-1]
    result = {name: last[name] for name in ("mode", "line", "source_state", "command", "error", "timeout_scope") if name in last}
    for field, size in (("command", 2000), ("error", 4000)):
        if field in result:
            result[field] = result[field][:size]
    if last.get("mode") not in {"heuristic", "normalization", "hammer", "reconstruction"}:
        return result
    state = last.get("source_state")
    if state is None:
        return result
    current = [step for step in steps if step.get("source_state") == state]
    result["hammer_attempted"] = any(step.get("mode") == "hammer" for step in current)
    result["candidate_timeout_count"] = sum(step.get("timeout_scope") == "candidate" for step in current)
    for step in reversed(steps[:-1]):
        if (step.get("mode") in {"search", "target"} and step.get("success")
                and step.get("command", "").strip()):
            result["preceding_command"] = step["command"][:2000]
            result["preceding_line"] = step.get("line")
            break
    for step in steps:
        if (step.get("source_state") == state and step.get("mode") == "heuristic"
                and not step.get("success") and "goal (" in step.get("error", "")):
            result["goal_diagnostic"] = step["error"][-4000:]
            break
    return result


def search_summary(steps: list[dict]) -> dict:
    """Keep search coverage visible even when compact reports truncate attempts."""
    result = {"candidate_timeouts": sum(s.get("timeout_scope") == "candidate" for s in steps)}
    for mode in ("heuristic", "normalization", "hammer", "reconstruction"):
        selected = [s for s in steps if s.get("mode") == mode]
        result[mode + "_attempts"] = len(selected)
        result[mode + "_successes"] = sum(bool(s.get("success")) for s in selected)
    return result


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
        diagnostics = {"workdir": str(directory), "build_log_path": str(directory / "build.log")}
        try:
            result = self.native_factory(self.config).request(
                record, "", directory=directory, action="context", heuristics=(),
                deadline=time.monotonic() + self.config.target_timeout_s)
            if not result["success"]:
                raise NativeFailure(result["failure_category"], result["error"],
                                    details={"native_result": result})
        except NativeFailure as exc:
            for name, value in diagnostics.items():
                exc.details.setdefault(name, value)
            raise
        except Exception as exc:
            category = "timeout" if isinstance(exc, TimeoutError) else "context_error"
            raise NativeFailure(category, f"{type(exc).__name__}: {exc}", details=diagnostics) from exc
        return {"baseline_ok": True, "workdir": str(directory), "backend_metadata": backend,
                **context.metadata, "native_result": result}

    def check(self, record: dict, *, backend_metadata: dict | None = None,
              force_hammer: bool = False) -> dict:
        mode = mode_of(record)
        result = {**verification_input(record, mode), **envelope(mode), "checker_version": CHECKER_VERSION,
                  "verification_method": "isabelle2026_native_completion",
                  "prove_success": False, "verified": False,
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
            sketch = normalize_sketch(record.get("isabelle_sketch", ""))
            stage = "toolchain_error"
            result["backend_metadata"] = backend_metadata or self.config.metadata()
            directory = self.directory("target-")
            result["workdir"] = str(directory)
            native = self.native_factory(self.config)
            stage = "worker_failure"
            search = native.request(record, sketch, directory=directory / "search", action="search",
                                    heuristics=() if force_hammer else HEURISTICS, deadline=deadline)
            result["native_search"] = search
            result["step_results"] = search["step_results"]
            result["search_summary"] = search_summary(search["step_results"])
            result["prover_settings"] = search.get("prover_settings", {})
            if not search["success"] or not search.get("target_closed"):
                message = search.get("error") or "target is open"
                result["failed_obligation"] = failure_obligation(search["step_results"])
                obligation = result["failed_obligation"]
                if (obligation.get("mode") in {"hammer", "reconstruction"}
                        and not obligation.get("goal_diagnostic")
                        and search.get("prover_settings", {}).get("goal_before_search")):
                    obligation["goal_diagnostic"] = search["prover_settings"]["goal_before_search"][-4000:]
                if obligation.get("preceding_command"):
                    message += (f"; after sketch line {obligation.get('preceding_line', '?')}: "
                                + obligation["preceding_command"][:400])
                if obligation.get("goal_diagnostic"):
                    message += "\n" + obligation["goal_diagnostic"]
                last_step = search["step_results"][-1] if search["step_results"] else {}
                if (not last_step.get("success") and last_step.get("error")
                        and last_step["error"] not in message):
                    message += f" (line {last_step.get('line', '?')}): {last_step['error']}"
                raise NativeFailure(search.get("failure_category") or "incomplete_proof", message)
            # The native job has already executed every command, reconstructed each
            # gap and closed this target. There is no second proof build.
            result["isabelle_proof"] = normalize_proof(search["isabelle_proof"])
            result["prove_success"] = result["verified"] = True
        except Exception as exc:
            if isinstance(exc, NativeFailure):
                result.update(exc.details)
            result["verify_error"] = f"{type(exc).__name__}: {exc}"
            result["failure_category"] = (exc.category if isinstance(exc, NativeFailure) else
                "timeout" if isinstance(exc, TimeoutError) else
                "rejected_proof" if isinstance(exc, ValueError) and stage == "input_error" else stage)
        result["verify_duration_seconds"] = round(time.monotonic() - started, 3)
        return result
