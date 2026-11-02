"""Individual-theorem DSP/PISA execution. Success is PISA completion, with no replay."""
from __future__ import annotations
import tempfile
import time
from pathlib import Path

from ..common import RESULTS_DIR, repo_path
from .input_contract import clean_record, envelope, input_metadata, mode_of, normalize_sketch, validate_artifacts
from .pisa_context import prepare_context
from .runtime import DspConfig, PisaFailure, run_job

CHECKER_VERSION = "dsp_pisa_isabelle2021_p1"
ProofFailure = PisaFailure


def verification_input(record, mode):
    result = clean_record(record, mode)
    for name in list(result):
        if name.startswith(("native_", "replay_", "verify_")) or name in {
            "workdir", "backend_metadata", "isabelle_proof", "dsp_result", "step_results", "prover_settings",
            "prove_success", "verified", "failure_category"}:
            result.pop(name, None)
    return result


class Checker:
    def __init__(self, config: DspConfig, *, results_dir=RESULTS_DIR, job_runner=None):
        self.config, self.results_dir = config, results_dir
        self.job_runner = job_runner or run_job

    def directory(self, prefix):
        parent = repo_path(self.results_dir) / "work"
        parent.mkdir(parents=True, exist_ok=True)
        return Path(tempfile.mkdtemp(prefix=prefix, dir=parent))

    def check_context(self, record, *, backend_metadata=None):
        context, preamble, imports = prepare_context(record, self.config)
        backend = backend_metadata or self.config.metadata()
        directory = self.directory("context-")
        request = {"action": "context", "formal": preamble, "theory_name": context.theory_name}
        result = self.job_runner(self.config, directory, request)
        if not result["success"]:
            raise PisaFailure(result.get("failure_category") or "context_error", result.get("error") or "target goal was not opened",
                details={"workdir": str(directory), "pisa_result": result, "import_resolution": imports})
        return {"baseline_ok": True, "workdir": str(directory), "backend_metadata": backend,
                "pisa_result": result, "import_resolution": imports, **context.metadata}

    def check(self, record, *, backend_metadata=None, force_hammer=False):
        mode = mode_of(record)
        result = {**verification_input(record, mode), **envelope(mode), "checker_version": CHECKER_VERSION,
                  "verified": False, "prove_success": False, "verification_method": "dsp_pisa_completion",
                  "verify_error": "", "failure_category": None, "step_results": []}
        started = time.monotonic()
        stage = "rejected_proof"
        try:
            validate_artifacts([record], mode)
            if record.get("input_error") or record.get("sketch_error"):
                raise PisaFailure(record.get("failure_category") or "sketch_error", record.get("input_error") or record["sketch_error"])
            result.update(input_metadata(record, mode))
            sketch = normalize_sketch(record.get("isabelle_sketch", ""))
            context, preamble, imports = prepare_context(record, self.config)
            stage = "toolchain_error"
            result["backend_metadata"] = backend_metadata or self.config.metadata()
            directory = self.directory("target-")
            result.update(workdir=str(directory), import_resolution=imports)
            stage = "worker_failure"
            checked = self.job_runner(self.config, directory, {"action": "prove", "theory_name": context.theory_name,
                "formal": preamble + "\n" + sketch, "force_hammer": force_hammer})
            result.update(pisa_result=checked, dsp_result=checked.get("dsp_result"), step_results=checked.get("step_results", []))
            if not checked["success"]:
                raise PisaFailure(checked.get("failure_category") or "proof_failure", checked.get("error") or "PISA did not finish the theorem")
            # The upstream success condition is done && reward == 1.0 after all steps.
            result["prove_success"] = result["verified"] = True
        except Exception as exc:
            if isinstance(exc, PisaFailure):
                result.update(exc.details)
            result["verify_error"] = f"{type(exc).__name__}: {exc}"
            result["failure_category"] = exc.category if isinstance(exc, PisaFailure) else stage
        result["verify_duration_seconds"] = round(time.monotonic()-started, 3)
        return result
