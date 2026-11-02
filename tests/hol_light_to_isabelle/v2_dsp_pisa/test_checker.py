"""Transport/orchestration tests; fake jobs never claim native mathematical validation."""
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path, write_jsonl
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.checker import Checker, CHECKER_VERSION
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.prove import prove_sketches
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.runtime import DspConfig, PisaFailure

CONFIG = DspConfig()
BACKEND = {"backend": "dsp-pisa", "isabelle_version": "Isabelle2021", "backend_fingerprint": "fixture"}
MODULE = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa."


def fake_job(config, directory, request):
    return {"success": True, "dsp_result": {"success": True, "num_steps": 3},
            "step_results": [{"mode": "search", "success": True}], "error": ""}


class CheckerTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="pisa-checker-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.job = Mock(side_effect=fake_job)
        self.checker = Checker(CONFIG, results_dir=str(self.path), job_runner=self.job)

    def test_one_upstream_job_is_the_complete_verification_no_replay(self):
        result = self.checker.check(control_record("by simp"), backend_metadata=BACKEND)
        self.assertTrue(result["verified"], result)
        self.assertTrue(result["prove_success"])
        self.assertEqual("dsp_pisa_completion", result["verification_method"])
        self.job.assert_called_once()
        request = self.job.call_args.args[2]
        self.assertTrue(request["formal"].rstrip().endswith("by simp"))
        self.assertNotIn("Symmetric_Polynomials", request["formal"])
        self.assertEqual("prove", request["action"])
        self.assertNotIn("replay_verified", result)
        self.assertNotIn("isabelle_proof", result)

    def test_incomplete_or_failed_pisa_result_is_a_failure(self):
        self.job.side_effect = None
        self.job.return_value = {"success": False, "failure_category": "proof_failure", "error": "open goal"}
        result = self.checker.check(control_record("by simp"), backend_metadata=BACKEND)
        self.assertFalse(result["verified"])
        self.assertEqual("proof_failure", result["failure_category"])
        self.job.assert_called_once()

    def test_context_gate_checks_open_target_with_no_source_proof(self):
        result = self.checker.check_context(control_record("by simp"), backend_metadata=BACKEND)
        self.assertTrue(result["baseline_ok"])
        request = self.job.call_args.args[2]
        self.assertEqual("context", request["action"])
        self.assertTrue(request["formal"].rstrip().endswith('lemma v2_control: "True"'))
        self.assertNotIn("by simp", request["formal"])

    def test_context_failure_preserves_work_directory(self):
        self.job.side_effect = None
        self.job.return_value = {"success": False, "failure_category": "context_error", "error": "bad imports"}
        with self.assertRaises(PisaFailure) as raised:
            self.checker.check_context(control_record("by simp"), backend_metadata=BACKEND)
        self.assertEqual("context_error", raised.exception.category)
        self.assertTrue(Path(raised.exception.details["workdir"]).is_dir())

    def test_admission_and_unsafe_settings_are_rejected_before_worker(self):
        for body in ('proof -\n sorry\nqed', 'by ("tactic" \\<open>all_tac\\<close>)',
                     'proof - supply [[smt_oracle = true]] show True by simp qed'):
            result = self.checker.check(control_record(body), backend_metadata=BACKEND)
            self.assertFalse(result["verified"])
            self.assertEqual("rejected_proof", result["failure_category"])
        self.job.assert_not_called()

    def test_old_native_results_are_rejected_and_cannot_supply_success(self):
        row = {**control_record("by simp"), "expected_isabelle_version": "Isabelle2026",
               "native_search": {"success": True}, "replay_verified": True}
        result = self.checker.check(row, backend_metadata=BACKEND)
        self.assertFalse(result["verified"])
        self.assertNotIn("native_search", result)
        self.assertNotIn("replay_verified", result)
        self.job.assert_not_called()

    def test_prove_resume_depends_on_current_backend(self):
        source, output = self.path/"sketches.jsonl", self.path/"result.jsonl"
        write_jsonl(source, [control_record("by simp")])
        options = dict(config=CONFIG, input_path=source, output_path=output, prove_output=None, results_dir=str(self.path))
        with patch(MODULE+"runtime.DspConfig.metadata", return_value=BACKEND), patch(MODULE+"checker.run_job", side_effect=fake_job) as job:
            first = prove_sketches(**options)
            second = prove_sketches(**options)
            self.assertTrue(first[0]["verified"])
            self.assertEqual(first, second)
            job.assert_called_once()
        with patch(MODULE+"runtime.DspConfig.metadata", return_value={**BACKEND, "backend_fingerprint": "changed"}), patch(MODULE+"checker.run_job", side_effect=fake_job) as job:
            prove_sketches(**options)
            job.assert_called_once()

    def test_missing_samples_are_still_failed_denominator_entries(self):
        row = control_record("by simp")
        source = self.path/"sketches.jsonl"
        write_jsonl(source,[row])
        with patch(MODULE+"runtime.DspConfig.metadata", return_value=BACKEND), patch(MODULE+"checker.run_job", side_effect=fake_job):
            result = prove_sketches(config=CONFIG,input_path=source,output_path=self.path/"result.jsonl",prove_output=None,
                                   expected=[row],expected_samples=2,results_dir=str(self.path))
        self.assertEqual(2,len(result))
        self.assertEqual(1,sum(r["verified"] for r in result))
        self.assertEqual("missing_sketch",result[1]["failure_category"])


if __name__ == "__main__":
    unittest.main()
