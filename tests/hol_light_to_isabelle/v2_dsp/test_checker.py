"""Orchestration tests use a fake adapter, not a mathematical proof checker."""
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, read_jsonl, repo_path, write_jsonl
from eval.pipeline.hol_light_to_isabelle.v2_dsp.checker import CHECKER_VERSION, Checker, HEURISTICS
from eval.pipeline.hol_light_to_isabelle.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.v2_dsp.prove import prove_sketches
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.v2_dsp.native_search import NativeFailure

CONFIG = DspConfig()
BACKEND = {"backend": "isabelle-native", "isabelle_version": "Isabelle2026", "native_adapter_sha256": "a"}
SKETCH = "proof -\n show True\n sledgehammer\nqed"
MODULE = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp."


class FakeNative:
    """Controlled job/replay fixture; it does not interpret Isabelle."""
    def __init__(self, config):
        self.calls = []
        self.success = self.closed = self.replay_ok = True
        self.error = None
        self.proof = "by simp"

    def request(self, record, sketch, **options):
        self.calls.append(("request", sketch, options))
        if self.error:
            raise self.error
        return {"success": self.success, "target_closed": self.closed, "isabelle_proof": self.proof,
                "failure_category": "missing_reconstruction", "error": "fixture failure",
                "step_results": [{"mode": "hammer", "success": self.success}],
                "prover_settings": {"resolved_provers": "e"}}

    def replay(self, record, proof, **options):
        self.calls.append(("replay", proof, options))
        path = options["directory"] / "V2Control.thy"
        path.parent.mkdir(parents=True)
        path.write_text("fixture replay artifact", encoding="utf-8")
        return {"success": self.replay_ok, "replay_theory_path": str(path)}


class CheckerTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="native-checker-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.fake = FakeNative(CONFIG)
        self.checker = Checker(CONFIG, native_factory=lambda config: self.fake, results_dir=str(self.path))

    def check(self, proof=SKETCH, **options):
        return self.checker.check(control_record(proof), backend_metadata=BACKEND, **options)

    def test_search_then_fresh_replay_and_preserved_sketch(self):
        result = self.check()
        self.assertTrue(result["verified"], result["verify_error"])
        self.assertEqual(SKETCH, result["isabelle_sketch"])
        self.assertEqual("by simp", result["isabelle_proof"])
        self.assertEqual(["request", "replay"], [x[0] for x in self.fake.calls])
        self.assertEqual(HEURISTICS, self.fake.calls[0][2]["heuristics"])
        self.assertNotEqual(self.fake.calls[0][2]["directory"], self.fake.calls[1][2]["directory"])

    def test_forced_hammer_gate_bypasses_heuristics(self):
        self.assertTrue(self.check(force_hammer=True)["verified"])
        self.assertEqual((), self.fake.calls[0][2]["heuristics"])

    def test_reconstruction_and_target_closure_are_required(self):
        for changed in ({"closed": False}, {"success": False}, {"proof": ""}, {"proof": "by sledgehammer"}):
            self.fake = FakeNative(CONFIG)
            for name, value in changed.items():
                setattr(self.fake, name, value)
            result = self.check()
            self.assertFalse(result["verified"], changed)
            self.assertFalse(any(call[0] == "replay" for call in self.fake.calls))

    def test_fresh_replay_failure_cannot_count_as_verified(self):
        self.fake.replay_ok = False
        result = self.check()
        self.assertTrue(result["prove_success"])
        self.assertFalse(result["replay_verified"])
        self.assertEqual("replay_failure", result["failure_category"])

    def test_timeout_does_not_continue_or_replay(self):
        self.fake.error = TimeoutError("fixture timeout")
        result = self.check()
        self.assertEqual("timeout", result["failure_category"])
        self.assertEqual(1, len(self.fake.calls))

    def test_admissions_ml_and_malformed_placeholders_are_rejected_before_native(self):
        for proof in ("proof -\n sorry\nqed", "by sledgehammer", "proof -\n sledgehammer [timeout=1]\nqed",
                      "proof -\n ML \\<open>fail ()\\<close>\nqed", "by (tactic \\<open>all_tac\\<close>)"):
            with self.subTest(proof=proof):
                result = self.check(proof)
                self.assertFalse(result["verified"])
                self.assertEqual("rejected_proof", result["failure_category"])
        self.assertEqual([], self.fake.calls)

    def test_context_preflight_does_not_require_a_draft(self):
        row = control_record("by simp")
        del row["draft"]
        result = self.checker.check_context(row, backend_metadata=BACKEND)
        self.assertTrue(result["baseline_ok"])
        self.assertEqual("context", self.fake.calls[0][2]["action"])

    def test_replay_only_does_not_search(self):
        row = {**control_record("by simp"), "isabelle_proof": "by simp"}
        result = self.checker.check(row, backend_metadata=BACKEND, replay_only=True)
        self.assertTrue(result["verified"])
        self.assertEqual(["replay"], [c[0] for c in self.fake.calls])

    def test_resume_depends_on_native_adapter_and_budgets(self):
        source, output = self.path / "sketches.jsonl", self.path / "verified.jsonl"
        row = control_record(SKETCH)
        write_jsonl(source, [row])
        result = {**row, "checker_version": CHECKER_VERSION, "prove_success": True,
                  "replay_verified": True, "verified": True}
        with patch.object(DspConfig, "metadata", return_value=BACKEND) as metadata, patch(
                MODULE + "prove.Checker.check", return_value=result) as check:
            opts = dict(config=CONFIG, input_path=source, output_path=output, prove_output=None,
                        expected=[row], expected_samples=1)
            prove_sketches(**opts)
            prove_sketches(**opts)
            self.assertEqual(1, check.call_count)
            metadata.return_value = {**BACKEND, "native_adapter_sha256": "changed"}
            prove_sketches(**opts)
            self.assertEqual(2, check.call_count)
            from dataclasses import replace
            prove_sketches(**{**opts, "config": replace(CONFIG, hammer_timeout_s=7)})
            self.assertEqual(3, check.call_count)

    def test_missing_and_failed_sketches_stay_in_cohort(self):
        source, output = self.path / "empty.jsonl", self.path / "verified.jsonl"
        write_jsonl(source, [])
        targets = [control_record(SKETCH), {**control_record(SKETCH), "target_key": "other"}]
        with patch.object(DspConfig, "metadata", return_value=BACKEND):
            rows = prove_sketches(config=CONFIG, input_path=source, output_path=output, prove_output=None,
                                  expected=targets, expected_samples=2)
        self.assertEqual(4, len(rows))
        self.assertTrue(all(row["failure_category"] == "missing_sketch" for row in rows))
        import json
        summary = json.loads(output.with_suffix(".summary.json").read_text())
        self.assertEqual(2, summary["targets"])
        self.assertEqual(0, summary["verified_samples"])
        self.assertEqual(4, summary["missing_samples"])


if __name__ == "__main__":
    unittest.main()
