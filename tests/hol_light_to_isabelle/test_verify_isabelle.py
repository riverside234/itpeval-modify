import unittest
from types import SimpleNamespace
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.verify_isabelle import (
    compose_theory, normalize_proof, preflight, summarize, verify_record,
)


class VerifyTests(unittest.TestCase):
    def test_rejects_admission_and_declaration_injection(self):
        for proof in ("by sorry", "proof -\n  sorry\nqed", "lemma fake: True by simp",
                      "by simp\naxiomatization x :: bool", "by simp\nend"):
            with self.subTest(proof=proof), self.assertRaises(ValueError):
                normalize_proof(proof)

    def test_replaces_only_selected_target(self):
        record, = extract_records(topic="circle_average",
                                  target_key="circleAverage_center_independent")
        original_count = record["isabelle_theory_template"].count("sorry")
        theory = compose_theory(record, "by simp")
        self.assertEqual(original_count - 1, theory.count("sorry"))
        self.assertIn("by simp", theory)
        self.assertIn("lemma circleAverage_center_eq", theory)

    def test_compiler_result_is_recorded(self):
        record, = extract_records(topic="circle_average",
                                  target_key="circleAverage_center_independent")
        record["isabelle_proof"] = "by simp"
        with patch("eval.pipeline.hol_light_to_isabelle.verify_isabelle.run_itp") as run:
            run.return_value = SimpleNamespace(ok=False, stderr="proof failed", stdout="",
                                               returncode=1, duration_ms=20)
            result = verify_record(record)
        self.assertFalse(result["verified"])
        self.assertIn("proof failed", result["verify_error"])
        run.assert_called_once()

    def test_summary_counts_targets_across_samples(self):
        base = {"source": "babel-formal", "theorem_id": 1,
                "topic": "circle_average", "target_key": "x"}
        rows = [
            {**base, "sample_idx": 0, "verified": False, "verify_error": "failed"},
            {**base, "sample_idx": 1, "verified": True, "verify_error": ""},
            {**base, "target_key": "y", "sample_idx": 0,
             "verified": True, "verify_error": ""},
        ]
        summary = summarize(rows)
        self.assertEqual(2, summary["targets"])
        self.assertEqual(0.5, summary["pass_at_1"])
        self.assertEqual(1.0, summary["pass_at_k"])

    def test_preflight_checks_baseline_and_negative_control(self):
        record, = extract_records(topic="circle_average",
                                  target_key="circleAverage_center_independent")
        good = SimpleNamespace(ok=True, stderr="", stdout="", returncode=0,
                               duration_ms=20)
        bad = SimpleNamespace(ok=False, stderr="expected failure", stdout="",
                              returncode=1, duration_ms=20)
        with patch("eval.pipeline.hol_light_to_isabelle.verify_isabelle.run_itp",
                   side_effect=[good, bad]) as prover:
            result = preflight(record)
        self.assertTrue(result["baseline_ok"])
        self.assertTrue(result["negative_control_failed"])
        self.assertEqual(2, prover.call_count)


if __name__ == "__main__":
    unittest.main()
