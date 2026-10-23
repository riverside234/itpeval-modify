import importlib
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, read_jsonl, repo_path, write_jsonl
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.v2_itpeval.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.v2_itpeval.runtime import isabelle2024_runtime
from eval.pipeline.hol_light_to_isabelle.v2_itpeval.verify_isabelle import verify_sketches


PREFIX = "eval.pipeline.hol_light_to_isabelle.v2_itpeval."
RUNTIME = {"prefix": ".", "isabelle_version": "Isabelle2024"}


class PolishTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="itpeval-test-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.record = extract_records(topic="circle_average",
                                      target_key="circleAverage_center_independent")[0]
        self.record["draft"] = "Unfold the definitions and apply integral_shift."

    def test_legacy_imports_are_the_actual_moved_modules(self):
        for name in ("generate_sketch", "verify_isabelle", "sketch_prompt"):
            self.assertIs(importlib.import_module(PREFIX + name), importlib.import_module(
                "eval.pipeline.hol_light_to_isabelle." + name))

    def test_version_mismatch_is_rejected(self):
        with patch("pathlib.Path.is_file", return_value=True), patch(
            PREFIX + "runtime.subprocess.run", return_value=SimpleNamespace(stdout="Isabelle2023\n")
        ):
            with self.assertRaisesRegex(ValueError, "requires Isabelle2024"):
                isabelle2024_runtime()

    def test_failed_drafts_produce_failure_rows_without_api_calls(self):
        source, output = self.root / "drafts.jsonl", self.root / "sketches.jsonl"
        write_jsonl(source, [{**self.record, "draft": "", "draft_error": "API failed"}])
        with patch(PREFIX + "generate_sketch.call_draft_model") as model:
            self.assertEqual(2, generate_sketches(
                input_path=str(source), output_path=str(output), samples=2))
        model.assert_not_called()
        rows = read_jsonl(output)
        self.assertEqual(2, len(rows))
        self.assertTrue(all(row["failure_category"] == "input_error" for row in rows))

    def test_draft_change_invalidates_sketch_resume(self):
        source, output = self.root / "drafts.jsonl", self.root / "sketches.jsonl"
        write_jsonl(source, [self.record])
        with patch(PREFIX + "generate_sketch.call_draft_model", return_value="by simp") as model:
            self.assertEqual(1, generate_sketches(input_path=str(source), output_path=str(output)))
            self.assertEqual(0, generate_sketches(input_path=str(source), output_path=str(output)))
            write_jsonl(source, [{**self.record, "draft": "A changed Draft"}])
            self.assertEqual(1, generate_sketches(input_path=str(source), output_path=str(output)))
            write_jsonl(source, [self.record])
            self.assertEqual(0, generate_sketches(input_path=str(source), output_path=str(output)))
            self.assertEqual(self.record["draft"], read_jsonl(output)[-1]["draft"])
        self.assertEqual(2, model.call_count)

    def test_failed_context_is_reported_without_an_api_call(self):
        from eval.pipeline.hol_light_to_isabelle.common import key
        source, output = self.root / "drafts.jsonl", self.root / "sketches.jsonl"
        write_jsonl(source, [self.record])
        with patch(PREFIX + "generate_sketch.call_draft_model") as model:
            generate_sketches(input_path=str(source), output_path=str(output),
                              blocked_targets={key(self.record): "theory failed to load"})
        model.assert_not_called()
        self.assertEqual("context_error", read_jsonl(output)[0]["failure_category"])

    def test_changed_statement_or_backend_does_not_reuse_verification(self):
        source, output = self.root / "sketches.jsonl", self.root / "verified.jsonl"
        row = {**self.record, "pipeline": "v2-itpeval", "sample_idx": 0,
               "isabelle_proof": "by simp"}
        write_jsonl(source, [row])
        compiled = SimpleNamespace(ok=True, stderr="", stdout="", duration_ms=1, returncode=0)
        with patch(PREFIX + "verify_isabelle.isabelle2024_runtime", return_value=RUNTIME), patch(
            PREFIX + "verify_isabelle.run_itp", return_value=compiled
        ) as prover:
            self.assertTrue(verify_sketches(input_path=str(source), output_path=str(output))[0]["verified"])
            verify_sketches(input_path=str(source), output_path=str(output))
            self.assertEqual(1, prover.call_count)
            write_jsonl(source, [{**row, "isabelle_statement": 'lemma fake: "False"'}])
            self.assertFalse(verify_sketches(input_path=str(source), output_path=str(output))[0]["verified"])
            write_jsonl(source, [{**row, "pipeline": "v2-dsp"}])
            self.assertFalse(verify_sketches(input_path=str(source), output_path=str(output))[0]["verified"])
            self.assertEqual(1, prover.call_count)

    def test_sample_bound_and_saved_draft_are_enforced_during_reverify(self):
        source, output = self.root / "sketches.jsonl", self.root / "verified.jsonl"
        write_jsonl(source, [{**self.record, "sample_idx": 0, "draft": "stale",
                             "isabelle_proof": "by simp"}])
        with patch(PREFIX + "verify_isabelle.isabelle2024_runtime", return_value=RUNTIME), patch(
            PREFIX + "verify_isabelle.run_itp"
        ) as prover:
            rows = verify_sketches(input_path=str(source), output_path=str(output),
                                   expected=[self.record], expected_samples=2)
        self.assertEqual(2, len(rows))
        self.assertTrue(all(not row["verified"] for row in rows))
        prover.assert_not_called()

    def test_reverifying_one_target_preserves_other_saved_results(self):
        source, output = self.root / "sketches.jsonl", self.root / "verified.jsonl"
        other = extract_records(topic="circle_average", target_key="circleAverage_center_eq")[0]
        rows = [{**row, "sample_idx": 0, "isabelle_proof": "by simp"}
                for row in (self.record, other)]
        write_jsonl(source, rows)
        compiled = SimpleNamespace(ok=True, stderr="", stdout="", duration_ms=1, returncode=0)
        with patch(PREFIX + "verify_isabelle.isabelle2024_runtime", return_value=RUNTIME), patch(
            PREFIX + "verify_isabelle.run_itp", return_value=compiled
        ):
            verify_sketches(input_path=str(source), output_path=str(output))
            verify_sketches(input_path=str(source), output_path=str(output),
                            target_key=self.record["target_key"])
        self.assertEqual(2, len(read_jsonl(output)))


if __name__ == "__main__":
    unittest.main()
