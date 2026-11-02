"""Regressions from the pulled real-run failures; no model or native calls."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.inference.client import GeneratedText
from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, repo_path, read_jsonl, write_jsonl
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.input_contract import normalize_sketch

MODULE = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa."
FIXTURE = json.loads((Path(__file__).parent / "fixtures/DSP_Sketch_Syntax.json").read_text(encoding="utf-8"))


class SketchSyntaxTests(unittest.TestCase):
    def test_actual_failed_outputs_are_rejected_without_rewriting_them(self):
        for name in ("draft_invalid", "direct_invalid"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "by"):
                normalize_sketch(FIXTURE[name])

    def test_valid_isar_forms_are_not_mistaken_for_indented_tactic_blocks(self):
        proofs = [FIXTURE["draft_corrected"], FIXTURE["direct_corrected"],
                  "by simp", "by standard simp_all", "by (unfold f_def, rule assumption)",
                  "by\n  (simp only: refl)", "by (use assms in auto)",
                  'proof -\n have "True" by simp\n show ?thesis by simp\nqed',
                  'by (fact "have") (* by have qed *)',
                  r'by (fact \<open>by have qed\<close>)']
        for proof in proofs:
            with self.subTest(proof=proof):
                self.assertEqual(proof, normalize_sketch(proof))

    def test_empty_by_and_trailing_outer_commands_are_rejected(self):
        proofs = ["by", "by (* comment *)", 'by\n (* comment *) have "True" by simp\nqed',
                  "by simp\nqed", 'by simp\nhave "True" by simp',
                  'proof -\n have "True" by\n show ?thesis by simp\nqed']
        for proof in proofs:
            with self.subTest(proof=proof), self.assertRaises(ValueError):
                normalize_sketch(proof)

    def test_failed_generations_keep_visible_content_usage_and_failed_samples(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        record = extract_records(topic="circle_average", target_key="circleAverage_center_independent")[0]
        record["draft"] = "Unfold the definitions and apply integral_shift."
        metadata = {"model": "fixture", "usage": {"input_tokens": 20, "output_tokens": 10}}
        with tempfile.TemporaryDirectory(prefix="sketch-syntax-", dir=base) as folder:
            source = Path(folder) / "records.jsonl"
            write_jsonl(source, [record])
            for mode, fixture in [("draft", "draft_invalid"), ("hol-light-proof", "direct_invalid")]:
                with self.subTest(mode=mode):
                    output = Path(folder) / (mode + ".jsonl")
                    response = GeneratedText("<think>HIDDEN_REASONING</think>\n~~~isabelle\n" +
                                             FIXTURE[fixture] + "\n~~~", metadata)
                    with patch(MODULE + "generate_sketch.call_draft_model", return_value=response):
                        generate_sketches(input_path=source, output_path=output,
                                          sketch_source=mode, samples=2)
                    rows = read_jsonl(output)
                    self.assertEqual(2, len(rows))
                    self.assertEqual([0, 1], [row["sample_idx"] for row in rows])
                    for row in rows:
                        self.assertEqual("sketch_error", row["failure_category"])
                        self.assertIn("by", row["sketch_error"])
                        self.assertEqual("", row["isabelle_sketch"])
                        self.assertIn(FIXTURE[fixture], row["sketch_response_content"])
                        self.assertEqual(metadata, row["sketch_response"])
                        self.assertIn("sketch_validator_version", row)
                    self.assertNotIn("HIDDEN_REASONING", output.read_text(encoding="utf-8"))

    def test_changed_validator_invalidates_saved_generation_even_with_same_prompt(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        record = extract_records(topic="circle_average", target_key="circleAverage_center_independent")[0]
        record["draft"] = "Unfold the definitions and apply integral_shift."
        with tempfile.TemporaryDirectory(prefix="sketch-resume-", dir=base) as folder:
            source, output = Path(folder) / "records.jsonl", Path(folder) / "sketches.jsonl"
            write_jsonl(source, [record])
            options = dict(input_path=source, output_path=output)
            with patch(MODULE + "generate_sketch.call_draft_model", return_value="by simp") as model:
                self.assertEqual(1, generate_sketches(**options))
                self.assertEqual(0, generate_sketches(**options))
                with patch(MODULE + "generate_sketch.SKETCH_VALIDATOR_VERSION", "changed-validator"):
                    self.assertEqual(1, generate_sketches(**options))
                self.assertEqual(2, model.call_count)
            rows = read_jsonl(output)
            self.assertEqual(rows[0]["sketch_prompt_sha256"], rows[1]["sketch_prompt_sha256"])
            self.assertNotEqual(rows[0]["sketch_fingerprint"], rows[1]["sketch_fingerprint"])


if __name__ == "__main__":
    unittest.main()
