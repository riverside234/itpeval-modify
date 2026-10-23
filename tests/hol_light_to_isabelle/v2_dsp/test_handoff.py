import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, read_jsonl, repo_path, write_jsonl
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import export_drafts, export_record
from eval.pipeline.hol_light_to_isabelle.v2_dsp.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.v2_dsp.sketch_prompt import build_sketch_prompt


class HandoffTests(unittest.TestCase):
    def setUp(self):
        self.record = extract_records(topic="circle_average",
                                      target_key="circleAverage_center_independent")[0]
        self.record["draft"] = "DRAFT_MARKER: unfold the definitions and use integral_shift."

    def test_export_retains_exact_draft_and_hides_api_prompt_fields(self):
        record = export_record({**self.record, "system_prompt": "secret", "user_prompt": "secret"})
        self.assertEqual(self.record["draft"], record["informal_proof"])
        self.assertEqual(self.record["isabelle_statement"], record["formal_statement"])
        self.assertEqual("v2-dsp", record["pipeline"])
        self.assertNotIn("system_prompt", record)
        self.assertNotIn("user_prompt", record)

    def test_missing_or_failed_drafts_are_rejected(self):
        for changed in ({"draft": ""}, {"draft_error": "failed"}):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                export_record({**self.record, **changed})

    def test_sketch_prompt_uses_only_draft_oracle_and_masked_context(self):
        record = export_record(self.record)
        record["hol_light_proof"] = "SOURCE_PROOF_SECRET"
        record["isabelle_theory_template"] = "FULL_TEMPLATE_SECRET"
        prompt = build_sketch_prompt(record)
        self.assertIn("DRAFT_MARKER", prompt.user_prompt)
        self.assertNotIn("SOURCE_PROOF_SECRET", prompt.user_prompt)
        self.assertNotIn("FULL_TEMPLATE_SECRET", prompt.user_prompt)
        self.assertIn("standalone sledgehammer", prompt.system_prompt)
        self.assertNotIn("DSP", prompt.system_prompt + prompt.user_prompt)

    def test_export_generate_resume_and_changed_draft(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="dsp-handoff-", dir=base) as folder:
            source, exported, sketches = (Path(folder) / name for name in (
                "drafts.jsonl", "input.jsonl", "sketches.jsonl"))
            write_jsonl(source, [self.record])
            export_drafts(input_path=str(source), output_path=str(exported))
            with patch("eval.pipeline.hol_light_to_isabelle.v2_dsp.generate_sketch.call_draft_model",
                       return_value="proof -\n show ?thesis\n sledgehammer\nqed") as model:
                self.assertEqual(2, generate_sketches(
                    input_path=str(exported), output_path=str(sketches), samples=2))
                self.assertEqual(0, generate_sketches(
                    input_path=str(exported), output_path=str(sketches), samples=2))
                write_jsonl(source, [{**self.record, "draft": "Changed saved Draft."}])
                export_drafts(input_path=str(source), output_path=str(exported))
                self.assertEqual(2, generate_sketches(
                    input_path=str(exported), output_path=str(sketches), samples=2))
            self.assertEqual(4, model.call_count)
            self.assertEqual(4, len(read_jsonl(sketches)))


if __name__ == "__main__":
    unittest.main()
