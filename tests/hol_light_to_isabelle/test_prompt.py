import unittest

from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.prompt import build_draft_prompt
from eval.pipeline.hol_light_to_isabelle.sketch_prompt import build_sketch_prompt


class PromptTests(unittest.TestCase):
    def test_draft_uses_source_proof_and_masked_target_context(self):
        record, = extract_records(topic="circle_average",
                                  target_key="circleAverage_center_independent")
        record["isabelle_theory_template"] += "SECRET_TARGET_PROOF_MARKER"
        prompt = build_draft_prompt(record).user_prompt
        self.assertIn("REWRITE_TAC[circleAverage; circleMap]", prompt)
        self.assertIn("integral_shift", prompt)
        self.assertNotIn("SECRET_TARGET_PROOF_MARKER", prompt)
        self.assertNotIn("Lean 4", prompt)

    def test_sketch_uses_draft_only(self):
        record, = extract_records(topic="circle_average",
                                  target_key="circleAverage_center_independent")
        record["draft"] = "DRAFT_MARKER"
        record["hol_light_proof"] = "SOURCE_PROOF_MARKER"
        prompt = build_sketch_prompt(record).user_prompt
        self.assertIn("DRAFT_MARKER", prompt)
        self.assertNotIn("SOURCE_PROOF_MARKER", prompt)


if __name__ == "__main__":
    unittest.main()
