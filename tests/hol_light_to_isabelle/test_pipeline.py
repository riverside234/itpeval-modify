import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, repo_path, write_jsonl
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.generate_draft import generate_drafts
from eval.pipeline.hol_light_to_isabelle.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.verify_isabelle import verify_sketches


class PipelineTests(unittest.TestCase):
    def test_single_target_handoff_and_resume(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="v2-pipeline-test-", dir=base) as directory:
            root = Path(directory)
            records = root / "records.jsonl"
            drafts = root / "drafts.jsonl"
            sketches = root / "sketches.jsonl"
            verified = root / "verified.jsonl"
            write_jsonl(records, extract_records(
                topic="circle_average", target_key="circleAverage_center_independent"))
            with patch("eval.pipeline.hol_light_to_isabelle.generate_draft.call_draft_model",
                       return_value="### Step 1\nUse integral_shift.") as draft_model, patch(
                "eval.pipeline.hol_light_to_isabelle.generate_sketch.call_draft_model",
                return_value="by simp") as sketch_model, patch(
                "eval.pipeline.hol_light_to_isabelle.verify_isabelle.run_itp",
                return_value=SimpleNamespace(ok=True, stderr="", stdout="",
                                             returncode=0, duration_ms=20)) as prover:
                self.assertEqual(1, generate_drafts(input_path=str(records),
                                                     output_path=str(drafts)))
                self.assertEqual(2, generate_sketches(input_path=str(drafts),
                                                       output_path=str(sketches), samples=2))
                first = verify_sketches(input_path=str(sketches),
                                        output_path=str(verified), limit=1)
                self.assertEqual(2, len(first))
                self.assertTrue(all(r["verified"] for r in first))
                self.assertEqual(0, generate_drafts(input_path=str(records),
                                                     output_path=str(drafts)))
                self.assertEqual(0, generate_sketches(input_path=str(drafts),
                                                       output_path=str(sketches), samples=2))
                verify_sketches(input_path=str(sketches), output_path=str(verified),
                                limit=1)
                self.assertEqual(1, draft_model.call_count)
                self.assertEqual(2, sketch_model.call_count)
                self.assertEqual(2, prover.call_count)


if __name__ == "__main__":
    unittest.main()
