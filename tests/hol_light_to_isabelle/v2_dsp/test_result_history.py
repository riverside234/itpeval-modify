"""Keep repeated experiments separate when their JSONL histories share a path."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    RESULTS_DIR, read_jsonl, repo_path, write_jsonl,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.input_contract import (
    align_samples, load_inputs, save_results,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record

MODULE = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp."


class ResultHistoryTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        folder = tempfile.TemporaryDirectory(prefix="dsp-result-history-", dir=base)
        self.addCleanup(folder.cleanup)
        self.path = Path(folder.name)
        self.row = {
            **control_record("by simp"), "sample_idx": 0,
            "sketch_model": {"provider": "openai", "model": "old", "reasoning_effort": "medium"},
            "sketch_prompt_version": "old-prompt", "sketch_prompt_sha256": "old-prompt-hash",
            "sketch_validator_version": "old-validator",
            "draft_model": {"model": "old-draft"}, "draft_fingerprint": "old-draft-id",
        }

    def test_latest_settings_do_not_borrow_old_sample_indices(self):
        changes = (
            {"sketch_model": {"model": "new"}},
            {"sketch_prompt_version": "new-prompt", "sketch_prompt_sha256": "new-hash"},
            {"sketch_validator_version": "new-validator"},
            {"draft": "Changed mathematical argument."},
            {"draft_model": {"model": "new-draft"}, "draft_fingerprint": "new-draft-id"},
        )
        for change in changes:
            with self.subTest(change=change):
                latest = {**self.row, **change, "isabelle_sketch": "", "sketch_error": "failed new sample"}
                source = self.path / "sketches.jsonl"
                write_jsonl(source, [self.row, {**self.row, "sample_idx": 1}, latest])
                selected = load_inputs(source, mode="draft", samples=True, artifacts=True)
                self.assertEqual([latest], selected)
                aligned = align_samples(selected, [latest], 2, mode="draft")
                self.assertEqual("failed new sample", aligned[0]["sketch_error"])
                self.assertEqual("missing_sketch", aligned[1]["failure_category"])

    def test_direct_mode_groups_source_proofs_without_draft_metadata(self):
        mode = "hol-light-proof"
        old = {**control_record("by simp", sketch_source=mode),
               "sketch_model": self.row["sketch_model"], "sample_idx": 0}
        current = {**old, "hol_light_proof": "REWRITE_TAC[]"}
        source = self.path / "direct.jsonl"
        write_jsonl(source, [old, {**old, "sample_idx": 1}, current])
        self.assertEqual([current], load_inputs(source, mode=mode, samples=True))
        aligned = align_samples([current], [current], 2, mode=mode)
        self.assertEqual("missing_sketch", aligned[1]["failure_category"])

    def test_same_settings_keep_samples_and_latest_failure(self):
        source = self.path / "sketches.jsonl"
        second = {**self.row, "sample_idx": 1}
        failure = {**self.row, "isabelle_sketch": "", "sketch_error": "latest failure"}
        write_jsonl(source, [self.row, second, failure])
        self.assertEqual([failure, second], load_inputs(source, mode="draft", samples=True))

    def test_missing_sample_placeholder_does_not_hide_successful_samples_on_reload(self):
        expected = {name: value for name, value in self.row.items()
                    if not name.startswith("sketch_") and name not in {"sample_idx", "isabelle_sketch"}}
        rows = align_samples([self.row], [expected], 2, mode="draft")
        self.assertEqual("missing_sketch", rows[1]["failure_category"])
        source = self.path / "prove.jsonl"
        write_jsonl(source, rows)
        self.assertEqual(rows, load_inputs(source, mode="draft", samples=True, artifacts=True))

    def test_reducing_k_removes_old_successes_only_for_selected_targets(self):
        path = self.path / "verified.jsonl"
        failure = {**self.row, "verified": False, "failure_category": "sketch_error"}
        old_success = {**self.row, "sample_idx": 1, "verified": True}
        unrelated = {**self.row, "target_key": "unrelated", "verified": True}
        write_jsonl(path, [failure, old_success, unrelated])
        summary = save_results(path, [failure], mode="draft", preserve_unselected=True,
                               expected=[self.row], expected_samples=1)
        self.assertEqual([unrelated, failure], read_jsonl(path))
        self.assertEqual(0, summary["pass_at_k"])
        self.assertEqual("current_selection", summary["summary_scope"])
        self.assertEqual(2, summary["stored_samples"])

    def test_same_draft_text_from_a_new_generation_is_not_misattributed(self):
        source, output = self.path / "drafts.jsonl", self.path / "sketches.jsonl"
        write_jsonl(source, [self.row])
        options = dict(input_path=source, output_path=output)
        with patch(MODULE + "generate_sketch.call_draft_model", return_value="by simp") as model:
            self.assertEqual(1, generate_sketches(**options))
            old = read_jsonl(output)[-1]
            current = {**self.row, "draft_model": {"model": "new-draft"}, "draft_fingerprint": "new-draft-id"}
            write_jsonl(source, [current])
            self.assertEqual(1, generate_sketches(**options))
            self.assertEqual(0, generate_sketches(**options))
            self.assertEqual(2, model.call_count)
        self.assertEqual(current["draft_model"], read_jsonl(output)[-1]["draft_model"])
        self.assertEqual("missing_sketch", align_samples([old], [current], 1, mode="draft")[0]["failure_category"])

    def test_summary_reports_actual_settings_and_search_activity(self):
        explicit = {**self.row, "verified": True,
                    "native_search": {"success": True},
                    "step_results": [{"mode": "search", "success": True}],
                    "draft_response": {"usage": {"input_tokens": 20}},
                    "sketch_response": {"usage": {"input_tokens": 30}}}
        gaps = {**explicit, "sample_idx": 1, "step_results": [
            {"mode": "heuristic", "success": False}, {"mode": "hammer", "success": True},
            {"mode": "reconstruction", "success": True}]}
        summary = save_results(self.path / "verified.jsonl", [explicit, gaps], mode="draft")
        self.assertEqual([self.row["sketch_model"]], summary["llm_profiles"]["sketch"])
        self.assertEqual([self.row["draft_model"]], summary["llm_profiles"]["draft"])
        activity = summary["search_activity"]
        self.assertEqual(2, activity["samples_with_pisa_search"])
        self.assertEqual(1, activity["samples_with_gap_filling"])
        self.assertEqual(1, activity["samples_with_sledgehammer"])
        self.assertEqual(1, activity["sledgehammer_calls"])
        self.assertEqual(1, activity["heuristic_attempts"])
        self.assertEqual(1, activity["reconstruction_attempts"])
        self.assertEqual(20, summary["llm_usage"]["draft"]["input_tokens"])
        self.assertEqual(60, summary["llm_usage"]["sketch"]["input_tokens"])


if __name__ == "__main__":
    unittest.main()
