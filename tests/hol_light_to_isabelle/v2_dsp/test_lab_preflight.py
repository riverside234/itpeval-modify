"""Offline tests for acceptance scope, failure accounting and portable diagnostics."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import lab_preflight as lab
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import (
    FIXTURE, PreparedNative, case_problems, proof_cases,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import NativeFailure, NativeSearch
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig


def row(topic="test_topic", target="test_target", prefix="", source="babel-formal"):
    return {**control_record("by simp", source=source), "topic": topic, "target_key": target,
            "isabelle_context_before_target": prefix}


class SelectionTests(unittest.TestCase):
    def test_default_selects_largest_prefix_and_historical_sentinels(self):
        records = [row("circle_average", "first", "x"),
                   row("circle_average", "last", "x" * 100),
                   row("circle_average", "circleAverage_center_independent", "xx"),
                   row("another_topic", "last", "xxx")]
        with patch.object(lab, "latest_records", return_value=records):
            selected, scope, issues = lab.discover_records(inputs=["records.jsonl"])
        self.assertFalse(issues)
        self.assertEqual(4, scope["available_targets"])
        self.assertEqual(2, scope["selected_topics"])
        self.assertEqual({("circle_average", "last"), ("circle_average", "circleAverage_center_independent"),
                          ("another_topic", "last")}, {(r["topic"], r["target_key"]) for r in selected})

    def test_all_targets_and_dataset_filters_have_explicit_scope(self):
        records = [row(target="a"), row(target="b"), row(source="hundred-theorems")]
        with patch.object(lab, "latest_records", return_value=records):
            selected, scope, issues = lab.discover_records(inputs=["rows"], dataset="babel-formal", all_targets=True)
        self.assertFalse(issues)
        self.assertEqual(2, len(selected))
        self.assertEqual("all_targets", scope["selection"])
        with patch.object(lab, "latest_records", return_value=records):
            selected, _, issues = lab.discover_records(inputs=["rows"], target_key="b")
        self.assertFalse(issues)
        self.assertEqual(["b"], [r["target_key"] for r in selected])

    def test_conflicting_duplicates_and_empty_selection_cannot_pass(self):
        records = [row(prefix="a"), row(prefix="different")]
        with patch.object(lab, "latest_records", side_effect=[[records[0]], [records[1]]]):
            selected, _, issues = lab.discover_records(inputs=["first", "second"])
        self.assertEqual(1, len(selected))
        self.assertIn("conflicting duplicate", issues[0]["error"])
        with patch.object(lab, "latest_records", return_value=[]):
            selected, _, issues = lab.discover_records(inputs=["empty"])
        self.assertFalse(selected)
        self.assertIn("empty dataset scope", issues[0]["error"])

    def test_unreadable_input_is_reported_even_if_another_file_is_usable(self):
        with patch.object(lab, "latest_records", side_effect=[ValueError("bad JSON"), [row()]]):
            selected, _, issues = lab.discover_records(inputs=["broken", "valid"])
        self.assertEqual(1, len(selected))
        self.assertEqual("broken", issues[0]["input"])


class CaseExpectationTests(unittest.TestCase):
    def setUp(self):
        self.cases = {c.name: c for c in proof_cases()}

    def test_catalog_contains_executed_using_and_external_atp_controls(self):
        self.assertEqual(26, len(self.cases))
        self.assertEqual("using h by metis", self.cases["using_reconstruction"].candidate)
        self.assertIn("\n", self.cases["using_reconstruction_comments"].candidate)
        self.assertEqual(("e",), self.cases["hammer_external_e"].provers)
        self.assertTrue(FIXTURE.is_file())

    def test_negative_controls_require_specific_failure_and_no_replay(self):
        case = self.cases["partial_goal_rejected"]
        result = {"verified": False, "prove_success": False, "failure_category": "missing_reconstruction",
                  "step_results": [{"mode": "reconstruction", "command": "apply simp", "success": True}]}
        self.assertFalse(case_problems(case, result))
        for change in ({"failure_category": "toolchain_error"}, {"native_replay": {}},
                       {"prove_success": True}, {"replay_verified": True}, {"step_results": []}):
            with self.subTest(change=change):
                self.assertTrue(case_problems(case, {**result, **change}))

    def test_using_control_requires_execution_and_fresh_replay(self):
        case = self.cases["using_reconstruction"]
        result = {"verified": True, "prove_success": True, "replay_verified": True, "step_results": [
            {"mode": "heuristic", "success": True, "command": case.candidate}]}
        self.assertFalse(case_problems(case, result))
        self.assertTrue(case_problems(case, {**result, "step_results": []}))
        self.assertTrue(case_problems(case, {**result, "replay_verified": False}))

    def test_external_atp_requires_played_reconstruction(self):
        case = self.cases["hammer_external_e"]
        result = {"verified": True, "prove_success": True, "replay_verified": True,
                  "prover_settings": {"reconstruction_source": "preplayed", "preplayed_count": "1"},
                  "step_results": [{"mode": "hammer", "success": True},
                                   {"mode": "reconstruction", "command": "by metis", "success": True}]}
        self.assertFalse(case_problems(case, result))
        self.assertTrue(case_problems(case, {**result, "prover_settings": {
            "reconstruction_source": "native_tactic", "preplayed_count": "0"}}))

    def test_corrupted_replay_control_must_first_prove_the_target(self):
        case = self.cases["corrupted_replay_rejected"]
        result = {"verified": False, "prove_success": True, "failure_category": "replay_failure"}
        self.assertFalse(case_problems(case, result))
        self.assertTrue(case_problems(case, {**result, "prove_success": False}))

    def test_prepared_parent_and_injected_candidate_use_real_adapter_path(self):
        parent = (Path("prepared-parent"), "PreparedSession")
        native = PreparedNative(DspConfig(), parent, candidate="using h by metis", corrupt_replay=True)
        with patch.object(NativeSearch, "infrastructure") as infrastructure, \
             patch.object(NativeSearch, "request", return_value={"success": True}) as request, \
             patch.object(NativeSearch, "replay", return_value={"success": False}) as replay:
            self.assertEqual(parent, native.infrastructure(deadline=10))
            infrastructure.assert_not_called()
            native.request({}, "sketch", action="search", heuristics=(), directory=Path("job"), deadline=10)
            self.assertEqual(("using h by metis",), request.call_args.kwargs["heuristics"])
            native.request({}, "", action="context", heuristics=(), directory=Path("context"), deadline=10)
            self.assertEqual((), request.call_args.kwargs["heuristics"])
            native.replay({}, "by simp", directory=Path("replay"), deadline=10)
            self.assertEqual("by (dsp_invalid_replay_method)", replay.call_args.args[1])


class LabReportTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="lab-report-test-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.parent = self.path / "prepared"
        self.parent.mkdir()
        (self.parent / "ROOT").write_text("fixture parent", encoding="utf-8")
        (self.parent / "build.log").write_text("fixture infrastructure log", encoding="utf-8")
        (self.parent / "DSP_Native.ML").write_text("fixture adapter", encoding="utf-8")
        (self.parent / "huge.heap").write_text("must not be copied", encoding="utf-8")
        self.records = [row(prefix="fixture")]
        self.scope = {"selection": "fixture", "selected_contexts": 1}
        self.config = DspConfig()
        self.backend = {"backend_fingerprint": "fixture", "isabelle_version": "Isabelle2026"}
        self.load = self.mock(lab.DspConfig, "load", return_value=self.config)
        self.metadata = self.mock(lab.DspConfig, "metadata", return_value=self.backend)
        self.infrastructure = self.mock(lab.NativeSearch, "infrastructure", return_value=(self.parent, "Prepared"))
        self.fixture = self.mock(lab, "run_fixture", return_value={"ok": True})
        self.proof = self.mock(lab, "run_proof_case", return_value={"ok": True})
        self.context = self.mock(lab.Checker, "check_context", return_value={"baseline_ok": True})

    def mock(self, obj, name, **options):
        patcher = patch.object(obj, name, **options)
        result = patcher.start()
        self.addCleanup(patcher.stop)
        return result

    def run_lab(self, **options):
        return lab.run_lab_preflight(config_path="fixture.json", records=self.records, scope=self.scope,
                                      output_root=str(self.path / "reports"), **options)

    def test_success_has_single_setup_and_complete_portable_bundle(self):
        def proof(case, *, directory, **options):
            directory.mkdir(parents=True, exist_ok=True)
            (directory / "input.json").write_text('{"request_id":"fixture"}', encoding="utf-8")
            (directory / "build.log").write_text("native output", encoding="utf-8")
            return {"ok": True}
        self.proof.side_effect = proof
        result = self.run_lab()
        self.assertTrue(result["ok"])
        self.metadata.assert_called_once()
        self.infrastructure.assert_called_once()
        self.assertEqual(26, self.proof.call_count)
        self.assertEqual(len(result["planned_checks"]), len(result["checks"]))
        directory = Path(result["report_directory"])
        self.assertEqual(result, json.loads((directory / "report.json").read_text(encoding="utf-8")))
        with zipfile.ZipFile(directory / "diagnostics.zip") as bundle:
            names = set(bundle.namelist())
            self.assertTrue({"summary.md", "report.json", "config.json", "backend.json", "events.jsonl",
                             "release_sources.json", "infrastructure/ROOT", "infrastructure/build.log"} <= names)
            self.assertIn("cases/using_reconstruction/input.json", names)
            self.assertIn("cases/using_reconstruction/build.log", names)
            self.assertFalse(any("huge.heap" in name for name in names))

    def test_setup_failure_is_reported_once_and_all_dependents_are_blocked(self):
        self.infrastructure.side_effect = NativeFailure("capability_error", "fixture compile failure",
            details={"build_log_path": str(self.parent / "build.log")})
        result = self.run_lab()
        self.assertFalse(result["ok"])
        self.infrastructure.assert_called_once()
        self.proof.assert_not_called()
        self.context.assert_not_called()
        self.assertEqual(1, result["counts"]["fail"])
        self.assertEqual(28, result["counts"]["blocked"])
        self.assertTrue((Path(result["report_directory"]) / "infrastructure/build.log").is_file())

    def test_bad_configuration_still_produces_a_report_and_bundle(self):
        self.load.side_effect = ValueError("obsolete config")
        result = self.run_lab()
        self.assertFalse(result["backend_ok"])
        self.infrastructure.assert_not_called()
        self.assertTrue((Path(result["report_directory"]) / "diagnostics.zip").is_file())

    def test_failed_control_does_not_skip_remaining_controls_or_contexts(self):
        self.fixture.return_value = {"ok": False, "error": "fixture failed"}
        self.proof.side_effect = [RuntimeError("one control crashed")] + [{"ok": True}] * 25
        result = self.run_lab()
        self.assertFalse(result["ok"])
        self.assertFalse(result["backend_ok"])
        self.assertTrue(result["contexts_ok"])
        self.assertEqual(26, self.proof.call_count)
        self.context.assert_called_once()

    def test_dataset_failure_is_distinct_from_successful_backend(self):
        self.context.side_effect = NativeFailure("context_error", "missing theory")
        result = self.run_lab()
        self.assertFalse(result["ok"])
        self.assertTrue(result["backend_ok"])
        self.assertFalse(result["contexts_ok"])
        self.assertEqual("context_error", result["checks"][-1]["failure_category"])

    def test_selection_or_export_error_cannot_become_an_all_green_report(self):
        with patch.object(lab, "dataset_cases", side_effect=ValueError("bad sentinel record")):
            result = self.run_lab(selection_issues=[{"error": "input was incomplete"}])
        self.assertFalse(result["ok"])
        self.assertTrue(result["backend_ok"])
        self.context.assert_called_once()
        first = Path(result["report_directory"]) / result["checks"][0]["details"]
        payload = json.loads(first.read_text(encoding="utf-8"))["payload"]
        self.assertEqual(2, len(payload["issues"]))

    def test_interrupt_checkpoints_results_and_marks_unrun_checks_blocked(self):
        self.proof.side_effect = KeyboardInterrupt
        result = self.run_lab()
        self.assertEqual("interrupted", result["status"])
        self.assertFalse(result["ok"])
        self.assertEqual(26, result["counts"]["blocked"])
        self.assertEqual(len(result["planned_checks"]), len(result["checks"]))
        self.assertTrue((Path(result["report_directory"]) / "diagnostics.zip").is_file())

    def test_orchestration_exception_is_finalized_instead_of_losing_the_report(self):
        with patch.object(lab, "proof_cases", side_effect=ValueError("bad catalog")):
            result = self.run_lab()
        self.assertFalse(result["ok"])
        self.assertEqual("orchestration_error", result["checks"][0]["name"])
        self.assertTrue((Path(result["report_directory"]) / "diagnostics.zip").is_file())

    def test_archive_failure_is_not_reported_as_success(self):
        with patch.object(lab.zipfile, "ZipFile", side_effect=OSError("disk full")):
            result = self.run_lab()
        self.assertFalse(result["ok"])
        self.assertIn("disk full", result["bundle_error"])
        self.assertTrue((Path(result["report_directory"]) / "report.json").is_file())

    def test_output_paths_stay_under_the_repository(self):
        with self.assertRaisesRegex(ValueError, "path must be under"):
            lab.Report("../outside-preflight", self.scope)


if __name__ == "__main__":
    unittest.main()
