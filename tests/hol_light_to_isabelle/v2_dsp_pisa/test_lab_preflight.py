"""Offline scope and report-preservation tests for the PISA acceptance run."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa import lab_preflight as lab
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.acceptance import case_problems, proof_cases
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.runtime import DspConfig, PisaFailure

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


class LabReportTests(unittest.TestCase):
    def setUp(self):
        base=repo_path(RESULTS_DIR)
        base.mkdir(parents=True,exist_ok=True)
        self.temp=tempfile.TemporaryDirectory(prefix="pisa-report-",dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path=Path(self.temp.name)
        self.records=[row(prefix="fixture")]
        self.scope={"selection":"fixture","selected_contexts":1}
        self.config=DspConfig()
        self.backend={"backend_fingerprint":"fixture","backend":"dsp-pisa","isabelle_version":"Isabelle2021"}
        self.load=self.mock(lab.DspConfig,"load",return_value=self.config)
        self.metadata=self.mock(lab.DspConfig,"metadata",return_value=self.backend)
        self.proof=self.mock(lab,"run_proof_case",return_value={"ok":True})
        self.context=self.mock(lab.Checker,"check_context",return_value={"baseline_ok":True})

    def mock(self,obj,name,**kwargs):
        patcher=patch.object(obj,name,**kwargs)
        result=patcher.start()
        self.addCleanup(patcher.stop)
        return result

    def run_lab(self,**kwargs):
        return lab.run_lab_preflight(config_path="fixture.json",records=self.records,scope=self.scope,
                                     output_root=str(self.path/"reports"),**kwargs)

    def test_success_has_one_setup_and_portable_bundle(self):
        def proof(case,*,directory,**options):
            directory.mkdir(parents=True,exist_ok=True)
            (directory/"input.json").write_text("{}",encoding="utf-8")
            (directory/"pisa-server.log").write_text("fixture output",encoding="utf-8")
            return {"ok":True}
        self.proof.side_effect=proof
        result=self.run_lab()
        self.assertTrue(result["ok"])
        self.metadata.assert_called_once()
        self.assertEqual(17,self.proof.call_count)
        self.assertEqual(len(result["planned_checks"]),len(result["checks"]))
        directory=Path(result["report_directory"])
        self.assertEqual(result,json.loads((directory/"report.json").read_text()))
        with zipfile.ZipFile(directory/"diagnostics.zip") as bundle:
            names=set(bundle.namelist())
            self.assertTrue({"report.json","summary.md","config.json","backend.json","events.jsonl"}<=names)
            self.assertIn("cases/normalhammer/pisa-server.log",names)
            self.assertIn("transport/input.json",names)
            self.assertFalse(any("replay" in name for name in names))

    def test_failed_transport_blocks_dependents_without_repeated_startup(self):
        self.proof.return_value={"ok":False,"error":"startup failed"}
        result=self.run_lab()
        self.assertFalse(result["ok"])
        self.proof.assert_called_once()
        self.context.assert_not_called()
        self.assertEqual(17,result["counts"]["blocked"])

    def test_bad_configuration_still_saves_a_report_and_bundle(self):
        self.load.side_effect=ValueError("native config retired")
        result=self.run_lab()
        self.assertFalse(result["backend_ok"])
        self.proof.assert_not_called()
        self.assertTrue((Path(result["report_directory"])/"diagnostics.zip").is_file())

    def test_failed_control_does_not_skip_other_controls_or_dataset_contexts(self):
        self.proof.side_effect=[{"ok":True},RuntimeError("control failed")]+[{"ok":True}]*15
        result=self.run_lab()
        self.assertFalse(result["backend_ok"])
        self.assertTrue(result["contexts_ok"])
        self.assertEqual(17,self.proof.call_count)
        self.context.assert_called_once()

    def test_dataset_dependency_failure_is_separate_from_backend_health(self):
        self.context.side_effect=PisaFailure("context_error","missing dependency")
        result=self.run_lab()
        self.assertTrue(result["backend_ok"])
        self.assertFalse(result["contexts_ok"])
        self.assertFalse(result["ok"])
        self.assertEqual("context_error",result["checks"][-1]["failure_category"])

    def test_interrupt_preserves_completed_checks_and_blocks_unrun_cases(self):
        self.proof.side_effect=[{"ok":True},KeyboardInterrupt]
        result=self.run_lab()
        self.assertEqual("interrupted",result["status"])
        self.assertFalse(result["ok"])
        self.assertEqual(len(result["planned_checks"]),len(result["checks"]))
        self.assertTrue((Path(result["report_directory"])/"diagnostics.zip").is_file())

    def test_selection_error_is_not_hidden_by_successful_contexts(self):
        result=self.run_lab(selection_issues=[{"error":"incomplete input"}])
        self.assertFalse(result["ok"])
        self.assertTrue(result["backend_ok"])

    def test_archive_failure_cannot_report_success(self):
        with patch.object(lab.zipfile,"ZipFile",side_effect=OSError("disk full")):
            result=self.run_lab()
        self.assertFalse(result["ok"])
        self.assertIn("disk full",result["bundle_error"])

    def test_output_cannot_escape_repository(self):
        with self.assertRaisesRegex(ValueError,"path must be under"):
            lab.Report("../outside",self.scope)


class ExpectationTests(unittest.TestCase):
    def test_negative_control_requires_exact_failure(self):
        case=next(c for c in proof_cases() if c.name=="invalid_method")
        self.assertFalse(case_problems(case,{"verified":False,"failure_category":"proof_failure"}))
        self.assertTrue(case_problems(case,{"verified":False,"failure_category":"worker_failure"}))

    def test_hammer_control_requires_executed_upstream_hammer(self):
        case=next(c for c in proof_cases() if c.name=="normalhammer")
        result={"verified":True,"prove_success":True,"step_results":[{"mode":"hammer","success":True,"observation":"by metis <hammer> done"}]}
        self.assertFalse(case_problems(case,result))
        self.assertTrue(case_problems(case,{**result,"step_results":[]}))
        self.assertTrue(case_problems(case,{**result,"replay_verified":True}))


if __name__ == "__main__":
    unittest.main()
