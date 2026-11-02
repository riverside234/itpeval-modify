"""Regressions for the 57-pass / 8-fail lab report and separated backends."""
import copy
import importlib
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import xml.etree.ElementTree as ET

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import lab_preflight as lab
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import (
    NativeFailure, NativeSearch, RESULT_VERSION, read_result, resolve_imports,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context


class RestoredBackendTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records, cls.scope, cls.issues = lab.discover_records(all_targets=True)

    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="native-restore-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)

    def test_all_262_candidates_remain_in_the_scope_including_core_set(self):
        self.assertFalse(self.issues)
        self.assertEqual(262, len(self.records))
        self.assertEqual(29, self.scope["selected_topics"])
        self.assertEqual(163, sum(r["source"] == "babel-formal" for r in self.records))
        plan = lab.dependency_plan(self.records, DspConfig())
        self.assertEqual(["Cayley_Hamilton", "Pratt_Certificate", "Triangle"], plan["required_afp_sessions"])
        self.assertEqual(24, len(plan["known_inherited_targets"]))
        self.assertEqual(262, sum(len(topic["targets"]) for topic in plan["topics"].values()))

    def test_reported_bare_imports_resolve_without_modifying_dataset_records(self):
        before = copy.deepcopy(self.records)
        plan = lab.dependency_plan(self.records, DspConfig())
        observed = {}
        for topic in plan["topics"].values():
            observed.update(zip(topic["original_imports"], topic["resolved_imports"]))
            self.assertTrue(all(name in {"Main", "Complex_Main"} or "." in name
                                for name in topic["resolved_imports"]))
        self.assertEqual("HOL-Computational_Algebra.Euclidean_Algorithm", observed["Euclidean_Algorithm"])
        self.assertEqual("HOL-Computational_Algebra.Primes", observed["Primes"])
        self.assertEqual("Triangle.Angles", observed["Angles"])
        self.assertEqual("Cayley_Hamilton.Square_Matrix", observed["Square_Matrix"])
        self.assertEqual("HOL.Lattices", observed["Lattices"])
        self.assertEqual("HOL.Boolean_Algebras", observed["Boolean_Algebras"])
        self.assertEqual(before, self.records)

    def test_old_lab_config_gets_missing_mappings_without_restoring_replay(self):
        path = self.path / "legacy.json"
        path.write_text(json.dumps({"backend": "isabelle-native", "replay_timeout_s": 1200,
                                    "theory_imports": {"Lebesgue_Measure": "HOL-Analysis.Lebesgue_Measure"}}))
        config = DspConfig.load(str(path))
        self.assertEqual("HOL", config.base_session)
        self.assertEqual("Triangle.Angles", config.theory_imports["Angles"])
        self.assertNotIn("replay_timeout_s", config.__dict__)
        for banner in ("Isabelle2026", "Isabelle2026: October 2026\n"):
            self.assertEqual("Isabelle2026", config.normalize_isabelle_version(banner))
        for banner in ("Isabelle2026-1", "Isabelle2026-RC3", "Isabelle20260", "Isabelle2021", ""):
            with self.assertRaises(ValueError):
                config.normalize_isabelle_version(banner)

    def test_missing_afp_reports_sessions_before_attempting_a_build(self):
        for topic, session in (("027_", "Triangle"), ("049_", "Cayley_Hamilton"), ("098_", "Pratt_Certificate")):
            row = next(r for r in self.records if r["topic"].startswith(topic))
            native = NativeSearch(DspConfig())
            with self.subTest(session=session), patch.object(native, "infrastructure") as build:
                with self.assertRaises(NativeFailure) as caught:
                    native.request(row, "", directory=self.path / session, action="context", heuristics=(),
                                   deadline=time.monotonic()+10)
                self.assertEqual("import_error", caught.exception.category)
                self.assertIn(session, caught.exception.details["required_afp_sessions"])
                self.assertIn("--afp-root", str(caught.exception))
                build.assert_not_called()

    def test_plurals_in_real_missing_session_error_are_classified_as_import_errors(self):
        (self.path / "build.log").write_text('*** Bad imports session "Pratt_Certificate" for "DSP_Job"\n')
        with self.assertRaises(NativeFailure) as caught:
            read_result(self.path / "result.xml", {}, returncode=2)
        self.assertEqual("import_error", caught.exception.category)
        self.assertIn("Pratt_Certificate", caught.exception.details["build_log_excerpt"])

    def test_success_xml_does_not_hide_a_failed_native_process(self):
        request = {"request_id": "test", "input_sha256": "owned", "action": "search"}
        root = ET.Element("dsp_result", schema=RESULT_VERSION, success="true", target_closed="true", **request)
        for name in ("proof", "category", "error", "attempts", "settings"):
            ET.SubElement(root, name).text = "by simp" if name == "proof" else ""
        path = self.path / "result.xml"
        ET.ElementTree(root).write(path, encoding="utf-8")
        (self.path / "build.log").write_text("*** failed after the worker wrote its result\n")
        result = read_result(path, request, returncode=2)
        self.assertFalse(result["success"])
        self.assertEqual(2, result["build_returncode"])
        self.assertIn("failed after the worker", result["error"])

    def test_native_is_the_default_and_pisa_configs_outputs_and_prompts_stay_separate(self):
        native = DspConfig.load("eval/configs/hol_light_to_isabelle/v2_dsp.example.json")
        pisa_base = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa"
        pisa_cls = importlib.import_module(pisa_base + ".runtime").DspConfig
        pisa = pisa_cls.load("eval/configs/hol_light_to_isabelle/v2_dsp_2021.example.json")
        self.assertEqual("Isabelle2026", native.expected_isabelle_version)
        self.assertEqual("Isabelle2021", pisa.expected_isabelle_version)
        with self.assertRaises(ValueError):
            DspConfig.load("eval/configs/hol_light_to_isabelle/v2_dsp_2021.example.json")
        with self.assertRaises(ValueError):
            pisa_cls.load("eval/configs/hol_light_to_isabelle/v2_dsp_2026.example.json")
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.input_contract import output_path
        pisa_path = importlib.import_module(pisa_base + ".input_contract").output_path
        args = dict(results_dir=RESULTS_DIR, filename="verified.jsonl", mode="draft")
        self.assertNotEqual(output_path(None, **args), pisa_path(None, **args))
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
        for package, version in ((pisa_base, "Isabelle2021"), (pisa_base.removesuffix("_pisa"), "Isabelle2026")):
            control = importlib.import_module(package + ".preflight").control_record("by simp")
            prompt = importlib.import_module(package + ".sketch_prompt").build_sketch_prompt(control)
            self.assertIn(version, prompt.system_prompt)


if __name__ == "__main__":
    unittest.main()
