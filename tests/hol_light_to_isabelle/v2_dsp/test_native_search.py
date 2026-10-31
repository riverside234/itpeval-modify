"""Protocol/driver tests never claim to validate Isabelle mathematics."""
import importlib.resources
import json
import tempfile
import time
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.v2_dsp.native_search import (
    NativeFailure, NativeSearch, RESULT_VERSION, imports_of, read_result,
)
from eval.pipeline.hol_light_to_isabelle.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig, NATIVE_DIR


class NativeSearchTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="native-protocol-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.request = {"request_id": "owned", "input_sha256": "a" * 64, "action": "search"}

    def result(self, **attrs):
        root = ET.Element("dsp_result", schema=RESULT_VERSION, success="true", target_closed="true", **self.request)
        for name, value in attrs.items():
            root.set(name, value)
        for name in ("proof", "category", "error", "attempts", "settings"):
            ET.SubElement(root, name).text = "by simp" if name == "proof" else ""
        path = self.path / "result.xml"
        ET.ElementTree(root).write(path, encoding="utf-8")
        return path

    def test_result_requires_matching_request_hash_and_successful_process(self):
        path = self.result()
        self.assertTrue(read_result(path, self.request, returncode=0)["success"])
        self.assertFalse(read_result(path, self.request, returncode=1)["success"])
        for attrs in ({"request_id": "stale"}, {"input_sha256": "bad"}, {"schema": "old"},
                      {"action": "context"}, {"target_closed": "false"}, {"success": "maybe"}):
            with self.subTest(attrs=attrs), self.assertRaises(NativeFailure):
                read_result(self.result(**attrs), self.request, returncode=0)

    def test_zero_exit_without_result_or_with_partial_result_never_passes(self):
        path = self.path / "missing.xml"
        with self.assertRaises(NativeFailure):
            read_result(path, self.request, returncode=0)
        path.write_text("<dsp_result", encoding="utf-8")
        with self.assertRaises(NativeFailure):
            read_result(path, self.request, returncode=0)

    def test_duplicate_or_missing_fields_are_rejected(self):
        path = self.result()
        root = ET.parse(path).getroot()
        ET.SubElement(root, "proof").text = "sorry"
        ET.ElementTree(root).write(path)
        with self.assertRaises(NativeFailure):
            read_result(path, self.request, returncode=0)

    def test_result_proof_cannot_contain_a_search_placeholder(self):
        path = self.result()
        root = ET.parse(path).getroot()
        root.find("proof").text = "by sledgehammer"
        ET.ElementTree(root).write(path)
        with self.assertRaises(ValueError):
            read_result(path, self.request, returncode=0)

    def test_driver_loads_only_imports_and_passes_preceding_context(self):
        config = DspConfig()
        native = NativeSearch(config)
        record = control_record("by simp")
        directory = self.path / "search"
        def build(folder, session, **options):
            request_xml = ET.parse(folder / "request.xml").getroot()
            attrs = {k: request_xml.get(k) for k in ("request_id", "input_sha256", "action")}
            root = ET.Element("dsp_result", schema=RESULT_VERSION, success="true", target_closed="true", **attrs)
            for name in ("proof", "category", "error", "attempts", "settings"):
                ET.SubElement(root, name).text = "by simp" if name == "proof" else ""
            ET.ElementTree(root).write(folder / "result.xml", encoding="utf-8")
            return 0
        with patch.object(native, "infrastructure", return_value=(self.path, "DSP_Infrastructure")), patch.object(
                native, "encode_symbols", side_effect=lambda text: text), patch.object(native, "run_build", side_effect=build):
            result = native.request(record, "by simp", directory=directory, action="search", heuristics=(),
                                    deadline=time.monotonic() + 30)
        self.assertTrue(result["success"])
        driver = (directory / "DSP_Driver.thy").read_text()
        self.assertIn('imports DSP_Native "Main"', driver)
        self.assertNotIn('imports V2Control', driver)
        request = json.loads((directory / "input.json").read_text())
        self.assertNotIn("v2_control", request["prefix"])
        self.assertNotIn("sorry", request["prefix"])
        self.assertEqual(["v2_control"], request["forbidden_names"])
        self.assertTrue((directory / "line_mapping.json").is_file())

    def test_replay_contains_no_search_helpers_or_later_theorems(self):
        native = NativeSearch(DspConfig())
        record = control_record("by simp")
        with patch.object(native, "encode_symbols", side_effect=lambda text: text), patch.object(native, "run_build", return_value=0):
            result = native.replay(record, "by simp", directory=self.path / "replay", deadline=time.monotonic() + 20)
        source = Path(result["replay_theory_path"]).read_text()
        self.assertNotIn("DSP_Native", source)
        self.assertNotIn("sledgehammer", source)
        self.assertNotIn("sorry", source)
        self.assertLess(source.index("quick_and_dirty = false"), source.index("lemma v2_control"))
        self.assertIn('lemma v2_control: "True"', source)

    def test_session_dependencies_and_budgeted_build_options(self):
        native = NativeSearch(DspConfig(session_roots=(str(self.path),), session_dependencies=("HOL-Analysis",), threads=2))
        command = native.build_command(self.path, "Job", parent_dir=self.path / "infra")
        self.assertEqual("build", command[1])
        self.assertIn("parallel_proofs=0", command)
        self.assertIn("threads=2", command)
        self.assertNotIn("ML_process", command)
        self.assertEqual(["Main", "HOL-Analysis.Analysis"], imports_of('theory X imports Main "HOL-Analysis.Analysis" begin'))

    def test_resources_are_available_through_the_python_package(self):
        root = importlib.resources.files("eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp") / "native"
        for name in ("ROOT", "DSP_Native.thy", "dsp_native.ML", "dsp_sledgehammer.ML", "release_sources.json"):
            self.assertTrue((root / name).is_file(), name)
        adapter = (root / "dsp_sledgehammer.ML").read_text()
        self.assertIn("SH_Some", adapter)
        self.assertIn("Played", adapter)
        self.assertIn("Markup.sendbackN", adapter)
        self.assertNotIn("<hammer>", adapter)


if __name__ == "__main__":
    unittest.main()
