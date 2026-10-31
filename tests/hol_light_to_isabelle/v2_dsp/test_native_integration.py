"""Opt-in real Isabelle2026 controls; no LLM calls. See the native DSP README."""
from dataclasses import replace
import os
from pathlib import Path
import shutil
import time
import unittest
import uuid

from eval.pipeline.hol_light_to_isabelle.v2_dsp.checker import Checker
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.v2_dsp.native_search import NativeSearch
from eval.pipeline.hol_light_to_isabelle.v2_dsp.preflight import control_record, preflight
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records


@unittest.skipUnless(os.environ.get("ITPEVAL_NATIVE_ISABELLE2026_CONFIG"),
                     "native Isabelle2026 acceptance requires the lab installation")
class NativeIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = DspConfig.load(os.environ["ITPEVAL_NATIVE_ISABELLE2026_CONFIG"])
        cls.backend = cls.config.metadata()

    def test_controls_in_both_input_modes(self):
        for mode in ("draft", "hol-light-proof"):
            with self.subTest(mode=mode):
                result = preflight(control_record("by simp", sketch_source=mode), config=self.config,
                                   backend_metadata=self.backend, sketch_source=mode)
                self.assertTrue(result["ok"], result)
                hammer = result["controls"]["hammer"]
                settings = hammer["prover_settings"]
                self.assertEqual("some", settings["native_outcome"])
                self.assertGreater(int(settings["candidate_count"]), 0)
                self.assertIn(settings["reconstruction_source"], {"preplayed", "native_tactic"})
                self.assertTrue(any(row["mode"] == "reconstruction" and row["success"]
                                    for row in hammer["step_results"]))

    def test_native_tactic_without_separate_preplay_is_executed_and_replayed(self):
        config = replace(self.config, provers=("simp",))
        proof = "proof -\n show True\n sledgehammer\nqed"
        result = Checker(config).check(control_record(proof), force_hammer=True,
                                       backend_metadata=config.metadata())
        self.assertTrue(result["verified"], result["verify_error"])
        settings = result["prover_settings"]
        self.assertEqual("native_tactic", settings["reconstruction_source"])
        self.assertEqual("0", settings["preplay_count"])
        self.assertGreater(int(settings["candidate_count"]), 0)
        self.assertTrue(any(row["mode"] == "reconstruction" and row["success"]
                            for row in result["step_results"]))
        self.assertTrue(result["replay_verified"])

    def test_native_reconstruction_without_pide_and_failed_preplay_filter(self):
        native = NativeSearch(self.config)
        deadline = time.monotonic() + self.config.target_timeout_s
        parent_dir, parent_session = native.infrastructure(deadline=deadline)
        directory = Checker(self.config).directory("reconstruction-regression-")
        theory = "DSP_Reconstruction_Test"
        source = Path(__file__).parent / "fixtures" / (theory + ".thy")
        shutil.copyfile(source, directory / source.name)
        session = "DSP_Reconstruction_Test_" + uuid.uuid4().hex
        (directory / "ROOT").write_text(
            f"session {session} = {parent_session} +\n"
            f"  options [document = false]\n  theories {theory}\n", encoding="utf-8")
        code = native.run_build(directory, session, timeout_s=self.config.startup_timeout_s,
                                deadline=deadline, parent_dir=parent_dir)
        self.assertEqual(0, code, (directory / "build.log").read_text(encoding="utf-8"))

    def test_nested_isar_multiple_gaps_local_assumptions_and_symbols(self):
        proof = ("proof -\n have first: True\n  sledgehammer\n"
                 " have both: \\<open>True \\<and> True\\<close>\n"
                 " proof\n  show True using first\n   sledgehammer\n"
                 "  show True using first\n   sledgehammer\n qed\n"
                 " show True using both\n  sledgehammer\nqed")
        for mode in ("draft", "hol-light-proof"):
            result = Checker(self.config).check(control_record(proof, sketch_source=mode), backend_metadata=self.backend)
            self.assertTrue(result["verified"], result["verify_error"])
            self.assertNotIn("sledgehammer", result["isabelle_proof"])

    def test_unavailable_prover_and_timeout_cannot_pass(self):
        proof = "proof -\n show True\n sledgehammer\nqed"
        config = replace(self.config, provers=("dsp_nonexistent_prover",))
        result = Checker(config).check(control_record(proof), force_hammer=True, backend_metadata=config.metadata())
        self.assertFalse(result["verified"])
        self.assertEqual("hammer_failure", result["failure_category"])
        self.assertEqual("dsp_nonexistent_prover", result["prover_settings"]["resolved_provers"])
        config = replace(self.config, step_timeout_s=0.000001)
        result = Checker(config).check(control_record(proof), backend_metadata=config.metadata())
        self.assertFalse(result["verified"])
        self.assertEqual("timeout", result["failure_category"])

    def test_babel_locale_source_modes_and_hundred_context(self):
        from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import export_record
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as hundred
        babel = extract_records(topic="circle_average", target_key="circleAverage_center_independent")[0]
        for mode in ("draft", "hol-light-proof"):
            raw = {**babel, "draft": "Unfold both definitions and use integral_shift."}
            record = export_record(raw, sketch_source=mode)
            record["isabelle_sketch"] = "proof -\n show ?thesis unfolding circleAverage_def circleMap_def\n sledgehammer\nqed"
            result = Checker(self.config).check(record, backend_metadata=self.backend)
            self.assertTrue(result["verified"], result["verify_error"])
        record = hundred(topic="030_the_ballot_problem", target_key="all_countings")[0]
        self.assertTrue(Checker(self.config).check_context(record, backend_metadata=self.backend)["baseline_ok"])
        for mode in ("draft", "hol-light-proof"):
            raw = {**record, "draft": "Use all_countings_set and the cardinality of fixed-size subsets."}
            row = export_record(raw, expected_source="hundred-theorems", sketch_source=mode)
            row["isabelle_sketch"] = "by (simp add: all_countings_set n_subsets)"
            result = Checker(self.config).check(row, backend_metadata=self.backend)
            self.assertTrue(result["verified"], result["verify_error"])


    def test_fresh_replay_error_is_not_search_success(self):
        from eval.pipeline.hol_light_to_isabelle.v2_dsp.native_search import NativeSearch
        class CorruptedReplay(NativeSearch):
            def replay(self, record, proof, **options):
                return super().replay(record, "by (dsp_invalid_replay_method)", **options)
        result = Checker(self.config, native_factory=CorruptedReplay).check(
            control_record("by simp"), backend_metadata=self.backend)
        self.assertTrue(result["prove_success"], result["verify_error"])
        self.assertFalse(result["verified"])
        self.assertEqual("replay_failure", result["failure_category"])


if __name__ == "__main__":
    unittest.main()
