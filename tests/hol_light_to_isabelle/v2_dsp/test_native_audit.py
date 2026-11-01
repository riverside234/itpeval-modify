"""Regressions from the setup/search/replay audit; no native or model calls."""
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.checker import Checker
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.input_contract import normalize_sketch
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import NativeFailure, NativeSearch, resolve_imports
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig


BACKEND = {"backend": "isabelle-native", "isabelle_version": "Isabelle2026"}


class NativeAuditTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="native-audit-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)

    def test_submillisecond_ml_limits_cannot_silently_disable_timeouts(self):
        for name in ("step_timeout_s", "hammer_timeout_s", "preplay_timeout_s"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "0.001"):
                DspConfig(**{name: 0.000001})
            self.assertEqual(0.001, getattr(DspConfig(**{name: 0.001}), name))

    def test_quoted_qualified_and_escaped_unsafe_methods_are_rejected(self):
        for name in ('"tactic"', '"raw_tactic"', 'Pure.raw_tactic',
                     r'"Pure.ta\099tic"', '"Pure.raw_tactic"'):
            proof = 'by (' + name + r' \<open>all_tac\<close>)'
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "forbidden"):
                normalize_sketch(proof)
        for name in ('quick_and_dirty', '"quick_and_dirty"', 'smt_oracle', 'SMT.smt_oracle'):
            proof = 'proof -\n supply [[' + name + ' = true]]\n show True by simp\nqed'
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "forbidden"):
                normalize_sketch(proof)

    def test_safe_quoted_methods_and_mathematical_text_remain_valid(self):
        for proof in ('by "simp"', 'by ("simp" only: TrueI)',
                      'proof -\n have "Local.tactic = Local.tactic" by simp\n show True by simp\nqed',
                      'proof -\n have "tactic = tactic" by simp\n show True by simp\nqed',
                      r'proof - show \<open>True\<close> by simp qed'):
            self.assertEqual(proof, normalize_sketch(proof))

    def test_search_and_replay_reject_the_same_unsafe_body_before_native_build(self):
        native = NativeSearch(DspConfig())
        proof = r'by ("tactic" \<open>all_tac\<close>)'
        with patch.object(native, "run_build") as build:
            with self.assertRaisesRegex(ValueError, "forbidden"):
                native.replay(control_record("by simp"), proof, directory=self.path / "replay",
                              deadline=time.monotonic() + 10)
        build.assert_not_called()
        fake = Mock()
        checker = Checker(DspConfig(), native_factory=lambda _: fake, results_dir=str(self.path))
        result = checker.check({**control_record("by simp"), "isabelle_proof": proof},
                               replay_only=True, backend_metadata=BACKEND)
        self.assertFalse(result["verified"])
        self.assertEqual("rejected_proof", result["failure_category"])
        fake.replay.assert_not_called()

    def test_target_import_cannot_hide_behind_a_theory_file_suffix(self):
        for target in ('V2Control', 'V2Control.thy', 'Session.V2Control', 'Session.V2Control.thy'):
            with self.subTest(target=target), self.assertRaisesRegex(NativeFailure, "selected target theory"):
                resolve_imports('theory V2Control imports "' + target + '" begin',
                                DspConfig(), theory_name="V2Control")

    def test_timeout_diagnostics_retain_the_failed_phase_and_log(self):
        factory = Mock()
        factory.return_value.process.returncode = -9
        def timeout():
            (self.path / "build.log").write_text("Running DSP_Job\nlast operation\n", encoding="utf-8")
            raise TimeoutError("worker startup deadline exceeded")
        factory.return_value.run.side_effect = timeout
        native = NativeSearch(DspConfig(), process_factory=factory)
        with patch.object(DspConfig, "environment", return_value={}):
            with self.assertRaises(NativeFailure) as caught:
                native.run_build(self.path, "DSP_Job", timeout_s=2, deadline=time.monotonic() + 2)
        error = caught.exception
        self.assertEqual("timeout", error.category)
        self.assertEqual(-9, error.details["build_returncode"])
        self.assertEqual(str(self.path / "build.log"), error.details["build_log_path"])
        self.assertIn("last operation", str(error))
        self.assertTrue((self.path / "command.json").is_file())

    def test_failed_recheck_cannot_retain_an_old_native_success(self):
        row = {**control_record("by simp"), "isabelle_proof": "by simp",
               "native_search": {"success": True}, "native_replay": {"success": True},
               "prover_settings": {"native_outcome": "some"}, "workdir": "old-job",
               "replay_theory_path": "old.thy", "replay_log_path": "old.log",
               "build_log_path": "old-build.log", "verify_fingerprint": "old-identity"}
        fake = Mock()
        fake.request.return_value = {"success": True}
        fake.replay.side_effect = TimeoutError("fresh replay timed out")
        result = Checker(DspConfig(), native_factory=lambda _: fake, results_dir=str(self.path)).check(
            row, replay_only=True, backend_metadata=BACKEND)
        self.assertFalse(result["verified"])
        self.assertEqual("timeout", result["failure_category"])
        for name in ("native_search", "native_replay", "prover_settings", "replay_theory_path",
                     "replay_log_path", "build_log_path", "verify_fingerprint"):
            self.assertNotIn(name, result, name)
        self.assertNotEqual("old-job", result["workdir"])

    def test_replay_only_rejects_context_contamination_before_replaying(self):
        fake = Mock()
        fake.request.return_value = {"success": False, "failure_category": "context_error",
                                     "error": "target or later fact leaked into the input context"}
        row = {**control_record("by simp"), "isabelle_proof": "by simp"}
        result = Checker(DspConfig(), native_factory=lambda _: fake, results_dir=str(self.path)).check(
            row, replay_only=True, backend_metadata=BACKEND)
        self.assertFalse(result["verified"])
        self.assertEqual("context_error", result["failure_category"])
        self.assertEqual("context", fake.request.call_args.kwargs["action"])
        fake.replay.assert_not_called()


if __name__ == "__main__":
    unittest.main()
