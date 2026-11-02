"""Regressions around the copied DSP code, not a replacement proof algorithm."""
import ast
import hashlib
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.upstream import checker as original
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.pisa_worker import ObservedChecker, BoundedStub
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.runtime import DspConfig, PACKAGE, PisaFailure, run_job


class UpstreamTests(unittest.TestCase):
    def test_critical_methods_match_the_copied_original_source(self):
        origin = json.loads((PACKAGE/"upstream/origin.json").read_text())
        tree = ast.parse((PACKAGE/"upstream/checker.py").read_text())
        cls = next(node for node in tree.body if isinstance(node, ast.ClassDef) and node.name=="Checker")
        methods = {node.name: hashlib.sha256(ast.dump(node, include_attributes=False).encode()).hexdigest()
                   for node in cls.body if isinstance(node, ast.FunctionDef)}
        for name, digest in origin["unchanged_methods_ast_sha256"].items():
            self.assertEqual(digest, methods[name], name)

    def test_original_heuristic_order_falls_back_to_normalhammer_from_same_state(self):
        checker = original.Checker("work", "isa", "Test.thy")
        env = Mock()
        # The upstream environment returns four values, not checker error metadata.
        def reply(action, **kwargs):
            return ("by metis <hammer> no goals", 1.0, True, {}) if action=="normalhammer" else ("Step error: fixture", 0.0, False, {})
        env.step_to_top_level_state.side_effect = reply
        result = checker._run_sledgehammer("sledgehammer", 2, "saved", env)
        actions = [call.kwargs["action"] for call in env.step_to_top_level_state.call_args_list]
        self.assertEqual(["by auto", "by simp", "by blast", "by fastforce", "by force", "by eval", "by presburger",
                          "by sos", "by arith", "by linarith", "by (auto simp: field_simps)", "normalhammer"], actions)
        self.assertTrue(result[2])
        self.assertTrue(all(c.kwargs["tls_name"]=="saved" for c in env.step_to_top_level_state.call_args_list))
        self.assertTrue(all(c.kwargs["new_name"]=="default_2" for c in env.step_to_top_level_state.call_args_list))

    def test_full_dataset_context_is_not_wrapped_in_minif2f_imports(self):
        checker = original.Checker("work", "isa", "Test.thy")
        env = Mock(successful_starting=True)
        env.post.return_value = 'theory Test imports Main begin<SEP>lemma t: "True"<SEP>by simp'
        env.step_to_top_level_state.side_effect = [("", 1.0, True, {}), ("goal", 0.0, False, {}), ("", 1.0, True, {})]
        formal='theory Test imports Main begin\nlemma t: "True"\nby simp'
        with patch.object(original, "initialise_env", return_value=env):
            result=checker.check(formal)
        self.assertTrue(result["success"])
        self.assertIn(formal, env.post.call_args_list[1].args[0])
        self.assertNotIn("Symmetric_Polynomials",env.post.call_args_list[1].args[0])

    def test_empty_parse_and_failed_last_step_cannot_pass(self):
        checker=original.Checker("work","isa","Test.thy")
        env=Mock(successful_starting=True)
        with patch.object(original,"initialise_env",return_value=env):
            env.post.return_value=""
            self.assertFalse(checker.check("formal")["success"])
            env.post.return_value="first<SEP>second"
            env.step_to_top_level_state.side_effect=[("",1.0,True,{}),("Step error: failed",0.0,False,{})]
            self.assertFalse(checker.check("formal")["success"])

    def test_inherited_target_is_rejected_before_proving(self):
        checker=ObservedChecker("work","isa","Set.thy")
        env=Mock()
        env.post.return_value="Pure,HOL.Set,HOL.Main"
        with patch.object(original.Checker,"_initialize",return_value=env), self.assertRaisesRegex(PisaFailure,"already inherited"):
            checker._initialize()

    def test_rpc_budget_and_errors_are_logged(self):
        base=repo_path(RESULTS_DIR)
        base.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as tmp:
            stub=Mock()
            stub.IsabelleCommand.side_effect=RuntimeError("RPC failed")
            bound=BoundedStub(stub,DspConfig(),Path(tmp),time.monotonic()+1)
            request=Mock(command="normalhammer")
            with self.assertRaisesRegex(RuntimeError,"RPC failed"):
                bound.IsabelleCommand(request)
            self.assertLessEqual(stub.IsabelleCommand.call_args.kwargs["timeout"],1)
            event=json.loads((Path(tmp)/"rpc.jsonl").read_text())
            self.assertIn("RPC failed",event["error"])
            self.assertIn("RPC failed",bound.last_error)

    def test_initialization_error_includes_rpc_failure(self):
        checker = original.Checker("work", "isa", "Test.thy")
        env = Mock(successful_starting=False)
        env.stub.last_error = "Missing theory: Test_Import"
        with patch.object(original, "initialise_env", return_value=env), self.assertRaisesRegex(RuntimeError, "Missing theory"):
            checker._initialize()

    def test_protocol_delimiters_fail_before_starting_worker(self):
        with patch("eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.runtime.OwnedProcess") as process:
            for marker in ("<SEP>", "<apply to top level state>"):
                with self.assertRaisesRegex(PisaFailure, "reserved PISA"):
                    run_job(DspConfig(), Path("unused"), {"formal": marker, "action": "prove"})
            process.assert_not_called()

    def test_mismatched_worker_response_cannot_pass(self):
        base=repo_path(RESULTS_DIR)
        base.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as tmp:
            directory=Path(tmp)
            def run():
                (directory/"result.json").write_text(json.dumps({"success":True,"request_id":"old","input_sha256":"old"}))
                return 0
            with patch("eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.runtime.OwnedProcess") as process, patch.object(DspConfig,"environment",return_value={}):
                process.return_value.run.side_effect=run
                with self.assertRaisesRegex(PisaFailure,"mismatched"):
                    run_job(DspConfig(),directory,{"formal":"proof","action":"prove","theory_name":"Test"})


if __name__ == "__main__":
    unittest.main()
