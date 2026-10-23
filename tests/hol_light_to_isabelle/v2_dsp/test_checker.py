import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, read_jsonl, repo_path, write_jsonl
from eval.pipeline.hol_light_to_isabelle.v2_dsp.checker import Checker, HEURISTICS
from eval.pipeline.hol_light_to_isabelle.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.v2_dsp.prove import prove_sketches
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig, PisaSession


CONFIG = DspConfig(".", ".", "fake.jar", ".", "Isabelle2021")
BACKEND = {"isabelle_version": "Isabelle2021", "pisa_jar_sha256": "jar_a"}
SKETCH = "proof -\n  show True\n    sledgehammer\nqed"


class FakeSession:
    """A transport fixture, not an Isabelle proof validator."""

    force_hammer = False
    no_reconstruction = False
    fail_replay = False
    timeout_hammer = False

    def __init__(self, *args, **kwargs):
        self.states = {"default": {"open": False, "structured": False, "pending": False}}
        self.calls = []

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        pass

    def parse(self, text):
        return [line.strip() for line in text.splitlines() if line.strip()]

    def step(self, command, old, new, hammer=False):
        self.calls.append((command, old, new))
        state = copy.deepcopy(self.states[old])
        if command.startswith("lemma"):
            state = {"open": True, "structured": False, "pending": True}
        elif command == "proof -":
            state["structured"] = True
        elif command.startswith("show"):
            state["pending"] = True
        elif command.startswith("by") or command == "normalhammer":
            if self.timeout_hammer and command == "normalhammer":
                raise TimeoutError("native hammer deadline")
            if self.force_hammer and "_heuristic_" in new:
                raise RuntimeError("Step error: heuristic failed")
            if command not in {"by simp", "by auto", "by (metis TrueI)", "normalhammer"}:
                raise RuntimeError("Step error: method failed")
            if self.fail_replay and "_replay_" in new:
                raise RuntimeError("Step error: replay failed")
            state["pending"] = False
            if not state["structured"]:
                state["open"] = False
        elif command == "qed":
            if state["pending"]:
                raise RuntimeError("Step error: unresolved goals")
            state["open"] = False
        elif command == "sorry":
            state["open"] = state["pending"] = False
        elif command == "end" and state["open"]:
            raise RuntimeError("Step error: open proof")
        self.states[new] = state
        if command == "normalhammer":
            return "no reconstruction" if self.no_reconstruction else "by (metis TrueI) <hammer> goal state"
        return "goal state"

    def finished(self, state):
        return not self.states[state]["open"]


class CheckerTests(unittest.TestCase):
    def run_checker(self, session_class=FakeSession, proof=SKETCH, replay_only=False):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="dsp-checker-test-", dir=base) as folder, patch(
            "eval.pipeline.hol_light_to_isabelle.v2_dsp.checker.repo_path",
            return_value=Path(folder),
        ):
            row = control_record(proof)
            if replay_only:
                row["isabelle_proof"] = proof
            result = Checker(CONFIG, session_factory=session_class).check(
                row, backend_metadata=BACKEND, replay_only=replay_only)
            replay_path = result.get("replay_theory_path")
            if result["verified"]:
                self.assertTrue(Path(replay_path).is_file())
            return result

    def test_fills_gap_then_replays_without_hammer(self):
        result = self.run_checker()
        self.assertTrue(result["verified"], result["verify_error"])
        self.assertIn("by auto", result["isabelle_proof"])
        self.assertNotIn("sledgehammer", result["isabelle_proof"])
        self.assertTrue(result["replay_verified"])
        replay = [row for row in result["step_results"] if row["mode"] == "replay"]
        self.assertTrue(replay)
        self.assertTrue(all("hammer" not in row["command"] for row in replay))

    def test_portfolio_attempts_start_from_the_same_state(self):
        class HammerSession(FakeSession):
            force_hammer = True
        result = self.run_checker(HammerSession)
        self.assertTrue(result["verified"], result["verify_error"])
        attempts = [row for row in result["step_results"] if row["mode"] in {"heuristic", "hammer"}]
        self.assertEqual(list(HEURISTICS), [row["command"] for row in attempts[:-1]])
        self.assertEqual(1, len({row["source_state"] for row in attempts}))
        self.assertIn("by (metis TrueI)", result["isabelle_proof"])

    def test_hammer_success_without_a_replayable_method_cannot_pass(self):
        class NoMethodSession(FakeSession):
            force_hammer = no_reconstruction = True
        result = self.run_checker(NoMethodSession)
        self.assertFalse(result["verified"])
        self.assertEqual("missing_reconstruction", result["failure_category"])

    def test_replay_failure_cannot_be_counted_as_success(self):
        class ReplayFailure(FakeSession):
            fail_replay = True
        result = self.run_checker(ReplayFailure)
        self.assertTrue(result["prove_success"])
        self.assertFalse(result["verified"])
        self.assertEqual("replay_failure", result["failure_category"])

    def test_timeout_does_not_fall_through_to_another_attempt(self):
        class TimeoutSession(FakeSession):
            force_hammer = timeout_hammer = True
        result = self.run_checker(TimeoutSession)
        self.assertFalse(result["verified"])
        self.assertEqual("timeout", result["failure_category"])

    def test_admissions_and_malformed_gap_are_rejected(self):
        for proof in ("proof -\n sorry\nqed", "by sledgehammer"):
            result = self.run_checker(proof=proof)
            self.assertFalse(result["verified"])
        self.assertEqual("rejected_proof", self.run_checker(
            proof="proof -\n sorry\nqed")["failure_category"])

    def test_open_target_is_not_a_completed_helper(self):
        result = self.run_checker(proof="proof -\n show True\nqed")
        self.assertFalse(result["verified"])
        self.assertEqual("sketch_step_failure", result["failure_category"])

    def test_replay_only_does_not_run_search(self):
        result = self.run_checker(proof="by simp", replay_only=True)
        self.assertTrue(result["verified"], result["verify_error"])
        self.assertFalse(any(row["mode"] in {"search", "heuristic", "hammer"}
                             for row in result["step_results"]))

    def test_cleanup_targets_only_its_owned_process_group(self):
        session = PisaSession.__new__(PisaSession)
        session.channel, session.log = Mock(), Mock()
        session.process = Mock(pid=713)
        with patch("eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime.os.name", "posix"), patch(
            "eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime.os.killpg", create=True
        ) as kill, patch(
            "eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime.signal.SIGKILL", 9, create=True
        ):
            session.close()
        self.assertEqual([713, 713], [call.args[0] for call in kill.call_args_list])
        session.channel.close.assert_called_once()

    def test_prove_resume_includes_backend_and_rejects_changed_drafts(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="dsp-prove-test-", dir=base) as folder:
            source, output = Path(folder) / "sketches.jsonl", Path(folder) / "verified.jsonl"
            row = control_record(SKETCH)
            write_jsonl(source, [row])
            result = {**row, "checker_version": "babel_formal_v2_dsp_checker_p1",
                      "prove_success": True, "replay_verified": True, "verified": True,
                      "isabelle_proof": "by simp"}
            with patch.object(DspConfig, "metadata", return_value=BACKEND) as metadata, patch(
                "eval.pipeline.hol_light_to_isabelle.v2_dsp.prove.Checker.check", return_value=result
            ) as check:
                options = dict(config=CONFIG, input_path=str(source), output_path=str(output),
                               prove_output=None, expected=[row], expected_samples=1)
                prove_sketches(**options)
                prove_sketches(**options)
                self.assertEqual(1, check.call_count)
                metadata.return_value = {**BACKEND, "pisa_jar_sha256": "jar_b"}
                prove_sketches(**options)
                self.assertEqual(2, check.call_count)
            self.assertTrue(read_jsonl(output)[0]["verified"])


if __name__ == "__main__":
    unittest.main()
