import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig, NATIVE_DIR, OwnedProcess

MODULE = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime."


class RuntimeTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="native-runtime-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)

    def load(self, data):
        path = self.path / "config.json"
        path.write_text(json.dumps(data), encoding="utf-8")
        return DspConfig.load(str(path))

    def test_native_config_defaults_and_root_confinement(self):
        config = self.load({"isabelle_home": str(self.path)})
        self.assertEqual("Isabelle2026", config.expected_isabelle_version)
        self.assertEqual("isabelle-native", config.backend)
        with self.assertRaises(ValueError):
            self.load({"isabelle_home": str(self.path.parent.parent.parent.parent.parent.parent)})

    def test_old_pisa_configuration_has_explicit_migration_error(self):
        for data in ({"pisa_jar": "old.jar"}, {"backend": "dsp-pisa"}, {"expected_isabelle_version": "Isabelle2021"}):
            with self.subTest(data=data), self.assertRaisesRegex(ValueError, "PISA"):
                self.load(data)

    def test_invalid_limits_provers_and_unknown_fields(self):
        for data in ({"step_timeout_s": 0}, {"threads": True}, {"threads": 0},
                     {"provers": []}, {"provers": "e"}, {"session_dependencies": ["bad;session"]},
                     {"step_timeout_s": float("inf")}, {"bogus": 1}):
            with self.subTest(data=data), self.assertRaises(ValueError):
                self.load(data)

    def test_environment_never_changes_home_and_keeps_artifacts_under_repo(self):
        config = DspConfig()
        with patch(MODULE + "RUNTIME_DIR", str(self.path)):
            env = config.environment()
        self.assertEqual(os.environ.get("HOME"), env.get("HOME"))
        self.assertEqual(os.environ.get("CODEX_HOME"), env.get("CODEX_HOME"))
        self.assertTrue(Path(env["USER_HOME"]).is_relative_to(self.path))
        self.assertEqual("Isabelle2026", env["ISABELLE_IDENTIFIER"])
        self.assertTrue(Path(env["TMPDIR"]).is_dir())
        settings = Path(env["USER_HOME"]) / ".isabelle/Isabelle2026/etc/settings"
        self.assertIn("ISABELLE_HEAPS=", settings.read_text())
        self.assertNotIn("ISABELLE_SETTINGS_PRESENT", env)

    def test_metadata_checks_release_and_resolved_paths(self):
        (self.path / "bin").mkdir()
        (self.path / "bin/isabelle").write_text("fixture")
        config = DspConfig(isabelle_home=str(self.path))
        hashes = json.loads((NATIVE_DIR / "release_sources.json").read_text())["sha256"]
        def run(command, **kwargs):
            if command[-1] == "version":
                return SimpleNamespace(stdout="Isabelle2026\n")
            return SimpleNamespace(stdout=str(self.path / command[-1]) + "\n")
        def digest(path):
            relative = str(path.relative_to(self.path)).replace("\\", "/") if path.is_relative_to(self.path) else ""
            return hashes.get(relative, "a" * 64)
        fake_os = SimpleNamespace(name="posix", environ=os.environ, access=os.access, X_OK=os.X_OK)
        with patch(MODULE + "os", fake_os), patch(MODULE + "subprocess.run", side_effect=run), patch(
                MODULE + "hash_file", side_effect=digest), patch(MODULE + "RUNTIME_DIR", str(self.path / "runtime")):
            metadata = config.metadata()
            self.assertEqual("isabelle-native", metadata["backend"])
            self.assertEqual(hashes, metadata["release_sources"])
            self.assertEqual(64, len(metadata["backend_fingerprint"]))
        with patch(MODULE + "os", fake_os), patch(MODULE + "hash_file", return_value="wrong"):
            with self.assertRaisesRegex(ValueError, "source mismatch"):
                config.metadata()

    def test_cleanup_uses_only_owned_process_group(self):
        process = OwnedProcess([], directory=self.path, env={}, log_path=self.path / "log",
                               timeout_s=1, deadline=1)
        process.process = Mock(pid=713)
        fake_os = SimpleNamespace(name="posix", killpg=Mock())
        with patch(MODULE + "os", fake_os):
            process.close()
        self.assertEqual([713, 713], [c.args[0] for c in fake_os.killpg.call_args_list])

    def test_exhausted_deadline_does_not_start_a_process(self):
        process = OwnedProcess([], directory=self.path, env={}, log_path=self.path / "log",
                               timeout_s=1, deadline=0)
        with patch(MODULE + "subprocess.Popen") as popen, self.assertRaises(TimeoutError):
            process.run()
        popen.assert_not_called()


    def test_deadline_is_checked_when_run_starts_not_when_process_is_constructed(self):
        with patch(MODULE + "time.monotonic", return_value=0):
            process = OwnedProcess([], directory=self.path, env={}, log_path=self.path / "log",
                                   timeout_s=20, deadline=5)
        with patch(MODULE + "time.monotonic", return_value=6), patch(
                MODULE + "subprocess.Popen") as popen, self.assertRaises(TimeoutError):
            process.run()
        popen.assert_not_called()

    def test_worker_startup_timeout_aborts_before_whole_target_timeout(self):
        process = OwnedProcess(["worker"], directory=self.path, env={}, log_path=self.path / "log",
                               timeout_s=20, deadline=20, ready_path=self.path / "ready",
                               startup_timeout_s=1)
        worker = Mock()
        worker.wait.side_effect = subprocess.TimeoutExpired("worker", 0.25)
        with patch(MODULE + "time.monotonic", side_effect=[0, 0.1, 1.1]), patch(
                MODULE + "subprocess.Popen", return_value=worker), patch.object(
                process, "capture_owned"), patch.object(process, "close") as close:
            with self.assertRaisesRegex(TimeoutError, "startup deadline"):
                process.run()
        self.assertEqual(1, worker.wait.call_count)
        close.assert_called_once()

    def test_ready_worker_can_search_beyond_startup_budget(self):
        ready = self.path / "ready"
        process = OwnedProcess(["worker"], directory=self.path, env={}, log_path=self.path / "log",
                               timeout_s=20, deadline=20, ready_path=ready, startup_timeout_s=1)
        worker = Mock()
        def wait(**kwargs):
            if not ready.exists():
                ready.write_text("ready")
                raise subprocess.TimeoutExpired("worker", kwargs["timeout"])
            return 0
        worker.wait.side_effect = wait
        with patch(MODULE + "time.monotonic", side_effect=[0, 0.1, 2]), patch(
                MODULE + "subprocess.Popen", return_value=worker), patch.object(
                process, "capture_owned"), patch.object(process, "close"):
            self.assertEqual(0, process.run())

    def test_children_of_nonleader_threads_are_tracked_recursively(self):
        proc = self.path / "proc"
        def task(pid, tid, children):
            folder = proc / str(pid) / "task" / str(tid)
            folder.mkdir(parents=True, exist_ok=True)
            (folder / "children").write_text(children)
        def stat(pid, group):
            fields = ["S", "1", str(group)] + ["0"] * 16 + [str(pid * 10)]
            (proc / str(pid) / "stat").write_text(f"{pid} (worker) " + " ".join(fields))
        task(713, 713, "")
        task(713, 720, "800")
        task(800, 800, "801")
        task(801, 801, "")
        task(999, 999, "")  # Unrelated process must not be discovered.
        for pid in (713, 800, 801, 999):
            stat(pid, pid)
        process = OwnedProcess([], directory=self.path, env={}, log_path=self.path / "log",
                               timeout_s=1, deadline=1)
        process.process = Mock(pid=713)
        with patch(MODULE + "PROC_ROOT", proc):
            process.capture_owned()
        self.assertEqual({713, 800, 801}, set(process.owned_processes))

    def test_cleanup_retains_owned_child_that_changed_process_group(self):
        process = OwnedProcess([], directory=self.path, env={}, log_path=self.path / "log",
                               timeout_s=1, deadline=1)
        process.process = Mock(pid=713)
        process.owned_processes = {713: {"start_ticks": "1", "group": 713},
                                   714: {"start_ticks": "2", "group": 713}}
        current = {713: process.owned_processes[713], 714: {"start_ticks": "2", "group": 714}}
        fake_os = SimpleNamespace(name="posix", killpg=Mock(), kill=Mock())
        with patch(MODULE + "os", fake_os), patch.object(process, "capture_owned"), patch.object(
                process, "process_identity", side_effect=current.get):
            process.close()
        self.assertEqual({713, 714}, {call.args[0] for call in fake_os.killpg.call_args_list})
        fake_os.kill.assert_not_called()

    def test_descendant_groups_are_owned_and_recycled_pids_are_ignored(self):
        process = OwnedProcess([], directory=self.path, env={}, log_path=self.path / "log",
                               timeout_s=1, deadline=1)
        process.process = Mock(pid=713)
        process.owned_processes = {713: {"start_ticks": "1", "group": 713},
                                   714: {"start_ticks": "2", "group": 714},
                                   715: {"start_ticks": "3", "group": 715}}
        fake_os = SimpleNamespace(name="posix", killpg=Mock(), kill=Mock())
        current = {713: process.owned_processes[713], 714: process.owned_processes[714],
                   715: {"start_ticks": "recycled", "group": 715}}
        with patch(MODULE + "os", fake_os), patch.object(process, "capture_owned"), patch.object(
                process, "process_identity", side_effect=current.get):
            process.close()
        self.assertEqual({713, 714}, {call.args[0] for call in fake_os.killpg.call_args_list})
        fake_os.kill.assert_not_called()


if __name__ == "__main__":
    unittest.main()
