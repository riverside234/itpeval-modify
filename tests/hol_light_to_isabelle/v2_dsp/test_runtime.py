import json
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig


MODULE = "eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime."


class RuntimeConfigTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="dsp-optional-source-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        pisa = self.root / "pisa"
        pisa.mkdir()
        for name in ("server_pb2.py", "server_pb2_grpc.py"):
            (pisa / name).write_text("# fixture\n", encoding="utf-8")
        jar = self.root / "pisa.jar"
        jar.write_bytes(b"fixture")
        isabelle = self.root / "isabelle"
        isabelle.mkdir()
        self.data = {
            "pisa_python_path": str(pisa), "pisa_jar": str(jar),
            "isabelle_home": str(isabelle), "expected_isabelle_version": "Isabelle2021",
        }

    def load(self, **options):
        path = self.root / "config.json"
        path.write_text(json.dumps({**self.data, **options}), encoding="utf-8")
        with patch(MODULE + "repo_path", return_value=path):
            return DspConfig.load(str(path))

    @contextmanager
    def commands(self, config, *, dsp_commit=None, pisa_commit=None):
        def run(args, **kwargs):
            if args[0] == "git":
                is_pisa = args[2] == config.pisa_python_path
                value = ((pisa_commit or config.expected_pisa_commit) if is_pisa else
                         (dsp_commit or config.expected_dsp_commit))
                return SimpleNamespace(stdout=value + "\n", stderr="")
            if args[-1] == "version":
                return SimpleNamespace(stdout="Isabelle2021\n", stderr="")
            return SimpleNamespace(stdout="", stderr="Java test runtime")
        with patch(MODULE + "subprocess.run", side_effect=run) as mocked, patch(
            MODULE + "repository_commit", return_value=None
        ):
            yield mocked

    def test_default_does_not_require_a_dsp_path_or_git_checkout(self):
        config = self.load()
        self.assertFalse(config.check_dsp_repo)
        self.assertIsNone(config.dsp_repo_root)
        with self.commands(config) as commands:
            metadata = config.metadata()
        self.assertFalse(metadata["dsp_repo_checked"])
        self.assertIsNone(metadata["dsp_commit"])
        git_calls = [call.args[0] for call in commands.call_args_list if call.args[0][0] == "git"]
        self.assertEqual([["git", "-C", config.pisa_python_path, "rev-parse", "HEAD"]], git_calls)

    def test_disabled_check_ignores_an_unavailable_dsp_checkout_and_pin(self):
        config = self.load(dsp_repo_root=str(self.root / "not-installed"),
                           expected_dsp_commit="unused")
        with self.commands(config):
            self.assertFalse(config.metadata()["dsp_repo_checked"])

    def test_enabled_check_requires_the_dsp_directory(self):
        with self.assertRaisesRegex(ValueError, "dsp_repo_root"):
            self.load(check_dsp_repo=True)
        config = self.load(check_dsp_repo=True, dsp_repo_root=str(self.root / "not-installed"))
        with self.assertRaisesRegex(FileNotFoundError, "dsp_repo_root"):
            config.metadata()

    def test_enabled_check_records_and_enforces_the_dsp_commit(self):
        dsp = self.root / "dsp"
        dsp.mkdir()
        config = self.load(check_dsp_repo=True, dsp_repo_root=str(dsp))
        with self.commands(config):
            metadata = config.metadata()
        self.assertTrue(metadata["dsp_repo_checked"])
        self.assertEqual(config.expected_dsp_commit, metadata["dsp_commit"])
        with self.commands(config, dsp_commit="0" * 40):
            with self.assertRaisesRegex(ValueError, "dsp commit mismatch"):
                config.metadata()

    def test_pisa_commit_remains_required_when_dsp_check_is_disabled(self):
        config = self.load()
        with self.commands(config, pisa_commit="0" * 40):
            with self.assertRaisesRegex(ValueError, "pisa commit mismatch"):
                config.metadata()

    def test_check_flag_requires_a_boolean(self):
        with self.assertRaisesRegex(ValueError, "boolean"):
            self.load(check_dsp_repo="false")


if __name__ == "__main__":
    unittest.main()
