import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from eval.pipeline.inference.config import repository_path


def load_script(name):
    path = repository_path("vllm/"+name+".py")
    spec = importlib.util.spec_from_file_location("itpeval_vllm_"+name,path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ServerToolTests(unittest.TestCase):
    def setUp(self):
        self.settings = load_script("settings")
        with patch.dict(sys.modules,{"settings":self.settings}):
            self.serve = load_script("serve")

    def test_cache_paths_and_runtime_default_config_stay_under_repo(self):
        config = self.settings.read_config()
        env = self.settings.cache_environment(create=False)
        root = repository_path("vllm")
        self.assertTrue(all(Path(value).is_relative_to(root) for value in env.values()))
        self.assertEqual(30002,config["port"])
        self.assertEqual(1,config["max_num_seqs"])
        self.assertFalse(repository_path("vllm/__init__.py").exists())
        command = self.serve.command(config)
        self.assertIn("--language-model-only",command)
        self.assertEqual("qwen3",command[command.index("--reasoning-parser")+1])
        self.assertEqual("vllm",command[command.index("--generation-config")+1])

    def test_server_dry_run_and_help_need_no_server_dependencies(self):
        result = subprocess.run([sys.executable,"-B","vllm/serve.py","--dry-run"],
                                capture_output=True,text=True,check=True,timeout=30)
        parsed = json.loads(result.stdout)
        self.assertIn("--max-model-len",parsed["command"])
        self.assertTrue(parsed["manifest"].endswith("server_manifest.json"))
        for name in ("serve","download_model","check_server"):
            result = subprocess.run([sys.executable,"-B","vllm/"+name+".py","--help"],
                                    capture_output=True,text=True,check=True,timeout=30)
            self.assertIn("--help",result.stdout)

    def test_native_preflight_refuses_the_client_environment(self):
        prefix = str(repository_path("."))
        with patch.object(self.serve.platform,"system",return_value="Linux"), patch.object(
                self.serve.sys,"prefix",prefix), patch.dict(os.environ,{"CONDA_PREFIX":prefix}), patch.object(
                self.serve.sys,"version_info",(3,10,0)):
            with self.assertRaisesRegex(ValueError,"Python 3.12"):
                self.serve.preflight(self.settings.read_config())

    def test_native_preflight_requires_an_active_conda_environment(self):
        with patch.object(self.serve.platform,"system",return_value="Linux"), patch.dict(
                os.environ,{},clear=True), patch.object(self.serve.packages,"version") as version:
            with self.assertRaisesRegex(ValueError,"conda activate vllm"):
                self.serve.preflight(self.settings.read_config())
            version.assert_not_called()

    def test_native_preflight_rejects_an_interpreter_from_another_environment(self):
        prefix = str(Path(tempfile.gettempdir())/"existing-conda-envs"/"vllm")
        with patch.object(self.serve.platform,"system",return_value="Linux"), patch.object(
                self.serve.sys,"prefix",str(repository_path("."))), patch.dict(
                os.environ,{"CONDA_PREFIX":prefix}), patch.object(self.serve.packages,"version") as version:
            with self.assertRaisesRegex(ValueError,"Python must come from the active conda"):
                self.serve.preflight(self.settings.read_config())
            version.assert_not_called()

    def test_native_preflight_accepts_existing_conda_environment_outside_repo(self):
        # Dependency/CUDA fixtures test environment selection, not actual GPU inference.
        prefix = str(Path(tempfile.gettempdir())/"existing-conda-envs"/"vllm")
        self.assertFalse(Path(prefix).resolve().is_relative_to(repository_path(".")))
        config = self.settings.read_config()
        torch = SimpleNamespace(
            __version__="fixture",version=SimpleNamespace(cuda="fixture"),
            cuda=SimpleNamespace(is_available=lambda:True,device_count=lambda:1,
                get_device_properties=lambda index:SimpleNamespace(
                    major=8,minor=0,name="FIXTURE GPU",total_memory=1024)))
        with patch.object(self.serve.platform,"system",return_value="Linux"), patch.object(
                self.serve.platform,"python_version",return_value="3.12.0"), patch.object(
                self.serve.sys,"prefix",prefix), patch.object(self.serve.sys,"version_info",(3,12,0)), patch.dict(
                os.environ,{"CONDA_PREFIX":prefix,"CONDA_DEFAULT_ENV":"vllm"}), patch.object(
                self.serve.packages,"version",side_effect=config["expected_versions"].__getitem__), patch.object(
                self.serve,"verify_checkpoint",return_value={"tokenizer_sha256":"a"*64,"template_sha256":"b"*64}), patch.object(
                self.serve,"package_freeze",return_value="fixture==1\n"), patch.dict(sys.modules,{"torch":torch}):
            manifest = self.serve.preflight(config)
        self.assertEqual("3.12.0",manifest["versions"]["python"])
        self.assertEqual(config["expected_versions"]["vllm"],manifest["versions"]["vllm"])

    def test_checkpoint_identity_sizes_and_template_changes_are_checked(self):
        base = repository_path("eval/results/inference_tests")
        base.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as folder:
            directory = Path(folder)
            # Minimal byte fixtures; these are not downloaded model artifacts.
            (directory/"weights.safetensors").write_bytes(b"fixture")
            (directory/"tokenizer.json").write_text('{"fixture":true}')
            (directory/"tokenizer_config.json").write_text('{"chat_template":"fixture"}')
            config = self.settings.read_config()
            config["model_dir"] = str(directory)
            manifest = {
                "schema_version":"itpeval_checkpoint_v1","model":config["model"],"revision":config["revision"],
                "files":{path.name:path.stat().st_size for path in directory.iterdir()},
                **self.settings.metadata_hashes(directory),
            }
            path = directory/".itpeval_download.json"
            path.write_text(json.dumps(manifest))
            self.settings.verify_checkpoint(config)
            (directory/"tokenizer_config.json").write_text('{"chat_template":"changed"}')
            with self.assertRaisesRegex(ValueError,"incomplete|modified"):
                self.settings.verify_checkpoint(config)


BASH = (str(Path("C:/Program Files/Git/bin/bash.exe"))
        if os.name=="nt" and Path("C:/Program Files/Git/bin/bash.exe").is_file()
        else shutil.which("bash") if os.name!="nt" else None)


@unittest.skipUnless(BASH,"Bash is required for launcher routing tests")
class LauncherTests(unittest.TestCase):
    def setUp(self):
        base = repository_path("eval/results/inference_tests")
        base.mkdir(parents=True,exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="conda-launcher-",dir=base)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        scripts = self.root/"server"
        scripts.mkdir()
        self.launcher = scripts/"launch_qwen.sh"
        self.launcher.write_bytes(repository_path("vllm/launch_qwen.sh").read_bytes())
        # Avoid creating real server caches; the fake interpreter only prints its arguments.
        (scripts/"env_vars.sh").write_bytes(b":\n")
        self.prefix = self.root/"existing conda envs"/"vllm"
        self.python = self.prefix/"bin"/"python"
        self.python.parent.mkdir(parents=True)
        self.env = os.environ.copy()

    @staticmethod
    def shell_path(path):
        value = path.resolve().as_posix()
        return "/"+value[0].lower()+value[2:] if os.name=="nt" else value

    def run_launcher(self,*args):
        return subprocess.run([BASH,self.shell_path(self.launcher),*args],env=self.env,
                              capture_output=True,text=True,timeout=15)

    def test_launcher_uses_active_prefix_with_spaces_and_preserves_arguments(self):
        self.python.write_bytes(b'#!/usr/bin/env bash\nprintf "%s\\n" "ACTIVE_CONDA_PYTHON" "$@"\n')
        self.python.chmod(0o755)
        self.env["CONDA_PREFIX"] = self.shell_path(self.prefix)
        syntax = subprocess.run([BASH,"-n",self.shell_path(self.launcher)],
                                capture_output=True,text=True,timeout=15)
        self.assertEqual(0,syntax.returncode,syntax.stderr)
        result = self.run_launcher("--preflight","--config","server config.json")
        self.assertEqual(0,result.returncode,result.stderr)
        lines = result.stdout.splitlines()
        self.assertEqual("ACTIVE_CONDA_PYTHON",lines[0])
        self.assertTrue(lines[1].endswith("/server/serve.py"))
        self.assertEqual(["--preflight","--config","server config.json"],lines[2:])

    def test_launcher_requests_activation_if_no_environment_is_active(self):
        self.env.pop("CONDA_PREFIX",None)
        result = self.run_launcher("--preflight")
        self.assertNotEqual(0,result.returncode)
        self.assertIn("conda activate vllm",result.stderr)
        self.assertEqual("",result.stdout)

    def test_launcher_rejects_missing_python_in_the_active_environment(self):
        self.env["CONDA_PREFIX"] = self.shell_path(self.prefix)
        result = self.run_launcher("--preflight")
        self.assertNotEqual(0,result.returncode)
        self.assertIn("Missing Python interpreter in the active conda environment",result.stderr)
        self.assertEqual("",result.stdout)


if __name__ == "__main__":
    unittest.main()
