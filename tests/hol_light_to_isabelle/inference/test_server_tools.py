import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
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
        with patch.object(self.serve.platform,"system",return_value="Linux"), patch.object(
                self.serve.sys,"prefix",str(repository_path("."))):
            with self.assertRaisesRegex(ValueError,"isolated"):
                self.serve.preflight(self.settings.read_config())

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


if __name__ == "__main__":
    unittest.main()
