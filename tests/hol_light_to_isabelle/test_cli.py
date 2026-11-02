import ast
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.common import RESULTS_DIR, repo_path, write_jsonl
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig


class CliTests(unittest.TestCase):
    def run_module(self, name, *args):
        run = subprocess.run(
            [sys.executable, "-B", "-m", "eval.pipeline.hol_light_to_isabelle." + name, *args],
            cwd=repo_path("."), capture_output=True, text=True, timeout=30)
        self.assertEqual(0, run.returncode, run.stderr)
        return run

    def test_all_stage_entry_points_load_without_pisa(self):
        for module in (
            "run_babel", "generate_sketch", "verify_isabelle",
            "v2_itpeval.run_babel", "v2_itpeval.generate_sketch", "v2_itpeval.verify_isabelle",
            "v2_dsp.run_babel", "v2_dsp.export_dsp", "v2_dsp.generate_sketch",
            "v2_dsp.preflight", "v2_dsp.prove",
        ):
            with self.subTest(module=module):
                self.assertIn("--help", self.run_module(module, "--help").stdout)

    def test_both_runner_previews_use_the_same_draft_without_creating_outputs(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="v2-cli-test-", dir=base) as folder:
            path = Path(folder) / "drafts.jsonl"
            record = extract_records(topic="circle_average",
                                     target_key="circleAverage_center_independent")[0]
            record["draft"] = "SHARED_DRAFT_MARKER"
            write_jsonl(path, [record])
            for name in ("v2_itpeval.run_babel", "v2_dsp.run_babel"):
                args = ["--drafts", str(path), "--dry-run"]
                if name.startswith("v2_dsp"):
                    args.extend(["--config", "not-installed.local.json"])
                preview = json.loads(self.run_module(name, *args).stdout)
                self.assertIn("SHARED_DRAFT_MARKER", preview["user_prompt"])
            self.assertEqual(["drafts.jsonl"], [item.name for item in Path(folder).iterdir()])

    def test_python_310_syntax_and_config_example(self):
        for path in repo_path("eval/pipeline/hol_light_to_isabelle").rglob("*.py"):
            with self.subTest(path=path.name):
                ast.parse(path.read_text(encoding="utf-8"), filename=str(path), feature_version=(3, 10))
        config = DspConfig.load("eval/configs/hol_light_to_isabelle/v2_dsp.example.json")
        self.assertEqual("isabelle-native", config.backend)
        self.assertEqual("Isabelle2026", config.expected_isabelle_version)
        self.assertTrue(Path(config.isabelle_home).is_relative_to(repo_path(".")))


if __name__ == "__main__":
    unittest.main()
