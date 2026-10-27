from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline import generate_draft as drafts
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    latest_records, read_jsonl, write_jsonl,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.generate_sketch import generate_sketches as dsp_sketches
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.export_dsp import export_drafts
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline import generate_draft as hundred_drafts
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as hundred_records
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_itpeval.generate_sketch import generate_sketches as hundred_sketches
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.generate_sketch import generate_sketches as hundred_dsp_sketches
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.export_dsp import export_drafts as hundred_export
from eval.pipeline.inference.config import repository_path, resolve_config
from inference.fixtures import fake_vllm

B = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline"


class PipelineTests(unittest.TestCase):
    def setUp(self):
        base = repository_path("eval/results/inference_tests")
        base.mkdir(parents=True,exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(dir=base)
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name)
        self.record = extract_records(topic="circle_average",target_key="circleAverage_center_independent")[0]

    def test_api_and_vllm_cache_separation_and_restoring_an_older_cached_draft(self):
        source,output = self.path/"records.jsonl",self.path/"drafts.jsonl"
        write_jsonl(source,[self.record])
        with patch(B+".generate_draft.call_draft_model",return_value="API DRAFT") as api:
            self.assertEqual(1,drafts.generate_drafts(input_path=source,output_path=output))
            api.assert_called_once()
        with fake_vllm(self.path) as state:
            self.assertEqual(1,drafts.generate_drafts(input_path=source,output_path=output,llm_config=state["profile_path"]))
            current = latest_records(output)[0]
            self.assertEqual("vllm",current["draft_model"]["provider"])
            self.assertEqual("stop",current["draft_response"]["finish_reason"])
            with patch(B+".generate_draft.call_draft_model") as api:
                self.assertEqual(0,drafts.generate_drafts(input_path=source,output_path=output))
                api.assert_not_called()
            self.assertEqual("API DRAFT",latest_records(output)[0]["draft"])
            self.assertEqual(3,len(read_jsonl(output)))
            # Same Qwen profile uses its saved result without another request.
            self.assertEqual(0,drafts.generate_drafts(input_path=source,output_path=output,llm_config=state["profile_path"]))
            self.assertEqual(1,len([url for url,_ in state["calls"] if url.endswith("/chat/completions")]))
            # Sampling is part of the cache identity.
            state["profile"]["temperature"] = 0.7
            state["profile_path"].write_text(json.dumps(state["profile"]),encoding="utf-8")
            self.assertEqual(1,drafts.generate_drafts(input_path=source,output_path=output,llm_config=state["profile_path"]))
            self.assertEqual(2,len([url for url,_ in state["calls"] if url.endswith("/chat/completions")]))
            self.assertNotIn("HIDDEN_REASONING_MARKER",output.read_text(encoding="utf-8"))

    def test_both_datasets_pass_visible_drafts_to_both_sketch_backends(self):
        datasets = [
            ("babel",self.record,drafts.generate_drafts,generate_sketches,dsp_sketches,export_drafts),
            ("hundred",hundred_records(topic="030_the_ballot_problem",target_key="all_countings")[0],
             hundred_drafts.generate_drafts,hundred_sketches,hundred_dsp_sketches,hundred_export),
        ]
        with fake_vllm(self.path) as state, patch.dict(os.environ,{},clear=True):
            for name,record,draft_fn,sketch_fn,dsp_fn,export_fn in datasets:
                with self.subTest(dataset=name):
                    source,draft_path,itp,dsp_input,dsp_path = [self.path/(name+"_"+suffix+".jsonl") for suffix in ("records","draft","itp","export","dsp")]
                    write_jsonl(source,[record])
                    draft_fn(input_path=source,output_path=draft_path,llm_config=state["profile_path"])
                    sketch_fn(input_path=draft_path,output_path=itp,llm_config=state["profile_path"],samples=2)
                    exported = export_fn(input_path=draft_path,output_path=dsp_input)
                    dsp_fn(input_path=dsp_input,output_path=dsp_path,llm_config=state["profile_path"],samples=2)
                    self.assertEqual(2,len(read_jsonl(itp)))
                    self.assertTrue(all(row["isabelle_proof"]=="by simp" for row in read_jsonl(itp)))
                    self.assertTrue(all("sledgehammer" in row["isabelle_sketch"] for row in read_jsonl(dsp_path)))
                    self.assertEqual(latest_records(draft_path)[0]["draft"],exported[0]["informal_proof"])
                    self.assertEqual(record["isabelle_statement"],exported[0]["formal_statement"])

    def test_truncated_drafts_remain_failures_and_do_not_call_sketch_model(self):
        source,output,sketch = self.path/"records.jsonl",self.path/"drafts.jsonl",self.path/"sketches.jsonl"
        write_jsonl(source,[self.record])
        with fake_vllm(self.path) as state:
            state.update(finish_reason="length",content="PARTIAL_FINAL_MUST_NOT_SURVIVE")
            drafts.generate_drafts(input_path=source,output_path=output,llm_config=state["profile_path"])
            row = read_jsonl(output)[0]
            self.assertEqual("",row["draft"])
            self.assertEqual("length",row["draft_response"]["finish_reason"])
            self.assertNotIn("PARTIAL_FINAL_MUST_NOT_SURVIVE",output.read_text(encoding="utf-8"))
            generate_sketches(input_path=output,output_path=sketch,llm_config=state["profile_path"],samples=2)
            self.assertTrue(all(row["failure_category"]=="input_error" for row in read_jsonl(sketch)))
            self.assertEqual(1,len([url for url,_ in state["calls"] if url.endswith("/chat/completions")]))

    def test_runtime_manifest_change_invalidates_draft_resume(self):
        source,output = self.path/"records.jsonl",self.path/"drafts.jsonl"
        write_jsonl(source,[self.record])
        with fake_vllm(self.path) as state:
            drafts.generate_drafts(input_path=source,output_path=output,llm_config=state["profile_path"])
            state["manifest"]["settings"]["dtype"] = "float16"
            state["manifest_path"].write_text(json.dumps(state["manifest"]),encoding="utf-8")
            drafts.generate_drafts(input_path=source,output_path=output,llm_config=state["profile_path"])
            self.assertEqual(2,len([url for url,_ in state["calls"] if url.endswith("/chat/completions")]))

    def test_unavailable_local_server_does_not_fall_back_to_paid_api(self):
        source,output = self.path/"records.jsonl",self.path/"drafts.jsonl"
        write_jsonl(source,[self.record])
        with fake_vllm(self.path) as state:
            profile = state["profile_path"]
        drafts.generate_drafts(input_path=source,output_path=output,llm_config=profile)
        row = read_jsonl(output)[0]
        self.assertEqual("",row["draft"])
        self.assertIn("unavailable",row["draft_error"])

    def test_new_profiles_preview_and_select_distinct_default_outputs(self):
        source = self.path/"records.jsonl"
        write_jsonl(source,[self.record])
        captured = io.StringIO()
        with redirect_stdout(captured):
            drafts.generate_drafts(input_path=source,llm_config="eval/configs/inference/qwen_vllm.example.json",
                                   dry_run=True, default_output=str(self.path/"drafts.jsonl"))
        preview = json.loads(captured.getvalue())
        self.assertIn("qwen_vllm",preview["output_path"])
        self.assertEqual("vllm",preview["llm_config"]["backend"])
        self.assertFalse(repository_path(preview["output_path"]).is_file())

    def test_all_saved_draft_runners_and_legacy_accept_profiles(self):
        source,draft = self.path/"records.jsonl",self.path/"drafts.jsonl"
        write_jsonl(source,[self.record])
        write_jsonl(draft,[{**self.record,"draft":"SHARED_DRAFT_FOR_PROFILE_TEST","draft_error":None}])
        hundred = hundred_records(topic="030_the_ballot_problem",target_key="all_countings")[0]
        hundred_path = self.path/"hundred_drafts.jsonl"
        write_jsonl(hundred_path,[{**hundred,"draft":"SHARED_DRAFT_FOR_PROFILE_TEST","draft_error":None}])
        profile = "eval/configs/inference/qwen_vllm.example.json"
        for dataset,path in (("babel_formal_pipeline",draft),("hundred_theorems_pipeline",hundred_path)):
            for pipeline in ("v2_itpeval","v2_dsp"):
                cmd = [sys.executable,"-B","-m","eval.pipeline.hol_light_to_isabelle."+dataset+"."+pipeline+".run",
                       "--drafts",str(path),"--sketch-llm-config",profile,"--dry-run"]
                if pipeline=="v2_dsp":
                    cmd += ["--config","not-installed.local.json"]
                result = subprocess.run(cmd,capture_output=True,text=True,check=True,timeout=30)
                preview = json.loads(result.stdout)
                self.assertEqual("vllm",preview["llm_config"]["backend"])
                self.assertIn("SHARED_DRAFT_FOR_PROFILE_TEST",preview["user_prompt"])
        # Explicit CLI overrides beat the profile, without contacting a server.
        result = subprocess.run(
            [sys.executable,"-B","-m",B+".generate_draft","--input",str(source),
             "--llm-config",profile,"--reasoning-effort","low","--max-output-tokens","99","--dry-run"],
            capture_output=True,text=True,check=True,timeout=30)
        preview = json.loads(result.stdout)
        self.assertEqual(("low",99),(preview["llm_config"]["reasoning_effort"],preview["llm_config"]["max_output_tokens"]))
        result = subprocess.run(
            [sys.executable,"-B","-m",B+".run_babel","--records",str(source),
             "--draft-llm-config",profile,"--sketch-llm-config","eval/configs/inference/api.example.json","--dry-run"],
            capture_output=True,text=True,check=True,timeout=30)
        self.assertEqual("vllm",json.loads(result.stdout)["llm_config"]["backend"])


if __name__ == "__main__":
    unittest.main()
