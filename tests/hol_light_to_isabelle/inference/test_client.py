import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from eval.pipeline.inference.client import (
    InferenceError, generate_text, response_content_only, server_preflight,
)
from eval.pipeline.inference.config import (
    InferenceConfig, QWEN_MODEL, QWEN_REVISION, resolve_config, repository_path,
)
from inference.fixtures import fake_vllm


class ClientTests(unittest.TestCase):
    def setUp(self):
        base = repository_path("eval/results/inference_tests")
        base.mkdir(parents=True,exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(dir=base)
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name)

    def api(self,response):
        client = Mock()
        client.responses.create.return_value = response
        manager = Mock()
        manager.__enter__ = Mock(return_value=client)
        manager.__exit__ = Mock(return_value=False)
        factory = Mock(return_value=manager)
        return client,factory

    def test_existing_api_request_and_metadata_contract(self):
        response = SimpleNamespace(
            output_text="VISIBLE", status="completed",id="api-response",model="gpt-5.6-terra",
            usage={"input_tokens":10,"output_tokens":12,"total_tokens":22,
                   "output_tokens_details":{"reasoning_tokens":8}})
        client,factory = self.api(response)
        with patch.dict("sys.modules",{"openai":SimpleNamespace(OpenAI=factory)}), patch.dict(
                os.environ,{"OPENAI_API_KEY":"test-key"}):
            result = generate_text(system_prompt="SYSTEM",user_prompt="USER",config=InferenceConfig())
        self.assertEqual("VISIBLE",result)
        self.assertEqual(8,result.metadata["usage"]["reasoning_tokens"])
        factory.assert_called_once_with(api_key="test-key")
        self.assertEqual({"effort":"medium"},client.responses.create.call_args.kwargs["reasoning"])
        self.assertEqual("input_text",client.responses.create.call_args.kwargs["input"][0]["content"][0]["type"])
        self.assertEqual({
            "provider":"openai","model":"gpt-5.6-terra","reasoning_effort":"medium",
            "max_output_tokens":16000,"stored_output":"content_only"},InferenceConfig().to_metadata())

    def test_api_errors_do_not_echo_keys_or_raw_provider_bodies(self):
        client,factory = self.api(None)
        client.responses.create.side_effect = RuntimeError("SECRET_KEY_AND_RAW_PROVIDER_BODY")
        with patch.dict("sys.modules",{"openai":SimpleNamespace(OpenAI=factory)}), patch.dict(
                os.environ,{"OPENAI_API_KEY":"test-key"}):
            with self.assertRaises(InferenceError) as failure:
                generate_text(system_prompt="s",user_prompt="u",config=InferenceConfig())
        self.assertNotIn("SECRET_KEY",str(failure.exception))
        self.assertEqual("RuntimeError",failure.exception.metadata["error_type"])

    def test_api_incomplete_response_cannot_be_saved_as_success(self):
        response = {"status":"incomplete","output_text":"partial proof","usage":{"output_tokens":128}}
        client,factory = self.api(response)
        with patch.dict("sys.modules",{"openai":SimpleNamespace(OpenAI=factory)}), patch.dict(
                os.environ,{"OPENAI_API_KEY":"test-key"}):
            with self.assertRaises(InferenceError) as failure:
                generate_text(system_prompt="s",user_prompt="u",config=InferenceConfig())
        self.assertEqual("incomplete",failure.exception.metadata["finish_reason"])
        self.assertNotIn("partial proof",str(failure.exception))

    def test_response_extractor_ignores_reasoning_items(self):
        response = {"output":[{"type":"reasoning","text":"HIDDEN"},
                              {"type":"message","content":[{"type":"output_text","text":"FINAL"}]}]}
        self.assertEqual("FINAL",response_content_only(response))

    def test_vllm_needs_no_openai_key_and_uses_chat_template_settings(self):
        with fake_vllm(self.path) as state, patch.dict(os.environ,{},clear=True):
            config = resolve_config(state["profile_path"])
            result = generate_text(system_prompt="SYSTEM",user_prompt="USER",config=config)
            self.assertIn("### Step",result)
            self.assertNotIn("HIDDEN",result)
            self.assertEqual("stop",result.metadata["finish_reason"])
            request = next(payload for url,payload in state["calls"] if url.endswith("/chat/completions"))
            self.assertEqual(QWEN_MODEL,request["model"])
            self.assertEqual({"enable_thinking":True,"reasoning_effort":"medium"},request["chat_template_kwargs"])
            self.assertEqual(128,request["max_tokens"])
            self.assertNotIn("reasoning",request)
            self.assertEqual("SYSTEM",request["messages"][0]["content"])
            self.assertNotIn("HIDDEN_REASONING_MARKER",json.dumps(result.metadata))

    def test_vllm_rejects_truncated_unfinished_or_empty_outputs(self):
        cases = [("length","partial"),("stop","<think>unfinished"),("stop",""),
                 ("stop","</think>unmatched"),("stop","<think>thought only</think>")]
        with fake_vllm(self.path) as state:
            config = resolve_config(state["profile_path"])
            for reason,content in cases:
                with self.subTest(reason=reason,content=content):
                    state.update(finish_reason=reason,content=content)
                    with self.assertRaises(InferenceError):
                        generate_text(system_prompt="s",user_prompt="u",config=config)

    def test_complete_thinking_block_is_removed_from_visible_output(self):
        with fake_vllm(self.path) as state:
            state["content"] = "<think>PRIVATE</think>FINAL"
            result = generate_text(system_prompt="s",user_prompt="u",config=resolve_config(state["profile_path"]))
            self.assertEqual("FINAL",result)

    def test_overflow_is_rejected_without_truncation_or_generation(self):
        with fake_vllm(self.path) as state:
            state["token_count"] = 65500
            with self.assertRaisesRegex(InferenceError,"exceeds") as failure:
                generate_text(system_prompt="s",user_prompt="u",config=resolve_config(state["profile_path"]))
            self.assertEqual(65500,failure.exception.metadata["token_budget"]["prompt_tokens"])
            self.assertFalse([url for url,_ in state["calls"] if url.endswith("/chat/completions")])

    def test_wrong_server_model_or_version_is_rejected(self):
        with fake_vllm(self.path) as state:
            config = resolve_config(state["profile_path"])
            state["model"] = "wrong"
            with self.assertRaisesRegex(InferenceError,"alias"):
                server_preflight(config)
            state["model"] = QWEN_MODEL
            state["version"] = "unexpected"
            with self.assertRaisesRegex(InferenceError,"version"):
                server_preflight(config)

    def test_server_http_error_does_not_persist_raw_body(self):
        with fake_vllm(self.path) as state:
            state["http_error"] = True
            with self.assertRaises(InferenceError) as failure:
                generate_text(system_prompt="s",user_prompt="u",config=resolve_config(state["profile_path"]))
            self.assertNotIn("DO_NOT_PERSIST",str(failure.exception))

    def test_profile_defaults_cli_overrides_and_invalid_settings(self):
        qwen = resolve_config("eval/configs/inference/qwen_vllm.example.json",dry_run=True)
        self.assertEqual("medium",qwen.reasoning_effort)
        changed = resolve_config(qwen,reasoning_effort="low",max_output_tokens=77,dry_run=True)
        self.assertEqual(("low",77),(changed.reasoning_effort,changed.max_output_tokens))
        self.assertEqual("high",resolve_config("eval/configs/inference/api.example.json",default_effort="high",dry_run=True).reasoning_effort)
        for options in ({"reasoning_effort":"high"},{"max_output_tokens":0},{"temperature":float("nan")}):
            with self.subTest(options=options),self.assertRaises(ValueError):
                from dataclasses import replace
                replace(qwen,**options)
        path = self.path/"bad.json"
        path.write_text('{"api_key":"MUST_NOT_STORE_A_KEY"}',encoding="utf-8")
        with self.assertRaisesRegex(ValueError,"unknown"):
            resolve_config(path)

    def test_mixed_backend_default_outputs_are_separate(self):
        from eval.pipeline.inference.config import output_path_for_profile
        api = InferenceConfig()
        qwen = resolve_config("eval/configs/inference/qwen_vllm.example.json",dry_run=True)
        path = "eval/results/stage/results.jsonl"
        api_draft = [{"draft_model":{"provider":"openai"}}]
        qwen_draft = [{"draft_model":{"provider":"vllm"}}]
        self.assertEqual(Path(path),Path(output_path_for_profile(None,path,api,draft_records=api_draft)))
        self.assertIn("qwen_draft_api_sketch",str(output_path_for_profile(None,path,api,draft_records=qwen_draft)))
        self.assertIn("api_draft_qwen_sketch",str(output_path_for_profile(None,path,qwen,draft_records=api_draft)))
        self.assertIn("qwen_vllm",str(output_path_for_profile(None,path,qwen,draft_records=qwen_draft)))

    def test_loopback_inference_bypasses_environment_proxy(self):
        with fake_vllm(self.path) as state, patch.dict(
                os.environ,{"HTTP_PROXY":"http://127.0.0.1:1","NO_PROXY":""}):
            result = generate_text(system_prompt="s",user_prompt="u",config=resolve_config(state["profile_path"]))
            self.assertTrue(str(result))

    def test_missing_or_changed_manifest_is_an_explicit_failure(self):
        config = resolve_config("eval/configs/inference/qwen_vllm.example.json",dry_run=True)
        with self.assertRaisesRegex(InferenceError,"manifest"):
            server_preflight(config)
        with fake_vllm(self.path) as state:
            data = state["manifest"]
            data["model_revision"] = "b"*40
            state["manifest_path"].write_text(json.dumps(data),encoding="utf-8")
            with self.assertRaisesRegex(ValueError,"checkpoint"):
                resolve_config(state["profile_path"])


if __name__ == "__main__":
    unittest.main()
