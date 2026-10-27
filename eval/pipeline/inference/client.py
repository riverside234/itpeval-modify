"""Final-content-only Responses and local Chat Completions clients."""

from __future__ import annotations

import json
import os
import re
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import ProxyHandler, Request, build_opener, urlopen
from urllib.parse import urlsplit

from .config import InferenceConfig


class InferenceError(ValueError):
    def __init__(self, message: str, *, metadata: dict | None = None):
        super().__init__(message)
        self.metadata = metadata or {}


class GeneratedText(str):
    """A string for legacy callers, carrying safe generation statistics."""
    def __new__(cls, value: str, metadata: dict):
        result = super().__new__(cls,value)
        result.metadata = metadata
        return result


def _field(value: Any, name: str, default=None):
    return value.get(name,default) if isinstance(value,dict) else getattr(value,name,default)


def response_content_only(response: Any) -> str:
    content = _field(response,"output_text")
    if isinstance(content,str) and content:
        return content.strip()
    texts = []
    for item in _field(response,"output",[]) or []:
        if _field(item,"type") == "message":
            texts.extend(_field(part,"text","") for part in _field(item,"content",[]) or []
                         if _field(part,"type") == "output_text" and _field(part,"text"))
    return "\n".join(texts).strip()


def visible_text(content: Any) -> str:
    if not isinstance(content,str):
        raise InferenceError("response did not contain final text")
    # Do not let an unfinished thinking block become a Draft or Sketch.
    remaining = content
    while match := re.search(r"<think\b[^>]*>",remaining,re.I):
        end = re.search(r"</think\s*>",remaining[match.end():],re.I)
        if end is None:
            raise InferenceError("response contains unfinished thinking")
        close = match.end()+end.end()
        inner = remaining[match.end():match.end()+end.start()]
        if re.search(r"<think\b",inner,re.I):
            raise InferenceError("response contains nested thinking markers")
        remaining = remaining[:match.start()]+remaining[close:]
    if re.search(r"</?think\b",remaining,re.I):
        raise InferenceError("response contains unmatched thinking markers")
    if not remaining.strip():
        raise InferenceError("response did not contain nonempty final text")
    return remaining.strip()


def _usage(response: Any) -> dict:
    source = _field(response,"usage") or {}
    result = {}
    for name in ("input_tokens","output_tokens","prompt_tokens","completion_tokens","total_tokens"):
        value = _field(source,name)
        if isinstance(value,int) and not isinstance(value,bool):
            result[name] = value
    for detail in ("output_tokens_details","completion_tokens_details"):
        reasoning = _field(_field(source,detail) or {},"reasoning_tokens")
        if isinstance(reasoning,int) and not isinstance(reasoning,bool):
            result["reasoning_tokens"] = reasoning
    cached = _field(_field(source,"input_tokens_details") or _field(source,"prompt_tokens_details") or {},"cached_tokens")
    if isinstance(cached,int):
        result["cached_tokens"] = cached
    return result


def _request(config: InferenceConfig, url: str, payload: dict | None = None) -> dict:
    key = os.environ.get(config.api_key_env,"EMPTY") if config.api_key_env else "EMPTY"
    request = Request(url, headers={"Content-Type":"application/json","Authorization":"Bearer "+key},
                      data=json.dumps(payload,ensure_ascii=False).encode("utf-8") if payload is not None else None)
    try:
        # A local model endpoint must not be routed through HTTP_PROXY.
        open_request = (build_opener(ProxyHandler({})).open
                        if urlsplit(url).hostname in {"localhost","127.0.0.1","::1"} else urlopen)
        with open_request(request,timeout=config.timeout_s or 3600) as response:
            result = json.load(response)
    except HTTPError as exc:
        # Never persist error bodies that may echo prompts or model reasoning.
        status = exc.code
        exc.close()
        raise InferenceError(f"vLLM HTTP {status} at {request.selector.split('?')[0]}") from exc
    except (URLError,TimeoutError,OSError) as exc:
        raise InferenceError("vLLM server is unavailable or timed out") from exc
    except (ValueError,UnicodeError) as exc:
        raise InferenceError("vLLM returned invalid JSON") from exc
    if not isinstance(result,dict):
        raise InferenceError("vLLM returned a non-object response")
    return result


def server_preflight(config: InferenceConfig) -> dict:
    if config.backend != "vllm":
        raise ValueError("server_preflight requires vllm")
    if config.server_info is None:
        raise InferenceError("missing server manifest; start vllm/launch_qwen.sh first")
    models = _request(config,config.base_url.rstrip("/")+"/models").get("data",[])
    matching = [model for model in models if model.get("id") == config.model]
    if len(matching) != 1:
        raise InferenceError("vLLM does not serve the requested model alias")
    model = matching[0]
    if model.get("root") != config.server_info["model_path"]:
        raise InferenceError("vLLM model root does not match the pinned server manifest")
    base = config.base_url.rstrip("/").removesuffix("/v1")
    version = _request(config,base+"/version").get("version")
    if version != config.server_info["versions"].get("vllm"):
        raise InferenceError("vLLM runtime version does not match the server manifest")
    return {"model":config.model,"vllm_version":version}


def token_budget(config: InferenceConfig, messages: list[dict]) -> dict:
    base = config.base_url.rstrip("/").removesuffix("/v1")
    response = _request(config,base+"/tokenize",{
        "model":config.model,"messages":messages,"add_generation_prompt":True,
        "chat_template_kwargs":config.template_kwargs(),
    })
    count = response.get("count")
    limit = config.server_info["settings"].get("max_model_len")
    actual_limit = response.get("max_model_len",limit)
    if not isinstance(count,int) or isinstance(count,bool) or count < 1:
        raise InferenceError("vLLM tokenizer did not return a valid token count")
    if not isinstance(limit,int) or limit < 1 or (actual_limit is not None and actual_limit != limit):
        raise InferenceError("vLLM context limit does not match the server manifest")
    metadata = {"prompt_tokens":count,"max_output_tokens":config.max_output_tokens,"context_limit":limit}
    if count+config.max_output_tokens > limit:
        raise InferenceError("prompt plus output budget exceeds the configured context limit",
                             metadata={"token_budget":metadata})
    return metadata


def generate_text(*, system_prompt: str, user_prompt: str, config: InferenceConfig) -> GeneratedText:
    if config.backend == "api":
        import openai
        env_name = config.api_key_env or "OPENAI_API_KEY"
        if not os.environ.get(env_name):
            raise InferenceError("missing API key environment variable: "+env_name)
        options = {"api_key":os.environ[env_name]}
        if config.base_url is not None:
            options["base_url"] = config.base_url
        if config.timeout_s is not None:
            options["timeout"] = config.timeout_s
        request = {
            "model":config.model,"max_output_tokens":config.max_output_tokens,
            "input":[
                {"role":"system","content":[{"type":"input_text","text":system_prompt}]},
                {"role":"user","content":[{"type":"input_text","text":user_prompt}]},
            ],
        }
        if config.reasoning_effort is not None:
            request["reasoning"] = {"effort":config.reasoning_effort}
        request.update(config.sampling())
        try:
            with openai.OpenAI(**options) as client:
                response = client.responses.create(**request)
        except Exception as exc:
            metadata = {"backend":"api","error_type":type(exc).__name__}
            status_code = getattr(exc,"status_code",None)
            if isinstance(status_code,int):
                metadata["status_code"] = status_code
            raise InferenceError("API request failed: "+type(exc).__name__,metadata=metadata) from None
        status = _field(response,"status")
        metadata = {"backend":"api","response_id":_field(response,"id"),
                    "model":_field(response,"model",config.model),"finish_reason":status,
                    "usage":_usage(response)}
        if status is not None and status != "completed":
            raise InferenceError("API response was not completed",metadata=metadata)
        try:
            return GeneratedText(visible_text(response_content_only(response)),metadata)
        except InferenceError as exc:
            raise InferenceError(str(exc),metadata=metadata) from exc

    server_preflight(config)
    messages = [{"role":"system","content":system_prompt},{"role":"user","content":user_prompt}]
    budget = token_budget(config,messages)
    response = _request(config,config.base_url.rstrip("/")+"/chat/completions",{
        "model":config.model,"messages":messages,"max_tokens":config.max_output_tokens,
        "stream":False, **config.sampling(), "chat_template_kwargs":config.template_kwargs(),
    })
    choices = response.get("choices")
    if not isinstance(choices,list) or len(choices) != 1:
        raise InferenceError("vLLM must return exactly one completion")
    choice = choices[0]
    metadata = {"backend":"vllm","response_id":response.get("id"),"model":response.get("model"),
                "finish_reason":choice.get("finish_reason"),"usage":_usage(response),"token_budget":budget}
    if choice.get("finish_reason") != "stop":
        raise InferenceError("vLLM response was truncated or did not finish normally",metadata=metadata)
    if response.get("model") != config.model:
        raise InferenceError("vLLM response model does not match the requested model",metadata=metadata)
    try:
        return GeneratedText(visible_text((choice.get("message") or {}).get("content")),metadata)
    except InferenceError as exc:
        raise InferenceError(str(exc),metadata=metadata) from exc
