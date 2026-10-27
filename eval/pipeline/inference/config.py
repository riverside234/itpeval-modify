"""Validated inference profiles and stable generation identity."""

from __future__ import annotations

from dataclasses import dataclass, field, fields, replace
import hashlib
import json
import math
from pathlib import Path
import re
from typing import Any, Literal
from urllib.parse import urlsplit

from eval.pipeline.config import REPO_ROOT

DEFAULT_DRAFT_MODEL = "gpt-5.6-terra"
ReasoningEffort = Literal["none", "minimal", "low", "medium", "high", "xhigh"]
DEFAULT_REASONING_EFFORT: ReasoningEffort = "medium"
QWEN_MODEL = "Qwen/Qwen3.8-27B"
QWEN_REVISION = "1d4bf0f2ff6012fd82039f2fa52739d0dd7c60c0"


def repository_path(path: str | Path) -> Path:
    root = REPO_ROOT.resolve()
    path = Path(path).expanduser()
    path = (path if path.is_absolute() else root/path).resolve()
    if not path.is_relative_to(root):
        raise ValueError(f"inference path must be under {root}: {path}")
    return path


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value, sort_keys=True, ensure_ascii=True, separators=(",", ":"),
        allow_nan=False).encode()).hexdigest()


@dataclass(frozen=True)
class InferenceConfig:
    # First three fields preserve the old DraftModelConfig constructor.
    model: str = DEFAULT_DRAFT_MODEL
    reasoning_effort: str | None = DEFAULT_REASONING_EFFORT
    max_output_tokens: int = 16000
    backend: str = "api"
    base_url: str | None = None
    api_key_env: str | None = None
    timeout_s: float | None = None
    temperature: float | None = None
    top_p: float | None = None
    top_k: int | None = None
    min_p: float | None = None
    presence_penalty: float | None = None
    repetition_penalty: float | None = None
    seed: int | None = None
    enable_thinking: bool | None = None
    model_revision: str | None = None
    tokenizer_revision: str | None = None
    server_manifest: str | None = None
    server_info: dict | None = field(default=None, repr=False)

    def __post_init__(self):
        if self.backend not in {"api", "vllm"}:
            raise ValueError("backend must be api or vllm")
        if not isinstance(self.model, str) or not self.model.strip():
            raise ValueError("model must be nonempty")
        if isinstance(self.max_output_tokens, bool) or not isinstance(self.max_output_tokens, int) or self.max_output_tokens < 1:
            raise ValueError("max_output_tokens must be a positive integer")
        if self.base_url is not None:
            if not isinstance(self.base_url,str):
                raise ValueError("base_url must be a string")
            parsed = urlsplit(self.base_url)
            if (parsed.scheme not in {"http", "https"} or not parsed.hostname
                    or parsed.username or parsed.password or parsed.query or parsed.fragment):
                raise ValueError("base_url must be an HTTP(S) URL without credentials, query, or fragment")
            if not parsed.path.rstrip("/").endswith("/v1"):
                raise ValueError("base_url must end with /v1")
        if self.api_key_env is not None and (not isinstance(self.api_key_env,str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", self.api_key_env)):
            raise ValueError("api_key_env must be an environment variable name")
        for name in ("timeout_s", "temperature", "top_p", "min_p", "presence_penalty", "repetition_penalty"):
            value = getattr(self, name)
            if value is not None and (isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value)):
                raise ValueError(name+" must be finite")
        if self.timeout_s is not None and self.timeout_s <= 0:
            raise ValueError("timeout_s must be positive")
        if self.temperature is not None and not 0 <= self.temperature <= 2:
            raise ValueError("temperature must be in [0, 2]")
        if self.top_p is not None and not 0 < self.top_p <= 1:
            raise ValueError("top_p must be in (0, 1]")
        if self.min_p is not None and not 0 <= self.min_p <= 1:
            raise ValueError("min_p must be in [0, 1]")
        if self.presence_penalty is not None and not -2 <= self.presence_penalty <= 2:
            raise ValueError("presence_penalty must be in [-2, 2]")
        if self.repetition_penalty is not None and self.repetition_penalty <= 0:
            raise ValueError("repetition_penalty must be positive")
        for name in ("top_k", "seed"):
            value = getattr(self, name)
            if value is not None and (isinstance(value, bool) or not isinstance(value, int) or value < (-1 if name == "top_k" else 0)):
                raise ValueError(name+" must be an integer in its supported range")
        if self.enable_thinking is not None and not isinstance(self.enable_thinking, bool):
            raise ValueError("enable_thinking must be a boolean")
        if self.backend == "api":
            if self.reasoning_effort not in {None,"none","minimal","low","medium","high","xhigh"}:
                raise ValueError("unsupported API reasoning_effort")
            if any(getattr(self, name) is not None for name in (
                    "top_k","min_p","repetition_penalty","presence_penalty","seed","enable_thinking",
                    "model_revision","tokenizer_revision","server_manifest","server_info")):
                raise ValueError("Qwen/server-specific options require backend=vllm")
        else:
            if not self.base_url:
                raise ValueError("vllm requires base_url")
            if self.enable_thinking is None:
                raise ValueError("vllm requires explicit enable_thinking")
            if self.enable_thinking and self.reasoning_effort not in {"low","medium","xhigh"}:
                raise ValueError("Qwen thinking effort must be low, medium, or xhigh; GPT high is not supported")
            if not self.enable_thinking and self.reasoning_effort is not None:
                raise ValueError("disable thinking with reasoning_effort=null")
            for name in ("model_revision","tokenizer_revision"):
                if not isinstance(getattr(self,name),str) or not re.fullmatch(r"[0-9a-f]{40}", getattr(self,name)):
                    raise ValueError(name+" must pin a full checkpoint commit")
            if not self.server_manifest:
                raise ValueError("vllm requires a server_manifest path")
            repository_path(self.server_manifest)

    def sampling(self) -> dict:
        names = ("temperature","top_p","top_k","min_p","presence_penalty","repetition_penalty","seed")
        return {name:getattr(self,name) for name in names if getattr(self,name) is not None}

    def template_kwargs(self) -> dict:
        result = {"enable_thinking":self.enable_thinking}
        if self.enable_thinking:
            result["reasoning_effort"] = self.reasoning_effort
        return result

    def to_metadata(self) -> dict[str, Any]:
        # Keep this exact default shape for old API resume fingerprints.
        result = {"provider":"openai" if self.backend == "api" else "vllm",
                  "model":self.model, "reasoning_effort":self.reasoning_effort,
                  "max_output_tokens":self.max_output_tokens, "stored_output":"content_only"}
        for name in ("base_url","api_key_env","timeout_s"):
            if getattr(self,name) is not None:
                result[name] = getattr(self,name)
        if self.sampling():
            result["sampling"] = self.sampling()
        if self.backend == "vllm":
            result.update(backend="vllm", api_mode="chat_completions",
                          enable_thinking=self.enable_thinking,
                          model_revision=self.model_revision, tokenizer_revision=self.tokenizer_revision,
                          server_manifest=self.server_manifest,
                          server_identity=self.server_info)
        return result

    def with_runtime(self) -> InferenceConfig:
        if self.backend != "vllm":
            return self
        path = repository_path(self.server_manifest)
        if not path.is_file():
            return self
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("schema_version") != "itpeval_qwen_server_v1":
            raise ValueError("unsupported vLLM server manifest")
        if (data.get("model") != self.model or data.get("model_revision") != self.model_revision
                or data.get("tokenizer_revision") != self.tokenizer_revision):
            raise ValueError("server manifest does not match requested checkpoint")
        # Timestamps, logs and PIDs do not change model identity.
        names = ("model","model_revision","tokenizer_revision","model_path","tokenizer_sha256",
                 "template_sha256","versions","settings","base_url","gpu")
        identity = {name:data.get(name) for name in names}
        if identity["base_url"] != self.base_url.rstrip("/"):
            raise ValueError("server manifest base_url mismatch")
        if not isinstance(identity["settings"],dict) or not isinstance(identity["versions"],dict):
            raise ValueError("incomplete server manifest")
        if not isinstance(identity["model_path"],str) or not identity["model_path"]:
            raise ValueError("server manifest has no model path")
        if not isinstance(identity["versions"].get("vllm"),str) or not identity["versions"]["vllm"]:
            raise ValueError("server manifest has no vLLM version")
        limit = identity["settings"].get("max_model_len")
        if isinstance(limit,bool) or not isinstance(limit,int) or limit < 1:
            raise ValueError("server manifest has no valid context limit")
        for name in ("tokenizer_sha256","template_sha256"):
            if not isinstance(identity[name],str) or not re.fullmatch(r"[0-9a-f]{64}",identity[name]):
                raise ValueError("server manifest has no valid "+name)
        return replace(self,server_info=identity)


def resolve_config(profile: str | Path | InferenceConfig | None = None, *,
                   model: str | None = None, reasoning_effort: str | None = None,
                   max_output_tokens: int | None = None, default_effort: str = "medium",
                   dry_run: bool = False) -> InferenceConfig:
    if isinstance(profile, InferenceConfig):
        config = profile
        overrides = {name:value for name,value in (
            ("model",model),("reasoning_effort",reasoning_effort),("max_output_tokens",max_output_tokens))
                     if value is not None}
        config = replace(config,**overrides)
    else:
        data = {}
        if profile is not None:
            data = json.loads(repository_path(profile).read_text(encoding="utf-8"))
            if not isinstance(data,dict):
                raise ValueError("LLM profile must be a JSON object")
            allowed = {item.name for item in fields(InferenceConfig)}-{"server_info"}
            if set(data)-allowed:
                raise ValueError("unknown LLM profile fields: "+", ".join(sorted(set(data)-allowed)))
        data.setdefault("model",DEFAULT_DRAFT_MODEL)
        if data.get("backend","api") == "vllm":
            data.setdefault("tokenizer_revision",data.get("model_revision"))
            data.setdefault("reasoning_effort","medium" if data.get("enable_thinking",True) else None)
        else:
            data.setdefault("reasoning_effort",default_effort)
        for name,value in (("model",model),("reasoning_effort",reasoning_effort),("max_output_tokens",max_output_tokens)):
            if value is not None:
                data[name] = value
        config = InferenceConfig(**data)
    return config if dry_run else config.with_runtime()


def output_path_for_profile(path: str | Path | None, default: str,
                            config: InferenceConfig, *, draft_records: list[dict] | None = None) -> str | Path:
    if path is not None:
        return path
    target = Path(default)
    folder = "qwen_vllm" if config.backend == "vllm" else None
    if draft_records:
        providers = {(row.get("draft_model") or {}).get("provider","openai") for row in draft_records}
        if config.backend == "vllm" and providers != {"vllm"}:
            folder = "api_draft_qwen_sketch" if providers == {"openai"} else "mixed_drafts_qwen_sketch"
        elif config.backend == "api" and providers != {"openai"}:
            folder = "qwen_draft_api_sketch" if providers == {"vllm"} else "mixed_drafts_api_sketch"
    if folder:
        target = target.parent/folder/target.name
    return str(target)
