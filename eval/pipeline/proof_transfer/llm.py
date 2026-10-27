"""Backward-compatible proof-transfer facade for API and vLLM inference."""

from __future__ import annotations

from eval.pipeline.inference.config import (
    DEFAULT_DRAFT_MODEL, DEFAULT_REASONING_EFFORT, ReasoningEffort,
    InferenceConfig as DraftModelConfig, resolve_config as resolve_model_config,
)
from eval.pipeline.inference.client import (
    generate_text, response_content_only,
)


def _load_keys() -> None:
    try:
        from dotenv import load_dotenv
        from pathlib import Path
        load_dotenv(Path(__file__).parents[2]/".env")
    except ImportError:
        pass


_loaded = False


def _ensure_loaded() -> None:
    global _loaded
    if not _loaded:
        _load_keys()
        _loaded = True


def call_draft_model(*, system_prompt: str, user_prompt: str,
                     config: DraftModelConfig | None = None) -> str:
    """Return visible text, with optional safe statistics on its metadata attribute."""
    cfg = config or DraftModelConfig()
    if cfg.backend == "api" or cfg.api_key_env:
        _ensure_loaded()
    return generate_text(system_prompt=system_prompt,user_prompt=user_prompt,config=cfg)
