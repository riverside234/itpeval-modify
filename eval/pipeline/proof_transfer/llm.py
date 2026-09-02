from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Any, Literal


ReasoningEffort = Literal["none", "minimal", "low", "medium", "high", "xhigh"]

DEFAULT_DRAFT_MODEL = "gpt-5.6-terra"
DEFAULT_REASONING_EFFORT: ReasoningEffort = "medium"


@dataclass(frozen=True)
class DraftModelConfig:
    model: str = DEFAULT_DRAFT_MODEL
    reasoning_effort: ReasoningEffort = DEFAULT_REASONING_EFFORT
    max_output_tokens: int = 16000

    def to_metadata(self) -> dict[str, Any]:
        return {
            "provider": "openai",
            "model": self.model,
            "reasoning_effort": self.reasoning_effort,
            "max_output_tokens": self.max_output_tokens,
            "stored_output": "content_only",
        }


def _load_keys() -> None:
    try:
        from dotenv import load_dotenv
        from pathlib import Path

        load_dotenv(Path(__file__).parents[2] / ".env")
    except ImportError:
        pass


_loaded = False


def _ensure_loaded() -> None:
    global _loaded
    if not _loaded:
        _load_keys()
        _loaded = True


def response_content_only(response: Any) -> str:
    """Extract only final visible output text, ignoring reasoning/thinking items."""
    output_text = (
        response.get("output_text")
        if isinstance(response, dict)
        else getattr(response, "output_text", None)
    )
    if output_text:
        return str(output_text).strip()

    texts: list[str] = []
    output = (
        response.get("output", [])
        if isinstance(response, dict)
        else getattr(response, "output", [])
    )
    for item in output or []:
        item_type = item.get("type") if isinstance(item, dict) else getattr(item, "type", None)
        if item_type != "message":
            continue
        item_content = (
            item.get("content", [])
            if isinstance(item, dict)
            else getattr(item, "content", [])
        )
        for part in item_content or []:
            part_type = part.get("type") if isinstance(part, dict) else getattr(part, "type", None)
            if part_type != "output_text":
                continue
            text = part.get("text", "") if isinstance(part, dict) else getattr(part, "text", "")
            if text:
                texts.append(str(text))
    return "\n".join(texts).strip()


def call_draft_model(
    *,
    system_prompt: str,
    user_prompt: str,
    config: DraftModelConfig | None = None,
) -> str:
    """Call OpenAI for proof-transfer Draft generation and return content only."""
    _ensure_loaded()

    import openai

    cfg = config or DraftModelConfig()
    client = openai.OpenAI(api_key=os.environ["OPENAI_API_KEY"])
    response = client.responses.create(
        model=cfg.model,
        reasoning={"effort": cfg.reasoning_effort},
        max_output_tokens=cfg.max_output_tokens,
        input=[
            {
                "role": "system",
                "content": [{"type": "input_text", "text": system_prompt}],
            },
            {
                "role": "user",
                "content": [{"type": "input_text", "text": user_prompt}],
            },
        ],
    )
    content = response_content_only(response)
    if not content:
        raise ValueError("OpenAI response did not contain final output text")
    return content
