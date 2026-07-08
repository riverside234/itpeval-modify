from __future__ import annotations

import json
import os
from datetime import datetime, timezone
from pathlib import Path

_GEMINI_BASE = "https://generativelanguage.googleapis.com/v1beta"


def _load_env() -> None:
    try:
        from dotenv import load_dotenv
        load_dotenv(Path(__file__).parent.parent / ".env")
    except ImportError:
        pass


_loaded = False


def _ensure_loaded() -> None:
    global _loaded
    if not _loaded:
        _load_env()
        _loaded = True


def openai_submit(
    requests: list[dict],
    model_id: str,
    max_tokens: int = 16000,
    temperature: float = 0.0,
) -> str:
    """Submit a batch to the OpenAI Batch API. Returns the batch ID.

    Each request dict must have: custom_id, system_prompt, user_prompt.
    """
    _ensure_loaded()
    import openai

    client = openai.OpenAI(api_key=os.environ["OPENAI_API_KEY"])

    # OpenAI batch input is one chat-completion request per JSONL row
    lines = []
    for req in requests:
        lines.append(json.dumps({
            "custom_id": req["custom_id"],
            "method": "POST",
            "url": "/v1/chat/completions",
            "body": {
                "model": model_id,
                "max_completion_tokens": max_tokens,
                "messages": [
                    {"role": "system", "content": req["system_prompt"]},
                    {"role": "user",   "content": req["user_prompt"]},
                ],
            },
        }))
    jsonl_bytes = "\n".join(lines).encode()

    file_obj = client.files.create(file=("batch_input.jsonl", jsonl_bytes), purpose="batch")
    batch = client.batches.create(
        input_file_id=file_obj.id,
        endpoint="/v1/chat/completions",
        completion_window="24h",
    )
    return batch.id


def openai_poll(batch_id: str) -> tuple[str, dict[str, str] | None]:
    """Poll an OpenAI batch job.

    Returns (status, results) where results maps custom_id → generated text,
    or (status, None) if not yet complete.
    Status values: 'validating', 'in_progress', 'completed', 'failed',
    'expired', 'cancelled'.
    """
    _ensure_loaded()
    import openai

    client = openai.OpenAI(api_key=os.environ["OPENAI_API_KEY"])
    batch = client.batches.retrieve(batch_id)

    if batch.status == "completed":
        raw = client.files.content(batch.output_file_id).content.decode()
        results = {}
        for line in raw.splitlines():
            r = json.loads(line)
            text = r["response"]["body"]["choices"][0]["message"]["content"]
            results[r["custom_id"]] = text
        return "completed", results

    if batch.status in ("failed", "expired", "cancelled"):
        return batch.status, None

    return batch.status, None


def anthropic_submit(
    requests: list[dict],
    model_id: str,
    max_tokens: int = 4096,
    temperature: float = 0.0,
) -> str:
    """Submit a batch to the Anthropic Message Batches API. Returns the batch ID."""
    _ensure_loaded()
    import anthropic

    client = anthropic.Anthropic(api_key=os.environ["ANTHROPIC_API_KEY"])

    batch = client.messages.batches.create(requests=[
        {
            "custom_id": req["custom_id"],
            "params": {
                "model": model_id,
                "max_tokens": max_tokens,
                "temperature": temperature,
                "system": req["system_prompt"],
                "messages": [{"role": "user", "content": req["user_prompt"]}],
            },
        }
        for req in requests
    ])
    return batch.id


def anthropic_poll(batch_id: str) -> tuple[str, dict[str, str] | None]:
    """Poll an Anthropic batch job.

    Returns (status, results) or (status, None) if not yet complete.
    Status values: 'in_progress', 'ended'.
    """
    _ensure_loaded()
    import anthropic

    client = anthropic.Anthropic(api_key=os.environ["ANTHROPIC_API_KEY"])
    batch = client.messages.batches.retrieve(batch_id)

    if batch.processing_status == "ended":
        results = {}
        for result in client.messages.batches.results(batch_id):
            if result.result.type == "succeeded":
                results[result.custom_id] = result.result.message.content[0].text
            else:
                results[result.custom_id] = ""
        return "completed", results

    return batch.processing_status, None


def gemini_batch_submit(
    reqs: list[dict],
    model_id: str,
    max_tokens: int = 16000,
    temperature: float = 0.0,
) -> str:
    """Submit a batch job to the Gemini Batch API using the File API.

    Uploads input JSONL via the Gemini File API (API key only, no GCS needed),
    submits the batch job via REST, and returns the batch name for polling.
    """
    _ensure_loaded()
    import requests as http

    api_key = os.environ["GEMINI_API_KEY"]

    # Gemini batch jobs use File API upload followed by a batchGenerateContent call
    lines = []
    for req in reqs:
        lines.append(json.dumps({
            "key": req["custom_id"],
            "request": {
                "system_instruction": {"parts": [{"text": req["system_prompt"]}]},
                "contents": [{"role": "user", "parts": [{"text": req["user_prompt"]}]}],
                "generation_config": {
                    "max_output_tokens": max_tokens,
                    "temperature": temperature,
                },
            },
        }))
    jsonl_bytes = "\n".join(lines).encode()

    _UPLOAD_BASE = "https://generativelanguage.googleapis.com/upload/v1beta"
    init_resp = http.post(
        f"{_UPLOAD_BASE}/files",
        headers={
            "x-goog-api-key": api_key,
            "X-Goog-Upload-Protocol": "resumable",
            "X-Goog-Upload-Command": "start",
            "X-Goog-Upload-Header-Content-Length": str(len(jsonl_bytes)),
            "X-Goog-Upload-Header-Content-Type": "text/plain",
            "Content-Type": "application/json",
        },
        json={"file": {"display_name": "batch_input.jsonl"}},
        timeout=30,
    )
    init_resp.raise_for_status()
    upload_url = init_resp.headers["x-goog-upload-url"]

    upload_resp = http.post(
        upload_url,
        headers={
            "x-goog-api-key": api_key,
            "Content-Length": str(len(jsonl_bytes)),
            "X-Goog-Upload-Offset": "0",
            "X-Goog-Upload-Command": "upload, finalize",
            "Content-Type": "text/plain",
        },
        data=jsonl_bytes,
        timeout=300,
    )
    upload_resp.raise_for_status()
    file_name = upload_resp.json()["file"]["name"]
    print(f"  Uploaded {len(reqs)} requests as {file_name}")

    display_name = f"itp-interop-{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}"
    resp = http.post(
        f"{_GEMINI_BASE}/models/{model_id}:batchGenerateContent",
        headers={"x-goog-api-key": api_key, "Content-Type": "application/json"},
        json={"batch": {"display_name": display_name, "input_config": {"file_name": file_name}}},
    )
    resp.raise_for_status()
    batch_name = resp.json()["name"]
    print(f"  Gemini batch job submitted: {batch_name}")
    return batch_name


def gemini_batch_poll(batch_name: str) -> tuple[str, dict[str, str] | None]:
    """Poll a Gemini batch job submitted via gemini_batch_submit.

    Returns (status, results) or (status, None) if not yet complete.
    Status values: 'running', 'completed', 'failed'.
    """
    _ensure_loaded()
    import requests as http

    api_key = os.environ["GEMINI_API_KEY"]

    resp = http.get(
        f"{_GEMINI_BASE}/{batch_name}",
        headers={"x-goog-api-key": api_key},
    )
    resp.raise_for_status()
    data = resp.json()
    state = data.get("metadata", {}).get("state", "")

    if "SUCCEEDED" in state:
        output_file = (
            data.get("response", {}).get("responsesFile")
            or data.get("metadata", {}).get("output", {}).get("responsesFile", "")
        )
        # Completed Gemini jobs return a file handle containing JSONL responses
        from google import genai

        client = genai.Client(api_key=api_key)
        content = client.files.download(file=output_file).decode()

        results = {}
        for line in content.splitlines():
            if not line.strip():
                continue
            r = json.loads(line)
            key = r.get("key", "")
            candidates = r.get("response", {}).get("candidates", [])
            text = ""
            if candidates:
                parts = candidates[0].get("content", {}).get("parts", [])
                text = parts[0].get("text", "") if parts else ""
            results[key] = text
        return "completed", results

    if "FAILED" in state or "CANCELLED" in state or "EXPIRED" in state:
        return "failed", None

    return "running", None


def submit(model_cfg: dict, requests: list[dict], **kwargs) -> str:
    """Submit a batch job for the given provider. Returns a batch_id string.

    Gemini uses the Gemini File API with GEMINI_API_KEY.
    """
    provider = model_cfg["provider"]
    model_id = model_cfg["id"]

    kwargs.pop("checkpoint_path", None)
    kwargs.pop("gcs_bucket", None)

    if provider == "openai":
        return openai_submit(requests, model_id, **kwargs)
    elif provider == "anthropic":
        return anthropic_submit(requests, model_id, **kwargs)
    elif provider == "gemini":
        return gemini_batch_submit(requests, model_id, **kwargs)
    else:
        raise ValueError(f"Batch not supported for provider: {provider!r}")


def poll(model_cfg: dict, batch_id: str) -> tuple[str, dict[str, str] | None]:
    """Poll a batch job."""
    provider = model_cfg["provider"]
    if provider == "openai":
        return openai_poll(batch_id)
    elif provider == "anthropic":
        return anthropic_poll(batch_id)
    elif provider == "gemini":
        return gemini_batch_poll(batch_id)
    else:
        raise ValueError(f"poll() not applicable for provider: {provider!r}")
