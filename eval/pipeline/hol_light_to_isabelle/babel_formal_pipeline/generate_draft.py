from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    LAB_REPO_ROOT, RESULTS_DIR, append_jsonl, fingerprint, key, prompt_hash, public_record, read_jsonl,
    repo_path, require_source, select, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import (
    DRAFT_PROMPT_VERSION, build_draft_prompt, normalize_visible_content,
)
from eval.pipeline.inference.config import output_path_for_profile
from eval.pipeline.proof_transfer.llm import (
    DEFAULT_DRAFT_MODEL, DEFAULT_REASONING_EFFORT, DraftModelConfig, call_draft_model, resolve_model_config,
)


DEFAULT_OUTPUT = RESULTS_DIR + "/babel_formal_v2_drafts.jsonl"


def generate_drafts(*, input_path: str = DEFAULT_INPUT, output_path: str | None = None,
                    topic: str | None = None, target_key: str | None = None,
                    limit: int | None = None, model: str | None = None,
                    reasoning_effort: str | None = None,
                    max_output_tokens: int | None = None, resume: bool = True,
                    continue_on_error: bool = True, dry_run: bool = False,
                      prompt_builder=None, prompt_version: str | None = None,
                      expected_source: str = "babel-formal", llm_config=None,
                      default_output: str = DEFAULT_OUTPUT) -> int:
    records = select(read_jsonl(input_path), topic=topic, target_key=target_key, limit=limit)
    require_source(records, expected_source)
    builder = prompt_builder or build_draft_prompt
    version = prompt_version or DRAFT_PROMPT_VERSION
    if not records:
        raise ValueError("no matching parsed V2 records")
    config = resolve_model_config(
        llm_config, model=model, reasoning_effort=reasoning_effort,
        max_output_tokens=max_output_tokens, default_effort="medium",
        dry_run=dry_run)
    output_path = output_path_for_profile(output_path, default_output, config)
    if dry_run:
        prompt = builder(records[0])
        print(json.dumps({
            "llm_config": config.to_metadata(), "output_path": str(output_path),
            "selected_records": len(records), "first_key": key(records[0]),
            "prompt_version": prompt.version,
            "system_prompt": prompt.system_prompt, "user_prompt": prompt.user_prompt,
        }, ensure_ascii=False, indent=2))
        return 0

    output = repo_path(output_path)
    if output == repo_path(input_path):
        raise ValueError("parsed input and Draft output must be distinct")
    if not resume:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("", encoding="utf-8")
    previous = read_jsonl(output_path) if resume and output.exists() else []
    model_metadata = config.to_metadata()
    completed = {
        (key(row), row.get("draft_prompt_sha256"), fingerprint(row.get("draft_model", {}))): row
        for row in previous if row.get("draft_prompt_version") == version
        and row.get("draft") and not row.get("draft_error")
    }
    latest = {key(row): row for row in previous}
    written = 0
    for index, record in enumerate(records, 1):
        prompt = builder(record)
        digest = prompt_hash(prompt.system_prompt, prompt.user_prompt)
        completed_key = (key(record), digest, fingerprint(model_metadata))
        cached = completed.get(completed_key)
        if cached is not None and all(cached.get(name) == value for name,value in public_record(record).items()):
            if latest.get(key(record)) != cached:
                append_jsonl(output_path, public_record(cached))
                latest[key(record)] = cached
            print(f"[{index}/{len(records)}] skip {record['topic']}/{record['target_key']}")
            continue
        result = public_record(record)
        result.update({
            "draft_prompt_version": prompt.version,
            "draft_prompt_sha256": digest,
            "draft_model": model_metadata,
            "draft_fingerprint": fingerprint(completed_key),
            "draft_generated_at": datetime.now(timezone.utc).isoformat(),
        })
        start = time.monotonic()
        try:
            response = call_draft_model(
                system_prompt=prompt.system_prompt, user_prompt=prompt.user_prompt,
                config=config)
            result["draft_response"] = getattr(response, "metadata", {})
            result["draft"] = normalize_visible_content(response)
            if not result["draft"]:
                raise ValueError("empty visible Draft")
            result["draft_error"] = None
        except Exception as exc:
            if not continue_on_error:
                raise
            result["draft"] = ""
            result["draft_response"] = getattr(exc, "metadata", {})
            result["draft_error"] = f"{type(exc).__name__}: {exc}"
        result["draft_duration_seconds"] = round(time.monotonic() - start, 3)
        append_jsonl(output_path, result)
        latest[key(record)] = result
        if result.get("draft") and not result.get("draft_error"):
            completed[completed_key] = result
        written += 1
        print(f"[{index}/{len(records)}] draft {record['topic']}/{record['target_key']}")
    return written


def main(*, legacy: bool = False, default_input: str = DEFAULT_INPUT,
         default_output: str = DEFAULT_OUTPUT, prompt_builder=None,
         prompt_version: str | None = None, expected_source: str = "babel-formal") -> None:
    parser = argparse.ArgumentParser(description="Generate HOL Light-derived V2 drafts.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--input", default=default_input)
    parser.add_argument("--output")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--llm-config", help="API or vLLM JSON profile; omitted means the existing API defaults.")
    parser.add_argument("--model", default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--max-output-tokens", type=int, default=None)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    written = generate_drafts(
        input_path=args.input, output_path=args.output, topic=args.topic,
        target_key=args.target_key, limit=args.limit, model=args.model,
        reasoning_effort=args.reasoning_effort, max_output_tokens=args.max_output_tokens,
        resume=not args.no_resume, continue_on_error=not args.fail_fast,
        dry_run=args.dry_run, prompt_builder=prompt_builder,
        prompt_version=prompt_version, expected_source=expected_source,
        llm_config=args.llm_config, default_output=default_output)
    if not args.dry_run:
        print(f"Wrote {written} new Draft records to {repo_path(output_path_for_profile(args.output, default_output, resolve_model_config(args.llm_config, dry_run=True)))}")


if __name__ == "__main__":
    main()
