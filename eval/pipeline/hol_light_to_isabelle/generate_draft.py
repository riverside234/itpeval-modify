from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, RESULTS_DIR, append_jsonl, key, prompt_hash, read_jsonl,
    repo_path, select, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.prompt import (
    DRAFT_PROMPT_VERSION, build_draft_prompt, normalize_visible_content,
)
from eval.pipeline.proof_transfer.llm import (
    DEFAULT_DRAFT_MODEL, DEFAULT_REASONING_EFFORT, DraftModelConfig, call_draft_model,
)


DEFAULT_OUTPUT = RESULTS_DIR + "/babel_formal_v2_drafts.jsonl"


def generate_drafts(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT,
                    topic: str | None = None, target_key: str | None = None,
                    limit: int | None = None, model: str = DEFAULT_DRAFT_MODEL,
                    reasoning_effort: str = DEFAULT_REASONING_EFFORT,
                    max_output_tokens: int = 16000, resume: bool = True,
                    continue_on_error: bool = True, dry_run: bool = False) -> int:
    records = select(read_jsonl(input_path), topic=topic, target_key=target_key, limit=limit)
    if not records:
        raise ValueError("no matching parsed V2 records")
    if dry_run:
        prompt = build_draft_prompt(records[0])
        print(json.dumps({
            "selected_records": len(records), "first_key": key(records[0]),
            "prompt_version": prompt.version,
            "system_prompt": prompt.system_prompt, "user_prompt": prompt.user_prompt,
        }, ensure_ascii=False, indent=2))
        return 0

    output = repo_path(output_path)
    if not resume:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("", encoding="utf-8")
    previous = read_jsonl(output_path) if resume and output.exists() else []
    completed = {(key(r), r.get("draft_prompt_sha256"),
                  r.get("draft_model", {}).get("model"),
                  r.get("draft_model", {}).get("reasoning_effort"),
                  r.get("draft_model", {}).get("max_output_tokens")) for r in previous
                 if r.get("draft_prompt_version") == DRAFT_PROMPT_VERSION
                 and r.get("draft") and not r.get("draft_error")}
    config = DraftModelConfig(model=model, reasoning_effort=reasoning_effort,
                              max_output_tokens=max_output_tokens)
    written = 0
    for index, record in enumerate(records, 1):
        prompt = build_draft_prompt(record)
        digest = prompt_hash(prompt.system_prompt, prompt.user_prompt)
        completed_key = (key(record), digest, model, reasoning_effort, max_output_tokens)
        if completed_key in completed:
            print(f"[{index}/{len(records)}] skip {record['topic']}/{record['target_key']}")
            continue
        result = dict(record)
        result.update({
            "draft_prompt_version": prompt.version,
            "draft_prompt_sha256": digest,
            "draft_model": config.to_metadata(),
            "draft_generated_at": datetime.now(timezone.utc).isoformat(),
        })
        start = time.monotonic()
        try:
            result["draft"] = normalize_visible_content(call_draft_model(
                system_prompt=prompt.system_prompt, user_prompt=prompt.user_prompt,
                config=config))
            if not result["draft"]:
                raise ValueError("empty visible Draft")
            result["draft_error"] = None
        except Exception as exc:
            if not continue_on_error:
                raise
            result["draft"] = ""
            result["draft_error"] = f"{type(exc).__name__}: {exc}"
        result["draft_duration_seconds"] = round(time.monotonic() - start, 3)
        append_jsonl(output_path, result)
        written += 1
        print(f"[{index}/{len(records)}] draft {record['topic']}/{record['target_key']}")
    return written


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate HOL Light-derived V2 drafts.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--input", default=DEFAULT_INPUT)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--reasoning-effort", default=DEFAULT_REASONING_EFFORT)
    parser.add_argument("--max-output-tokens", type=int, default=16000)
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
        dry_run=args.dry_run)
    if not args.dry_run:
        print(f"Wrote {written} new Draft records to {repo_path(args.output)}")


if __name__ == "__main__":
    main()
