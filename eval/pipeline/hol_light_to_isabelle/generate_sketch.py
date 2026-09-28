from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, RESULTS_DIR, append_jsonl, key, prompt_hash, read_jsonl,
    repo_path, select, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.generate_draft import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.prompt import normalize_visible_content
from eval.pipeline.hol_light_to_isabelle.sketch_prompt import (
    SKETCH_PROMPT_VERSION, build_sketch_prompt,
)
from eval.pipeline.proof_transfer.llm import (
    DEFAULT_DRAFT_MODEL, DraftModelConfig, call_draft_model,
)


DEFAULT_OUTPUT = RESULTS_DIR + "/babel_formal_v2_sketches.jsonl"


def latest_drafts(path: str, *, topic: str | None = None,
                  target_key: str | None = None, limit: int | None = None) -> list[dict]:
    latest = {}
    for record in read_jsonl(path):
        latest[key(record)] = record
    return select(latest.values(), topic=topic, target_key=target_key, limit=limit)


def generate_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT,
                      topic: str | None = None, target_key: str | None = None,
                      limit: int | None = None, samples: int = 1,
                      model: str = DEFAULT_DRAFT_MODEL, reasoning_effort: str = "high",
                      max_output_tokens: int = 16000, resume: bool = True,
                      continue_on_error: bool = True, dry_run: bool = False) -> int:
    if samples < 1:
        raise ValueError("samples must be positive")
    records = latest_drafts(input_path, topic=topic, target_key=target_key, limit=limit)
    if not records:
        raise ValueError("no matching V2 Draft records")
    if dry_run:
        prompt = build_sketch_prompt(records[0])
        print(json.dumps({
            "selected_records": len(records), "samples": samples,
            "first_key": key(records[0]), "prompt_version": prompt.version,
            "system_prompt": prompt.system_prompt, "user_prompt": prompt.user_prompt,
        }, ensure_ascii=False, indent=2))
        return 0

    output = repo_path(output_path)
    if not resume:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("", encoding="utf-8")
    previous = read_jsonl(output_path) if resume and output.exists() else []
    completed = {
        (key(r), int(r["sample_idx"]), r.get("sketch_prompt_sha256"),
         r.get("sketch_model", {}).get("model"),
         r.get("sketch_model", {}).get("reasoning_effort"),
         r.get("sketch_model", {}).get("max_output_tokens"))
        for r in previous if r.get("isabelle_proof") and not r.get("sketch_error")
        and r.get("sketch_prompt_version") == SKETCH_PROMPT_VERSION
    }
    config = DraftModelConfig(model=model, reasoning_effort=reasoning_effort,
                              max_output_tokens=max_output_tokens)
    written = 0
    for record in records:
        if not record.get("draft") or record.get("draft_error"):
            print(f"skip missing Draft: {record['topic']}/{record['target_key']}")
            continue
        prompt = build_sketch_prompt(record)
        digest = prompt_hash(prompt.system_prompt, prompt.user_prompt)
        for sample_idx in range(samples):
            if (key(record), sample_idx, digest, model, reasoning_effort,
                    max_output_tokens) in completed:
                continue
            result = dict(record)
            result.update({
                "sample_idx": sample_idx,
                "sketch_prompt_version": prompt.version,
                "sketch_prompt_sha256": digest,
                "sketch_model": config.to_metadata(),
                "sketch_generated_at": datetime.now(timezone.utc).isoformat(),
            })
            start = time.monotonic()
            try:
                result["isabelle_proof"] = normalize_visible_content(call_draft_model(
                    system_prompt=prompt.system_prompt, user_prompt=prompt.user_prompt,
                    config=config))
                if not result["isabelle_proof"]:
                    raise ValueError("empty visible Isabelle proof")
                result["sketch_error"] = None
            except Exception as exc:
                if not continue_on_error:
                    raise
                result["isabelle_proof"] = ""
                result["sketch_error"] = f"{type(exc).__name__}: {exc}"
            result["sketch_duration_seconds"] = round(time.monotonic() - start, 3)
            append_jsonl(output_path, result)
            written += 1
            print(f"sketch {record['topic']}/{record['target_key']} sample={sample_idx}")
    return written


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate Isabelle Sketch proofs from V2 Drafts.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--input", default=DEFAULT_INPUT)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--reasoning-effort", default="high")
    parser.add_argument("--max-output-tokens", type=int, default=16000)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    written = generate_sketches(
        input_path=args.input, output_path=args.output, topic=args.topic,
        target_key=args.target_key, limit=args.limit, samples=args.samples,
        model=args.model, reasoning_effort=args.reasoning_effort,
        max_output_tokens=args.max_output_tokens, resume=not args.no_resume,
        continue_on_error=not args.fail_fast, dry_run=args.dry_run)
    if not args.dry_run:
        print(f"Wrote {written} Isabelle Sketch records to {repo_path(args.output)}")


if __name__ == "__main__":
    main()
