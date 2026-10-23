"""Generate Isabelle sketches from the exported saved Drafts."""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, RESULTS_DIR, append_jsonl, fingerprint, key, latest_records,
    prompt_hash, public_record, read_jsonl, repo_path, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.prompt import normalize_visible_content
from eval.pipeline.hol_light_to_isabelle.theory_context import input_metadata, normalize_body
from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.v2_dsp.sketch_prompt import (
    SKETCH_PROMPT_VERSION, build_sketch_prompt,
)
from eval.pipeline.proof_transfer.llm import DEFAULT_DRAFT_MODEL, DraftModelConfig, call_draft_model


DEFAULT_OUTPUT = RESULTS_DIR + "/v2-dsp/babel_formal_v2_sketches.jsonl"


def generate_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT,
                      topic: str | None = None, target_key: str | None = None,
                      limit: int | None = None, samples: int = 1,
                      model: str = DEFAULT_DRAFT_MODEL, reasoning_effort: str = "high",
                      max_output_tokens: int = 16000, resume: bool = True,
                      continue_on_error: bool = True, dry_run: bool = False,
                      blocked_targets: dict | None = None) -> int:
    if samples < 1:
        raise ValueError("samples must be positive")
    records = latest_records(input_path, topic=topic, target_key=target_key, limit=limit)
    if not records:
        raise ValueError("no matching exported Drafts")
    if dry_run:
        input_metadata(records[0])
        prompt = build_sketch_prompt(records[0])
        print(json.dumps({"selected_records": len(records), "samples": samples,
                          "pipeline": "v2-dsp", "prompt_version": prompt.version,
                          "system_prompt": prompt.system_prompt,
                          "user_prompt": prompt.user_prompt}, indent=2))
        return 0
    output = repo_path(output_path)
    if output == repo_path(input_path):
        raise ValueError("exported input and Sketch output must be distinct")
    if not resume:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("", encoding="utf-8")
    previous = read_jsonl(output_path) if resume and output.is_file() else []
    completed = {row.get("sketch_fingerprint"): row for row in previous
                 if row.get("pipeline") == "v2-dsp" and row.get("isabelle_sketch")
                 and not row.get("sketch_error")}
    latest_sample = {(key(row), row["sample_idx"]): row.get("sketch_fingerprint")
                     for row in previous}
    config = DraftModelConfig(model=model, reasoning_effort=reasoning_effort,
                              max_output_tokens=max_output_tokens)
    written = 0
    for record in records:
        input_category = "input_error"
        try:
            if blocked_targets and key(record) in blocked_targets:
                input_category = "context_error"
                raise ValueError(blocked_targets[key(record)])
            if record.get("pipeline") != "v2-dsp":
                raise ValueError("use export_dsp before generating DSP sketches")
            metadata = input_metadata(record)
            prompt = build_sketch_prompt(record)
            digest = prompt_hash(prompt.system_prompt, prompt.user_prompt)
            input_error = None
        except ValueError as exc:
            if not continue_on_error:
                raise
            metadata, prompt, digest, input_error = {}, None, "", str(exc)
        for sample_idx in range(samples):
            identity = fingerprint({
                "pipeline": "v2-dsp", "target": key(record),
                "input": metadata.get("input_fingerprint"), "prompt": digest,
                "model": config.to_metadata(), "sample_idx": sample_idx,
            })
            if not input_error and identity in completed:
                if latest_sample.get((key(record), sample_idx)) != identity:
                    append_jsonl(output_path, public_record(completed[identity]))
                    latest_sample[(key(record), sample_idx)] = identity
                continue
            result = {**public_record(record), **metadata, "pipeline": "v2-dsp",
                      "sample_idx": sample_idx, "sketch_fingerprint": identity,
                      "sketch_prompt_version": SKETCH_PROMPT_VERSION,
                      "sketch_prompt_sha256": digest, "sketch_model": config.to_metadata(),
                      "sketch_generated_at": datetime.now(timezone.utc).isoformat()}
            started = time.monotonic()
            try:
                if input_error:
                    raise ValueError(input_error)
                body = normalize_visible_content(call_draft_model(
                    system_prompt=prompt.system_prompt, user_prompt=prompt.user_prompt,
                    config=config))
                result["isabelle_sketch"] = normalize_body(body, allow_hammer=True)
                result["sketch_error"], result["failure_category"] = None, None
            except Exception as exc:
                if not continue_on_error:
                    raise
                result["isabelle_sketch"] = ""
                result["sketch_error"] = f"{type(exc).__name__}: {exc}"
                result["failure_category"] = input_category if input_error else "sketch_error"
            result["sketch_duration_seconds"] = round(time.monotonic() - started, 3)
            append_jsonl(output_path, result)
            latest_sample[(key(record), sample_idx)] = identity
            written += 1
            print(f"DSP sketch {record['topic']}/{record['target_key']} sample={sample_idx}")
    return written


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
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
    generate_sketches(input_path=args.input, output_path=args.output, topic=args.topic,
                      target_key=args.target_key, limit=args.limit, samples=args.samples,
                      model=args.model, reasoning_effort=args.reasoning_effort,
                      max_output_tokens=args.max_output_tokens, resume=not args.no_resume,
                      continue_on_error=not args.fail_fast, dry_run=args.dry_run)


if __name__ == "__main__":
    main()
