"""Generate Isabelle sketches from the exported saved Drafts."""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    LAB_REPO_ROOT, RESULTS_DIR, append_jsonl, fingerprint, key, latest_records,
    prompt_hash, public_record, read_jsonl, repo_path, require_source, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import normalize_visible_content
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import input_metadata, normalize_body
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.export_dsp import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.sketch_prompt import (
    SKETCH_PROMPT_VERSION, build_sketch_prompt,
)
from eval.pipeline.inference.config import output_path_for_profile
from eval.pipeline.proof_transfer.llm import DEFAULT_DRAFT_MODEL, DraftModelConfig, call_draft_model, resolve_model_config


DEFAULT_OUTPUT = RESULTS_DIR + "/v2-dsp/babel_formal_v2_sketches.jsonl"


def generate_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str | None = None,
                      topic: str | None = None, target_key: str | None = None,
                      limit: int | None = None, samples: int = 1,
                      model: str | None = None, reasoning_effort: str | None = None,
                      max_output_tokens: int | None = None, resume: bool = True,
                      continue_on_error: bool = True, dry_run: bool = False,
                      blocked_targets: dict | None = None,
                      prompt_builder=None, prompt_version: str | None = None,
                      expected_source: str = "babel-formal", llm_config=None,
                      default_output: str = DEFAULT_OUTPUT) -> int:
    if samples < 1:
        raise ValueError("samples must be positive")
    records = latest_records(input_path, topic=topic, target_key=target_key, limit=limit)
    require_source(records, expected_source)
    builder = prompt_builder or build_sketch_prompt
    version = prompt_version or SKETCH_PROMPT_VERSION
    if not records:
        raise ValueError("no matching exported Drafts")
    config = resolve_model_config(
        llm_config, model=model, reasoning_effort=reasoning_effort,
        max_output_tokens=max_output_tokens, default_effort="high",
        dry_run=dry_run)
    output_path = output_path_for_profile(output_path, default_output, config, draft_records=records)
    if dry_run:
        input_metadata(records[0])
        prompt = builder(records[0])
        print(json.dumps({"llm_config": config.to_metadata(), "output_path": str(output_path),
            "selected_records": len(records), "samples": samples,
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
                 and not row.get("sketch_error") and row.get("sketch_prompt_version") == version}
    latest_sample = {(key(row), row["sample_idx"]): row.get("sketch_fingerprint")
                     for row in previous}
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
            prompt = builder(record)
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
                      "sketch_prompt_version": version,
                      "sketch_prompt_sha256": digest, "sketch_model": config.to_metadata(),
                      "sketch_generated_at": datetime.now(timezone.utc).isoformat()}
            started = time.monotonic()
            try:
                if input_error:
                    raise ValueError(input_error)
                response = call_draft_model(
                    system_prompt=prompt.system_prompt, user_prompt=prompt.user_prompt,
                    config=config)
                result["sketch_response"] = getattr(response, "metadata", {})
                body = normalize_visible_content(response)
                result["isabelle_sketch"] = normalize_body(body, allow_hammer=True)
                result["sketch_error"], result["failure_category"] = None, None
            except Exception as exc:
                if not continue_on_error:
                    raise
                result["isabelle_sketch"] = ""
                result["sketch_response"] = getattr(exc, "metadata", {})
                result["sketch_error"] = f"{type(exc).__name__}: {exc}"
                result["failure_category"] = input_category if input_error else "sketch_error"
            result["sketch_duration_seconds"] = round(time.monotonic() - started, 3)
            append_jsonl(output_path, result)
            latest_sample[(key(record), sample_idx)] = identity
            written += 1
            print(f"DSP sketch {record['topic']}/{record['target_key']} sample={sample_idx}")
    return written


def main(*, legacy: bool = False, default_input: str = DEFAULT_INPUT,
         default_output: str = DEFAULT_OUTPUT, prompt_builder=None,
         prompt_version: str | None = None, expected_source: str = "babel-formal") -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--input", default=default_input)
    parser.add_argument("--output")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--llm-config", help="API or vLLM JSON profile; omitted means the existing API defaults.")
    parser.add_argument("--model", default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--max-output-tokens", type=int, default=None)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    selected_drafts = latest_records(args.input, topic=args.topic, target_key=args.target_key, limit=args.limit)
    chosen_config = resolve_model_config(
        args.llm_config, model=args.model, reasoning_effort=args.reasoning_effort,
        max_output_tokens=args.max_output_tokens, default_effort="high", dry_run=args.dry_run)
    args.output = output_path_for_profile(args.output, default_output, chosen_config, draft_records=selected_drafts)
    generate_sketches(input_path=args.input, output_path=args.output, topic=args.topic,
                      target_key=args.target_key, limit=args.limit, samples=args.samples,
                      model=args.model, reasoning_effort=args.reasoning_effort,
                      max_output_tokens=args.max_output_tokens, resume=not args.no_resume,
                      continue_on_error=not args.fail_fast, dry_run=args.dry_run, prompt_builder=prompt_builder,
        prompt_version=prompt_version, expected_source=expected_source,
        llm_config=chosen_config, default_output=default_output)


if __name__ == "__main__":
    main()
