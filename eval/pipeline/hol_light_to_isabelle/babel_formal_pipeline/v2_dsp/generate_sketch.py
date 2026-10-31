"""Generate Isabelle2026 Sketches from saved Drafts or completed HOL Light proofs."""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime, timezone

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    LAB_REPO_ROOT, RESULTS_DIR, append_jsonl, fingerprint, key,
    prompt_hash, public_record, read_jsonl, repo_path, require_source, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import normalize_visible_content
from .input_contract import (MODES, envelope, clean_record, input_metadata, load_inputs,
                             validate_artifacts, normalize_sketch, output_path as native_output_path)
from .direct_sketch_prompt import build_direct_sketch_prompt, DIRECT_PROMPT_VERSION
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.export_dsp import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.sketch_prompt import (
    SKETCH_PROMPT_VERSION, build_sketch_prompt,
)
from eval.pipeline.proof_transfer.llm import call_draft_model, resolve_model_config


DEFAULT_OUTPUT = native_output_path(None, results_dir=RESULTS_DIR, filename="sketches.jsonl", mode="draft")


def generate_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str | None = None,
                      topic: str | None = None, target_key: str | None = None,
                      limit: int | None = None, samples: int = 1,
                      model: str | None = None, reasoning_effort: str | None = None,
                      max_output_tokens: int | None = None, resume: bool = True,
                      continue_on_error: bool = True, dry_run: bool = False,
                      blocked_targets: dict | None = None,
                      prompt_builder=None, prompt_version: str | None = None,
                      expected_source: str = "babel-formal", llm_config=None,
                      default_output: str = DEFAULT_OUTPUT, sketch_source: str = "draft",
                      results_dir: str = RESULTS_DIR) -> int:
    if samples < 1:
        raise ValueError("samples must be positive")
    records = load_inputs(input_path, mode=sketch_source, topic=topic, target_key=target_key, limit=limit)
    require_source(records, expected_source)
    if prompt_builder is None and expected_source == "hundred-theorems":
        import importlib
        module = importlib.import_module("eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp." +
                                        ("direct_sketch_prompt" if sketch_source == "hol-light-proof" else "sketch_prompt"))
        prompt_builder = module.build_direct_sketch_prompt if sketch_source == "hol-light-proof" else module.build_sketch_prompt
        prompt_version = module.DIRECT_PROMPT_VERSION if sketch_source == "hol-light-proof" else module.SKETCH_PROMPT_VERSION
    builder = prompt_builder or (build_direct_sketch_prompt if sketch_source == "hol-light-proof" else build_sketch_prompt)
    version = prompt_version or (DIRECT_PROMPT_VERSION if sketch_source == "hol-light-proof" else SKETCH_PROMPT_VERSION)
    if not records:
        raise ValueError("no matching Sketch inputs")
    config = resolve_model_config(
        llm_config, model=model, reasoning_effort=reasoning_effort,
        max_output_tokens=max_output_tokens, default_effort="high",
        dry_run=dry_run)
    output_path = native_output_path(output_path, results_dir=results_dir, filename="sketches.jsonl",
                                     mode=sketch_source, config=config, records=records)
    if dry_run:
        from .export_dsp import export_record
        preview = export_record(records[0], expected_source=expected_source, sketch_source=sketch_source)
        prompt = builder(preview)
        print(json.dumps({"llm_config": config.to_metadata(), "output_path": str(output_path),
            "selected_records": len(records), "samples": samples,
                          **envelope(sketch_source), "prompt_version": prompt.version,
                          "system_prompt": prompt.system_prompt,
                          "user_prompt": prompt.user_prompt}, indent=2))
        return 0
    output = repo_path(output_path)
    if output == repo_path(input_path):
        raise ValueError("exported input and Sketch output must be distinct")
    if output.is_file():
        validate_artifacts(read_jsonl(output_path), sketch_source)
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
    for raw_record in records:
        from .export_dsp import export_record
        try:
            record = export_record(raw_record, expected_source=expected_source, sketch_source=sketch_source)
        except ValueError as exc:
            record = {**clean_record(raw_record, sketch_source), **envelope(sketch_source), "input_error": str(exc)}
        input_category = "input_error"
        try:
            if blocked_targets and key(record) in blocked_targets:
                blocked = blocked_targets[key(record)]
                input_category = blocked.get("failure_category", "context_error") if isinstance(blocked, dict) else "context_error"
                raise ValueError(blocked.get("error", str(blocked)) if isinstance(blocked, dict) else blocked)
            if record.get("pipeline") != "v2-dsp":
                raise ValueError("use export_dsp before generating DSP sketches")
            metadata = input_metadata(record, sketch_source)
            prompt = builder(record)
            digest = prompt_hash(prompt.system_prompt, prompt.user_prompt)
            input_error = None
        except ValueError as exc:
            if not continue_on_error:
                raise
            metadata, prompt, digest, input_error = {}, None, "", str(exc)
        for sample_idx in range(samples):
            identity = fingerprint({
                **envelope(sketch_source), "target": key(record),
                "input": metadata.get("input_fingerprint"), "prompt": digest,
                "model": config.to_metadata(), "sample_idx": sample_idx,
            })
            if not input_error and identity in completed:
                if latest_sample.get((key(record), sample_idx)) != identity:
                    append_jsonl(output_path, public_record(completed[identity]))
                    latest_sample[(key(record), sample_idx)] = identity
                continue
            result = {**clean_record(record, sketch_source), **metadata, **envelope(sketch_source),
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
                result["isabelle_sketch"] = normalize_sketch(body)
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
         default_output: str = DEFAULT_OUTPUT, prompt_builder=None, results_dir: str = RESULTS_DIR,
         prompt_version: str | None = None, expected_source: str = "babel-formal") -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--sketch-source", choices=MODES, default="draft")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--input")
    group.add_argument("--drafts")
    group.add_argument("--records")
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
    if args.records and args.sketch_source != "hol-light-proof" or args.drafts and args.sketch_source != "draft":
        parser.error("--records requires hol-light-proof; --drafts requires draft")
    args.input = args.input or args.records or args.drafts or default_input
    if args.sketch_source == "hol-light-proof" and not (args.records or args.input != default_input):
        parser.error("direct mode requires --records or --input")
    chosen_config = resolve_model_config(
        args.llm_config, model=args.model, reasoning_effort=args.reasoning_effort,
        max_output_tokens=args.max_output_tokens, default_effort="high", dry_run=args.dry_run)
    generate_sketches(input_path=args.input, output_path=args.output, topic=args.topic,
                      target_key=args.target_key, limit=args.limit, samples=args.samples,
                      model=args.model, reasoning_effort=args.reasoning_effort,
                      max_output_tokens=args.max_output_tokens, resume=not args.no_resume,
                      continue_on_error=not args.fail_fast, dry_run=args.dry_run, prompt_builder=prompt_builder,
        prompt_version=prompt_version, expected_source=expected_source,
        llm_config=chosen_config, default_output=default_output, results_dir=results_dir, sketch_source=args.sketch_source)


if __name__ == "__main__":
    main()
