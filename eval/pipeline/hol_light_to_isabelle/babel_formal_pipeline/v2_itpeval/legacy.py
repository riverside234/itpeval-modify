from __future__ import annotations

import argparse
import json

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    LAB_REPO_ROOT, RESULTS_DIR, latest_records, repo_path, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light import DEFAULT_OUTPUT as DEFAULT_RECORDS
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.generate_draft import (
    DEFAULT_OUTPUT as DEFAULT_DRAFTS, generate_drafts,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.generate_sketch import generate_sketches
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.verify_isabelle import summarize, verify_sketches
from eval.pipeline.inference.config import output_path_for_profile
from eval.pipeline.proof_transfer.llm import DEFAULT_DRAFT_MODEL, resolve_model_config


DEFAULT_SKETCHES = RESULTS_DIR + "/babel_formal_v2_sketches.jsonl"
DEFAULT_VERIFIED = RESULTS_DIR + "/babel_formal_v2_verified.jsonl"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run Babel Formal V2: HOL Light proof to Isabelle Draft, Sketch, verification.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--records", default=DEFAULT_RECORDS)
    parser.add_argument("--draft-output")
    parser.add_argument("--sketch-output")
    parser.add_argument("--output")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--draft-llm-config")
    parser.add_argument("--draft-model", default=None)
    parser.add_argument("--draft-reasoning-effort", default=None)
    parser.add_argument("--sketch-llm-config")
    parser.add_argument("--sketch-model", default=None)
    parser.add_argument("--sketch-reasoning-effort", default=None)
    parser.add_argument("--max-output-tokens", type=int, default=None)
    parser.add_argument("--timeout-s", type=int, default=1200)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--skip-draft", action="store_true")
    parser.add_argument("--skip-sketch", action="store_true")
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    draft_config = resolve_model_config(
        args.draft_llm_config, model=args.draft_model, reasoning_effort=args.draft_reasoning_effort,
        max_output_tokens=args.max_output_tokens, default_effort="medium", dry_run=args.dry_run)
    sketch_config = resolve_model_config(
        args.sketch_llm_config, model=args.sketch_model, reasoning_effort=args.sketch_reasoning_effort,
        max_output_tokens=args.max_output_tokens, default_effort="high", dry_run=args.dry_run)
    args.draft_output = output_path_for_profile(args.draft_output, DEFAULT_DRAFTS, draft_config)
    if not args.skip_draft or args.dry_run:
        generate_drafts(
            input_path=args.records, output_path=args.draft_output,
            topic=args.topic, target_key=args.target_key, limit=args.limit,
            model=args.draft_model, reasoning_effort=args.draft_reasoning_effort,
            max_output_tokens=args.max_output_tokens,
            resume=not args.no_resume, continue_on_error=not args.fail_fast,
            dry_run=args.dry_run, llm_config=draft_config)
    elif not repo_path(args.draft_output).exists():
        parser.error("--skip-draft requires an existing Draft JSONL")
    if args.dry_run:
        return
    saved_drafts = latest_records(args.draft_output,topic=args.topic,target_key=args.target_key,limit=args.limit)
    args.sketch_output = output_path_for_profile(args.sketch_output, DEFAULT_SKETCHES, sketch_config, draft_records=saved_drafts)
    args.output = output_path_for_profile(args.output, DEFAULT_VERIFIED, sketch_config, draft_records=saved_drafts)
    if not args.skip_sketch:
        generate_sketches(
            input_path=args.draft_output, output_path=args.sketch_output,
            topic=args.topic, target_key=args.target_key, limit=args.limit,
            samples=args.samples, model=args.sketch_model,
            reasoning_effort=args.sketch_reasoning_effort,
            max_output_tokens=args.max_output_tokens,
            resume=not args.no_resume, continue_on_error=not args.fail_fast, llm_config=sketch_config)
    elif not repo_path(args.sketch_output).exists():
        parser.error("--skip-sketch requires an existing Sketch JSONL")
    if not args.skip_verify:
        results = verify_sketches(
            input_path=args.sketch_output, output_path=args.output,
            topic=args.topic, target_key=args.target_key,
            limit=args.limit, timeout_s=args.timeout_s,
            resume=not args.no_resume)
        print(f"Verified {sum(bool(r['verified']) for r in results)}/{len(results)} samples")
        print(json.dumps(summarize(results), indent=2))


if __name__ == "__main__":
    main()
