from __future__ import annotations

import argparse
import json

from eval.pipeline.hol_light_to_isabelle.common import LAB_REPO_ROOT, repo_path, validate_layout
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import DEFAULT_OUTPUT as DEFAULT_RECORDS
from eval.pipeline.hol_light_to_isabelle.generate_draft import (
    DEFAULT_OUTPUT as DEFAULT_DRAFTS, generate_drafts,
)
from eval.pipeline.hol_light_to_isabelle.generate_sketch import (
    DEFAULT_OUTPUT as DEFAULT_SKETCHES, generate_sketches,
)
from eval.pipeline.hol_light_to_isabelle.verify_isabelle import (
    DEFAULT_OUTPUT as DEFAULT_VERIFIED, summarize, verify_sketches,
)
from eval.pipeline.proof_transfer.llm import DEFAULT_DRAFT_MODEL


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run Babel Formal V2: HOL Light proof to Isabelle Draft, Sketch, verification.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--records", default=DEFAULT_RECORDS)
    parser.add_argument("--draft-output", default=DEFAULT_DRAFTS)
    parser.add_argument("--sketch-output", default=DEFAULT_SKETCHES)
    parser.add_argument("--output", default=DEFAULT_VERIFIED)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--draft-model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--draft-reasoning-effort", default="medium")
    parser.add_argument("--sketch-model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--sketch-reasoning-effort", default="high")
    parser.add_argument("--max-output-tokens", type=int, default=16000)
    parser.add_argument("--timeout-s", type=int, default=1200)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--skip-draft", action="store_true")
    parser.add_argument("--skip-sketch", action="store_true")
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if not args.skip_draft or args.dry_run:
        generate_drafts(
            input_path=args.records, output_path=args.draft_output,
            topic=args.topic, target_key=args.target_key, limit=args.limit,
            model=args.draft_model, reasoning_effort=args.draft_reasoning_effort,
            max_output_tokens=args.max_output_tokens,
            resume=not args.no_resume, continue_on_error=not args.fail_fast,
            dry_run=args.dry_run)
    elif not repo_path(args.draft_output).exists():
        parser.error("--skip-draft requires an existing Draft JSONL")
    if args.dry_run:
        return
    if not args.skip_sketch:
        generate_sketches(
            input_path=args.draft_output, output_path=args.sketch_output,
            topic=args.topic, target_key=args.target_key, limit=args.limit,
            samples=args.samples, model=args.sketch_model,
            reasoning_effort=args.sketch_reasoning_effort,
            max_output_tokens=args.max_output_tokens,
            resume=not args.no_resume, continue_on_error=not args.fail_fast)
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
