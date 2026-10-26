"""Run the existing ITPEval baseline from shared, already generated Drafts."""

from __future__ import annotations

import argparse
import json

from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.common import (
    LAB_REPO_ROOT, SOURCE, key, latest_records, repo_path, require_source, summarize, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_itpeval.generate_sketch import (
    DEFAULT_OUTPUT as DEFAULT_SKETCHES, generate_sketches,
)
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_itpeval.verify_isabelle import (
    DEFAULT_OUTPUT, preflight, verify_sketches,
)
from eval.pipeline.proof_transfer.llm import DEFAULT_DRAFT_MODEL


def main() -> None:
    parser = argparse.ArgumentParser(description="v2-itpeval: saved Drafts to Isabelle2024 proofs.")
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--drafts", required=True)
    parser.add_argument("--sketch-output", default=DEFAULT_SKETCHES)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--sketch-model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--sketch-reasoning-effort", default="high")
    parser.add_argument("--max-output-tokens", type=int, default=16000)
    parser.add_argument("--timeout-s", type=int, default=1200)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--skip-sketch", action="store_true")
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    filters = dict(topic=args.topic, target_key=args.target_key, limit=args.limit)
    records = latest_records(args.drafts, **filters)
    require_source(records, SOURCE)
    if not records:
        parser.error("no matching saved Drafts")
    if args.samples < 1:
        parser.error("--samples must be positive")
    paths = [args.drafts, args.sketch_output, args.output]
    if len(set(repo_path(path) for path in paths)) != len(paths):
        parser.error("saved Draft, Sketch, and verified output paths must be distinct")
    blocked = {}
    if not args.dry_run and not args.skip_sketch:
        # The full masked-template baseline is shared by all targets in a topic.
        seen = {}
        for record in records:
            if record.get("draft_error") or not record.get("draft"):
                continue
            template = record["isabelle_theory_template"]
            if template not in seen:
                check = preflight(record, timeout_s=args.timeout_s)
                if not check["baseline_ok"] or not check["negative_control_failed"]:
                    if args.fail_fast:
                        raise RuntimeError("Isabelle preflight failed: " + json.dumps(check))
                    seen[template] = json.dumps(check)
                else:
                    seen[template] = None
            if seen[template]:
                blocked[key(record)] = seen[template]
    if not args.skip_sketch or args.dry_run:
        generate_sketches(
            input_path=args.drafts, output_path=args.sketch_output, **filters,
            samples=args.samples, model=args.sketch_model,
            reasoning_effort=args.sketch_reasoning_effort,
            max_output_tokens=args.max_output_tokens, resume=not args.no_resume,
            continue_on_error=not args.fail_fast, dry_run=args.dry_run,
            blocked_targets=blocked)
    elif not repo_path(args.sketch_output).is_file():
        parser.error("--skip-sketch requires an existing Sketch JSONL")
    if not args.dry_run and not args.skip_verify:
        results = verify_sketches(
            input_path=args.sketch_output, output_path=args.output, **filters,
            timeout_s=args.timeout_s, resume=not args.no_resume,
            expected=records, expected_samples=args.samples)
        print(json.dumps(summarize(results, expected=records,
                                   expected_samples=args.samples), indent=2))


if __name__ == "__main__":
    main()
