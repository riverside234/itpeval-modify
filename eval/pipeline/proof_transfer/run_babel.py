from __future__ import annotations

import argparse
import json
import sys

from eval.pipeline.proof_transfer.aligned_data import LAB_REPO_ROOT, validate_repo_layout
from eval.pipeline.proof_transfer.export_dsp import DEFAULT_DSP_OUTPUT, export_dsp
from eval.pipeline.proof_transfer.generate_draft import (
    DEFAULT_DRAFTS_OUTPUT,
    DEFAULT_RECORDS_INPUT,
    generate_drafts,
)
from eval.pipeline.proof_transfer.llm import DEFAULT_DRAFT_MODEL, DEFAULT_REASONING_EFFORT


def _print_json(data: object) -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    print(json.dumps(data, indent=2, ensure_ascii=False))


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run Babel Formal V1: parsed records -> Drafts -> DSP+ JSONL."
    )
    parser.add_argument("--expected-root", help=f"Expected repo root, e.g. {LAB_REPO_ROOT}.")
    parser.add_argument("--check-layout", action="store_true", help="Validate repo/input paths and exit.")
    parser.add_argument(
        "--records",
        default=DEFAULT_RECORDS_INPUT,
        help="Parsed exact-name Babel Formal V1 records JSONL.",
    )
    parser.add_argument(
        "--draft-output",
        default=DEFAULT_DRAFTS_OUTPUT,
        help="Intermediate Draft records JSONL.",
    )
    parser.add_argument("--output", default=DEFAULT_DSP_OUTPUT, help="Final DSP+ JSONL output.")
    parser.add_argument("--topic", help="Optional Babel Formal topic filter.")
    parser.add_argument("--target-key", help="Optional local target theorem filter.")
    parser.add_argument("--limit", type=int, help="Optional maximum number of selected records.")
    parser.add_argument("--model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--reasoning-effort", default=DEFAULT_REASONING_EFFORT)
    parser.add_argument("--max-output-tokens", type=int, default=16000)
    parser.add_argument("--resume", dest="resume", action="store_true", default=True)
    parser.add_argument("--no-resume", dest="resume", action="store_false")
    parser.add_argument("--continue-on-error", dest="continue_on_error", action="store_true", default=True)
    parser.add_argument("--fail-fast", dest="continue_on_error", action="store_false")
    parser.add_argument("--dry-run", action="store_true", help="Print the first Draft prompt and do not call the API.")
    parser.add_argument(
        "--skip-draft",
        action="store_true",
        help="Export an existing Draft JSONL without making API calls.",
    )
    parser.add_argument(
        "--allow-empty-draft",
        action="store_true",
        help="Export records with empty drafts for smoke tests only.",
    )
    parser.add_argument(
        "--include-metadata",
        action="store_true",
        help="Include ITPEval provenance metadata as an extra DSP+ JSON field.",
    )
    args = parser.parse_args()

    if args.expected_root or args.check_layout:
        layout = validate_repo_layout(args.expected_root)
        if args.check_layout:
            _print_json(layout)
            return

    if not args.skip_draft:
        generate_drafts(
            input_path=args.records,
            output_path=args.draft_output,
            topic=args.topic,
            target_key=args.target_key,
            limit=args.limit,
            model=args.model,
            reasoning_effort=args.reasoning_effort,
            max_output_tokens=args.max_output_tokens,
            resume=args.resume,
            continue_on_error=args.continue_on_error,
            dry_run=args.dry_run,
        )

    if args.dry_run:
        return

    export_dsp(
        input_path=args.draft_output,
        output_path=args.output,
        topic=args.topic,
        target_key=args.target_key,
        limit=args.limit,
        allow_empty_draft=args.allow_empty_draft,
        include_metadata=args.include_metadata,
    )


if __name__ == "__main__":
    main()
