"""Export saved V2 Drafts for the individual-theorem Isabelle DSP adapter."""

from __future__ import annotations

import argparse

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, RESULTS_DIR, key, latest_records, public_record, repo_path,
    validate_layout, write_jsonl,
)
from eval.pipeline.hol_light_to_isabelle.generate_draft import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.theory_context import input_metadata


SCHEMA_VERSION = "hol_light_to_isabelle_dsp_v1"
DEFAULT_OUTPUT = RESULTS_DIR + "/v2-dsp/babel_formal_v2_dsp_input.jsonl"


def export_record(record: dict) -> dict:
    if record.get("pipeline") not in {None, "v2-dsp"}:
        raise ValueError("export requires shared Drafts or v2-dsp input")
    result = public_record(record)
    result.update(input_metadata(record))
    result.update({
        "schema_version": SCHEMA_VERSION, "pipeline": "v2-dsp",
        "name": "/".join(str(part) for part in key(record)),
        "formal_statement": record["isabelle_statement"],
        "informal_proof": record["draft"],
        "input_error": None,
    })
    return result


def export_drafts(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT,
                  topic: str | None = None, target_key: str | None = None,
                  limit: int | None = None, continue_on_error: bool = False) -> list[dict]:
    records = latest_records(input_path, topic=topic, target_key=target_key, limit=limit)
    if repo_path(input_path) == repo_path(output_path):
        raise ValueError("saved Drafts and DSP export must be distinct")
    if not records:
        raise ValueError("no matching saved V2 Drafts")
    result = []
    for record in records:
        try:
            row = export_record(record)
        except ValueError as exc:
            if not continue_on_error:
                raise
            row = {**public_record(record), "pipeline": "v2-dsp",
                   "input_error": str(exc), "failure_category": "input_error"}
        result.append(row)
    write_jsonl(output_path, result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--input", default=DEFAULT_INPUT)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    validate_layout(args.expected_root)
    rows = export_drafts(input_path=args.input, output_path=args.output,
                         topic=args.topic, target_key=args.target_key, limit=args.limit)
    print(f"Exported {len(rows)} saved Drafts to {args.output}")


if __name__ == "__main__":
    main()
