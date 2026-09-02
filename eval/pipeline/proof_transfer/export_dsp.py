from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

from eval.pipeline.proof_transfer.aligned_data import LAB_REPO_ROOT, validate_repo_layout
from eval.pipeline.proof_transfer.generate_draft import (
    DEFAULT_DRAFTS_OUTPUT,
    read_jsonl,
    record_key,
    resolve_repo_path,
    select_records,
    write_jsonl,
)


DEFAULT_DSP_OUTPUT = "eval/results/proof_transfer/babel_formal_v1_dsp.jsonl"
DSP_EXPORT_VERSION = "babel_formal_v1_dsp_export_2026_09_02"


def _print_json(data: Any) -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    print(json.dumps(data, indent=2, ensure_ascii=False))


def _required_text(record: dict[str, Any], key: str) -> str:
    value = record.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"record {record_key(record)} is missing required text field {key!r}")
    return value.strip()


def _optional_text(record: dict[str, Any], key: str) -> str:
    value = record.get(key, "")
    if value is None:
        return ""
    if not isinstance(value, str):
        raise ValueError(f"record {record_key(record)} field {key!r} must be a string")
    return value.strip()


def dsp_problem_name(record: dict[str, Any]) -> str:
    source, theorem_id, topic, target_key = record_key(record)
    safe_source = source.replace("-", "_")
    return f"{safe_source}__{theorem_id:03d}__{topic}__{target_key}"


def lean4_statement_for_dsp(statement: str) -> str:
    """Convert a sanitized sorry theorem into the DSP+ proof-prefix form."""
    statement = statement.strip()
    rewrites = (
        (r":=\s*by\s+sorry\s*\Z", ":= by"),
        (r":=\s*by\s*\n\s*sorry\s*\Z", ":= by"),
        (r":=\s*sorry\s*\Z", ":= by"),
    )
    for pattern, replacement in rewrites:
        rewritten = re.sub(pattern, replacement, statement, flags=re.DOTALL)
        if rewritten != statement:
            return rewritten.strip()
    if statement.endswith(":= by"):
        return statement
    if statement.endswith(":="):
        return f"{statement} by"
    return statement


def compose_formal_statement(record: dict[str, Any]) -> str:
    statement = _required_text(record, "lean4_statement")
    return lean4_statement_for_dsp(statement)


def _lean_doc_comment_text(text: str) -> str:
    return text.replace("-/", "- /")


def informal_prefix(record: dict[str, Any]) -> str:
    statement = _required_text(record, "isabelle_statement")
    topic = record.get("topic", "")
    target = record.get("target_key", "")
    return (
        "/-- Isabelle source theorem translated into a DSP+ Draft. "
        f"Topic: {topic}. Target: {target}.\n\n"
        f"{_lean_doc_comment_text(statement)}\n"
        "-/"
    )


def metadata_for_dsp(record: dict[str, Any]) -> dict[str, Any]:
    metadata = record.get("metadata", {})
    if not isinstance(metadata, dict):
        metadata = {}

    return {
        "export_version": DSP_EXPORT_VERSION,
        "source": record.get("source"),
        "theorem_id": record.get("theorem_id"),
        "topic": record.get("topic"),
        "target_key": record.get("target_key"),
        "isabelle_target_name": record.get("isabelle_target_name"),
        "lean4_target_name": record.get("lean4_target_name"),
        "context_mode": record.get("context_mode"),
        "target_selection_mode": record.get("target_selection_mode"),
        "target_alignment_status": record.get("target_alignment_status"),
        "semantic_alignment_verified": record.get("semantic_alignment_verified"),
        "draft_prompt_version": record.get("draft_prompt_version"),
        "draft_prompt_sha256": record.get("draft_prompt_sha256"),
        "draft_model": record.get("draft_model"),
        "source_hashes": {
            "isabelle_proof_sha256": metadata.get("isabelle_proof_sha256"),
            "isabelle_stmt_sha256": metadata.get("isabelle_stmt_sha256"),
            "lean4_stmt_sha256": metadata.get("lean4_stmt_sha256"),
        },
    }


def latest_records_by_key(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    latest: dict[tuple[str, int, str, str], dict[str, Any]] = {}
    for record in records:
        latest[record_key(record)] = record
    return list(latest.values())


def export_dsp_record(
    record: dict[str, Any],
    *,
    allow_empty_draft: bool = False,
    include_metadata: bool = False,
) -> dict[str, Any]:
    draft = record.get("draft", "")
    if not isinstance(draft, str):
        raise ValueError(f"record {record_key(record)} has non-string draft")
    draft = draft.strip()

    if record.get("draft_error") and not allow_empty_draft:
        raise ValueError(f"record {record_key(record)} has draft_error: {record['draft_error']}")
    if not draft and not allow_empty_draft:
        raise ValueError(f"record {record_key(record)} has no draft")

    lean4_statement = compose_formal_statement(record)
    isabelle_statement = _required_text(record, "isabelle_statement")

    dsp_record = {
        "name": dsp_problem_name(record),
        "split": "test",
        "informal_prefix": informal_prefix(record),
        "formal_statement": lean4_statement,
        "goal": str(record.get("lean4_target_name") or record.get("target_key")),
        "header": _optional_text(record, "lean4_header"),
        "informal_statement": isabelle_statement,
        "informal_proof": draft,
    }
    if include_metadata:
        dsp_record["metadata"] = metadata_for_dsp(record)
    return dsp_record


def export_dsp(
    *,
    input_path: str | Path = DEFAULT_DRAFTS_OUTPUT,
    output_path: str | Path = DEFAULT_DSP_OUTPUT,
    topic: str | None = None,
    target_key: str | None = None,
    limit: int | None = None,
    allow_empty_draft: bool = False,
    include_metadata: bool = False,
) -> int:
    records = select_records(
        latest_records_by_key(read_jsonl(input_path)),
        topic=topic,
        target_key=target_key,
        limit=limit,
    )
    if not records:
        raise SystemExit("No draft records matched the requested filters.")

    dsp_records = [
        export_dsp_record(
            record,
            allow_empty_draft=allow_empty_draft,
            include_metadata=include_metadata,
        )
        for record in records
    ]
    write_jsonl(output_path, dsp_records)
    print(f"Wrote {len(dsp_records)} DSP+ record(s) to {resolve_repo_path(output_path)}")
    return len(dsp_records)


def main() -> None:
    parser = argparse.ArgumentParser(description="Export Draft records to DSP+ JSONL.")
    parser.add_argument("--expected-root", help=f"Expected repo root, e.g. {LAB_REPO_ROOT}.")
    parser.add_argument("--check-layout", action="store_true", help="Validate repo/input paths and exit.")
    parser.add_argument("--input", default=DEFAULT_DRAFTS_OUTPUT, help="Draft records JSONL.")
    parser.add_argument("--output", default=DEFAULT_DSP_OUTPUT, help="DSP+ JSONL output.")
    parser.add_argument("--topic", help="Optional Babel Formal topic filter.")
    parser.add_argument("--target-key", help="Optional local target theorem filter.")
    parser.add_argument("--limit", type=int, help="Optional maximum number of selected records.")
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

    export_dsp(
        input_path=args.input,
        output_path=args.output,
        topic=args.topic,
        target_key=args.target_key,
        limit=args.limit,
        allow_empty_draft=args.allow_empty_draft,
        include_metadata=args.include_metadata,
    )


if __name__ == "__main__":
    main()
