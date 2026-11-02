"""Normalize saved Drafts or extracted HOL Light proofs for native Isabelle Sketch."""
from __future__ import annotations
import argparse
from ..common import LAB_REPO_ROOT, RESULTS_DIR, key, repo_path, require_source, validate_layout, write_jsonl, read_jsonl
from ..generate_draft import DEFAULT_OUTPUT as DEFAULT_INPUT
from .input_contract import (SCHEMA_VERSION, MODES, clean_record, envelope, input_metadata,
                             load_inputs, output_path as native_output_path, validate_artifacts)

DEFAULT_OUTPUT = native_output_path(None, results_dir=RESULTS_DIR, filename="inputs.jsonl", mode="draft")


def export_record(record: dict, *, expected_source: str = "babel-formal",
                  sketch_source: str = "draft") -> dict:
    require_source([record], expected_source)
    if record.get("pipeline") not in {None, "v2-dsp"}:
        raise ValueError("export requires extracted records or shared saved Drafts")
    if record.get("pipeline") == "v2-dsp":
        validate_artifacts([record], sketch_source)
    result = clean_record(record, sketch_source)
    result.update(input_metadata(result, sketch_source))
    result.update({**envelope(sketch_source), "name": "/".join(str(x) for x in key(record)),
                   "formal_statement": record["isabelle_statement"], "input_error": None})
    if sketch_source == "draft":
        result["informal_proof"] = record["draft"]
    return result


def export_inputs(*, input_path: str, output_path: str | None = None, sketch_source="draft",
                  topic=None, target_key=None, limit=None, continue_on_error=False,
                  expected_source="babel-formal", results_dir=RESULTS_DIR) -> list[dict]:
    records = load_inputs(input_path, mode=sketch_source, topic=topic, target_key=target_key, limit=limit)
    require_source(records, expected_source)
    destination = native_output_path(output_path, results_dir=results_dir,
                                           filename="inputs.jsonl", mode=sketch_source)
    if repo_path(input_path) == repo_path(destination):
        raise ValueError("source input and DSP export must be distinct")
    if not records:
        raise ValueError("no matching Sketch inputs")
    if repo_path(destination).is_file():
        validate_artifacts(read_jsonl(destination), sketch_source)
    rows = []
    for record in records:
        try:
            row = export_record(record, expected_source=expected_source, sketch_source=sketch_source)
        except ValueError as exc:
            if not continue_on_error:
                raise
            row = {**clean_record(record, sketch_source), **envelope(sketch_source),
                   "input_error": str(exc), "failure_category": "input_error"}
        rows.append(row)
    write_jsonl(destination, rows)
    return rows


def export_drafts(*, input_path=DEFAULT_INPUT, output_path=DEFAULT_OUTPUT, **options) -> list[dict]:
    """Compatibility entry point for the saved-Draft experiment."""
    if options.pop("sketch_source", "draft") != "draft":
        raise ValueError("export_drafts is Draft-only; use export_inputs for direct mode")
    return export_inputs(input_path=input_path, output_path=output_path, sketch_source="draft", **options)


def main(*, default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
         expected_source="babel-formal", results_dir=RESULTS_DIR) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--sketch-source", choices=MODES, default="draft")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--drafts")
    group.add_argument("--records")
    group.add_argument("--input", help="Compatibility input path; interpreted using --sketch-source")
    parser.add_argument("--output")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.records and args.sketch_source != "hol-light-proof" or args.drafts and args.sketch_source != "draft":
        parser.error("--records requires hol-light-proof; --drafts requires draft")
    source = args.input or args.records or args.drafts
    if source is None:
        if args.sketch_source != "draft":
            parser.error("direct mode requires --records")
        source = default_input
    rows = export_inputs(input_path=source, output_path=args.output, sketch_source=args.sketch_source,
                         topic=args.topic, target_key=args.target_key, limit=args.limit,
                         expected_source=expected_source, results_dir=results_dir)
    print(f"Exported {len(rows)} {args.sketch_source} inputs")


if __name__ == "__main__":
    main()
