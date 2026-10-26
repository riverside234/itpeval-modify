"""Extract per-declaration HOL Light to Isabelle records with a coverage report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light import build_record as _build_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context
from .aligned_data import list_topics, load_topic, raw_inputs
from .common import LAB_REPO_ROOT, RESULTS_DIR, SOURCE, repo_path, sha256, validate_layout, write_jsonl
from .hol_syntax import inventory_hol_declarations
from .inventory import inventory_topic
from .manifest import MANIFEST, Target, targets_for_topic

DEFAULT_OUTPUT = RESULTS_DIR + "/hundred_theorems_v2_records.jsonl"


def build_record(topic, target: Target, *, proofs=None, masked=None) -> dict:
    proofs = proofs if proofs is not None else inventory_hol_declarations(topic.hol_light_proof_content,masked=False)
    masked = masked if masked is not None else inventory_hol_declarations(topic.hol_light_stmt_content,masked=True)
    record = _build_record(topic,target,proofs=proofs,masked=masked)
    _,source,target_input = raw_inputs(topic.theorem_id)
    record["metadata"].update({
        "raw_hol_light_stmt_sha256":sha256(source["content"]),
        "raw_isabelle_stmt_sha256":sha256(target_input["content"]),
        "proof_masking_version":"hundred_theorems_repair_p1",
        "input_source":"eval/data/proofs.json:hol-light + eval/data/stmts.json:hol-light,isabelle",
    })
    validate_context(record)
    return record


def extract_records(*, topic: str | None = None, theorem_id: int | None = None,
                    target_key: str | None = None, verified_only: bool = False,
                    manifest_path: str | Path = MANIFEST, continue_on_error: bool = True,
                    report: dict | None = None) -> list[dict]:
    topics = [(tid,title) for tid,title in list_topics()
              if (topic is None or title == topic) and (theorem_id is None or tid == theorem_id)]
    if not topics:
        raise ValueError("no matching Hundred Theorems file group")
    result,coverage = [],[]
    for tid,title in topics:
        row = {"theorem_id":tid,"topic":title,"candidate_count":0,"selected_count":0,
               "extracted_count":0,"issues":[]}
        try:
            aligned = load_topic(tid)
            inventory = inventory_topic(aligned)
            row["inventory"] = inventory
            row["candidate_count"] = len(inventory["candidate_pairs"])
            targets = targets_for_topic(title,inventory["candidate_pairs"],verified_only=verified_only,
                                        manifest_path=manifest_path)
            if target_key is not None:
                targets = [target for target in targets if target.target_key == target_key]
            row["selected_count"] = len(targets)
            proofs = inventory_hol_declarations(aligned.hol_light_proof_content,masked=False)
            masked = inventory_hol_declarations(aligned.hol_light_stmt_content,masked=True)
            for target in targets:
                try:
                    result.append(build_record(aligned,target,proofs=proofs,masked=masked))
                    row["extracted_count"] += 1
                except (ValueError,KeyError) as exc:
                    if not continue_on_error:
                        raise
                    row["issues"].append({"target_key":target.target_key,"error":f"{type(exc).__name__}: {exc}"})
        except (ValueError,KeyError) as exc:
            if not continue_on_error:
                raise
            row["issues"].append({"error":f"{type(exc).__name__}: {exc}"})
        coverage.append(row)
    if report is not None:
        report.update(source=SOURCE,selected_file_groups=len(topics),record_count=len(result),
                      candidate_count=sum(row["candidate_count"] for row in coverage),
                      semantic_alignment_verified_count=sum(bool(row["semantic_alignment_verified"]) for row in result),
                      file_groups=coverage)
    if not result:
        raise ValueError("no extractable Hundred Theorems targets; inspect the coverage report and manifest")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root",help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--topic")
    parser.add_argument("--id",type=int,help="Aligned theorem_id from inventory, not the filename's 001-100 number.")
    parser.add_argument("--all-topics",action="store_true")
    parser.add_argument("--target-key")
    parser.add_argument("--all-targets",action="store_true")
    parser.add_argument("--verified-only",action="store_true")
    parser.add_argument("--manifest",default=str(MANIFEST))
    parser.add_argument("--fail-fast",action="store_true")
    parser.add_argument("--output",default=DEFAULT_OUTPUT)
    parser.add_argument("--report",help="Defaults to <output>.coverage.json.")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.all_topics == bool(args.topic or args.id is not None):
        parser.error("choose --all-topics or --topic/--id")
    if args.all_targets == bool(args.target_key):
        parser.error("choose --all-targets or --target-key")
    report = {}
    records = None
    try:
        records = extract_records(topic=args.topic,theorem_id=args.id,target_key=args.target_key,
                                  verified_only=args.verified_only,manifest_path=args.manifest,
                                  continue_on_error=not args.fail_fast,report=report)
    finally:
        path = repo_path(args.report or (args.output+".coverage.json"))
        if path == repo_path(args.output):
            raise ValueError("records and coverage report paths must be distinct")
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    path = write_jsonl(args.output,records)
    print(f"Wrote {len(records)} Hundred Theorems V2 records to {path}")
    print(f"Coverage report: {repo_path(args.report or (args.output+'.coverage.json'))}")


if __name__ == "__main__":
    main()
