"""Extract most-match targets with bounded references and a full verifier context."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from .aligned_data import load_topic, topics
from .common import DATASET_ROOT, RESULTS_DIR, SOURCE, repo_path, sha256, validate_layout, write_jsonl
from .context import build_contexts, SOURCE_CONTEXT_CHARS, ISABELLE_CONTEXT_CHARS
from .inventory import inventory_topic
from ..babel_formal_pipeline.sanitize_isabelle import sanitize_target
from ..babel_formal_pipeline.theory_context import validate_context

DEFAULT_OUTPUT = RESULTS_DIR + "/records.jsonl"


def build_record(group, pair, *, source_chars=SOURCE_CONTEXT_CHARS, isabelle_chars=ISABELLE_CONTEXT_CHARS):
    source = next(s for s in group["sources"] if Path(s.path).name == pair["source_file"])
    target = next(d for d in source.proofs if d.name == pair["hol_light_name"])
    isa = sanitize_target(group["template"], pair["isabelle_name"], topic=group["topic"])
    hol_reference, isa_reference, retrieval = build_contexts(source, target, isa,
        source_chars=source_chars, isabelle_chars=isabelle_chars,
        import_root=Path(group["target_path"]).parents[3] / "afp" / "stmts" / "isabelle")
    record = {
        "experiment_version": "v2", "experiment_setting": "oracle_isabelle_statement",
        "source": SOURCE, "theorem_id": group["theorem_id"], "topic": group["topic"], "tier": "most-match",
        "target_key": pair["isabelle_name"], "source_prover": "hol-light", "target_prover": "isabelle",
        "hol_light_target_name": target.name, "isabelle_target_name": isa.name,
        "hol_light_statement": target.statement, "hol_light_proof": target.proof,
        "hol_light_reference_context": hol_reference, "isabelle_prompt_context": isa_reference,
        "isabelle_statement": isa.statement, "isabelle_proof_prefix": isa.proof_prefix,
        "isabelle_context_before_target": isa.context_before_target, "isabelle_theory_template": isa.theory_template,
        "isabelle_target_proof_span": list(isa.proof_span), "context_mode": "bounded_relevant_masked_references",
        "target_selection_mode": pair["status"], "target_alignment_status": pair["status"],
        "semantic_alignment_verified": False,
        "metadata": {"input_source": "hol_dataset/most-match named file groups",
            "hol_light_proof_path": str(Path(source.path).relative_to(repo_path('.'))),
            "hol_light_stmt_path": str(Path(source.statement_path).relative_to(repo_path('.'))),
            "isabelle_stmt_path": str(Path(group["target_path"]).relative_to(repo_path('.'))),
            "hol_light_proof_sha256": sha256(source.proof_text),
            "raw_hol_light_stmt_sha256": sha256(source.statement_text),
            "hol_light_stmt_sha256": sha256(hol_reference),
            "raw_isabelle_stmt_sha256": sha256(group["raw_template"]),
            "isabelle_stmt_sha256": sha256(isa.theory_template),
            "hol_light_declaration_span": list(target.declaration_span), "hol_light_line_start": target.line_start,
            "isabelle_line_start": isa.line_start, "isabelle_prior_theorem_count": isa.prior_theorem_count,
            "prompt_context": retrieval},
    }
    validate_context(record)
    return record


def extract_records(*, dataset_root=DATASET_ROOT, topic=None, target_key=None,
                    source_chars=SOURCE_CONTEXT_CHARS, isabelle_chars=ISABELLE_CONTEXT_CHARS, report=None):
    records, rows = [], []
    for name in topics(topic):
        group = load_topic(name, dataset_root)
        coverage = inventory_topic(group)
        coverage.update(extracted_count=0, issues=[])
        for pair in coverage["candidate_pairs"]:
            if target_key is not None and pair["isabelle_name"] != target_key:
                continue
            try:
                records.append(build_record(group, pair, source_chars=source_chars, isabelle_chars=isabelle_chars))
                coverage["extracted_count"] += 1
            except (ValueError, KeyError) as exc:
                coverage["issues"].append({"target_key": pair["isabelle_name"], "error": f"{type(exc).__name__}: {exc}"})
        rows.append(coverage)
    if report is not None:
        report.update(source=SOURCE, candidate_count=sum(r["candidate_count"] for r in rows),
            record_count=len(records), topics=rows, semantic_alignment_verified=False,
            zero_match_topics=[r["topic"] for r in rows if not r["candidate_pairs"]])
    return records


def add_extraction_arguments(parser):
    parser.add_argument("--dataset-root", default=DATASET_ROOT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--source-context-chars", type=int, default=SOURCE_CONTEXT_CHARS)
    parser.add_argument("--isabelle-context-chars", type=int, default=ISABELLE_CONTEXT_CHARS)


def extraction_options(args):
    return dict(dataset_root=args.dataset_root, topic=args.topic, target_key=args.target_key,
                source_chars=args.source_context_chars, isabelle_chars=args.isabelle_context_chars)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    add_extraction_arguments(parser)
    parser.add_argument("--all-topics", action="store_true")
    parser.add_argument("--all-targets", action="store_true")
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--report")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.all_topics and args.topic or args.all_targets and args.target_key:
        parser.error("all selectors cannot be combined with an individual selector")
    destination = repo_path(args.output)
    coverage_path = repo_path(args.report or (args.output + ".coverage.json"))
    if destination == coverage_path:
        parser.error("record and coverage paths must be distinct")
    report = {}
    records = extract_records(**extraction_options(args), report=report)
    coverage_path.parent.mkdir(parents=True, exist_ok=True)
    coverage_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    write_jsonl(destination, records)
    print(f"Wrote {len(records)} records; {report['candidate_count']} candidate mappings. Coverage: {coverage_path}")
    if not records or any(row["issues"] for row in report["topics"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
