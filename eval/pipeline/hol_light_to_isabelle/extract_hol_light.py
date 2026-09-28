from __future__ import annotations

import argparse
from eval.pipeline.hol_light_to_isabelle.aligned_data import iter_topics
from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, RESULTS_DIR, validate_layout, write_jsonl,
)
from eval.pipeline.hol_light_to_isabelle.inventory import (
    inventory_hol_declarations, inventory_topic,
)
from eval.pipeline.hol_light_to_isabelle.manifest import Target, targets_for_topic
from eval.pipeline.hol_light_to_isabelle.sanitize_isabelle import sanitize_target


DEFAULT_OUTPUT = RESULTS_DIR + "/babel_formal_v2_exact_name_records.jsonl"


def _unique_by_name(declarations, name: str, kind: str):
    matches = [declaration for declaration in declarations if declaration.name == name]
    if len(matches) != 1:
        raise ValueError(f"expected one {kind} {name!r}, found {len(matches)}")
    return matches[0]


def build_record(topic, target: Target, *, proofs=None, masked=None) -> dict:
    if target.topic != topic.topic:
        raise ValueError("target/topic mismatch")
    proofs = proofs if proofs is not None else inventory_hol_declarations(
        topic.hol_light_proof_content, masked=False)
    masked = masked if masked is not None else inventory_hol_declarations(
        topic.hol_light_stmt_content, masked=True)
    source = _unique_by_name(proofs, target.hol_light_target_name, "HOL proof")
    source_masked = _unique_by_name(masked, target.hol_light_target_name, "masked HOL statement")
    if source.proof is None or not source.proof.strip():
        raise ValueError(f"missing HOL proof for {source.name}")
    if source_masked.proof is not None:
        raise ValueError(f"HOL reference contains proof for {source.name}")
    if " ".join(source.statement.split()) != " ".join(source_masked.statement.split()):
        raise ValueError(f"HOL statement mismatch for {source.name}")
    isa = sanitize_target(topic.isabelle_stmt_content, target.isabelle_target_name,
                          topic=topic.topic)
    return {
        "experiment_version": "v2",
        "experiment_setting": "oracle_isabelle_statement",
        "source": "babel-formal", "theorem_id": topic.theorem_id,
        "topic": topic.topic, "tier": topic.tier,
        "target_key": target.target_key,
        "source_prover": "hol-light", "target_prover": "isabelle",
        "hol_light_target_name": target.hol_light_target_name,
        "isabelle_target_name": target.isabelle_target_name,
        "hol_light_statement": source.statement,
        "hol_light_proof": source.proof,
        "hol_light_reference_context": topic.hol_light_stmt_content,
        "isabelle_statement": isa.statement,
        "isabelle_proof_prefix": isa.proof_prefix,
        "isabelle_context_before_target": isa.context_before_target,
        "isabelle_theory_template": isa.theory_template,
        "isabelle_target_proof_span": list(isa.proof_span),
        "context_mode": "proof_masked_source_and_target_context",
        "target_selection_mode": "manifest_verified" if target.status == "verified" else target.status,
        "target_alignment_status": target.status,
        "semantic_alignment_verified": target.semantic_alignment_verified,
        "metadata": {
            "hol_light_proof_sha256": topic.hol_light_proof_sha256,
            "hol_light_stmt_sha256": topic.hol_light_stmt_sha256,
            "isabelle_stmt_sha256": topic.isabelle_stmt_sha256,
            "hol_light_declaration_span": list(source.declaration_span),
            "hol_light_line_start": source.line_start,
            "isabelle_line_start": isa.line_start,
            "isabelle_prior_theorem_count": isa.prior_theorem_count,
        },
    }


def extract_records(*, topic: str | None = None, theorem_id: int | None = None,
                    target_key: str | None = None, verified_only: bool = False) -> list[dict]:
    records = []
    topics = list(iter_topics(topic=topic, theorem_id=theorem_id))
    if not topics:
        raise ValueError("no matching Babel Formal topic")
    for aligned in topics:
        proof = inventory_hol_declarations(aligned.hol_light_proof_content, masked=False)
        masked = inventory_hol_declarations(aligned.hol_light_stmt_content, masked=True)
        pairs = inventory_topic(aligned)["candidate_pairs"]
        targets = targets_for_topic(aligned.topic, pairs, verified_only=verified_only)
        if target_key is not None:
            targets = [target for target in targets if target.target_key == target_key]
        records.extend(build_record(aligned, target, proofs=proof, masked=masked)
                       for target in targets)
    if not records:
        raise ValueError("no matching Babel Formal theorem targets")
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract V2 HOL Light to Isabelle records.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--topic")
    parser.add_argument("--id", type=int)
    parser.add_argument("--all-topics", action="store_true")
    parser.add_argument("--target-key")
    parser.add_argument("--all-targets", action="store_true")
    parser.add_argument("--verified-only", action="store_true")
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.all_topics == bool(args.topic or args.id is not None):
        parser.error("choose --all-topics or --topic/--id")
    if args.all_targets == bool(args.target_key):
        parser.error("choose --all-targets or --target-key")
    records = extract_records(topic=args.topic, theorem_id=args.id,
                              target_key=args.target_key, verified_only=args.verified_only)
    path = write_jsonl(args.output, records)
    print(f"Wrote {len(records)} V2 records to {path}")


if __name__ == "__main__":
    main()
