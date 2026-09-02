from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable

from eval.pipeline.proof_transfer.aligned_data import (
    BABEL_FORMAL,
    LAB_REPO_ROOT,
    AlignedBabelTopic,
    iter_babel_topics,
    load_babel_topic,
    load_babel_topic_by_name,
    resolved_repo_root,
    validate_repo_layout,
)
from eval.pipeline.proof_transfer.inventory import (
    Declaration,
    inventory_isabelle_declarations,
)
from eval.pipeline.proof_transfer.manifest import (
    BabelTarget,
    get_babel_target,
    iter_babel_targets,
)
from eval.pipeline.proof_transfer.sanitize_lean import sanitize_lean_target


CONTEXT_MODE = "proof_masked_stmt_file"


@dataclass(frozen=True)
class IsabelleTarget:
    name: str
    kind: str
    statement: str
    proof: str
    full_block: str
    declaration_span: tuple[int, int]
    statement_span: tuple[int, int]
    proof_span: tuple[int, int]
    line_start: int
    line_end: int

    def to_dict(self, *, include_full_block: bool = False) -> dict[str, Any]:
        data = asdict(self)
        if not include_full_block:
            data.pop("full_block", None)
        return data


def _find_declaration(
    declarations: Iterable[Declaration],
    name: str,
    *,
    prover: str,
) -> Declaration:
    declarations = list(declarations)
    for declaration in declarations:
        if declaration.name == name:
            return declaration

    for declaration in declarations:
        if declaration.name.lower() == name.lower():
            return declaration

    available = ", ".join(declaration.name for declaration in declarations)
    raise ValueError(f"could not find {prover} declaration {name!r}; available: {available}")


def _validate_verified_target(target: BabelTarget) -> None:
    if target.status != "verified" or not target.semantic_alignment_verified:
        raise ValueError(
            f"target {target.target_key!r} is not verified "
            f"(status={target.status!r}, "
            f"semantic_alignment_verified={target.semantic_alignment_verified!r})"
        )


def extract_isabelle_target(
    topic: AlignedBabelTopic,
    target: BabelTarget,
) -> IsabelleTarget:
    if target.topic != topic.topic:
        raise ValueError(f"target topic {target.topic!r} does not match aligned topic {topic.topic!r}")

    proof_declarations = inventory_isabelle_declarations(
        topic.isabelle_proof_content,
        topic=topic.topic,
    )
    stmt_declarations = inventory_isabelle_declarations(
        topic.isabelle_stmt_content,
        topic=topic.topic,
    )

    declaration = _find_declaration(
        proof_declarations,
        target.isabelle_target_name,
        prover="Isabelle proof",
    )
    _find_declaration(
        stmt_declarations,
        target.isabelle_target_name,
        prover="Isabelle proof-masked statement",
    )

    if declaration.proof_span is None:
        raise ValueError(f"Isabelle target declaration {declaration.name!r} has no proof span.")

    statement_start, statement_end = declaration.statement_span
    proof_start, proof_end = declaration.proof_span
    block_start, block_end = declaration.declaration_span

    return IsabelleTarget(
        name=declaration.name,
        kind=declaration.kind,
        statement=topic.isabelle_proof_content[statement_start:statement_end].strip(),
        proof=topic.isabelle_proof_content[proof_start:proof_end].strip(),
        full_block=topic.isabelle_proof_content[block_start:block_end].strip(),
        declaration_span=declaration.declaration_span,
        statement_span=declaration.statement_span,
        proof_span=declaration.proof_span,
        line_start=declaration.line_start,
        line_end=declaration.line_end,
    )


def build_v1_record(topic: AlignedBabelTopic, target: BabelTarget) -> dict[str, Any]:
    _validate_verified_target(target)

    isabelle = extract_isabelle_target(topic, target)
    lean4 = sanitize_lean_target(
        topic.lean4_stmt_content,
        target.lean4_target_name,
        topic=topic.topic,
    )

    return {
        "source": BABEL_FORMAL,
        "theorem_id": topic.theorem_id,
        "topic": topic.topic,
        "tier": topic.tier,
        "target_key": target.target_key,
        "isabelle_target_name": target.isabelle_target_name,
        "lean4_target_name": target.lean4_target_name,
        "isabelle_statement": isabelle.statement,
        "isabelle_proof": isabelle.proof,
        "isabelle_reference_context": topic.isabelle_stmt_content.strip(),
        "lean4_statement": lean4.statement,
        "lean4_header": lean4.header,
        "lean4_footer": lean4.footer,
        "context_mode": CONTEXT_MODE,
        "target_alignment_status": target.status,
        "semantic_alignment_verified": target.semantic_alignment_verified,
        "metadata": {
            "isabelle": isabelle.to_dict(),
            "lean4": lean4.to_dict(),
            "isabelle_proof_sha256": topic.isabelle_proof_sha256,
            "isabelle_stmt_sha256": topic.isabelle_stmt_sha256,
            "lean4_stmt_sha256": topic.lean4_stmt_sha256,
        },
    }


def _load_topic_from_args(args: argparse.Namespace) -> AlignedBabelTopic:
    if args.id is None and not args.topic:
        raise SystemExit("Provide --id or --topic.")

    if args.id is not None:
        topic = load_babel_topic(args.id)
        if args.topic and args.topic != topic.topic:
            raise SystemExit(f"--topic {args.topic!r} does not match theorem_id {args.id}: {topic.topic!r}")
        return topic

    return load_babel_topic_by_name(args.topic)


def _topics_for_args(args: argparse.Namespace) -> list[AlignedBabelTopic]:
    if args.all_topics:
        if args.id is not None or args.topic:
            raise SystemExit("Use either --all-topics or --id/--topic, not both.")
        if not args.all_targets:
            raise SystemExit("--all-topics requires --all-targets.")
        return list(iter_babel_topics())

    return [_load_topic_from_args(args)]


def _targets_for_args(args: argparse.Namespace, topic: AlignedBabelTopic) -> list[BabelTarget]:
    if args.all_targets:
        return [
            target
            for target in iter_babel_targets(statuses=["verified"])
            if target.topic == topic.topic
        ]

    if not args.target_key:
        raise SystemExit("Provide --target-key or --all-targets.")

    return [get_babel_target(topic=topic.topic, target_key=args.target_key)]


def _print_json(data: Any, *, include_indent: bool = True) -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    indent = 2 if include_indent else None
    print(json.dumps(data, indent=indent, ensure_ascii=False))


def _resolve_output_path(output: str) -> Path:
    root = resolved_repo_root()
    path = Path(output).expanduser()
    if not path.is_absolute():
        path = root / path
    resolved = path.resolve(strict=False)
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise SystemExit(f"--output must be inside repo root {root}: {resolved}") from exc
    return resolved


def _write_records(records: list[dict[str, Any]], args: argparse.Namespace) -> None:
    if args.output:
        output_path = _resolve_output_path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        if args.jsonl:
            payload = "\n".join(json.dumps(record, ensure_ascii=False) for record in records)
            output_path.write_text(payload + ("\n" if payload else ""), encoding="utf-8")
        else:
            data: Any = records[0] if len(records) == 1 else records
            output_path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"Wrote {len(records)} record(s) to {output_path}")
        return

    if args.jsonl:
        for record in records:
            _print_json(record, include_indent=False)
        return

    if len(records) == 1:
        _print_json(records[0])
    else:
        _print_json(records)


def main() -> None:
    parser = argparse.ArgumentParser(description="Build parsed Babel Formal V1 target records.")
    parser.add_argument("--source", default=BABEL_FORMAL, choices=[BABEL_FORMAL])
    parser.add_argument("--expected-root", help=f"Expected repo root, e.g. {LAB_REPO_ROOT}.")
    parser.add_argument("--check-layout", action="store_true", help="Validate repo/input paths and exit.")
    parser.add_argument("--id", type=int, help="Babel theorem_id.")
    parser.add_argument("--topic", help="Babel topic name.")
    parser.add_argument("--all-topics", action="store_true", help="Build verified targets across all Babel topics.")
    parser.add_argument("--target-key", help="Manifest target key.")
    parser.add_argument("--all-targets", action="store_true", help="Build every verified target in the topic.")
    parser.add_argument("--jsonl", action="store_true", help="Print one compact JSON record per line.")
    parser.add_argument("--output", help="Write JSON/JSONL under the repo root instead of printing to stdout.")
    args = parser.parse_args()

    if args.expected_root or args.check_layout:
        layout = validate_repo_layout(args.expected_root)
        if args.check_layout:
            _print_json(layout)
            return

    records: list[dict[str, Any]] = []
    for topic in _topics_for_args(args):
        targets = _targets_for_args(args, topic)
        records.extend(build_v1_record(topic, target) for target in targets)

    if not records:
        raise SystemExit("No verified target records found. Add verified targets to the Babel manifest first.")

    _write_records(records, args)


if __name__ == "__main__":
    main()
