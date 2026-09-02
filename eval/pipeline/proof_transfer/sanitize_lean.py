from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from typing import Any

from eval.pipeline.proof_transfer.aligned_data import (
    BABEL_FORMAL,
    LAB_REPO_ROOT,
    load_babel_topic,
    load_babel_topic_by_name,
    validate_repo_layout,
)
from eval.pipeline.proof_transfer.inventory import (
    Declaration,
    inventory_lean4_declarations,
)
from eval.pipeline.proof_transfer.manifest import get_babel_target


LEAN_SORRY_BODY = ":= by sorry"
LEAN_TARGET_SUFFIX = " := by sorry"
TRAILING_END_RE = re.compile(r"^end(?:\s+\S+)?$")


@dataclass(frozen=True)
class SanitizedLeanTarget:
    name: str
    kind: str
    statement: str
    header: str
    footer: str
    original_declaration: str
    original_proof: str
    declaration_span: tuple[int, int]
    statement_span: tuple[int, int]
    proof_span: tuple[int, int] | None
    line_start: int
    line_end: int
    prior_theorem_count: int

    @property
    def file_content(self) -> str:
        parts = [part for part in (self.header, self.statement, self.footer) if part]
        return "\n\n".join(parts).rstrip() + "\n"

    def to_dict(self, *, include_file_content: bool = False) -> dict[str, Any]:
        data = asdict(self)
        if include_file_content:
            data["file_content"] = self.file_content
        return data


def _find_declaration(declarations: list[Declaration], name: str) -> Declaration:
    for declaration in declarations:
        if declaration.name == name:
            return declaration

    for declaration in declarations:
        if declaration.name.lower() == name.lower():
            return declaration

    available = ", ".join(declaration.name for declaration in declarations)
    raise ValueError(f"could not find Lean4 declaration {name!r}; available: {available}")


def _replace_spans(content: str, replacements: list[tuple[tuple[int, int], str]]) -> str:
    updated = content
    for (start, end), replacement in sorted(replacements, reverse=True):
        updated = updated[:start] + replacement + updated[end:]
    return updated


def proof_erase_lean_theorem_bodies(content: str, *, topic: str = "") -> str:
    replacements: list[tuple[tuple[int, int], str]] = []
    for declaration in inventory_lean4_declarations(content, topic=topic):
        if declaration.proof_span is not None:
            replacements.append((declaration.proof_span, LEAN_SORRY_BODY))
    return _replace_spans(content, replacements)


def _extract_trailing_footer(content: str) -> str:
    footer_lines: list[str] = []
    for line in reversed(content.rstrip().splitlines()):
        stripped = line.strip()
        if not stripped or stripped.startswith("--") or TRAILING_END_RE.match(stripped):
            footer_lines.append(line)
            continue
        break
    return "\n".join(reversed(footer_lines)).strip()


def sanitize_lean_target(
    content: str,
    target_name: str,
    *,
    topic: str = "",
) -> SanitizedLeanTarget:
    if not content.strip():
        raise ValueError("Lean4 statement file content is empty.")
    if not target_name.strip():
        raise ValueError("Lean4 target name is empty.")

    declarations = inventory_lean4_declarations(content, topic=topic)
    target = _find_declaration(declarations, target_name.strip())

    raw_header = content[: target.char_start].rstrip()
    header = proof_erase_lean_theorem_bodies(raw_header, topic=topic).rstrip()
    statement_prefix = content[target.statement_span[0] : target.statement_span[1]].rstrip()
    if not statement_prefix:
        raise ValueError(f"Lean4 target declaration {target.name!r} has an empty statement.")

    proof = ""
    if target.proof_span is not None:
        proof = content[target.proof_span[0] : target.proof_span[1]].strip()

    return SanitizedLeanTarget(
        name=target.name,
        kind=target.kind,
        statement=f"{statement_prefix}{LEAN_TARGET_SUFFIX}",
        header=header,
        footer=_extract_trailing_footer(content),
        original_declaration=target.text,
        original_proof=proof,
        declaration_span=target.declaration_span,
        statement_span=target.statement_span,
        proof_span=target.proof_span,
        line_start=target.line_start,
        line_end=target.line_end,
        prior_theorem_count=len(inventory_lean4_declarations(raw_header, topic=topic)),
    )


def _load_topic_from_args(args: argparse.Namespace) -> Any:
    if args.id is None and not args.topic:
        raise SystemExit("Provide --id or --topic.")

    if args.id is not None:
        topic = load_babel_topic(args.id)
        if args.topic and args.topic != topic.topic:
            raise SystemExit(f"--topic {args.topic!r} does not match theorem_id {args.id}: {topic.topic!r}")
        return topic

    return load_babel_topic_by_name(args.topic)


def _print_json(data: Any, *, include_indent: bool = True) -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    indent = 2 if include_indent else None
    print(json.dumps(data, indent=indent, ensure_ascii=False))


def main() -> None:
    parser = argparse.ArgumentParser(description="Sanitize one Babel Formal Lean4 target statement.")
    parser.add_argument("--source", default=BABEL_FORMAL, choices=[BABEL_FORMAL])
    parser.add_argument("--expected-root", help=f"Expected repo root, e.g. {LAB_REPO_ROOT}.")
    parser.add_argument("--check-layout", action="store_true", help="Validate repo/input paths and exit.")
    parser.add_argument("--id", type=int, help="Babel theorem_id.")
    parser.add_argument("--topic", help="Babel topic name.")
    parser.add_argument("--target-key", required=False, help="Manifest target key.")
    parser.add_argument("--include-file-content", action="store_true")
    args = parser.parse_args()

    if args.expected_root or args.check_layout:
        layout = validate_repo_layout(args.expected_root)
        if args.check_layout:
            _print_json(layout)
            return

    if not args.target_key:
        raise SystemExit("Provide --target-key.")

    topic = _load_topic_from_args(args)
    target = get_babel_target(topic=topic.topic, target_key=args.target_key)
    lean = sanitize_lean_target(
        topic.lean4_stmt_content,
        target.lean4_target_name,
        topic=topic.topic,
    )
    _print_json(lean.to_dict(include_file_content=args.include_file_content))


if __name__ == "__main__":
    main()
