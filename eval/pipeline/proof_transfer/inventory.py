from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from typing import Iterable, Literal

from eval.pipeline.proof_transfer.aligned_data import (
    BABEL_FORMAL,
    AlignedBabelTopic,
    iter_babel_topics,
)


DeclarationKind = Literal["theorem", "lemma", "corollary", "proposition"]


@dataclass(frozen=True)
class Declaration:
    prover: str
    topic: str
    kind: str
    name: str
    line_start: int
    line_end: int
    char_start: int
    char_end: int
    statement_span: tuple[int, int]
    proof_span: tuple[int, int] | None
    declaration_span: tuple[int, int]
    text: str

    def to_dict(self, *, include_text: bool = False) -> dict:
        data = asdict(self)
        if not include_text:
            data.pop("text", None)
        return data


ISABELLE_DECL_RE = re.compile(
    r"(?m)^(?P<indent>[ \t]*)(?P<kind>lemma|theorem|corollary|proposition)\s+"
    r"(?P<name>[^\s:]+)\s*:"
)
ISABELLE_BOUNDARY_RE = re.compile(
    r"(?m)^[ \t]*(?:lemma|theorem|corollary|proposition|definition|datatype|fun|locale|context|end)\b"
)
ISABELLE_PROOF_RE = re.compile(
    r"(?m)^[ \t]*(?:sorry|by\b|proof\b|unfolding\b|using\b|apply\b)"
)

LEAN4_DECL_RE = re.compile(
    r"(?m)^(?P<indent>[ \t]*)(?P<kind>theorem|lemma)\s+(?P<name>[^\s(:]+)"
)
LEAN4_BOUNDARY_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:noncomputable|protected|private)\s+)?"
    r"(?:theorem|lemma|def|axiom|class|structure|inductive|instance|abbrev|namespace|section|end|variable)\b"
)


def _line_number(content: str, char_index: int) -> int:
    return content.count("\n", 0, char_index) + 1


def _line_end(content: str, char_index: int) -> int:
    if char_index <= 0:
        return 1
    return _line_number(content, max(0, char_index - 1))


def _next_boundary(content: str, boundary_re: re.Pattern[str], start: int) -> int:
    match = boundary_re.search(content, start)
    return match.start() if match else len(content)


def _isabelle_statement_and_proof_spans(
    content: str,
    start: int,
    end: int,
) -> tuple[tuple[int, int], tuple[int, int] | None]:
    block = content[start:end]
    proof_match = ISABELLE_PROOF_RE.search(block)
    if not proof_match:
        return (start, end), None
    proof_start = start + proof_match.start()
    return (start, proof_start), (proof_start, end)


def _lean4_statement_and_proof_spans(
    content: str,
    start: int,
    end: int,
) -> tuple[tuple[int, int], tuple[int, int] | None]:
    assign = content.find(":=", start, end)
    if assign == -1:
        return (start, end), None
    return (start, assign), (assign, end)


def _inventory_declarations(
    *,
    content: str,
    topic: str,
    prover: str,
    decl_re: re.Pattern[str],
    boundary_re: re.Pattern[str],
) -> list[Declaration]:
    declarations: list[Declaration] = []
    matches = list(decl_re.finditer(content))

    for match in matches:
        start = match.start()
        end = _next_boundary(content, boundary_re, match.end())
        text = content[start:end].rstrip()
        char_end = start + len(text)

        if prover == "isabelle":
            statement_span, proof_span = _isabelle_statement_and_proof_spans(content, start, char_end)
        elif prover == "lean4":
            statement_span, proof_span = _lean4_statement_and_proof_spans(content, start, char_end)
        else:
            raise ValueError(f"unsupported prover: {prover}")

        declarations.append(
            Declaration(
                prover=prover,
                topic=topic,
                kind=match.group("kind"),
                name=match.group("name"),
                line_start=_line_number(content, start),
                line_end=_line_end(content, char_end),
                char_start=start,
                char_end=char_end,
                statement_span=statement_span,
                proof_span=proof_span,
                declaration_span=(start, char_end),
                text=text,
            )
        )

    return declarations


def inventory_isabelle_declarations(content: str, *, topic: str = "") -> list[Declaration]:
    return _inventory_declarations(
        content=content,
        topic=topic,
        prover="isabelle",
        decl_re=ISABELLE_DECL_RE,
        boundary_re=ISABELLE_BOUNDARY_RE,
    )


def inventory_lean4_declarations(content: str, *, topic: str = "") -> list[Declaration]:
    return _inventory_declarations(
        content=content,
        topic=topic,
        prover="lean4",
        decl_re=LEAN4_DECL_RE,
        boundary_re=LEAN4_BOUNDARY_RE,
    )


def exact_name_matches(
    isabelle_declarations: Iterable[Declaration],
    lean4_declarations: Iterable[Declaration],
) -> list[str]:
    isabelle_names = {decl.name for decl in isabelle_declarations}
    lean4_names = {decl.name for decl in lean4_declarations}
    return sorted(isabelle_names & lean4_names)


def inventory_babel_topic(topic: AlignedBabelTopic) -> dict:
    isabelle_proof_decls = inventory_isabelle_declarations(
        topic.isabelle_proof_content,
        topic=topic.topic,
    )
    isabelle_stmt_decls = inventory_isabelle_declarations(
        topic.isabelle_stmt_content,
        topic=topic.topic,
    )
    lean4_stmt_decls = inventory_lean4_declarations(
        topic.lean4_stmt_content,
        topic=topic.topic,
    )

    matches = exact_name_matches(isabelle_proof_decls, lean4_stmt_decls)
    return {
        **topic.to_metadata_dict(),
        "isabelle_proof_declaration_count": len(isabelle_proof_decls),
        "isabelle_stmt_declaration_count": len(isabelle_stmt_decls),
        "lean4_stmt_declaration_count": len(lean4_stmt_decls),
        "exact_name_match_count": len(matches),
        "exact_name_matches": matches,
        "isabelle_proof_declarations": [decl.to_dict() for decl in isabelle_proof_decls],
        "isabelle_stmt_declarations": [decl.to_dict() for decl in isabelle_stmt_decls],
        "lean4_stmt_declarations": [decl.to_dict() for decl in lean4_stmt_decls],
    }


def inventory_babel_topics(
    *,
    theorem_ids: Iterable[int] | None = None,
    topics: Iterable[str] | None = None,
) -> list[dict]:
    return [
        inventory_babel_topic(topic)
        for topic in iter_babel_topics(theorem_ids=theorem_ids, topics=topics)
    ]


def _parse_csv(value: str | None) -> list[str] | None:
    if not value:
        return None
    return [item.strip() for item in value.split(",") if item.strip()]


def main() -> None:
    parser = argparse.ArgumentParser(description="Inventory Babel Formal theorem declarations.")
    parser.add_argument("--source", default=BABEL_FORMAL, choices=[BABEL_FORMAL])
    parser.add_argument("--ids", help="Comma-separated Babel theorem_ids.")
    parser.add_argument("--topics", help="Comma-separated Babel topic names.")
    parser.add_argument("--json", action="store_true", help="Print machine-readable JSON.")
    parser.add_argument("--names", action="store_true", help="Print exact-name match names.")
    args = parser.parse_args()

    theorem_ids = [int(item) for item in _parse_csv(args.ids) or []] or None
    topics = _parse_csv(args.topics)
    inventories = inventory_babel_topics(theorem_ids=theorem_ids, topics=topics)

    if args.json:
        print(json.dumps(inventories, indent=2, ensure_ascii=False))
        return

    total_matches = 0
    for item in inventories:
        total_matches += item["exact_name_match_count"]
        print(
            f"{item['theorem_id']:>2} {item['topic']}: "
            f"isabelle_proofs={item['isabelle_proof_declaration_count']} "
            f"isabelle_stmts={item['isabelle_stmt_declaration_count']} "
            f"lean4_stmts={item['lean4_stmt_declaration_count']} "
            f"exact_matches={item['exact_name_match_count']}"
        )
        if args.names:
            for name in item["exact_name_matches"]:
                print(f"  - {name}")

    print(f"Total exact-name matches: {total_matches}")


if __name__ == "__main__":
    main()

