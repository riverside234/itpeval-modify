from __future__ import annotations

import argparse
import re
from dataclasses import dataclass

from eval.pipeline.hol_light_to_isabelle.aligned_data import iter_topics
from eval.pipeline.hol_light_to_isabelle.common import LAB_REPO_ROOT, validate_layout
from eval.pipeline.proof_transfer.inventory import inventory_isabelle_declarations


LET_RE = re.compile(r"(?m)^let[ \t]+([A-Za-z_][A-Za-z_0-9']*)[ \t]*=[ \t]*")
TERM_QUOTE = chr(96)


@dataclass(frozen=True)
class HolDeclaration:
    name: str
    statement: str
    proof: str | None
    declaration_span: tuple[int, int]
    statement_span: tuple[int, int]
    proof_span: tuple[int, int] | None
    line_start: int
    line_end: int
    text: str


def _terminator(content: str, start: int) -> int:
    """Find a top-level OCaml phrase terminator outside HOL terms and comments."""
    i, comment_depth = start, 0
    in_term = in_string = False
    while i < len(content) - 1:
        pair = content[i:i + 2]
        if comment_depth:
            if pair == "(*":
                comment_depth += 1
                i += 2
                continue
            if pair == "*)":
                comment_depth -= 1
                i += 2
                continue
        elif in_term:
            if content[i] == TERM_QUOTE:
                in_term = False
        elif in_string:
            if content[i] == "\\":
                i += 2
                continue
            if content[i] == '"':
                in_string = False
        else:
            if pair == "(*":
                comment_depth = 1
                i += 2
                continue
            if pair == ";;":
                return i + 2
            if content[i] == TERM_QUOTE:
                in_term = True
            elif content[i] == '"':
                in_string = True
        i += 1
    raise ValueError(f"unterminated HOL Light declaration at offset {start}")


def _quotation(content: str, start: int, end: int) -> tuple[int, int]:
    opening = content.find(TERM_QUOTE, start, end)
    if opening < 0:
        raise ValueError(f"missing HOL Light term quotation at offset {start}")
    closing = content.find(TERM_QUOTE, opening + 1, end)
    if closing < 0:
        raise ValueError(f"unterminated HOL Light term quotation at offset {opening}")
    return opening + 1, closing


def inventory_hol_declarations(content: str, *, masked: bool) -> list[HolDeclaration]:
    declarations: list[HolDeclaration] = []
    cursor = 0
    while match := LET_RE.search(content, cursor):
        end = _terminator(content, match.end())
        cursor = end
        rhs = content[match.end():end - 2]
        is_proof = bool(re.match(r"\s*prove\b", rhs))
        if masked and is_proof:
            raise ValueError(f"masked HOL Light file contains proof declaration {match.group(1)}")
        if masked and not rhs.lstrip().startswith(TERM_QUOTE):
            continue
        if not masked and not is_proof:
            continue
        quote_start, quote_end = _quotation(content, match.end(), end - 2)
        statement = content[quote_start:quote_end].strip()
        if not statement:
            raise ValueError(f"empty HOL Light statement {match.group(1)}")
        proof_span = None
        proof = None
        if is_proof:
            after_term = quote_end + 1
            comma = re.match(r"\s*,", content[after_term:end - 2])
            if not comma:
                raise ValueError(f"missing statement/proof separator for {match.group(1)}")
            proof_start = after_term + comma.end()
            close = content.rfind(")", proof_start, end - 2)
            if close < 0 or content[close + 1:end - 2].strip():
                raise ValueError(f"malformed prove call for {match.group(1)}")
            proof_span = (proof_start, close)
            proof = content[proof_start:close].strip()
            if not proof:
                raise ValueError(f"empty HOL Light proof {match.group(1)}")
        declarations.append(HolDeclaration(
            name=match.group(1), statement=statement, proof=proof,
            declaration_span=(match.start(), end),
            statement_span=(quote_start, quote_end), proof_span=proof_span,
            line_start=content.count("\n", 0, match.start()) + 1,
            line_end=content.count("\n", 0, end) + 1,
            text=content[match.start():end],
        ))
    return declarations


def inventory_topic(topic) -> dict:
    proof = inventory_hol_declarations(topic.hol_light_proof_content, masked=False)
    masked = inventory_hol_declarations(topic.hol_light_stmt_content, masked=True)
    isa = inventory_isabelle_declarations(topic.isabelle_stmt_content, topic=topic.topic)
    proof_names = {d.name for d in proof}
    masked_names = {d.name for d in masked}
    isa_names = {d.name for d in isa}
    matches = sorted(proof_names & masked_names & isa_names)
    candidate_pairs = match_pairs(proof, masked, isa)
    return {
        "theorem_id": topic.theorem_id, "topic": topic.topic,
        "hol_light_proofs": len(proof), "hol_light_stmts": len(masked),
        "isabelle_stmts": len(isa), "exact_name_matches": matches,
        "candidate_pairs": candidate_pairs,
    }


def match_pairs(proof, masked, isa) -> list[tuple[str, str, str]]:
    """Return unique exact or case-folded candidate name pairs."""
    masked_names = {d.name for d in masked}
    isa_by_fold: dict[str, list[str]] = {}
    for declaration in isa:
        isa_by_fold.setdefault(declaration.name.casefold(), []).append(declaration.name)
    pairs = []
    for source in proof:
        if source.name not in masked_names:
            continue
        matches = isa_by_fold.get(source.name.casefold(), [])
        if len(matches) != 1:
            continue
        target = matches[0]
        pairs.append((source.name, target,
                      "exact_name_match" if source.name == target else "casefold_name_match"))
    return pairs


def main() -> None:
    parser = argparse.ArgumentParser(description="Inventory HOL Light to Isabelle Babel targets.")
    parser.add_argument("--expected-root", default=None, help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--all-topics", action="store_true")
    parser.add_argument("--topic")
    parser.add_argument("--names", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.all_topics and args.topic:
        parser.error("choose --all-topics or --topic")
    topics = list(iter_topics(topic=args.topic))
    if not topics:
        parser.error("no matching topics")
    total = 0
    for topic in topics:
        row = inventory_topic(topic)
        names = row["candidate_pairs"]
        total += len(names)
        print(f'{topic.theorem_id:2d} {topic.topic}: hol_light_proofs={row["hol_light_proofs"]} '
              f'hol_light_stmts={row["hol_light_stmts"]} '
              f'isabelle_stmts={row["isabelle_stmts"]} '
              f'exact_matches={len(row["exact_name_matches"])} candidates={len(names)}')
        if args.names:
            for source, target, status in names:
                print(f"  {source} -> {target} ({status})")
    print(f"Total candidate matches: {total}")


if __name__ == "__main__":
    main()
