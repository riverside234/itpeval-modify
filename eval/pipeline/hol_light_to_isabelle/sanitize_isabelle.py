from __future__ import annotations

import re
from dataclasses import dataclass

from eval.pipeline.proof_transfer.inventory import inventory_isabelle_declarations


@dataclass(frozen=True)
class IsabelleTarget:
    name: str
    statement: str
    proof_prefix: str
    context_before_target: str
    theory_template: str
    proof_span: tuple[int, int]
    prior_theorem_count: int
    line_start: int


def sanitize_target(content: str, target_name: str, *, topic: str = "") -> IsabelleTarget:
    declarations = inventory_isabelle_declarations(content, topic=topic)
    matches = [declaration for declaration in declarations if declaration.name == target_name]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one Isabelle target {target_name!r}, found {len(matches)}")
    target = matches[0]
    if target.proof_span is None:
        raise ValueError(f"Isabelle target {target_name!r} has no proof placeholder")
    proof_start, proof_end = target.proof_span
    body = content[proof_start:proof_end]
    placeholder = re.search(r"(?m)^[ \t]*\bsorry\b", body)
    if placeholder is None:
        raise ValueError(f"Isabelle target {target_name!r} has no masked sorry: {body[:100]!r}")
    proof_prefix = body[:placeholder.start()]
    if proof_prefix.strip() and not re.fullmatch(
        r"\s*(?:(?:unfolding|using)\b[^\n]*\n\s*)+", proof_prefix
    ):
        raise ValueError(f"unexpected Isabelle proof prefix for {target_name!r}: {proof_prefix[:100]!r}")
    sorry_offset = placeholder.end() - len("sorry")
    span = (proof_start + sorry_offset, proof_start + placeholder.end())
    statement = content[slice(*target.statement_span)].strip()
    if not statement:
        raise ValueError(f"Isabelle target {target_name!r} has empty statement")
    prefix = content[:target.char_start]
    return IsabelleTarget(
        name=target.name, statement=statement, proof_prefix=proof_prefix.strip(),
        context_before_target=prefix, theory_template=content,
        proof_span=span,
        prior_theorem_count=sum(d.char_start < target.char_start for d in declarations),
        line_start=target.line_start,
    )
