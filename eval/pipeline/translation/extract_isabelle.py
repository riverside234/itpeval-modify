"""Utilities for extracting a target theorem and proof from Isabelle/HOL source.

The first version intentionally focuses only on:

    whole Isabelle source
        ->
    target theorem statement
        +
    target proof body

Dependency / used-lemma extraction should be added separately after this
works reliably on the ITPEval Isabelle data.
"""

from __future__ import annotations

import re
from dataclasses import dataclass


# Isabelle declarations that can introduce theorem-like results.
DECL_RE = re.compile(
    r"^\s*"
    r"(theorem|lemma|corollary|proposition)"
    r"\s+"
    r"([A-Za-z0-9_'.-]+)"
    r"\s*:",
    re.MULTILINE,
)


# Common starts of an Isabelle proof.
#
# Examples:
#
#   proof
#   proof -
#   by simp
#   using foo
#   unfolding foo_def
#   apply simp
#
PROOF_START_RE = re.compile(
    r"^\s*(proof\b|by\b|using\b|unfolding\b|apply\b)",
    re.MULTILINE,
)


@dataclass
class IsabelleTheorem:
    """One extracted Isabelle theorem."""

    name: str
    declaration_kind: str
    statement: str
    proof: str
    full_block: str


def list_theorem_names(source: str) -> list[str]:
    """Return theorem-like declaration names appearing in source."""

    return [m.group(2) for m in DECL_RE.finditer(source)]


def _normalize_name(name: str) -> str:
    """Small normalization used only as a fallback for matching."""

    name = name.strip()

    # Allow callers to accidentally pass:
    #
    #   theorem foo
    #   lemma foo
    #
    name = re.sub(
        r"^(theorem|lemma|corollary|proposition)\s+",
        "",
        name,
        flags=re.IGNORECASE,
    )

    # Remove trailing colon if present.
    name = name.rstrip(":")

    return name


def _find_target_declaration(
    source: str,
    theorem_name: str,
) -> re.Match[str]:
    """Find the declaration corresponding to theorem_name."""

    theorem_name = _normalize_name(theorem_name)

    matches = list(DECL_RE.finditer(source))

    if not matches:
        raise ValueError(
            "No Isabelle theorem/lemma declarations were found in the source."
        )

    # 1. Exact name match.
    for match in matches:
        if match.group(2) == theorem_name:
            return match

    # 2. Case-insensitive exact match.
    for match in matches:
        if match.group(2).lower() == theorem_name.lower():
            return match

    available = ", ".join(match.group(2) for match in matches)

    raise ValueError(
        f"Could not find Isabelle theorem {theorem_name!r}. "
        f"Available declarations: {available}"
    )


def _find_block_end(
    source: str,
    target_match: re.Match[str],
) -> int:
    """Find the end of the target theorem block.

    For the first implementation, the block ends immediately before the next
    theorem-like declaration. If this is the final declaration in the theory,
    it extends to the end of the source.

    We later trim a trailing Isabelle `end`.
    """

    target_start = target_match.start()

    for match in DECL_RE.finditer(source, target_match.end()):
        if match.start() > target_start:
            return match.start()

    return len(source)


def _trim_theory_end(block: str) -> str:
    """Remove a trailing top-level `end` from the extracted final theorem."""

    lines = block.rstrip().splitlines()

    while lines and not lines[-1].strip():
        lines.pop()

    if lines and lines[-1].strip() == "end":
        lines.pop()

    return "\n".join(lines).rstrip()


def _split_statement_and_proof(
    block: str,
) -> tuple[str, str]:
    """Split one Isabelle theorem block into statement and proof.

    Example:

        theorem foo:
          "x + 0 = x"
        proof
          ...
        qed

    becomes:

        statement:
            theorem foo:
              "x + 0 = x"

        proof:
            proof
              ...
            qed
    """

    proof_match = PROOF_START_RE.search(block)

    if proof_match is None:
        raise ValueError(
            "Found the target theorem declaration, but could not locate "
            "the beginning of its proof."
        )

    statement = block[: proof_match.start()].strip()
    proof = block[proof_match.start() :].strip()

    if not statement:
        raise ValueError("Extracted theorem statement is empty.")

    if not proof:
        raise ValueError("Extracted theorem proof is empty.")

    return statement, proof


def extract_target_theorem(
    source: str,
    theorem_name: str,
) -> IsabelleTheorem:
    """Extract one target theorem from an Isabelle theory/source string.

    Parameters
    ----------
    source:
        Isabelle source. This may be an entire `.thy` file.

    theorem_name:
        Exact Isabelle theorem/lemma identifier, e.g.
        ``circle_average_shift``.

    Returns
    -------
    IsabelleTheorem
        Contains:
        - name
        - declaration_kind
        - statement
        - proof
        - full_block

    Raises
    ------
    ValueError
        If the theorem cannot be found or the proof cannot be separated.
    """

    if not source or not source.strip():
        raise ValueError("Isabelle source is empty.")

    if not theorem_name or not theorem_name.strip():
        raise ValueError("theorem_name is empty.")

    target_match = _find_target_declaration(
        source,
        theorem_name,
    )

    block_start = target_match.start()
    block_end = _find_block_end(
        source,
        target_match,
    )

    full_block = source[block_start:block_end]
    full_block = _trim_theory_end(full_block)

    statement, proof = _split_statement_and_proof(full_block)

    return IsabelleTheorem(
        name=target_match.group(2),
        declaration_kind=target_match.group(1),
        statement=statement,
        proof=proof,
        full_block=full_block,
    )


def extract_statement_and_proof(
    source: str,
    theorem_name: str,
) -> tuple[str, str]:
    """Convenience wrapper returning only statement and proof."""

    theorem = extract_target_theorem(
        source=source,
        theorem_name=theorem_name,
    )

    return theorem.statement, theorem.proof
