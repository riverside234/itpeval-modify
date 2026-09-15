from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any


STATEMENT_ONLY_PROMPT_VERSION = "babel_formal_v1_isabelle_statement_only_2026_09_15_p1"

SYSTEM_PROMPT = (
    "You are an expert mathematician and formal theorem prover, fluent in "
    "Isabelle/HOL and Lean 4. This is a statement-only control experiment. "
    "Convert the specified Isabelle theorem statement into a mathematical proof "
    "Draft that could help a later automated proof-generation stage. You are "
    "not given the original Isabelle proof. Do not pretend to know source proof "
    "steps that were not provided. Instead, produce a plausible mathematical "
    "proof plan from the theorem statement and any proof-masked reference "
    "statements explicitly supplied. Preserve names of relevant definitions, "
    "assumptions, and helper theorem statements when they are available. Return "
    "only the final Draft using numbered proof-step headings."
)


@dataclass(frozen=True)
class StatementOnlyPrompt:
    system_prompt: str
    user_prompt: str
    prompt_version: str = STATEMENT_ONLY_PROMPT_VERSION
    input_mode: str = "isabelle_statement_only"


def _required_text(record: dict[str, Any], key: str) -> str:
    value = record.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"record is missing required non-empty text field {key!r}")
    return value.strip()


def _fenced(language: str, content: str) -> str:
    return f"```{language}\n{content.rstrip()}\n```"


def build_statement_only_prompt(
    record: dict[str, Any],
    *,
    include_reference_context: bool = False,
) -> StatementOnlyPrompt:
    """Build the statement-only control prompt for one parsed V1 record."""
    source = record.get("source", "")
    theorem_id = record.get("theorem_id", "")
    topic = record.get("topic", "")
    target_key = record.get("target_key", "")
    input_mode = (
        "isabelle_statement_plus_masked_reference"
        if include_reference_context
        else "isabelle_statement_only"
    )

    sections = [
        "EXPERIMENT TARGET\n"
        f"source: {source}\n"
        f"theorem_id: {theorem_id}\n"
        f"topic: {topic}\n"
        f"target_key: {target_key}\n"
        f"control_input_mode: {input_mode}",
        "TARGET ISABELLE THEOREM STATEMENT\n"
        + _fenced("isabelle", _required_text(record, "isabelle_statement")),
    ]

    if include_reference_context:
        sections.append(
            "PROOF-MASKED REFERENCE ISABELLE FILE\n"
            + _fenced("isabelle", _required_text(record, "isabelle_reference_context"))
        )

    sections.append(
        "DRAFT REQUIREMENTS\n"
        "- This is a control run: do not use the original Isabelle proof.\n"
        "- Do not use the oracle Lean statement, Lean header, Lean proof, or any target-language proof.\n"
        "- Use only the target Isabelle theorem statement"
        + (" and the proof-masked Isabelle reference file" if include_reference_context else "")
        + ".\n"
        "- If a proof-masked reference file is provided, use it only for definitions, notation, assumptions, and helper theorem statements; do not use sorry placeholders as evidence.\n"
        "- Produce a mathematical Draft: a sequence of useful claims, reductions, cases, witnesses, or lemmas that could plausibly reconstruct the target theorem.\n"
        "- Preserve variable names, function names, constants, definitions, assumptions, and helper theorem names when they appear in the provided Isabelle text.\n"
        "- Prefer explicit formulas, equations, inequalities, quantified propositions, set relations, implications, or witnesses.\n"
        "- Do not mention tactic names, proof commands, automation procedures, source-prover implementation details, or the fact that this is only a control run.\n"
        "- Do not include code fences, Lean code, Isabelle code, hidden reasoning, or meta-commentary.\n"
        "- The final step must state the target conclusion.\n"
        "- Output only proof-draft steps in this format:\n"
        "### Step 1:\n"
        "...\n\n"
        "### Step 2:\n"
        "..."
    )

    return StatementOnlyPrompt(
        system_prompt=SYSTEM_PROMPT,
        user_prompt="\n\n".join(sections),
        input_mode=input_mode,
    )


_THINK_RE = re.compile(r"<think\b[^>]*>.*?</think>", re.IGNORECASE | re.DOTALL)
_FENCE_RE = re.compile(r"\A```(?:[A-Za-z0-9_+-]+)?\s*\n(?P<body>.*)\n```\s*\Z", re.DOTALL)


def normalize_draft_content(content: str) -> str:
    """Strip accidental wrappers while preserving visible final text only."""
    content = _THINK_RE.sub("", content).strip()
    match = _FENCE_RE.match(content)
    if match:
        content = match.group("body").strip()
    return content
