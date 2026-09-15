from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from eval.pipeline.proof_transfer.inventory import inventory_isabelle_declarations


STATEMENT_ONLY_PROMPT_VERSION = "babel_formal_v1_isabelle_statement_reference_2026_09_15_p4"
INPUT_MODE = "isabelle_statement_plus_masked_reference"

SYSTEM_PROMPT = (
    "You are an expert mathematician and formal theorem prover, fluent in "
    "Isabelle/HOL and Lean 4. Generate a mathematical Draft for one theorem "
    "from the provided proof-masked Isabelle theorem statement and proof-masked "
    "Isabelle reference context. This is a statement/reference control "
    "experiment: the original Isabelle proof is not provided. Produce a "
    "plausible sequence of proof-step claims that could guide a later proof "
    "generator. Follow the style of a Draft phase: numbered steps, mostly "
    "formulas or precise mathematical claims, no source code, and no discussion "
    "of prover internals."
)


@dataclass(frozen=True)
class StatementOnlyPrompt:
    system_prompt: str
    user_prompt: str
    prompt_version: str = STATEMENT_ONLY_PROMPT_VERSION
    input_mode: str = INPUT_MODE


def _required_text(record: dict[str, Any], key: str) -> str:
    value = record.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"record is missing required non-empty text field {key!r}")
    return value.strip()


def _fenced(language: str, content: str) -> str:
    return f"```{language}\n{content.rstrip()}\n```"


def proof_masked_isabelle_statement(record: dict[str, Any]) -> str:
    """Extract the target theorem statement from the proof-masked Isabelle file."""
    reference = _required_text(record, "isabelle_reference_context")
    target_name = record.get("isabelle_target_name") or record.get("target_key")
    if not isinstance(target_name, str) or not target_name:
        raise ValueError("record is missing isabelle_target_name/target_key")

    declarations = inventory_isabelle_declarations(
        reference,
        topic=str(record.get("topic", "")),
    )
    for declaration in declarations:
        if declaration.name == target_name:
            start, end = declaration.statement_span
            return reference[start:end].strip()

    available = ", ".join(declaration.name for declaration in declarations)
    raise ValueError(
        f"could not find target {target_name!r} in proof-masked Isabelle reference; "
        f"available declarations: {available}"
    )


def build_statement_only_prompt(record: dict[str, Any]) -> StatementOnlyPrompt:
    """Build the statement-plus-masked-reference control prompt for one V1 record."""
    source = record.get("source", "")
    theorem_id = record.get("theorem_id", "")
    topic = record.get("topic", "")
    target_key = record.get("target_key", "")
    masked_statement = proof_masked_isabelle_statement(record)
    masked_reference = _required_text(record, "isabelle_reference_context")

    sections = [
        "experiment_target:\n"
        f"source: {source}\n"
        f"theorem_id: {theorem_id}\n"
        f"topic: {topic}\n"
        f"target_key: {target_key}\n"
        f"control_input_mode: {INPUT_MODE}",
        "isabelle_statement:\n"
        + _fenced("isabelle", masked_statement),
        "isabelle_reference:\n"
        + _fenced("isabelle", masked_reference),
    ]

    sections.append(
        "Please provide a possible mathematical proof Draft in numbered steps. "
        "The Draft should be useful to a later automated proof-generation stage.\n\n"
        "Important constraints:\n"
        "- Use only the proof-masked Isabelle theorem statement and proof-masked Isabelle reference context above.\n"
        "- Do not use the original Isabelle proof; it is intentionally not provided.\n"
        "- Do not use the oracle Lean statement, Lean header, Lean proof, or any target-language proof.\n"
        "- Use the proof-masked Isabelle reference only for definitions, notation, assumptions, and helper theorem statements. Do not use `sorry` placeholders as proof evidence.\n"
        "- Do not claim that the source proof performed a step unless that step follows from the provided statement or reference context.\n"
        "- Prefer a sequence of explicit formulas, equations, inequalities, quantified propositions, case claims, witnesses, or named helper facts.\n"
        "- Each step should contain one principal mathematical claim. Short explanatory phrases are allowed only when they clarify the claim.\n"
        "- Preserve names of functions, constants, definitions, assumptions, and helper theorems that appear in the provided Isabelle text.\n"
        "- Do not output Isabelle code, Lean code, tactic names, proof commands, automation procedures, or meta-commentary.\n"
        "- The final step should state the target conclusion.\n\n"
        "Here is the required output format:\n"
        "### Step 1:\n"
        "<one formula or precise mathematical claim>\n\n"
        "### Step 2:\n"
        "<one formula or precise mathematical claim>\n\n"
        "Continue until the theorem follows.\n"
    )

    return StatementOnlyPrompt(
        system_prompt=SYSTEM_PROMPT,
        user_prompt="\n\n".join(sections),
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
