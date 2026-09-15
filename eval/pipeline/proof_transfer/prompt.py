from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any


DRAFT_PROMPT_VERSION = "babel_formal_v1_isabelle_to_draft_2026_09_15_p6"

SYSTEM_PROMPT = (
    "You are an expert mathematician and formal theorem prover, fluent in "
    "Isabelle/HOL and Lean 4. Convert only the specified Isabelle target proof "
    "into a mathematical proof Draft that will be used by a later automated "
    "proof-generation stage. The Draft should help a downstream Lean 4 prover "
    "reconstruct the proof in a different formal language. Follow the source "
    "proof strategy, preserve all mathematically important intermediate "
    "claims, and translate prover-specific tactics, rewrites, automation, and "
    "local facts into the mathematical facts they establish. Use the "
    "proof-masked Isabelle reference theory to understand the source proof and "
    "the proof-masked Lean 4 context to translate source notation into exact "
    "target-side identifiers. When an equivalent Lean declaration is present, "
    "use its exact name and expression vocabulary in the Draft. Write formulas "
    "as plain Lean-like expressions inside Markdown prose, not as LaTeX. Do not "
    "invent a different proof, translate unrelated theorems, emit Lean proof "
    "code, or treat sorry placeholders as proof content. Return only the final "
    "Draft using numbered Markdown proof-step headings."
)


@dataclass(frozen=True)
class DraftPrompt:
    system_prompt: str
    user_prompt: str
    prompt_version: str = DRAFT_PROMPT_VERSION


def _required_text(record: dict[str, Any], key: str) -> str:
    value = record.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"record is missing required non-empty text field {key!r}")
    return value.strip()


def _optional_text(record: dict[str, Any], key: str) -> str:
    value = record.get(key, "")
    if value is None:
        return ""
    if not isinstance(value, str):
        raise ValueError(f"record field {key!r} must be a string if present")
    return value.strip()


def _fenced(language: str, content: str) -> str:
    return f"```{language}\n{content.rstrip()}\n```"


def build_draft_prompt(record: dict[str, Any]) -> DraftPrompt:
    """Build the Isabelle-proof-to-Draft prompt for one parsed V1 record."""
    source = record.get("source", "")
    theorem_id = record.get("theorem_id", "")
    topic = record.get("topic", "")
    target_key = record.get("target_key", "")
    context_mode = record.get("context_mode", "")

    lean4_statement = _required_text(record, "lean4_statement")
    lean4_header = _required_text(record, "lean4_header")

    user_prompt = "\n\n".join(
        [
            "EXPERIMENT TARGET\n"
            f"source: {source}\n"
            f"theorem_id: {theorem_id}\n"
            f"topic: {topic}\n"
            f"target_key: {target_key}\n"
            f"context_mode: {context_mode}",
            "ORACLE LEAN4 TARGET STATEMENT (proof masked; use only as the "
            "target conclusion)\n"
            + _fenced("lean4", lean4_statement),
            "PROOF-MASKED LEAN4 CONTEXT (use only for exact target-side "
            "declaration names, notation, types, and helper-fact statements)\n"
            + _fenced("lean4", lean4_header),
            "TARGET ISABELLE THEOREM STATEMENT\n"
            + _fenced("isabelle", _required_text(record, "isabelle_statement")),
            "TARGET ISABELLE PROOF TO TRANSLATE\n"
            + _fenced("isabelle", _required_text(record, "isabelle_proof")),
            "PROOF-MASKED REFERENCE ISABELLE FILE\n"
            + _fenced("isabelle", _required_text(record, "isabelle_reference_context")),
            "DRAFT REQUIREMENTS\n"
            "- Translate only the target Isabelle proof body.\n"
            "- Read the whole target statement, target proof, oracle Lean4 "
            "statement, proof-masked Lean4 context, and Isabelle reference "
            "context before writing the Draft.\n"
            "- Use the proof-masked reference file only for definitions, notation, "
            "assumptions, and helper facts needed by the target proof.\n"
            "- Use the proof-masked Lean4 context as a vocabulary map for the "
            "target language, not as proof evidence.\n"
            "- Do not use sorry placeholders as evidence.\n"
            "- Follow the same proof strategy and order as the source proof.\n"
            "- If the source proof unfolds definitions, state the unfolded equation "
            "and use the exact corresponding definition names from the Lean4 "
            "context when available. An Isabelle name such as `foo_def` often "
            "corresponds to the Lean definition `foo`; do not retain `_def` unless "
            "that exact declaration exists in the Lean4 context.\n"
            "- If the source proof applies a named theorem, lemma, or assumption, "
            "state the exact corresponding Lean4 name when available and the "
            "mathematical fact being applied.\n"
            "- Preserve the names of definitions, assumptions, and helper theorems "
            "that are actually used, together with the mathematical claim each "
            "one contributes.\n"
            "- Preserve variable names, hypotheses, case assumptions, induction "
            "hypotheses, contradiction assumptions, auxiliary variables, and "
            "witnesses when they are mathematically necessary.\n"
            "- Replace Isabelle tactics and proof commands with their mathematical "
            "consequences.\n"
            "- Prefer explicit formulas, equations, inequalities, quantified "
            "propositions, set relations, implications, or witnesses. Write them "
            "in plain Lean-like notation whenever the Lean4 context provides the "
            "needed vocabulary.\n"
            "- Translate Isabelle-only syntax and notation into the corresponding "
            "Lean-like expression. For example, translate `\\<lambda>theta. ...` "
            "to `fun theta => ...`, and translate source-only `theta +C c` to "
            "`AddMonoid.add theta c` when that is the operation declared in the "
            "Lean4 context.\n"
            "- Use inline backticks around identifiers and formulas. Do not use "
            "LaTeX commands, display-math delimiters, HTML escapes, trailing "
            "backslashes, or invented notation.\n"
            "- Avoid renaming functions, constants, hypotheses, or helper facts "
            "when their original names appear in the target statement or "
            "reference context.\n"
            "- Keep each step focused on one principal mathematical claim or one "
            "named proof move.\n"
            "- Omit routine syntactic operations, but do not omit intermediate "
            "facts needed to reconstruct the argument.\n"
            "- If the proof is short, output only the necessary steps. If the "
            "proof is long, include all important intermediate claims that "
            "would help reconstruct the proof.\n"
            "- Make the Draft self-contained enough for a later proof generator "
            "to follow without seeing the original Isabelle proof.\n"
            "- The final step must establish the Lean4 target conclusion.\n"
            "- Do not reproduce Isabelle tactic syntax, proof-command syntax, "
            "automation procedures, source-prover implementation details, hidden "
            "reasoning, or meta-commentary. Describe the mathematical effect of "
            "each source proof move instead.\n"
            "- Do not include code fences, a complete Lean theorem, or tactic-mode "
            "proof code in the Draft.\n"
            "- Output only proof-draft steps in this Markdown format:\n"
            "### Step 1\n"
            "<one proof move followed by its Lean-like formula or precise claim>\n\n"
            "### Step 2\n"
            "<one proof move followed by its Lean-like formula or precise claim>\n\n"
            "FORMAT EXAMPLE (illustrative only; do not copy its theorem-specific "
            "content into other problems):\n"
            "### Step 1\n"
            "Unfold `circleAverage` and `circleMap`. The goal becomes "
            "`integral (fun theta => f (AddMonoid.add theta c)) = integral f`.\n\n"
            "### Step 2\n"
            "Apply `integral_shift f c`, whose conclusion is exactly the current "
            "goal. Therefore, `circleAverage f c = integral f`.",
        ]
    )

    return DraftPrompt(system_prompt=SYSTEM_PROMPT, user_prompt=user_prompt)


_THINK_RE = re.compile(r"<think\b[^>]*>.*?</think>", re.IGNORECASE | re.DOTALL)
_FENCE_RE = re.compile(r"\A```(?:[A-Za-z0-9_+-]+)?\s*\n(?P<body>.*)\n```\s*\Z", re.DOTALL)


def normalize_draft_content(content: str) -> str:
    """Strip accidental wrappers while preserving only visible final text."""
    content = _THINK_RE.sub("", content).strip()
    match = _FENCE_RE.match(content)
    if match:
        content = match.group("body").strip()
    return content
