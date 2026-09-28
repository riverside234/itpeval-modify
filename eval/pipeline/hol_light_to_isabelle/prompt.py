from __future__ import annotations

import re
from dataclasses import dataclass


DRAFT_PROMPT_VERSION = "babel_formal_v2_hol_light_to_isabelle_p1"

SYSTEM_PROMPT = (
    "You are an expert mathematician fluent in HOL Light and Isabelle/HOL. "
    "Convert only the selected HOL Light proof into a mathematical proof draft "
    "for a later Isabelle/HOL proof generator. Follow the source proof strategy "
    "and preserve important intermediate claims. Use the proof-masked HOL Light "
    "file for source definitions and facts, and the proof-masked Isabelle context "
    "for exact target names, locale assumptions, and notation. Return numbered "
    "mathematical proof steps only. Do not output HOL Light tactics, Isabelle "
    "proof code, a complete theorem, or hidden reasoning."
)


@dataclass(frozen=True)
class Prompt:
    system_prompt: str
    user_prompt: str
    version: str


def _required(record: dict, name: str) -> str:
    value = record.get(name)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"missing nonempty {name}")
    return value.strip()


def _section(title: str, content: str) -> str:
    return f"{title}\n~~~\n{content}\n~~~"


def build_draft_prompt(record: dict) -> Prompt:
    prefix = record.get("isabelle_proof_prefix") or ""
    user = "\n\n".join([
        f"TARGET: Babel Formal topic {record['topic']}, theorem {record['target_key']}.",
        _section("ORACLE ISABELLE TARGET STATEMENT (conclusion only)",
                 _required(record, "isabelle_statement")),
        _section("PROOF-MASKED ISABELLE CONTEXT BEFORE TARGET",
                 _required(record, "isabelle_context_before_target")),
        _section("ISABELLE TARGET PROOF PREFIX (preserve if present)",
                 prefix if prefix else "(none)"),
        _section("HOL LIGHT TARGET STATEMENT",
                 _required(record, "hol_light_statement")),
        _section("HOL LIGHT TARGET PROOF TO TRANSLATE",
                 _required(record, "hol_light_proof")),
        _section("COMPLETE PROOF-MASKED HOL LIGHT REFERENCE FILE",
                 _required(record, "hol_light_reference_context")),
        "DRAFT REQUIREMENTS\n"
        "- Read the entire selected proof before writing the draft. Translate only "
        "that proof; the other theorems in the reference file supply definitions "
        "and helper statements, not proof bodies.\n"
        "- Follow the source strategy and order. State the mathematical effect of "
        "quantifier introduction, assumptions, conjunct extraction, rewriting, "
        "instantiation, witnesses, case splits, and induction.\n"
        "- If the source uses REPEAT GEN_TAC or DISCH_THEN, identify the introduced "
        "variables and assumptions. If it selects a conjunct through CONJUNCT1, "
        "CONJUNCT2, CONJUNCTS, or List.nth, state that conjunct. If it uses "
        "REWRITE_TAC, MATCH_MP_TAC, SPEC/SPECL, EXISTS_TAC, or ACCEPT_TAC, "
        "state the resulting claim rather than only naming the tactic.\n"
        "- HOL Light may pass operations as explicit parameters while Isabelle "
        "fixes them in a locale. Treat the oracle Isabelle statement and locale "
        "as authoritative; use their variable names, notation, and assumptions.\n"
        "- Use exact Isabelle helper and definition names when present in the "
        "target context. For source-only helpers, such as dest_integral, state "
        "the extracted mathematical fact instead of inventing an Isabelle name.\n"
        "- State the useful instantiated equations and hypotheses explicitly. "
        "Do not invent a different proof or cite later target theorems.\n"
        "- Treat every sorry placeholder as unavailable proof evidence.\n"
        "- Do not force brevity; include all intermediate facts useful to the "
        "later proof generator and omit routine syntax-only moves.\n"
        "- Use plain inline identifiers and formulas, not LaTeX commands, "
        "display math, HTML escapes, or invented Isabelle notation.\n"
        "- Do not output executable Isabelle proof commands or source-language "
        "tactic code. End by establishing the oracle Isabelle conclusion.\n"
        "- Output only sections headed ### Step 1, ### Step 2, and so on.",
    ])
    return Prompt(SYSTEM_PROMPT, user, DRAFT_PROMPT_VERSION)


_THINK = re.compile(r"<think\b[^>]*>.*?</think>", re.I | re.S)
_FENCE = re.compile(r"\A(?:~~~|\x60{3})[^\n]*\n(?P<body>.*)\n(?:~~~|\x60{3})\s*\Z", re.S)


def normalize_visible_content(content: str) -> str:
    value = _THINK.sub("", content).strip()
    match = _FENCE.match(value)
    return match.group("body").strip() if match else value
