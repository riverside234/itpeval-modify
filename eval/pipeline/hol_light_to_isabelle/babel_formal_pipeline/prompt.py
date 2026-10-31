from __future__ import annotations

import re
from dataclasses import dataclass


DRAFT_PROMPT_VERSION = "babel_formal_v2_hol_light_to_isabelle_p3"

SYSTEM_PROMPT = (
    "You are a mathematician fluent in HOL Light and Isabelle/HOL. Convert the "
    "selected completed HOL Light proof into a mathematical proof draft that another "
    "system can formalize in Isabelle/HOL without seeing the source proof. Preserve "
    "the source argument and its necessary intermediate facts, expressed using the "
    "exact target declaration's vocabulary and assumptions. Return only numbered "
    "mathematical proof steps, each containing an explicit claim and a justification "
    "that identifies its premises and dependencies. "
    "Output the proof itself, without formal proof code or commentary about the "
    "translation process."
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


def build_draft_prompt(record: dict, *, dataset_label: str = "Babel Formal",
                       version: str = DRAFT_PROMPT_VERSION) -> Prompt:
    prefix = record.get("isabelle_proof_prefix") or ""
    user = "\n\n".join([
        f"TARGET: {dataset_label} topic {record['topic']}, theorem {record['target_key']}.",
        _section("EXACT ORACLE ISABELLE DECLARATION (goal and hypotheses)",
                 _required(record, "isabelle_statement")),
        _section("PROOF-MASKED ISABELLE CONTEXT BEFORE TARGET",
                 _required(record, "isabelle_context_before_target")),
        _section("ISABELLE PROOF PREFIX ALREADY PRESENT (if any)",
                 prefix if prefix else "(none)"),
        _section("HOL LIGHT TARGET STATEMENT",
                 _required(record, "hol_light_statement")),
        _section("HOL LIGHT TARGET PROOF TO TRANSLATE",
                 _required(record, "hol_light_proof")),
        _section("COMPLETE PROOF-MASKED HOL LIGHT REFERENCE FILE",
                 _required(record, "hol_light_reference_context")),
        "DRAFT REQUIREMENTS\n"
        "- Translate only the selected proof. Use the full proof-masked source file "
        "to interpret relevant definitions and helper statements. Its masked copy "
        "of the selected theorem is the goal, not a premise.\n"
        "- The exact Isabelle declaration and preceding context determine the goal, "
        "types, quantifiers, fixed parameters, assumptions, and notation. Account "
        "for any supplied proof prefix. Do not add assumptions, weaken the conclusion, "
        "or treat the theorem's own name as an available fact.\n"
        "- Match source and target objects by mathematical meaning. HOL Light may "
        "pass operations explicitly where Isabelle fixes them in a locale. Explain "
        "any necessary change of representation or definition unfolding; matching "
        "names alone do not establish equivalence. Use target variable names where "
        "they express the same objects, and make other substitutions explicit.\n"
        "- Preserve the source strategy, logical dependencies, case splits, induction "
        "variable and hypotheses, contradiction assumptions, witnesses, and useful "
        "intermediate equations. Omit bookkeeping that has no mathematical effect. "
        "Introduce each auxiliary variable with its type or domain and role before "
        "using it. Keep case assumptions and induction hypotheses within their "
        "scope, and explain when the cases recombine or a local assumption is "
        "discharged.\n"
        "- When the source selects a conjunct, rewrites a term, or instantiates a "
        "helper, state the actual clause or resulting formula and the substitution "
        "used. Give the premises that make each application valid, including relevant "
        "side conditions, domains, bounds, and nonzero or positivity requirements.\n"
        "- Each step should give one principal mathematical claim and explain why "
        "it follows from definitions, assumptions, earlier steps, or an applicable "
        "helper fact. Distinguish supplied assumptions and available helper facts "
        "from intermediate claims established in this proof. Refer to earlier step "
        "numbers when using their results; a claim introduced in a later step "
        "cannot justify the current one. A helper's name alone is insufficient: "
        "state the instance used. "
        "For source automation, describe the established claim and supporting facts "
        "without inventing an internal derivation or narrating tactic calls.\n"
        "- When using a definition, give the defining equation and show the "
        "expression before and after substitution in target notation. Distinguish "
        "the defined constant from the equation or theorem that justifies rewriting "
        "it. Cite an exact defining-fact name only when supported by the supplied "
        "context; do not invent one from a source-language name.\n"
        "- Cite exact Isabelle helper names only when their statements support the "
        "application. For a source-only helper, state the needed mathematical fact "
        "and how it relates to the target definitions or assumptions, without "
        "inventing an Isabelle counterpart or a missing helper proof. Earlier "
        "masked Isabelle helper statements are available background facts; their "
        "sorry placeholders provide no proof details. Do not cite later target facts. "
        "If a necessary supporting fact cannot be justified from the supplied "
        "material, identify that precise mathematical obligation in the relevant "
        "justification instead of presenting it as an available theorem.\n"
        "- Do not force brevity or a fixed number of steps. Include the facts and "
        "justifications needed to reconstruct this argument; a short source proof "
        "does not need artificial intermediate steps or an alternative strategy.\n"
        "- Use readable mathematical prose and inline formulas with the supplied "
        "identifiers and notation. Do not use LaTeX commands, display math, HTML "
        "escapes, invented notation, tactic transcripts, or executable proof code. "
        "Describe mathematical operations and their results rather than telling "
        "the next system which proof commands or tactic blocks to write.\n"
        "- Output only sections headed ### Step 1, ### Step 2, and so on. Within "
        "each step write Claim: followed by one mathematical assertion, then "
        "Justification: followed by its supporting definitions, assumptions, "
        "instantiated facts, or earlier step numbers. Both parts are mathematical "
        "prose with inline formulas, not formal proof syntax. The final step must "
        "derive the exact oracle conclusion from the preceding argument.",
    ])
    return Prompt(SYSTEM_PROMPT, user, version)


_THINK = re.compile(r"<think\b[^>]*>.*?</think>", re.I | re.S)
_FENCE = re.compile(r"\A(?:~~~|\x60{3})[^\n]*\n(?P<body>.*)\n(?:~~~|\x60{3})\s*\Z", re.S)


def normalize_visible_content(content: str) -> str:
    value = _THINK.sub("", content).strip()
    match = _FENCE.match(value)
    return match.group("body").strip() if match else value
