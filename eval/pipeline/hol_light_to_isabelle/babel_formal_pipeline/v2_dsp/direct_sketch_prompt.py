"""Translate one completed HOL Light proof directly into an Isabelle2026 sketch."""
from ..prompt import Prompt
from .input_contract import input_metadata, require_text
from .sketch_prompt import ISABELLE_OUTPUT_RULES, ISABELLE_PROOF_REQUIREMENTS

DIRECT_PROMPT_VERSION = "babel_formal_dsp_isabelle2026_direct_p5"
SYSTEM_PROMPT = (
    "You are a proof engineer fluent in HOL Light and Isabelle/HOL. Translate the "
    "selected completed HOL Light proof directly into an Isabelle proof, preserving "
    "its mathematical strategy and necessary intermediate facts. Translate the "
    "mathematical effect of source proof operations into target claims and "
    "justifications. " + ISABELLE_OUTPUT_RULES + " Do not output an informal draft "
    "or commentary about the translation."
)


def build_direct_sketch_prompt(record: dict, *, isabelle_context: str | None = None,
                               partial_context: bool = False) -> Prompt:
    input_metadata(record, "hol-light-proof")

    def section(title, field):
        return title + "\n~~~\n" + require_text(record, field) + "\n~~~"

    user = "\n\n".join([
        "TARGET: " + record["topic"] + "/" + record["isabelle_target_name"],
        "AVAILABLE ISABELLE CONTEXT BEFORE TARGET\n~~~\n"
        + (isabelle_context if isabelle_context is not None else require_text(record, "isabelle_context_before_target")) + "\n~~~",
        section("EXACT ORACLE ISABELLE DECLARATION", "isabelle_statement"),
        "PROOF PREFIX ALREADY PRESENT (continue after it; do not repeat)\n~~~\n"
        + (record.get("isabelle_proof_prefix") or "(none)") + "\n~~~",
        section("SELECTED HOL LIGHT STATEMENT", "hol_light_statement"),
        section("SELECTED COMPLETED HOL LIGHT PROOF TO TRANSLATE", "hol_light_proof"),
        section("RETRIEVED PROOF-MASKED HOL LIGHT REFERENCES" if partial_context else "COMPLETE PROOF-MASKED HOL LIGHT REFERENCE", "hol_light_reference_context"),
        "TRANSLATION REQUIREMENTS\n"
        "- Translate only the selected proof. Use the masked source reference for "
        "relevant definitions and helper statements, not as additional proof bodies. "
        "Its masked copy of the selected theorem is not a premise.\n"
        "- Align source and target objects by their mathematical meaning, not just "
        "their names. Map explicit HOL Light parameters to the corresponding "
        "Isabelle locale parameters and account for any representation differences "
        "using the supplied definitions and assumptions.\n"
        "- Turn introductions, conjunct selection, rewrites, and helper applications "
        "into the actual instantiated claims and subgoals. Preserve the source "
        "argument's logical dependencies rather than transcribing tactic names. "
        "For source automation, expose the claim and supporting facts without "
        "inventing its internal derivation.\n"
        "- Justify each helper application with the required premises. When a "
        "source-only helper is needed, formulate its mathematical instance in the "
        "target vocabulary and establish it locally; do not assume a theorem with "
        "the same name exists in Isabelle.",
        ISABELLE_PROOF_REQUIREMENTS,
    ])
    return Prompt(SYSTEM_PROMPT, user, DIRECT_PROMPT_VERSION)
