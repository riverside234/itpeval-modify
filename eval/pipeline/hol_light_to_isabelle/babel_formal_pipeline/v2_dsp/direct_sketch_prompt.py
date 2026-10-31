"""Translate one completed HOL Light proof directly into an Isabelle2026 sketch."""
from ..prompt import Prompt
from .input_contract import input_metadata, require_text

DIRECT_PROMPT_VERSION = "babel_formal_dsp_isabelle2026_direct_p1"
SYSTEM_PROMPT = (
    "You are a HOL Light and Isabelle/HOL proof engineer. Translate the selected completed "
    "HOL Light proof directly into one Isabelle2026 Isar proof body for the exact oracle "
    "declaration in its original theory/locale context. Preserve the source strategy and "
    "necessary intermediate claims, cases, witnesses and induction hypotheses. The source "
    "reference contains only definitions and proof-masked helper statements. Source theorem "
    "names need not exist in Isabelle: use the supplied target vocabulary and available facts. "
    "Return only the proof body, starting with by or proof. Use standalone sledgehammer "
    "commands for unresolved obligations; a native prover will replace each with a checked "
    "proof. Never output a mathematical draft, theory header, repeated declaration, "
    "commentary, admissions, new axioms, ML, setup commands or hidden reasoning."
)


def build_direct_sketch_prompt(record: dict) -> Prompt:
    input_metadata(record, "hol-light-proof")
    def section(title, field):
        return title + "\n~~~\n" + require_text(record, field) + "\n~~~"
    user = "\n\n".join([
        "TARGET: " + record["topic"] + "/" + record["isabelle_target_name"],
        section("AVAILABLE ISABELLE CONTEXT BEFORE TARGET", "isabelle_context_before_target"),
        section("EXACT ORACLE ISABELLE DECLARATION", "isabelle_statement"),
        "PROOF PREFIX ALREADY PRESENT (continue after it; do not repeat)\n~~~\n"
        + (record.get("isabelle_proof_prefix") or "(none)") + "\n~~~",
        section("SELECTED HOL LIGHT STATEMENT", "hol_light_statement"),
        section("SELECTED COMPLETED HOL LIGHT PROOF TO TRANSLATE", "hol_light_proof"),
        section("COMPLETE PROOF-MASKED HOL LIGHT REFERENCE", "hol_light_reference_context"),
        "Follow only the selected proof. Use the reference only for relevant definitions and "
        "helper statements. Treat the oracle statement, fixed locale parameters, notation and "
        "hypotheses as authoritative. Express useful intermediate claims using have/show. "
        "Do not assume source tactic or helper names exist in Isabelle. Do not cite later "
        "target declarations. For an unresolved pending obligation put sledgehammer on its "
        "own line, with no parameters; never write by sledgehammer. Structured proofs must "
        "finish with qed. Never use sorry, oops, admit, normalhammer, executable ML or extra "
        "axioms. Include all useful reasoning; there is no brevity constraint. Return only "
        "the target Isar proof body.",
    ])
    return Prompt(SYSTEM_PROMPT, user, DIRECT_PROMPT_VERSION)
