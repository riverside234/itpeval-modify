from __future__ import annotations

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import Prompt, _required


SKETCH_PROMPT_VERSION = "babel_formal_dsp_isabelle2026_draft_p3"

# Both input modes use the same target, background, and gap contract.
ISABELLE_OUTPUT_RULES = (
    "Construct one Isabelle2026/HOL Isar proof body for the exact oracle declaration "
    "in its supplied theory and locale context. Use standalone sledgehammer commands "
    "for unresolved proof obligations; a later prover will replace each with a "
    "checked proof that closes that obligation. Return only the proof body, starting "
    "with by or proof and ending with qed for a structured proof."
)

ISABELLE_PROOF_REQUIREMENTS = (
    "PROOF REQUIREMENTS\n"
    "- The oracle declaration and preceding Isabelle context are authoritative. "
    "Preserve types, quantifiers, hypotheses, fixed locale parameters, and notation. "
    "Introduce only variables, assumptions, and witnesses justified by the current "
    "goal or a proved fact; do not strengthen assumptions to make the proof work.\n"
    "- The declaration and supplied proof prefix have already been executed. "
    "Continue from that proof state without repeating either. Do not redeclare "
    "locale parameters or close the surrounding theory or locale.\n"
    "- Use definitions and facts available in the preceding context or its imports, "
    "plus local facts you establish. Earlier masked helper statements are usable "
    "background facts; their sorry placeholders are not proof instructions. Do not "
    "cite the target itself or later declarations, or guess a library theorem name. "
    "A source-language name is not automatically an Isabelle fact.\n"
    "- Preserve the argument's useful intermediate claims and dependencies. Name "
    "local facts with have, pass relevant facts with using, and discharge the goal "
    "with show. Retain necessary cases, induction hypotheses, witnesses, substitutions, "
    "and side conditions. Where a needed helper has no available Isabelle counterpart, "
    "state and prove the required instance as a local claim.\n"
    "- Use a concrete proof method when its application is clear. Otherwise put "
    "sledgehammer alone on a line after a complete command that opens a proof "
    "obligation, such as have, show, or obtain, with any needed using facts or "
    "unfolding definitions. It replaces the proof of that obligation; continue "
    "afterward with the remaining Isar commands. Never write by sledgehammer or "
    "supply hammer parameters.\n"
    "- Keep all mathematical claims, bindings, and case structure explicit: search "
    "fills local proof gaps, not missing statements or malformed syntax. Do not "
    "replace a substantive source argument with a single search call on the whole "
    "theorem. A direct by proof is appropriate when it captures the given argument. "
    "There is no length limit or required number of steps.\n"
    "- Close every local goal, case, and target goal with valid Isar structure. "
    "Return only the proof body: no Markdown fences, explanatory prose, repeated "
    "declaration, theory header, global definitions, axioms, ML/setup commands, or "
    "admissions such as sorry, oops, or admit."
)

SYSTEM_PROMPT = (
    "You are an Isabelle/HOL proof engineer. Formalize the supplied mathematical "
    "proof draft, preserving its strategy and necessary intermediate claims. "
    + ISABELLE_OUTPUT_RULES
)


def build_sketch_prompt(record: dict) -> Prompt:
    if record.get("input_error"):
        raise ValueError(record["input_error"])
    draft = _required(record, "informal_proof")
    if draft != _required(record, "draft"):
        raise ValueError("informal_proof must be the saved Draft")
    statement = _required(record, "formal_statement")
    if statement != _required(record, "isabelle_statement"):
        raise ValueError("formal_statement must be the unchanged oracle")
    prefix = record.get("isabelle_proof_prefix") or "(none)"
    user = "\n\n".join([
        f"TARGET: {record['topic']}/{record['isabelle_target_name']}",
        "AVAILABLE ISABELLE CONTEXT BEFORE TARGET\n~~~isabelle\n"
        + _required(record, "isabelle_context_before_target") + "\n~~~",
        "EXACT ORACLE DECLARATION\n~~~isabelle\n" + statement + "\n~~~",
        "PROOF PREFIX ALREADY PRESENT (continue after it; do not repeat)\n~~~isabelle\n"
        + prefix + "\n~~~",
        "MATHEMATICAL PROOF DRAFT\n~~~text\n" + draft + "\n~~~",
        "Use the draft as the mathematical argument to formalize. Check each step "
        "against the exact goal and available facts; the draft is guidance, not an "
        "additional assumption. Repair notation, explicit instantiations, and "
        "missing justifications locally while preserving the argument. If the draft "
        "names a source-only helper, establish its needed mathematical instance "
        "instead of copying the name into Isabelle.",
        ISABELLE_PROOF_REQUIREMENTS,
    ])
    return Prompt(SYSTEM_PROMPT, user, SKETCH_PROMPT_VERSION)
