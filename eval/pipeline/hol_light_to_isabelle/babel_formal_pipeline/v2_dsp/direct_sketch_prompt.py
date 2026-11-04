"""Translate one completed HOL Light proof directly into an Isabelle2026 sketch."""
from ..prompt import Prompt
from .input_contract import input_metadata, require_text
from .sketch_prompt import ISABELLE_OUTPUT_RULES, ISABELLE_PROOF_REQUIREMENTS

DIRECT_PROMPT_VERSION = "babel_formal_dsp_isabelle2026_direct_p9"
SYSTEM_PROMPT = (
    "You are a proof engineer fluent in HOL Light and Isabelle/HOL. Translate the "
    "selected completed HOL Light proof directly into an Isabelle proof, preserving "
    "its mathematical strategy and necessary intermediate facts. Translate the "
    "mathematical effect of source proof operations into target claims and "
    "justifications. " + ISABELLE_OUTPUT_RULES + " Do not output an informal draft "
    "or commentary about the translation."
)


DIRECT_PROOF_STATE_RULES = (
    "TARGET PROOF STATE AND INDUCTION\n"
    "- Follow the HOL Light argument in Isabelle's current proof state. Distinguish "
    "meta-implication (\\<Longrightarrow>) from object implication (\\<longrightarrow>): "
    "impI introduces only an object implication. A goal whose conclusion is an "
    "existential needs a witness, not impI. Do not repeat introductions that "
    "induction, case, or a previous proof method has already performed.\n"
    "- For induction, keep dependent hypotheses generalized until applying the "
    "induction rule. Supply them with using or appropriate arbitrary variables. "
    "After each case command, use its actual induction hypotheses and premises "
    "(such as case_name.IH and case_name.prems when generated). Do not assume "
    "that ?case still contains the implication written before induction. Pass "
    "the case premises to the base/step proof explicitly when needed.\n"
    "- A bare proof applies a default introduction rule and can change the goal. "
    "Use proof - to organize a case without applying such a rule; use "
    "proof (rule ...) only for an intended rule application. Do not put a new "
    "assume block around a premise already available from case.\n"
    "- For an existential conclusion, give the source argument's witness explicitly "
    "with rule exI[where x=...] or establish the witness's properties before the "
    "final show. Obtain witnesses from an established existential or membership "
    "fact; do not transfer HOL Light choice/tactic syntax literally. For finite-set "
    "induction, track the base witness, the inserted element, the smaller set, "
    "the induction witness, and each required finiteness/subset/coverage condition.\n"
    "- Avoid speculative method chains such as intro followed by several rules "
    "when the current outer connective is uncertain. Prefer a small, well-typed "
    "local claim with its relevant case facts and a standalone sledgehammer gap. "
    "Search cannot correct an ill-typed claim, missing case premise, or invalid "
    "proof-block structure. Do not invent case fact names or add assumptions.\n"
    "- Before returning the proof body, check the scope of each variable and fact, "
    "the current goal at each show, the witness at each existential, and the "
    "matching proof/qed blocks. Return only the Isabelle proof body."
)


DIRECT_HELPER_RULES = (
    "HELPER APPLICATIONS AND REPRESENTATION MATCHING\n"
    "- Read each available helper's actual Isabelle statement before applying it. "
    "Match its quantified variables, types, premises and conclusion to the "
    "current step. Use a direct rule application with explicitly instantiated "
    "premises when it already proves the claim; do not hand a general "
    "higher-order rule and large set expressions to blast to discover the "
    "instantiation. For a helper mono with premises U \\<subseteq> V and P V, "
    "and matching facts sub and pV, the schematic pattern is "
    "by (rule mono[OF sub pV]). Use actual available names and matching types.\n"
    "- Reuse one local abbreviation for each set, function or interpretation. "
    "Keep comprehension binder order and conjunct order consistent with the "
    "helper being used. Equivalent expressions are not necessarily syntactically "
    "identical: changing bound-variable order or swapping conjuncts inside a "
    "set argument may block an otherwise direct rule application.\n"
    "- If two set representations differ, prove their equality or the required "
    "inclusion separately, then rewrite the argument of the surrounding "
    "predicate with that fact. For instance, establish A = B before transferring "
    "R A to R B. Use a small membership/extensionality argument or targeted "
    "simplification for this bridge. blast alone does not rewrite arbitrary "
    "opaque predicates by extensional equality of their set arguments. "
    "Avoid unfolding a substantial semantic predicate just to change its set "
    "argument; first normalize or rewrite that argument.\n"
    "- Before invoking a substantial library theorem, enumerate every premise "
    "in its supplied target signature. Source and target versions can have "
    "different side conditions. Establish them for the exact transformed object "
    "at the scope where the theorem is applied. For example, a property known "
    "for each finite subset is not automatically an available fact about the "
    "whole set; prove any required closure under substitutions, images or "
    "transformations separately. Do not leave a required well-formedness or "
    "quantifier-free condition implicit.\n"
    "- Use the imported helper's displayed signature to prove the concrete "
    "next goal, supplying established premises explicitly. Avoid manufacturing "
    "a more general implication and asking search to rediscover a substantial "
    "compactness, completeness, induction or existence theorem. If an "
    "imported helper needs additional premises, prove them before invoking it; "
    "an opaque search gap is not a replacement for that dependency.\n"
    "- Treat a source helper as a dependency, not a tactic to copy. Establish "
    "only the needed mathematical instance if no supplied Isabelle helper "
    "matches it. Keep this local claim narrowly scoped and supply its relevant "
    "facts to a standalone sledgehammer gap. Do not guess imported theorem "
    "names, and do not strengthen a local statement merely to imitate the "
    "source helper's generality.\n"
    "- For an obtains declaration, construct a witness and all required "
    "properties, then discharge the resulting thesis with the provided "
    "elimination premise (usually that). Choosing a member of a set needs "
    "nonemptiness; handle an empty-set case when the available helper requires "
    "a member. For subset or monotonicity steps, normalize both set arguments "
    "before applying the helper, instead of repeatedly invoking broad automation."
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
        DIRECT_PROOF_STATE_RULES,
        DIRECT_HELPER_RULES,
    ])
    return Prompt(SYSTEM_PROMPT, user, DIRECT_PROMPT_VERSION)
