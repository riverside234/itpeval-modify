from __future__ import annotations

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import Prompt, _required


SKETCH_PROMPT_VERSION = "babel_formal_dsp_isabelle2026_draft_p2"
SYSTEM_PROMPT = (
    "You are an Isabelle2026/HOL proof engineer. Turn the supplied mathematical proof "
    "draft into one Isar proof body of the exact oracle theorem in its original "
    "theory and locale context. Follow the draft's strategy and state useful "
    "intermediate claims explicitly. Use direct proof methods where known. For "
    "a remaining proof obligation, use a standalone sledgehammer command; a later "
    "automated prover will replace it with a checked proof method. Return only "
    "the proof body, starting with by or proof. Do not output a theory header, "
    "theorem declaration, new axiom, sorry, or commentary."
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
        "Write only the target proof body. Preserve the conclusion, locale "
        "parameters, hypotheses, and names from the available context. Follow "
        "the draft, including required cases, induction hypotheses, witnesses, "
        "and equations. Check every cited fact against this context. Do not "
        "invent theorem names or use later declarations. Use have/show for "
        "intermediate claims. End structured proofs with qed. A sledgehammer "
        "command closes a pending proof obligation; do not write by sledgehammer "
        "or add hammer parameters. Never use sorry, oops, admit, normalhammer, "
        "ML, axiomatization, or Lean prove_with placeholders. Include all "
        "mathematically useful steps; there is no brevity constraint.",
    ])
    return Prompt(SYSTEM_PROMPT, user, SKETCH_PROMPT_VERSION)
