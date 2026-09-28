from __future__ import annotations

from eval.pipeline.hol_light_to_isabelle.prompt import Prompt, _required


SKETCH_PROMPT_VERSION = "babel_formal_v2_isabelle_sketch_p1"
SYSTEM_PROMPT = (
    "You are an Isabelle/HOL proof engineer. Produce one proof body for the "
    "specified oracle theorem. Use the mathematical draft and the preceding "
    "proof-masked Isabelle theory context. Preserve the supplied statement "
    "and the proof prefix already present after it. Return only an executable "
    "Isabelle proof body starting with by or proof. Do not output a theory, "
    "theorem declaration, axiom, sorry, or commentary."
)


def build_sketch_prompt(record: dict) -> Prompt:
    draft = _required(record, "draft")
    prefix = record.get("isabelle_proof_prefix") or ""
    user = "\n\n".join([
        f"TARGET: {record['topic']}/{record['isabelle_target_name']}",
        "ISABELLE CONTEXT BEFORE TARGET\n~~~isabelle\n"
        + _required(record, "isabelle_context_before_target") + "\n~~~",
        "ORACLE TARGET STATEMENT\n~~~isabelle\n"
        + _required(record, "isabelle_statement") + "\n~~~",
        "PROOF PREFIX ALREADY IN THEORY\n~~~isabelle\n"
        + (prefix if prefix else "(none)") + "\n~~~",
        "MATHEMATICAL PROOF DRAFT\n~~~text\n" + draft + "\n~~~",
        "Write only the Isabelle proof body replacing the target sorry. "
        "You may use definitions, locale assumptions, and earlier named facts "
        "from the supplied context. Later declarations are unavailable. "
        "If the proof prefix already unfolds or uses facts, continue after it "
        "without repeating it. End a structured proof with qed. Do not use "
        "sorry, oops, admit, ML, axiomatization, or new declarations.",
    ])
    return Prompt(SYSTEM_PROMPT, user, SKETCH_PROMPT_VERSION)
