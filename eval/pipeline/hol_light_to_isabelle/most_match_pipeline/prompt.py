"""Mathematical Draft using only the saved, bounded reference selections."""
from ..babel_formal_pipeline.prompt import Prompt, build_draft_prompt as _build
from .context import validate_prompt_context

DRAFT_PROMPT_VERSION = "most_match_draft_v1"
CONTEXT_NOTE = (
    "REFERENCE SCOPE: The references are selected excerpts, not a complete library or theory. "
    "They contain earlier helper statements and relevant definitions; proofs are masked. "
    "The Isabelle verifier retains the full preceding theory context and its original imports. "
    "Only the displayed active-scope assumptions and the oracle hypotheses are assumptions "
    "for this goal. An omitted fact is not thereby false, but do not invent its statement "
    "or name. If a source helper has no justified target counterpart, state the needed "
    "mathematical obligation explicitly. The selected target is never an available premise."
)


def build_draft_prompt(record):
    validate_prompt_context(record)
    prompt = _build(record, dataset_label="HOL most-match", version=DRAFT_PROMPT_VERSION,
                    isabelle_context=record["isabelle_prompt_context"], partial_context=True)
    return Prompt(prompt.system_prompt, prompt.user_prompt + "\n\n" + CONTEXT_NOTE, DRAFT_PROMPT_VERSION)
