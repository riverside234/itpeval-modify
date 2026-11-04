"""Bounded-reference most-match build_direct_sketch_prompt adapter."""
from ...babel_formal_pipeline.v2_dsp.direct_sketch_prompt import build_direct_sketch_prompt as _build
from ...babel_formal_pipeline.prompt import Prompt
from ..context import validate_prompt_context
from ..prompt import CONTEXT_NOTE

DIRECT_PROMPT_VERSION = "most_match_direct_sketch_v6"


def build_direct_sketch_prompt(record):
    validate_prompt_context(record)
    prompt = _build(record, isabelle_context=record["isabelle_prompt_context"], partial_context=True)
    return Prompt(prompt.system_prompt, prompt.user_prompt + "\n\n" + CONTEXT_NOTE, DIRECT_PROMPT_VERSION)
