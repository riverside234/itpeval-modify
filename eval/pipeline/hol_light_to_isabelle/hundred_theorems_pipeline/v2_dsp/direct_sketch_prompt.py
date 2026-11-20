"""Direct HOL Light proof to Isabelle2026 Sketch for Hundred Theorems."""
from ...babel_formal_pipeline.prompt import Prompt
from ...babel_formal_pipeline.v2_dsp.direct_sketch_prompt import build_direct_sketch_prompt as _build
from ...context_helpers.prompts import direct_prompt_version
from ..common import SOURCE, require_source

DIRECT_PROMPT_VERSION = "hundred_theorems_dsp_isabelle2026_direct_p10"


def build_direct_sketch_prompt(record: dict) -> Prompt:
    require_source([record], SOURCE)
    prompt = _build(record)
    return Prompt(prompt.system_prompt, prompt.user_prompt, direct_prompt_version(record, DIRECT_PROMPT_VERSION))
