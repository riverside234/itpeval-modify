"""Use the identical Isabelle v2_dsp prompt contract for this dataset."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import Prompt
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.sketch_prompt import SYSTEM_PROMPT, build_sketch_prompt as _build
from ..common import SOURCE, require_source

SKETCH_PROMPT_VERSION = "hundred_theorems_dsp_isabelle2026_draft_p2"


def build_sketch_prompt(record: dict) -> Prompt:
    require_source([record], SOURCE)
    prompt = _build(record)
    return Prompt(prompt.system_prompt, prompt.user_prompt, SKETCH_PROMPT_VERSION)
