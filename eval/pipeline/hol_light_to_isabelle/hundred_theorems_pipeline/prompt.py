"""The same translation Draft contract, identified for Hundred Theorems."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.prompt import (
    Prompt, SYSTEM_PROMPT, normalize_visible_content, build_draft_prompt as _build,
)
from .common import SOURCE, require_source

DRAFT_PROMPT_VERSION = "hundred_theorems_v2_hol_light_to_isabelle_p1"


def build_draft_prompt(record: dict) -> Prompt:
    require_source([record], SOURCE)
    return _build(record, dataset_label="Hundred Theorems", version=DRAFT_PROMPT_VERSION)
