"""Generate Hundred Theorems Drafts with the shared model/content contract."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline import generate_draft as _engine
from .common import RESULTS_DIR, SOURCE
from .extract_hol_light import DEFAULT_OUTPUT as DEFAULT_INPUT
from .prompt import DRAFT_PROMPT_VERSION, build_draft_prompt

DEFAULT_OUTPUT = RESULTS_DIR + "/hundred_theorems_v2_drafts.jsonl"


def generate_drafts(*, input_path: str = DEFAULT_INPUT, output_path: str | None = None, **options) -> int:
    return _engine.generate_drafts(
        input_path=input_path, output_path=output_path,
        prompt_builder=build_draft_prompt, prompt_version=DRAFT_PROMPT_VERSION,
        expected_source=SOURCE, default_output=DEFAULT_OUTPUT, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
                 prompt_builder=build_draft_prompt, prompt_version=DRAFT_PROMPT_VERSION,
                 expected_source=SOURCE)


if __name__ == "__main__":
    main()
