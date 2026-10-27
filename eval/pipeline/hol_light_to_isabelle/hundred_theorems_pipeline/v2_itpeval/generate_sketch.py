"""Generate v2_itpeval sketches from saved Hundred Theorems Drafts."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval import generate_sketch as _engine
from ..common import RESULTS_DIR, SOURCE
from ..generate_draft import DEFAULT_OUTPUT as DEFAULT_INPUT
from .sketch_prompt import SKETCH_PROMPT_VERSION, build_sketch_prompt

DEFAULT_OUTPUT = RESULTS_DIR + "/v2-itpeval/hundred_theorems_v2_sketches.jsonl"


def generate_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str | None = None, **options) -> int:
    return _engine.generate_sketches(
        input_path=input_path, output_path=output_path,
        prompt_builder=build_sketch_prompt, prompt_version=SKETCH_PROMPT_VERSION,
        expected_source=SOURCE, default_output=DEFAULT_OUTPUT, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
                 prompt_builder=build_sketch_prompt, prompt_version=SKETCH_PROMPT_VERSION,
                 expected_source=SOURCE)


if __name__ == "__main__":
    main()
