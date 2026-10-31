"""Generate v2_dsp sketches from saved Hundred Theorems Drafts."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import generate_sketch as _engine
from ..common import RESULTS_DIR, SOURCE
from .export_dsp import DEFAULT_OUTPUT as DEFAULT_INPUT
from .sketch_prompt import SKETCH_PROMPT_VERSION, build_sketch_prompt

from ...babel_formal_pipeline.v2_dsp.input_contract import output_path
from .direct_sketch_prompt import DIRECT_PROMPT_VERSION, build_direct_sketch_prompt
DEFAULT_OUTPUT = output_path(None, results_dir=RESULTS_DIR, filename="sketches.jsonl", mode="draft")


def generate_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str | None = None, **options) -> int:
    mode = options.get("sketch_source", "draft")
    return _engine.generate_sketches(
        input_path=input_path, output_path=output_path,
        prompt_builder=build_direct_sketch_prompt if mode == "hol-light-proof" else build_sketch_prompt,
        prompt_version=DIRECT_PROMPT_VERSION if mode == "hol-light-proof" else SKETCH_PROMPT_VERSION,
        expected_source=SOURCE, default_output=DEFAULT_OUTPUT, results_dir=RESULTS_DIR, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
                 expected_source=SOURCE, results_dir=RESULTS_DIR)


if __name__ == "__main__":
    main()
