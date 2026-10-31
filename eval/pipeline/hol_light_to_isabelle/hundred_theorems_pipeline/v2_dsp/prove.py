"""Search and replay Hundred Theorems sketches with the shared DSP checker."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import prove as _engine
from ..common import RESULTS_DIR, SOURCE
from .generate_sketch import DEFAULT_OUTPUT as DEFAULT_INPUT

from ...babel_formal_pipeline.v2_dsp.input_contract import output_path
DEFAULT_OUTPUT = output_path(None, results_dir=RESULTS_DIR, filename="verified.jsonl", mode="draft")
DEFAULT_PROVE_OUTPUT = output_path(None, results_dir=RESULTS_DIR, filename="prove.jsonl", mode="draft")


def prove_sketches(*, config, input_path: str = DEFAULT_INPUT, output_path: str | None = None,
                   prove_output=_engine._DEFAULT_PROVE, **options) -> list[dict]:
    return _engine.prove_sketches(
        config=config, input_path=input_path, output_path=output_path, prove_output=prove_output,
        results_dir=RESULTS_DIR, expected_source=SOURCE, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
                 default_prove_output=DEFAULT_PROVE_OUTPUT, results_dir=RESULTS_DIR,
                 expected_source=SOURCE)


if __name__ == "__main__":
    main()
