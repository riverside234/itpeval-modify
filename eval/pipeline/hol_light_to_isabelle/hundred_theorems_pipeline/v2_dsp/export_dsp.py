"""Export the same saved Draft/oracle adapter schema for Hundred Theorems."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import export_dsp as _engine
from ..common import RESULTS_DIR, SOURCE
from ..generate_draft import DEFAULT_OUTPUT as DEFAULT_INPUT

from ...babel_formal_pipeline.v2_dsp.input_contract import output_path
DEFAULT_OUTPUT = output_path(None, results_dir=RESULTS_DIR, filename="inputs.jsonl", mode="draft")
SCHEMA_VERSION = _engine.SCHEMA_VERSION


def export_record(record: dict, *, sketch_source="draft") -> dict:
    return _engine.export_record(record, expected_source=SOURCE, sketch_source=sketch_source)


def export_inputs(**options) -> list[dict]:
    return _engine.export_inputs(expected_source=SOURCE, results_dir=RESULTS_DIR, **options)


def export_drafts(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT, **options) -> list[dict]:
    return _engine.export_drafts(input_path=input_path, output_path=output_path,
                                 expected_source=SOURCE, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
                 expected_source=SOURCE, results_dir=RESULTS_DIR)


if __name__ == "__main__":
    main()
