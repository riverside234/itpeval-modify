"""Export the same saved Draft/oracle adapter schema for Hundred Theorems."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import export_dsp as _engine
from ..common import RESULTS_DIR, SOURCE
from ..generate_draft import DEFAULT_OUTPUT as DEFAULT_INPUT

DEFAULT_OUTPUT = RESULTS_DIR + "/v2-dsp/hundred_theorems_v2_dsp_input.jsonl"
SCHEMA_VERSION = _engine.SCHEMA_VERSION


def export_record(record: dict) -> dict:
    return _engine.export_record(record, expected_source=SOURCE)


def export_drafts(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT, **options) -> list[dict]:
    return _engine.export_drafts(input_path=input_path, output_path=output_path,
                                 expected_source=SOURCE, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
                 expected_source=SOURCE)


if __name__ == "__main__":
    main()
