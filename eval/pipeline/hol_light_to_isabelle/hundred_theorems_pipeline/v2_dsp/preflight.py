"""Run the identical native DSP preflight on Hundred Theorems contexts."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import preflight as _engine
from ..common import RESULTS_DIR, SOURCE, require_source
from ..extract_hol_light import DEFAULT_OUTPUT as DEFAULT_INPUT


def control_record(proof: str) -> dict:
    return _engine.control_record(proof, source=SOURCE)


def preflight(record: dict, **options) -> dict:
    require_source([record], SOURCE)
    return _engine.preflight(record, results_dir=RESULTS_DIR, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, results_dir=RESULTS_DIR, expected_source=SOURCE)


if __name__ == "__main__":
    main()
