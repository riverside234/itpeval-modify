"""Compile Hundred Theorems candidates with the same Isabelle2024 verifier."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval import verify_isabelle as _engine
from ..common import RESULTS_DIR, SOURCE, require_source, summarize
from .generate_sketch import DEFAULT_OUTPUT as DEFAULT_INPUT

DEFAULT_OUTPUT = RESULTS_DIR + "/v2-itpeval/hundred_theorems_v2_verified.jsonl"
VERIFY_VERSION = _engine.VERIFY_VERSION
normalize_proof = _engine.normalize_proof
compose_theory = _engine.compose_theory


def compile_theory(theory: str, **options):
    return _engine.compile_theory(theory, results_dir=RESULTS_DIR, **options)


def preflight(record: dict, **options) -> dict:
    require_source([record], SOURCE)
    return _engine.preflight(record, results_dir=RESULTS_DIR, **options)


def verify_record(record: dict, **options) -> dict:
    require_source([record], SOURCE)
    return _engine.verify_record(record, results_dir=RESULTS_DIR, **options)


def verify_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT, **options) -> list[dict]:
    return _engine.verify_sketches(
        input_path=input_path, output_path=output_path,
        results_dir=RESULTS_DIR, expected_source=SOURCE, **options)


def main() -> None:
    _engine.main(default_input=DEFAULT_INPUT, default_output=DEFAULT_OUTPUT,
                 results_dir=RESULTS_DIR, expected_source=SOURCE)


if __name__ == "__main__":
    main()
