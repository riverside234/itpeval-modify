"""The original DSP search/replay contract with a separate work directory."""

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.checker import (
    CHECKER_VERSION, HEURISTICS, ProofFailure, Checker as _Checker,
)
from ..common import RESULTS_DIR


class Checker(_Checker):
    def __init__(self, config, **options):
        super().__init__(config, results_dir=RESULTS_DIR, **options)
