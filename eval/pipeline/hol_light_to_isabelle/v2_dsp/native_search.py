"""Compatibility alias for the Babel Formal native DSP module."""
from importlib import import_module
import sys
sys.modules[__name__] = import_module("eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search")
