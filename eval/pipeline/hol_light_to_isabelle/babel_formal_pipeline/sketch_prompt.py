"""Compatibility import for the original V2 Sketch prompt."""
import sys
from importlib import import_module

sys.modules[__name__] = import_module(
    "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.sketch_prompt")
