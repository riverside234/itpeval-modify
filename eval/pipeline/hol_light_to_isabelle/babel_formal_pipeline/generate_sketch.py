"""Compatibility entry point for the original V2 generator."""
import sys
from importlib import import_module

_implementation = import_module(
    "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.generate_sketch")
if __name__ == "__main__":
    _implementation.main(legacy=True)
else:
    sys.modules[__name__] = _implementation
