"""Compatibility entry point for the original V2 verifier."""
import sys
from importlib import import_module

_implementation = import_module(
    "eval.pipeline.hol_light_to_isabelle.v2_itpeval.verify_isabelle")
if __name__ == "__main__":
    _implementation.main(legacy=True)
else:
    sys.modules[__name__] = _implementation
