"""Compatibility alias for the relocated Babel Formal pipeline."""

from importlib import import_module
import sys

module = import_module("eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.generate_draft")

if __name__ == "__main__":
    module.main()
else:
    sys.modules[__name__] = module
