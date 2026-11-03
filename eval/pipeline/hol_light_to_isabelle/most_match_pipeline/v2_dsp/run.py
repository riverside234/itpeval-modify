"""Run most-match Draft-to-Sketch or direct source-proof-to-Sketch experiments."""
from ...babel_formal_pipeline.v2_dsp.run_babel import main as _main
from ..common import RESULTS_DIR, SOURCE


def main():
    _main(expected_source=SOURCE, results_dir=RESULTS_DIR)


if __name__ == "__main__":
    main()
