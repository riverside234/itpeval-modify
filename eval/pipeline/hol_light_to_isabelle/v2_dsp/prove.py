"""Fill DSP sketches and replay the completed individual target proofs."""

from __future__ import annotations

import argparse
import json

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, RESULTS_DIR, align_samples, fingerprint, key, latest_records, read_jsonl,
    repo_path, save_results, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.v2_dsp.checker import CHECKER_VERSION, Checker
from eval.pipeline.hol_light_to_isabelle.v2_dsp.generate_sketch import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig


DEFAULT_OUTPUT = RESULTS_DIR + "/v2-dsp/babel_formal_v2_verified.jsonl"
DEFAULT_PROVE_OUTPUT = RESULTS_DIR + "/v2-dsp/babel_formal_v2_prove.jsonl"


def prove_sketches(*, config: DspConfig, input_path: str = DEFAULT_INPUT,
                   output_path: str = DEFAULT_OUTPUT, prove_output: str | None = DEFAULT_PROVE_OUTPUT,
                   topic: str | None = None, target_key: str | None = None,
                   limit: int | None = None, resume: bool = True,
                   replay_only: bool = False, expected: list[dict] | None = None,
                   expected_samples: int | None = None) -> list[dict]:
    records = latest_records(input_path, samples=True, topic=topic, target_key=target_key, limit=limit)
    records = align_samples(records, expected, expected_samples, pipeline="v2-dsp")
    if not records:
        raise ValueError("no matching DSP Sketch records")
    output = repo_path(output_path)
    previous = read_jsonl(output_path) if resume and output.is_file() else []
    completed = {row.get("verify_fingerprint"): row for row in previous
                 if row.get("pipeline") == "v2-dsp" and row.get("verified")
                 and row.get("checker_version") == CHECKER_VERSION}
    try:
        backend = config.metadata()
        backend_error = None
    except Exception as exc:
        backend, backend_error = None, exc
    results = []
    for record in records:
        identity = fingerprint({
            "pipeline": "v2-dsp", "record": record, "backend": backend,
            "config": config.__dict__, "checker_version": CHECKER_VERSION,
            "replay_only": replay_only,
        })
        result = completed.get(identity) if backend_error is None else None
        if result is None:
            if backend_error is not None and not record.get("sketch_error"):
                result = {**record, "pipeline": "v2-dsp", "verified": False,
                          "prove_success": False, "replay_verified": False,
                          "checker_version": CHECKER_VERSION, "step_results": [],
                          "failure_category": "toolchain_error",
                          "verify_error": f"{type(backend_error).__name__}: {backend_error}"}
            else:
                result = Checker(config).check(
                    record, replay_only=replay_only, backend_metadata=backend)
            result["verify_fingerprint"] = identity
        results.append(result)
        print(f"DSP {'PASS' if result['verified'] else 'FAIL'} "
              f"{record['topic']}/{record['target_key']} sample={record['sample_idx']}")
    if prove_output and repo_path(prove_output) != output:
        save_results(prove_output, results, expected=expected, expected_samples=expected_samples,
                     preserve_unselected=resume)
    save_results(output_path, results, expected=expected, expected_samples=expected_samples,
                 preserve_unselected=resume)
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--config", required=True)
    parser.add_argument("--input", default=DEFAULT_INPUT)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--prove-output", default=DEFAULT_PROVE_OUTPUT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--replay-only", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    records = prove_sketches(
        config=DspConfig.load(args.config), input_path=args.input, output_path=args.output,
        prove_output=args.prove_output, topic=args.topic, target_key=args.target_key,
        limit=args.limit, resume=not args.no_resume, replay_only=args.replay_only)
    print(json.dumps({"targets": len({key(row) for row in records}),
                      "verified_samples": sum(bool(row["verified"]) for row in records)}, indent=2))


if __name__ == "__main__":
    main()
