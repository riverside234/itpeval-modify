"""Fill DSP sketches and replay the completed individual target proofs."""

from __future__ import annotations

import argparse
import json

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    LAB_REPO_ROOT, RESULTS_DIR, fingerprint, key, read_jsonl,
    repo_path, require_source, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.checker import CHECKER_VERSION, Checker
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.generate_sketch import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from .input_contract import (MODES, align_samples, envelope, load_inputs, output_path as native_output_path,
                             validate_artifacts, save_results)


DEFAULT_OUTPUT = native_output_path(None, results_dir=RESULTS_DIR, filename="verified.jsonl", mode="draft")
DEFAULT_PROVE_OUTPUT = native_output_path(None, results_dir=RESULTS_DIR, filename="prove.jsonl", mode="draft")
_DEFAULT_PROVE = object()


def prove_sketches(*, config: DspConfig, input_path: str = DEFAULT_INPUT,
                   output_path: str | None = None, prove_output=_DEFAULT_PROVE,
                   topic: str | None = None, target_key: str | None = None,
                   limit: int | None = None, resume: bool = True,
                   replay_only: bool = False, expected: list[dict] | None = None,
                   expected_samples: int | None = None, results_dir: str = RESULTS_DIR,
                   expected_source: str = "babel-formal", sketch_source: str = "draft") -> list[dict]:
    records = load_inputs(input_path, mode=sketch_source, artifacts=True, samples=True, topic=topic, target_key=target_key, limit=limit)
    records = align_samples(records, expected, expected_samples, mode=sketch_source)
    if not records:
        raise ValueError("no matching DSP Sketch records")
    require_source(records, expected_source)
    output_path = native_output_path(output_path, results_dir=results_dir, filename="verified.jsonl",
                                     mode=sketch_source, records=records)
    if prove_output is _DEFAULT_PROVE:
        prove_output = native_output_path(None, results_dir=results_dir, filename="prove.jsonl",
                                          mode=sketch_source, records=records)
    if repo_path(input_path) == repo_path(output_path) or prove_output and repo_path(input_path) == repo_path(prove_output):
        raise ValueError("Sketch/Prove input and verification outputs must be distinct")
    output = repo_path(output_path)
    all_previous = read_jsonl(output_path) if output.is_file() else []
    validate_artifacts(all_previous, sketch_source)
    if prove_output and repo_path(prove_output).is_file():
        validate_artifacts(read_jsonl(prove_output), sketch_source)
    previous = all_previous if resume else []
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
            **envelope(sketch_source), "record": record, "backend": backend,
            "config": config.__dict__, "checker_version": CHECKER_VERSION,
            "replay_only": replay_only,
        })
        result = completed.get(identity) if backend_error is None else None
        if result is None:
            if backend_error is not None and not record.get("sketch_error"):
                result = {**record, **envelope(sketch_source), "verified": False,
                          "prove_success": False, "replay_verified": False,
                          "checker_version": CHECKER_VERSION, "step_results": [],
                          "failure_category": "toolchain_error",
                          "verify_error": f"{type(backend_error).__name__}: {backend_error}"}
            else:
                result = Checker(config, results_dir=results_dir).check(
                    record, replay_only=replay_only, backend_metadata=backend)
            result["verify_fingerprint"] = identity
        results.append(result)
        print(f"DSP {'PASS' if result['verified'] else 'FAIL'} "
              f"{record['topic']}/{record['target_key']} sample={record['sample_idx']}")
    if prove_output and repo_path(prove_output) != output:
        save_results(prove_output, results, expected=expected, expected_samples=expected_samples,
                     preserve_unselected=resume, mode=sketch_source)
    save_results(output_path, results, expected=expected, expected_samples=expected_samples,
                 preserve_unselected=resume, mode=sketch_source)
    return results


def main(*, default_input: str = DEFAULT_INPUT, default_output: str = DEFAULT_OUTPUT,
         default_prove_output: str = DEFAULT_PROVE_OUTPUT, results_dir: str = RESULTS_DIR,
         expected_source: str = "babel-formal") -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--config", required=True)
    parser.add_argument("--sketch-source", choices=MODES, default="draft")
    parser.add_argument("--input", default=default_input)
    parser.add_argument("--output")
    parser.add_argument("--prove-output", default=_DEFAULT_PROVE)
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
        limit=args.limit, resume=not args.no_resume, replay_only=args.replay_only, results_dir=results_dir, expected_source=expected_source, sketch_source=args.sketch_source)
    print(json.dumps({"targets": len({key(row) for row in records}),
                      "verified_samples": sum(bool(row["verified"]) for row in records)}, indent=2))


if __name__ == "__main__":
    main()
