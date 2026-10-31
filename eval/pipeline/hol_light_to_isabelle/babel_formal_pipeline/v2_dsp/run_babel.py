"""Run saved-Draft or direct HOL Light Sketch with DSP-style native Isabelle2026."""
from __future__ import annotations

import argparse
import importlib
import json
from pathlib import Path

from ..common import LAB_REPO_ROOT, RESULTS_DIR, key, repo_path, require_source, validate_layout, read_jsonl
from .export_dsp import export_inputs, export_record
from .generate_sketch import generate_sketches
from .input_contract import MODES, envelope, load_inputs, output_path, validate_artifacts
from .preflight import preflight
from .prove import prove_sketches
from .runtime import DspConfig
from eval.pipeline.proof_transfer.llm import resolve_model_config


def main(*, expected_source="babel-formal", results_dir=RESULTS_DIR) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--config", required=True)
    parser.add_argument("--sketch-source", choices=MODES, default="draft")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--drafts")
    group.add_argument("--records")
    for name in ("dsp-output", "sketch-output", "prove-output", "output", "topic", "target-key"):
        parser.add_argument("--" + name)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--sketch-llm-config", help="API or vLLM profile for Sketch; no Draft is generated")
    parser.add_argument("--sketch-model")
    parser.add_argument("--sketch-reasoning-effort")
    parser.add_argument("--max-output-tokens", type=int)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--skip-sketch", action="store_true")
    parser.add_argument("--skip-prove", action="store_true", help="Replay saved completed --prove-output proofs")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    mode = args.sketch_source
    if mode == "draft" and not args.drafts or mode == "hol-light-proof" and not args.records:
        parser.error("draft mode requires --drafts; hol-light-proof mode requires --records")
    if args.samples < 1:
        parser.error("--samples must be positive")
    source = args.drafts or args.records
    filters = dict(topic=args.topic, target_key=args.target_key, limit=args.limit)
    expected = load_inputs(source, mode=mode, **filters)
    require_source(expected, expected_source)
    if not expected:
        parser.error("no matching input targets")
    llm = resolve_model_config(args.sketch_llm_config, model=args.sketch_model,
        reasoning_effort=args.sketch_reasoning_effort, max_output_tokens=args.max_output_tokens,
        default_effort="high", dry_run=args.dry_run)
    for attr, filename in (("dsp_output", "inputs.jsonl"), ("sketch_output", "sketches.jsonl"),
                           ("prove_output", "prove.jsonl"), ("output", "verified.jsonl")):
        setattr(args, attr, output_path(getattr(args, attr), results_dir=results_dir,
                                       filename=filename, mode=mode, config=llm, records=expected))
    dataset = "hundred_theorems_pipeline" if expected_source == "hundred-theorems" else "babel_formal_pipeline"
    module = importlib.import_module("eval.pipeline.hol_light_to_isabelle." + dataset + ".v2_dsp." +
                                   ("direct_sketch_prompt" if mode == "hol-light-proof" else "sketch_prompt"))
    builder = module.build_direct_sketch_prompt if mode == "hol-light-proof" else module.build_sketch_prompt
    version = module.DIRECT_PROMPT_VERSION if mode == "hol-light-proof" else module.SKETCH_PROMPT_VERSION
    if args.dry_run:
        prompt = builder(export_record(expected[0], expected_source=expected_source, sketch_source=mode))
        print(json.dumps({**envelope(mode), "selected_records": len(expected), "samples": args.samples,
            "llm_config": llm.to_metadata(), "prompt_version": prompt.version,
            "outputs": {name: getattr(args, name) for name in ("dsp_output", "sketch_output", "prove_output", "output")},
            "system_prompt": prompt.system_prompt, "user_prompt": prompt.user_prompt}, indent=2))
        return
    paths = [source, args.dsp_output, args.sketch_output, args.prove_output, args.output]
    if len({repo_path(path) for path in paths}) != len(paths):
        parser.error("source input, export, Sketch, Prove and final paths must be distinct")
    for path in paths[1:]:
        if repo_path(path).is_file():
            validate_artifacts(read_jsonl(path), mode)
    config = DspConfig.load(args.config)
    exported = export_inputs(input_path=source, output_path=args.dsp_output, **filters,
        sketch_source=mode, expected_source=expected_source, results_dir=results_dir,
        continue_on_error=not args.fail_fast)
    run_dir = str(Path(args.output).parent)
    if not args.skip_sketch and not args.skip_prove:
        blocked = {}
        try:
            backend = config.metadata()
            first = True
            capability_error = None
            for record in exported:
                if record.get("input_error"):
                    continue
                check = preflight(record, config=config, controls=first, backend_metadata=backend,
                                  results_dir=run_dir, sketch_source=mode)
                if not check["ok"]:
                    blocked[key(record)] = json.dumps(check)
                    if check.get("baseline_ok"):
                        capability_error = "native capability controls failed: " + json.dumps(check)
                        break
                    if args.fail_fast:
                        raise RuntimeError("target context preflight failed: " + json.dumps(check))
                else:
                    first = False
            if capability_error:
                blocked = {key(row): {"failure_category": "capability_error", "error": capability_error} for row in exported}
        except Exception as exc:
            if args.fail_fast:
                raise
            blocked = {key(row): {"failure_category": "toolchain_error",
                                  "error": "native preflight failed before inference: " + str(exc)} for row in exported}
        generate_sketches(input_path=args.dsp_output, output_path=args.sketch_output, **filters,
            samples=args.samples, resume=not args.no_resume, continue_on_error=not args.fail_fast,
            blocked_targets=blocked, llm_config=llm, sketch_source=mode, expected_source=expected_source,
            prompt_builder=builder, prompt_version=version, results_dir=results_dir)
    proof_input = args.prove_output if args.skip_prove else args.sketch_output
    if not repo_path(proof_input).is_file():
        parser.error("requested saved Sketch/Prove artifact does not exist")
    results = prove_sketches(config=config, input_path=proof_input, output_path=args.output,
        prove_output=None if args.skip_prove else args.prove_output, **filters,
        resume=not args.no_resume, replay_only=args.skip_prove, expected=exported,
        expected_samples=args.samples, results_dir=run_dir, sketch_source=mode, expected_source=expected_source)
    summary_path = repo_path(args.output).with_suffix(".summary.json")
    print(summary_path.read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
