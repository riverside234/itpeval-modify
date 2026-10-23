"""Run Isabelle Sketch, DSP Prove, and replay from shared saved V2 Drafts."""

from __future__ import annotations

import argparse
import json

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, key, latest_records, repo_path, summarize, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import (
    DEFAULT_OUTPUT as DEFAULT_DSP, export_drafts, export_record,
)
from eval.pipeline.hol_light_to_isabelle.v2_dsp.generate_sketch import (
    DEFAULT_OUTPUT as DEFAULT_SKETCHES, generate_sketches,
)
from eval.pipeline.hol_light_to_isabelle.v2_dsp.preflight import preflight
from eval.pipeline.hol_light_to_isabelle.v2_dsp.prove import (
    DEFAULT_OUTPUT, DEFAULT_PROVE_OUTPUT, prove_sketches,
)
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.v2_dsp.sketch_prompt import build_sketch_prompt
from eval.pipeline.proof_transfer.llm import DEFAULT_DRAFT_MODEL


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--config", required=True)
    parser.add_argument("--drafts", required=True)
    parser.add_argument("--dsp-output", default=DEFAULT_DSP)
    parser.add_argument("--sketch-output", default=DEFAULT_SKETCHES)
    parser.add_argument("--prove-output", default=DEFAULT_PROVE_OUTPUT)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--sketch-model", default=DEFAULT_DRAFT_MODEL)
    parser.add_argument("--sketch-reasoning-effort", default="high")
    parser.add_argument("--max-output-tokens", type=int, default=16000)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--fail-fast", action="store_true")
    parser.add_argument("--skip-sketch", action="store_true")
    parser.add_argument("--skip-prove", action="store_true",
                        help="Replay the already completed --prove-output proofs only.")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.samples < 1:
        parser.error("--samples must be positive")
    filters = dict(topic=args.topic, target_key=args.target_key, limit=args.limit)
    expected = latest_records(args.drafts, **filters)
    if not expected:
        parser.error("no matching saved Drafts")
    if args.dry_run:
        prompt = build_sketch_prompt(export_record(expected[0]))
        print(json.dumps({"pipeline": "v2-dsp", "selected_records": len(expected),
                          "samples": args.samples, "prompt_version": prompt.version,
                          "system_prompt": prompt.system_prompt,
                          "user_prompt": prompt.user_prompt}, indent=2))
        return
    paths = [args.drafts, args.dsp_output, args.sketch_output, args.prove_output, args.output]
    if len(set(repo_path(path) for path in paths)) != len(paths):
        parser.error("Draft, exported input, Sketch, Prove, and final paths must be distinct")
    config = DspConfig.load(args.config)
    exported = export_drafts(
        input_path=args.drafts, output_path=args.dsp_output, **filters,
        continue_on_error=not args.fail_fast)
    if not args.skip_sketch and not args.skip_prove:
        backend = config.metadata()
        first = True
        blocked = {}
        for record in exported:
            if record.get("input_error"):
                continue
            check = preflight(record, config=config, controls=first, backend_metadata=backend)
            if not check["ok"]:
                if args.fail_fast or check.get("baseline_ok"):
                    raise RuntimeError("DSP preflight failed: " + json.dumps(check))
                blocked[key(record)] = json.dumps(check)
            else:
                first = False
        generate_sketches(
            input_path=args.dsp_output, output_path=args.sketch_output, **filters,
            samples=args.samples, model=args.sketch_model,
            reasoning_effort=args.sketch_reasoning_effort,
            max_output_tokens=args.max_output_tokens, resume=not args.no_resume,
            continue_on_error=not args.fail_fast, blocked_targets=blocked)
    source = args.prove_output if args.skip_prove else args.sketch_output
    if not repo_path(source).is_file():
        parser.error("requested saved Sketch/Prove artifact does not exist")
    results = prove_sketches(
        config=config, input_path=source, output_path=args.output,
        prove_output=None if args.skip_prove else args.prove_output,
        **filters, resume=not args.no_resume, replay_only=args.skip_prove,
        expected=expected, expected_samples=args.samples)
    print(json.dumps(summarize(results, expected=expected, expected_samples=args.samples), indent=2))


if __name__ == "__main__":
    main()
