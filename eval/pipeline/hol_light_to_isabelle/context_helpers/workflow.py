"""Compare current and dependency-aware prompt context for most-match."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import time

from ..babel_formal_pipeline.isabelle_syntax import tokens as isabelle_tokens
from ..babel_formal_pipeline.preflight_storage import write_json
from ..babel_formal_pipeline.theory_context import validate_context
from ..babel_formal_pipeline.v2_dsp.checker import Checker
from ..babel_formal_pipeline.v2_dsp.export_dsp import export_record
from ..babel_formal_pipeline.v2_dsp.generate_sketch import generate_sketches
from ..babel_formal_pipeline.v2_dsp.input_contract import clean_record, envelope, load_inputs, validate_artifacts
from ..babel_formal_pipeline.v2_dsp.native_search import NativeFailure
from ..babel_formal_pipeline.v2_dsp.parallel import (
    add_parallel_arguments, completed_jobs, parallel_options, plan_parallel, prepare_batch,
)
from ..babel_formal_pipeline.v2_dsp.prove import prove_sketches
from ..babel_formal_pipeline.v2_dsp.runtime import DspConfig
from ..most_match_pipeline.common import (
    DATASET_ROOT, LAB_REPO_ROOT, RESULTS_DIR, SOURCE, fingerprint, key, prompt_hash, read_jsonl,
    repo_path, require_source, validate_layout, write_jsonl,
)
from ..most_match_pipeline.context import DEPENDENCY_CONTEXT_VERSION, validate_prompt_context
from ..most_match_pipeline.v2_dsp.direct_sketch_prompt import DIRECT_PROMPT_VERSION, build_direct_sketch_prompt
from eval.pipeline.proof_transfer.llm import resolve_model_config

from .context import arm_record, baseline_view, prepare_selection, selection_change
from .contracts import ContextConfig, MODE, SelectionFailure, VERSION

DEFAULT_OUTPUT = RESULTS_DIR + "/context_helpers"
ARMS = ("baseline", "context", "context-native")


def prepare_records(records, config, *, arm, dataset_root):
    prepared = []
    for original in records:
        row = arm_record(original, arm)
        report = {"target": list(key(row)), "arm": arm, "status": "selected",
                  "baseline": baseline_view(original)}
        selection = None
        try:
            validate_prompt_context(original)
            if arm == "baseline":
                validate_context(original)
            else:
                selection = prepare_selection(original, config, dataset_root=dataset_root)
                snapshot, report = selection.render()
                row = snapshot if arm == "context" else row
        except (KeyError, OSError, ValueError) as exc:
            mark_failure(report, getattr(exc, "category", "context_selection_error"), exc)
        report["arm"] = arm
        prepared.append((row, report, selection))
    return prepared


def mark_failure(report, category, exc):
    report.update(status="failed", failure_category=category, error=str(exc)[:2000])


def check_native(prepared, *, arm, config, plan, output):
    """Open each original target once before inference. Use the same parent for Prove."""
    valid = [i for i, (_, report, _) in enumerate(prepared) if report["status"] != "failed"]
    if not valid:
        return None, 0.0
    started = time.monotonic()
    try:
        runtime, backend, factory = prepare_batch(config, [prepared[i][0] for i in valid], plan)
    except Exception as exc:
        for i in valid:
            mark_failure(prepared[i][1], getattr(exc, "category", "toolchain_error"), exc)
        return None, round(time.monotonic() - started, 3)
    setup_s = round(time.monotonic() - started, 3)
    checker = Checker(runtime, native_factory=factory, results_dir=str(output))
    backend_sha = backend["backend_fingerprint"]

    def check(i):
        row, report, selection = prepared[i]
        began = time.monotonic()
        action = "inspect_facts" if arm == "context-native" else "context"
        options = {"fact_names": tuple(selection.shortlist)} if action == "inspect_facts" else {}
        try:
            native = factory(runtime).request(
                row, "", directory=checker.directory("inspect-" if options else "context-"),
                action=action, heuristics=(), deadline=began + runtime.target_timeout_s, **options)
            if not native["success"]:
                raise NativeFailure(native["failure_category"], native["error"], details=native)
            if action == "inspect_facts":
                snapshot = report["selection"]
                row, report = selection.render(inspection=native["fact_inspection"], backend_sha256=backend_sha)
                report["native_changes"] = selection_change(snapshot["isabelle"], report["selection"]["isabelle"])
            report["resolved_imports"] = native["import_resolution"]["resolved_imports"]
        except (NativeFailure, ValueError, OSError, TimeoutError) as exc:
            category = "timeout" if isinstance(exc, TimeoutError) else getattr(exc, "category", "context_error")
            mark_failure(report, category, exc)
            details = getattr(exc, "details", {})
            report["native_log"] = details.get("build_log_path")
        report["context_check_s"] = round(time.monotonic() - began, 3)
        print(f"CONTEXT {report['status'].upper()} {row['topic']}/{row['target_key']}", flush=True)
        return row, report, None

    for index, result in completed_jobs(check, valid, workers=plan.workers):
        prepared[valid[index]] = result
    return (backend, factory), setup_s


def export_selected(prepared, helper_config):
    exported, reports, blocked = [], [], {}
    for raw, report, _ in prepared:
        try:
            if report["status"] == "failed":
                raise SelectionFailure(report["failure_category"], report["error"])
            row = export_record(raw, expected_source=SOURCE, sketch_source=MODE)
            prompt = build_direct_sketch_prompt(row)
            report["prompt_chars"] = len(prompt.system_prompt) + len(prompt.user_prompt)
            if report["prompt_chars"] > helper_config.max_prompt_chars:
                raise SelectionFailure("prompt_context_overflow", "whole sketch prompt exceeds max_prompt_chars")
            report["prompt_sha256"] = prompt_hash(prompt.system_prompt, prompt.user_prompt)
        except ValueError as exc:
            mark_failure(report, getattr(exc, "category", "input_error"), exc)
            blocked[key(raw)] = {"failure_category": report["failure_category"], "error": report["error"]}
            row = {**clean_record(raw, MODE), **envelope(MODE), "input_error": report["error"],
                   "failure_category": report["failure_category"]}
        exported.append(row)
        reports.append(report)
    return exported, reports, blocked


def check_outputs(output, arm):
    for name in ("inputs.jsonl", "sketches.jsonl", "verified.jsonl"):
        path = output / name
        if path.is_file():
            previous = read_jsonl(path)
            validate_artifacts(previous, MODE)
            if any(row.get("metadata", {}).get("context_experiment", {}).get("arm") != arm for row in previous):
                raise ValueError(f"incompatible experiment arm in {path}; use a separate output directory")


def save_outcomes(output, results, reports, *, arm, settings_sha):
    report_by_key = {tuple(report["target"]): report for report in reports}
    outcomes = []
    for result in results:
        identity = key(result)
        report = report_by_key[identity]
        meta = result["metadata"]["context_experiment"]
        usage = (result.get("sketch_response") or {}).get("usage") or {}
        obligation = result.get("failed_obligation") or {}
        proof_names = {item.text.rsplit(".", 1)[-1] for item in isabelle_tokens(result.get("isabelle_proof", ""))
                       if item.kind == "word"}
        selected_facts = [item["name"] for item in report.get("selection", report["baseline"])["isabelle"]["selected_snippets"]
                          if item["kind"] in {"lemma", "theorem", "corollary", "proposition", "lemmas", "signature"}]
        outcomes.append({
            "selected_fact_mentions": [name for name in selected_facts if name.rsplit(".", 1)[-1] in proof_names],            "target": list(identity), "arm": arm, "pair_sha256": meta["pair_sha256"],
            "settings_sha256": settings_sha, "verified": result["verified"],
            "failure_category": result.get("failure_category"),
            "failed_phase": obligation.get("mode") or result.get("failure_category"),
            "input_tokens": usage.get("input_tokens"), "output_tokens": usage.get("output_tokens"),
            "prompt_chars": report.get("prompt_chars"), "context_check_s": report.get("context_check_s"),
            "sketch_s": result.get("sketch_duration_seconds"), "verify_s": result.get("verify_duration_seconds"),
            "hammer_calls": (result.get("search_summary") or {}).get("hammer_attempts", 0),
            "reconstructions": (result.get("search_summary") or {}).get("reconstruction_attempts", 0),
        })
    write_jsonl(output / "outcomes.jsonl", outcomes)


def compare_arms(root):
    baseline_path = root / "baseline" / "outcomes.jsonl"
    if not baseline_path.is_file():
        return
    baseline = {tuple(row["target"]): row for row in read_jsonl(baseline_path)}
    summary = {}
    for arm in ARMS[1:]:
        path = root / arm / "outcomes.jsonl"
        if not path.is_file():
            continue
        context = {tuple(row["target"]): row for row in read_jsonl(path)}
        paired = []
        for target in sorted(baseline.keys() & context.keys()):
            left, right = baseline[target], context[target]
            if all(left[field] == right[field] for field in ("pair_sha256", "settings_sha256")):
                paired.append({"target": list(target), "baseline": left, "context": right})
        summary[arm] = {"paired_targets": len(paired), "baseline_only_targets": len(baseline.keys() - context.keys()),
                        "context_only_targets": len(context.keys() - baseline.keys()),
                        "incompatible_pairs": len(baseline.keys() & context.keys()) - len(paired),
                        "both_pass": sum(row["baseline"]["verified"] and row["context"]["verified"] for row in paired),
                        "baseline_pass_only": sum(row["baseline"]["verified"] and not row["context"]["verified"] for row in paired),
                        "context_pass_only": sum(row["context"]["verified"] and not row["baseline"]["verified"] for row in paired),
                        "both_fail": sum(not row["baseline"]["verified"] and not row["context"]["verified"] for row in paired),
                        "outcomes": paired}
    if summary:
        write_json(root / "comparison.json", summary)


def run_experiment(records, *, output, arm, helper_config, dataset_root, inspect_only,
                   native_config=None, llm=None, parallel=None, resume=True):
    if not inspect_only:
        check_outputs(output, arm)
    prepared = prepare_records(records, helper_config, arm=arm, dataset_root=dataset_root)
    setup_s, prepared_native = 0.0, None
    if native_config is not None:
        plan = plan_parallel(native_config, **parallel)
        prepared_native, setup_s = check_native(
            prepared, arm=arm, config=native_config, plan=plan, output=output)
    exported, reports, blocked = export_selected(prepared, helper_config)
    write_jsonl(output / ("inspection.jsonl" if inspect_only else "selection.jsonl"), reports)
    summary = {"version": VERSION, "arm": arm, "inspect_only": inspect_only, "targets": len(records),
               "blocked_targets": len(blocked), "selection_failures": dict(Counter(
                   failure["failure_category"] for failure in blocked.values())), "native_setup_s": setup_s}
    if inspect_only:
        return summary
    inputs, sketches, verified = (output / filename for filename in ("inputs.jsonl", "sketches.jsonl", "verified.jsonl"))
    write_jsonl(inputs, exported)
    written = generate_sketches(
        input_path=str(inputs), output_path=str(sketches), samples=1, resume=resume,
        llm_config=llm, blocked_targets=blocked, sketch_source=MODE, expected_source=SOURCE,
        prompt_builder=build_direct_sketch_prompt, prompt_version=DIRECT_PROMPT_VERSION)
    results = prove_sketches(
        config=native_config, input_path=str(sketches), output_path=str(verified), prove_output=None,
        resume=resume, expected=exported, expected_samples=1, results_dir=str(output),
        sketch_source=MODE, expected_source=SOURCE, prepared_native=prepared_native, **parallel)
    # A cold baseline can create the HOL heap during setup. Pair on release,
    # sources, worker code and configuration rather than the pre-build heap list.
    backend = {name: value for name, value in prepared_native[0].items()
               if name not in {"backend_fingerprint", "session_heaps_sha256"}} if prepared_native else None
    settings = fingerprint([DIRECT_PROMPT_VERSION, llm.to_metadata(), native_config.__dict__, parallel, backend,
                            helper_config.max_prompt_chars])
    save_outcomes(output, results, reports, arm=arm, settings_sha=settings)
    compare_arms(output.parent)
    summary.update(new_sketch_rows=written, verified=sum(row["verified"] for row in results),
                   verification_summary=str(verified.with_suffix(".summary.json")))
    write_json(output / "run.json", summary)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--dataset", choices=["most-match"], default="most-match")
    parser.add_argument("--dataset-root", default=DATASET_ROOT)
    parser.add_argument("--records", required=True, help="Fresh extracted most-match records JSONL")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--helper-mode", choices=["baseline", "context"], default="context")
    parser.add_argument("--helper-config", help="Optional context experiment settings JSON")
    parser.add_argument("--config", help="Native Isabelle2026 configuration for lab runs")
    parser.add_argument("--llm-config", help="API or vLLM profile for the existing direct sketch")
    parser.add_argument("--inspect-only", action="store_true", help="Write a selection comparison without inference")
    parser.add_argument("--native-facts", action="store_true", help="Resolve a shortlist in the native Isabelle context")
    parser.add_argument("--samples", type=int, choices=[1], default=1)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT, help="Parent directory for the experiment arms")
    add_parallel_arguments(parser)
    parser.set_defaults(memory_per_worker_gb=12.0)
    args = parser.parse_args()
    if args.native_facts and args.helper_mode != "context":
        parser.error("--native-facts requires --helper-mode context")
    use_native = not args.inspect_only or args.native_facts
    if use_native and not args.config:
        parser.error("--config is required for a lab run or --native-facts")
    arm = "context-native" if args.native_facts else args.helper_mode
    try:
        validate_layout(args.expected_root)
        output = repo_path(Path(args.output_dir) / arm)
        input_paths = [args.records, args.config, args.llm_config, args.helper_config]
        if any(repo_path(path).is_relative_to(output) for path in input_paths if path):
            raise ValueError("keep input records and configurations outside the experiment arm directory")
        records = load_inputs(args.records, mode=MODE, topic=args.topic, target_key=args.target_key, limit=args.limit)
        require_source(records, SOURCE)
        if not records or any(row.get("pipeline") or row.get("metadata", {}).get("context_experiment")
                              or baseline_view(row)["version"] == DEPENDENCY_CONTEXT_VERSION for row in records):
            raise ValueError("provide matching original most-match extraction records")
        summary = run_experiment(records, output=output, arm=arm, helper_config=ContextConfig.load(args.helper_config),
            dataset_root=args.dataset_root, inspect_only=args.inspect_only,
            native_config=DspConfig.load(args.config) if use_native else None,
            llm=None if args.inspect_only else resolve_model_config(args.llm_config, default_effort="high"),
            parallel=parallel_options(args), resume=not args.no_resume)
    except (OSError, KeyError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps(summary, indent=2))
    if args.inspect_only and summary["blocked_targets"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
