"""Compare masked context and complete source helper proofs for HOL Light to Isabelle."""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import replace
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
from ..babel_formal_pipeline.v2_dsp.native_search import NativeFailure, inherits_core_set
from ..babel_formal_pipeline.v2_dsp.parallel import (
    add_parallel_arguments, completed_jobs, parallel_options, plan_parallel, prepare_batch,
)
from ..babel_formal_pipeline.v2_dsp.prove import prove_sketches
from ..babel_formal_pipeline.v2_dsp.runtime import DspConfig
from ..babel_formal_pipeline.common import (
    LAB_REPO_ROOT, fingerprint, key, prompt_hash, read_jsonl, repo_path, require_source, validate_layout, write_jsonl,
)
from ..most_match_pipeline.common import DATASET_ROOT
from ..isabelle_references import has_reference_proofs, reference_output
from ..most_match_pipeline.context import has_dependency_context
from eval.pipeline.proof_transfer.llm import resolve_model_config

from .context import arm_record, baseline_view, prepare_selection, selection_change
from .contracts import ARMS, HELPER_MODES, ContextConfig, MODE, NATIVE_ARMS, SelectionFailure, VERSION, context_arm
from .datasets import DATASETS, dataset_for
from .prompts import BUNDLE_FIELD
from .source_loads import LoadCatalog

def prepare_records(records, config, *, arm, dataset_root):
    mode = arm.split("-", 1)[0]
    catalog = LoadCatalog(config) if config.cross_file and arm != "baseline" else None
    prepared = []
    for original in records:
        row = arm_record(original, arm)
        report = {"target": list(key(row)), "arm": arm, "status": "selected"}
        selection = None
        try:
            if arm == "baseline":
                validate_context(original)
                report["baseline"] = baseline_view(original)
            else:
                selection = prepare_selection(original, config, dataset_root=dataset_root, catalog=catalog)
                if arm in NATIVE_ARMS:
                    _, report = selection.render()
                else:
                    row, report = selection.render(mode=mode)
        except (KeyError, OSError, ValueError) as exc:
            mark_failure(report, getattr(exc, "category", "context_selection_error"), exc)
        report["arm"] = arm
        prepared.append((row, report, selection))
    return prepared


def mark_failure(report, category, exc):
    report.update(status="failed", failure_category=category, error=str(exc)[:2000])


def check_native(prepared, *, arm, config, plan, output):
    """Open each original target once before inference. Use the same parent for Prove."""
    valid = []
    for i, (row, report, _) in enumerate(prepared):
        if report["status"] == "failed":
            continue
        if inherits_core_set(config, validate_context(row).theory_name):
            mark_failure(report, "unavailable_context", "Core Set is already inherited by the HOL parent")
        else:
            valid.append(i)
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
        action = "inspect_facts" if arm in NATIVE_ARMS else "context"
        options = {"fact_names": tuple(selection.shortlist)} if action == "inspect_facts" else {}
        try:
            native = factory(runtime).request(
                row, "", directory=checker.directory("inspect-" if options else "context-"),
                action=action, heuristics=(), deadline=began + runtime.target_timeout_s, **options)
            if not native["success"]:
                raise NativeFailure(native["failure_category"], native["error"], details=native)
            if action == "inspect_facts":
                snapshot = report["selection"]
                row, report = selection.render(mode=arm.split("-", 1)[0], inspection=native["fact_inspection"],
                                               backend_sha256=backend_sha)
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


def export_selected(prepared, helper_config, dataset):
    exported, reports, blocked = [], [], {}
    for raw, report, _ in prepared:
        try:
            if report["status"] == "failed":
                raise SelectionFailure(report["failure_category"], report["error"])
            row = export_record(raw, expected_source=dataset.source, sketch_source=MODE)
            prompt = dataset.prompt(row)
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


def check_outputs(output, arm, *, expected_source=None):
    for name in ("inputs.jsonl", "sketches.jsonl", "verified.jsonl"):
        path = output / name
        if path.is_file():
            previous = read_jsonl(path)
            validate_artifacts(previous, MODE)
            if expected_source is not None:
                require_source(previous, expected_source)
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
        view = report.get("selection") or report.get("baseline") or {}
        selected_facts = [item["name"] for item in view.get("isabelle", {}).get("selected_snippets", ())
                          if item["kind"] in {"lemma", "theorem", "corollary", "proposition", "lemmas", "signature"}]
        expansion = report.get("source_helper_expansion", {})
        outcomes.append({
            "reference_selection_sha256": fingerprint([view, report.get("dependency_graph"),
                                                       report.get("target_candidates")]),
            "source_helper_count": len(expansion.get("included", ())),
            "source_helper_proof_chars": expansion.get("proof_chars", 0),
            "source_helper_support_chars": expansion.get("support_chars", 0),
            "selected_fact_mentions": [name for name in selected_facts if name.rsplit(".", 1)[-1] in proof_names],
            "target": list(identity), "arm": arm, "pair_sha256": meta["pair_sha256"],
            "settings_sha256": settings_sha, "verified": result["verified"],
            "failure_category": result.get("failure_category"),
            "failed_phase": obligation.get("mode") or result.get("failure_category"),
            "input_tokens": usage.get("input_tokens", usage.get("prompt_tokens")),
            "output_tokens": usage.get("output_tokens", usage.get("completion_tokens")),
            "prompt_chars": report.get("prompt_chars"), "context_check_s": report.get("context_check_s"),
            "sketch_s": result.get("sketch_duration_seconds"), "verify_s": result.get("verify_duration_seconds"),
            "hammer_calls": (result.get("search_summary") or {}).get("hammer_attempts", 0),
            "reconstructions": (result.get("search_summary") or {}).get("reconstruction_attempts", 0),
        })
    write_jsonl(output / "outcomes.jsonl", outcomes)


def compare_arms(root):
    outcomes = {}
    for arm in ARMS:
        path = root / arm / "outcomes.jsonl"
        if path.is_file():
            outcomes[arm] = {tuple(row["target"]): row for row in read_jsonl(path)}
    summary = {}
    for arm in ARMS[1:]:
        candidate = arm.split("-", 1)[0]
        reference = "context" if candidate == "expand" else "baseline"
        left_arm = arm.replace("expand", "context", 1) if candidate == "expand" else reference
        if left_arm not in outcomes or arm not in outcomes:
            continue
        left, right = outcomes[left_arm], outcomes[arm]
        shared = left.keys() & right.keys()
        fields = ["pair_sha256", "settings_sha256"]
        if candidate == "expand":
            fields.append("reference_selection_sha256")
        paired = [{"target": list(target), reference: left[target], candidate: right[target]}
                  for target in sorted(shared)
                  if all(field in left[target] and left[target][field] == right[target].get(field) for field in fields)]
        counts = Counter((row[reference]["verified"], row[candidate]["verified"]) for row in paired)
        summary[arm] = {
            "reference_arm": left_arm, "paired_targets": len(paired),
            f"{reference}_only_targets": len(left.keys() - right.keys()),
            f"{candidate}_only_targets": len(right.keys() - left.keys()),
            "incompatible_pairs": len(shared) - len(paired), "both_pass": counts[True, True],
            f"{reference}_pass_only": counts[True, False], f"{candidate}_pass_only": counts[False, True],
            "both_fail": counts[False, False], "outcomes": paired,
        }
    if summary:
        write_json(root / "comparison.json", summary)


def run_experiment(records, *, output, arm, helper_config, dataset_root, inspect_only,
                   native_config=None, llm=None, parallel=None, resume=True):
    if not records:
        raise ValueError("no matching extraction records")
    dataset = dataset_for(records[0])
    require_source(records, dataset.source)
    if any(row.get("pipeline") or row.get("metadata", {}).get("context_experiment")
           or has_dependency_context(row) or BUNDLE_FIELD in row for row in records):
        raise ValueError("provide original extraction records")
    mode = arm.split("-", 1)[0]
    if arm not in ARMS or arm != context_arm(native=arm in NATIVE_ARMS, cross_file=helper_config.cross_file, mode=mode):
        raise ValueError("experiment arm must match its mode, cross-file and native fact settings")
    if arm in NATIVE_ARMS and native_config is None:
        raise ValueError("native fact inspection requires a native configuration")
    if not inspect_only:
        check_outputs(output, arm, expected_source=dataset.source)
    prepared = prepare_records(records, helper_config, arm=arm, dataset_root=dataset_root)
    setup_s, prepared_native = 0.0, None
    if native_config is not None:
        plan = plan_parallel(native_config, **parallel)
        prepared_native, setup_s = check_native(
            prepared, arm=arm, config=native_config, plan=plan, output=output)
    exported, reports, blocked = export_selected(prepared, helper_config, dataset)
    write_jsonl(output / ("inspection.jsonl" if inspect_only else "selection.jsonl"), reports)
    summary = {"version": VERSION, "dataset": dataset.source, "arm": arm, "inspect_only": inspect_only,
               "targets": len(records),
               "blocked_targets": len(blocked), "selection_failures": dict(Counter(
                   failure["failure_category"] for failure in blocked.values())), "native_setup_s": setup_s}
    if mode == "expand":
        expansions = [report.get("source_helper_expansion", {}) for report in reports]
        summary.update(targets_with_source_helpers=sum(bool(item.get("included")) for item in expansions),
                       source_helpers=sum(len(item.get("included", ())) for item in expansions))
    if inspect_only:
        return summary
    inputs, sketches, verified = (output / filename for filename in ("inputs.jsonl", "sketches.jsonl", "verified.jsonl"))
    write_jsonl(inputs, exported)
    written = generate_sketches(
        input_path=str(inputs), output_path=str(sketches), samples=1, resume=resume,
        llm_config=llm, blocked_targets=blocked, sketch_source=MODE, expected_source=dataset.source,
        prompt_builder=dataset.prompt, prompt_version=dataset.prompt_version)
    results = prove_sketches(
        config=native_config, input_path=str(sketches), output_path=str(verified), prove_output=None,
        resume=resume, expected=exported, expected_samples=1, results_dir=str(output),
        sketch_source=MODE, expected_source=dataset.source, prepared_native=prepared_native, **parallel)
    # A cold baseline can create the HOL heap during setup. Pair on release,
    # sources, worker code and configuration rather than the pre-build heap list.
    backend = {name: value for name, value in prepared_native[0].items()
               if name not in {"backend_fingerprint", "session_heaps_sha256"}} if prepared_native else None
    settings = fingerprint([dataset.prompt_version, llm.to_metadata(), native_config.__dict__, parallel, backend,
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
    parser.add_argument("--dataset", choices=DATASETS, default="most-match")
    parser.add_argument("--dataset-root", default=DATASET_ROOT,
                        help="Local most-match root; its parent supplies Isabelle import snapshots")
    parser.add_argument("--records", required=True, help="Original extracted HOL Light to Isabelle records JSONL")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--helper-mode", choices=HELPER_MODES, default="context")
    parser.add_argument("--helper-config", help="Optional context experiment settings JSON")
    parser.add_argument("--cross-file", action=argparse.BooleanOptionalAction,
                        help="Follow pinned HOL Light load directives. Overrides cross_file in --helper-config.")
    parser.add_argument("--config", help="Native Isabelle2026 configuration for lab runs")
    parser.add_argument("--llm-config", help="API or vLLM profile for the existing direct sketch")
    parser.add_argument("--inspect-only", action="store_true", help="Write a selection comparison without inference")
    parser.add_argument("--native-facts", action="store_true", help="Resolve a shortlist in the native Isabelle context")
    parser.add_argument("--samples", type=int, choices=[1], default=1)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--output-dir", help="Parent directory for the experiment arms (defaults by dataset)")
    add_parallel_arguments(parser)
    parser.set_defaults(memory_per_worker_gb=None)
    args = parser.parse_args()
    if args.memory_per_worker_gb is None:
        args.memory_per_worker_gb = 4.0 if args.dataset == "babel-formal" else 12.0
    if args.native_facts and args.helper_mode == "baseline":
        parser.error("--native-facts requires --helper-mode context or expand")
    use_native = not args.inspect_only or args.native_facts
    if use_native and not args.config:
        parser.error("--config is required for a lab run or --native-facts")
    try:
        validate_layout(args.expected_root)
        helper_config = ContextConfig.load(args.helper_config)
        if args.cross_file is not None:
            helper_config = replace(helper_config, cross_file=args.cross_file)
        arm = context_arm(native=args.native_facts, cross_file=helper_config.cross_file, mode=args.helper_mode)
        records = load_inputs(args.records, mode=MODE, topic=args.topic, target_key=args.target_key, limit=args.limit)
        dataset = DATASETS[args.dataset]
        require_source(records, dataset.source)
        output = Path(args.output_dir or (dataset.results_dir + "/context_helpers")) / arm
        if any(has_reference_proofs(row) for row in records):
            output = reference_output(output)
        output = repo_path(output)
        input_paths = [args.records, args.config, args.llm_config, args.helper_config]
        if any(repo_path(path).is_relative_to(output) for path in input_paths if path):
            raise ValueError("keep input records and configurations outside the experiment arm directory")
        summary = run_experiment(records, output=output, arm=arm, helper_config=helper_config,
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
