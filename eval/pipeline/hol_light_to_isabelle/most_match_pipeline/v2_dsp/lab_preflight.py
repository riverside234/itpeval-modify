"""Representative long-file preflight: real imports, scopes, caps and native search."""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
from ..common import RESULTS_DIR, SOURCE, key, latest_records, require_source, validate_layout, repo_path
from ..context import validate_prompt_context
from ..extract_hol_light import extract_records, add_extraction_arguments, extraction_options
from ...babel_formal_pipeline.theory_context import validate_context
from ...babel_formal_pipeline.v2_dsp.acceptance import proof_cases, ProofCase
from ...babel_formal_pipeline.v2_dsp.export_dsp import export_record
from ...babel_formal_pipeline.v2_dsp.lab_preflight import run_lab_preflight
from ...babel_formal_pipeline.v2_dsp.parallel import add_parallel_arguments, parallel_options, plan_parallel
from ...babel_formal_pipeline.v2_dsp.runtime import DspConfig

DEFAULT_CONFIG = "eval/configs/hol_light_to_isabelle/v2_dsp_most_match_2026.example.json"
DEFAULT_REPORT_ROOT = "eval/preflight_results/isabelle2026-most-match"
CONTROL_NAMES = {
    "explicit_draft", "explicit_direct", "hammer_configured", "hammer_external_e",
    "using_reconstruction_comments", "multiple_subgoals", "invalid_method",
    "admission_rejected", "self_reference_rejected", "later_fact_rejected", "inherited_theory_search",
}


def select_contexts(records, *, all_targets=False):
    groups = defaultdict(list)
    for row in records:
        groups[row["topic"]].append(row)
    selected, reasons = {}, defaultdict(list)
    def add(row, reason):
        selected[key(row)] = row
        reasons[key(row)].append(reason)
    for topic, rows in sorted(groups.items()):
        ordered = sorted(rows, key=lambda r: (r["metadata"]["isabelle_line_start"], r["target_key"]))
        if all_targets:
            for row in ordered:
                add(row, "all targets")
            continue
        add(ordered[0], "first declaration")
        add(ordered[len(ordered)//2], "middle declaration")
        add(ordered[-1], "last/largest verifier prefix")
        add(max(rows, key=lambda r: len(r["hol_light_proof"])), "longest selected HOL proof")
        add(max(rows, key=lambda r: validate_context(r).depth), "deepest active Isabelle scope")
        # Every distinct source library in a split topic is represented.
        libraries = defaultdict(list)
        for row in rows:
            libraries[row["metadata"]["hol_light_proof_path"]].append(row)
        for library in libraries.values():
            add(max(library, key=lambda r: len(r["isabelle_context_before_target"])), "source library coverage")
    scope = {"dataset": SOURCE, "selection": "all_targets" if all_targets else "first_middle_last_longest_proof_deepest_scope_per_topic",
        "available_targets": len(records), "selected_contexts": len(selected), "selected_topics": len(groups),
        "targets": [list(k) for k in sorted(selected)],
        "selection_reasons": [{"target": list(k), "reasons": reasons[k]} for k in sorted(selected)]}
    return [selected[k] for k in sorted(selected)], scope


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--dataset", choices=("most-match",), default="most-match")
    parser.add_argument("--config", default=DEFAULT_CONFIG)
    parser.add_argument("--input", help="Optional saved extraction; omitted means fresh extraction")
    add_extraction_arguments(parser)
    add_parallel_arguments(parser)
    parser.add_argument("--all-targets", action="store_true")
    parser.add_argument("--expected-contexts", type=int)
    parser.add_argument("--output-root", default=DEFAULT_REPORT_ROOT)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args(argv)
    validate_layout(args.expected_root)
    coverage = {}
    if args.input:
        records = latest_records(args.input, topic=args.topic, target_key=args.target_key)
        coverage["input"] = args.input
    else:
        records = extract_records(**extraction_options(args), report=coverage)
    require_source(records, SOURCE)
    issues = [issue for topic in coverage.get("topics", []) for issue in topic["issues"]]
    if not records:
        issues.append({"error": "empty candidate selection"})
    for row in records:
        try:
            validate_context(row)
            validate_prompt_context(row)
        except ValueError as exc:
            issues.append({"target": key(row), "error": str(exc)})
    selected, scope = select_contexts(records, all_targets=args.all_targets)
    scope["coverage"] = coverage
    if args.expected_contexts is not None and len(selected) != args.expected_contexts:
        issues.append({"error": f"expected {args.expected_contexts} contexts, selected {len(selected)}"})
    config = DspConfig.load(args.config)
    plan = plan_parallel(config, **parallel_options(args))
    controls = [case for case in proof_cases() if case.name in CONTROL_NAMES]
    # A deterministic proof in a real dataset context complements synthetic controls.
    # It is used only for preflight and never supplies target proof text to prompts.
    proofs = []
    sentinel = next((r for r in records if r["topic"] == "Cross3" and r["target_key"] == "cross_refl"), None)
    if sentinel:
        row = export_record({**sentinel, "sample_idx": 0,
                             "isabelle_sketch": "by (simp add: cross3_simps)"},
                            expected_source=SOURCE, sketch_source="hol-light-proof")
        proofs.append(ProofCase("most_match_cross_refl", row))
    if args.plan_only:
        print(json.dumps({"scope": scope, "issues": issues, "parallelism": plan.metadata(),
                          "backend_controls": [c.name for c in controls],
                          "dataset_proofs": [c.name for c in proofs],
                          "output_root": str(repo_path(args.output_root))}, indent=2))
        raise SystemExit(1 if issues else 0)
    result = run_lab_preflight(config_path=args.config, records=selected, scope=scope,
        selection_issues=issues, output_root=args.output_root, controls_override=controls,
        extra_proof_cases=proofs, warm_dependencies=True, **parallel_options(args))
    raise SystemExit(130 if result["status"] == "interrupted" else 0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
