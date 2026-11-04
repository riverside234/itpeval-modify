"""Retry failed rsum_bound sketches with general timeout and forced-Hammer probes.

No LLM calls, new generated sketches, broad context/capability controls or replay.
The old requests are checked against freshly extracted, proof-masked input before
using their unchanged sketches. Old runtime paths/settings are never executed.
"""
from __future__ import annotations

import argparse
import json

from ...babel_formal_pipeline.common import fingerprint, key, repo_path, validate_layout
from ...babel_formal_pipeline.theory_context import validate_context
from ...babel_formal_pipeline.sanitize_isabelle import sanitize_target
from ...babel_formal_pipeline.v2_dsp.acceptance import ProofCase, timeout_hammer_case
from ...babel_formal_pipeline.v2_dsp.export_dsp import export_record
from ...babel_formal_pipeline.v2_dsp.input_contract import normalize_sketch
from ...babel_formal_pipeline.v2_dsp.lab_preflight import run_lab_preflight
from ...babel_formal_pipeline.v2_dsp.native_search import read_result, resolve_imports
from ...babel_formal_pipeline.v2_dsp.runtime import DspConfig
from ..extract_hol_light import extract_records

COMMIT = "6300569dde128f9e9ec54e7af1c4e12a66c4efc5"
TOPIC = "015_the_fundamental_theorem_of_integral_calculus"
TARGET = "rsum_bound"
BASE = "eval/results/hol_light_to_isabelle_v2/hundred-theorems/"
LOGS = (
    ("rsum_bound_saved_search", BASE + "work/target-pk0im2_0/search"),
    ("rsum_bound_direct_search", BASE + "v2-dsp-isabelle2026/rsum-bound/direct/work/target-3zezl1b1/search"),
)
REPORT_ROOT = "eval/preflight_results/isabelle2026-rsum-bound"
FAILED_RUN = REPORT_ROOT + "/20261104T002751Z-cfc4b7f0"
TRIANGLE_PROBE = "rsum_bound_triangle_forced_hammer"


def recorded_case(record: dict, config: DspConfig, name: str, directory: str) -> ProofCase:
    path = repo_path(directory)
    request = json.loads((path / "input.json").read_text(encoding="utf-8"))
    digest = fingerprint({k: v for k, v in request.items() if k != "input_sha256"})
    if request.get("input_sha256") != digest:
        raise ValueError("recorded search request digest mismatch: " + directory)
    context = validate_context(record)
    prefix, _ = resolve_imports(context.prefix, config, theory_name=context.theory_name)
    expected = {"action": "search", "target_name": record["isabelle_target_name"],
                "prefix": prefix, "statement": context.statement, "proof_prefix": context.proof_prefix,
                "depth": str(context.depth)}
    for field, value in expected.items():
        if request.get(field) != value:
            raise ValueError("recorded search differs from current target context: " + field)
    previous = read_result(path / "result.xml", request, returncode=0)
    if previous["success"] or previous["target_closed"]:
        raise ValueError("refusing to rerun a successful recorded search")
    # This envelope supplies current source/context validation only. It is a
    # prover regression, not a new direct-mode generation or a Draft experiment.
    row = export_record(record, expected_source="hundred-theorems", sketch_source="hol-light-proof")
    row.update(isabelle_sketch=normalize_sketch(request["sketch"]), sample_idx=0,
               regression_provenance={"commit": COMMIT, "search_directory": directory,
                   "input_sha256": digest, "previous_failure": previous["failure_category"],
                   "generation": "unchanged recorded sketch; no model generation"})
    return ProofCase(name, row)


def triangle_hammer_case(record: dict) -> ProofCase:
    """Test the actual failed obligation with Hammer, without a heuristic shortcut.

    Use the same masked prefix/imports as the original target, but replace the
    target with this explicitly labelled, isolated proof-search regression. No
    rsum_bound fact or completed target proof enters the probe's context.
    """
    context = validate_context(record)
    name = "v2_rsum_triangle_probe"
    declaration = (
        "lemma " + name + ":\n"
        '  assumes fin: "finite p"\n'
        r'  shows "norm (\<Sum>(x,k)\<in>p. content k *\<^sub>R f x) \<le>' + "\n"
        r'    (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f x))"'
    )
    template = context.prefix + "\n" + declaration + "\n  sorry\n" + "end\n" * context.depth
    target = sanitize_target(template, name)
    raw = {
        "source": record["source"], "theorem_id": record["theorem_id"], "topic": record["topic"],
        "target_key": name, "isabelle_target_name": name,
        "isabelle_statement": target.statement, "isabelle_proof_prefix": target.proof_prefix,
        "isabelle_theory_template": template, "isabelle_context_before_target": target.context_before_target,
        "isabelle_target_proof_span": list(target.proof_span),
        "draft": "Apply the finite-sum triangle inequality to the pair-indexed summand.",
        "isabelle_sketch": "proof -\n  show ?thesis using fin\n    sledgehammer\nqed",
        "sample_idx": 0,
        "regression_provenance": {"run": FAILED_RUN, "target": TARGET,
            "kind": "isolated failed triangle obligation; hand-written regression, no LLM"},
    }
    row = export_record(raw, expected_source="hundred-theorems")
    return ProofCase(TRIANGLE_PROBE, row, force_hammer=True, hammer_kind="any", min_reconstructions=1)


def select_cases(config: DspConfig):
    records = extract_records(topic=TOPIC, target_key=TARGET, continue_on_error=False)
    if len(records) != 1:
        raise ValueError("expected exactly one current rsum_bound record")
    cases = [recorded_case(records[0], config, name, path) for name, path in LOGS]
    cases.append(triangle_hammer_case(records[0]))
    scope = {"selection": "failed_only", "dataset": "hundred-theorems",
             "selected_contexts": 1, "selected_targets": [list(key(records[0]))],
             "previous_commit": COMMIT, "previous_run": FAILED_RUN,
             "failed_searches": [name for name, _ in LOGS],
             "forced_hammer_probes": [TRIANGLE_PROBE],
             "context_checks_requested": False,
             "note": "Two failed sketches plus one forced-Hammer probe of their failed triangle gap; "
                     "no model calls, separate context tests or broad capability controls."}
    return records, cases, scope


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--config", default="eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json")
    parser.add_argument("--output-root", default=REPORT_ROOT)
    parser.add_argument("--dependency-threads", type=int, default=8)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args(argv)
    validate_layout(args.expected_root)
    config = DspConfig.load(args.config)
    records, cases, scope = select_cases(config)
    controls = [timeout_hammer_case(config)]
    scope["backend_regressions"] = [case.name for case in controls]
    scope["note"] += " Includes a general candidate-timeout-to-Sledgehammer regression."
    if args.plan_only:
        print(json.dumps({"scope": scope, "proof_searches": [c.name for c in cases],
                          "standalone_context_tests": [], "backend_controls": [c.name for c in controls],
                          "forced_hammer_probes": [c.name for c in cases if c.force_hammer],
                          "native_fixture": False, "report_root": args.output_root}, indent=2))
        return
    result = run_lab_preflight(config_path=args.config, records=records, scope=scope,
        output_root=args.output_root, workers=1, threads_per_worker=1, memory_per_worker_gb=12,
        dependency_jobs=1, dependency_threads=args.dependency_threads, warm_dependencies=True,
        controls_override=controls, extra_proof_cases=cases,
        include_fixture=False, include_dataset_cases=False, include_contexts=False)
    print(json.dumps({name: result[name] for name in ("ok", "counts", "report_directory")}, indent=2))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
