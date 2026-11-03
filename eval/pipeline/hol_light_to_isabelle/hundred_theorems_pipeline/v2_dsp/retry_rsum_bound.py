"""Rerun only the two failed rsum_bound searches committed in 6300569.

No LLM calls, new sketches, separate context tests, capability controls or replay.
The old requests are checked against freshly extracted, proof-masked input before
using their unchanged sketches. Old runtime paths/settings are never executed.
"""
from __future__ import annotations

import argparse
import json

from ...babel_formal_pipeline.common import fingerprint, key, repo_path, validate_layout
from ...babel_formal_pipeline.theory_context import validate_context
from ...babel_formal_pipeline.v2_dsp.acceptance import ProofCase
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


def select_cases(config: DspConfig):
    records = extract_records(topic=TOPIC, target_key=TARGET, continue_on_error=False)
    if len(records) != 1:
        raise ValueError("expected exactly one current rsum_bound record")
    cases = [recorded_case(records[0], config, name, path) for name, path in LOGS]
    scope = {"selection": "failed_only", "dataset": "hundred-theorems",
             "selected_contexts": 1, "selected_targets": [list(key(records[0]))],
             "previous_commit": COMMIT, "failed_searches": [case.name for case in cases],
             "context_checks_requested": False,
             "note": "Only two previously failed searches; no model calls or separate context/control tests."}
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
    if args.plan_only:
        print(json.dumps({"scope": scope, "proof_searches": [c.name for c in cases],
                          "standalone_context_tests": [], "backend_controls": [],
                          "native_fixture": False, "report_root": args.output_root}, indent=2))
        return
    result = run_lab_preflight(config_path=args.config, records=records, scope=scope,
        output_root=args.output_root, workers=1, threads_per_worker=1, memory_per_worker_gb=12,
        dependency_jobs=1, dependency_threads=args.dependency_threads, warm_dependencies=True,
        controls_override=[], extra_proof_cases=cases,
        include_fixture=False, include_dataset_cases=False, include_contexts=False)
    print(json.dumps({name: result[name] for name in ("ok", "counts", "report_directory")}, indent=2))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
