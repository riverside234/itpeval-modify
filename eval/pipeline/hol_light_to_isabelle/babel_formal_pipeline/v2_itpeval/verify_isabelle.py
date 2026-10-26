from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import (
    LAB_REPO_ROOT, RESULTS_DIR, align_samples, fingerprint, key, latest_records, public_record,
    read_jsonl, repo_path, require_source, save_results, select, summarize, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.generate_sketch import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import (
    input_metadata, normalize_body, validate_context,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.runtime import isabelle2024_runtime
from itpeval.itp import run_itp


DEFAULT_OUTPUT = RESULTS_DIR + "/v2-itpeval/babel_formal_v2_verified.jsonl"
VERIFY_VERSION = "babel_formal_v2_itpeval_verify_p2"


def normalize_proof(proof: str) -> str:
    return normalize_body(proof)


def compose_theory(record: dict, proof: str) -> str:
    return validate_context(record).theory(proof, full=True)


def _stage_theory(task_dir: Path, theory: str) -> None:
    match = re.search(r"(?m)^\s*theory\s+([A-Za-z_][A-Za-z_0-9]*)\b", theory)
    if not match:
        raise ValueError("Isabelle template has no theory declaration")
    name = match.group(1)
    (task_dir / f"{name}.thy").write_text(theory, encoding="utf-8")
    (task_dir / "ROOT").write_text(
        f'session "ITPEval_{name}" = HOL +\n  theories\n    {name}\n',
        encoding="utf-8",
    )


def compile_theory(theory: str, *, timeout_s: int = 1200, runtime: dict | None = None,
                   results_dir: str = RESULTS_DIR):
    runtime = runtime or isabelle2024_runtime()
    base = repo_path(results_dir + "/v2-itpeval/work")
    base.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="isabelle-v2-", dir=base) as directory:
        task_dir = Path(directory)
        _stage_theory(task_dir, theory)
        return run_itp(prover="isabelle", task_dir=task_dir, timeout_s=timeout_s,
                       prefix=Path(runtime["prefix"]))


def preflight(record: dict, *, timeout_s: int = 1200, runtime: dict | None = None, results_dir: str = RESULTS_DIR) -> dict:
    runtime = runtime or isabelle2024_runtime()
    template = validate_context(record).template
    baseline = compile_theory(template, timeout_s=timeout_s, runtime=runtime, results_dir=results_dir)
    if not baseline.ok:
        return {"baseline_ok": False, "negative_control_failed": None,
                "baseline_error": (baseline.stderr or baseline.stdout).strip()}
    invalid = compose_theory(record, "by (v2_missing_negative_control_method)")
    negative = compile_theory(invalid, timeout_s=timeout_s, runtime=runtime, results_dir=results_dir)
    return {"baseline_ok": True, "negative_control_failed": not negative.ok,
            "pipeline": "v2-itpeval", "backend_metadata": runtime,
            "negative_control_output": (negative.stderr or negative.stdout).strip()}


def verify_record(record: dict, *, timeout_s: int = 1200,
                  runtime: dict | None = None, results_dir: str = RESULTS_DIR) -> dict:
    result = public_record(record)
    result["pipeline"] = "v2-itpeval"
    result["verify_version"] = VERIFY_VERSION
    result["verify_timeout_s"] = timeout_s
    started = time.monotonic()
    stage = "rejected_proof"
    try:
        if record.get("pipeline") not in {None, "v2-itpeval"}:
            raise ValueError("cannot verify a different pipeline as v2-itpeval")
        if record.get("sketch_error"):
            raise ValueError(f"Sketch failed: {record['sketch_error']}")
        theory = compose_theory(record, record.get("isabelle_proof", ""))
        context = validate_context(record)
        result.update(context.metadata)
        if record.get("draft"):
            result.update(input_metadata(record))
        stage = "toolchain_error"
        runtime = runtime or isabelle2024_runtime()
        result["backend_metadata"] = runtime
        stage = "isabelle_failure"
        run = compile_theory(theory, timeout_s=timeout_s, runtime=runtime, results_dir=results_dir)
        result["verified"] = bool(run.ok)
        result["verify_error"] = "" if run.ok else (run.stderr or run.stdout or
                                                       f"Isabelle exited {run.returncode}").strip()
        result["verify_duration_seconds"] = round(run.duration_ms / 1000, 3)
        result["failure_category"] = None if run.ok else "isabelle_failure"
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError) as exc:
        result["verified"] = False
        result["verify_error"] = f"{type(exc).__name__}: {exc}"
        result["failure_category"] = record.get("failure_category") or (
            "timeout" if isinstance(exc, subprocess.TimeoutExpired) else
            stage)
        result["verify_duration_seconds"] = round(time.monotonic() - started, 3)
    return result


def verify_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT,
                    topic: str | None = None, target_key: str | None = None,
                    limit: int | None = None, timeout_s: int = 1200,
                    resume: bool = True, expected: list[dict] | None = None,
                    expected_samples: int | None = None, results_dir: str = RESULTS_DIR,
                    expected_source: str = "babel-formal") -> list[dict]:
    records = latest_records(input_path, samples=True, topic=topic,
                             target_key=target_key, limit=limit)
    records = align_samples(records, expected, expected_samples, pipeline="v2-itpeval")
    if not records:
        raise ValueError("no matching V2 Sketch records")
    require_source(records, expected_source)
    output = repo_path(output_path)
    previous = read_jsonl(output_path) if resume and output.exists() else []
    try:
        runtime = isabelle2024_runtime()
        runtime_error = None
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        runtime, runtime_error = None, exc
    completed = {r.get("verify_fingerprint"): r for r in previous
                 if r.get("pipeline") == "v2-itpeval" and r.get("verified")
                 and r.get("verify_version") == VERIFY_VERSION}
    results = []
    for index, record in enumerate(records, 1):
        result_key = fingerprint({
            "pipeline": "v2-itpeval", "target": key(record),
            "sample_idx": record["sample_idx"], "template": record.get("isabelle_theory_template"),
            "statement": record.get("isabelle_statement"), "draft": record.get("draft"),
            "prefix": record.get("isabelle_context_before_target"),
            "proof_span": record.get("isabelle_target_proof_span"),
            "proof_prefix": record.get("isabelle_proof_prefix", ""),
            "proof": record.get("isabelle_proof"), "sketch": record.get("sketch_fingerprint"),
            "runtime": runtime, "timeout": timeout_s, "version": VERIFY_VERSION,
            "source_metadata": record.get("metadata"), "input_pipeline": record.get("pipeline"),
            "sketch_error": record.get("sketch_error"),
        })
        try:
            validate_context(record)
            if record.get("draft"):
                input_metadata(record)
            valid_input = record.get("pipeline") in {None, "v2-itpeval"}
        except ValueError:
            valid_input = False
        verified = completed.get(result_key) if runtime_error is None and valid_input else None
        if verified is None:
            verified = verify_record(record, timeout_s=timeout_s, runtime=runtime, results_dir=results_dir)
        verified["verify_fingerprint"] = result_key
        results.append(verified)
        print(f"[{index}/{len(records)}] {'PASS' if verified['verified'] else 'FAIL'} "
              f"{record['topic']}/{record['target_key']} sample={record['sample_idx']}")
    save_results(output_path, results, expected=expected, expected_samples=expected_samples,
                 preserve_unselected=resume)
    return results


def main(*, legacy: bool = False, default_input: str = DEFAULT_INPUT,
         default_output: str = DEFAULT_OUTPUT, results_dir: str = RESULTS_DIR,
         expected_source: str = "babel-formal") -> None:
    parser = argparse.ArgumentParser(description="Compile generated V2 Isabelle proofs.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--input", default=(
        RESULTS_DIR + "/babel_formal_v2_sketches.jsonl" if legacy else default_input))
    parser.add_argument("--output", default=(
        RESULTS_DIR + "/babel_formal_v2_verified.jsonl" if legacy else default_output))
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--timeout-s", type=int, default=1200)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--preflight", action="store_true",
                        help="Compile a parsed masked theory, then confirm an invalid target proof fails.")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    if args.preflight:
        records = select(read_jsonl(args.input), topic=args.topic,
                         target_key=args.target_key, limit=1)
        if not records:
            parser.error("no matching parsed V2 record for preflight")
        require_source(records, expected_source)
        result = preflight(records[0], timeout_s=args.timeout_s, results_dir=results_dir)
        print(json.dumps(result, indent=2))
        if not result["baseline_ok"] or not result["negative_control_failed"]:
            raise SystemExit(1)
        return
    results = verify_sketches(
        input_path=args.input, output_path=args.output,
        topic=args.topic, target_key=args.target_key,
        limit=args.limit, timeout_s=args.timeout_s, resume=not args.no_resume,
        results_dir=results_dir, expected_source=expected_source)
    passed = sum(bool(r["verified"]) for r in results)
    print(f"Verified {passed}/{len(results)} Isabelle proof samples")
    print(json.dumps(summarize(results), indent=2))


if __name__ == "__main__":
    main()
