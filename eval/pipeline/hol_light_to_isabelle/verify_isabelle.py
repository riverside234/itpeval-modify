from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, RESULTS_DIR, key, read_jsonl, repo_path, select,
    validate_layout, write_jsonl,
)
from eval.pipeline.hol_light_to_isabelle.generate_sketch import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.prompt import normalize_visible_content
from itpeval.itp import run_itp


DEFAULT_OUTPUT = RESULTS_DIR + "/babel_formal_v2_verified.jsonl"
VERIFY_VERSION = "babel_formal_v2_isabelle_verify_p1"
FORBIDDEN = re.compile(
    r"\b(?:sorry|oops|admit|axiomatization|axioms|oracle|theory|locale|"
    r"theorem|lemma|corollary|proposition|definition|ML|ML_file)\b",
    re.IGNORECASE,
)
TOP_LEVEL = re.compile(
    r"(?mi)^\s*(?:end|context|section|subsection|notepad|declare|"
    r"interpretation|fun|primrec|datatype|record|class|instance|text)\b"
)


def normalize_proof(proof: str) -> str:
    value = normalize_visible_content(proof)
    if not value:
        raise ValueError("empty Isabelle proof")
    if FORBIDDEN.search(value) or TOP_LEVEL.search(value):
        raise ValueError("proof contains admission or forbidden declaration")
    if not re.match(r"\A(?:by|proof)\b", value):
        raise ValueError("proof body must start with by or proof")
    if value.startswith("proof") and not re.search(r"\bqed\s*\Z", value):
        raise ValueError("structured proof must end with qed")
    return value


def compose_theory(record: dict, proof: str) -> str:
    template = record["isabelle_theory_template"]
    start, end = record["isabelle_target_proof_span"]
    if not isinstance(template, str) or template[start:end] != "sorry":
        raise ValueError("stale or invalid Isabelle target proof span")
    body = normalize_proof(proof)
    return template[:start] + body + template[end:]


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


def compile_theory(theory: str, *, timeout_s: int = 1200):
    base = repo_path(RESULTS_DIR)
    base.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="isabelle-v2-", dir=base) as directory:
        task_dir = Path(directory)
        _stage_theory(task_dir, theory)
        return run_itp(prover="isabelle", task_dir=task_dir, timeout_s=timeout_s)


def preflight(record: dict, *, timeout_s: int = 1200) -> dict:
    template = record["isabelle_theory_template"]
    start, end = record["isabelle_target_proof_span"]
    if template[start:end] != "sorry":
        raise ValueError("stale or invalid Isabelle target proof span")
    baseline = compile_theory(template, timeout_s=timeout_s)
    if not baseline.ok:
        return {"baseline_ok": False, "negative_control_failed": None,
                "baseline_error": (baseline.stderr or baseline.stdout).strip()}
    invalid = compose_theory(record, "by (rule FalseE)")
    negative = compile_theory(invalid, timeout_s=timeout_s)
    return {"baseline_ok": True, "negative_control_failed": not negative.ok,
            "negative_control_output": (negative.stderr or negative.stdout).strip()}


def verify_record(record: dict, *, timeout_s: int = 1200) -> dict:
    result = dict(record)
    result["verify_version"] = VERIFY_VERSION
    result["verify_timeout_s"] = timeout_s
    started = time.monotonic()
    try:
        if record.get("sketch_error"):
            raise ValueError(f"Sketch failed: {record['sketch_error']}")
        theory = compose_theory(record, record.get("isabelle_proof", ""))
        run = compile_theory(theory, timeout_s=timeout_s)
        result["verified"] = bool(run.ok)
        result["verify_error"] = "" if run.ok else (run.stderr or run.stdout or
                                                       f"Isabelle exited {run.returncode}").strip()
        result["verify_duration_seconds"] = round(run.duration_ms / 1000, 3)
    except (ValueError, FileNotFoundError, RuntimeError, OSError, subprocess.TimeoutExpired) as exc:
        result["verified"] = False
        result["verify_error"] = f"{type(exc).__name__}: {exc}"
        result["verify_duration_seconds"] = round(time.monotonic() - started, 3)
    return result


def verify_sketches(*, input_path: str = DEFAULT_INPUT, output_path: str = DEFAULT_OUTPUT,
                    topic: str | None = None, target_key: str | None = None,
                    limit: int | None = None, timeout_s: int = 1200,
                    resume: bool = True) -> list[dict]:
    latest = {}
    for record in read_jsonl(input_path):
        latest[(key(record), int(record["sample_idx"]))] = record
    records = select(latest.values(), topic=topic, target_key=target_key)
    if limit is not None:
        if limit < 1:
            raise ValueError("limit must be positive")
        target_keys = list(dict.fromkeys(key(r) for r in records))[:limit]
        records = [r for r in records if key(r) in target_keys]
    if not records:
        raise ValueError("no matching V2 Sketch records")
    output = repo_path(output_path)
    previous = read_jsonl(output_path) if resume and output.exists() else []
    completed = {
        (key(r), int(r["sample_idx"]), r.get("sketch_prompt_sha256"),
         r.get("isabelle_proof"), r.get("verify_timeout_s")): r
        for r in previous if r.get("verify_version") == VERIFY_VERSION
    }
    results = []
    for index, record in enumerate(records, 1):
        result_key = (key(record), int(record["sample_idx"]),
                      record.get("sketch_prompt_sha256"), record.get("isabelle_proof"),
                      timeout_s)
        verified = completed.get(result_key)
        if verified is None:
            verified = verify_record(record, timeout_s=timeout_s)
        results.append(verified)
        print(f"[{index}/{len(records)}] {'PASS' if verified['verified'] else 'FAIL'} "
              f"{record['topic']}/{record['target_key']} sample={record['sample_idx']}")
    write_jsonl(output_path, results)
    summary = summarize(results)
    output.with_suffix(".summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return results


def summarize(records: list[dict]) -> dict:
    groups: dict[tuple, list[dict]] = {}
    failures: dict[str, int] = {}
    for record in records:
        groups.setdefault(key(record), []).append(record)
        if record.get("verified"):
            continue
        error = str(record.get("verify_error", ""))
        if record.get("sketch_error"):
            category = "sketch_error"
        elif error.startswith("ValueError:"):
            category = "rejected_proof"
        elif error.startswith("TimeoutExpired:"):
            category = "timeout"
        else:
            category = "isabelle_failure"
        failures[category] = failures.get(category, 0) + 1
    passed_one = sum(any(r.get("verified") and r.get("sample_idx") == 0
                         for r in group) for group in groups.values())
    passed_k = sum(any(r.get("verified") for r in group) for group in groups.values())
    total = len(groups)
    return {
        "targets": total, "samples": len(records),
        "verified_samples": sum(bool(r.get("verified")) for r in records),
        "pass_at_1_count": passed_one, "pass_at_1": passed_one / total if total else 0,
        "pass_at_k_count": passed_k, "pass_at_k": passed_k / total if total else 0,
        "failure_counts": failures,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Compile generated V2 Isabelle proofs.")
    parser.add_argument("--expected-root", help=f"Expected repo root (lab: {LAB_REPO_ROOT}).")
    parser.add_argument("--input", default=DEFAULT_INPUT)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
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
        result = preflight(records[0], timeout_s=args.timeout_s)
        print(json.dumps(result, indent=2))
        if not result["baseline_ok"] or not result["negative_control_failed"]:
            raise SystemExit(1)
        return
    results = verify_sketches(
        input_path=args.input, output_path=args.output,
        topic=args.topic, target_key=args.target_key,
        limit=args.limit, timeout_s=args.timeout_s, resume=not args.no_resume)
    passed = sum(bool(r["verified"]) for r in results)
    print(f"Verified {passed}/{len(results)} Isabelle proof samples")
    print(json.dumps(summarize(results), indent=2))


if __name__ == "__main__":
    main()
