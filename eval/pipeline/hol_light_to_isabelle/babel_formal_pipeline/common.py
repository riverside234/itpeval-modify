from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Iterable

from eval.pipeline.config import REPO_ROOT


LAB_REPO_ROOT = "/data/not_backed_up/yxu209/ITPEval"
RESULTS_DIR = "eval/results/hol_light_to_isabelle_v2"


def validate_layout(expected_root: str | None = None) -> Path:
    root = REPO_ROOT.resolve()
    if expected_root and root != Path(expected_root).expanduser().resolve():
        raise ValueError(f"expected repository {expected_root}, found {root}")
    for name in ("eval/data/proofs.json", "eval/data/stmts.json"):
        if not (root / name).is_file():
            raise FileNotFoundError(root / name)
    return root


def repo_path(path: str | Path) -> Path:
    root = REPO_ROOT.resolve()
    candidate = Path(path).expanduser()
    resolved = (candidate if candidate.is_absolute() else root / candidate).resolve()
    if not resolved.is_relative_to(root):
        raise ValueError(f"path must be under {root}: {resolved}")
    return resolved


def require_source(records: Iterable[dict], source: str) -> None:
    for record in records:
        if record.get("source") != source:
            raise ValueError(f"expected {source} input, found {record.get('source')!r}")


def sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def key(record: dict[str, Any]) -> tuple[str, int, str, str]:
    return (str(record["source"]), int(record["theorem_id"]),
            str(record["topic"]), str(record["target_key"]))


def select(records: Iterable[dict[str, Any]], *, topic: str | None = None,
           target_key: str | None = None, limit: int | None = None) -> list[dict[str, Any]]:
    selected = [r for r in records if (topic is None or r["topic"] == topic)
                and (target_key is None or r["target_key"] == target_key)]
    if limit is not None and limit < 1:
        raise ValueError("limit must be positive")
    return selected[:limit]


def read_jsonl(path: str | Path) -> list[dict[str, Any]]:
    result = []
    with repo_path(path).open(encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            if line.strip():
                value = json.loads(line)
                if not isinstance(value, dict):
                    raise ValueError(f"expected object at {path}:{number}")
                result.append(value)
    return result


def append_jsonl(path: str | Path, record: dict[str, Any]) -> None:
    destination = repo_path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(record, ensure_ascii=False) + "\n")


def write_jsonl(path: str | Path, records: Iterable[dict[str, Any]]) -> Path:
    destination = repo_path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("w", encoding="utf-8") as stream:
        for record in records:
            stream.write(json.dumps(record, ensure_ascii=False) + "\n")
    return destination


def prompt_hash(system: str, user: str) -> str:
    return sha256(system + "\n\n" + user)


def fingerprint(value: Any) -> str:
    return sha256(json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":")))


def repository_commit() -> str | None:
    try:
        run = subprocess.run(["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"],
                             capture_output=True, text=True, check=True, timeout=10)
        return run.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return None


def public_record(record: dict) -> dict:
    omitted = {"system_prompt", "user_prompt", "thinking", "reasoning_content", "raw_response"}
    return {name: value for name, value in record.items() if name not in omitted}


def latest_records(path: str | Path, *, samples: bool = False, **filters) -> list[dict]:
    latest = {}
    for record in read_jsonl(path):
        identity = (key(record), int(record["sample_idx"])) if samples else key(record)
        latest[identity] = record
    limit = filters.pop("limit", None)
    records = select(latest.values(), **filters)
    if limit is not None:
        if limit < 1:
            raise ValueError("limit must be positive")
        wanted = list(dict.fromkeys(key(record) for record in records))[:limit]
        records = [record for record in records if key(record) in wanted]
    return records


def align_samples(records: list[dict], expected: list[dict] | None,
                  samples: int | None, *, pipeline: str) -> list[dict]:
    if expected is None:
        return records
    if samples is None or samples < 1:
        raise ValueError("expected_samples must be positive with an expected cohort")
    latest = {(key(record), int(record["sample_idx"])): record for record in records}
    fields = ("draft", "isabelle_statement", "isabelle_theory_template",
              "isabelle_context_before_target", "isabelle_proof_prefix",
              "isabelle_target_proof_span", "metadata")
    result = []
    for target in expected:
        for index in range(samples):
            record = latest.get((key(target), index))
            if record is not None and all(
                record.get(field, "" if field == "isabelle_proof_prefix" else None)
                == target.get(field, "" if field == "isabelle_proof_prefix" else None)
                for field in fields
            ):
                result.append(record)
            else:
                result.append({
                    **public_record(target), "pipeline": pipeline, "sample_idx": index,
                    "sketch_error": "missing or stale Sketch for this saved Draft/context",
                    "failure_category": "missing_sketch",
                })
    return result


def summarize(records: list[dict], *, expected: list[dict] | None = None,
              expected_samples: int | None = None) -> dict:
    groups: dict[tuple, list[dict]] = {key(record): [] for record in expected or []}
    failures: dict[str, int] = {}
    for record in records:
        groups.setdefault(key(record), []).append(record)
        if not record.get("verified"):
            category = record.get("failure_category") or (
                "sketch_error" if record.get("sketch_error") else "verification_failure")
            failures[category] = failures.get(category, 0) + 1
    one = sum(any(row.get("verified") and row.get("sample_idx") == 0 for row in rows)
              for rows in groups.values())
    many = sum(any(row.get("verified") for row in rows) for rows in groups.values())
    total = len(groups)
    result = {
        "targets": total, "samples": len(records),
        "verified_samples": sum(bool(row.get("verified")) for row in records),
        "pass_at_1_count": one, "pass_at_1": one / total if total else 0,
        "pass_at_k_count": many, "pass_at_k": many / total if total else 0,
        "metric": "empirical first-sample success and success among generated K samples",
        "failure_counts": failures,
    }
    if expected_samples is not None:
        result["expected_samples_per_target"] = expected_samples
        result["missing_samples"] = sum(
            len(set(range(expected_samples)) - {int(row["sample_idx"]) for row in rows})
            for rows in groups.values())
    return result


def save_results(path: str | Path, records: list[dict], *,
                 preserve_unselected: bool = False, **summary_options) -> dict:
    stored = records
    output = repo_path(path)
    if preserve_unselected and output.is_file():
        active = {(row.get("pipeline"), key(row), int(row["sample_idx"])) for row in records}
        retained = [row for row in read_jsonl(path)
                    if (row.get("pipeline"), key(row), int(row["sample_idx"])) not in active]
        stored = retained + records
    output = write_jsonl(path, [public_record(record) for record in stored])
    summary = summarize(records, **summary_options)
    output.with_suffix(".summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return summary
