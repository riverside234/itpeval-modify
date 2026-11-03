"""Reuse successful contexts only with matching inputs and checked backend identity.

Older compact reports truncated context fingerprints. For those reports the
original lab's checks.full.jsonl and backend.json are required; names alone are
never evidence of input/toolchain equivalence.
"""
from __future__ import annotations

import json
from pathlib import Path

from ..common import fingerprint, key, repo_path, sha256
from .checker import CHECKER_VERSION


def backend_identity(backend):
    # A report-only commit must not invalidate identical checker/source hashes.
    return fingerprint({k: v for k, v in backend.items()
                        if k not in {"backend_fingerprint", "itpeval_commit"}})


def context_identity(record):
    return fingerprint({"target": key(record), **{name: record.get(name) for name in (
        "isabelle_target_name", "isabelle_theory_template", "isabelle_statement",
        "isabelle_context_before_target", "isabelle_proof_prefix", "isabelle_target_proof_span")}})


def read_report(path):
    path = repo_path(path)
    if path.is_dir():
        path = path / "report.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    if report.get("checker_version") != CHECKER_VERSION:
        raise ValueError("resume report uses a different checker version; run a fresh preflight")
    successes = {}
    for row in report.get("checks", []):
        if row.get("domain") == "context" and row.get("status") == "pass":
            target = tuple(row.get("target", ()))
            if len(target) != 4 or target in successes:
                raise ValueError("invalid/duplicate successful context in resume report")
            successes[target] = row
    return path, report, successes


def preview_resume(path):
    report_path, report, successes = read_report(path)
    return {"report": str(report_path), "previous_passed_contexts": len(successes),
            "legacy_local_artifacts_required": not bool(report.get("resume_backend_fingerprint")),
            "note": "Eligibility is checked against current inputs and backend at runtime."}


def load_reusable(path, records, backend):
    report_path, report, successes = read_report(path)
    current = {key(row): row for row in records}
    selected = set(successes) & set(current)
    summary = {"report": str(report_path), "previous_passed_contexts": len(successes),
               "selected_previous_passes": len(selected), "reused_contexts": 0, "rerun_contexts": len(records)}
    reusable = {}
    def remember(target, old, method):
        reusable[target] = {"report": str(report_path), "check": old["name"],
            "method": method, "original_duration_seconds": old.get("duration_seconds", 0)}
    identity = backend_identity(backend)
    if report.get("resume_backend_fingerprint"):
        if report["resume_backend_fingerprint"] != identity:
            summary["reason"] = "backend/config/checker inputs changed; rerunning all contexts"
        else:
            for target in selected:
                old = successes[target]
                if old.get("context_fingerprint") == context_identity(current[target]):
                    remember(target, old, "fingerprint")
    elif selected:
        # Interrupted v4 reports have no metadata.json yet. The immutable full
        # payloads in the lab-local work directory contain the missing evidence.
        try:
            work = repo_path(report["local_artifacts"])
            previous_backend = json.loads((work / "backend.json").read_text(encoding="utf-8"))
            full = work / "checks.full.jsonl"
            if not full.is_file():
                raise FileNotFoundError(full)
        except (KeyError, OSError, ValueError) as exc:
            raise ValueError("legacy resume requires the original lab-local backend.json and "
                             "checks.full.jsonl under local_artifacts; keep that directory or run without --resume-from") from exc
        if backend_identity(previous_backend) != identity:
            summary["reason"] = "legacy backend/config/checker inputs changed; rerunning all contexts"
        else:
            with full.open(encoding="utf-8") as stream:
                for line in stream:
                    try:
                        saved = json.loads(line)
                    except json.JSONDecodeError:
                        # A process may have been killed during its final append.
                        continue
                    target = tuple(saved.get("target", ()))
                    if target not in selected or saved.get("domain") != "context" or saved.get("status") != "pass":
                        continue
                    old = successes[target]
                    if saved.get("name") != old["name"] or saved.get("details_line") != old.get("details_line"):
                        continue
                    result = saved.get("payload", {}).get("result", {})
                    row = current[target]
                    if (result.get("baseline_ok") is True
                            and result.get("native_result", {}).get("success") is True
                            and result.get("background_policy") == "earlier_masked_helpers_admitted"
                            and all(result.get(saved_name) == sha256(row[field]) for saved_name, field in (
                                ("context_sha256", "isabelle_context_before_target"),
                                ("statement_sha256", "isabelle_statement"),
                                ("template_sha256", "isabelle_theory_template")))):
                        remember(target, old, "legacy_full_payload")
    summary.update(reused_contexts=len(reusable), rerun_contexts=len(records) - len(reusable))
    return reusable, summary
