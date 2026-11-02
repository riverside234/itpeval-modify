"""Compact completed legacy preflight runs without deleting full local diagnostics.

Does not change Git's index, commits, branches, or remotes. See the report README
for removing oversized files from an already rejected, unpushed commit.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import uuid

from .common import repo_path, validate_layout
from .preflight_storage import ReportStorage, append_jsonl, compact, excerpt, write_json, write_bytes


def compact_run(path):
    source = repo_path(path)
    root = repo_path("eval/preflight_results")
    if not source.is_relative_to(root) or len(source.relative_to(root).parts) != 2:
        raise ValueError("Expected one run directory: eval/preflight_results/<backend>/<run-id>")
    report_path = source / "report.json"
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if report.get("report_format") == "compact_v1":
        return {"run": str(source), "already_compact": True}
    if report.get("status") not in {"complete", "interrupted"}:
        raise ValueError("Only completed or interrupted runs can be compacted; stop the active preflight first")
    if not isinstance(report.get("checks"), list):
        raise ValueError("Missing preflight checks")
    tag = uuid.uuid4().hex
    backup = repo_path(Path("itpeval/.runs/preflight_archives") / source.parent.name / (source.name + "-" + tag))
    staging = repo_path(Path("itpeval/.runs/preflight_compaction") / tag)
    if backup.exists() or staging.exists():
        raise FileExistsError("Compaction backup/staging path already exists")
    staging.mkdir(parents=True)
    storage = ReportStorage(staging, work_path=source)
    rows = []
    for index, old in enumerate(report["checks"], 1):
        detail = (source / old["details"]).resolve()
        if not detail.is_relative_to(source):
            raise ValueError("Detail path escapes the report directory")
        payload = json.loads(detail.read_text(encoding="utf-8")).get("payload", {})
        row = {**old, "details": "checks.jsonl", "details_line": index}
        if row.get("error"):
            row["error"] = excerpt(row["error"])
        append_jsonl(staging / "checks.jsonl", {**row, "payload": compact(payload)})
        rows.append(row)
    storage.finish()
    metadata = json.loads((staging / "metadata.json").read_text(encoding="utf-8"))
    metadata["local_artifacts"] = str(backup)
    write_json(staging / "metadata.json", metadata)
    unavailable = [r for r in rows if r["status"] == "unavailable_context"]
    report.update(checks=rows, diagnostic_bundle=None, report_format="compact_v1",
                  local_artifacts=str(backup), report_directory=str(source),
                  log_export=metadata["log_export"], unavailable_contexts=unavailable)
    write_json(staging / "report.json", report)
    write_json(staging / "unavailable_contexts.json", unavailable)
    lines = ["# Compacted preflight report", "", f"Status: **{report['status']}**; overall OK: **{report.get('ok')}**.",
             "", "Existing check outcomes and cohort counts are preserved in report.json.",
             "Details are in checks.jsonl; bounded log excerpts are in logs.jsonl.",
             "", f"Full original run, including diagnostics.zip, retained locally: `{backup}`.",
             "", "| Check | Domain | Status | Error |", "| --- | --- | --- | --- |"]
    for row in rows:
        error = " ".join(row.get("error", "").split()).replace("|", "&#124;")[:240]
        lines.append(f"| {row['name']} | {row['domain']} | {row['status']} | {error} |")
    write_bytes(staging / "summary.md", ("\n".join(lines) + "\n").encode("utf-8"))
    # Both resolved destinations are inside the repository, and the backup is new.
    # Rename only after all compact output has been generated successfully.
    backup.parent.mkdir(parents=True, exist_ok=True)
    source.rename(backup)
    try:
        staging.rename(source)
    except BaseException:
        backup.rename(source)
        raise
    return {"run": str(source), "local_backup": str(backup),
            "report_files": len(list(source.iterdir())), "checks": len(rows)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--run", action="append", required=True, help="Completed run directory; repeat for multiple runs")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    for path in args.run:
        print(json.dumps(compact_run(path), indent=2))


if __name__ == "__main__":
    main()
