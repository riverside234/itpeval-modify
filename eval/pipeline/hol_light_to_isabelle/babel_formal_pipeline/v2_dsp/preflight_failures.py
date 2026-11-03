"""Select failed checks for a new, explicitly partial regression run.

This is not resume: no old success is trusted or copied, and checker changes
are allowed. Historical report paths are read-only selection evidence.
"""
from __future__ import annotations

import json
from ..common import repo_path, key, sha256
from .preflight_resume import context_identity


def select_failures(path, records, *, known_checks=()):
    path = repo_path(path)
    if path.is_dir():
        path = path / "report.json"
    content = path.read_text(encoding="utf-8")
    report = json.loads(content)
    if not isinstance(report, dict) or not isinstance(report.get("checks"), list):
        raise ValueError("failed-from must be an Isabelle preflight report with checks")
    failures = [row for row in report["checks"] if row.get("status") == "fail"]
    if not failures:
        raise ValueError("the selected report has no failed checks")
    current = {key(row): row for row in records}
    if len(current) != len(records):
        raise ValueError("duplicate current targets in failure-only input")
    selected, names, changed = {}, set(), []
    known = set(known_checks) | {"input_selection", "metadata", "dependencies", "infrastructure", "import_heaps"}
    for row in failures:
        name = row.get("name")
        if not isinstance(name, str) or name in names:
            raise ValueError("invalid/duplicate failed check in report")
        names.add(name)
        if row.get("domain") == "context":
            target = tuple(row.get("target", ()))
            if target not in current:
                raise ValueError("failed context not found in current selection: " + str(target))
            if target in selected:
                raise ValueError("duplicate failed target in report: " + str(target))
            selected[target] = current[target]
            if row.get("context_fingerprint") != context_identity(current[target]):
                changed.append(list(target))
        elif name not in known:
            raise ValueError("failed check has no current implementation: " + name)
    info = {"report": str(path), "report_sha256": sha256(content),
            "previous_checker_version": report.get("checker_version"),
            "previous_context_counts": report.get("context_counts", {}),
            "failed_checks": sorted(names), "selected_contexts": len(selected),
            "previous_passes_not_revalidated": sum(row.get("status") == "pass" for row in report["checks"]),
            "changed_context_inputs": changed,
            "note": "Only prior failures are tested; prerequisite setup still runs. No previous pass is reused or revalidated."}
    return [selected[k] for k in sorted(selected)], info
