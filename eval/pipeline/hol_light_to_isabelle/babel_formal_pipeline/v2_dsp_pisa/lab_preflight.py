"""One original DSP/PISA Isabelle2021 acceptance run, saved with portable diagnostics."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import time
import uuid
import zipfile

from ..common import fingerprint, key, latest_records, repo_path, validate_layout
from .acceptance import dataset_cases, proof_cases, run_proof_case
from .checker import CHECKER_VERSION, Checker
from .runtime import DspConfig, PACKAGE, PisaFailure, hash_file

REPORT_VERSION = "dsp_pisa_isabelle2021_lab_preflight_v1"
DEFAULT_REPORT_ROOT = "eval/preflight_results/pisa_isabelle2021"
SENTINELS = {
    ("babel-formal", "circle_average"): "circleAverage_center_independent",
    ("hundred-theorems", "030_the_ballot_problem"): "all_countings",
    ("hundred-theorems", "015_the_fundamental_theorem_of_integral_calculus"): "rsum_bound",
}


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def discover_records(*, dataset="both", inputs=(), topic=None, target_key=None, all_targets=False):
    rows, issues = [], []
    if inputs:
        for path in inputs:
            try:
                rows.extend(latest_records(path))
            except Exception as exc:
                issues.append({"input": str(path), "error": f"{type(exc).__name__}: {exc}"})
    else:
        if dataset in {"both", "babel-formal"}:
            from ..extract_hol_light import extract_records
            try:
                rows.extend(extract_records())
            except Exception as exc:
                issues.append({"source": "babel-formal", "error": f"{type(exc).__name__}: {exc}"})
        if dataset in {"both", "hundred-theorems"}:
            from ...hundred_theorems_pipeline.extract_hol_light import extract_records
            coverage = {}
            try:
                rows.extend(extract_records(report=coverage))
            except Exception as exc:
                issues.append({"source": "hundred-theorems", "error": f"{type(exc).__name__}: {exc}"})
            for group in coverage.get("file_groups", []):
                for issue in group.get("issues", []):
                    issues.append({"source": "hundred-theorems", "topic": group["topic"], **issue})
    unique = {}
    for row in rows:
        try:
            identity = key(row)
            if row["source"] not in {"babel-formal", "hundred-theorems"}:
                raise ValueError("unsupported dataset: " + row["source"])
            if dataset != "both" and row["source"] != dataset:
                continue
            if (topic and row["topic"] != topic) or (target_key and row["target_key"] != target_key):
                continue
            if identity in unique and fingerprint(unique[identity]) != fingerprint(row):
                raise ValueError("conflicting duplicate target across input files: " + str(identity))
            unique[identity] = row
        except Exception as exc:
            issues.append({"error": f"{type(exc).__name__}: {exc}"})
    available = list(unique.values())
    chosen = {}
    if all_targets:
        chosen = unique
    else:
        # The longest prefix covers the most preceding declarations in each topic.
        # Keep the concrete historical regression targets as extra sentinels.
        groups = {}
        for row in available:
            group = (row["source"], row["topic"])
            previous = groups.get(group)
            if previous is None or len(row.get("isabelle_context_before_target", "")) > len(previous.get("isabelle_context_before_target", "")):
                groups[group] = row
            if row["target_key"] == SENTINELS.get(group):
                chosen[key(row)] = row
        chosen.update((key(row), row) for row in groups.values())
    selected = [chosen[k] for k in sorted(chosen)]
    if not selected:
        issues.append({"error": "no matching target contexts; an empty dataset scope cannot pass"})
    scope = {"dataset": dataset, "inputs": list(map(str, inputs)), "topic": topic, "target_key": target_key,
             "selection": "all_targets" if all_targets else "longest_prefix_per_topic_plus_sentinels",
             "available_targets": len(available), "selected_contexts": len(selected),
             "selected_topics": len({(r["source"], r["topic"]) for r in selected}),
             "targets": [key(r) for r in selected]}
    return selected, scope, issues


def error_payload(exc):
    return {"ok": False, "error": f"{type(exc).__name__}: {exc}",
            "failure_category": exc.category if isinstance(exc, PisaFailure) else
                "timeout" if isinstance(exc, TimeoutError) else "preflight_error",
            **(exc.details if isinstance(exc, PisaFailure) else {})}


class Report:
    def __init__(self, root, scope):
        parent = repo_path(root)
        self.path = parent / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8])
        self.path.mkdir(parents=True)
        self.data = {"schema_version": REPORT_VERSION, "checker_version": CHECKER_VERSION,
                     "started_at": utc_now(), "status": "running", "ok": False,
                     "scope": scope, "checks": [], "active_check": None,
                     "diagnostic_bundle": "diagnostics.zip", "report_directory": str(self.path),
                     "acceptance_sha256": {p.name: hash_file(p) for p in
                         (Path(__file__), Path(__file__).with_name("acceptance.py"), PACKAGE / "upstream/checker.py")}}
        self.checkpoint()

    def checkpoint(self):
        checks = self.data["checks"]
        backend = [r for r in checks if r["domain"] in {"setup", "backend"}]
        data = [r for r in checks if r["domain"] in {"selection", "context", "dataset_proof"}]
        self.data.update(counts=dict(Counter(r["status"] for r in checks)),
            backend_ok=bool(backend) and all(r["status"] == "pass" for r in backend),
            contexts_ok=bool(data) and all(r["status"] == "pass" for r in data))
        self.data["ok"] = (self.data["status"] == "complete" and self.data["backend_ok"]
                           and self.data["contexts_ok"] and not self.data.get("bundle_error"))
        write_json(self.path / "report.json", self.data)
        lines = ["# DSP/PISA Isabelle2021 lab preflight", "", f"Status: **{self.data['status']}**; overall OK: **{self.data['ok']}**.",
                 f"Backend OK: **{self.data['backend_ok']}**; selected dataset checks OK: **{self.data['contexts_ok']}**.",
                 "", "Scope: `" + self.data["scope"]["selection"] + "`; " + str(self.data["scope"]["selected_contexts"]) + " contexts.",
                 "", "| Check | Domain | Status | Failure | Details |", "| --- | --- | --- | --- | --- |"]
        for row in checks:
            reason = " ".join(row.get("error", "").split()).replace("|", "&#124;")[:240]
            lines.append(f"| {row['name']} | {row['domain']} | {row['status']} | {reason} | [JSON]({row['details']}) |")
        lines += ["", "Expected negative controls pass only for their specific expected rejection.",
                  "Dataset failures do not turn into backend successes or disappear from the denominator.",
                  "Representative contexts do not establish readiness for every target; use --all-targets for that scope.",
                  "", "Push this complete run directory, including diagnostics.zip, after the command finishes."]
        (self.path / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    def start(self, name, domain):
        self.data["active_check"] = {"name": name, "domain": domain, "started_at": utc_now()}
        self.checkpoint()
        print(f"RUN   {domain}: {name}", flush=True)

    def record(self, name, domain, payload, *, duration=0, blocked=False):
        slug = re.sub(r"[^A-Za-z0-9_-]+", "_", name)[:100]
        details = f"details/{len(self.data['checks']) + 1:03d}-{slug}.json"
        result = payload.get("result") or {}
        row = {"name": name, "domain": domain, "status": "blocked" if blocked else "pass" if payload.get("ok") else "fail",
               "duration_seconds": round(duration, 3), "details": details,
               "failure_category": payload.get("failure_category") or result.get("failure_category"),
               "expected_failure": payload.get("expected_failure")}
        if row["status"] != "pass":
            row["error"] = (payload.get("error") or result.get("verify_error")
                or "; ".join(payload.get("expectation_errors", []))
                or "; ".join(issue.get("error", str(issue)) for issue in payload.get("issues", [])))
        write_json(self.path / details, {**row, "payload": payload})
        self.data["checks"].append(row)
        self.data["active_check"] = None
        with (self.path / "events.jsonl").open("a", encoding="utf-8") as stream:
            stream.write(json.dumps({"at": utc_now(), **row}) + "\n")
        self.checkpoint()
        print(f"{row['status'].upper():5} {domain}: {name} [{details}]", flush=True)

    def finish(self, *, interrupted=False):
        self.data.update(status="interrupted" if interrupted else "complete", finished_at=utc_now(), active_check=None)
        self.checkpoint()
        archive = self.path / "diagnostics.zip"
        temporary = self.path / "diagnostics.zip.tmp"
        try:
            with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED) as bundle:
                for path in sorted(self.path.rglob("*")):
                    if path.is_file() and path not in {archive, temporary}:
                        bundle.write(path, str(path.relative_to(self.path)))
            temporary.replace(archive)
        except Exception as exc:
            self.data["bundle_error"] = f"{type(exc).__name__}: {exc}"
            self.checkpoint()
        print(f"{'PASS' if self.data['ok'] else 'FAIL'}: backend_ok={self.data['backend_ok']}, "
              f"contexts_ok={self.data['contexts_ok']}, checks={self.data['counts']}", flush=True)
        print("Report: " + str(self.path / "report.json"), flush=True)
        print("Bundle: " + str(archive), flush=True)
        return self.data


def run_lab_preflight(*, config_path, records, scope, selection_issues=(), output_root=DEFAULT_REPORT_ROOT):
    report = Report(output_root, scope)
    pending, interrupted = [], False
    config = backend = None
    def run(name, domain, fn, *, blocked=None):
        report.start(name, domain)
        started = time.monotonic()
        try:
            payload = {"ok": False, "error": blocked} if blocked else fn()
        except KeyboardInterrupt:
            report.record(name, domain, {"ok": False, "error": "interrupted by user", "failure_category": "interrupted"})
            pending.remove((name, domain))
            raise
        except Exception as exc:
            payload = error_payload(exc)
        report.record(name, domain, payload, duration=time.monotonic()-started, blocked=bool(blocked))
        pending.remove((name, domain))
        return payload
    try:
        controls = proof_cases()
        proofs, issues = [], list(selection_issues)
        for row in records:
            try:
                proofs.extend(dataset_cases([row]))
            except Exception as exc:
                issues.append({"target": key(row), "error": str(exc)})
        jobs = [("context_" + row["source"] + "_" + row["topic"] + "_" + row["target_key"], row) for row in records]
        pending = [("input_selection", "selection"), ("metadata", "setup"), ("pisa_transport", "setup")]
        pending += [(c.name, "backend") for c in controls] + [(c.name, "dataset_proof") for c in proofs]
        pending += [(name, "context") for name, _ in jobs]
        report.data["planned_checks"] = [dict(name=n, domain=d) for n, d in pending]
        run("input_selection", "selection", lambda: {"ok": not issues and bool(records), "issues": issues})
        def metadata():
            nonlocal config, backend
            config = DspConfig.load(str(config_path))
            write_json(report.path / "config.json", config.__dict__)
            backend = config.metadata()
            write_json(report.path / "backend.json", backend)
            return {"ok": True, "backend_fingerprint": backend["backend_fingerprint"]}
        setup = run("metadata", "setup", metadata)
        transport = run("pisa_transport", "setup", lambda: run_proof_case(controls[0], config=config, backend=backend,
            directory=report.path / "transport"), blocked=None if setup["ok"] else "metadata/setup failed")
        blocked = None if transport["ok"] else "PISA startup/transport unavailable; see setup diagnostics"
        for case, domain in [(c, "backend") for c in controls] + [(c, "dataset_proof") for c in proofs]:
            run(case.name, domain, lambda case=case: run_proof_case(case, config=config, backend=backend,
                directory=report.path / "cases" / case.name), blocked=blocked)
        for name, row in jobs:
            def check(row=row):
                result = Checker(config, results_dir=str(report.path)).check_context(row, backend_metadata=backend)
                return {"ok": result["baseline_ok"], "target": key(row), "result": result}
            run(name, "context", check, blocked=blocked)
    except KeyboardInterrupt:
        interrupted = True
    except Exception as exc:
        report.record("orchestration_error", "setup", error_payload(exc))
    finally:
        completed = {(r["name"], r["domain"]) for r in report.data["checks"]}
        for name, domain in pending:
            if (name, domain) not in completed:
                report.record(name, domain, {"ok": False, "error": "run interrupted or aborted"}, blocked=True)
        result = report.finish(interrupted=interrupted)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--config", required=True)
    parser.add_argument("--dataset", choices=("both", "babel-formal", "hundred-theorems"), default="both")
    parser.add_argument("--input", action="append", default=[], help="Optional saved records; repeat for multiple files")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--all-targets", action="store_true", help="Check every selected target, not topic representatives")
    parser.add_argument("--output-root", default=DEFAULT_REPORT_ROOT, help="A unique run directory is created here")
    parser.add_argument("--plan-only", action="store_true", help="Print scope/checks without Isabelle, model calls or output writes")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    records, scope, issues = discover_records(dataset=args.dataset, inputs=args.input, topic=args.topic,
                                               target_key=args.target_key, all_targets=args.all_targets)
    if args.plan_only:
        print(json.dumps({"scope": scope, "selection_issues": issues,
                          "backend_cases": [c.name for c in proof_cases()],
                          "dataset_cases": [c.name for c in dataset_cases(records)],
                          "output_root": str(repo_path(args.output_root))}, indent=2))
        raise SystemExit(1 if issues else 0)
    result = run_lab_preflight(config_path=args.config, records=records, scope=scope,
                               selection_issues=issues, output_root=args.output_root)
    raise SystemExit(130 if result["status"] == "interrupted" else 0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
