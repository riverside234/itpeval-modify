"""One recorded Isabelle2026 acceptance run: setup, controls, datasets and diagnostic ZIP."""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import replace
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import time
import uuid
import zipfile

from ..common import fingerprint, key, latest_records, repo_path, validate_layout
from .acceptance import (FIXTURE, PreparedNative, dataset_cases, proof_cases, run_fixture, run_proof_case)
from .checker import CHECKER_VERSION, Checker
from .native_search import NativeFailure, NativeSearch, resolve_imports
from ..theory_context import validate_context
from .runtime import DspConfig, NATIVE_DIR, hash_file

REPORT_VERSION = "isabelle2026_lab_preflight_v3"
DEFAULT_REPORT_ROOT = "eval/preflight_results/isabelle2026"
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


def dependency_plan(records, config):
    """Explain dependency requirements without loading original target theories."""
    topics = {}
    required = set()
    inherited = []
    for row in records:
        context = validate_context(row)
        _, resolution = resolve_imports(context.prefix, config, theory_name=context.theory_name)
        external = sorted(set(resolution["session_dependencies"]) &
                          {"Triangle", "Cayley_Hamilton", "Pratt_Certificate"})
        required.update(external)
        identity = row["source"] + "/" + row["topic"]
        topic = topics.setdefault(identity, {"theory_name": context.theory_name, **resolution,
                                             "required_afp_sessions": external, "targets": []})
        topic["targets"].append(row["target_key"])
        # This is a known incompatibility, never an exclusion or a successful check.
        # The native ancestor check remains the authoritative gate for every target.
        if config.base_session == "HOL" and context.theory_name == "Set":
            inherited.append(key(row))
    return {"required_afp_sessions": sorted(required), "session_roots": list(config.session_roots),
            "known_inherited_targets": inherited, "topics": topics,
            "guidance": "Install the AFP release matching Isabelle2026 and supply its thys root; "
                        "keep base_session HOL. Core Set targets remain ineligible in this parent, "
                        "stay in the reported cohort and cannot count as isolated proof successes."}


def error_payload(exc):
    return {"ok": False, "error": f"{type(exc).__name__}: {exc}",
            "failure_category": exc.category if isinstance(exc, NativeFailure) else
                "timeout" if isinstance(exc, TimeoutError) else "preflight_error",
            **(exc.details if isinstance(exc, NativeFailure) else {})}


class Report:
    def __init__(self, root, scope):
        parent = repo_path(root)
        self.path = parent / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8])
        self.path.mkdir(parents=True)
        self.data = {"schema_version": REPORT_VERSION, "checker_version": CHECKER_VERSION,
                     "started_at": utc_now(), "status": "running", "ok": False, "replay_enabled": False,
                     "scope": scope, "checks": [], "active_check": None,
                     "diagnostic_bundle": "diagnostics.zip", "report_directory": str(self.path),
                     "acceptance_sha256": {p.name: hash_file(p) for p in
                         (Path(__file__), Path(__file__).with_name("acceptance.py"), FIXTURE)}}
        self.checkpoint()

    def checkpoint(self):
        checks = self.data["checks"]
        backend = [r for r in checks if r["domain"] in {"setup", "backend"}]
        unavailable = [r for r in checks if r["status"] == "unavailable_context"]
        data = [r for r in checks if r["domain"] in {"selection", "context", "dataset_proof"}
                and r["status"] != "unavailable_context"]
        contexts = [r for r in checks if r["domain"] == "context"]
        available = [r for r in contexts if r["status"] != "unavailable_context"]
        self.data.update(unavailable_contexts=unavailable, context_counts={
            "selected": self.data["scope"]["selected_contexts"],
            "reported": len(contexts), "unavailable": len(unavailable),
            "passed": sum(r["status"] == "pass" for r in contexts),
            "failed": sum(r["status"] == "fail" for r in contexts),
            "blocked": sum(r["status"] == "blocked" for r in contexts)},
            full_context_coverage=bool(contexts) and not unavailable and
                len(contexts) == self.data["scope"]["selected_contexts"] and
                all(r["status"] in {"pass", "fail"} for r in contexts))
        write_json(self.path / "unavailable_contexts.json", unavailable)
        self.data.update(counts=dict(Counter(r["status"] for r in checks)),
            backend_ok=bool(backend) and all(r["status"] == "pass" for r in backend),
            contexts_ok=bool(available) and all(r["status"] == "pass" for r in data))
        self.data["ok"] = (self.data["status"] == "complete" and self.data["backend_ok"]
                           and self.data["contexts_ok"] and not self.data.get("bundle_error"))
        write_json(self.path / "report.json", self.data)
        lines = ["# Isabelle2026 lab preflight", "", f"Status: **{self.data['status']}**; overall OK: **{self.data['ok']}**.",
                 f"Backend OK: **{self.data['backend_ok']}**; available dataset checks OK: **{self.data['contexts_ok']}**.",
                 "", "Scope: `" + self.data["scope"]["selection"] + "`; " + str(self.data["scope"]["selected_contexts"]) + " contexts.",
                 "", "| Check | Domain | Status | Failure | Details |", "| --- | --- | --- | --- | --- |"]
        for row in [r for r in checks if r["status"] != "unavailable_context"]:
            reason = " ".join(row.get("error", "").split()).replace("|", "&#124;")[:240]
            lines.append(f"| {row['name']} | {row['domain']} | {row['status']} | {reason} | [JSON]({row['details']}) |")
        lines += ["", "## Unavailable context", "",
                  f"{len(unavailable)} selected contexts are unavailable; they remain in the candidate count.",
                  "", "| Target | Reason | Details |", "| --- | --- | --- |"]
        for row in unavailable:
            reason = " ".join(row.get("error", "").split()).replace("|", "&#124;")
            lines.append(f"| {row['name']} | {reason} | [JSON]({row['details']}) |")
        lines += ["", "Overall OK evaluates the backend and available contexts; it does not claim unavailable contexts passed.",
                  "An entirely unavailable selection cannot pass."]
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
        row = {"name": name, "domain": domain, "status": "unavailable_context" if domain == "context" and payload.get("unavailable_context")
                   else "blocked" if blocked else "pass" if payload.get("ok") else "fail",
               "duration_seconds": round(duration, 3), "details": details,
               "failure_category": payload.get("failure_category") or result.get("failure_category"),
               "expected_failure": payload.get("expected_failure")}
        if payload.get("target") is not None:
            row["target"] = list(payload["target"])
        if row["status"] == "unavailable_context":
            row["status_label"] = "unavailable context"
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


def snapshot_infrastructure(parent: Path, report: Report):
    destination = report.path / "infrastructure"
    destination.mkdir(exist_ok=True)
    for path in parent.iterdir():
        if path.is_file() and (path.name in {"ROOT", "build.log", "build.processes.json", "command.json"}
                               or path.suffix in {".ML", ".thy"}):
            shutil.copyfile(path, destination / path.name)


def run_lab_preflight(*, config_path, records, scope, selection_issues=(), output_root=DEFAULT_REPORT_ROOT, afp_root=None):
    report = Report(output_root, scope)
    pending = []
    config = backend = parent = None
    unavailable_targets = set()
    interrupted = False
    def run(name, domain, fn, *, blocked=None):
        pending.remove((name, domain))
        report.start(name, domain)
        started = time.monotonic()
        try:
            payload = {"ok": False, "error": blocked} if blocked else fn()
        except KeyboardInterrupt:
            report.record(name, domain, {"ok": False, "error": "interrupted by user", "failure_category": "interrupted"},
                          duration=time.monotonic() - started)
            raise
        except Exception as exc:
            payload = error_payload(exc)
        report.record(name, domain, payload, duration=time.monotonic() - started, blocked=bool(blocked))
        return payload
    try:
        controls = proof_cases()
        proofs, issues = [], list(selection_issues)
        for row in records:
            try:
                proofs.extend(dataset_cases([row]))
            except Exception as exc:
                issues.append({"target": key(row), "error": f"{type(exc).__name__}: {exc}"})
        context_jobs = [("context_" + row["source"] + "_" + row["topic"] + "_" + row["target_key"], row) for row in records]
        pending = [("input_selection", "selection"), ("metadata", "setup"), ("infrastructure", "setup"), ("native_fixture", "backend")]
        pending += [(c.name, "backend") for c in controls] + [(c.name, "dataset_proof") for c in proofs]
        pending += [(name, "context") for name, _ in context_jobs]
        report.data["planned_checks"] = [dict(name=n, domain=d) for n, d in pending]
        run("input_selection", "selection", lambda: {"ok": not issues and bool(records), "issues": issues})
        def metadata():
            nonlocal config, backend, unavailable_targets
            config = DspConfig.load(str(config_path))
            if afp_root:
                root = str(repo_path(afp_root))
                config = replace(config, session_roots=tuple(dict.fromkeys((*config.session_roots, root))))
            dependencies = dependency_plan(records, config)
            unavailable_targets = {tuple(target) for target in dependencies.get("known_inherited_targets", [])}
            write_json(report.path / "dependencies.json", dependencies)
            write_json(report.path / "config.json", config.__dict__)
            backend = config.metadata()
            write_json(report.path / "backend.json", backend)
            shutil.copyfile(NATIVE_DIR / "release_sources.json", report.path / "release_sources.json")
            return {"ok": True, "backend_fingerprint": backend["backend_fingerprint"], "backend_file": "backend.json"}
        setup = run("metadata", "setup", metadata)
        def infrastructure():
            nonlocal parent
            try:
                parent = NativeSearch(config).infrastructure(deadline=time.monotonic() + config.target_timeout_s)
            except NativeFailure as exc:
                log = exc.details.get("build_log_path")
                if log and Path(log).parent.is_dir():
                    snapshot_infrastructure(Path(log).parent, report)
                raise
            snapshot_infrastructure(parent[0], report)
            return {"ok": True, "session": parent[1], "snapshot": "infrastructure"}
        infra = run("infrastructure", "setup", infrastructure, blocked=None if setup["ok"] else "metadata/setup failed")
        blocked = None if infra["ok"] else "native infrastructure unavailable; see setup diagnostics"
        run("native_fixture", "backend", lambda: run_fixture(config, parent, report.path / "fixture"), blocked=blocked)
        for case, domain in [(c, "backend") for c in controls] + [(c, "dataset_proof") for c in proofs]:
            run(case.name, domain, lambda case=case: run_proof_case(case, config=config, backend=backend, parent=parent,
                directory=report.path / "cases" / case.name), blocked=blocked)
        for name, row in context_jobs:
            if key(row) in unavailable_targets:
                run(name, "context", lambda row=row: {"ok": False, "unavailable_context": True,
                    "target": key(row), "failure_category": "inherited_target_theory",
                    "error": "Core Set is already inherited by the HOL parent; an isolated target context "
                             "is unavailable. Installing AFP does not change this restriction."})
                continue
            def context_check(row=row):
                checked = Checker(config, results_dir=str(report.path), native_factory=lambda cfg: PreparedNative(cfg, parent)).check_context(
                    row, backend_metadata=backend)
                return {"ok": checked["baseline_ok"], "target": key(row), "result": checked}
            run(name, "context", context_check, blocked=blocked)
    except KeyboardInterrupt:
        interrupted = True
    except Exception as exc:
        report.record("orchestration_error", "setup", error_payload(exc))
    finally:
        for name, domain in pending:
            report.record(name, domain, {"ok": False, "error": "not executed because the run was interrupted or aborted"}, blocked=True)
        result = report.finish(interrupted=interrupted)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--config", default="eval/configs/hol_light_to_isabelle/v2_dsp_2026.example.json")
    parser.add_argument("--afp-root", help="Repository-local thys directory of the AFP release matching Isabelle2026")
    parser.add_argument("--expected-contexts", type=int, help="Fail selection if the selected candidate count differs")
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
    if args.expected_contexts is not None:
        if args.expected_contexts < 1:
            parser.error("--expected-contexts must be positive")
        scope["expected_contexts"] = args.expected_contexts
        if len(records) != args.expected_contexts:
            issues.append({"error": f"expected {args.expected_contexts} candidate contexts, selected {len(records)}"})
    if args.plan_only:
        print(json.dumps({"scope": scope, "selection_issues": issues,
                          "backend_cases": [c.name for c in proof_cases()],
                          "dataset_cases": [c.name for c in dataset_cases(records)],
                          "output_root": str(repo_path(args.output_root))}, indent=2))
        raise SystemExit(1 if issues else 0)
    result = run_lab_preflight(config_path=args.config, records=records, scope=scope,
                               selection_issues=issues, output_root=args.output_root, afp_root=args.afp_root)
    raise SystemExit(130 if result["status"] == "interrupted" else 0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
