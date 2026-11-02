"""Report size, aggregation and non-destructive legacy migration regressions."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline import preflight_storage as storage
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline import compact_preflight as migration
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import lab_preflight as lab


class CompactReportsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        def resolve(path):
            candidate = Path(path)
            result = (candidate if candidate.is_absolute() else self.root / candidate).resolve()
            if not result.is_relative_to(self.root):
                raise ValueError("path outside fixture repository")
            return result
        for module in (storage, migration, lab):
            mocker = patch.object(module, "repo_path", side_effect=resolve)
            mocker.start()
            self.addCleanup(mocker.stop)

    def test_262_contexts_large_payloads_and_logs_stay_in_six_files(self):
        with contextlib.redirect_stdout(io.StringIO()):
            report = lab.Report("eval/preflight_results/isabelle2026", {"selection": "all_targets", "selected_contexts": 262})
            report.record("backend", "setup", {"ok": True})
            for i in range(262):
                report.record(str(i), "context", {"ok": False, "target": ["test", i, "topic", "goal"],
                    "unavailable_context": i < 24, "error": "problem " * 5000,
                    "result": {"steps": [{"trace": "x" * 4096}] * 40}})
            for i in range(3):
                (report.work_path / f"large-{i}.log").write_bytes(b"HEAD" + b"x" * (2 * storage.MIB) + b"TAIL")
            result = report.finish()
        files = list(report.path.iterdir())
        self.assertEqual(storage.REPORT_FILES, {p.name for p in files})
        self.assertLess(sum(p.stat().st_size for p in files), 20 * storage.MIB)
        self.assertTrue(all(p.stat().st_size < storage.MAX_FILE_BYTES for p in files))
        self.assertEqual(262, result["context_counts"]["reported"])
        self.assertEqual(24, result["context_counts"]["unavailable"])
        self.assertEqual(238, result["context_counts"]["failed"])
        self.assertEqual(263, len((report.path / "checks.jsonl").read_text().splitlines()))
        logs = [json.loads(line) for line in (report.path / "logs.jsonl").read_text().splitlines()]
        self.assertEqual(3, len(logs))
        self.assertTrue(all(r["truncated"] and r["text"].startswith("HEAD") and r["text"].endswith("TAIL") for r in logs))
        self.assertEqual(263, len((report.work_path / "checks.full.jsonl").read_text().splitlines()))

    def test_pathological_payload_and_log_count_are_bounded_and_visible(self):
        value = {str(i): "\x00" * 5000 for i in range(100)}
        self.assertLessEqual(len(storage.encode(storage.compact(value))), storage.MAX_DETAIL_BYTES)
        path = self.root / "report"
        path.mkdir()
        writer = storage.ReportStorage(path)
        for i in range(5):
            (writer.work_path / f"{i}.log").write_text("log")
        with patch.object(storage, "MAX_LOG_FILES", 2):
            stats = writer.finish()
        self.assertEqual(2, stats["included"])
        self.assertEqual(3, stats["omitted"])
        with patch.object(storage, "MAX_FILE_BYTES", 10):
            with self.assertRaisesRegex(ValueError, "size limit"):
                storage.write_json(path / "too-big.json", {"trace": "x" * 100})
        self.assertFalse((path / "too-big.json").exists())

    def legacy(self):
        path = self.root / "eval/preflight_results/isabelle2026/legacy"
        (path / "details").mkdir(parents=True)
        (path / "work").mkdir()
        row = {"name": "target", "domain": "context", "status": "fail", "details": "details/one.json", "error": "missing theory"}
        (path / "report.json").write_text(json.dumps({"status": "complete", "ok": False, "checks": [row],
            "scope": {"selected_contexts": 1}, "counts": {"fail": 1}}))
        (path / "details/one.json").write_text(json.dumps({"payload": {"ok": False, "error": "missing theory", "prover_settings": {"provers": ["e"]}}}))
        (path / "work/build.log").write_text("the relevant failure")
        (path / "backend.json").write_text(json.dumps({"backend_fingerprint": "test"}))
        (path / "diagnostics.zip").write_bytes(b"must survive unchanged locally")
        return path

    def test_legacy_conversion_keeps_full_backup_and_results_and_is_idempotent(self):
        path = self.legacy()
        result = migration.compact_run(path)
        backup = Path(result["local_backup"])
        self.assertEqual(b"must survive unchanged locally", (backup / "diagnostics.zip").read_bytes())
        self.assertEqual(storage.REPORT_FILES, {p.name for p in path.iterdir()})
        report = json.loads((path / "report.json").read_text())
        self.assertFalse(report["ok"])
        self.assertEqual({"fail": 1}, report["counts"])
        self.assertEqual(1, report["scope"]["selected_contexts"])
        detail = json.loads((path / "checks.jsonl").read_text())
        self.assertEqual(["e"], detail["payload"]["prover_settings"]["provers"])
        self.assertIn("the relevant failure", (path / "logs.jsonl").read_text())
        self.assertEqual(str(backup), json.loads((path / "metadata.json").read_text())["local_artifacts"])
        self.assertTrue(migration.compact_run(path)["already_compact"])

    def test_legacy_write_failure_keeps_original_untouched(self):
        path = self.legacy()
        with patch.object(migration.ReportStorage, "finish", side_effect=OSError("disk full")):
            with self.assertRaisesRegex(OSError, "disk full"):
                migration.compact_run(path)
        self.assertTrue((path / "details/one.json").exists())
        self.assertTrue((path / "diagnostics.zip").exists())
        self.assertNotIn("report_format", json.loads((path / "report.json").read_text()))

    def test_legacy_rejects_active_run_and_escaping_detail_paths(self):
        path = self.legacy()
        file = path / "report.json"
        report = json.loads(file.read_text())
        report["status"] = "running"
        file.write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError, "active preflight"):
            migration.compact_run(path)
        report["status"] = "complete"
        report["checks"][0]["details"] = "../../../../secret.json"
        file.write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError, "escapes"):
            migration.compact_run(path)
        self.assertTrue((path / "diagnostics.zip").exists())


if __name__ == "__main__":
    unittest.main()
