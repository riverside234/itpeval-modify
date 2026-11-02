"""Pinned full-source installation and independent unavailable-context reporting."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import repo_path, RESULTS_DIR, key
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import prepare_afp as setup
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import lab_preflight as lab
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record


class AfpSetupTests(unittest.TestCase):
    def setUp(self):
        root = repo_path(RESULTS_DIR)
        root.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="afp-test-", dir=root)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.archive = self.path / "release.tar.gz"
        self.destination = self.path / "afp"
        self.config = self.path / "config.json"
        self.original = {"backend": "isabelle-native", "threads": 8, "session_roots": ["external/keep/thys"]}
        self.config.write_text(json.dumps(self.original))

    def archive_fixture(self, *, version="2026", extra=None):
        files = {"etc/version": "AFP_VERSION=" + version + "\n",
                 "thys/ROOTS": "\n".join(setup.REQUIRED_THEORIES) + "\nUnrelated_Session\n",
                 "thys/Unrelated_Session/Full_Source.thy": "full source retained\n"}
        for session, theory in setup.REQUIRED_THEORIES.items():
            files["thys/" + session + "/ROOT"] = "session " + session + " = HOL +\n"
            files["thys/" + session + "/" + theory + ".thy"] = "theory " + theory + " imports Main begin end\n"
        files.update(extra or {})
        with tarfile.open(self.archive, "w:gz") as archive:
            for name, content in files.items():
                data = content.encode()
                member = tarfile.TarInfo(setup.ARCHIVE_ROOT + "/" + name)
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
        return hashlib.sha256(self.archive.read_bytes()).hexdigest()

    def install(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return setup.install(config_path=self.config, destination=self.destination, archive_path=self.archive)

    def test_full_sources_and_existing_settings_are_preserved_and_reruns_are_idempotent(self):
        digest = self.archive_fixture()
        with patch.object(setup, "ARCHIVE_SHA256", digest), patch.object(setup.urllib.request, "urlopen") as network:
            self.install()
            first = self.config.read_bytes()
            result = self.install()
            network.assert_not_called()
        self.assertEqual(first, self.config.read_bytes())
        data = json.loads(first)
        self.assertEqual(8, data["threads"])
        self.assertEqual("external/keep/thys", data["session_roots"][0])
        self.assertEqual(2, len(data["session_roots"]))
        self.assertFalse(Path(data["session_roots"][1]).is_absolute())
        self.assertTrue((self.destination / "thys/Unrelated_Session/Full_Source.thy").is_file())
        self.assertEqual(digest, result["archive_sha256"])

    def test_checksum_mismatch_never_changes_config_or_installs_partial_sources(self):
        self.archive_fixture()
        before = self.config.read_bytes()
        with self.assertRaisesRegex(ValueError, "checksum mismatch"):
            self.install()
        self.assertEqual(before, self.config.read_bytes())
        self.assertFalse(self.destination.exists())

    def test_wrong_isabelle_release_is_rejected_even_with_a_matching_archive_hash(self):
        digest = self.archive_fixture(version="2025-2")
        before = self.config.read_bytes()
        with patch.object(setup, "ARCHIVE_SHA256", digest), self.assertRaisesRegex(ValueError, "AFP_VERSION=2026"):
            self.install()
        self.assertEqual(before, self.config.read_bytes())
        self.assertFalse(self.destination.exists())

    def test_existing_user_directory_is_not_overwritten(self):
        self.destination.mkdir()
        (self.destination / "keep.txt").write_text("user data")
        with self.assertRaisesRegex(ValueError, "already exists"):
            self.install()
        self.assertEqual("user data", (self.destination / "keep.txt").read_text())

    def test_download_is_atomic_and_checksum_checked(self):
        digest = self.archive_fixture()
        content = self.archive.read_bytes()
        cache = self.path / "cache.tar.gz"
        with patch.object(setup, "ARCHIVE_SHA256", digest), patch.object(
                setup.urllib.request, "urlopen", return_value=io.BytesIO(content)):
            setup.download_archive(cache)
        self.assertEqual(content, cache.read_bytes())
        with patch.object(setup.urllib.request, "urlopen", return_value=io.BytesIO(b"truncated")):
            with self.assertRaisesRegex(ValueError, "pinned"):
                setup.download_archive(self.path / "failed.tar.gz")
        self.assertFalse((self.path / "failed.tar.gz").exists())
        self.assertFalse(list(self.path.glob("*.part")))

    def test_traversal_absolute_paths_and_links_cannot_escape_staging(self):
        staging = self.path / "staging"
        staging.mkdir()
        for name, kind, link in ((setup.ARCHIVE_ROOT+"/../escape", tarfile.REGTYPE, ""),
                                 ("/absolute", tarfile.REGTYPE, ""),
                                 (setup.ARCHIVE_ROOT+"/link", tarfile.SYMTYPE, "../../outside"),
                                 (setup.ARCHIVE_ROOT+"/link", tarfile.LNKTYPE, "../../outside")):
            with self.subTest(name=name, kind=kind):
                with tarfile.open(self.archive, "w:gz") as archive:
                    member = tarfile.TarInfo(name)
                    member.type, member.linkname = kind, link
                    archive.addfile(member)
                with self.assertRaises(ValueError):
                    setup.extract_sources(self.archive, staging)
        self.assertFalse((self.path / "escape").exists())


class UnavailableContextTests(unittest.TestCase):
    def setUp(self):
        root = repo_path(RESULTS_DIR)
        root.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="unavailable-test-", dir=root)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)

    def test_separate_unavailable_report_does_not_claim_full_coverage(self):
        report = lab.Report(self.path, {"selected_contexts": 2, "selection": "test"})
        with contextlib.redirect_stdout(io.StringIO()):
            report.record("setup", "setup", {"ok": True})
            report.record("available", "context", {"ok": True})
            report.record("core_Set", "context", {"ok": False, "unavailable_context": True,
                "failure_category": "inherited_target_theory", "target": ["hundred-theorems", "052", "lemma"],
                "error": "Already inherited by HOL"})
            result = report.finish()
        self.assertTrue(result["ok"])
        self.assertFalse(result["full_context_coverage"])
        self.assertEqual(1, result["counts"]["unavailable_context"])
        self.assertEqual(2, result["context_counts"]["selected"])
        rows = json.loads((report.path / "unavailable_contexts.json").read_text())
        self.assertEqual("unavailable context", rows[0]["status_label"])
        self.assertIn("## Unavailable context", (report.path / "summary.md").read_text())

    def test_entirely_unavailable_selection_and_regular_failures_cannot_pass(self):
        for payload in ({"unavailable_context": True}, {"failure_category": "import_error"}):
            report = lab.Report(self.path, {"selected_contexts": 1, "selection": "test"})
            with contextlib.redirect_stdout(io.StringIO()):
                report.record("setup", "setup", {"ok": True})
                report.record("target", "context", {"ok": False, **payload})
                result = report.finish()
            self.assertFalse(result["ok"])
            expected = "unavailable_context" if payload.get("unavailable_context") else "fail"
            self.assertEqual(expected, result["checks"][-1]["status"])

    def test_unavailable_target_never_reaches_native_but_stays_in_report(self):
        records = [control_record("by simp"), {**control_record("by simp"), "target_key": "set_goal"}]
        scope = {"selected_contexts": 2, "selection": "test"}
        parent = self.path / "parent"
        parent.mkdir()
        (parent / "ROOT").write_text("fixture")
        with patch.object(lab.DspConfig, "load", return_value=lab.DspConfig()), patch.object(
                lab.DspConfig, "metadata", return_value={"backend_fingerprint": "fixture"}), patch.object(
                lab, "dependency_plan", return_value={"known_inherited_targets": [key(records[1])]}), patch.object(
                lab.NativeSearch, "infrastructure", return_value=(parent, "Prepared")), patch.object(
                lab, "run_fixture", return_value={"ok": True}), patch.object(lab, "proof_cases", return_value=[]), patch.object(
                lab, "dataset_cases", return_value=[]), patch.object(
                lab.Checker, "check_context", return_value={"baseline_ok": True}) as native, contextlib.redirect_stdout(io.StringIO()):
            result = lab.run_lab_preflight(config_path="fixture.json", records=records, scope=scope, output_root=self.path)
        native.assert_called_once()
        self.assertEqual(6, len(result["checks"]))
        self.assertEqual(1, result["context_counts"]["unavailable"])
        self.assertEqual("unavailable_context", result["checks"][-1]["status"])
        self.assertEqual(list(key(records[1])), result["checks"][-1]["target"])
        self.assertTrue(result["ok"])

    def test_catalog_identifies_24_set_targets_and_31_distinct_afp_targets(self):
        records, _, issues = lab.discover_records(all_targets=True)
        self.assertFalse(issues)
        plan = lab.dependency_plan(records, lab.DspConfig())
        inherited = {tuple(row) for row in plan["known_inherited_targets"]}
        afp = {key(row) for row in records
               if plan["topics"][row["source"] + "/" + row["topic"]]["required_afp_sessions"]}
        self.assertEqual(24, len(inherited))
        self.assertEqual(31, len(afp))
        self.assertFalse(inherited & afp)
        self.assertEqual(262, len(records))


if __name__ == "__main__":
    unittest.main()
