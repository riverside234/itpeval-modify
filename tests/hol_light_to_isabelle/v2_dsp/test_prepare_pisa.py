"""Offline checks for setting up the pinned server without changing proof code."""
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import prepare_pisa as setup
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig, PISA_COMMIT, source_hash


class PreparePisaTests(unittest.TestCase):
    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.root = self.path / "pisa"
        self.root.mkdir()
        self.config = DspConfig(pisa_root=str(self.root))
        self.original = 'libraryDependencies += "de.unruh" %% "scala-isabelle" % "master-SNAPSHOT" from "file:{$PWD}/lib/scala-isabelle_2.13.jar"\n'
        (self.root / "build.sbt").write_text(self.original, encoding="utf-8")
        self.proto = self.root / "src/main/protobuf/server.proto"
        self.proto.parent.mkdir(parents=True)
        self.proto.write_text('syntax = "proto3";\n', encoding="utf-8")
        (self.path / "upstream").mkdir()
        (self.path / "upstream/pisa_sources.json").write_text(json.dumps({
            "src/main/protobuf/server.proto": source_hash(self.proto)}), encoding="utf-8")

    def command(self, args, **kwargs):
        if args[-2:] == ["rev-parse", "HEAD"]:
            return SimpleNamespace(stdout=PISA_COMMIT + "\n")
        if "show" in args:
            return SimpleNamespace(stdout=self.original)
        self.assertIn("grpc_tools.protoc", args)
        self.assertEqual(str(self.proto), args[-1])
        for name in ("server_pb2.py", "server_pb2_grpc.py"):
            (self.config.generated / name).write_text("# generated for fixture\n", encoding="utf-8")
        return SimpleNamespace(returncode=0)

    def test_repeated_setup_preserves_sources_and_fixes_only_bundled_jar_url(self):
        with patch.object(setup, "PACKAGE", self.path), patch.object(setup.subprocess, "run", side_effect=self.command):
            setup.prepare(self.config)
            once = (self.root / "build.sbt").read_text(encoding="utf-8")
            setup.prepare(self.config)
        self.assertEqual(once, (self.root / "build.sbt").read_text(encoding="utf-8"))
        self.assertEqual(self.original.replace('from "file:{$PWD}/lib/scala-isabelle_2.13.jar"',
            'from ((baseDirectory.value / "lib" / "scala-isabelle_2.13.jar").toURI.toString)'), once)
        self.assertTrue((self.config.generated / "server_pb2.py").is_file())
        self.assertEqual('syntax = "proto3";\n', self.proto.read_text(encoding="utf-8"))

    def test_unrelated_source_or_build_changes_are_not_overwritten(self):
        with patch.object(setup, "PACKAGE", self.path), patch.object(setup.subprocess, "run", side_effect=self.command):
            (self.root / "build.sbt").write_text("custom build", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "unrelated edits"):
                setup.prepare(self.config)
            self.assertEqual("custom build", (self.root / "build.sbt").read_text())
            self.proto.write_text("modified protocol", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "pinned revision"):
                setup.prepare(self.config)
            self.assertEqual("modified protocol", self.proto.read_text())


if __name__ == "__main__":
    unittest.main()
