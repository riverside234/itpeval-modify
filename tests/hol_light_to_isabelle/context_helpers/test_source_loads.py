"""Check load order, reachability and masked cross-file context."""

from dataclasses import replace
import json
from pathlib import Path
import tempfile
import unittest

from eval.pipeline.hol_light_to_isabelle.context_helpers.context import prepare_selection
from eval.pipeline.hol_light_to_isabelle.context_helpers.contracts import ContextConfig
from eval.pipeline.hol_light_to_isabelle.context_helpers.dependencies import source_packages, walk
from eval.pipeline.hol_light_to_isabelle.context_helpers.source_index import SourceIndex, SourceView
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.common import repo_path, sha256
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.context import source_snippets
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.extract_hol_light import extract_records


def theorem(name, term, proof):
    quote = chr(96)
    return f"let {name} = prove ({quote}{term}{quote}, {proof});;\n"


class OrderedLoadTests(unittest.TestCase):
    def setUp(self):
        out = repo_path("eval/results")
        out.mkdir(parents=True, exist_ok=True)
        temp = tempfile.TemporaryDirectory(dir=out)
        self.addCleanup(temp.cleanup)
        self.folder = Path(temp.name)
        self.config = ContextConfig(cross_file=True, source_load_manifest=str(self.folder / "loads.json"))

    def test_nested_loads_respect_definition_order_and_exact_paths(self):
        root_text = (
            'needs "Core/prior.ml";;\n'
            'needs "Scoped/helpers.ml";;\n'
            'needs "Sibling/helpers.ml";;\n'
            'needs "./Scoped/helpers.ml";;\n'
            'needs "Missing/helpers.ml";;\n'
            'needs "../escape.ml";;\n'
            'needs "Bad/wrong_digest.ml";;\n'
            + theorem("ROOT_FACT", "T", "USE [MAIN_RULE; SHARED_BINDING; LATE_RULE]") +
            'loads "Future/later.ml";;\n')
        files = {
            "Core/prior.ml": theorem("BASE_RULE", "T", "BASE_PROOF_CODE"),
            "Scoped/helpers.ml": (
                'loadt "Nested/leaf.ml";;\n'
                "let CAPTURED_ALIAS = SHARED_BINDING;;\n"
                + theorem("MAIN_RULE", "T", "USE [CAPTURED_ALIAS; ROOT_FACT]") +
                'needs "Cycle/root.ml";;\n'),
            "Nested/leaf.ml": theorem("SHARED_BINDING", "P", "USE BASE_RULE"),
            "Sibling/helpers.ml": theorem("SHARED_BINDING", "Q", "UNRELATED_PROOF_CODE"),
            "Cycle/root.ml": root_text,
            "Bad/wrong_digest.ml": theorem("LATE_RULE", "T", "BAD_PROOF_CODE"),
            "Future/later.ml": theorem("LATE_RULE", "T", "FUTURE_PROOF_CODE"),
        }
        manifest = {"version": 1, "root": self.folder.relative_to(repo_path(".")).as_posix(), "files": {}}
        for i, (logical, content) in enumerate(files.items()):
            name = f"snapshot_{i}.ml"
            (self.folder / name).write_bytes(content.encode("utf-8"))
            digest = "0" * 64 if logical.startswith("Bad/") else sha256(content)
            manifest["files"][logical] = {"proof": name, "proof_sha256": digest}
        (self.folder / "loads.json").write_text(json.dumps(manifest), encoding="utf-8")
        index = SourceIndex(root_text, self.config)
        root = index.bindings["ROOT_FACT"][0]
        quote = chr(96)
        view = SourceView(index, root, "root.ml", "root_masked.ml", sha256(root_text), "",
                          source_snippets(f"let ROOT_FACT = {quote}T{quote};;\n"))
        cfg = replace(self.config, dependency_depth=3)
        helpers, _, report, _ = walk(view, cfg)
        self.assertEqual([(item.binding.name, item.binding.statement) for item in helpers],
                         [("MAIN_RULE", "T"), ("SHARED_BINDING", "Q"), ("SHARED_BINDING", "P"), ("BASE_RULE", "T")])
        self.assertEqual([node["depth"] for node in report["nodes"]], [0, 1, 1, 2, 3])
        loads = [(event.get("path"), event["status"]) for event in report["loads"]]
        self.assertIn(("./Scoped/helpers.ml", "already_loaded"), loads)
        self.assertIn(("Cycle/root.ml", "load_cycle"), loads)
        self.assertIn(("Missing/helpers.ml", "unmapped_load"), loads)
        self.assertIn(("../escape.ml", "unsupported_load_path"), loads)
        self.assertIn(("Bad/wrong_digest.ml", "source_snapshot_mismatch"), loads)
        self.assertNotIn("Future/later.ml", [path for path, _ in loads])
        self.assertTrue(any(edge["name"] == "ROOT_FACT" and edge["status"] == "excluded_target"
                            for edge in report["edges"]))
        self.assertTrue(any(edge.get("alias_chain") == ["CAPTURED_ALIAS"] and edge["cross_file"]
                            for edge in report["edges"]))
        _, _, packages = source_packages(view, helpers, report)
        reference = "\n".join(snippet.text for _, snippet, _ in packages)
        self.assertIn(f"let BASE_RULE = {quote}T{quote};;", reference)
        self.assertNotIn("PROOF_CODE", reference)
        self.assertNotIn("LATE_RULE", reference)
        self.assertTrue(all(snippet.origin and not required for _, snippet, required in packages))

        disabled, _, off, _ = walk(view, replace(cfg, cross_file=False, source_load_manifest="missing.json"))
        self.assertFalse(disabled)
        self.assertEqual(off["coverage"], "static_same_file_references")
        _, _, shallow, _ = walk(view, replace(cfg, max_load_depth=1))
        self.assertTrue(any(event["status"] == "load_depth_limit" for event in shallow["loads"]))
        _, _, limited, _ = walk(view, replace(cfg, max_load_files=1))
        self.assertTrue(any(event["status"] == "load_file_limit" for event in limited["loads"]))

    def test_forced_loads_rebind_but_needs_does_not(self):
        files = {
            "first.ml": theorem("SHARED_BINDING", "P", "FIRST_PROOF"),
            "second.ml": theorem("SHARED_BINDING", "Q", "SECOND_PROOF"),
        }
        manifest = {"version": 1, "root": self.folder.relative_to(repo_path(".")).as_posix(),
                    "files": {name: {"proof": name, "proof_sha256": sha256(text)} for name, text in files.items()}}
        for name, text in files.items():
            (self.folder / name).write_bytes(text.encode("utf-8"))
        (self.folder / "loads.json").write_text(json.dumps(manifest), encoding="utf-8")
        text = ('needs "first.ml";;\nloadt "second.ml";;\n'
                "let SAVED_RULE = SHARED_BINDING;;\n"
                'loads "first.ml";;\n' + theorem("ROOT_FACT", "T", "USE [SAVED_RULE; SHARED_BINDING]"))
        index = SourceIndex(text, self.config)
        view = SourceView(index, index.bindings["ROOT_FACT"][0], "root.ml", "", sha256(text), "", ())
        helpers, _, report, _ = walk(view, self.config)
        self.assertEqual([item.binding.statement for item in helpers], ["Q", "P"])
        self.assertEqual([event["status"] for event in report["loads"]], ["loaded"] * 3)

    def test_dataset_uses_nested_masked_snapshot_with_original_oracle(self):
        raw = extract_records(topic="Polytope", target_key="Krein_Milman_Minkowski")[0]
        row, report = prepare_selection(raw, ContextConfig(cross_file=True)).render()
        helper = next(node for node in report["dependency_graph"]["nodes"] if node["name"] == "CONVEX_CONVEX_HULL")
        self.assertEqual(helper["load_chain"], ["Multivariate/paths.ml", "Multivariate/convex.ml"])
        self.assertEqual(helper["selection"], "selected")
        self.assertTrue(helper["reference_path"].endswith("/stmts/hol-light/convex.ml"))
        self.assertIn("let CONVEX_CONVEX_HULL =", row["hol_light_reference_context"])
        self.assertNotIn("let CONVEX_CONVEX_HULL = prove", row["hol_light_reference_context"])
        self.assertEqual(row["metadata"]["context_experiment"]["arm"], "context-cross-file")
        self.assertEqual(row["isabelle_theory_template"], raw["isabelle_theory_template"])
        self.assertEqual(row["isabelle_context_before_target"], raw["isabelle_context_before_target"])
        self.assertTrue(any(e["name"] == "relative_interior" and e.get("reference_selection") == "selected"
                            for e in report["dependency_graph"]["edges"]))
        self.assertLessEqual(len(row["hol_light_reference_context"]), 16000)
