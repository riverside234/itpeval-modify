"""Check dependency evidence, prompt budgets, and arm isolation."""

from collections import Counter
from dataclasses import replace
import os
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import read_jsonl, repo_path, sha256
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.checker import Checker
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import FACTS_VERSION, NativeSearch
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.context_helpers.context import prepare_selection
from eval.pipeline.hol_light_to_isabelle.context_helpers.contracts import ContextConfig, SelectionFailure
from eval.pipeline.hol_light_to_isabelle.context_helpers.dependencies import walk
from eval.pipeline.hol_light_to_isabelle.context_helpers.selection import Selection
from eval.pipeline.hol_light_to_isabelle.context_helpers.source_index import SourceIndex, SourceView
from eval.pipeline.hol_light_to_isabelle.context_helpers.workflow import check_outputs, run_experiment
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.common import DATASET_ROOT
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.context import Snippet
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.extract_hol_light import extract_records
from eval.pipeline.inference.config import InferenceConfig


class DependencyTests(unittest.TestCase):
    def test_exact_edges_order_aliases_and_shared_child(self):
        text = """
let BASE_FACT = prove (|T|, BASE_PROOF);;
let FIRST_FACT = prove (|T|, RULE BASE_FACT);;
let OTHER_FACT = prove (|T|, RULE BASE_FACT);;
let SHADOW_FACT = prove (|T|, A_TAC);;
let OLD_FACT = prove (|T|, A_TAC);;
let OLD_FACT = BUILD_THM some_list;;
let FIRST_ALIAS = FIRST_FACT;;
let CYCLE_A = CYCLE_B;;
let CYCLE_B = CYCLE_A;;
needs "Library/not_in_snapshot.ml";;
let ROOT_FACT = prove (|T|,
   (* COMMENT_FACT *)
   RULE [FIRST_ALIAS; OTHER_FACT; OLD_FACT; LATER_FACT; ROOT_FACT; CYCLE_B] THEN
   (let SHADOW_FACT = TRUTH in RULE SHADOW_FACT) THEN
   READ "STRING_FACT" THEN TERM |QUOTED_FACT|);;
let LATER_FACT = prove (|T|, A_TAC);;
""".replace("|", chr(96))
        config = ContextConfig()
        index = SourceIndex(text, config)
        root = index.bindings["ROOT_FACT"][0]
        view = SourceView(index, root, "proof.ml", "stmt.ml", sha256(text), "", ())
        helpers, _, report, _ = walk(view, config)
        self.assertEqual([item.binding.name for item in helpers], ["FIRST_FACT", "OTHER_FACT", "BASE_FACT"])
        self.assertEqual([item["depth"] for item in report["nodes"]], [0, 1, 1, 2])
        self.assertEqual(report["loads"][0]["status"], "unresolved_load")
        edges = report["edges"]
        statuses = {e["name"]: e["status"] for e in edges}
        self.assertEqual(statuses["FIRST_ALIAS"], "resolved_alias")
        self.assertEqual(statuses["OLD_FACT"], "unsupported_binding")
        self.assertEqual(statuses["LATER_FACT"], "not_yet_bound")
        self.assertEqual(statuses["SHADOW_FACT"], "possible_local_binding")
        self.assertEqual(statuses["ROOT_FACT"], "excluded_target")
        self.assertEqual(statuses["CYCLE_B"], "cycle_or_forward_alias")
        self.assertTrue(any(e.get("shared_child") and e["name"] == "BASE_FACT" for e in edges))
        self.assertFalse({"COMMENT_FACT", "STRING_FACT", "QUOTED_FACT"} & statuses.keys())
        _, _, bounded, _ = walk(view, replace(config, dependency_depth=1))
        self.assertTrue(any(e["name"] == "BASE_FACT" and e["status"] == "depth_limit" for e in bounded["edges"]))
        _, _, bounded, _ = walk(view, replace(config, max_helpers=1))
        self.assertTrue(any(e["status"] == "node_limit" for e in bounded["edges"]))

    def test_oversized_package_keeps_pinned_scope_and_allows_other_branch(self):
        scope = Snippet("Example", "locale", 0, 50, "locale Example = fixes x")
        anchor = Snippet("anchor", "lemma", 100, 110, 'lemma anchor: "P" sorry')
        huge = Snippet("huge", "definition", 50, 99, "definition huge " + "x" * 350)
        sibling = Snippet("sibling", "lemma", 200, 250, 'lemma sibling: "Q" sorry')
        selection = Selection(256, [scope])
        self.assertFalse(selection.add_optional(anchor, [huge]))
        self.assertFalse(selection.add_optional(anchor))
        self.assertTrue(selection.add_optional(sibling))
        context, metadata = selection.finish([scope, anchor, huge, sibling])
        self.assertEqual(["Example", "sibling"], [item["name"] for item in metadata["selected_snippets"]])
        self.assertLessEqual(len(context), 256)
        with self.assertRaises(SelectionFailure) as error:
            Selection(256, [huge])
        self.assertEqual(error.exception.category, "mandatory_context_overflow")


class ContextExperimentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = extract_records(topic="Canonical_Models", target_key="compact_canon_qfree")[0]

    def test_known_imported_signatures_and_unchanged_verifier_input(self):
        first, report = prepare_selection(self.raw, ContextConfig()).render()
        second, _ = prepare_selection(self.raw, ContextConfig()).render()
        self.assertEqual(first, second)
        selected = {fact["requested"] for fact in report["target_candidates"] if fact["selection"] == "selected"}
        self.assertLessEqual({"Ground_FOL_Compactness.compact_prop", "Ground_FOL_Compactness.qfree_formsubst"}, selected)
        for field in ("isabelle_theory_template", "isabelle_context_before_target", "isabelle_statement",
                      "isabelle_proof_prefix", "isabelle_target_proof_span", "hol_light_proof"):
            self.assertEqual(self.raw[field], first[field])
        self.assertNotIn("let COMPACT_CANON_QFREE = prove", first["hol_light_reference_context"])
        self.assertLessEqual(len(first["hol_light_reference_context"]), 16000)
        self.assertLessEqual(len(first["isabelle_prompt_context"]), 8000)

    def test_second_hop_can_change_reference_selection(self):
        raw = extract_records(topic="Conformal_Mappings", target_key="Bloch")[0]
        row, report = prepare_selection(raw, ContextConfig()).render()
        name = "HOLOMORPHIC_COMPLEX_DERIVATIVE"
        nodes = report["dependency_graph"]["nodes"]
        self.assertTrue(any(n["depth"] == 2 and n["name"] == name and n["selection"] == "selected"
                            for n in nodes))
        self.assertIn(name, [item[0] for item in report["changes"]["hol_light"]["gained"]])
        self.assertIn("let " + name + " =", row["hol_light_reference_context"])
        self.assertNotIn("let " + name + " = prove", row["hol_light_reference_context"])


    def test_mocked_lab_workflow_reuses_prepared_backend_and_separates_arms(self):
        calls = Counter()
        backend = {"backend": "isabelle-native", "isabelle_version": "Isabelle2026",
                   "backend_fingerprint": "test_backend", "distribution_sources_sha256": "test_sources"}

        class Native:
            def request(self, record, sketch, *, action, fact_names=(), **options):
                calls[action] += 1
                result = {"success": True, "error": "", "import_resolution": {"resolved_imports": ["Main"]}}
                if action == "inspect_facts":
                    facts = []
                    for name in fact_names:
                        resolved = name.endswith(".compact_prop")
                        facts.append({"requested": name, "status": "resolved" if resolved else "not_resolved",
                                      "name": name if resolved else "", "scope": "global" if resolved else "",
                                      "propositions": ["P ==> P"] if resolved else []})
                    result["fact_inspection"] = {"version": FACTS_VERSION, "boundary": "before_oracle", "facts": facts}
                elif action == "search":
                    result.update(target_closed=True, isabelle_proof="by simp", step_results=[])
                return result

        root = repo_path("eval/results")
        root.mkdir(parents=True, exist_ok=True)
        parallel = {"workers": 1, "memory_per_worker_gb": 1, "dependency_threads": 1}
        module = "eval.pipeline.hol_light_to_isabelle"
        with tempfile.TemporaryDirectory(dir=root) as tmp, patch(
                module + ".context_helpers.workflow.prepare_batch",
                side_effect=lambda cfg, records, plan: (cfg, backend, lambda _: Native())), patch(
                module + ".babel_formal_pipeline.v2_dsp.generate_sketch.call_draft_model",
                return_value="by simp") as model:
            root = Path(tmp)
            common = dict(dataset_root=DATASET_ROOT, inspect_only=False,
                          native_config=DspConfig(), llm=InferenceConfig(), parallel=parallel)
            for arm in ("baseline", "context-native", "context-native",
                        "context-cross-file", "context-native-cross-file"):
                helper_config = ContextConfig(cross_file=arm.endswith("-cross-file"))
                result = run_experiment([self.raw], output=root / arm, arm=arm,
                                        helper_config=helper_config, **common)
                self.assertEqual(result["verified"], 1)
            self.assertEqual(model.call_count, 4)
            self.assertEqual(calls, {"context": 2, "inspect_facts": 3, "search": 4})
            baseline, context = [read_jsonl(root / arm / "inputs.jsonl")[0] for arm in ("baseline", "context-native")]
            self.assertEqual(baseline["isabelle_statement"], context["isabelle_statement"])
            self.assertNotEqual(baseline["input_fingerprint"], context["input_fingerprint"])
            self.assertIn("P ==> P", context["isabelle_prompt_context"])
            self.assertNotIn("lemma qfree_formsubst", context["isabelle_prompt_context"])
            self.assertTrue((root / "comparison.json").is_file())
            self.assertRaises(ValueError, check_outputs, root / "context-native", "baseline")


@unittest.skipUnless(os.environ.get("ITPEVAL_NATIVE_ISABELLE2026_CONFIG"),
                     "native fact inspection requires the lab Isabelle2026 toolchain")
class NativeInspectionTests(unittest.TestCase):
    def test_named_fact_bundle_scope_and_target_exclusion(self):
        config = DspConfig.load(os.environ["ITPEVAL_NATIVE_ISABELLE2026_CONFIG"])
        extra = """
lemma inspect_good: "x = (x::nat)" sorry
lemmas inspect_bundle = inspect_good TrueI
context
  fixes p :: bool
  assumes inspect_local: p
begin
end
"""
        row = control_record("by simp", extra_context=extra)
        row["isabelle_theory_template"] = row["isabelle_theory_template"].rsplit("end", 1)[0] + \
            'lemma inspect_later: "True" sorry\nend\n'
        directory = Checker(config).directory("fact-inspection-test-")
        config.metadata()
        result = NativeSearch(config).request(
            row, "", directory=directory, action="inspect_facts", heuristics=(),
            fact_names=("inspect_good", "inspect_bundle", "inspect_local", "v2_control", "inspect_later"),
            deadline=time.monotonic() + config.target_timeout_s)
        self.assertTrue(result["success"], result["error"])
        self.assertFalse(result["target_closed"])
        self.assertFalse(result["isabelle_proof"])
        self.assertFalse(any(step["mode"] in {"hammer", "search"} for step in result["step_results"]))
        facts = {fact["requested"]: fact for fact in result["fact_inspection"]["facts"]}
        self.assertEqual(facts["inspect_good"]["status"], "resolved")
        self.assertIn("nat", facts["inspect_good"]["propositions"][0])
        self.assertEqual(len(facts["inspect_bundle"]["propositions"]), 2)
        self.assertEqual(facts["inspect_local"]["status"], "not_resolved")
        self.assertEqual(facts["v2_control"]["status"], "excluded")
        self.assertEqual(facts["inspect_later"]["status"], "excluded")
