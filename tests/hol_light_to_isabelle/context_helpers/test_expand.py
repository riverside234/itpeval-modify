"""Complete source helper packages and their direct Sketch contract."""

from collections import Counter
from copy import deepcopy
from dataclasses import replace
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import read_jsonl, repo_path, sha256
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light import extract_records as extract_babel
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.checker import Checker
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.input_contract import CONTEXT_FIELDS, input_metadata
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import FACTS_VERSION
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.context_helpers.context import prepare_selection
from eval.pipeline.hol_light_to_isabelle.context_helpers.contracts import ContextConfig
from eval.pipeline.hol_light_to_isabelle.context_helpers.datasets import dataset_for
from eval.pipeline.hol_light_to_isabelle.context_helpers.dependencies import walk
from eval.pipeline.hol_light_to_isabelle.context_helpers.expansion import select_source_helpers
from eval.pipeline.hol_light_to_isabelle.context_helpers.prompts import BUNDLE_DIGEST, BUNDLE_FIELD, render_support
from eval.pipeline.hol_light_to_isabelle.context_helpers.source_index import SourceIndex, SourceView
from eval.pipeline.hol_light_to_isabelle.context_helpers.workflow import export_selected, prepare_records, run_experiment
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as extract_hundred
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.common import DATASET_ROOT
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.extract_hol_light import extract_records as extract_most
from eval.pipeline.inference.config import InferenceConfig

MODULE = "eval.pipeline.hol_light_to_isabelle"


class SourceHelperSelectionTests(unittest.TestCase):
    def setUp(self):
        oversized = "NAME_" + "X" * 96
        text = f"""
let CHILD_FACT = prove (|T|, (* entire proof *) USE MISSING_FACT);;
let LEFT_FACT = prove (|T|, USE CHILD_FACT);;
let RIGHT_FACT = prove (|T|, USE CHILD_FACT);;
let LARGE_FACT = prove (|T|, USE {oversized});;
let SMALL_FACT = prove (|T|, DONE_TAC);;
let ROOT_FACT = prove (|T|, USE [LEFT_FACT; RIGHT_FACT; LARGE_FACT; SMALL_FACT]);;
let LATER_FACT = prove (|T|, LATER_TAC);;
""".replace("|", chr(96))
        self.config = ContextConfig(max_helper_proof_chars=80)
        index = SourceIndex(text, self.config)
        source = SourceView(index, index.bindings["ROOT_FACT"][0], "example.ml", "example-stmts.ml",
                            sha256(text), "", ())
        self.helpers, _, self.graph, _ = walk(source, self.config)

    def select(self, config=None, facts=(), *, base_chars=500):
        return select_source_helpers(self.helpers, self.graph, facts, config or self.config,
                                     base_prompt_chars=base_chars)

    def test_whole_proofs_child_before_both_parents_and_unavailable_child(self):
        bundle, report = self.select()
        self.assertEqual(bundle, self.select()[0])
        helpers = bundle["helpers"]
        self.assertEqual(["CHILD_FACT", "LEFT_FACT", "RIGHT_FACT", "SMALL_FACT"],
                         [helper["name"] for helper in helpers])
        self.assertEqual("(* entire proof *) USE MISSING_FACT", helpers[0]["proof"])
        reports = {node["name"]: node for node in report["nodes"]}
        self.assertEqual("proof_too_large", reports["LARGE_FACT"]["status"])
        self.assertEqual("unresolved_identifier", reports["CHILD_FACT"]["dependencies"][0]["evidence"])
        self.assertEqual(2, len(reports["CHILD_FACT"]["parents"]))
        self.assertEqual(len(render_support(helpers)), report["support_chars"])

    def test_whole_prompt_limit_omits_optional_proofs_and_keeps_small_branches(self):
        _, full = self.select()
        nodes = {node["name"]: node for node in full["nodes"]}
        first_cost = nodes["LEFT_FACT"]["added_support_chars"]
        settings = replace(self.config, max_prompt_chars=500 + first_cost + nodes["SMALL_FACT"]["added_support_chars"])
        bundle, report = self.select(settings)
        self.assertEqual(["LEFT_FACT", "SMALL_FACT"], [helper["name"] for helper in bundle["helpers"]])
        self.assertLessEqual(500 + report["support_chars"], settings.max_prompt_chars)
        left = next(node for node in report["nodes"] if node["name"] == "LEFT_FACT")
        self.assertEqual("budget_exhausted", left["dependencies"][0]["support"])
        child = next(node for node in report["nodes"] if node["name"] == "CHILD_FACT")
        self.assertEqual("max_prompt_chars", child["limit"])
        for setting in ("max_total_helper_proof_chars", "max_helper_support_chars"):
            bundle, report = self.select(replace(self.config, **{setting: 0}))
            self.assertFalse(bundle["helpers"])
            self.assertEqual(0, report["proof_chars"])
            self.assertEqual(0, report["support_chars"])

    def test_live_exact_matches_defer_only_their_own_branches(self):
        facts = [{"requested": name.lower(), "name": name.lower(), "source_name_match": name,
                  "availability": "resolved", "scope": "global", "selection": "selected"}
                 for name in ("LEFT_FACT", "RIGHT_FACT")]
        with_only_left, _ = self.select(facts=facts[:1])
        self.assertEqual(["CHILD_FACT", "RIGHT_FACT", "SMALL_FACT"],
                         [helper["name"] for helper in with_only_left["helpers"]])
        with_both, report = self.select(facts=facts)
        self.assertEqual(["SMALL_FACT"], [helper["name"] for helper in with_both["helpers"]])
        self.assertEqual(2, report["counts"]["native_candidate_supplied"])
        self.assertEqual(1, report["counts"]["parent_not_expanded"])
        snapshot = [{**facts[0], "availability": "snapshot_only"}]
        self.assertIn("LEFT_FACT", [h["name"] for h in self.select(facts=snapshot)[0]["helpers"]])


class ExpansionWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.babel, = extract_babel(topic="circle_average", target_key="circleAverage_center_eq")
        cls.hundred, = extract_hundred(topic="015_the_fundamental_theorem_of_integral_calculus",
                                       target_key="rsum_bound")
        cls.most, = extract_most(topic="Conformal_Mappings", target_key="Bloch")

    def test_real_inputs_share_context_and_keep_fingerprinted_helper_text_separate(self):
        for raw in (self.babel, self.hundred, self.most):
            with self.subTest(dataset=raw["source"]):
                selection = prepare_selection(raw, ContextConfig())
                base, _ = selection.render()
                row, report = selection.render(mode="expand")
                support = report["source_helper_expansion"]
                self.assertNotIn(BUNDLE_FIELD, base)
                self.assertTrue(row[BUNDLE_FIELD]["helpers"])
                for field in (*CONTEXT_FIELDS, "hol_light_proof"):
                    self.assertEqual(raw[field], row[field])
                for field in ("hol_light_reference_context", "isabelle_prompt_context"):
                    self.assertEqual(base[field], row[field])
                builder = dataset_for(raw).prompt
                old, new = builder(base), builder(row)
                self.assertEqual(old.system_prompt, new.system_prompt)
                self.assertNotEqual(old.version, new.version)
                self.assertEqual(support["support_chars"], len(new.user_prompt) - len(old.user_prompt))
                for helper in row[BUNDLE_FIELD]["helpers"]:
                    self.assertIn(helper["proof"], new.user_prompt)
                    self.assertNotIn(helper["proof"], row["hol_light_reference_context"])
                self.assertEqual(support["bundle_sha256"], input_metadata(row, "hol-light-proof")[BUNDLE_DIGEST])
                corrupted = deepcopy(row)
                corrupted[BUNDLE_FIELD]["helpers"][0]["proof"] += " THEN ALL_TAC"
                with self.assertRaisesRegex(ValueError, "stale source helper bundle"):
                    builder(corrupted)
                del corrupted[BUNDLE_FIELD]
                with self.assertRaisesRegex(ValueError, "missing.*source helper bundle"):
                    builder(corrupted)

    def test_prompt_guard_retains_a_target_when_even_masked_context_overflows(self):
        settings = ContextConfig(max_prompt_chars=256)
        prepared = prepare_records([self.babel], settings, arm="expand", dataset_root=DATASET_ROOT)
        rows, reports, blocked = export_selected(prepared, settings, dataset_for(self.babel))
        self.assertEqual(1, len(blocked))
        self.assertEqual("prompt_context_overflow", rows[0]["failure_category"])
        self.assertEqual(0, reports[0]["source_helper_expansion"]["support_chars"])

    def test_cross_file_proof_provenance_with_isabelle_examples(self):
        raw, = extract_most(topic="Polytope", target_key="Krein_Milman", isabelle_reference_proofs=True)
        row, report = prepare_selection(raw, ContextConfig(cross_file=True)).render(mode="expand")
        helper = next(h for h in row[BUNDLE_FIELD]["helpers"] if h["name"] == "CONVEX_HULL_EMPTY")
        self.assertTrue(helper["references"]["load_chain"])
        node = next(n for n in report["source_helper_expansion"]["nodes"] if n["id"] == helper["id"])
        self.assertEqual(sha256(helper["proof"]), node["proof_sha256"])
        self.assertGreater(row["metadata"]["isabelle_reference_proofs"]["proof_count"], 0)
        self.assertEqual("expand-cross-file", report["arm"])

    def test_one_sketch_and_one_native_search_per_arm_and_compatible_resume(self):
        calls = Counter()

        class Native:
            def request(self, record, sketch, *, action, fact_names=(), **options):
                calls[action] += 1
                response = {"success": True, "import_resolution": {"resolved_imports": ["Main"]}}
                if action == "inspect_facts":
                    response["fact_inspection"] = {
                        "version": FACTS_VERSION,
                        "facts": [{"requested": name, "status": "not_resolved"} for name in fact_names],
                    }
                elif action == "search":
                    response.update(target_closed=True, isabelle_proof=sketch, step_results=[])
                return response

        backend = {"backend": "isabelle-native", "isabelle_version": "Isabelle2026",
                   "backend_fingerprint": "expand-test"}
        parallel = {"workers": 1, "memory_per_worker_gb": 1, "dependency_threads": 1}
        settings = ContextConfig()
        root = repo_path("eval/results")
        root.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=root) as temp, patch(
                MODULE + ".context_helpers.workflow.prepare_batch",
                side_effect=lambda cfg, records, plan: (cfg, backend, lambda _: Native())), patch(
                MODULE + ".babel_formal_pipeline.v2_dsp.generate_sketch.call_draft_model",
                return_value='proof -\n  have h: "True" by simp\n  show ?thesis by simp\nqed') as model:
            for raw in (self.babel, self.hundred, self.most):
                run = Path(temp) / raw["source"]
                for arm in ("context-native", "expand-native", "expand-native"):
                    summary = run_experiment([raw], output=run / arm, arm=arm, helper_config=settings,
                        dataset_root=DATASET_ROOT, inspect_only=False, native_config=DspConfig(),
                        llm=InferenceConfig(), parallel=parallel)
                    self.assertEqual(1, summary["verified"])
                completed, = read_jsonl(run / "expand-native" / "verified.jsonl")
                self.assertTrue(completed[BUNDLE_FIELD]["helpers"])
                self.assertIn("expand_p", completed["sketch_prompt_version"])
                pairs = json.loads((run / "comparison.json").read_text(encoding="utf-8"))["expand-native"]
                self.assertEqual(1, pairs["both_pass"])
                self.assertEqual(0, pairs["incompatible_pairs"])
                self.assertGreater(pairs["outcomes"][0]["expand"]["source_helper_count"], 0)
            self.assertEqual(6, model.call_count)
            self.assertEqual(3, sum("COMPLETED HOL LIGHT HELPER PROOFS" in call.kwargs["user_prompt"]
                                    for call in model.call_args_list))
        self.assertEqual(6, calls["search"])
        self.assertEqual(9, calls["inspect_facts"])


@unittest.skipUnless(os.environ.get("ITPEVAL_NATIVE_ISABELLE2026_CONFIG"),
                     "local helper proof checking requires the lab Isabelle2026 toolchain")
class NativeExpansionTests(unittest.TestCase):
    def test_two_level_local_helpers_are_checked_with_hammer_reconstruction(self):
        config = DspConfig.load(os.environ["ITPEVAL_NATIVE_ISABELLE2026_CONFIG"])
        row = control_record(
            'proof -\n  have child: "True"\n    sledgehammer\n'
            '  have parent: "True" by (rule child)\n  show ?thesis by (rule parent)\nqed',
            sketch_source="hol-light-proof")
        result = Checker(config).check(row, force_hammer=True)
        self.assertTrue(result["verified"], result["verify_error"])
        self.assertGreater(result["search_summary"]["reconstruction_successes"], 0)
