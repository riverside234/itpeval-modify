"""Mode A on the two aligned JSON datasets."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import read_jsonl, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light import extract_records as extract_babel
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.input_contract import CONTEXT_FIELDS
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import FACTS_VERSION
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.context_helpers.context import prepare_selection
from eval.pipeline.hol_light_to_isabelle.context_helpers.contracts import ContextConfig, SelectionFailure
from eval.pipeline.hol_light_to_isabelle.context_helpers.datasets import DATASETS
from eval.pipeline.hol_light_to_isabelle.context_helpers.workflow import run_experiment
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as extract_hundred
from eval.pipeline.hol_light_to_isabelle.isabelle_references import REFERENCE_FIELD, proof_context
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.common import DATASET_ROOT
from eval.pipeline.inference.config import InferenceConfig

MODULE = "eval.pipeline.hol_light_to_isabelle"


class AlignedDatasetTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.babel, = extract_babel(topic="circle_average", target_key="circleAverage_center_eq")
        cls.hundred, = extract_hundred(topic="015_the_fundamental_theorem_of_integral_calculus",
                                       target_key="rsum_bound")

    def test_bounded_context_preserves_original_theory_and_uses_pinned_source(self):
        cases = (("babel-formal", self.babel, "circleAverage_center_independent"),
                 ("hundred-theorems", self.hundred, "DIVISION_UBOUND"))
        config = ContextConfig(source_context_chars=4000, isabelle_context_chars=3000)
        for dataset, raw, helper in cases:
            with self.subTest(dataset=dataset):
                row, report = prepare_selection(raw, config).render()
                for field in (*CONTEXT_FIELDS, "hol_light_proof"):
                    self.assertEqual(raw[field], row[field], field)
                self.assertTrue(report["dependency_graph"]["source_path"].startswith(
                    f"eval/data/proofs.json:{dataset}:"))
                self.assertIn(helper, {node["name"] for node in report["dependency_graph"]["nodes"]})
                self.assertEqual(len(raw["hol_light_reference_context"]), report["baseline"]["hol_light"]["selected_chars"])
                self.assertEqual(config.source_context_chars, report["selection"]["hol_light"]["budget_chars"])
                self.assertEqual(config.isabelle_context_chars, report["selection"]["isabelle"]["budget_chars"])
                prompt = DATASETS[dataset].prompt(row).user_prompt
                self.assertIn(row["isabelle_prompt_context"], prompt)
                self.assertIn(row["hol_light_reference_context"], prompt)
                self.assertNotIn(raw["hol_light_reference_context"], prompt)
                self.assertNotIn(raw["isabelle_target_name"], {
                    snippet["name"] for snippet in report["selection"]["isabelle"]["selected_snippets"]})
        mismatched = {**self.babel, "metadata": {**self.babel["metadata"], "hol_light_proof_sha256": "0" * 64}}
        with self.assertRaises(SelectionFailure) as error:
            prepare_selection(mismatched, config)
        self.assertEqual("source_snapshot_mismatch", error.exception.category)

    def test_proof_examples_use_the_aligned_reference(self):
        for extract, raw in ((extract_babel, self.babel), (extract_hundred, self.hundred)):
            with self.subTest(dataset=raw["source"]):
                proof_row, = extract(topic=raw["topic"], target_key=raw["target_key"], isabelle_reference_proofs=True)
                row, _ = prepare_selection(proof_row, ContextConfig()).render()
                self.assertLessEqual(len(proof_context(row)), 8000)
                self.assertGreater(row["metadata"][REFERENCE_FIELD]["proof_count"], 0)
                self.assertTrue(all(example["source"].startswith("eval/data/proofs.json:")
                                    for example in row["metadata"][REFERENCE_FIELD]["proofs"]))

    def test_native_arm_routes_the_dataset_and_compares_the_same_oracle(self):
        native_actions = []

        class Native:
            def request(self, record, sketch, *, action, fact_names=(), **options):
                native_actions.append((record["source"], action, record["isabelle_statement"]))
                result = {"success": True, "error": "", "import_resolution": {"resolved_imports": ["Main"]}}
                if action == "inspect_facts":
                    facts = [{"requested": name, "status": "resolved", "name": name,
                              "scope": "global", "propositions": ["P ==> P"]} for name in fact_names]
                    result["fact_inspection"] = {"version": FACTS_VERSION, "boundary": "before_oracle", "facts": facts}
                elif action == "search":
                    result.update(target_closed=True, isabelle_proof="by simp", step_results=[])
                return result

        backend = {"backend": "isabelle-native", "isabelle_version": "Isabelle2026", "backend_fingerprint": "test"}
        root = repo_path("eval/results")
        root.mkdir(parents=True, exist_ok=True)
        config = ContextConfig(max_prompt_chars=250_000)
        parallel = {"workers": 1, "memory_per_worker_gb": 1, "dependency_threads": 1}
        with tempfile.TemporaryDirectory(dir=root) as temp, patch(
                MODULE + ".context_helpers.workflow.prepare_batch",
                side_effect=lambda cfg, records, plan: (cfg, backend, lambda _: Native())), patch(
                MODULE + ".babel_formal_pipeline.v2_dsp.generate_sketch.call_draft_model",
                return_value="by simp") as model:
            for raw in (self.babel, self.hundred):
                run = Path(temp) / raw["source"]
                for arm in ("baseline", "context-native"):
                    result = run_experiment([raw], output=run / arm, arm=arm, helper_config=config,
                        dataset_root=DATASET_ROOT, inspect_only=False, native_config=DspConfig(),
                        llm=InferenceConfig(), parallel=parallel)
                    self.assertEqual(1, result["verified"])
                compiled, = read_jsonl(run / "context-native" / "verified.jsonl")
                self.assertEqual(raw["source"], compiled["source"])
                self.assertEqual(raw["isabelle_statement"], compiled["isabelle_statement"])
                self.assertIn("P ==> P", compiled["isabelle_prompt_context"])
                self.assertTrue((run / "comparison.json").is_file())
        self.assertEqual(4, model.call_count)
        for raw in (self.babel, self.hundred):
            self.assertEqual(["context", "search", "inspect_facts", "search"],
                             [action for source, action, statement in native_actions
                              if source == raw["source"] and statement == raw["isabelle_statement"]])
