"""Regression tests for the optional Isabelle proof examples."""

from importlib import import_module
import unittest

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context
from eval.pipeline.hol_light_to_isabelle.context_helpers.context import prepare_selection
from eval.pipeline.hol_light_to_isabelle.context_helpers.contracts import ContextConfig
from eval.pipeline.hol_light_to_isabelle.isabelle_references import (
    REFERENCE_FIELD, REFERENCE_TITLE, ReferenceProofs, proof_context,
)
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.context import isabelle_snippets, retrieve

PACKAGE = "eval.pipeline.hol_light_to_isabelle."


class ReferenceMatchingTests(unittest.TestCase):
    def test_only_matching_preceding_proofs_are_restored(self):
        full = """theory Test imports Main begin
lemma earlier: "True"
  proof -
    have "True" by simp
    show ?thesis ..
  qed
lemma different: "False" by (rule DIFFERENT_PROOF)
lemma dots: "True" ..
lemma goal: "True" by (rule TARGET_PROOF)
lemma later: "True" by (rule LATER_PROOF)
end
"""
        # The masked prefix can be a subset or even a different order than the
        # proof snapshot. A fact after the full target stays masked.
        masked = """theory Test imports Main begin
lemma different: "True"
  sorry
lemma earlier: "True"
  sorry
lemma dots: "True"
  sorry
lemma later: "True"
  sorry
"""
        refs = ReferenceProofs(full, "Test.thy", masked_theory="Test", target_name="goal",
                               target_statement='lemma goal: "True"')
        text, proofs = refs.restore(masked)
        self.assertEqual(["earlier", "dots"], [proof.name for proof in proofs])
        self.assertIn("show ?thesis ..\n  qed", text)
        self.assertIn('\nlemma dots: "True"\n  ..', text)
        for sentinel in ("DIFFERENT_PROOF", "TARGET_PROOF", "LATER_PROOF"):
            self.assertNotIn(sentinel, text)
        mismatch = ReferenceProofs(full, "Test.thy", masked_theory="Test", target_name="goal",
                                   target_statement='lemma goal: "False"')
        self.assertEqual("target_boundary_unmatched", mismatch.status)
        self.assertEqual((masked, []), mismatch.restore(masked))

    def test_most_match_fits_a_whole_proof_or_uses_the_masked_fact(self):
        masked = """theory Test imports Main begin
lemma sizeable_helper: "True"
  sorry
"""
        full = masked.replace("sorry", "by (simp add: " + "x" * 500 + ")")
        parts, scopes = isabelle_snippets(masked)
        refs = ReferenceProofs(full, "Test.thy", masked_theory="Test", target_name="goal")
        fitting, info = retrieve(parts, query="sizeable_helper", budget=256, mandatory=scopes,
                                 proof_sources={"": refs})
        self.assertIn("sorry", fitting)
        self.assertNotIn("simp add:", fitting)
        self.assertLessEqual(len(fitting), 256)
        self.assertTrue(all("reference_proof" not in item for item in info["selected_snippets"]))


class ReferencePipelineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.examples = (
            ("babel_formal_pipeline", "circle_average", "circleAverage_center_independent", "circleMap_zero"),
            ("hundred_theorems_pipeline", "015_the_fundamental_theorem_of_integral_calculus", "rsum_bound", "norm_diff2"),
            ("most_match_pipeline", "Canonical_Models", "compact_canon_qfree", "compact_prop"),
        )

    def test_three_datasets_use_reference_proofs_in_draft_and_sketch(self):
        for dataset, topic, target, helper in self.examples:
            with self.subTest(dataset=dataset):
                package = PACKAGE + dataset
                extract = import_module(package + ".extract_hol_light").extract_records
                masked, = extract(topic=topic, target_key=target)
                record, = extract(topic=topic, target_key=target, isabelle_reference_proofs=True)
                context = validate_context(record)
                self.assertEqual(validate_context(masked), context)
                self.assertEqual("sorry", context.template[slice(*context.proof_span)])
                self.assertEqual(masked["hol_light_reference_context"], record["hol_light_reference_context"])
                self.assertIsNone(proof_context(masked))
                view = proof_context(record)
                examples = record["metadata"][REFERENCE_FIELD]["proofs"]
                self.assertIn(helper, {row["name"] for row in examples})
                self.assertNotIn(target, {row["name"] for row in examples})
                if dataset == "most_match_pipeline":
                    self.assertLessEqual(len(view), 8000)
                    self.assertTrue(any("/afp/proofs/isabelle/" in row["source"] for row in examples))
                draft_module = import_module(package + ".prompt")
                self.assertIn(view.strip(), draft_module.build_draft_prompt(record).user_prompt)
                for backend in ("v2_dsp", "v2_dsp_pisa", "v2_itpeval"):
                    if dataset == "most_match_pipeline" and backend != "v2_dsp":
                        continue
                    backend_package = package + "." + backend
                    draft = {**record, "draft": "Show the claimed proposition."}
                    if backend != "v2_itpeval":
                        export = import_module(backend_package + ".export_dsp").export_record
                        if dataset == "babel_formal_pipeline":
                            source = {"expected_source": record["source"]}
                        else:
                            source = {}
                        direct = export(record, sketch_source="hol-light-proof", **source)
                        old = export(masked, sketch_source="hol-light-proof", **source)
                        self.assertNotEqual(direct["input_fingerprint"], old["input_fingerprint"])
                        build = import_module(backend_package + ".direct_sketch_prompt").build_direct_sketch_prompt
                        prompt = build(direct)
                        self.assertIn(REFERENCE_TITLE, prompt.user_prompt)
                        self.assertIn(view, prompt.user_prompt)
                        draft = export(draft, **source)
                    sketch = import_module(backend_package + ".sketch_prompt").build_sketch_prompt
                    self.assertIn(view, sketch(draft).user_prompt)
                with self.assertRaisesRegex(ValueError, "stale Isabelle reference"):
                    proof_context({**record, "isabelle_prompt_context": view + "\nextra"})

    def test_recursive_context_can_keep_examples_with_native_signatures(self):
        extract = import_module(PACKAGE + "most_match_pipeline.extract_hol_light").extract_records
        record, = extract(topic="Canonical_Models", target_key="compact_canon_qfree", isabelle_reference_proofs=True)
        selection = prepare_selection(record, ContextConfig())
        row, _ = selection.render()
        self.assertGreater(row["metadata"][REFERENCE_FIELD]["proof_count"], 0)
        name = "Ground_FOL_Compactness.compact_prop"
        self.assertIn(name, selection.shortlist)
        facts = [{"requested": key, "name": key, "scope": "global",
                  "status": "resolved" if key == name else "not_resolved",
                  "propositions": ["test_signature"] if key == name else []} for key in selection.shortlist]
        row, _ = selection.render(inspection={"version": "test", "facts": facts})
        text = proof_context(row)
        self.assertIn("test_signature", text)
        self.assertIn("Proof example from the Isabelle snapshot", text)
        self.assertEqual(["compact_prop"], [proof["name"] for proof in row["metadata"][REFERENCE_FIELD]["proofs"]])
        self.assertLessEqual(len(text), 8000)
