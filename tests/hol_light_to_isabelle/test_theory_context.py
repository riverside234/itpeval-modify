import copy
import unittest

from eval.pipeline.hol_light_to_isabelle.common import align_samples, sha256
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.sanitize_isabelle import sanitize_target
from eval.pipeline.hol_light_to_isabelle.theory_context import normalize_body, tokens, validate_context


class ContextTests(unittest.TestCase):
    def test_all_163_targets_retain_scopes_and_exclude_later_facts(self):
        records = extract_records()
        self.assertEqual(163, len(records))
        self.assertEqual(16, len({row["topic"] for row in records}))
        for record in records:
            with self.subTest(topic=record["topic"], target=record["target_key"]):
                context = validate_context(record)
                theory = context.theory("by simp")
                self.assertTrue(theory.startswith(context.preamble))
                words = [token.text for token in tokens(theory) if token.kind == "word"]
                self.assertEqual(words.count("begin"), words.count("end"))
                self.assertNotIn(record["isabelle_target_name"], context.prior_names)

    def test_scope_words_in_comments_and_terms_are_not_commands(self):
        record = extract_records(topic="circle_average",
                                 target_key="circleAverage_center_independent")[0]
        original = validate_context(record)
        template = record["isabelle_theory_template"].replace(
            "imports Main", 'imports Main (* end (* begin *) end *)')
        target = sanitize_target(template, record["isabelle_target_name"])
        record.update(isabelle_theory_template=template,
                      isabelle_context_before_target=target.context_before_target,
                      isabelle_target_proof_span=list(target.proof_span))
        record["metadata"]["isabelle_stmt_sha256"] = sha256(template)
        self.assertEqual(original.depth, validate_context(record).depth)

    def test_rejects_stale_statement_prefix_span_and_hash(self):
        record = extract_records(topic="circle_average",
                                 target_key="circleAverage_center_independent")[0]
        for field, value in (
            ("isabelle_statement", 'lemma fake: "False"'),
            ("isabelle_context_before_target", "theory Other imports Main begin"),
            ("isabelle_target_proof_span", [-5, -1]),
            ("isabelle_proof_prefix", "using fake"),
        ):
            changed = {**record, field: value}
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_context(changed)
        changed = copy.deepcopy(record)
        changed["metadata"]["isabelle_stmt_sha256"] = "stale"
        with self.assertRaisesRegex(ValueError, "hash"):
            validate_context(changed)

    def test_admission_guard_ignores_comments_but_blocks_code(self):
        self.assertEqual("by simp (* sorry is not code *)",
                         normalize_body("by simp (* sorry is not code *)"))
        for body in ("by sorry", "by (tactic \\<open>all_tac\\<close>)",
                     "by simp\nend", "proof -\n normalhammer\nqed",
                     "by simp\nML_val \\<open>1\\<close>"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                normalize_body(body)
        self.assertIn("sledgehammer", normalize_body(
            "proof -\n show True\n sledgehammer\nqed", allow_hammer=True))
        with self.assertRaises(ValueError):
            normalize_body("proof -\n show True\n sledgehammer\nqed")

    def test_missing_and_stale_samples_remain_in_the_cohort(self):
        record = extract_records(topic="circle_average",
                                 target_key="circleAverage_center_independent")[0]
        record["draft"] = "Saved Draft"
        stale = {**record, "sample_idx": 0, "draft": "Old Draft", "isabelle_proof": "by simp"}
        aligned = align_samples([stale], [record], 2, pipeline="v2-itpeval")
        self.assertEqual(2, len(aligned))
        self.assertTrue(all(row["failure_category"] == "missing_sketch" for row in aligned))


if __name__ == "__main__":
    unittest.main()
