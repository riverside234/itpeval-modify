import unittest

from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records


class ExtractTests(unittest.TestCase):
    def test_full_cohort_has_unique_complete_pairs(self):
        records = extract_records()
        self.assertEqual(163, len(records))
        self.assertEqual(163, len({(r["theorem_id"], r["target_key"]) for r in records}))
        for record in records:
            self.assertTrue(record["hol_light_proof"].strip())
            self.assertTrue(record["isabelle_statement"].strip())
            start, end = record["isabelle_target_proof_span"]
            self.assertEqual("sorry", record["isabelle_theory_template"][start:end])
            self.assertNotIn("= prove", record["hol_light_reference_context"])

    def test_circle_average_source_and_target_are_distinct(self):
        record, = extract_records(topic="circle_average",
                                  target_key="circleAverage_center_independent")
        self.assertIn("REWRITE_TAC[circleAverage; circleMap]", record["hol_light_proof"])
        self.assertIn("lemma circleAverage_center_independent", record["isabelle_statement"])
        self.assertNotIn("integral_shift)", record["isabelle_statement"])


if __name__ == "__main__":
    unittest.main()
