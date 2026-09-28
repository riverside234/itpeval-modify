import unittest

from eval.pipeline.hol_light_to_isabelle.aligned_data import iter_topics
from eval.pipeline.hol_light_to_isabelle.inventory import (
    inventory_hol_declarations, inventory_topic,
)


class InventoryTests(unittest.TestCase):
    def test_cohort_counts_and_casefold_mapping(self):
        rows = [inventory_topic(topic) for topic in iter_topics()]
        self.assertEqual(16, len(rows))
        self.assertEqual(143, sum(len(r["exact_name_matches"]) for r in rows))
        self.assertEqual(163, sum(len(r["candidate_pairs"]) for r in rows))
        group = next(r for r in rows if r["topic"] == "group")
        self.assertIn(("MUL_LEFT_CANCEL", "mul_left_cancel", "casefold_name_match"),
                      group["candidate_pairs"])

    def test_terminator_inside_quotation_does_not_end_declaration(self):
        quote = chr(96)
        content = f"let example = prove ({quote}!x. x = x;;{quote}, REFL_TAC);;\n"
        declarations = inventory_hol_declarations(content, masked=False)
        self.assertEqual(1, len(declarations))
        self.assertEqual("!x. x = x;;", declarations[0].statement)
        self.assertEqual("REFL_TAC", declarations[0].proof)


if __name__ == "__main__":
    unittest.main()
