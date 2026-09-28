import unittest

from eval.pipeline.hol_light_to_isabelle.aligned_data import iter_topics
from eval.pipeline.hol_light_to_isabelle.sanitize_isabelle import sanitize_target


class SanitizeTests(unittest.TestCase):
    def test_preserves_masked_proof_prefix(self):
        topic, = iter_topics(topic="polynomial")
        target = sanitize_target(topic.isabelle_stmt_content, "eval_X_minus")
        self.assertEqual("unfolding X_minus_def", target.proof_prefix)
        start, end = target.proof_span
        self.assertEqual("sorry", target.theory_template[start:end])

    def test_rejects_completed_target_proof(self):
        content = 'theory T imports Main begin\nlemma x: "True" by simp\nend\n'
        with self.assertRaises(ValueError):
            sanitize_target(content, "x")


if __name__ == "__main__":
    unittest.main()
