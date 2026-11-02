"""Regression cases from the 41 context failures committed in fabeacf1."""
import hashlib
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import native_search as native
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records


class ContextRegressions(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = extract_records()

    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="context-regressions-", dir=base)
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.job = self.path / "job"
        self.job.mkdir()

    def test_five_inner_product_targets_allow_the_earlier_scoped_helper(self):
        rows = [r for r in self.records if r['topic'].startswith('078_') and r['target_key'] in {
            'norm_cauchy_schwarz', 'norm_eq', 'norm_eq_1', 'norm_le', 'norm_lt'}]
        self.assertEqual(5, len(rows))
        for row in rows:
            context = validate_context(row)
            self.assertIn('dot_square_norm', context.prior_names)
            later = context.template[len(context.prefix):]
            self.assertIn('lemma dot_square_norm:', later)
            forbidden = native.forbidden_fact_names(context)
            self.assertNotIn('dot_square_norm', forbidden)
            self.assertIn(row['isabelle_target_name'], forbidden)
            self.assertIn('norm_eq_square', forbidden)
            self.assertNotIn('lemma norm_eq_square:', context.prefix)

    def fixture_source(self):
        root = self.path / "afp/thys"
        file = root / "Bertrands_Postulate/bertrand.ML"
        file.parent.mkdir(parents=True)
        content = b"structure Bertrand = struct end;\n"
        file.write_bytes(content)
        mapping = {('Bertrand', 'bertrand.ML'): ('Bertrands_Postulate/bertrand.ML', hashlib.sha256(content).hexdigest())}
        return root, file, content, mapping

    def test_all_21_bertrand_contexts_stage_only_the_exact_ml_companion(self):
        root, file, content, mapping = self.fixture_source()
        rows = [r for r in self.records if r['topic'].startswith('098_') and 'ML_file' in r['isabelle_context_before_target']]
        self.assertEqual(21, len(rows))
        with patch.dict(native.AUXILIARY_SOURCES, mapping):
            for row in rows:
                context = validate_context(row)
                sources = native.stage_auxiliary_files(context.prefix, context.theory_name,
                    DspConfig(session_roots=(str(root),)), self.job)
                self.assertEqual(1, len(sources))
                self.assertEqual(str(file.resolve()), sources[0]['source'])
                self.assertEqual(content, (self.job / 'bertrand.ML').read_bytes())
        self.assertEqual(['bertrand.ML'], sorted(p.name for p in self.job.iterdir()))

    def test_auxiliary_support_accepts_string_and_both_cartouche_spellings(self):
        root, _, _, mapping = self.fixture_source()
        with patch.dict(native.AUXILIARY_SOURCES, mapping):
            for literal in ('"bertrand.ML"', r'\<open>bertrand.ML\<close>', '‹bertrand.ML›'):
                result = native.stage_auxiliary_files('ML_file ' + literal, 'Bertrand',
                    DspConfig(session_roots=(str(root / 'Bertrands_Postulate'),)), self.job)
                self.assertEqual('bertrand.ML', result[0]['file'])

    def test_missing_modified_and_unknown_auxiliary_files_fail_before_execution(self):
        prefix = r'ML_file \<open>bertrand.ML\<close>'
        with self.assertRaisesRegex(native.NativeFailure, 'prepare_afp'):
            native.stage_auxiliary_files(prefix, 'Bertrand', DspConfig(), self.job)
        root, file, _, mapping = self.fixture_source()
        file.write_text('different source')
        with patch.dict(native.AUXILIARY_SOURCES, mapping), self.assertRaisesRegex(native.NativeFailure, 'hash mismatch'):
            native.stage_auxiliary_files(prefix, 'Bertrand', DspConfig(session_roots=(str(root),)), self.job)
        with self.assertRaisesRegex(native.NativeFailure, 'No audited auxiliary'):
            native.stage_auxiliary_files('ML_file "../elsewhere.ML"', 'Bertrand', DspConfig(), self.job)
        self.assertFalse(list(self.job.iterdir()))

    def test_stale_polynomial_inputs_explain_reextraction_without_running_isabelle(self):
        row = next(r for r in self.records if r['topic'].startswith('089_'))
        context = validate_context(row)
        old_prefix = context.prefix.replace('setup_lifting type_definition_poly', '')
        with self.assertRaisesRegex(native.NativeFailure, 'Re-extract') as caught:
            native.stage_auxiliary_files(old_prefix, 'Polynomial', DspConfig(), self.job)
        self.assertEqual('input_error', caught.exception.category)
        self.assertEqual([], native.stage_auxiliary_files(context.prefix, 'Polynomial', DspConfig(), self.job))

    def test_request_records_auxiliary_identity_and_context_budget_without_importing_target(self):
        root, _, content, mapping = self.fixture_source()
        row = next(r for r in self.records if r['topic'].startswith('098_'))
        engine = native.NativeSearch(DspConfig(session_roots=(str(root),), context_step_timeout_s=90))
        with patch.dict(native.AUXILIARY_SOURCES, mapping), patch.object(engine, 'infrastructure', return_value=(self.path, 'Prepared')), patch.object(
                engine, 'encode_symbols', side_effect=lambda x: x), patch.object(engine, 'run_build', return_value=0), patch.object(
                native, 'read_result', return_value={'success': True}):
            engine.request(row, '', directory=self.job, action='context', heuristics=(), deadline=time.monotonic()+120)
        data = json.loads((self.job / 'input.json').read_text())
        self.assertEqual('90', data['context_step_timeout_s'])
        self.assertEqual('10', data['step_timeout_s'])
        self.assertEqual(['bertrand.ML:' + hashlib.sha256(content).hexdigest()], data['auxiliary_sources'])
        self.assertNotIn('Bertrand', (self.job / 'DSP_Driver.thy').read_text())
        self.assertIn('Pratt_Certificate', (self.job / 'ROOT').read_text())

    def test_context_timeout_remains_positive_bounded_and_separate_from_proof_steps(self):
        self.assertEqual(120, DspConfig().context_step_timeout_s)
        self.assertEqual(10, DspConfig().step_timeout_s)
        for value in (0, -1, 0.0001, True, float('inf')):
            with self.assertRaises(ValueError):
                DspConfig(context_step_timeout_s=value)


if __name__ == '__main__':
    unittest.main()
