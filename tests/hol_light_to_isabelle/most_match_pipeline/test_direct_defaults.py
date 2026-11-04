"""The committed most-match failure, direct CLI defaults, and repair diagnostics."""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.common import repo_path, RESULTS_DIR
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp import run, export_dsp, generate_sketch, prove
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp.direct_sketch_prompt import build_direct_sketch_prompt
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp.sketch_prompt import build_sketch_prompt
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import write_jsonl, read_jsonl
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.checker import failure_obligation, search_summary
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.input_contract import summarize_results

ENGINE = 'eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.'
MODE = 'hol-light-proof'
LOG = ('eval/results/hol_light_to_isabelle_v2/most-match/v2-dsp-isabelle2026/'
       'canonical-models-finite-subset-instance/direct/verified.jsonl')


class DirectDefaultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = extract_records(topic='Canonical_Models', target_key='finite_subset_instance')[0]

    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        folder = tempfile.TemporaryDirectory(prefix='direct-default-', dir=base)
        self.addCleanup(folder.cleanup)
        self.path = Path(folder.name)
        self.source = self.path/'records.jsonl'
        write_jsonl(self.source, [self.raw])

    def call(self, main, *args):
        stdout = io.StringIO()
        with patch.object(sys, 'argv', ['test', *map(str,args)]), redirect_stdout(stdout):
            main()
        return stdout.getvalue()

    def test_committed_failure_is_explicit_method_before_any_search(self):
        row = read_jsonl(repo_path(LOG))[0]
        self.assertEqual('finite_subset_instance', row['target_key'])
        self.assertEqual('sketch_step_failure', row['failure_category'])
        self.assertIn('intro impI', row['failed_obligation']['command'])
        self.assertIn(r'\<exists>t.', row['failed_obligation']['error'])
        self.assertEqual(0, row['search_summary']['hammer_attempts'])
        self.assertEqual(0, row['search_summary']['heuristic_attempts'])

    def test_run_and_generation_default_to_direct_with_bounded_context(self):
        for entry, args in ((run.main, ['--config','unused.local.json']), (generate_sketch.main, [])):
            with self.subTest(entry=entry.__module__):
                preview = json.loads(self.call(entry, '--records', self.source, '--dry-run', *args))
                self.assertEqual(MODE, preview['sketch_source'])
                self.assertFalse(preview['draft_used'])
                self.assertIn(self.raw['hol_light_proof'], preview['user_prompt'])
                self.assertIn(self.raw['isabelle_prompt_context'], preview['user_prompt'])
                self.assertNotIn(self.raw['isabelle_theory_template'], preview['user_prompt'])
                self.assertIn('direct', preview.get('outputs',{}).get('output', 'direct'))

    def test_export_and_prove_commands_default_to_direct(self):
        exported = self.path/'inputs.jsonl'
        self.call(export_dsp.main, '--records', self.source, '--output', exported)
        self.assertEqual(MODE, read_jsonl(exported)[0]['sketch_source'])
        with patch(ENGINE+'prove.DspConfig.load', return_value=object()), patch(
                ENGINE+'prove.prove_sketches', return_value=[]) as execute:
            self.call(prove.main, '--config', 'unused.local.json', '--input', exported)
        self.assertEqual(MODE, execute.call_args.kwargs['sketch_source'])

    def test_explicit_draft_inputs_keep_the_previous_mode(self):
        source = self.path/'drafts.jsonl'
        write_jsonl(source, [{**self.raw, 'draft':'Induct on the finite set and extend its finite witness.'}])
        for entry, args in ((run.main, ['--config','unused.local.json']), (generate_sketch.main, [])):
            preview = json.loads(self.call(entry, '--drafts', source, '--dry-run', *args))
            self.assertEqual('draft', preview['sketch_source'])
            self.assertTrue(preview['draft_used'])
        exported = self.path/'draft-inputs.jsonl'
        self.call(export_dsp.main, '--sketch-source','draft','--input',source,'--output',exported)
        self.assertEqual('draft', read_jsonl(exported)[0]['sketch_source'])

    def test_conflicting_mode_and_missing_direct_input_fail_before_inference(self):
        for entry, args in ((run.main, ['--config','unused','--records',self.source,'--sketch-source','draft']),
                            (generate_sketch.main, ['--dry-run']), (export_dsp.main, []),
                            (prove.main, ['--config','unused'])):
            with self.subTest(entry=entry.__module__), redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as exc:
                    self.call(entry, *args)
                self.assertEqual(2, exc.exception.code)

    def test_prompt_addresses_case_state_without_changing_draft_prompt(self):
        direct = build_direct_sketch_prompt(export_dsp.export_record(self.raw, sketch_source=MODE))
        draft = build_sketch_prompt(export_dsp.export_record({**self.raw, 'draft':'Induct on the finite set.'}))
        for phrase in ('meta-implication', 'case_name.prems', 'case_name.IH',
                       'existential needs a witness', 'A bare proof applies',
                       'standalone sledgehammer gap'):
            self.assertIn(phrase, direct.user_prompt)
        self.assertNotIn('TARGET PROOF STATE AND INDUCTION', draft.user_prompt)
        self.assertEqual('most_match_sketch_v3', draft.version)
        self.assertNotIn('draft', direct.system_prompt.lower().replace('informal draft', ''))

    def test_repair_diagnostics_retain_inner_failure_and_report_success_separately(self):
        original = dict(mode='search', success=False, source_state='4', line='12',
                        command='by (intro impI)', error='Failed to apply initial proof method')
        hammer = dict(mode='hammer', success=False, source_state='4', error='timed out')
        repair = dict(mode='terminal_repair', success=False, source_state='4', line='12',
                      command=original['command'], error='native Sledgehammer timed out')
        detail = failure_obligation([original, hammer, repair])
        self.assertEqual('hammer', detail['mode'])
        self.assertTrue(detail['hammer_attempted'])
        self.assertEqual(original['command'], detail['repair_of_command'])
        self.assertEqual('12', detail['repair_of_line'])
        success = {**repair, 'success':True, 'error':''}
        stats = search_summary([original, {**hammer, 'success':True}, success])
        self.assertEqual((1,1), (stats['terminal_repair_attempts'],stats['terminal_repair_successes']))
        row = {**export_dsp.export_record(self.raw, sketch_source=MODE), 'sample_idx':0,
               'verified':True, 'step_results':[original, success]}
        summary = summarize_results([row], mode=MODE)['search_activity']
        self.assertEqual(1, summary['terminal_repair_successes'])
        self.assertEqual(1, summary['samples_with_gap_filling'])
        self.assertEqual(0, summary['sledgehammer_calls'])
