"""Regression checks for the two real rsum_bound timeouts in commit 6300569."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import repo_path, fingerprint
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import checker, lab_preflight as lab, parallel
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import import_cache
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import read_result
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp import retry_rsum_bound as retry
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.direct_sketch_prompt import build_direct_sketch_prompt
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.sketch_prompt import build_sketch_prompt


class RsumRegressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = DspConfig()
        cls.records, cls.cases, cls.scope = retry.select_cases(cls.config)

    def setUp(self):
        base = repo_path('eval/results/hol_light_to_isabelle_v2')
        base.mkdir(parents=True, exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix='rsum-regression-', dir=base)
        self.addCleanup(temp.cleanup)
        self.path = Path(temp.name)

    def test_both_recorded_failures_keep_the_original_sketch_and_oracle(self):
        self.assertEqual(2, len(self.cases))
        for case, (_, source) in zip(self.cases, retry.LOGS):
            path = repo_path(source)
            request = json.loads((path/'input.json').read_text(encoding='utf-8'))
            old = read_result(path/'result.xml', request, returncode=0)
            self.assertFalse(old['success'])
            self.assertEqual('timeout', old['failure_category'])
            self.assertEqual(request['sketch'], case.record['isabelle_sketch'])
            self.assertEqual(request['statement'], case.record['isabelle_statement'])
            self.assertNotIn('draft', case.record)
            diagnostic = checker.failure_obligation(old['step_results'])
            self.assertIn('content', diagnostic['goal_diagnostic'])
            self.assertIn('content_pos_le', diagnostic['preceding_command'])
            self.assertEqual('hammer', diagnostic['mode'])
            self.assertTrue(all(s['success'] for s in old['step_results'] if s['mode']=='context'))

    def test_recorded_request_rejects_tampering_or_different_current_context(self):
        source = repo_path(retry.LOGS[0][1])
        request = json.loads((source/'input.json').read_text(encoding='utf-8'))
        bad = {**request, 'sketch':'by simp'}
        (self.path/'input.json').write_text(json.dumps(bad), encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            retry.recorded_case(self.records[0], self.config, 'test', str(self.path))
        bad['input_sha256'] = fingerprint({k:v for k,v in bad.items() if k!='input_sha256'})
        bad['statement'] += '\ninvalid target change'
        bad['input_sha256'] = fingerprint({k:v for k,v in bad.items() if k!='input_sha256'})
        (self.path/'input.json').write_text(json.dumps(bad), encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'current target context: statement'):
            retry.recorded_case(self.records[0], self.config, 'test', str(self.path))

    def test_successful_recordings_are_not_selected(self):
        with patch.object(retry, 'read_result', return_value={'success':True,'target_closed':True}):
            with self.assertRaisesRegex(ValueError, 'successful'):
                retry.recorded_case(self.records[0], self.config, *retry.LOGS[0])

    def test_failure_diagnostics_do_not_take_goals_from_an_earlier_state(self):
        steps = [{'mode':'heuristic','source_state':'1','success':False,'error':'goal (1 subgoal): old'},
                 {'mode':'search','source_state':'2','success':True,'line':'9','command':'have later: True'},
                 {'mode':'hammer','source_state':'3','success':False,'error':'timeout','line':'0'}]
        detail = checker.failure_obligation(steps)
        self.assertNotIn('goal_diagnostic', detail)
        self.assertEqual('9', detail['preceding_line'])
        steps.append({'mode':'search','success':True})
        self.assertEqual({}, checker.failure_obligation(steps))
        row = checker.verification_input({**self.cases[0].record,'failed_obligation':{'error':'old'}}, 'hol-light-proof')
        self.assertNotIn('failed_obligation', row)

    def test_both_prompt_modes_require_explicit_nonlinear_and_sum_reasoning(self):
        direct = build_direct_sketch_prompt(self.cases[0].record)
        draft_row = {**self.records[0], 'formal_statement':self.records[0]['isabelle_statement'],
                     'draft':'Apply the triangle inequality and bound each scaled summand.',
                     'informal_proof':'Apply the triangle inequality and bound each scaled summand.'}
        draft = build_sketch_prompt(draft_row)
        for prompt in (direct, draft):
            self.assertIn('product of two variable quantities is nonlinear', prompt.user_prompt)
            self.assertIn('sum monotonicity', prompt.user_prompt)
            self.assertIn("scalar's sign", prompt.user_prompt)

    def test_hundred_single_worker_batch_prepares_exact_import_heaps(self):
        plan = parallel.ParallelPlan(1,1,1,8,12,64,1,8)
        parent = self.path/'parent', 'DSP_Native_test'
        with patch.object(DspConfig,'metadata',return_value={'backend_fingerprint':'test'}), patch.object(
            parallel,'prepare_dependencies'), patch.object(parallel.NativeSearch,'infrastructure',return_value=parent), patch.object(
            import_cache,'prepare_import_parents',return_value=({'fixture':'parent'},{'ok':True})) as heaps:
            config, backend, factory = parallel.prepare_batch(self.config, self.records, plan)
        self.assertEqual(self.records, heaps.call_args.args[1])
        self.assertEqual({'fixture':'parent'}, factory(config).import_parents)

    def test_retry_cli_runs_only_failed_proof_searches(self):
        with patch.object(retry.DspConfig,'load',return_value=self.config), patch.object(
            retry,'select_cases',return_value=(self.records,self.cases,self.scope)), patch.object(
            retry,'run_lab_preflight',return_value={'ok':True,'counts':{'pass':7},'report_directory':'fixture'}) as run, contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit) as exited:
                retry.main([])
        self.assertEqual(0, exited.exception.code)
        options = run.call_args.kwargs
        self.assertEqual(self.cases, options['extra_proof_cases'])
        self.assertEqual([], options['controls_override'])
        self.assertFalse(options['include_contexts'])
        self.assertFalse(options['include_fixture'])
        self.assertFalse(options['include_dataset_cases'])

    def test_proof_only_preflight_success_and_failure_accounting_and_compact_logs(self):
        for failed in (False, True):
            with self.subTest(failed=failed), patch.object(lab.DspConfig,'load',return_value=self.config), patch.object(
                lab.DspConfig,'metadata',return_value={'backend_fingerprint':'test'}), patch.object(
                lab,'plan_parallel',return_value=parallel.ParallelPlan(1,1,1,8,12,64,1,8)), patch.object(
                lab,'snapshot_infrastructure'), patch.object(lab.NativeSearch,'infrastructure',return_value=(self.path,'test')), patch.object(
                lab,'prepare_dependencies',return_value={'ok':True}), patch.object(
                lab,'prepare_import_parents',return_value=({}, {'ok':True,'import_sets':1})), patch.object(
                lab,'run_fixture') as fixture, patch.object(lab.Checker,'check_context') as context, patch.object(
                lab,'run_proof_case',return_value={'ok':not failed,'result':{'verified':not failed,
                    'verify_error':'failed product bound' if failed else '',
                    'failed_obligation':{'goal_diagnostic':'norm (f x) <= e'} if failed else {}}}) as prove, contextlib.redirect_stdout(io.StringIO()):
                result = lab.run_lab_preflight(config_path='unused', records=self.records, scope=self.scope,
                    output_root=self.path/str(failed), controls_override=[], extra_proof_cases=self.cases,
                    include_contexts=False, include_fixture=False, include_dataset_cases=False, warm_dependencies=True)
            self.assertEqual(not failed, result['ok'])
            self.assertEqual(not failed, result['dataset_checks_ok'])
            self.assertFalse(result['contexts_ok'])
            self.assertFalse(result['full_context_coverage'])
            self.assertEqual(0, result['context_counts']['reported'])
            self.assertEqual(0, result['backend_controls_executed'])
            self.assertEqual(2, prove.call_count)
            fixture.assert_not_called()
            context.assert_not_called()
            proofs = [c for c in result['checks'] if c['domain']=='dataset_proof']
            self.assertEqual(2, len(proofs))
            if failed:
                self.assertTrue(all('failed_obligation' in c for c in proofs))
            self.assertLessEqual(len(list(Path(result['report_directory']).iterdir())), 6)


if __name__ == '__main__':
    unittest.main()
