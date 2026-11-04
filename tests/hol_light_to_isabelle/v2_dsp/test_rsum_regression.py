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
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import (
    case_problems, timeout_hammer_case, run_proof_case, PreparedNative)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context
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
        self.assertEqual(3, len(self.cases))
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

    def test_latest_failures_are_candidate_timeouts_at_the_next_gap(self):
        report = json.loads((repo_path(retry.FAILED_RUN)/'report.json').read_text(encoding='utf-8'))
        failed = [c for c in report['checks'] if c['status']=='fail']
        self.assertEqual([name for name, _ in retry.LOGS], [c['name'] for c in failed])
        for row in failed:
            detail = row['failed_obligation']
            self.assertEqual('heuristic', detail['mode'])
            self.assertIn('metis', detail['command'])
            self.assertEqual('using fin', detail['preceding_command'])
            self.assertIn('norm (', detail['goal_diagnostic'])
            self.assertIn('Timeout after', detail['error'])

    def test_forced_hammer_probe_uses_the_same_prefix_and_cannot_pass_on_heuristics(self):
        probe = self.cases[-1]
        self.assertEqual(retry.TRIANGLE_PROBE, probe.name)
        self.assertTrue(probe.force_hammer)
        self.assertEqual('any', probe.hammer_kind)
        context = validate_context(probe.record)
        self.assertEqual(validate_context(self.records[0]).prefix.rstrip(), context.prefix.rstrip())
        self.assertNotIn('lemma rsum_bound:', context.prefix)
        self.assertNotEqual(self.records[0]['isabelle_statement'], context.statement)
        for exercised in (False, True):
            steps = ([{'mode':'hammer','success':True}, {'mode':'reconstruction','success':True}]
                     if exercised else [{'mode':'heuristic','success':True}])
            native = {'success':True,'target_closed':True,'isabelle_proof':'by simp',
                      'step_results':steps,'prover_settings':{}}
            with patch.object(PreparedNative, 'request', return_value=native) as request:
                result = run_proof_case(probe, config=self.config, backend={}, parent=(self.path,'test'),
                                        directory=self.path/str(exercised))
            self.assertEqual((), request.call_args.kwargs['heuristics'])
            self.assertEqual(exercised, result['ok'])
            self.assertEqual(int(exercised), result['result']['search_summary']['hammer_attempts'])

    def test_general_timeout_probe_requires_hammer_from_the_original_state(self):
        case = timeout_hammer_case(self.config)
        self.assertNotIn('content', case.record['formal_statement'])
        self.assertNotIn('norm', case.record['formal_statement'])
        self.assertTrue(case.require_candidate_timeout)
        self.assertFalse(case.force_hammer)
        steps = [dict(mode='heuristic', success=False, command=case.candidate,
                      source_state='5', timeout_scope='candidate'),
                 dict(mode='hammer', success=True, source_state='5'),
                 dict(mode='reconstruction', success=True, source_state='5')]
        result = dict(verified=True, prove_success=True, native_search={'target_closed':True},
                      step_results=steps, prover_settings={'reconstruction_source':'native_tactic'})
        self.assertEqual([], case_problems(case, result))
        for broken in ({**steps[0], 'timeout_scope':''}, {**steps[0], 'success':True}):
            self.assertTrue(case_problems(case, {**result, 'step_results':[broken]+steps[1:]}))
        self.assertTrue(case_problems(case, {**result, 'step_results':[
            steps[0], {**steps[1], 'source_state':'6'}, steps[2]]}))

    def test_search_summary_preserves_hammer_coverage_and_candidate_timeouts(self):
        steps = [dict(mode='heuristic', success=False, source_state='1', timeout_scope='candidate'),
                 dict(mode='hammer', success=True, source_state='1'),
                 dict(mode='reconstruction', success=True, source_state='1'),
                 dict(mode='heuristic', success=False, source_state='2', timeout_scope='candidate'),
                 dict(mode='hammer', success=False, source_state='2')]
        summary = checker.search_summary(steps)
        self.assertEqual(2, summary['candidate_timeouts'])
        self.assertEqual(2, summary['hammer_attempts'])
        self.assertEqual(1, summary['hammer_successes'])
        detail = checker.failure_obligation(steps)
        self.assertTrue(detail['hammer_attempted'])
        self.assertEqual(1, detail['candidate_timeout_count'])
        self.assertNotIn('search_summary', checker.verification_input(
            {**self.cases[0].record, 'search_summary':summary}, 'hol-light-proof'))

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
        self.assertEqual(['candidate_timeout_then_hammer'], [c.name for c in options['controls_override']])
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
                    'failed_obligation':{'goal_diagnostic':'norm (f x) <= e'} if failed else {},
                    'search_summary':{'hammer_attempts':1, 'hammer_successes':int(not failed)}}}) as prove, contextlib.redirect_stdout(io.StringIO()):
                result = lab.run_lab_preflight(config_path='unused', records=self.records, scope=self.scope,
                    output_root=self.path/str(failed), controls_override=[timeout_hammer_case(self.config)], extra_proof_cases=self.cases,
                    include_contexts=False, include_fixture=False, include_dataset_cases=False, warm_dependencies=True)
            self.assertEqual(not failed, result['ok'])
            self.assertEqual(not failed, result['dataset_checks_ok'])
            self.assertFalse(result['contexts_ok'])
            self.assertFalse(result['full_context_coverage'])
            self.assertEqual(0, result['context_counts']['reported'])
            self.assertEqual(1, result['backend_controls_executed'])
            self.assertEqual(4, prove.call_count)
            fixture.assert_not_called()
            context.assert_not_called()
            proofs = [c for c in result['checks'] if c['domain']=='dataset_proof']
            self.assertEqual(3, len(proofs))
            self.assertTrue(all(c['search_summary']['hammer_attempts']==1 for c in proofs))
            if failed:
                self.assertTrue(all('failed_obligation' in c for c in proofs))
            self.assertLessEqual(len(list(Path(result['report_directory']).iterdir())), 6)


if __name__ == '__main__':
    unittest.main()
