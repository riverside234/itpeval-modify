"""Resume preserves input/backend identity, failure accounting and compact evidence."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import repo_path, key
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import lab_preflight as lab
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import preflight_resume as resume
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.parallel import ParallelPlan
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig


class ResumeTests(unittest.TestCase):
    def setUp(self):
        root = repo_path('eval/results/hol_light_to_isabelle_v2')
        root.mkdir(parents=True, exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix='resume-test-', dir=root)
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.old = self.root / 'old'
        self.old.mkdir()
        self.work = self.root / 'old-work'
        self.work.mkdir()
        self.records = [{**control_record('by simp'), 'topic': 't'+str(i)} for i in range(3)]
        self.backend = {'backend_fingerprint': 'old-hash', 'itpeval_commit': 'old-commit',
                        'native_adapter_sha256': {'checker.py': 'same'}, 'config': {'threads': 1}}
        self.rows = [{'name': 'context_'+str(i), 'domain': 'context', 'status': 'pass',
                      'target': list(key(row)), 'details_line': i+1, 'duration_seconds': 100+i,
                      'context_fingerprint': resume.context_identity(row)} for i, row in enumerate(self.records)]
        self.report = {'checker_version': lab.CHECKER_VERSION, 'status': 'running',
                       'local_artifacts': str(self.work), 'checks': self.rows,
                       'resume_backend_fingerprint': resume.backend_identity(self.backend)}

    def save(self):
        (self.old / 'report.json').write_text(json.dumps(self.report), encoding='utf-8')

    def test_reuse_successes_only_and_rerun_changed_inputs(self):
        self.rows[1]['status'] = 'fail'
        self.rows[2]['status'] = 'blocked'
        self.save()
        reused, info = resume.load_reusable(self.old, self.records, self.backend)
        self.assertEqual({key(self.records[0])}, set(reused))
        self.assertEqual(2, info['rerun_contexts'])
        changed = [{**self.records[0], 'isabelle_proof_prefix': 'using changed'}]
        self.assertFalse(resume.load_reusable(self.old, changed, self.backend)[0])

    def test_changed_config_or_checker_cannot_resume_but_report_only_commit_can(self):
        self.save()
        backend = {**self.backend, 'itpeval_commit': 'new', 'backend_fingerprint': 'new-hash'}
        self.assertEqual(3, len(resume.load_reusable(self.old, self.records, backend)[0]))
        backend['config'] = {'threads': 2}
        self.assertFalse(resume.load_reusable(self.old, self.records, backend)[0])
        backend = {**self.backend, 'native_adapter_sha256': {'checker.py': 'changed'}}
        self.assertFalse(resume.load_reusable(self.old, self.records, backend)[0])
        self.report['checker_version'] = 'another-version'
        self.save()
        with self.assertRaisesRegex(ValueError, 'different checker'):
            resume.load_reusable(self.old, self.records, self.backend)

    def legacy(self):
        self.report.pop('resume_backend_fingerprint')
        for row in self.rows:
            row.pop('context_fingerprint')
        (self.work / 'backend.json').write_text(json.dumps(self.backend), encoding='utf-8')
        full = []
        for row, record in zip(self.rows, self.records):
            full.append({**row, 'payload': {'ok': True, 'result': {
                **validate_context(record).metadata, 'baseline_ok': True,
                'native_result': {'success': True}}}})
        (self.work / 'checks.full.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in full) + '{partial', encoding='utf-8')
        self.save()

    def test_legacy_truncated_report_uses_full_local_hashes_and_ignores_partial_tail(self):
        self.legacy()
        reused, info = resume.load_reusable(self.old / 'report.json', self.records, self.backend)
        self.assertEqual(3, info['reused_contexts'])
        self.assertTrue(all(r['method'] == 'legacy_full_payload' for r in reused.values()))
        changed = [{**self.records[0], 'isabelle_theory_template': self.records[0]['isabelle_theory_template']+'\n'}]
        self.assertFalse(resume.load_reusable(self.old, changed, self.backend)[0])

    def test_missing_legacy_evidence_fails_instead_of_trusting_names(self):
        self.legacy()
        (self.work / 'checks.full.jsonl').unlink()
        with self.assertRaisesRegex(ValueError, 'original lab-local'):
            resume.load_reusable(self.old, self.records, self.backend)

    def test_new_report_does_not_require_original_runtime_files(self):
        self.report['local_artifacts'] = str(self.root / 'does-not-exist')
        self.save()
        self.assertEqual(3, len(resume.load_reusable(self.old, self.records, self.backend)[0]))

    def test_coordinator_reuses_two_passes_and_reruns_failure_in_new_report(self):
        self.rows[1]['status'] = 'fail'
        self.save()
        old_text = (self.old / 'report.json').read_bytes()
        parent = self.root / 'parent'
        parent.mkdir()
        with contextlib.ExitStack() as stack:
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            stack.enter_context(patch.object(lab.DspConfig, 'load', return_value=DspConfig(threads=1)))
            stack.enter_context(patch.object(lab.DspConfig, 'metadata', return_value=self.backend))
            stack.enter_context(patch.object(lab.NativeSearch, 'infrastructure', return_value=(parent, 'Parent')))
            stack.enter_context(patch.object(lab, 'prepare_dependencies', return_value={'ok': True}))
            stack.enter_context(patch.object(lab, 'run_fixture', return_value={'ok': True}))
            stack.enter_context(patch.object(lab, 'plan_parallel', return_value=ParallelPlan(2,2,1,8,4,64)))
            checker = stack.enter_context(patch.object(lab.Checker, 'check_context', return_value={'baseline_ok': True}))
            report = lab.run_lab_preflight(config_path='unused', records=self.records,
                scope={'selection': 'test', 'selected_contexts': 3}, output_root=str(self.root / 'reports'),
                controls_override=[], workers=2, resume_from=str(self.old))
        self.assertTrue(report['ok'])
        self.assertEqual(3, report['context_counts']['passed'])
        self.assertEqual(2, sum(bool(r.get('resumed_from')) for r in report['checks']))
        self.assertEqual(self.records[1], checker.call_args.args[0])
        checker.assert_called_once()
        self.assertEqual(old_text, (self.old / 'report.json').read_bytes())
        self.assertEqual(1, report['context_execution']['completed_this_run'])
        # A subsequent resume uses the consolidated report and does not need the old one.
        self.assertEqual(3, len(resume.load_reusable(report['report_directory'], self.records, self.backend)[0]))

    def test_backend_metadata_is_saved_by_reference_without_hiding_context_evidence(self):
        path = self.root / 'reports'
        backend = {**self.backend, 'session_sources_sha256': {str(i): 'x'*64 for i in range(30000)}}
        with contextlib.redirect_stdout(io.StringIO()):
            report = lab.Report(path, {'selection': 'test', 'selected_contexts': 1})
            report.record('context', 'context', {'ok': True, 'target': key(self.records[0]),
                'context_fingerprint': resume.context_identity(self.records[0]),
                'result': {'baseline_ok': True, 'backend_metadata': backend}})
        detail = json.loads((report.path / 'checks.jsonl').read_text(encoding='utf-8'))
        self.assertNotIn('_truncated', detail['payload'])
        self.assertTrue(detail['payload']['result']['baseline_ok'])
        self.assertLess((report.work_path / 'checks.full.jsonl').stat().st_size, 4096)
        self.assertEqual(30000, len(backend['session_sources_sha256']))
