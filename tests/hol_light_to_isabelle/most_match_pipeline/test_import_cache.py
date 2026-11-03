"""Regressions for f56944e: repeated imports, killed workers, failure-only scope."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import repo_path, key
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.sanitize_isabelle import sanitize_target
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import import_cache as cache
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import lab_preflight as lab
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import native_search as native
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import PreparedNative
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.parallel import ParallelPlan
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight_failures import select_failures
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig, OwnedProcess

REPORT = 'eval/preflight_results/isabelle2026-most-match/20261103T030137Z-650c526a'


def record(imports='Main', topic='test'):
    row = control_record('by simp', source='hol-most-match')
    template = row['isabelle_theory_template'].replace('imports Main', 'imports ' + imports)
    target = sanitize_target(template, row['isabelle_target_name'])
    row.update(topic=topic, isabelle_theory_template=template, isabelle_statement=target.statement,
               isabelle_context_before_target=target.context_before_target,
               isabelle_target_proof_span=list(target.proof_span), isabelle_proof_prefix=target.proof_prefix)
    return row


class ImportHeapTests(unittest.TestCase):
    def setUp(self):
        root = repo_path('eval/results/hol_light_to_isabelle_v2')
        root.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='import-cache-test-', dir=root)
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.parent = self.root/'base', 'DSP_Native_test'
        self.parent[0].mkdir()
        self.config = DspConfig(threads=1)
        self.plan = ParallelPlan(8,8,1,128,12,450,dependency_jobs=2,dependency_threads=8)
        self.mock(cache, 'RUNTIME_DIR', str(self.root/'runtime'))
        self.mock(DspConfig, 'environment', return_value={})
        self.process = Mock()
        self.process.run.return_value = 0
        self.factory = self.mock(cache, 'OwnedProcess', return_value=self.process)

    def mock(self, obj, name, *args, **kwargs):
        patcher = patch.object(obj, name, *args, **kwargs)
        result = patcher.start()
        self.addCleanup(patcher.stop)
        return result

    def build(self, rows):
        with contextlib.redirect_stdout(io.StringIO()):
            return cache.prepare_import_parents(self.config, rows, self.plan, self.parent,
                                               directory=self.root/'build')

    def test_heaps_deduplicate_exact_import_sets_without_broadening_context(self):
        rows = [record('"HOL-Analysis.Starlike"', 'a'), record('"HOL-Analysis.Starlike"', 'b'),
                record('"HOL-Library.Finite_Map"', 'c')]
        parents, report = self.build(rows)
        self.assertEqual(2, report['import_sets'])
        self.assertEqual(1, self.factory.call_count)
        command = self.factory.call_args.args[0]
        self.assertEqual('2', command[command.index('-j')+1])
        self.assertIn('-b', command)
        self.assertNotIn('-f', command)
        self.assertNotIn('-S', command)
        self.assertNotIn('-c', command)
        for parent in parents.values():
            source = (parent.directory/'DSP_Imports.thy').read_text()
            self.assertNotIn('lemma', source)
            self.assertNotIn('V2Control', source)
            for name in ('HOL-Analysis.Starlike', 'HOL-Library.Finite_Map'):
                self.assertEqual(name in parent.imports, name in source)
            root = (parent.directory/'ROOT').read_text()
            self.assertIn('threads = 8', root)
            self.assertIn('parallel_proofs = 1', root)
            self.assertIn('= "DSP_Native_test"', root)
        before = {p.session: (p.directory/'ROOT').stat().st_mtime_ns for p in parents.values()}
        again, _ = self.build(rows)
        self.assertEqual(before, {p.session: (p.directory/'ROOT').stat().st_mtime_ns for p in again.values()})
        self.assertEqual(2, self.factory.call_count)  # Recheck heap freshness, never a blind marker.

    def test_cached_job_loads_exact_parent_and_keeps_original_driver_imports(self):
        row = record('"HOL-Analysis.Starlike"')
        parents, _ = self.build([row])
        engine = PreparedNative(self.config, self.parent, import_parents=parents)
        self.mock(engine, 'encode_symbols', side_effect=lambda text:text)
        build = self.mock(engine, 'run_build', return_value=0)
        self.mock(native, 'read_result', return_value={'success':True})
        result = engine.request(row, '', directory=self.root/'job', action='context', heuristics=(),
                                deadline=time.monotonic()+60)
        parent = next(iter(parents.values()))
        self.assertEqual(parent.session, result['parent_session'])
        self.assertEqual((self.parent[0], parent.directory), build.call_args.kwargs['parent_dir'])
        root = (self.root/'job/ROOT').read_text()
        self.assertIn('= '+parent.session, root)
        driver = (self.root/'job/DSP_Driver.thy').read_text()
        self.assertIn('imports DSP_Native "HOL-Analysis.Starlike"', driver)
        self.assertNotIn('imports DSP_Imports', driver)  # Original theory parents are unchanged.
        command = engine.build_command(self.root/'job', 'Job', parent_dir=parent.job_parent()[0])
        self.assertIn(str(self.parent[0]), command)
        self.assertIn(str(parent.directory), command)

    def test_cache_cannot_fall_back_to_an_unprepared_or_unrelated_heap(self):
        engine = PreparedNative(self.config, self.parent, import_parents={})
        resolution = native.resolve_imports('theory X imports Main begin', self.config, theory_name='X')[1]
        with self.assertRaisesRegex(native.NativeFailure, 'exact original import set'):
            engine.job_parent(resolution, deadline=30)
        with self.assertRaisesRegex(native.NativeFailure, 'selected target theory'):
            self.build([record('V2Control')])
        self.factory.assert_not_called()

    def test_shared_import_build_failure_keeps_diagnostics(self):
        self.process.run.return_value = 1
        with self.assertRaises(native.NativeFailure) as raised:
            self.build([record()])
        self.assertEqual('import_build_error', raised.exception.category)
        self.assertEqual(1, raised.exception.details['build_returncode'])

    def test_sigkill_and_library_build_failures_are_distinguished(self):
        job = self.root/'job'
        job.mkdir()
        (job/'build.log').write_text('Killed worker\n')
        (job/'build.metrics.json').write_text(json.dumps({'worker_ready':False,'peak_tree_rss_mb':12000}))
        with self.assertRaises(native.NativeFailure) as killed:
            native.read_result(job/'result.xml', {}, returncode=137)
        self.assertEqual('resource_error', killed.exception.category)
        self.assertIn('not proven', killed.exception.details['termination_hint'])
        self.assertEqual(12000, killed.exception.details['build_metrics']['peak_tree_rss_mb'])
        (job/'build.log').write_text('*** Failed to load theory "HOL-Analysis.X"\n*** Timeout after 37s\n')
        with self.assertRaises(native.NativeFailure) as failed:
            native.read_result(job/'result.xml', {}, returncode=1)
        self.assertEqual('import_build_error', failed.exception.category)

    def test_memory_sample_only_counts_current_owned_process_identities(self):
        process = OwnedProcess([], directory=self.root, env={}, log_path=self.root/'build.log', timeout_s=30, deadline=60)
        process.owned_processes = {1:{'start_ticks':'1','group':1}, 2:{'start_ticks':'2','group':1}}
        fake_proc = self.root/'proc'
        for pid in (1,2):
            (fake_proc/str(pid)).mkdir(parents=True)
            (fake_proc/str(pid)/'status').write_text('VmRSS: 102400 kB\n')
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import runtime
        with patch.object(runtime, 'PROC_ROOT', fake_proc), patch.object(process, 'process_identity',
            side_effect=lambda pid: {'start_ticks':str(pid) if pid==1 else 'reused', 'group':1}):
            self.assertEqual(100.0, process.sampled_tree_rss_mb())

    def test_failed_only_coordinator_skips_passed_controls_and_preserves_metrics(self):
        rows = [record(topic='a'), record(topic='b')]
        self.mock(lab.DspConfig, 'load', return_value=self.config)
        self.mock(lab.DspConfig, 'metadata', return_value={'backend_fingerprint':'test'})
        self.mock(lab, 'plan_parallel', return_value=self.plan)
        self.mock(lab.NativeSearch, 'infrastructure', return_value=self.parent)
        self.mock(lab, 'prepare_dependencies', return_value={'ok':True})
        heaps = self.mock(lab, 'prepare_import_parents', return_value=({}, {'ok':True, 'import_sets':1}))
        fixture = self.mock(lab, 'run_fixture')
        proof = self.mock(lab, 'run_proof_case')
        checker = self.mock(lab.Checker, 'check_context', return_value={'baseline_ok':True,
            'native_result':{'build_metrics':{'startup_seconds':1.2,'peak_tree_rss_mb':1400}}})
        with contextlib.redirect_stdout(io.StringIO()):
            result = lab.run_lab_preflight(config_path='unused', records=rows, workers=8,
                scope={'selection':'failed_only','selected_contexts':2}, output_root=self.root/'reports',
                controls_override=[], include_fixture=False, include_dataset_cases=False)
        self.assertTrue(result['ok'])
        self.assertFalse(result['full_context_coverage'])
        self.assertEqual(0, result['backend_controls_executed'])
        self.assertEqual(2, checker.call_count)
        self.assertEqual(rows, heaps.call_args.args[1])
        fixture.assert_not_called()
        proof.assert_not_called()
        self.assertEqual(2, result['context_execution']['successful_this_run'])
        self.assertTrue(all(r['performance']['startup_seconds']==1.2 for r in result['checks'] if r['domain']=='context'))
        self.assertLessEqual(len(list(Path(result['report_directory']).iterdir())), 6)


class FailureSelectionTests(unittest.TestCase):
    def test_committed_report_selects_112_failures_and_no_previous_passes(self):
        report = json.loads((repo_path(REPORT)/'report.json').read_text(encoding='utf-8'))
        records = [dict(zip(('source','theorem_id','topic','target_key'), c['target']))
                   for c in report['checks'] if c['domain']=='context']
        selected, info = select_failures(REPORT, records)
        expected = {tuple(c['target']) for c in report['checks'] if c['status']=='fail'}
        self.assertEqual(expected, {key(r) for r in selected})
        self.assertEqual(112, len(selected))
        self.assertEqual(8, len({r['topic'] for r in selected}))
        self.assertEqual(258, info['previous_passes_not_revalidated'])
        self.assertEqual(241, info['previous_context_counts']['passed'])
        with self.assertRaisesRegex(ValueError, 'not found'):
            select_failures(REPORT, selected[1:])

    def test_cli_failed_only_passes_no_fixture_or_proof_controls_to_runner(self):
        from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp import lab_preflight as most
        report = json.loads((repo_path(REPORT)/'report.json').read_text(encoding='utf-8'))
        row = record(topic='Polytope')
        records = []
        for c in report['checks']:
            if c['domain']=='context':
                records.append({**row, **dict(zip(('source','theorem_id','topic','target_key'), c['target']))})
        with patch.object(most, 'extract_records', return_value=records), patch.object(most,'validate_context'), patch.object(
            most, 'validate_prompt_context'), patch.object(most,'resolve_imports', return_value=('',{'resolved_imports':['Main'],
                'session_dependencies':[]})), patch.object(most,'run_lab_preflight',return_value={'status':'complete','ok':True}) as run, patch.object(
            most, 'select_contexts',return_value=(records,{})), contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit) as status:
                most.main(['--failed-from',REPORT,'--expected-contexts','112','--workers','8'])
        self.assertEqual(0, status.exception.code)
        self.assertEqual(112, len(run.call_args.kwargs['records']))
        self.assertEqual([], run.call_args.kwargs['controls_override'])
        self.assertEqual([], run.call_args.kwargs['extra_proof_cases'])
        self.assertFalse(run.call_args.kwargs['include_fixture'])
        self.assertFalse(run.call_args.kwargs['include_dataset_cases'])


class ReportReplaceTests(unittest.TestCase):
    def test_transient_windows_lock_retries_without_unlinking_previous_report(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline import preflight_storage as storage
        error = PermissionError("sharing violation")
        error.winerror = 32
        source = Mock()
        source.replace.side_effect = [error, error, None]
        with patch.object(storage.time, "sleep") as sleep:
            storage.replace_file(source, "report.json")
        self.assertEqual(3, source.replace.call_count)
        self.assertEqual(2, sleep.call_count)
        source.unlink.assert_not_called()

    def test_nonwindows_permission_errors_fail_immediately_and_windows_retries_are_bounded(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline import preflight_storage as storage
        for windows, attempts in ((False, 1), (True, 7)):
            error = PermissionError("denied")
            if windows:
                error.winerror = 5
            source = Mock()
            source.replace.side_effect = error
            with patch.object(storage.time, "sleep"), self.assertRaises(PermissionError):
                storage.replace_file(source, "report.json")
            self.assertEqual(attempts, source.replace.call_count)
