"""Limits, job isolation, cancellation, resume and failure accounting."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import threading
import time
import unittest
from unittest.mock import patch, Mock
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp import parallel, prove, lab_preflight as lab
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import CANCEL_EVENT, DspConfig
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import repo_path, write_jsonl, read_jsonl


class ParallelTests(unittest.TestCase):
    def test_limits_and_single_thread_per_parallel_worker(self):
        with patch.object(parallel, 'available_cpus', return_value=64), patch.object(parallel, 'available_memory_bytes', return_value=512*1024**3):
            plan = parallel.plan_parallel(DspConfig(threads=4), workers=60)
            self.assertEqual((60, 1), (plan.workers, plan.threads_per_worker))
            with patch.object(parallel, 'available_memory_bytes', return_value=16*1024**3):
                self.assertEqual(4, parallel.plan_parallel(DspConfig(), workers=60).workers)
            self.assertEqual(4, parallel.plan_parallel(DspConfig(), workers=1).threads_per_worker)
            for workers in (0, -1, 61, True, 2.5):
                with self.assertRaises(ValueError):
                    parallel.plan_parallel(DspConfig(), workers=workers)
            for reserve in (0, float('nan'), float('inf'), True):
                with self.assertRaises(ValueError):
                    parallel.plan_parallel(DspConfig(), workers=2, memory_per_worker_gb=reserve)

    def test_jobs_overlap_but_never_exceed_bound(self):
        lock, barrier = threading.Lock(), threading.Barrier(3)
        active = maximum = 0
        def work(index):
            nonlocal active, maximum
            with lock:
                active += 1
                maximum = max(maximum, active)
            if index < 3:
                barrier.wait(timeout=3)
            time.sleep(0.005 * (index % 3))
            with lock:
                active -= 1
            return index*2
        results = dict(parallel.completed_jobs(work, range(12), workers=3))
        self.assertEqual(3, maximum)
        self.assertEqual({i: i*2 for i in range(12)}, results)

    def test_closing_iterator_cancels_only_its_workers(self):
        started, stopped = threading.Event(), threading.Event()
        def work(index):
            if index == 0:
                self.assertTrue(started.wait(3))
                return 'complete'
            started.set()
            cancellation = CANCEL_EVENT.get()
            self.assertIsNotNone(cancellation)
            cancellation.wait(3)
            if cancellation.is_set():
                stopped.set()
            return 'cancelled'
        iterator = parallel.completed_jobs(work, [0, 1], workers=2)
        self.assertEqual((0, 'complete'), next(iterator))
        iterator.close()
        self.assertTrue(stopped.is_set())
        self.assertIsNone(CANCEL_EVENT.get())

    def test_dependency_build_occurs_once_with_bounded_jobs(self):
        base = repo_path('eval/results/hol_light_to_isabelle_v2')
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as temp:
            config = DspConfig(session_dependencies=('HOL-Library',), threads=1)
            plan = parallel.ParallelPlan(60, 4, 1, 4, 4, 16)
            process = Mock()
            process.run.return_value = 0
            with patch.object(parallel, 'OwnedProcess', return_value=process) as factory, patch.object(DspConfig, 'environment', return_value={}):
                result = parallel.prepare_dependencies(config, [control_record('by simp')], plan, directory=Path(temp))
            command = factory.call_args.args[0]
            self.assertEqual('4', command[command.index('-j')+1])
            self.assertEqual(1, command.count('HOL-Library'))
            self.assertTrue(result['ok'])
            process.run.assert_called_once()

    def test_parallel_prove_writes_every_sample_and_resumes_successes(self):
        base = repo_path('eval/results/hol_light_to_isabelle_v2')
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as temp, contextlib.redirect_stdout(io.StringIO()):
            root = Path(temp)
            rows = [{**control_record('by simp'), 'sample_idx': i} for i in range(5)]
            write_jsonl(root/'sketches.jsonl', rows)
            config = DspConfig(threads=1)
            backend = {'backend': 'isabelle-native', 'isabelle_version': 'Isabelle2026'}
            plan = parallel.ParallelPlan(3, 3, 1, 8, 4, 64)
            def check(row, **_):
                time.sleep(0.002*(4-row['sample_idx']))
                return {**row, 'verified': True, 'prove_success': True,
                        'checker_version': prove.CHECKER_VERSION, 'step_results': []}
            with patch.object(prove, 'plan_parallel', return_value=plan), patch.object(prove, 'prepare_batch', return_value=(config, backend, None)), patch.object(prove.Checker, 'check', side_effect=check) as checker:
                options = dict(config=config, input_path=str(root/'sketches.jsonl'),
                    output_path=str(root/'verified.jsonl'), prove_output=str(root/'prove.jsonl'), workers=3)
                first = prove.prove_sketches(**options)
                again = prove.prove_sketches(**options)
                self.assertEqual(5, checker.call_count)
            self.assertEqual(list(range(5)), [row['sample_idx'] for row in first])
            self.assertEqual(first, again)
            self.assertEqual(5, len(read_jsonl(root/'verified.jsonl')))
            self.assertEqual(5, len(read_jsonl(root/'prove.jsonl')))

    def test_parallel_preflight_records_all_failures_in_compact_files(self):
        base = repo_path('eval/results/hol_light_to_isabelle_v2')
        base.mkdir(parents=True, exist_ok=True)
        rows = [{**control_record('by simp'), 'topic': 'topic'+str(i)} for i in range(5)]
        def check(row, **_):
            time.sleep(0.003)
            if row['topic'] == 'topic2':
                raise ValueError('deliberate failure')
            return {'baseline_ok': True}
        with tempfile.TemporaryDirectory(dir=base) as temp, contextlib.redirect_stdout(io.StringIO()):
            root = Path(temp)
            parent = root/'parent'
            parent.mkdir()
            with patch.object(lab.DspConfig, 'load', return_value=DspConfig()), patch.object(lab.DspConfig, 'metadata', return_value={'backend_fingerprint':'test'}), patch.object(lab.NativeSearch, 'infrastructure', return_value=(parent,'Parent')), patch.object(lab,'prepare_dependencies',return_value={'ok':True}), patch.object(lab,'run_fixture',return_value={'ok':True}), patch.object(lab.Checker,'check_context',side_effect=check), patch.object(lab, 'plan_parallel', return_value=parallel.ParallelPlan(3,3,1,8,4,64)):
                report = lab.run_lab_preflight(config_path='unused', records=rows,
                    scope={'selection':'test','selected_contexts':5}, output_root=str(root/'reports'),
                    controls_override=[], workers=3)
            self.assertFalse(report['ok'])
            self.assertEqual({'selected':5,'reported':5,'unavailable':0,'passed':4,'failed':1,'blocked':0}, report['context_counts'])
            files = list(Path(report['report_directory']).iterdir())
            self.assertLessEqual(len(files), 6)
            self.assertFalse(any(p.suffix == '.zip' for p in files))
            details = [json.loads(line) for line in (Path(report['report_directory'])/'checks.jsonl').read_text(encoding='utf-8').splitlines()]
            self.assertEqual(len(report['checks']), len(details))


class DatasetTagTests(unittest.TestCase):
    def test_most_match_tag_routes_to_isolated_preflight(self):
        import sys
        from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp import lab_preflight as most
        for tag in (("--dataset", "most-match"), ("--dataset=most-match",)):
            with patch.object(sys, "argv", ["preflight", *tag, "--all-targets", "--workers", "60", "--plan-only"]), patch.object(most, "main") as dispatch, patch.object(lab, "discover_records") as legacy:
                lab.main()
                dispatch.assert_called_once_with(argv=["--all-targets", "--workers", "60", "--plan-only"])
                legacy.assert_not_called()
