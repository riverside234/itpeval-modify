"""Regressions for the 52fa4ea rsum_bound import/preflight failure."""
import copy
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import RESULTS_DIR, repo_path
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import (
    NativeFailure, NativeSearch, imports_of, read_result, resolve_imports,
)
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import preflight, control_record
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig

BASE = "eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp."
ALIASES = {"Lebesgue_Measure": "HOL-Analysis.Lebesgue_Measure",
           "Tagged_Division": "HOL-Analysis.Tagged_Division"}
SOURCE = 'theory Sample imports Lebesgue_Measure Tagged_Division "HOL-Real_Asymp.Real_Asymp" begin\n'
BACKEND = {"backend": "isabelle-native", "isabelle_version": "Isabelle2026"}


class ImportResolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records
        cls.record = extract_records(topic="015_the_fundamental_theorem_of_integral_calculus",
                                     target_key="rsum_bound")[0]

    def setUp(self):
        base = repo_path(RESULTS_DIR)
        base.mkdir(parents=True, exist_ok=True)
        self.folder = tempfile.TemporaryDirectory(prefix="rsum-imports-", dir=base)
        self.addCleanup(self.folder.cleanup)
        self.path = Path(self.folder.name)
        self.config = DspConfig(theory_imports=ALIASES)

    def test_import_mapping_and_qualified_names_add_deduplicated_session_dependencies(self):
        original = SOURCE + 'text \\<open>Lebesgue_Measure is not an import here\\<close>\n'
        source, resolution = resolve_imports(original, self.config, theory_name="Sample")
        self.assertEqual(list(ALIASES.values()) + ["HOL-Real_Asymp.Real_Asymp"], imports_of(source))
        self.assertEqual(["HOL-Analysis", "HOL-Real_Asymp"], resolution["session_dependencies"])
        self.assertEqual(original.split('begin', 1)[1], source.split('begin', 1)[1])
        self.assertEqual(original.count('\n'), source.count('\n'))
        config = DspConfig(session_dependencies=("HOL-Library", "HOL-Analysis"))
        _, already_qualified = resolve_imports(source, config, theory_name="Sample")
        self.assertEqual(["HOL-Library", "HOL-Analysis", "HOL-Real_Asymp"], already_qualified["session_dependencies"])

    def test_main_and_unmapped_imports_are_not_guessed(self):
        source = 'theory Sample imports Main Complex_Main Unknown_Helper begin\n'
        resolved, plan = resolve_imports(source, self.config, theory_name="Sample")
        self.assertEqual(source, resolved)
        self.assertEqual([], plan["session_dependencies"])

    def test_mapping_cannot_substitute_a_different_theory_or_escape_to_a_path(self):
        invalid = [[], {"Lebesgue_Measure": "HOL-Analysis.Analysis"},
                   {"Lebesgue_Measure": "../Lebesgue_Measure"},
                   {"HOL-Analysis.Lebesgue_Measure": "Other.Lebesgue_Measure"}]
        for aliases in invalid:
            with self.subTest(aliases=aliases), self.assertRaises(ValueError):
                DspConfig(theory_imports=aliases)

    def test_selected_target_theory_cannot_be_imported_under_a_session_alias(self):
        config = DspConfig(theory_imports={"Sample": "HOL-Analysis.Sample"})
        with self.assertRaisesRegex(NativeFailure, "selected target theory"):
            resolve_imports('theory Sample imports Sample begin', config, theory_name="Sample")

    def test_real_rsum_search_and_replay_use_identical_resolved_imports(self):
        original = copy.deepcopy(self.record)
        native = NativeSearch(self.config)
        search, replay = self.path / "search", self.path / "replay"
        fake_result = {"success": True, "target_closed": False, "step_results": []}
        with patch.object(native, "infrastructure", return_value=(self.path / "infra", "DSP_Infrastructure")), patch.object(
                native, "run_build", return_value=0), patch.object(native, "encode_symbols", side_effect=lambda x:x), patch(
                BASE + "native_search.read_result", return_value=fake_result):
            result = native.request(self.record, "", directory=search, action="context", heuristics=(),
                                    deadline=time.monotonic()+30)
            native.replay(self.record, "by simp", directory=replay, deadline=time.monotonic()+30)
        self.assertEqual(original, self.record)
        expected_imports = list(ALIASES.values()) + ["HOL-Real_Asymp.Real_Asymp"]
        request = json.loads((search / 'input.json').read_text(encoding='utf-8'))
        self.assertEqual(expected_imports, imports_of(request['prefix']))
        self.assertEqual(original['isabelle_statement'], request['statement'])
        self.assertEqual(original['isabelle_proof_prefix'], request['proof_prefix'])
        replay_source = (replay / 'Henstock_Kurzweil_Integration.thy').read_text(encoding='utf-8')
        self.assertEqual(expected_imports, imports_of(replay_source))
        self.assertIn(original['isabelle_statement'], replay_source)
        self.assertNotIn('DSP_Native', replay_source)
        self.assertIn('imports DSP_Native "HOL-Analysis.Lebesgue_Measure"',
                      (search / 'DSP_Driver.thy').read_text(encoding='utf-8'))
        for directory in (search, replay):
            root = (directory / 'ROOT').read_text(encoding='utf-8')
            self.assertIn('sessions "HOL-Analysis" "HOL-Real_Asymp"', root)
            self.assertNotIn('= "HOL-Analysis"', root)
            self.assertEqual(result['import_resolution'], json.loads((directory / 'import_resolution.json').read_text()))

    def test_missing_result_preserves_observed_import_error_details(self):
        log = ('*** Cannot load theory file "Lebesgue_Measure.thy"\n'
               '*** Cannot load theory file "Tagged_Division.thy"\n'
               '*** Bad import of theory "HOL-Real_Asymp.Real_Asymp": need to include sessions "HOL-Real_Asymp" in ROOT\n')
        (self.path / 'build.log').write_text(log, encoding='utf-8')
        with self.assertRaises(NativeFailure) as raised:
            read_result(self.path / 'result.xml', {}, returncode=2)
        error = raised.exception
        self.assertEqual('import_error', error.category)
        self.assertIn('Lebesgue_Measure', str(error))
        self.assertIn('HOL-Real_Asymp', str(error))
        self.assertEqual(2, error.details['build_returncode'])
        self.assertEqual(log.splitlines(), error.details['build_log_excerpt'].splitlines())

    def test_preflight_failure_keeps_paths_category_and_saved_report(self):
        failure = NativeFailure('import_error', 'Cannot load theory Lebesgue_Measure',
                                details={'build_log_excerpt': 'missing library', 'build_returncode': 2})
        with patch(BASE + 'checker.NativeSearch.request', side_effect=failure):
            result = preflight(self.record, config=self.config, controls=False,
                               backend_metadata=BACKEND, results_dir=str(self.path))
        self.assertFalse(result['ok'])
        self.assertEqual('import_error', result['failure_category'])
        self.assertTrue(Path(result['workdir']).is_dir())
        self.assertEqual(str(Path(result['workdir'])/'build.log'), result['build_log_path'])
        self.assertEqual(json.loads(json.dumps(result)), json.loads(Path(result['report_path']).read_text(encoding='utf-8')))
        self.assertEqual('missing library', result['build_log_excerpt'])

    def test_batch_runner_keeps_import_failure_without_calling_the_model(self):
        import contextlib, io, sys
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.common import write_jsonl, read_jsonl
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.run_babel import main
        source = self.path / 'records.jsonl'
        output = self.path / 'verified.jsonl'
        write_jsonl(source, [self.record])
        args = ['runner', '--config', 'eval/configs/hol_light_to_isabelle/v2_dsp.example.json',
                '--sketch-source', 'hol-light-proof', '--records', str(source), '--samples', '2',
                '--dsp-output', str(self.path/'inputs.jsonl'), '--sketch-output', str(self.path/'sketches.jsonl'),
                '--prove-output', str(self.path/'prove.jsonl'), '--output', str(output)]
        failure = {'ok': False, 'failure_category': 'import_error', 'error': 'Cannot load theory Missing'}
        with patch.object(sys, 'argv', args), patch.object(DspConfig, 'metadata', return_value=BACKEND), patch(
                BASE+'run_babel.preflight', return_value=failure), patch(
                BASE+'generate_sketch.call_draft_model') as model, contextlib.redirect_stdout(io.StringIO()):
            main(expected_source='hundred-theorems', results_dir=str(self.path))
        model.assert_not_called()
        rows = read_jsonl(output)
        self.assertEqual(2, len(rows))
        self.assertTrue(all(row['failure_category'] == 'import_error' for row in rows))
        self.assertTrue(all(not row['verified'] for row in rows))

    def test_replay_failure_retains_the_actual_build_error(self):
        native = NativeSearch(self.config)
        def build(folder, session, **options):
            (folder / 'build.log').write_text('*** Bad import of theory "missing"', encoding='utf-8')
            return 2
        with patch.object(native, 'encode_symbols', side_effect=lambda x:x), patch.object(native, 'run_build', side_effect=build):
            result = native.replay(control_record('by simp'), 'by simp', directory=self.path/'replay',
                                   deadline=time.monotonic()+30)
        self.assertFalse(result['success'])
        self.assertIn('Bad import of theory', result['error'])
        self.assertEqual(2, result['build_returncode'])


if __name__ == '__main__':
    unittest.main()
