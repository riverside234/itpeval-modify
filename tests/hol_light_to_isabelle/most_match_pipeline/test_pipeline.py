"""Extraction, reference budgets and representative coverage."""
import copy
from pathlib import Path
import unittest
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline import context
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.common import DATASET_ROOT, repo_path
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.extract_hol_light import extract_records
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.prompt import build_draft_prompt
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp.export_dsp import export_record
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp.sketch_prompt import build_sketch_prompt
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp.direct_sketch_prompt import build_direct_sketch_prompt
from eval.pipeline.hol_light_to_isabelle.most_match_pipeline.v2_dsp.lab_preflight import select_contexts, CONTROL_NAMES, DEFAULT_CONFIG
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.theory_context import validate_context
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import proof_cases
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import resolve_imports
from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.hol_syntax import tokens, inventory_hol_declarations


class RetrievalTests(unittest.TestCase):
    def test_reference_excludes_tactic_code_and_residual_proofs(self):
        source = ('let HELPER = `!x. x = x`;;\nlet secret = prove (`T`, SECRET_TAC);;\n'
                  'let CUSTOM_TAC = SECRET_TAC;;\nlet op = new_definition `op x = x`;;\n'
                  'let TARGET = `op x = x`;;')
        chunks = context.source_snippets(source)
        self.assertEqual(['HELPER', 'op', 'TARGET'], [c.name for c in chunks])
        text, meta = context.retrieve(chunks, query='HELPER op', budget=400, mandatory=[chunks[-1]])
        self.assertIn('let TARGET', text)
        self.assertNotIn('SECRET_TAC', text)
        self.assertLessEqual(len(text), 400)
        self.assertEqual(len(text), meta['selected_chars'])
        self.assertTrue(text.endswith(';;'))

    def test_whole_snippets_mandatory_overflow_and_validation(self):
        short = context.Snippet('aaa', 'statement', 0, 10, 'let aaa = `T`;;')
        long = context.Snippet('bbb', 'definition', 10, 4000, 'x' * 4000)
        text, _ = context.retrieve([short, long], query='bbb', budget=256, mandatory=[short])
        self.assertNotIn('x' * 20, text)
        with self.assertRaisesRegex(ValueError, 'mandatory'):
            context.retrieve([long], query='bbb', budget=256, mandatory=[long])
        for cap in (0, -1, True, 1.5):
            with self.assertRaises(ValueError):
                context.retrieve([], query='', budget=cap)

    def test_import_retrieval_follows_only_masked_ancestors_and_retains_provenance(self):
        import tempfile
        from unittest.mock import patch
        base = repo_path('eval/results/hol_light_to_isabelle_v2')
        base.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as folder:
            root = Path(folder)
            (root/'Parent.thy').write_text('theory Parent imports Grand Main begin\n'
                'lemma helper: "True" by simp\nlemma \\<open>True\\<close> sorry\ncontext fixes x :: nat begin\n'
                'lemma hidden: "x=x" sorry\nend\nend',encoding='utf-8')
            (root/'Grand.thy').write_text('theory Grand imports Target begin\n'
                'lemma ancestor: "True" sorry\nend',encoding='utf-8')
            (root/'Target.thy').write_text('DO NOT READ TARGET',encoding='utf-8')
            (root/'Sibling.thy').write_text('DO NOT READ SIBLING',encoding='utf-8')
            opened=[]
            original=Path.read_text
            def read(path,*args,**kwargs):
                opened.append(path.name)
                return original(path,*args,**kwargs)
            with patch.object(Path,'read_text',read):
                parts,meta=context.imported_references('section \\<open>Introduction\\<close>\ntheory Target imports Parent Other.Parent begin',root)
            self.assertEqual(['Parent.thy','Grand.thy'],opened)
            self.assertEqual(['helper','ancestor'],[s.name for s in parts])
            self.assertNotIn('by simp',' '.join(s.text for s in parts))
            self.assertTrue(all(s.origin for s in parts))
            self.assertEqual(['Main','Other.Parent'],meta['unresolved_imports'])
            self.assertTrue(all(s['masked_sha256'] for s in meta['sources']))
            # Identical spans in different files must not collide.
            copies=[context.Snippet('helper','lemma',0,20,'lemma helper: True sorry',origin=n)
                    for n in ('A.thy','B.thy')]
            _,metadata=context.retrieve(copies,query='helper',budget=500)
            self.assertEqual(2,len(metadata['selected_snippets']))

    def test_active_scopes_and_annotated_definitions(self):
        prefix = ('theory T imports Main begin\ncontext fixes x :: nat assumes h: "x > 0" begin\n'
                  'definition\\<^marker>\\<open>tag important\\<close> op where "op = x"\n'
                  'lemma old: "True" sorry\n')
        chunks, scopes = context.isabelle_snippets(prefix)
        self.assertEqual(['T', 'fixes'], [s.name for s in scopes])
        self.assertIn('op', [s.name for s in chunks])
        text, _ = context.retrieve(chunks, query='op', budget=1000, mandatory=scopes)
        self.assertIn('assumes h: "x > 0"', text)
        _, closed = context.isabelle_snippets(prefix + '\nend\n')
        self.assertEqual(['T'], [s.name for s in closed])


@unittest.skipUnless(repo_path(DATASET_ROOT).is_dir(), 'most-match dataset not installed')
class DatasetTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.coverage = {}
        cls.records = extract_records(report=cls.coverage)

    def test_all_candidates_and_zero_match_topic_are_accounted_for(self):
        self.assertEqual(353, len(self.records))
        self.assertEqual(16, len(self.coverage['topics']))
        self.assertEqual(['Poly_Roots'], self.coverage['zero_match_topics'])
        self.assertFalse([i for r in self.coverage['topics'] for i in r['issues']])
        self.assertEqual(353, len({(r['topic'], r['target_key']) for r in self.records}))
        self.assertTrue(all(not r['semantic_alignment_verified'] for r in self.records))
        self.assertFalse(any(Path(r['metadata']['hol_light_proof_path']).name.startswith('_') for r in self.records))

    def test_reference_caps_masking_and_exclusion_of_later_facts(self):
        for row in self.records:
            with self.subTest(topic=row['topic'], target=row['target_key']):
                context.validate_prompt_context(row)
                checked = validate_context(row)
                self.assertLessEqual(len(row['hol_light_reference_context']), 16000)
                self.assertLessEqual(len(row['isabelle_prompt_context']), 8000)
                self.assertFalse(any(t.text == 'prove' and t.kind == 'word' for t in tokens(row['hol_light_reference_context'])))
                masked = inventory_hol_declarations(row['hol_light_reference_context'], masked=True)
                self.assertEqual(1, sum(d.name == row['hol_light_target_name'] for d in masked))
                meta = row['metadata']['prompt_context']
                target = next(s for s in meta['hol_light']['selected_snippets'] if s['name'] == row['hol_light_target_name'])
                self.assertTrue(all(s['span'][0] <= target['span'][0] for s in meta['hol_light']['selected_snippets']))
                self.assertTrue(all(s['span'][1] <= len(checked.prefix) for s in meta['isabelle']['selected_snippets'] if not s.get('origin')))
                self.assertNotIn(row['isabelle_target_name'], [s['name'] for s in meta['isabelle']['selected_snippets']
                    if s['kind'] in {'lemma', 'theorem', 'corollary', 'proposition'}])

    def test_prompts_are_bounded_and_checker_keeps_full_context(self):
        row = max(self.records, key=lambda r: len(r['isabelle_context_before_target']))
        original = copy.deepcopy(row)
        draft = build_draft_prompt(row)
        direct = build_direct_sketch_prompt(export_record(row, sketch_source='hol-light-proof'))
        sketch = build_sketch_prompt(export_record({**row, 'draft': 'Use the selected proof strategy.'}))
        self.assertEqual(original, row)
        self.assertGreater(len(row['isabelle_context_before_target']), 8000)
        for prompt in (draft, direct, sketch):
            self.assertIn(row['isabelle_prompt_context'], prompt.user_prompt)
            self.assertNotIn(row['isabelle_context_before_target'], prompt.user_prompt)
            self.assertIn(row['isabelle_statement'], prompt.user_prompt)
        self.assertIn(row['hol_light_proof'], draft.user_prompt)
        self.assertIn(row['hol_light_proof'], direct.user_prompt)
        broken = copy.deepcopy(row)
        broken['isabelle_prompt_context'] += 'stale edit'
        with self.assertRaisesRegex(ValueError, 'stale'):
            build_draft_prompt(broken)

    def test_representatives_cover_every_topic_library_and_longest_proofs(self):
        selected, scope = select_contexts(self.records)
        self.assertEqual(65, len(selected))
        self.assertEqual(15, scope['selected_topics'])
        self.assertEqual({r['metadata']['hol_light_proof_path'] for r in self.records},
                         {r['metadata']['hol_light_proof_path'] for r in selected})
        for topic in {r['topic'] for r in self.records}:
            all_rows = [r for r in self.records if r['topic'] == topic]
            chosen = [r for r in selected if r['topic'] == topic]
            for field in ('hol_light_proof','isabelle_context_before_target'):
                self.assertEqual(max(len(r[field]) for r in all_rows), max(len(r[field]) for r in chosen))
        self.assertEqual(353, len(select_contexts(self.records, all_targets=True)[0]))
        self.assertEqual(11, len(CONTROL_NAMES))
        self.assertTrue(CONTROL_NAMES <= {c.name for c in proof_cases()})

    def test_new_imports_are_qualified_without_importing_target(self):
        config = DspConfig.load(DEFAULT_CONFIG)
        self.assertEqual('HOL', config.base_session)
        for row in self.records:
            target = validate_context(row)
            _, imports = resolve_imports(target.prefix, config, theory_name=target.theory_name)
            self.assertTrue(all('.' in n or n in {'Main', 'Complex_Main'} for n in imports['resolved_imports']))
            self.assertNotIn(target.theory_name, [n.rsplit('.', 1)[-1] for n in imports['resolved_imports']])
