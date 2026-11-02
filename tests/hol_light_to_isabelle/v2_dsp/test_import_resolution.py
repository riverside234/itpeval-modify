"""Import and target-context checks shared by both datasets."""
import unittest
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.pisa_context import prepare_context,resolve_imports
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.runtime import DspConfig,PisaFailure
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight import control_record

class ImportTests(unittest.TestCase):
    def test_only_explicit_mappings_are_qualified(self):
        config=DspConfig(theory_imports={"Lebesgue_Measure":"HOL-Analysis.Lebesgue_Measure"})
        source='theory Example imports Lebesgue_Measure Main begin\nlemma goal: "True"'
        resolved,report=resolve_imports(source,config,theory_name="Example")
        self.assertIn('"HOL-Analysis.Lebesgue_Measure" Main',resolved)
        self.assertEqual(['HOL-Analysis.Lebesgue_Measure','Main'],report['resolved_imports'])
        self.assertTrue(resolved.endswith('lemma goal: "True"'))

    def test_target_import_and_renamed_mapping_are_rejected(self):
        for name in ('Test','Test.thy','HOL.Test','HOL.Test.thy'):
            with self.assertRaises(PisaFailure):
                resolve_imports('theory Test imports "'+name+'" begin',DspConfig(),theory_name='Test')
        with self.assertRaises(ValueError):
            DspConfig(theory_imports={"Unknown":"HOL.Main"})

    def test_later_declarations_are_not_in_the_prover_input(self):
        row=control_record('by simp')
        row['isabelle_theory_template']=row['isabelle_theory_template'].rsplit('end',1)[0]+'lemma secret: "False" sorry\nend\n'
        _,source,_=prepare_context(row,DspConfig())
        self.assertNotIn('secret',source)
        self.assertLess(source.index('quick_and_dirty = false'),source.index('lemma v2_control'))

if __name__ == '__main__':
    unittest.main()
