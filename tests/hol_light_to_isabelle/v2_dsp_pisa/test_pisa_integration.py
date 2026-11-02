"""Optional integration check using the same cases as the recorded lab preflight."""
import os
import unittest
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.acceptance import proof_cases,run_proof_case
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.runtime import DspConfig
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa.checker import Checker

@unittest.skipUnless(os.environ.get("ITPEVAL_PISA_ISABELLE2021_CONFIG"),"requires the lab PISA/Isabelle2021 installation")
class PisaIntegrationTests(unittest.TestCase):
    def test_upstream_proof_and_negative_controls(self):
        config=DspConfig.load(os.environ["ITPEVAL_PISA_ISABELLE2021_CONFIG"])
        backend=config.metadata()
        for case in proof_cases():
            with self.subTest(case=case.name):
                result=run_proof_case(case,config=config,backend=backend,directory=Checker(config).directory("pisa-integration-"))
                self.assertTrue(result["ok"],result)
