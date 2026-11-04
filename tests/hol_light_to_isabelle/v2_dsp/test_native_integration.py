"""Opt-in real Isabelle2026 controls; no LLM calls. See the native DSP README."""
from dataclasses import replace
import os
from pathlib import Path
import shutil
import time
import unittest
import uuid

from eval.pipeline.hol_light_to_isabelle.v2_dsp.checker import Checker
from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import proof_cases
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig, NATIVE_DIR
from eval.pipeline.hol_light_to_isabelle.v2_dsp.native_search import NativeSearch
from eval.pipeline.hol_light_to_isabelle.v2_dsp.preflight import control_record, preflight
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import extract_records


@unittest.skipUnless(os.environ.get("ITPEVAL_NATIVE_ISABELLE2026_CONFIG"),
                     "native Isabelle2026 acceptance requires the lab installation")
class NativeIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = DspConfig.load(os.environ["ITPEVAL_NATIVE_ISABELLE2026_CONFIG"])
        cls.backend = cls.config.metadata()

    def test_generic_candidate_timeout_falls_through_to_sledgehammer(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import (
            timeout_hammer_case, run_proof_case)
        config = replace(self.config, step_timeout_s=0.1)
        native = NativeSearch(config)
        parent = native.infrastructure(deadline=time.monotonic()+config.target_timeout_s)
        case = timeout_hammer_case(config)
        result = run_proof_case(case, config=config, backend=self.backend, parent=parent,
                                directory=Checker(config).directory("timeout-hammer-"))
        self.assertTrue(result['ok'], result)
        row = result['result']
        self.assertEqual(1, row['search_summary']['candidate_timeouts'])
        self.assertEqual(1, row['search_summary']['hammer_successes'])
        self.assertNotIn('dsp_regression_delay', row['isabelle_proof'])
        self.assertNotIn('apply (rule conjI)', row['isabelle_proof'])

    def test_partial_candidate_timeout_retries_heuristic_from_saved_state(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import timeout_hammer_case
        config = replace(self.config, step_timeout_s=0.1)
        case = timeout_hammer_case(config)
        class RetryNative(NativeSearch):
            def request(self, record, sketch, **options):
                options['heuristics'] = (case.candidate, 'by simp')
                return super().request(record, sketch, **options)
        result = Checker(config, native_factory=RetryNative).check(case.record, backend_metadata=self.backend)
        self.assertTrue(result['verified'], result['verify_error'])
        attempts = [s for s in result['step_results'] if s['mode']=='heuristic']
        self.assertEqual([False, True], [s['success'] for s in attempts])
        self.assertEqual('candidate', attempts[0]['timeout_scope'])
        self.assertEqual(attempts[0]['source_state'], attempts[1]['source_state'])
        self.assertEqual(0, result['search_summary']['hammer_attempts'])
        self.assertNotIn('dsp_regression_delay', result['isabelle_proof'])
        self.assertNotIn('apply (rule conjI)', result['isabelle_proof'])

    def test_required_source_command_timeout_still_aborts(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import timeout_hammer_case
        config = replace(self.config, step_timeout_s=0.1)
        row = {**timeout_hammer_case(config).record, 'isabelle_sketch':'by dsp_regression_delay'}
        result = Checker(config).check(row, backend_metadata=self.backend)
        self.assertFalse(result['verified'])
        self.assertEqual('timeout', result['failure_category'])
        self.assertEqual('search', result['step_results'][-1]['mode'])
        self.assertEqual(0, result['search_summary']['candidate_timeouts'])
        self.assertEqual(0, result['search_summary']['hammer_attempts'])

    def test_sledgehammer_reserve_skips_heuristics_when_budget_is_short(self):
        config = replace(self.config, target_timeout_s=90, hammer_timeout_s=90,
                         step_timeout_s=1, provers=('simp',))
        result = Checker(config).check(control_record('sledgehammer'), backend_metadata=self.backend)
        self.assertTrue(result['verified'], result['verify_error'])
        self.assertEqual(0, result['search_summary']['heuristic_attempts'])
        self.assertEqual(1, result['search_summary']['hammer_successes'])
        self.assertEqual(1, result['search_summary']['reconstruction_successes'])

    def test_pair_sum_rules_are_generic_and_preserve_pointwise_assumptions(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.sanitize_isabelle import sanitize_target
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.checker import HEURISTICS
        config = replace(self.config, provers=('dsp_nonexistent_prover',))
        cases = [
            (True, r"\<And>p::('a*'b)set. \<And>f::'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector. "
                r"finite p \<Longrightarrow> norm (\<Sum>(x,k)\<in>p. f x k) \<le> (\<Sum>(x,k)\<in>p. norm (f x k))",
                "by (simp only: case_prod_beta'; rule norm_sum)"),
            (True, r"\<And>p::('a*'b)set. \<And>f g::'a \<Rightarrow> 'b \<Rightarrow> real. "
                r"(\<And>x k. (x,k)\<in>p \<Longrightarrow> f x k \<le> g x k) \<Longrightarrow> "
                r"(\<Sum>(x,k)\<in>p. f x k) \<le> (\<Sum>(x,k)\<in>p. g x k)",
                "by (simp only: case_prod_beta'; intro sum_mono; force)"),
            (True, r"\<And>p::('a*'b)set. \<And>f::'a \<Rightarrow> 'b \<Rightarrow> real. \<And>c t::real. "
                r"(\<Sum>(x,k)\<in>p. f x k) = t \<Longrightarrow> (\<Sum>(x,k)\<in>p. c * f x k) = c*t",
                "by (simp add: case_prod_beta' sum_distrib_left[symmetric] sum_distrib_right[symmetric])"),
            (False, r"\<And>p::('a*'b)set. \<And>f g::'a \<Rightarrow> 'b \<Rightarrow> real. "
                r"(\<Sum>(x,k)\<in>p. f x k) \<le> (\<Sum>(x,k)\<in>p. g x k)",
                "by (simp only: case_prod_beta'; intro sum_mono; force)"),
        ]
        for valid, goal, candidate in cases:
            with self.subTest(valid=valid, candidate=candidate):
                self.assertIn(candidate, HEURISTICS)
                row = control_record('sledgehammer', conclusion=goal)
                template = row['isabelle_theory_template'].replace('imports Main', 'imports Complex_Main')
                target = sanitize_target(template, row['isabelle_target_name'])
                row.update(isabelle_theory_template=template, isabelle_statement=target.statement,
                    formal_statement=target.statement, isabelle_context_before_target=target.context_before_target,
                    isabelle_target_proof_span=list(target.proof_span), isabelle_proof_prefix=target.proof_prefix)
                class RuleNative(NativeSearch):
                    def request(self, record, sketch, **options):
                        options['heuristics'] = (candidate,)
                        return super().request(record, sketch, **options)
                result = Checker(config, native_factory=RuleNative).check(row, backend_metadata=self.backend)
                self.assertEqual(valid, result['verified'], result['verify_error'])
                if valid:
                    self.assertEqual(1, result['search_summary']['heuristic_successes'])
                    self.assertEqual(0, result['search_summary']['hammer_attempts'])

    def test_scaled_norm_heuristics_preserve_required_sign_conditions(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.sanitize_isabelle import sanitize_target
        # Disable ATP fallback: the valid obligation must be closed by the native
        # heuristic portfolio; the invalid variant must never acquire a sign fact.
        config = replace(self.config, provers=("dsp_nonexistent_prover",))
        goal = (r"\<And>c::real. \<And>u::'a::real_normed_vector. \<And>b::real. "
                r"0 \<le> c \<Longrightarrow> norm u \<le> b \<Longrightarrow> "
                r"norm (c *\<^sub>R u) \<le> b*c")
        for valid in (True, False):
            conclusion = goal if valid else goal.replace(r"0 \<le> c \<Longrightarrow> ", "")
            row = control_record("sledgehammer", conclusion=conclusion)
            template = row["isabelle_theory_template"].replace("imports Main", "imports Complex_Main")
            target = sanitize_target(template, row["isabelle_target_name"])
            row.update(isabelle_theory_template=template, isabelle_statement=target.statement,
                       isabelle_context_before_target=target.context_before_target,
                       isabelle_target_proof_span=list(target.proof_span), isabelle_proof_prefix=target.proof_prefix)
            result = Checker(config).check(row, backend_metadata=self.backend)
            self.assertEqual(valid, result["verified"], result.get("verify_error"))
            if valid:
                self.assertTrue(any(s["mode"] == "heuristic" and s["success"] for s in result["step_results"]))
                self.assertFalse(any(s["mode"] == "hammer" for s in result["step_results"]))

    def test_cached_import_parent_keeps_context_and_ancestor_guard(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.import_cache import prepare_import_parents
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.parallel import plan_parallel
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import PreparedNative
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.sanitize_isabelle import sanitize_target
        row = control_record("by simp")
        template = row["isabelle_theory_template"].replace("imports Main", 'imports "HOL-Library.Finite_Map"')
        target = sanitize_target(template, row["isabelle_target_name"])
        row.update(isabelle_theory_template=template, isabelle_statement=target.statement,
                   isabelle_context_before_target=target.context_before_target,
                   isabelle_target_proof_span=list(target.proof_span), isabelle_proof_prefix=target.proof_prefix)
        inherited = next(c.record for c in proof_cases() if c.name == "inherited_theory_search")
        config = replace(self.config, threads=1)
        native = NativeSearch(config)
        parent = native.infrastructure(deadline=time.monotonic()+config.target_timeout_s)
        parents, _ = prepare_import_parents(config, [row, inherited], plan_parallel(config), parent)
        checker = Checker(config, native_factory=lambda cfg: PreparedNative(cfg, parent, import_parents=parents))
        result = checker.check(row, backend_metadata=self.backend)
        self.assertTrue(result["verified"], result.get("verify_error"))
        self.assertTrue(result["native_search"]["parent_session"].startswith("DSP_Imports_"))
        rejected = checker.check(inherited, backend_metadata=self.backend)
        self.assertFalse(rejected["verified"])
        self.assertEqual("context_error", rejected["failure_category"])
        self.assertIn("already inherited", rejected["verify_error"])

    def test_controls_in_both_input_modes(self):
        for mode in ("draft", "hol-light-proof"):
            with self.subTest(mode=mode):
                result = preflight(control_record("by simp", sketch_source=mode), config=self.config,
                                   backend_metadata=self.backend, sketch_source=mode)
                self.assertTrue(result["ok"], result)
                hammer = result["controls"]["hammer"]
                settings = hammer["prover_settings"]
                self.assertEqual("some", settings["native_outcome"])
                self.assertGreater(int(settings["candidate_count"]), 0)
                self.assertIn(settings["reconstruction_source"], {"preplayed", "native_tactic"})
                self.assertTrue(any(row["mode"] == "reconstruction" and row["success"]
                                    for row in hammer["step_results"]))

    def test_native_tactic_without_separate_preplay_is_executed_and_closed(self):
        config = replace(self.config, provers=("simp",))
        proof = "proof -\n show True\n sledgehammer\nqed"
        row = control_record(proof, extra_context="sledgehammer_params [falsify = true, abduce = 1]\n")
        result = Checker(config).check(row, force_hammer=True, backend_metadata=config.metadata())
        self.assertTrue(result["verified"], result["verify_error"])
        settings = result["prover_settings"]
        self.assertEqual("native_tactic", settings["reconstruction_source"])
        self.assertIn("falsify = SOME false", " ".join(settings["native_parameters"].split()))
        self.assertIn("abduce = SOME 0", settings["native_parameters"])
        self.assertEqual("0", settings["preplay_count"])
        self.assertGreater(int(settings["candidate_count"]), 0)
        self.assertTrue(any(row["mode"] == "reconstruction" and row["success"]
                            for row in result["step_results"]))
        self.assertTrue(result["native_search"]["target_closed"])

    def test_native_reconstruction_without_pide_and_failed_preplay_filter(self):
        native = NativeSearch(self.config)
        deadline = time.monotonic() + self.config.target_timeout_s
        parent_dir, parent_session = native.infrastructure(deadline=deadline)
        directory = Checker(self.config).directory("reconstruction-regression-")
        theory = "DSP_Reconstruction_Test"
        source = NATIVE_DIR / "checks" / (theory + ".thy")
        shutil.copyfile(source, directory / source.name)
        session = "DSP_Reconstruction_Test_" + uuid.uuid4().hex
        (directory / "ROOT").write_text(
            f"session {session} = {parent_session} +\n"
            f"  options [document = false]\n  theories {theory}\n", encoding="utf-8")
        code = native.run_build(directory, session, timeout_s=self.config.startup_timeout_s,
                                deadline=deadline, parent_dir=parent_dir)
        self.assertEqual(0, code, (directory / "build.log").read_text(encoding="utf-8"))

    def test_using_reconstruction_executes_separators_and_comments(self):
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import proof_cases, run_proof_case
        parent = NativeSearch(self.config).infrastructure(deadline=time.monotonic() + self.config.target_timeout_s)
        for case in proof_cases():
            if case.candidate is not None:
                with self.subTest(case=case.name):
                    result = run_proof_case(case, config=self.config, backend=self.backend, parent=parent,
                        directory=Checker(self.config).directory("using-regression-"))
                    self.assertTrue(result["ok"], result)

    def test_nested_isar_multiple_gaps_local_assumptions_and_symbols(self):
        proof = ("proof -\n have first: True\n  sledgehammer\n"
                 " have both: \\<open>True \\<and> True\\<close>\n"
                 " proof\n  show True using first\n   sledgehammer\n"
                 "  show True using first\n   sledgehammer\n qed\n"
                 " show True using both\n  sledgehammer\nqed")
        for mode in ("draft", "hol-light-proof"):
            result = Checker(self.config).check(control_record(proof, sketch_source=mode), backend_metadata=self.backend)
            self.assertTrue(result["verified"], result["verify_error"])
            self.assertNotIn("sledgehammer", result["isabelle_proof"])

    def test_multiple_subgoals_and_quoted_terms_are_reconstructed_and_closed(self):
        config = replace(self.config, provers=("simp",))
        proof = ('proof -\n have both: "True \\<and> True"\n'
                 '  apply (rule conjI)\n  sledgehammer\n'
                 ' from both show "True" by simp\nqed')
        result = Checker(config).check(control_record(proof), force_hammer=True,
                                       backend_metadata=config.metadata())
        self.assertTrue(result["verified"], result["verify_error"])
        self.assertIn('"True \\<and> True"', result["isabelle_proof"])
        self.assertNotIn("\x7f", result["isabelle_proof"])
        steps = [step for step in result["step_results"]
                 if step["mode"] == "reconstruction" and step["success"]]
        self.assertGreaterEqual(len(steps), 2)
        self.assertTrue(any(step["command"].lstrip().startswith("apply") for step in steps))
        self.assertTrue(result["native_search"]["target_closed"])

    def test_partial_reconstruction_cannot_admit_the_remaining_subgoal(self):
        config = replace(self.config, provers=("simp",))
        proof = ('proof -\n have impossible: "True \\<and> False"\n'
                 '  apply (rule conjI)\n  sledgehammer\n'
                 ' then show "True" by simp\nqed')
        result = Checker(config).check(control_record(proof), force_hammer=True,
                                       backend_metadata=config.metadata())
        self.assertFalse(result["verified"])
        self.assertFalse(result["prove_success"])
        self.assertNotIn("native_replay", result)
        self.assertTrue(any(step["mode"] == "reconstruction" and step["success"]
                            for step in result["step_results"]))

    def test_local_blocks_short_proofs_and_local_definition_commands(self):
        proofs = [
            'proof -\n { have "True" .. }\n then show "True" .\nqed',
            'proof -\n define t where "t = True"\n'
            ' have ht: t unfolding t_def by simp\n'
            ' consider t using ht by blast\n then show True by cases simp\nqed',
            'proof -\n show "True"\n subgoal by simp\n done\nqed',
            'proof -\n show "True"\n apply simp\n sledgehammer\nqed',
        ]
        for proof in proofs:
            with self.subTest(proof=proof):
                result = Checker(self.config).check(control_record(proof), backend_metadata=self.backend)
                self.assertTrue(result["verified"], result["verify_error"])
                self.assertNotIn("\x7f", result["isabelle_proof"])

    def test_unavailable_prover_and_timeout_cannot_pass(self):
        proof = "proof -\n show True\n sledgehammer\nqed"
        config = replace(self.config, provers=("dsp_nonexistent_prover",))
        result = Checker(config).check(control_record(proof), force_hammer=True, backend_metadata=config.metadata())
        self.assertFalse(result["verified"])
        self.assertEqual("hammer_failure", result["failure_category"])
        self.assertEqual("dsp_nonexistent_prover", result["prover_settings"]["resolved_provers"])
        # Sub-millisecond settings are rejected rather than disabling ML timeouts.
        with self.assertRaisesRegex(ValueError, "0.001"):
            replace(self.config, step_timeout_s=0.000001)

    def test_babel_locale_source_modes_and_hundred_context(self):
        from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import export_record
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as hundred
        babel = extract_records(topic="circle_average", target_key="circleAverage_center_independent")[0]
        for mode in ("draft", "hol-light-proof"):
            raw = {**babel, "draft": "Unfold both definitions and use integral_shift."}
            record = export_record(raw, sketch_source=mode)
            record["isabelle_sketch"] = "proof -\n show ?thesis unfolding circleAverage_def circleMap_def\n sledgehammer\nqed"
            result = Checker(self.config).check(record, backend_metadata=self.backend)
            self.assertTrue(result["verified"], result["verify_error"])
        record = hundred(topic="030_the_ballot_problem", target_key="all_countings")[0]
        self.assertTrue(Checker(self.config).check_context(record, backend_metadata=self.backend)["baseline_ok"])
        for mode in ("draft", "hol-light-proof"):
            raw = {**record, "draft": "Use all_countings_set and the cardinality of fixed-size subsets."}
            row = export_record(raw, expected_source="hundred-theorems", sketch_source=mode)
            row["isabelle_sketch"] = "by (simp add: all_countings_set n_subsets)"
            result = Checker(self.config).check(row, backend_metadata=self.backend)
            self.assertTrue(result["verified"], result["verify_error"])


    def test_corrected_real_run_sketches_in_circle_average_locale(self):
        """Manual syntax diagnostics; never counted as model-generated successes."""
        import json
        from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import export_record
        examples = json.loads((Path(__file__).parent / "fixtures/DSP_Sketch_Syntax.json").read_text(encoding="utf-8"))
        raw = extract_records(topic="circle_average", target_key="circleAverage_center_independent")[0]
        raw["draft"] = "Unfold the definitions and apply integral_shift."
        for mode, name in [("draft", "draft_corrected"), ("hol-light-proof", "direct_corrected")]:
            with self.subTest(mode=mode):
                row = export_record(raw, sketch_source=mode)
                row["isabelle_sketch"] = examples[name]
                result = Checker(self.config).check(row, backend_metadata=self.backend)
                self.assertTrue(result["verified"], result["verify_error"])
                self.assertTrue(result["native_search"]["target_closed"])

    def test_hundred_rsum_bound_original_context_imports(self):
        """Real import graph + 153 masked helpers; no model or target proof supplied."""
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as hundred
        config = replace(self.config, theory_imports={**self.config.theory_imports,
            "Lebesgue_Measure": "HOL-Analysis.Lebesgue_Measure",
            "Tagged_Division": "HOL-Analysis.Tagged_Division"})
        record = hundred(topic="015_the_fundamental_theorem_of_integral_calculus", target_key="rsum_bound")[0]
        result = Checker(config).check_context(record, backend_metadata=config.metadata())
        self.assertTrue(result["baseline_ok"], result)
        self.assertIn("HOL-Analysis", result["native_result"]["import_resolution"]["session_dependencies"])

    def test_preflight_context_regressions_in_real_isabelle(self):
        from eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light import extract_records as hundred
        from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.acceptance import PreparedNative
        parent = NativeSearch(self.config).infrastructure(deadline=time.monotonic() + self.config.target_timeout_s)
        checker = Checker(self.config, native_factory=lambda cfg: PreparedNative(cfg, parent))
        for topic, name in (
            ('078_the_cauchy-schwarz_inequality', 'norm_cauchy_schwarz'),
            ('089_the_factor_and_remainder_theorems', 'poly_zero'),
            ('098_bertrand_s_postulate', 'bertrand'),
        ):
            with self.subTest(topic=topic):
                record = hundred(topic=topic, target_key=name)[0]
                self.assertTrue(checker.check_context(record, backend_metadata=self.backend)['baseline_ok'])

    def test_external_e_prover_reconstruction_and_target_completion(self):
        # The default True control may be solved by an integrated tactic. This
        # explicitly tests the bundled external ATP + preplay + reconstruction.
        config = replace(self.config, provers=("e",))
        proof = 'proof -\n show "True"\n sledgehammer\nqed'
        result = Checker(config).check(control_record(proof), force_hammer=True,
                                       backend_metadata=config.metadata())
        self.assertTrue(result["verified"], result["verify_error"])
        settings = result["prover_settings"]
        self.assertEqual("e", settings["resolved_provers"])
        self.assertEqual("preplayed", settings["reconstruction_source"])
        self.assertGreater(int(settings["preplayed_count"]), 0)
        self.assertTrue(result["native_search"]["target_closed"])

    def test_imported_smt_setting_does_not_enable_oracle_proofs(self):
        row = control_record("by (smt)", extra_context="declare [[smt_oracle = true]]\n")
        result = Checker(self.config).check(row, backend_metadata=self.backend)
        self.assertTrue(result["verified"], result["verify_error"])
        self.assertTrue(result["native_search"]["target_closed"])
        self.assertNotIn("native_replay", result)

    def test_inherited_target_theory_is_rejected_before_search(self):
        case = next(c for c in proof_cases() if c.name == "inherited_theory_search")
        result = Checker(self.config).check(case.record, backend_metadata=self.backend)
        self.assertFalse(result["verified"])
        self.assertEqual("context_error", result["failure_category"])
        self.assertIn("already inherited", result["verify_error"])



if __name__ == "__main__":
    unittest.main()
