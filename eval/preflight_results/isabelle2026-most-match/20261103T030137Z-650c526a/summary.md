# Isabelle2026 lab preflight

Status: **complete**; overall OK: **False**.
Backend OK: **True**; available dataset checks OK: **False**.

Scope: `all_targets`; 353 contexts.

| Check | Domain | Status | Failure | Details |
| --- | --- | --- | --- | --- |
| input_selection | selection | pass |  | [Line 1](checks.jsonl) |
| metadata | setup | pass |  | [Line 2](checks.jsonl) |
| dependencies | setup | pass |  | [Line 3](checks.jsonl) |
| infrastructure | setup | pass |  | [Line 4](checks.jsonl) |
| native_fixture | backend | pass |  | [Line 5](checks.jsonl) |
| explicit_draft | backend | pass |  | [Line 6](checks.jsonl) |
| explicit_direct | backend | pass |  | [Line 7](checks.jsonl) |
| hammer_configured | backend | pass |  | [Line 8](checks.jsonl) |
| hammer_external_e | backend | pass |  | [Line 9](checks.jsonl) |
| using_reconstruction_comments | backend | pass |  | [Line 10](checks.jsonl) |
| multiple_subgoals | backend | pass |  | [Line 11](checks.jsonl) |
| invalid_method | backend | pass |  | [Line 12](checks.jsonl) |
| admission_rejected | backend | pass |  | [Line 13](checks.jsonl) |
| self_reference_rejected | backend | pass |  | [Line 14](checks.jsonl) |
| later_fact_rejected | backend | pass |  | [Line 15](checks.jsonl) |
| inherited_theory_search | backend | pass |  | [Line 16](checks.jsonl) |
| most_match_cross_refl | dataset_proof | pass |  | [Line 17](checks.jsonl) |
| context_hol-most-match_Bumping_bumpform | context | pass |  | [Line 18](checks.jsonl) |
| context_hol-most-match_Bumping_bumpform_interpretation | context | pass |  | [Line 19](checks.jsonl) |
| context_hol-most-match_Bumping_bumpterm | context | pass |  | [Line 20](checks.jsonl) |
| context_hol-most-match_Bumping_functions_form_bumpform | context | pass |  | [Line 21](checks.jsonl) |
| context_hol-most-match_Bumping_num_of_form_inj | context | pass |  | [Line 22](checks.jsonl) |
| context_hol-most-match_Bumping_num_of_term_inj | context | pass |  | [Line 23](checks.jsonl) |
| context_hol-most-match_Bumping_numlist_num_of_term | context | pass |  | [Line 24](checks.jsonl) |
| context_hol-most-match_Bumping_unbumpform | context | pass |  | [Line 25](checks.jsonl) |
| context_hol-most-match_Bumping_unbumpterm | context | pass |  | [Line 26](checks.jsonl) |
| context_hol-most-match_Canonical_Models_canon | context | pass |  | [Line 27](checks.jsonl) |
| context_hol-most-match_Canonical_Models_canonical_canon_of_prop | context | pass |  | [Line 28](checks.jsonl) |
| context_hol-most-match_Canonical_Models_compact_canon_qfree | context | pass |  | [Line 29](checks.jsonl) |
| context_hol-most-match_Canonical_Models_compact_ls | context | pass |  | [Line 30](checks.jsonl) |
| context_hol-most-match_Canonical_Models_finite_subset_instance | context | pass |  | [Line 31](checks.jsonl) |
| context_hol-most-match_Canonical_Models_finite_subset_skolem | context | pass |  | [Line 32](checks.jsonl) |
| context_hol-most-match_Canonical_Models_fol_valid_imp_prop_valid | context | pass |  | [Line 33](checks.jsonl) |
| context_hol-most-match_Canonical_Models_holds_canon_of_prop | context | pass |  | [Line 34](checks.jsonl) |
| context_hol-most-match_Canonical_Models_holds_canon_of_prop_general | context | pass |  | [Line 35](checks.jsonl) |
| context_hol-most-match_Canonical_Models_holds_itlist_exists | context | pass |  | [Line 36](checks.jsonl) |
| context_hol-most-match_Canonical_Models_interpretation_canon_of_prop | context | pass |  | [Line 37](checks.jsonl) |
| context_hol-most-match_Canonical_Models_interpretation_extendlanguage | context | pass |  | [Line 38](checks.jsonl) |
| context_hol-most-match_Canonical_Models_interpretation_restrictlanguage | context | pass |  | [Line 39](checks.jsonl) |
| context_hol-most-match_Canonical_Models_lowmod_dom_empty | context | pass |  | [Line 40](checks.jsonl) |
| context_hol-most-match_Canonical_Models_lowmod_holds | context | pass |  | [Line 41](checks.jsonl) |
| context_hol-most-match_Canonical_Models_lowmod_termval | context | pass |  | [Line 42](checks.jsonl) |
| context_hol-most-match_Canonical_Models_prop_valid_imp_fol_valid | context | pass |  | [Line 43](checks.jsonl) |
| context_hol-most-match_Canonical_Models_psatisfies_instances | context | pass |  | [Line 44](checks.jsonl) |
| context_hol-most-match_Canonical_Models_satisfies_instances | context | pass |  | [Line 45](checks.jsonl) |
| context_hol-most-match_Canonical_Models_satisfies_psatisfies | context | pass |  | [Line 46](checks.jsonl) |
| context_hol-most-match_Canonical_Models_uniformity | context | pass |  | [Line 47](checks.jsonl) |
| context_hol-most-match_Canonical_Models_valuation_exists | context | pass |  | [Line 48](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_null_homotopic | context | fail | NativeFailure: native worker produced no structured result (exit status 137); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-xayqxnbp/build.log Running DSP_Jo | [Line 49](checks.jsonl) |
| context_hol-most-match_Cross3_cross_basis | context | fail | NativeFailure: native worker produced no structured result (exit status 137); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-s0eqxdpm/build.log Running DSP_Jo | [Line 50](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_holomorphic_convex_primitive | context | fail | NativeFailure: native worker produced no structured result (exit status 137); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-c0t295y3/build.log Running DSP_Jo | [Line 51](checks.jsonl) |
| context_hol-most-match_Continuous_Extension_Urysohn_local | context | pass |  | [Line 52](checks.jsonl) |
| context_hol-most-match_Continuous_Extension_subordinate_partition_of_unity | context | pass |  | [Line 53](checks.jsonl) |
| context_hol-most-match_Continuous_Extension_Dugundji | context | pass |  | [Line 54](checks.jsonl) |
| context_hol-most-match_Continuous_Extension_Urysohn | context | pass |  | [Line 55](checks.jsonl) |
| context_hol-most-match_Continuous_Extension_Tietze | context | pass |  | [Line 56](checks.jsonl) |
| context_hol-most-match_Continuous_Extension_Urysohn_strong | context | pass |  | [Line 57](checks.jsonl) |
| context_hol-most-match_Continuous_Extension_Urysohn_local_strong | context | pass |  | [Line 58](checks.jsonl) |
| context_hol-most-match_Cross3_cross_orthogonal_matrix | context | fail | NativeFailure: native worker produced no structured result (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ua9ilz3n/build.log Running DSP_Job_ | [Line 59](checks.jsonl) |
| context_hol-most-match_Cross3_bilinear_cross | context | fail | NativeFailure: native worker produced no structured result (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-4xf6nu7m/build.log Running DSP_Job_ | [Line 60](checks.jsonl) |
| context_hol-most-match_Cross3_continuous_on_cross | context | fail | NativeFailure: native worker produced no structured result (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-g2lr9440/build.log Running DSP_Job_ | [Line 61](checks.jsonl) |
| context_hol-most-match_Cross3_cross_eq_self | context | fail | NativeFailure: native worker produced no structured result (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-r9bernlu/build.log Running DSP_Job_ | [Line 62](checks.jsonl) |
| context_hol-most-match_Cross3_cross_cross_det | context | pass |  | [Line 63](checks.jsonl) |
| context_hol-most-match_Cross3_continuous_cross | context | pass |  | [Line 64](checks.jsonl) |
| context_hol-most-match_Cross3_cross_basis_nonzero | context | pass |  | [Line 65](checks.jsonl) |
| context_hol-most-match_Cross3_cross_dot_cancel | context | pass |  | [Line 66](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_homotopic_loops | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-yckd92ey/build.log (exit status -15); /data/not | [Line 67](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_convex_simple | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-0gkkldi0/build.log (exit status -15); /data/not | [Line 68](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_flat | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-vva4pvk4/build.log (exit status -15); /data/not | [Line 69](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_flat_lemma | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-tznmdr7y/build.log (exit status -15); /data/not | [Line 70](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_homotopic_paths | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-rxz7a0nu/build.log (exit status -15); /data/not | [Line 71](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_quadrisection | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-380nymqj/build.log (exit status -15); /data/not | [Line 72](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_starlike | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ebr7saq7/build.log (exit status -15); /data/not | [Line 73](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_starlike_simple | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-bk0tdkjo/build.log (exit status -15); /data/not | [Line 74](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_Cauchy_theorem_triangle_interior | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-o8iobove/build.log (exit status -15); /data/not | [Line 75](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_holomorphic_point_small_triangle | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ci_kg4l3/build.log (exit status -15); /data/not | [Line 76](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_holomorphic_starlike_primitive | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-is_4682y/build.log (exit status -15); /data/not | [Line 77](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_norm_sum_lemma | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ul4yvf9w/build.log (exit status -15); /data/not | [Line 78](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_starlike_convex_subset | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-2c2octlg/build.log (exit status -15); /data/not | [Line 79](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_triangle_linear_has_chain_integral | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-22cab617/build.log (exit status -15); /data/not | [Line 80](checks.jsonl) |
| context_hol-most-match_Cauchy_Integral_Theorem_triangle_points_closer | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-zb7lq_dg/build.log (exit status -15); /data/not | [Line 81](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_Bloch | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-bx_z2pyw/build.log (exit status -15); /data/not | [Line 82](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_Bloch_lemma | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-asshooqz/build.log (exit status -15); /data/not | [Line 83](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_Bloch_unit | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-w7b_21z2/build.log (exit status -15); /data/not | [Line 84](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_Schwarz_Lemma | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-vibkmxei/build.log (exit status -15); /data/not | [Line 85](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_Schwarz_reflection | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-spit7evy/build.log (exit status -15); /data/not | [Line 86](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_analytic_continuation | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-6k3lrftz/build.log (exit status -15); /data/not | [Line 87](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_covering_space_lift_holomorphic | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-lg_0cixs/build.log (exit status -15); /data/not | [Line 88](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_covering_space_lift_is_holomorphic | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ed2ltkb5/build.log (exit status -15); /data/not | [Line 89](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_has_complex_derivative_locally_injective | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ngdmy32o/build.log (exit status -15); /data/not | [Line 90](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_has_complex_derivative_locally_invertible | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-jo29ojuj/build.log (exit status -15); /data/not | [Line 91](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_holomorphic_factor_order_of_zero | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-a6uulpqe/build.log (exit status -15); /data/not | [Line 92](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_holomorphic_factor_order_of_zero_strong | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-5nd1r1rw/build.log (exit status -15); /data/not | [Line 93](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_holomorphic_factor_zero_nonconstant | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-g99_68vx/build.log (exit status -15); /data/not | [Line 94](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_holomorphic_injective_imp_regular | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-jcm2h_jd/build.log (exit status -15); /data/not | [Line 95](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_holomorphic_lower_bound_difference | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-6874qs38/build.log (exit status -15); /data/not | [Line 96](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_holomorphic_on_paste_across_line | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ogt05j6p/build.log (exit status -15); /data/not | [Line 97](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_isolated_zeros | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-mcxelgis/build.log (exit status -15); /data/not | [Line 98](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_maximum_modulus_frontier | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-uat2ik4f/build.log (exit status -15); /data/not | [Line 99](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_maximum_modulus_principle | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ykdmnrmz/build.log (exit status -15); /data/not | [Line 100](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_open_mapping_thm | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-x0v_p3_5/build.log (exit status -15); /data/not | [Line 101](checks.jsonl) |
| context_hol-most-match_Conformal_Mappings_pole_at_infinity | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-r0jv9ktt/build.log (exit status -15); /data/not | [Line 102](checks.jsonl) |
| context_hol-most-match_Cross3_cross_components | context | pass |  | [Line 103](checks.jsonl) |
| context_hol-most-match_Cross3_cross_eq_0 | context | pass |  | [Line 104](checks.jsonl) |
| context_hol-most-match_Cross3_cross_orthogonal_transformation | context | pass |  | [Line 105](checks.jsonl) |
| context_hol-most-match_Cross3_cross_rotation_matrix | context | pass |  | [Line 106](checks.jsonl) |
| context_hol-most-match_Cross3_cross_refl | context | pass |  | [Line 107](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_splitting_lemma_left_gen | context | pass |  | [Line 108](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_exact_sequence_sum_lemma | context | pass |  | [Line 109](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_splitting_lemma_left | context | pass |  | [Line 110](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_splitting_lemma_right | context | pass |  | [Line 111](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_splitting_lemma_right_gen | context | pass |  | [Line 112](checks.jsonl) |
| context_hol-most-match_Cross3_cross_linear_image | context | pass |  | [Line 113](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_splitting_sublemma | context | pass |  | [Line 114](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_splitting_sublemma_gen | context | pass |  | [Line 115](checks.jsonl) |
| context_hol-most-match_Exact_Sequence_very_short_exact_sequence | context | pass |  | [Line 116](checks.jsonl) |
| context_hol-most-match_FSigma_homeomorphic_map_fsigmaness_eq | context | pass |  | [Line 117](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_diff | context | pass |  | [Line 118](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_topspace | context | pass |  | [Line 119](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_Union | context | pass |  | [Line 120](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_subtopology | context | pass |  | [Line 121](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_empty | context | pass |  | [Line 122](checks.jsonl) |
| context_hol-most-match_FSigma_open_imp_gdelta_in | context | pass |  | [Line 123](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_gdelta_subtopology | context | pass |  | [Line 124](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_subset | context | pass |  | [Line 125](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_alt | context | pass |  | [Line 126](checks.jsonl) |
| context_hol-most-match_FSigma_closed_imp_fsigma_in | context | pass |  | [Line 127](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_topspace | context | pass |  | [Line 128](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_relative_to | context | pass |  | [Line 129](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_subset | context | pass |  | [Line 130](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_ascending | context | pass |  | [Line 131](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_diff | context | pass |  | [Line 132](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_empty | context | pass |  | [Line 133](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_fsigma_subtopology | context | pass |  | [Line 134](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_fsigma_in | context | pass |  | [Line 135](checks.jsonl) |
| context_hol-most-match_FSigma_homeomorphic_map_fsigmaness | context | pass |  | [Line 136](checks.jsonl) |
| context_hol-most-match_FSigma_homeomorphic_map_gdeltaness | context | pass |  | [Line 137](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_gdelta_in | context | pass |  | [Line 138](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_relative_to | context | pass |  | [Line 139](checks.jsonl) |
| context_hol-most-match_FSigma_fsigma_in_subtopology | context | pass |  | [Line 140](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_Inter | context | pass |  | [Line 141](checks.jsonl) |
| context_hol-most-match_FSigma_gdelta_in_descending | context | pass |  | [Line 142](checks.jsonl) |
| context_hol-most-match_FSigma_homeomorphic_map_gdeltaness_eq | context | pass |  | [Line 143](checks.jsonl) |
| context_hol-most-match_Cross3_cross_rotoinversion_matrix | context | pass |  | [Line 144](checks.jsonl) |
| context_hol-most-match_Cross3_cross_skew | context | pass |  | [Line 145](checks.jsonl) |
| context_hol-most-match_Cross3_norm_cross | context | pass |  | [Line 146](checks.jsonl) |
| context_hol-most-match_Cross3_cross_triple | context | pass |  | [Line 147](checks.jsonl) |
| context_hol-most-match_Cross3_norm_and_cross_eq_0 | context | pass |  | [Line 148](checks.jsonl) |
| context_hol-most-match_Cross3_orthogonal_cross | context | pass |  | [Line 149](checks.jsonl) |
| context_hol-most-match_Cross3_dot_cross_det | context | pass |  | [Line 150](checks.jsonl) |
| context_hol-most-match_Cross3_dot_cross_self | context | pass |  | [Line 151](checks.jsonl) |
| context_hol-most-match_Cross3_norm_cross_dot | context | pass |  | [Line 152](checks.jsonl) |
| context_hol-most-match_Cross3_dot_cross | context | pass |  | [Line 153](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_fashoda_unit | context | fail | NativeFailure: native worker produced no structured result (exit status 137); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-pbdo7ips/build.log Running DSP_Jo | [Line 154](checks.jsonl) |
| context_hol-most-match_Great_Picard_little_Picard | context | fail | NativeFailure: native worker produced no structured result (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-mm2fwl2z/build.log Running DSP_Job_ | [Line 155](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_continuous_interval_bij | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-6iyfm_ba/build.log (exit status -15); /data/not | [Line 156](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_continuous_on_interval_bij | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-zjobqf_2/build.log (exit status -15); /data/not | [Line 157](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_fashoda | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-x6sassx9/build.log (exit status -15); /data/not | [Line 158](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_fashoda_interlace | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-lqlzugu9/build.log (exit status -15); /data/not | [Line 159](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_in_interval_interval_bij | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-lh6m6gil/build.log (exit status -15); /data/not | [Line 160](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_fashoda_unit_path | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-_88p3sxw/build.log (exit status -15); /data/not | [Line 161](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_infnorm_eq_1_2 | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-w_s4vrba/build.log (exit status -15); /data/not | [Line 162](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_infnorm_2 | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-icf_icoa/build.log (exit status -15); /data/not | [Line 163](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_infnorm_eq_1_imp | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-muikxlvm/build.log (exit status -15); /data/not | [Line 164](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_interval_bij_affine | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-3gq0hggf/build.log (exit status -15); /data/not | [Line 165](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_interval_bij_bij | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-jyt6lcpe/build.log (exit status -15); /data/not | [Line 166](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_segment_horizontal | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-2jmz1wjv/build.log (exit status -15); /data/not | [Line 167](checks.jsonl) |
| context_hol-most-match_Fashoda_Theorem_segment_vertical | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-tolir8qq/build.log (exit status -15); /data/not | [Line 168](checks.jsonl) |
| context_hol-most-match_Great_Picard_Casorati_Weierstrass | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-nj2mkeuk/build.log (exit status -15); /data/not | [Line 169](checks.jsonl) |
| context_hol-most-match_Great_Picard_Hurwitz_injective | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-vjqbwywo/build.log (exit status -15); /data/not | [Line 170](checks.jsonl) |
| context_hol-most-match_Great_Picard_Hurwitz_no_zeros | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-d8erwqep/build.log (exit status -15); /data/not | [Line 171](checks.jsonl) |
| context_hol-most-match_Great_Picard_Landau_Picard | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-e_yosrds/build.log (exit status -15); /data/not | [Line 172](checks.jsonl) |
| context_hol-most-match_Great_Picard_Montel | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-q0lwvval/build.log (exit status -15); /data/not | [Line 173](checks.jsonl) |
| context_hol-most-match_Great_Picard_Schottky | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-k97oe5si/build.log (exit status -15); /data/not | [Line 174](checks.jsonl) |
| context_hol-most-match_Great_Picard_great_Picard_alt | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-bff_xzl4/build.log (exit status -15); /data/not | [Line 175](checks.jsonl) |
| context_hol-most-match_Great_Picard_great_Picard_infinite | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-l2j9qeu9/build.log (exit status -15); /data/not | [Line 176](checks.jsonl) |
| context_hol-most-match_Great_Picard_holomorphic_involution_point | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-14tent2p/build.log (exit status -15); /data/not | [Line 177](checks.jsonl) |
| context_hol-most-match_Great_Picard_holomorphic_periodic_fixpoint | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-jeqwuhbo/build.log (exit status -15); /data/not | [Line 178](checks.jsonl) |
| context_hol-most-match_Improper_Integral_absolutely_integrable_improper | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-yvg43iww/build.log (exit status -15); /data/not | [Line 179](checks.jsonl) |
| context_hol-most-match_Improper_Integral_bounded_equiintegral_over_thin_tagged_partial_division | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-dr9br4lx/build.log (exit status -15); /data/not | [Line 180](checks.jsonl) |
| context_hol-most-match_Improper_Integral_bounded_integrals_over_subintervals | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-_anzbex4/build.log (exit status -15); /data/not | [Line 181](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_add | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-8r0rjdl9/build.log (exit status -15); /data/not | [Line 182](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_halfspace_restrictions_gt | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ixunlc9v/build.log (exit status -15); /data/not | [Line 183](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_halfspace_restrictions_ge | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-vi3xu12_/build.log (exit status -15); /data/not | [Line 184](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_cmul | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-nilr1g6t/build.log (exit status -15); /data/not | [Line 185](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_halfspace_restrictions_le | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-dd8066u9/build.log (exit status -15); /data/not | [Line 186](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_limit | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-knrdm2nn/build.log (exit status -15); /data/not | [Line 187](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_on_null | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-1ua9tiec/build.log (exit status -15); /data/not | [Line 188](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_reflect | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-cyxl6fbl/build.log (exit status -15); /data/not | [Line 189](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_closed_interval_restrictions | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-m3v6k9dd/build.log (exit status -15); /data/not | [Line 190](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_sum | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-odwletaq/build.log (exit status -15); /data/not | [Line 191](checks.jsonl) |
| context_hol-most-match_Improper_Integral_indefinite_integral_uniformly_continuous | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-p1g18t7y/build.log (exit status -15); /data/not | [Line 192](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_halfspace_restrictions_lt | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ge73ix8q/build.log (exit status -15); /data/not | [Line 193](checks.jsonl) |
| context_hol-most-match_Improper_Integral_equiintegrable_on_sing | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-a2vl2iit/build.log (exit status -15); /data/not | [Line 194](checks.jsonl) |
| context_hol-most-match_Improper_Integral_sum_content_area_over_thin_division | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-qsz97dcr/build.log (exit status -15); /data/not | [Line 195](checks.jsonl) |
| context_hol-most-match_Improper_Integral_second_mean_value_theorem_full | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-s452tkgt/build.log (exit status -15); /data/not | [Line 196](checks.jsonl) |
| context_hol-most-match_Improper_Integral_second_mean_value_theorem | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-qlnc4s22/build.log (exit status -15); /data/not | [Line 197](checks.jsonl) |
| context_hol-most-match_Improper_Integral_indefinite_integral_continuous | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-p2ijnfxc/build.log (exit status -15); /data/not | [Line 198](checks.jsonl) |
| context_hol-most-match_Polytope_Krein_Milman_polytope | context | pass |  | [Line 199](checks.jsonl) |
| context_hol-most-match_Polytope_Krein_Milman | context | pass |  | [Line 200](checks.jsonl) |
| context_hol-most-match_Polytope_Krein_Milman_Minkowski | context | pass |  | [Line 201](checks.jsonl) |
| context_hol-most-match_Polytope_aff_dim_simplex | context | pass |  | [Line 202](checks.jsonl) |
| context_hol-most-match_Polytope_affine_imp_polyhedron | context | pass |  | [Line 203](checks.jsonl) |
| context_hol-most-match_Polytope_closed_conic_hull_strong | context | pass |  | [Line 204](checks.jsonl) |
| context_hol-most-match_Polytope_cell_complex_subdivision_exists | context | pass |  | [Line 205](checks.jsonl) |
| context_hol-most-match_Polytope_exposed_face_of | context | pass |  | [Line 206](checks.jsonl) |
| context_hol-most-match_Polytope_empty_face_of | context | pass |  | [Line 207](checks.jsonl) |
| context_hol-most-match_Polytope_empty_exposed_face_of | context | pass |  | [Line 208](checks.jsonl) |
| context_hol-most-match_Polytope_exposed_face_of_parallel | context | pass |  | [Line 209](checks.jsonl) |
| context_hol-most-match_Polytope_closed_convex_cone_hull | context | pass |  | [Line 210](checks.jsonl) |
| context_hol-most-match_Polytope_exposed_face_of_polyhedron | context | pass |  | [Line 211](checks.jsonl) |
| context_hol-most-match_Polytope_edge_of_imp_subset | context | pass |  | [Line 212](checks.jsonl) |
| context_hol-most-match_Polytope_exposed_face_of_Inter | context | pass |  | [Line 213](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_empty | context | fail | NativeFailure: native worker produced no structured result (exit status 137); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-memvdr7v/build.log Running DSP_Jo | [Line 214](checks.jsonl) |
| context_hol-most-match_Polytope_exposed_face_of_refl | context | fail | NativeFailure: native worker produced no structured result (exit status 137); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-7m_iklgv/build.log Running DSP_Jo | [Line 215](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_polyhedron_subset_explicit | context | fail | NativeFailure: native worker produced no structured result (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-eu4lbx1e/build.log Running DSP_Job_ | [Line 216](checks.jsonl) |
| context_hol-most-match_Polytope_exposed_face_of_refl_eq | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-eh05cbqp/build.log (exit status -15); /data/not | [Line 217](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_stillconvex | context | pass |  | [Line 218](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_conic | context | pass |  | [Line 219](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_convex_hull | context | pass |  | [Line 220](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_not_in_interior | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-ouz07_3u/build.log (exit status -15); /data/not | [Line 221](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_convex_hull_2 | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-uq5sxqtq/build.log (exit status -15); /data/not | [Line 222](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_convex_hull_convex_independent | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-7zamnxxa/build.log (exit status -15); /data/not | [Line 223](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_convex_hull_eq | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-gccxv0iw/build.log (exit status -15); /data/not | [Line 224](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_segment | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-yvip0ksf/build.log (exit status -15); /data/not | [Line 225](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_face | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-kk39i_xp/build.log (exit status -15); /data/not | [Line 226](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_Inter | context | pass |  | [Line 227](checks.jsonl) |
| context_hol-most-match_Polytope_exposed_face_of_sums | context | pass |  | [Line 228](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_translation_eq | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-t4ufumf0/build.log (exit status -15); /data/not | [Line 229](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_exists_convex | context | pass |  | [Line 230](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_convex_hull_affine_independent | context | pass |  | [Line 231](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_points_of_convex_hull_eq | context | pass |  | [Line 232](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_point_of_convex_hull_insert | context | pass |  | [Line 233](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_points_of_convex_hull | context | pass |  | [Line 234](checks.jsonl) |
| context_hol-most-match_Polytope_extreme_points_of_translation | context | pass |  | [Line 235](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_aff_dim_lt | context | pass |  | [Line 236](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_convex_hull_insert_eq | context | pass |  | [Line 237](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_conic | context | pass |  | [Line 238](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_affine_trivial | context | pass |  | [Line 239](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_imp_subset | context | pass |  | [Line 240](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_imp_convex | context | pass |  | [Line 241](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_convex_hull_subset | context | pass |  | [Line 242](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_linear_image | context | pass |  | [Line 243](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_polyhedron | context | pass |  | [Line 244](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_affine_eq | context | pass |  | [Line 245](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_empty | context | pass |  | [Line 246](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_eq | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-e2alihf9/build.log (exit status -15); /data/not | [Line 247](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_polyhedron_explicit | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-54t26w2k/build.log (exit status -15); /data/not | [Line 248](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_polyhedron_subset_facet | context | pass |  | [Line 249](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_disjoint_interior | context | pass |  | [Line 250](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_imp_closed | context | pass |  | [Line 251](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_imp_compact | context | pass |  | [Line 252](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_face | context | pass |  | [Line 253](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_convex_hull_affine_independent | context | pass |  | [Line 254](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_halfspace_ge | context | pass |  | [Line 255](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_subset | context | pass |  | [Line 256](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_convex_hulls | context | pass |  | [Line 257](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_refl_eq | context | pass |  | [Line 258](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_convex_hull_insert | context | pass |  | [Line 259](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_slice | context | pass |  | [Line 260](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_halfspace_le | context | pass |  | [Line 261](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_refl | context | pass |  | [Line 262](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_polytope_polytope | context | pass |  | [Line 263](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_polyhedron_polyhedron | context | pass |  | [Line 264](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_trans | context | pass |  | [Line 265](checks.jsonl) |
| context_hol-most-match_Polytope_faces_of_linear_image | context | pass |  | [Line 266](checks.jsonl) |
| context_hol-most-match_Polytope_faces_of_translation | context | pass |  | [Line 267](checks.jsonl) |
| context_hol-most-match_Polytope_face_of_translation_eq | context | pass |  | [Line 268](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_empty | context | pass |  | [Line 269](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_convex_hull_affine_independent_alt | context | pass |  | [Line 270](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_convex_hull_affine_independent | context | pass |  | [Line 271](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_halfspace_ge | context | pass |  | [Line 272](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_halfspace_le | context | pass |  | [Line 273](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_imp_subset | context | pass |  | [Line 274](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_imp_face_of | context | pass |  | [Line 275](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_imp_polyhedron | context | fail | NativeFailure: native worker produced no structured result (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-agy10gt0/build.log Running DSP_Job_ | [Line 276](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_polyhedron_explicit | context | pass |  | [Line 277](checks.jsonl) |
| context_hol-most-match_Polytope_finite_polyhedron_exposed_faces | context | pass |  | [Line 278](checks.jsonl) |
| context_hol-most-match_Polytope_fine_triangular_subdivision_of_cell_complex | context | pass |  | [Line 279](checks.jsonl) |
| context_hol-most-match_Polytope_finite_polyhedron_faces | context | pass |  | [Line 280](checks.jsonl) |
| context_hol-most-match_Polytope_finite_polytope_faces | context | pass |  | [Line 281](checks.jsonl) |
| context_hol-most-match_Polytope_fine_simplicial_subdivision_of_cell_complex | context | pass |  | [Line 282](checks.jsonl) |
| context_hol-most-match_Polytope_facet_of_polyhedron | context | pass |  | [Line 283](checks.jsonl) |
| context_hol-most-match_Polytope_finite_polyhedron_facets | context | pass |  | [Line 284](checks.jsonl) |
| context_hol-most-match_Polytope_finite_polyhedron_extreme_points | context | pass |  | [Line 285](checks.jsonl) |
| context_hol-most-match_Polytope_hyperplane_facet_of_halfspace_le | context | pass |  | [Line 286](checks.jsonl) |
| context_hol-most-match_Polytope_interior_of_triangle | context | pass |  | [Line 287](checks.jsonl) |
| context_hol-most-match_Polytope_inside_of_triangle | context | pass |  | [Line 288](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_Inter | context | pass |  | [Line 289](checks.jsonl) |
| context_hol-most-match_Polytope_frontier_of_convex_hull | context | pass |  | [Line 290](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_affine_hull | context | pass |  | [Line 291](checks.jsonl) |
| context_hol-most-match_Polytope_finite_polytope_facets | context | pass |  | [Line 292](checks.jsonl) |
| context_hol-most-match_Polytope_hyperplane_face_of_halfspace_ge | context | pass |  | [Line 293](checks.jsonl) |
| context_hol-most-match_Polytope_hyperplane_facet_of_halfspace_ge | context | pass |  | [Line 294](checks.jsonl) |
| context_hol-most-match_Polytope_hyperplane_face_of_halfspace_le | context | pass |  | [Line 295](checks.jsonl) |
| context_hol-most-match_Polytope_frontier_of_triangle | context | pass |  | [Line 296](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_UNIV | context | pass |  | [Line 297](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_convex_cone_hull | context | pass |  | [Line 298](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_convex_hull | context | pass |  | [Line 299](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_halfspace_le | context | pass |  | [Line 300](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_empty | context | pass |  | [Line 301](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_conic_hull_polytope | context | pass |  | [Line 302](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_hyperplane | context | pass |  | [Line 303](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_convex_cone_hull_polytope | context | pass |  | [Line 304](checks.jsonl) |
| context_hol-most-match_Product_Groups_finite_product_group | context | pass |  | [Line 305](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_halfspace_ge | context | pass |  | [Line 306](checks.jsonl) |
| context_hol-most-match_Product_Groups_product_group | context | pass |  | [Line 307](checks.jsonl) |
| context_hol-most-match_Product_Groups_product_group_subgroup_generated | context | pass |  | [Line 308](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_eq_finite_faces | context | pass |  | [Line 309](checks.jsonl) |
| context_hol-most-match_Product_Groups_sum_group_subgroup_generated | context | pass |  | [Line 310](checks.jsonl) |
| context_hol-most-match_Product_Groups_subgroup_sum_group | context | pass |  | [Line 311](checks.jsonl) |
| context_hol-most-match_Product_Groups_trivial_product_group | context | pass |  | [Line 312](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_empty | context | pass |  | [Line 313](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_eq_finite_exposed_faces | context | pass |  | [Line 314](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_imp_closed | context | pass |  | [Line 315](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_scaling | context | pass |  | [Line 316](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_interval | context | pass |  | [Line 317](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_negations | context | pass |  | [Line 318](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_imp_convex | context | pass |  | [Line 319](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_linear_image | context | pass |  | [Line 320](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_imp_convex | context | pass |  | [Line 321](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_eq_bounded_polyhedron | context | pass |  | [Line 322](checks.jsonl) |
| context_hol-most-match_Polytope_polyhedron_linear_image_eq | context | pass |  | [Line 323](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_functions_form_skolemize | context | pass |  | [Line 324](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_facet_exists | context | pass |  | [Line 325](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_imp_compact | context | pass |  | [Line 326](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_imp_bounded | context | pass |  | [Line 327](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_lowdim_imp_simplex | context | pass |  | [Line 328](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_holds_skolem1 | context | pass |  | [Line 329](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_imp_closed | context | pass |  | [Line 330](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_skolem_qfree | context | pass |  | [Line 331](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_convex_hull | context | pass |  | [Line 332](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_interval | context | pass |  | [Line 333](checks.jsonl) |
| context_hol-most-match_Polytope_segment_face_of | context | pass |  | [Line 334](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_skolem_satisfiable | context | pass |  | [Line 335](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_skomod1_works | context | pass |  | [Line 336](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_skomod_interpretation | context | pass |  | [Line 337](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_skolemize_satisfiable | context | pass |  | [Line 338](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_translation_eq | context | pass |  | [Line 339](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_convex_hull | context | pass |  | [Line 340](checks.jsonl) |
| context_hol-most-match_Polytope_polytope_sing | context | pass |  | [Line 341](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_specialize_language | context | pass |  | [Line 342](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_skomod_works | context | pass |  | [Line 343](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_specialize_qfree | context | pass |  | [Line 344](checks.jsonl) |
| context_hol-most-match_Skolem_Normal_Form_specialize_satisfies | context | pass |  | [Line 345](checks.jsonl) |
| context_hol-most-match_Polytope_simplex | context | pass |  | [Line 346](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_imp_polytope | context | pass |  | [Line 347](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_empty | context | pass |  | [Line 348](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_imp_polyhedron | context | pass |  | [Line 349](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_dim_ge | context | pass |  | [Line 350](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_insert_dimplus1 | context | pass |  | [Line 351](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_segment_cases | context | pass |  | [Line 352](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_segment | context | pass |  | [Line 353](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_minus_1 | context | pass |  | [Line 354](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_sing | context | pass |  | [Line 355](checks.jsonl) |
| context_hol-most-match_Polytope_simplicial_subdivision_of_cell_complex | context | pass |  | [Line 356](checks.jsonl) |
| context_hol-most-match_Polytope_simplex_zero | context | pass |  | [Line 357](checks.jsonl) |
| context_hol-most-match_Polytope_simplicial_subdivision_of_cell_complex_lowdim | context | pass |  | [Line 358](checks.jsonl) |
| context_hol-most-match_Polytope_subset_of_face_of | context | pass |  | [Line 359](checks.jsonl) |
| context_hol-most-match_Polytope_subset_of_face_of_affine_hull | context | pass |  | [Line 360](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_Vitali_covering_lemma_balls | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-egm7vlug/build.log (exit status -15); /data/not | [Line 361](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_Vitali_covering_lemma_cballs | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-wg6zhb7_/build.log (exit status -15); /data/not | [Line 362](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_Vitali_covering_lemma_cballs_balls | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-0mtlw69f/build.log (exit status -15); /data/not | [Line 363](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_Vitali_covering_theorem_balls | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-p7i3jiac/build.log (exit status -15); /data/not | [Line 364](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_Vitali_covering_theorem_cballs | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-8vcakbbz/build.log (exit status -15); /data/not | [Line 365](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_lambda_add_Galois | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-4l0_miea/build.log (exit status -15); /data/not | [Line 366](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_lambda_swap_Galois | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-dchk9xmi/build.log (exit status -15); /data/not | [Line 367](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_negligible_eq_zero_density | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-uj692f_z/build.log (exit status -15); /data/not | [Line 368](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_negligible_eq_zero_density_alt | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-zej1igd4/build.log (exit status -15); /data/not | [Line 369](checks.jsonl) |
| context_hol-most-match_Vitali_Covering_Theorem_stretch_Galois | context | fail | NativeFailure: native worker startup deadline exceeded; inspect /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a/work/context-tpc8p0eh/build.log (exit status -15); /data/not | [Line 370](checks.jsonl) |

## Unavailable context

0 selected contexts are unavailable; they remain in the candidate count.

| Target | Reason | Details |
| --- | --- | --- |

Overall OK evaluates the backend and available contexts; it does not claim unavailable contexts passed.
An entirely unavailable selection cannot pass.

## Resumed contexts

31 context passes were reused from a previous report after identity checks.
Setup and backend controls were rerun. Reused rows retain provenance in report.json and checks.jsonl.

## Context scheduling

New checks completed: 322/322; batch wall time: 6329.822 s; completed checks/minute: 3.052.
Overlap excludes unfinished jobs; it is not CPU utilization or serial speedup.

Expected negative controls pass only for their specific expected rejection.
Dataset failures do not turn into backend successes or disappear from the denominator.
Representative contexts do not establish readiness for every target; use --all-targets for that scope.

Push the compact report files in this directory. Full runtime artifacts are retained locally at: /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T030137Z-650c526a
