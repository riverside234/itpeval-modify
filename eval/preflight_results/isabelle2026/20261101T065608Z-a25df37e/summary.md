# Isabelle2026 lab preflight

Status: **complete**; overall OK: **False**.
Backend OK: **False**; selected dataset checks OK: **False**.

Scope: `longest_prefix_per_topic_plus_sentinels`; 32 contexts.

| Check | Domain | Status | Failure | Details |
| --- | --- | --- | --- | --- |
| input_selection | selection | pass |  | [JSON](details/001-input_selection.json) |
| metadata | setup | pass |  | [JSON](details/002-metadata.json) |
| infrastructure | setup | pass |  | [JSON](details/003-infrastructure.json) |
| native_fixture | backend | fail | native acceptance fixture failed (exit status 1); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/fixture/build.log Running DSP_Acceptance_97b3eaabfb28470c8d5927acc6c66139 ... DSP_Acce | [JSON](details/004-native_fixture.json) |
| explicit_draft | backend | pass |  | [JSON](details/005-explicit_draft.json) |
| explicit_direct | backend | pass |  | [JSON](details/006-explicit_direct.json) |
| hammer_configured | backend | pass |  | [JSON](details/007-hammer_configured.json) |
| hammer_native_tactic | backend | pass |  | [JSON](details/008-hammer_native_tactic.json) |
| hammer_external_e | backend | pass |  | [JSON](details/009-hammer_external_e.json) |
| using_reconstruction | backend | pass |  | [JSON](details/010-using_reconstruction.json) |
| using_reconstruction_comments | backend | pass |  | [JSON](details/011-using_reconstruction_comments.json) |
| nested_gaps_symbols | backend | pass |  | [JSON](details/012-nested_gaps_symbols.json) |
| multiple_subgoals | backend | pass |  | [JSON](details/013-multiple_subgoals.json) |
| partial_goal_rejected | backend | pass |  | [JSON](details/014-partial_goal_rejected.json) |
| zero_goal_done | backend | pass |  | [JSON](details/015-zero_goal_done.json) |
| local_blocks | backend | pass |  | [JSON](details/016-local_blocks.json) |
| local_definitions | backend | pass |  | [JSON](details/017-local_definitions.json) |
| subgoal_block | backend | pass |  | [JSON](details/018-subgoal_block.json) |
| invalid_method | backend | pass |  | [JSON](details/019-invalid_method.json) |
| admission_rejected | backend | pass |  | [JSON](details/020-admission_rejected.json) |
| quoted_ml_rejected | backend | pass |  | [JSON](details/021-quoted_ml_rejected.json) |
| quick_and_dirty_override_rejected | backend | pass |  | [JSON](details/022-quick_and_dirty_override_rejected.json) |
| smt_oracle_override_rejected | backend | pass |  | [JSON](details/023-smt_oracle_override_rejected.json) |
| self_reference_rejected | backend | pass |  | [JSON](details/024-self_reference_rejected.json) |
| later_fact_rejected | backend | pass |  | [JSON](details/025-later_fact_rejected.json) |
| unavailable_prover_rejected | backend | pass |  | [JSON](details/026-unavailable_prover_rejected.json) |
| saved_proof_replay | backend | pass |  | [JSON](details/027-saved_proof_replay.json) |
| corrupted_replay_rejected | backend | pass |  | [JSON](details/028-corrupted_replay_rejected.json) |
| inherited_theory_search | backend | pass |  | [JSON](details/029-inherited_theory_search.json) |
| inherited_theory_replay | backend | pass |  | [JSON](details/030-inherited_theory_replay.json) |
| circle_average_configured | dataset_proof | pass |  | [JSON](details/031-circle_average_configured.json) |
| circle_average_native_metis | dataset_proof | pass |  | [JSON](details/032-circle_average_native_metis.json) |
| ballot_explicit | dataset_proof | pass |  | [JSON](details/033-ballot_explicit.json) |
| context_babel-formal_circle_average_circleAverage_center_independent | context | pass |  | [JSON](details/034-context_babel-formal_circle_average_circleAverage_center_independent.json) |
| context_babel-formal_circle_average_circleAverage_shift_commute | context | pass |  | [JSON](details/035-context_babel-formal_circle_average_circleAverage_shift_commute.json) |
| context_babel-formal_comp_commute_commute_transport_right_id | context | pass |  | [JSON](details/036-context_babel-formal_comp_commute_commute_transport_right_id.json) |
| context_babel-formal_galois_gal_isSolvable_tower_split | context | pass |  | [JSON](details/037-context_babel-formal_galois_gal_isSolvable_tower_split.json) |
| context_babel-formal_graph_paths_cycle_refl | context | pass |  | [JSON](details/038-context_babel-formal_graph_paths_cycle_refl.json) |
| context_babel-formal_group_stabilizer_conjugate_orbit | context | pass |  | [JSON](details/039-context_babel-formal_group_stabilizer_conjugate_orbit.json) |
| context_babel-formal_ideals_sum_isIdeal | context | pass |  | [JSON](details/040-context_babel-formal_ideals_sum_isIdeal.json) |
| context_babel-formal_inner_product_parallelogram | context | pass |  | [JSON](details/041-context_babel-formal_inner_product_parallelogram.json) |
| context_babel-formal_integral_comp_neg_Iic_sigma_abs_bound | context | pass |  | [JSON](details/042-context_babel-formal_integral_comp_neg_Iic_sigma_abs_bound.json) |
| context_babel-formal_lattice_like_sup_absorption | context | pass |  | [JSON](details/043-context_babel-formal_lattice_like_sup_absorption.json) |
| context_babel-formal_limits_uniqueness_limit_unique | context | pass |  | [JSON](details/044-context_babel-formal_limits_uniqueness_limit_unique.json) |
| context_babel-formal_linear_map_im_smul | context | pass |  | [JSON](details/045-context_babel-formal_linear_map_im_smul.json) |
| context_babel-formal_polynomial_degree_factorisation | context | pass |  | [JSON](details/046-context_babel-formal_polynomial_degree_factorisation.json) |
| context_babel-formal_probability_prob_bigUnion_disjoint_zero | context | pass |  | [JSON](details/047-context_babel-formal_probability_prob_bigUnion_disjoint_zero.json) |
| context_babel-formal_set_algebra_de_morgan_inter | context | pass |  | [JSON](details/048-context_babel-formal_set_algebra_de_morgan_inter.json) |
| context_babel-formal_supinf_limit_inv_succ | context | pass |  | [JSON](details/049-context_babel-formal_supinf_limit_inv_succ.json) |
| context_babel-formal_zero_le_one_elem_matrix_le_antisymm | context | pass |  | [JSON](details/050-context_babel-formal_zero_le_one_elem_matrix_le_antisymm.json) |
| context_hundred-theorems_011_the_infinitude_of_primes_bezout_prime | context | fail | NativeFailure: native worker produced no structured result (exit status 2); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/work/context-i1hj4bqh/build.log *** Cannot load theory file  | [JSON](details/051-context_hundred-theorems_011_the_infinitude_of_primes_bezout_prime.json) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integrable_continuous | context | pass |  | [JSON](details/052-context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integrable_continuous.json) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_rsum_bound | context | pass |  | [JSON](details/053-context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_rsum_bound.json) |
| context_hundred-theorems_027_sum_of_the_angles_of_a_triangle_Pythagoras | context | fail | NativeFailure: native worker produced no structured result (exit status 2); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/work/context-ficcvewp/build.log *** Cannot load theory file  | [JSON](details/054-context_hundred-theorems_027_sum_of_the_angles_of_a_triangle_Pythagoras.json) |
| context_hundred-theorems_030_the_ballot_problem_all_countings | context | pass |  | [JSON](details/055-context_hundred-theorems_030_the_ballot_problem_all_countings.json) |
| context_hundred-theorems_030_the_ballot_problem_valid_countings | context | pass |  | [JSON](details/056-context_hundred-theorems_030_the_ballot_problem_valid_countings.json) |
| context_hundred-theorems_049_the_cayley-hamilton_theorem_Cayley_Hamilton | context | fail | NativeFailure: native worker produced no structured result (exit status 2); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/work/context-ezay0p9w/build.log *** Cannot load theory file  | [JSON](details/057-context_hundred-theorems_049_the_cayley-hamilton_theorem_Cayley_Hamilton.json) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_image | context | fail | NativeFailure: native worker produced no structured result (exit status 2); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/work/context-8417i2wp/build.log *** Cannot load theory file  | [JSON](details/058-context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_image.json) |
| context_hundred-theorems_065_isosceles_triangle_theorem_isosceles_triangle_converse | context | fail | NativeFailure: native worker produced no structured result (exit status 2); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/work/context-b0hbe2ic/build.log *** Cannot load theory file  | [JSON](details/059-context_hundred-theorems_065_isosceles_triangle_theorem_isosceles_triangle_converse.json) |
| context_hundred-theorems_077_sum_of_kth_powers_sum_of_powers | context | pass |  | [JSON](details/060-context_hundred-theorems_077_sum_of_kth_powers_sum_of_powers.json) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_dot_norm | context | pass |  | [JSON](details/061-context_hundred-theorems_078_the_cauchy-schwarz_inequality_dot_norm.json) |
| context_hundred-theorems_088_derangements_formula_permutes_swap | context | pass |  | [JSON](details/062-context_hundred-theorems_088_derangements_formula_permutes_swap.json) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_squarefree_decomp | context | fail | NativeFailure: native worker produced no structured result (exit status 2); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/work/context-__big8wd/build.log *** Cannot load theory file  | [JSON](details/063-context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_squarefree_decomp.json) |
| context_hundred-theorems_095_ptolemy_s_theorem_ptolemy | context | pass |  | [JSON](details/064-context_hundred-theorems_095_ptolemy_s_theorem_ptolemy.json) |
| context_hundred-theorems_098_bertrand_s_postulate_bertrand | context | fail | NativeFailure: native worker produced no structured result (exit status 2); /data/not_backed_up/yxu209/itpeval-modify/eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/work/context-c3mdntwc/build.log *** Bad imports session "Pra | [JSON](details/065-context_hundred-theorems_098_bertrand_s_postulate_bertrand.json) |

Expected negative controls pass only for their specific expected rejection.
Dataset failures do not turn into backend successes or disappear from the denominator.
Representative contexts do not establish readiness for every target; use --all-targets for that scope.

Push this complete run directory, including diagnostics.zip, after the command finishes.
