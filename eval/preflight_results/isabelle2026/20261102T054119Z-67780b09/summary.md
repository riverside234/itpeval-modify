# Compacted preflight report

Status: **complete**; overall OK: **False**.

Existing check outcomes and cohort counts are preserved in report.json.
Details are in checks.jsonl; bounded log excerpts are in logs.jsonl.

Full original run, including diagnostics.zip, retained locally: `/data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight_archives/isabelle2026/20261102T054119Z-67780b09-11535e5fa449474792a8fed93ab21526`.

| Check | Domain | Status | Error |
| --- | --- | --- | --- |
| input_selection | selection | pass |  |
| metadata | setup | pass |  |
| infrastructure | setup | pass |  |
| native_fixture | backend | pass |  |
| explicit_draft | backend | pass |  |
| explicit_direct | backend | pass |  |
| hammer_configured | backend | pass |  |
| hammer_native_tactic | backend | pass |  |
| hammer_external_e | backend | pass |  |
| using_reconstruction | backend | pass |  |
| using_reconstruction_comments | backend | pass |  |
| nested_gaps_symbols | backend | pass |  |
| multiple_subgoals | backend | pass |  |
| partial_goal_rejected | backend | pass |  |
| zero_goal_done | backend | pass |  |
| local_blocks | backend | pass |  |
| local_definitions | backend | pass |  |
| subgoal_block | backend | pass |  |
| invalid_method | backend | pass |  |
| admission_rejected | backend | pass |  |
| quoted_ml_rejected | backend | pass |  |
| quick_and_dirty_override_rejected | backend | pass |  |
| smt_oracle_override_rejected | backend | pass |  |
| self_reference_rejected | backend | pass |  |
| later_fact_rejected | backend | pass |  |
| unavailable_prover_rejected | backend | pass |  |
| inherited_theory_search | backend | pass |  |
| circle_average_configured | dataset_proof | pass |  |
| circle_average_native_metis | dataset_proof | pass |  |
| ballot_explicit | dataset_proof | pass |  |
| context_babel-formal_circle_average_circleAverage_add | context | pass |  |
| context_babel-formal_circle_average_circleAverage_add_assoc | context | pass |  |
| context_babel-formal_circle_average_circleAverage_add_const | context | pass |  |
| context_babel-formal_circle_average_circleAverage_center_comm | context | pass |  |
| context_babel-formal_circle_average_circleAverage_center_eq | context | pass |  |
| context_babel-formal_circle_average_circleAverage_center_independent | context | pass |  |
| context_babel-formal_circle_average_circleAverage_comm_add | context | pass |  |
| context_babel-formal_circle_average_circleAverage_const | context | pass |  |
| context_babel-formal_circle_average_circleAverage_fun_add | context | pass |  |
| context_babel-formal_circle_average_circleAverage_idempotent | context | pass |  |
| context_babel-formal_circle_average_circleAverage_linear | context | pass |  |
| context_babel-formal_circle_average_circleAverage_of_zero_integral | context | pass |  |
| context_babel-formal_circle_average_circleAverage_shift | context | pass |  |
| context_babel-formal_circle_average_circleAverage_shift_commute | context | pass |  |
| context_babel-formal_circle_average_circleAverage_zero | context | pass |  |
| context_babel-formal_circle_average_circleMap_add | context | pass |  |
| context_babel-formal_circle_average_circleMap_zero | context | pass |  |
| context_babel-formal_comp_commute_commute_congr | context | pass |  |
| context_babel-formal_comp_commute_commute_refl | context | pass |  |
| context_babel-formal_comp_commute_commute_symm | context | pass |  |
| context_babel-formal_comp_commute_commute_transport_left_id | context | pass |  |
| context_babel-formal_comp_commute_commute_transport_right_id | context | pass |  |
| context_babel-formal_comp_commute_commute_with_id_l | context | pass |  |
| context_babel-formal_comp_commute_commute_with_id_r | context | pass |  |
| context_babel-formal_comp_commute_comp_assoc | context | pass |  |
| context_babel-formal_comp_commute_comp_id_l | context | pass |  |
| context_babel-formal_comp_commute_comp_id_r | context | pass |  |
| context_babel-formal_galois_add_cancel_l | context | pass |  |
| context_babel-formal_galois_add_cancel_r | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_double_tower | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_map_after_split | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_map_poly | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_map_poly_comp | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_mutual_split | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_of_split | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_quadruple_tower | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_split_tower | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_three_step_map | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_tower | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_tower_split | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_triple_tower | context | pass |  |
| context_babel-formal_galois_gal_isSolvable_two_step_map | context | pass |  |
| context_babel-formal_galois_inv_involutive | context | pass |  |
| context_babel-formal_galois_inv_unique | context | pass |  |
| context_babel-formal_galois_mul_cancel_l | context | pass |  |
| context_babel-formal_galois_mul_cancel_r | context | pass |  |
| context_babel-formal_galois_mul_inv_r | context | pass |  |
| context_babel-formal_galois_mul_one_r | context | pass |  |
| context_babel-formal_galois_zero_add | context | pass |  |
| context_babel-formal_graph_paths_concat3 | context | pass |  |
| context_babel-formal_graph_paths_concat_edge_left | context | pass |  |
| context_babel-formal_graph_paths_concat_edge_right | context | pass |  |
| context_babel-formal_graph_paths_cycle_refl | context | pass |  |
| context_babel-formal_graph_paths_edge_path | context | pass |  |
| context_babel-formal_graph_paths_path_refl | context | pass |  |
| context_babel-formal_graph_paths_path_trans | context | pass |  |
| context_babel-formal_graph_paths_reverse_in_Erev | context | pass |  |
| context_babel-formal_graph_paths_reverse_path | context | pass |  |
| context_babel-formal_group_act_inv | context | pass |  |
| context_babel-formal_group_act_inv_r | context | pass |  |
| context_babel-formal_group_inv_eq_of_mul_eq_one | context | pass |  |
| context_babel-formal_group_inv_inv | context | pass |  |
| context_babel-formal_group_inv_mul | context | pass |  |
| context_babel-formal_group_mul_left_cancel | context | pass |  |
| context_babel-formal_group_mul_right_cancel | context | pass |  |
| context_babel-formal_group_mul_rotate' | context | pass |  |
| context_babel-formal_group_orbit_partition | context | pass |  |
| context_babel-formal_group_orbit_refl | context | pass |  |
| context_babel-formal_group_orbit_sym | context | pass |  |
| context_babel-formal_group_orbit_trans | context | pass |  |
| context_babel-formal_group_stabilizer_conjugate | context | pass |  |
| context_babel-formal_group_stabilizer_conjugate_orbit | context | pass |  |
| context_babel-formal_group_stabilizer_inv | context | pass |  |
| context_babel-formal_group_stabilizer_mul | context | pass |  |
| context_babel-formal_group_stabilizer_one | context | pass |  |
| context_babel-formal_ideals_inter_isIdeal | context | pass |  |
| context_babel-formal_ideals_sum_isIdeal | context | pass |  |
| context_babel-formal_inner_product_ip_add_add | context | pass |  |
| context_babel-formal_inner_product_ip_neg_left | context | pass |  |
| context_babel-formal_inner_product_ip_neg_right | context | pass |  |
| context_babel-formal_inner_product_ip_sub_sub | context | pass |  |
| context_babel-formal_inner_product_parallelogram | context | pass |  |
| context_babel-formal_inner_product_pythagoras | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_integral_neg | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_integral_sub | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_lt_irrefl | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_lt_trans_strict | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_preimage_comp | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_preimage_inter | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_preimage_neg_Iic | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_preimage_neg_Ioi | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_preimage_union | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_sigma_abs_bound | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_sigma_bilinear | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_sigma_empty | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_sigma_le_monotone | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_sigma_nonneg | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_sigma_preimage_neg_Ioi | context | pass |  |
| context_babel-formal_integral_comp_neg_Iic_sigma_split | context | pass |  |
| context_babel-formal_lattice_like_inf_absorption | context | pass |  |
| context_babel-formal_lattice_like_inf_assoc | context | pass |  |
| context_babel-formal_lattice_like_inf_comm | context | pass |  |
| context_babel-formal_lattice_like_sup_absorption | context | pass |  |
| context_babel-formal_lattice_like_sup_assoc | context | pass |  |
| context_babel-formal_lattice_like_sup_comm | context | pass |  |
| context_babel-formal_limits_uniqueness_abs_sub_triangle | context | pass |  |
| context_babel-formal_limits_uniqueness_limit_unique | context | pass |  |
| context_babel-formal_linear_map_im_add | context | pass |  |
| context_babel-formal_linear_map_im_smul | context | pass |  |
| context_babel-formal_linear_map_ker_add | context | pass |  |
| context_babel-formal_linear_map_ker_smul | context | pass |  |
| context_babel-formal_polynomial_X_minus_nonzero | context | pass |  |
| context_babel-formal_polynomial_deg_poly_of_roots | context | pass |  |
| context_babel-formal_polynomial_degree_factorisation | context | pass |  |
| context_babel-formal_polynomial_eval_X_minus | context | pass |  |
| context_babel-formal_polynomial_mynat_add_O_left | context | pass |  |
| context_babel-formal_polynomial_mynat_add_S_left | context | pass |  |
| context_babel-formal_polynomial_mynat_add_S_r | context | pass |  |
| context_babel-formal_polynomial_mynat_add_comm | context | pass |  |
| context_babel-formal_polynomial_mynat_add_zero_r | context | pass |  |
| context_babel-formal_polynomial_mynat_succ_le_succ | context | pass |  |
| context_babel-formal_polynomial_mynat_zero_le | context | pass |  |
| context_babel-formal_polynomial_poly_of_roots_nonzero | context | pass |  |
| context_babel-formal_polynomial_root_factor | context | pass |  |
| context_babel-formal_polynomial_root_factor_list | context | pass |  |
| context_babel-formal_polynomial_root_of_product | context | pass |  |
| context_babel-formal_polynomial_root_scale_constant | context | pass |  |
| context_babel-formal_polynomial_root_transfer | context | pass |  |
| context_babel-formal_polynomial_roots_le_degree | context | pass |  |
| context_babel-formal_polynomial_sub_eq_zero_l | context | pass |  |
| context_babel-formal_probability_bayes_symm | context | pass |  |
| context_babel-formal_probability_indep_compl_both | context | pass |  |
| context_babel-formal_probability_indep_compl_left | context | pass |  |
| context_babel-formal_probability_indep_compl_right | context | pass |  |
| context_babel-formal_probability_indep_symm | context | pass |  |
| context_babel-formal_probability_law_total_prob | context | pass |  |
| context_babel-formal_probability_prob_bigUnion_disjoint | context | pass |  |
| context_babel-formal_probability_prob_bigUnion_disjoint_zero | context | pass |  |
| context_babel-formal_probability_prob_diff | context | pass |  |
| context_babel-formal_probability_prob_union_comm | context | pass |  |
| context_babel-formal_probability_prob_union_idem | context | pass |  |
| context_babel-formal_probability_prob_union_indep | context | pass |  |
| context_babel-formal_set_algebra_de_morgan_inter | context | pass |  |
| context_babel-formal_set_algebra_de_morgan_union | context | pass |  |
| context_babel-formal_set_algebra_inter_distrib_left | context | pass |  |
| context_babel-formal_set_algebra_inter_distrib_right | context | pass |  |
| context_babel-formal_supinf_add_sub_cancel_r | context | pass |  |
| context_babel-formal_supinf_inf_lt | context | pass |  |
| context_babel-formal_supinf_inv_succ_pos | context | pass |  |
| context_babel-formal_supinf_le_lim | context | pass |  |
| context_babel-formal_supinf_le_of_le_add_eps | context | pass |  |
| context_babel-formal_supinf_limit_inv_succ | context | pass |  |
| context_babel-formal_supinf_rabs_pos | context | pass |  |
| context_babel-formal_supinf_unique_max | context | pass |  |
| context_babel-formal_zero_le_one_elem_Zero_le_One_matrix | context | pass |  |
| context_babel-formal_zero_le_one_elem_matrix_eq_le | context | pass |  |
| context_babel-formal_zero_le_one_elem_matrix_eq_refl | context | pass |  |
| context_babel-formal_zero_le_one_elem_matrix_eq_sym | context | pass |  |
| context_babel-formal_zero_le_one_elem_matrix_eq_trans | context | pass |  |
| context_babel-formal_zero_le_one_elem_matrix_le_antisymm | context | pass |  |
| context_babel-formal_zero_le_one_elem_matrix_le_refl | context | pass |  |
| context_babel-formal_zero_le_one_elem_matrix_le_trans | context | pass |  |
| context_babel-formal_zero_le_one_elem_zero_le_one_elem | context | pass |  |
| context_hundred-theorems_011_the_infinitude_of_primes_bezout_prime | context | pass |  |
| context_hundred-theorems_011_the_infinitude_of_primes_chinese_remainder | context | pass |  |
| context_hundred-theorems_011_the_infinitude_of_primes_coprime_bezout_strong | context | pass |  |
| context_hundred-theorems_011_the_infinitude_of_primes_primes_infinite | context | pass |  |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integrable_Cauchy | context | pass |  |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integrable_continuous | context | pass |  |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integral_add | context | pass |  |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integral_cmul | context | pass |  |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integral_null | context | pass |  |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_rsum_bound | context | pass |  |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_rsum_diff_bound | context | pass |  |
| context_hundred-theorems_027_sum_of_the_angles_of_a_triangle_Pythagoras | context | pass |  |
| context_hundred-theorems_030_the_ballot_problem_all_countings | context | pass |  |
| context_hundred-theorems_030_the_ballot_problem_valid_countings | context | pass |  |
| context_hundred-theorems_049_the_cayley-hamilton_theorem_Cayley_Hamilton | context | pass |  |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_Diff_UNIV | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_Diff_empty | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_Diff_insert | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_UNIV_not_empty | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_disjoint_insert | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_empty_Diff | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_empty_not_UNIV | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_insert_Diff | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_insert_UNIV | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_insert_subset | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_not_psubset_empty | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_empty | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_image | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_insert | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_mono | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_psubset_subset_trans | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_psubset_trans | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_UNIV | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_antisym | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_empty | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_insert | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_psubset_trans | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_refl | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_trans | context | unavailable_context | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. |
| context_hundred-theorems_065_isosceles_triangle_theorem_isosceles_triangle_converse | context | pass |  |
| context_hundred-theorems_077_sum_of_kth_powers_diff_bernpoly | context | pass |  |
| context_hundred-theorems_077_sum_of_kth_powers_integrals_eq | context | pass |  |
| context_hundred-theorems_077_sum_of_kth_powers_sum_of_powers | context | pass |  |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_dot_norm | context | pass |  |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_cauchy_schwarz | context | fail | NativeFailure: target or later fact leaked into the input context: dot_square_norm |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_eq | context | fail | NativeFailure: target or later fact leaked into the input context: dot_square_norm |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_eq_1 | context | fail | NativeFailure: target or later fact leaked into the input context: dot_square_norm |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_eq_square | context | pass |  |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_ge_square | context | pass |  |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_gt_square | context | pass |  |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_le | context | fail | NativeFailure: target or later fact leaked into the input context: dot_square_norm |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_le_square | context | pass |  |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_lt | context | fail | NativeFailure: target or later fact leaked into the input context: dot_square_norm |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_lt_square | context | pass |  |
| context_hundred-theorems_088_derangements_formula_permutes_swap | context | pass |  |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order_decomp | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order_divides | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order_root | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_IVT_neg | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_IVT_pos | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_MVT | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_add | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_diff | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_differentiable | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_roots_finite | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_squarefree_decomp | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_squarefree_decomp_order | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_zero | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_rsquarefree_roots | context | fail | NativeFailure: failed command: lift_definition zero_poly :: "'a poly" is "\<lambda>_. 0" |
| context_hundred-theorems_095_ptolemy_s_theorem_ptolemy | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_bertrand | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_fact_expand_psi | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_fact_psi_bound_2_3 | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_fact_psi_bound_even | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_fact_psi_bound_odd | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_floor_half_interval | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_ln_fact | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_ln_fact_bounds | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_ln_fact_diff_bounds | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_ln_primefact | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_overpower_lemma | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_induct | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_ln_fact | context | pass |  |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_sustained | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_sustained_induct | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_double_lemma | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_expansion_cutoff | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_mono | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_pos | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_residues_compare | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_residues_compare_2 | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_split | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_sqrt | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_theta | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_ubound_3_2 | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_psi_ubound_log | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_sum_expand_lemma | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
| context_hundred-theorems_098_bertrand_s_postulate_theta_double_lemma | context | fail | NativeFailure: failed command: ML_file \<open>bertrand.ML\<close> |
