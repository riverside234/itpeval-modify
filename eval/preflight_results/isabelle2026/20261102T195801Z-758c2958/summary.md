# Isabelle2026 lab preflight

Status: **complete**; overall OK: **True**.
Backend OK: **True**; available dataset checks OK: **True**.

Scope: `all_targets`; 262 contexts.

| Check | Domain | Status | Failure | Details |
| --- | --- | --- | --- | --- |
| input_selection | selection | pass |  | [Line 1](checks.jsonl) |
| metadata | setup | pass |  | [Line 2](checks.jsonl) |
| infrastructure | setup | pass |  | [Line 3](checks.jsonl) |
| native_fixture | backend | pass |  | [Line 4](checks.jsonl) |
| explicit_draft | backend | pass |  | [Line 5](checks.jsonl) |
| explicit_direct | backend | pass |  | [Line 6](checks.jsonl) |
| hammer_configured | backend | pass |  | [Line 7](checks.jsonl) |
| hammer_native_tactic | backend | pass |  | [Line 8](checks.jsonl) |
| hammer_external_e | backend | pass |  | [Line 9](checks.jsonl) |
| using_reconstruction | backend | pass |  | [Line 10](checks.jsonl) |
| using_reconstruction_comments | backend | pass |  | [Line 11](checks.jsonl) |
| nested_gaps_symbols | backend | pass |  | [Line 12](checks.jsonl) |
| multiple_subgoals | backend | pass |  | [Line 13](checks.jsonl) |
| partial_goal_rejected | backend | pass |  | [Line 14](checks.jsonl) |
| zero_goal_done | backend | pass |  | [Line 15](checks.jsonl) |
| local_blocks | backend | pass |  | [Line 16](checks.jsonl) |
| local_definitions | backend | pass |  | [Line 17](checks.jsonl) |
| subgoal_block | backend | pass |  | [Line 18](checks.jsonl) |
| invalid_method | backend | pass |  | [Line 19](checks.jsonl) |
| admission_rejected | backend | pass |  | [Line 20](checks.jsonl) |
| quoted_ml_rejected | backend | pass |  | [Line 21](checks.jsonl) |
| quick_and_dirty_override_rejected | backend | pass |  | [Line 22](checks.jsonl) |
| smt_oracle_override_rejected | backend | pass |  | [Line 23](checks.jsonl) |
| self_reference_rejected | backend | pass |  | [Line 24](checks.jsonl) |
| later_fact_rejected | backend | pass |  | [Line 25](checks.jsonl) |
| unavailable_prover_rejected | backend | pass |  | [Line 26](checks.jsonl) |
| inherited_theory_search | backend | pass |  | [Line 27](checks.jsonl) |
| circle_average_configured | dataset_proof | pass |  | [Line 28](checks.jsonl) |
| circle_average_native_metis | dataset_proof | pass |  | [Line 29](checks.jsonl) |
| ballot_explicit | dataset_proof | pass |  | [Line 30](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_add | context | pass |  | [Line 31](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_add_assoc | context | pass |  | [Line 32](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_add_const | context | pass |  | [Line 33](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_center_comm | context | pass |  | [Line 34](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_center_eq | context | pass |  | [Line 35](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_center_independent | context | pass |  | [Line 36](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_comm_add | context | pass |  | [Line 37](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_const | context | pass |  | [Line 38](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_fun_add | context | pass |  | [Line 39](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_idempotent | context | pass |  | [Line 40](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_linear | context | pass |  | [Line 41](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_of_zero_integral | context | pass |  | [Line 42](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_shift | context | pass |  | [Line 43](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_shift_commute | context | pass |  | [Line 44](checks.jsonl) |
| context_babel-formal_circle_average_circleAverage_zero | context | pass |  | [Line 45](checks.jsonl) |
| context_babel-formal_circle_average_circleMap_add | context | pass |  | [Line 46](checks.jsonl) |
| context_babel-formal_circle_average_circleMap_zero | context | pass |  | [Line 47](checks.jsonl) |
| context_babel-formal_comp_commute_commute_congr | context | pass |  | [Line 48](checks.jsonl) |
| context_babel-formal_comp_commute_commute_refl | context | pass |  | [Line 49](checks.jsonl) |
| context_babel-formal_comp_commute_commute_symm | context | pass |  | [Line 50](checks.jsonl) |
| context_babel-formal_comp_commute_commute_transport_left_id | context | pass |  | [Line 51](checks.jsonl) |
| context_babel-formal_comp_commute_commute_transport_right_id | context | pass |  | [Line 52](checks.jsonl) |
| context_babel-formal_comp_commute_commute_with_id_l | context | pass |  | [Line 53](checks.jsonl) |
| context_babel-formal_comp_commute_commute_with_id_r | context | pass |  | [Line 54](checks.jsonl) |
| context_babel-formal_comp_commute_comp_assoc | context | pass |  | [Line 55](checks.jsonl) |
| context_babel-formal_comp_commute_comp_id_l | context | pass |  | [Line 56](checks.jsonl) |
| context_babel-formal_comp_commute_comp_id_r | context | pass |  | [Line 57](checks.jsonl) |
| context_babel-formal_galois_add_cancel_l | context | pass |  | [Line 58](checks.jsonl) |
| context_babel-formal_galois_add_cancel_r | context | pass |  | [Line 59](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_double_tower | context | pass |  | [Line 60](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_map_after_split | context | pass |  | [Line 61](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_map_poly | context | pass |  | [Line 62](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_map_poly_comp | context | pass |  | [Line 63](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_mutual_split | context | pass |  | [Line 64](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_of_split | context | pass |  | [Line 65](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_quadruple_tower | context | pass |  | [Line 66](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_split_tower | context | pass |  | [Line 67](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_three_step_map | context | pass |  | [Line 68](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_tower | context | pass |  | [Line 69](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_tower_split | context | pass |  | [Line 70](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_triple_tower | context | pass |  | [Line 71](checks.jsonl) |
| context_babel-formal_galois_gal_isSolvable_two_step_map | context | pass |  | [Line 72](checks.jsonl) |
| context_babel-formal_galois_inv_involutive | context | pass |  | [Line 73](checks.jsonl) |
| context_babel-formal_galois_inv_unique | context | pass |  | [Line 74](checks.jsonl) |
| context_babel-formal_galois_mul_cancel_l | context | pass |  | [Line 75](checks.jsonl) |
| context_babel-formal_galois_mul_cancel_r | context | pass |  | [Line 76](checks.jsonl) |
| context_babel-formal_galois_mul_inv_r | context | pass |  | [Line 77](checks.jsonl) |
| context_babel-formal_galois_mul_one_r | context | pass |  | [Line 78](checks.jsonl) |
| context_babel-formal_galois_zero_add | context | pass |  | [Line 79](checks.jsonl) |
| context_babel-formal_graph_paths_concat3 | context | pass |  | [Line 80](checks.jsonl) |
| context_babel-formal_graph_paths_concat_edge_left | context | pass |  | [Line 81](checks.jsonl) |
| context_babel-formal_graph_paths_concat_edge_right | context | pass |  | [Line 82](checks.jsonl) |
| context_babel-formal_graph_paths_cycle_refl | context | pass |  | [Line 83](checks.jsonl) |
| context_babel-formal_graph_paths_edge_path | context | pass |  | [Line 84](checks.jsonl) |
| context_babel-formal_graph_paths_path_refl | context | pass |  | [Line 85](checks.jsonl) |
| context_babel-formal_graph_paths_path_trans | context | pass |  | [Line 86](checks.jsonl) |
| context_babel-formal_graph_paths_reverse_in_Erev | context | pass |  | [Line 87](checks.jsonl) |
| context_babel-formal_graph_paths_reverse_path | context | pass |  | [Line 88](checks.jsonl) |
| context_babel-formal_group_act_inv | context | pass |  | [Line 89](checks.jsonl) |
| context_babel-formal_group_act_inv_r | context | pass |  | [Line 90](checks.jsonl) |
| context_babel-formal_group_inv_eq_of_mul_eq_one | context | pass |  | [Line 91](checks.jsonl) |
| context_babel-formal_group_inv_inv | context | pass |  | [Line 92](checks.jsonl) |
| context_babel-formal_group_inv_mul | context | pass |  | [Line 93](checks.jsonl) |
| context_babel-formal_group_mul_left_cancel | context | pass |  | [Line 94](checks.jsonl) |
| context_babel-formal_group_mul_right_cancel | context | pass |  | [Line 95](checks.jsonl) |
| context_babel-formal_group_mul_rotate' | context | pass |  | [Line 96](checks.jsonl) |
| context_babel-formal_group_orbit_partition | context | pass |  | [Line 97](checks.jsonl) |
| context_babel-formal_group_orbit_refl | context | pass |  | [Line 98](checks.jsonl) |
| context_babel-formal_group_orbit_sym | context | pass |  | [Line 99](checks.jsonl) |
| context_babel-formal_group_orbit_trans | context | pass |  | [Line 100](checks.jsonl) |
| context_babel-formal_group_stabilizer_conjugate | context | pass |  | [Line 101](checks.jsonl) |
| context_babel-formal_group_stabilizer_conjugate_orbit | context | pass |  | [Line 102](checks.jsonl) |
| context_babel-formal_group_stabilizer_inv | context | pass |  | [Line 103](checks.jsonl) |
| context_babel-formal_group_stabilizer_mul | context | pass |  | [Line 104](checks.jsonl) |
| context_babel-formal_group_stabilizer_one | context | pass |  | [Line 105](checks.jsonl) |
| context_babel-formal_ideals_inter_isIdeal | context | pass |  | [Line 106](checks.jsonl) |
| context_babel-formal_ideals_sum_isIdeal | context | pass |  | [Line 107](checks.jsonl) |
| context_babel-formal_inner_product_ip_add_add | context | pass |  | [Line 108](checks.jsonl) |
| context_babel-formal_inner_product_ip_neg_left | context | pass |  | [Line 109](checks.jsonl) |
| context_babel-formal_inner_product_ip_neg_right | context | pass |  | [Line 110](checks.jsonl) |
| context_babel-formal_inner_product_ip_sub_sub | context | pass |  | [Line 111](checks.jsonl) |
| context_babel-formal_inner_product_parallelogram | context | pass |  | [Line 112](checks.jsonl) |
| context_babel-formal_inner_product_pythagoras | context | pass |  | [Line 113](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_integral_neg | context | pass |  | [Line 114](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_integral_sub | context | pass |  | [Line 115](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_lt_irrefl | context | pass |  | [Line 116](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_lt_trans_strict | context | pass |  | [Line 117](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_preimage_comp | context | pass |  | [Line 118](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_preimage_inter | context | pass |  | [Line 119](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_preimage_neg_Iic | context | pass |  | [Line 120](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_preimage_neg_Ioi | context | pass |  | [Line 121](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_preimage_union | context | pass |  | [Line 122](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_sigma_abs_bound | context | pass |  | [Line 123](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_sigma_bilinear | context | pass |  | [Line 124](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_sigma_empty | context | pass |  | [Line 125](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_sigma_le_monotone | context | pass |  | [Line 126](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_sigma_nonneg | context | pass |  | [Line 127](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_sigma_preimage_neg_Ioi | context | pass |  | [Line 128](checks.jsonl) |
| context_babel-formal_integral_comp_neg_Iic_sigma_split | context | pass |  | [Line 129](checks.jsonl) |
| context_babel-formal_lattice_like_inf_absorption | context | pass |  | [Line 130](checks.jsonl) |
| context_babel-formal_lattice_like_inf_assoc | context | pass |  | [Line 131](checks.jsonl) |
| context_babel-formal_lattice_like_inf_comm | context | pass |  | [Line 132](checks.jsonl) |
| context_babel-formal_lattice_like_sup_absorption | context | pass |  | [Line 133](checks.jsonl) |
| context_babel-formal_lattice_like_sup_assoc | context | pass |  | [Line 134](checks.jsonl) |
| context_babel-formal_lattice_like_sup_comm | context | pass |  | [Line 135](checks.jsonl) |
| context_babel-formal_limits_uniqueness_abs_sub_triangle | context | pass |  | [Line 136](checks.jsonl) |
| context_babel-formal_limits_uniqueness_limit_unique | context | pass |  | [Line 137](checks.jsonl) |
| context_babel-formal_linear_map_im_add | context | pass |  | [Line 138](checks.jsonl) |
| context_babel-formal_linear_map_im_smul | context | pass |  | [Line 139](checks.jsonl) |
| context_babel-formal_linear_map_ker_add | context | pass |  | [Line 140](checks.jsonl) |
| context_babel-formal_linear_map_ker_smul | context | pass |  | [Line 141](checks.jsonl) |
| context_babel-formal_polynomial_X_minus_nonzero | context | pass |  | [Line 142](checks.jsonl) |
| context_babel-formal_polynomial_deg_poly_of_roots | context | pass |  | [Line 143](checks.jsonl) |
| context_babel-formal_polynomial_degree_factorisation | context | pass |  | [Line 144](checks.jsonl) |
| context_babel-formal_polynomial_eval_X_minus | context | pass |  | [Line 145](checks.jsonl) |
| context_babel-formal_polynomial_mynat_add_O_left | context | pass |  | [Line 146](checks.jsonl) |
| context_babel-formal_polynomial_mynat_add_S_left | context | pass |  | [Line 147](checks.jsonl) |
| context_babel-formal_polynomial_mynat_add_S_r | context | pass |  | [Line 148](checks.jsonl) |
| context_babel-formal_polynomial_mynat_add_comm | context | pass |  | [Line 149](checks.jsonl) |
| context_babel-formal_polynomial_mynat_add_zero_r | context | pass |  | [Line 150](checks.jsonl) |
| context_babel-formal_polynomial_mynat_succ_le_succ | context | pass |  | [Line 151](checks.jsonl) |
| context_babel-formal_polynomial_mynat_zero_le | context | pass |  | [Line 152](checks.jsonl) |
| context_babel-formal_polynomial_poly_of_roots_nonzero | context | pass |  | [Line 153](checks.jsonl) |
| context_babel-formal_polynomial_root_factor | context | pass |  | [Line 154](checks.jsonl) |
| context_babel-formal_polynomial_root_factor_list | context | pass |  | [Line 155](checks.jsonl) |
| context_babel-formal_polynomial_root_of_product | context | pass |  | [Line 156](checks.jsonl) |
| context_babel-formal_polynomial_root_scale_constant | context | pass |  | [Line 157](checks.jsonl) |
| context_babel-formal_polynomial_root_transfer | context | pass |  | [Line 158](checks.jsonl) |
| context_babel-formal_polynomial_roots_le_degree | context | pass |  | [Line 159](checks.jsonl) |
| context_babel-formal_polynomial_sub_eq_zero_l | context | pass |  | [Line 160](checks.jsonl) |
| context_babel-formal_probability_bayes_symm | context | pass |  | [Line 161](checks.jsonl) |
| context_babel-formal_probability_indep_compl_both | context | pass |  | [Line 162](checks.jsonl) |
| context_babel-formal_probability_indep_compl_left | context | pass |  | [Line 163](checks.jsonl) |
| context_babel-formal_probability_indep_compl_right | context | pass |  | [Line 164](checks.jsonl) |
| context_babel-formal_probability_indep_symm | context | pass |  | [Line 165](checks.jsonl) |
| context_babel-formal_probability_law_total_prob | context | pass |  | [Line 166](checks.jsonl) |
| context_babel-formal_probability_prob_bigUnion_disjoint | context | pass |  | [Line 167](checks.jsonl) |
| context_babel-formal_probability_prob_bigUnion_disjoint_zero | context | pass |  | [Line 168](checks.jsonl) |
| context_babel-formal_probability_prob_diff | context | pass |  | [Line 169](checks.jsonl) |
| context_babel-formal_probability_prob_union_comm | context | pass |  | [Line 170](checks.jsonl) |
| context_babel-formal_probability_prob_union_idem | context | pass |  | [Line 171](checks.jsonl) |
| context_babel-formal_probability_prob_union_indep | context | pass |  | [Line 172](checks.jsonl) |
| context_babel-formal_set_algebra_de_morgan_inter | context | pass |  | [Line 173](checks.jsonl) |
| context_babel-formal_set_algebra_de_morgan_union | context | pass |  | [Line 174](checks.jsonl) |
| context_babel-formal_set_algebra_inter_distrib_left | context | pass |  | [Line 175](checks.jsonl) |
| context_babel-formal_set_algebra_inter_distrib_right | context | pass |  | [Line 176](checks.jsonl) |
| context_babel-formal_supinf_add_sub_cancel_r | context | pass |  | [Line 177](checks.jsonl) |
| context_babel-formal_supinf_inf_lt | context | pass |  | [Line 178](checks.jsonl) |
| context_babel-formal_supinf_inv_succ_pos | context | pass |  | [Line 179](checks.jsonl) |
| context_babel-formal_supinf_le_lim | context | pass |  | [Line 180](checks.jsonl) |
| context_babel-formal_supinf_le_of_le_add_eps | context | pass |  | [Line 181](checks.jsonl) |
| context_babel-formal_supinf_limit_inv_succ | context | pass |  | [Line 182](checks.jsonl) |
| context_babel-formal_supinf_rabs_pos | context | pass |  | [Line 183](checks.jsonl) |
| context_babel-formal_supinf_unique_max | context | pass |  | [Line 184](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_Zero_le_One_matrix | context | pass |  | [Line 185](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_matrix_eq_le | context | pass |  | [Line 186](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_matrix_eq_refl | context | pass |  | [Line 187](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_matrix_eq_sym | context | pass |  | [Line 188](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_matrix_eq_trans | context | pass |  | [Line 189](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_matrix_le_antisymm | context | pass |  | [Line 190](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_matrix_le_refl | context | pass |  | [Line 191](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_matrix_le_trans | context | pass |  | [Line 192](checks.jsonl) |
| context_babel-formal_zero_le_one_elem_zero_le_one_elem | context | pass |  | [Line 193](checks.jsonl) |
| context_hundred-theorems_011_the_infinitude_of_primes_bezout_prime | context | pass |  | [Line 194](checks.jsonl) |
| context_hundred-theorems_011_the_infinitude_of_primes_chinese_remainder | context | pass |  | [Line 195](checks.jsonl) |
| context_hundred-theorems_011_the_infinitude_of_primes_coprime_bezout_strong | context | pass |  | [Line 196](checks.jsonl) |
| context_hundred-theorems_011_the_infinitude_of_primes_primes_infinite | context | pass |  | [Line 197](checks.jsonl) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integrable_Cauchy | context | pass |  | [Line 198](checks.jsonl) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integrable_continuous | context | pass |  | [Line 199](checks.jsonl) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integral_add | context | pass |  | [Line 200](checks.jsonl) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integral_cmul | context | pass |  | [Line 201](checks.jsonl) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_integral_null | context | pass |  | [Line 202](checks.jsonl) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_rsum_bound | context | pass |  | [Line 203](checks.jsonl) |
| context_hundred-theorems_015_the_fundamental_theorem_of_integral_calculus_rsum_diff_bound | context | pass |  | [Line 204](checks.jsonl) |
| context_hundred-theorems_027_sum_of_the_angles_of_a_triangle_Pythagoras | context | pass |  | [Line 205](checks.jsonl) |
| context_hundred-theorems_030_the_ballot_problem_all_countings | context | pass |  | [Line 206](checks.jsonl) |
| context_hundred-theorems_030_the_ballot_problem_valid_countings | context | pass |  | [Line 207](checks.jsonl) |
| context_hundred-theorems_049_the_cayley-hamilton_theorem_Cayley_Hamilton | context | pass |  | [Line 208](checks.jsonl) |
| context_hundred-theorems_065_isosceles_triangle_theorem_isosceles_triangle_converse | context | pass |  | [Line 233](checks.jsonl) |
| context_hundred-theorems_077_sum_of_kth_powers_diff_bernpoly | context | pass |  | [Line 234](checks.jsonl) |
| context_hundred-theorems_077_sum_of_kth_powers_integrals_eq | context | pass |  | [Line 235](checks.jsonl) |
| context_hundred-theorems_077_sum_of_kth_powers_sum_of_powers | context | pass |  | [Line 236](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_dot_norm | context | pass |  | [Line 237](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_cauchy_schwarz | context | pass |  | [Line 238](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_eq | context | pass |  | [Line 239](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_eq_1 | context | pass |  | [Line 240](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_eq_square | context | pass |  | [Line 241](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_ge_square | context | pass |  | [Line 242](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_gt_square | context | pass |  | [Line 243](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_le | context | pass |  | [Line 244](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_le_square | context | pass |  | [Line 245](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_lt | context | pass |  | [Line 246](checks.jsonl) |
| context_hundred-theorems_078_the_cauchy-schwarz_inequality_norm_lt_square | context | pass |  | [Line 247](checks.jsonl) |
| context_hundred-theorems_088_derangements_formula_permutes_swap | context | pass |  | [Line 248](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order | context | pass |  | [Line 249](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order_decomp | context | pass |  | [Line 250](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order_divides | context | pass |  | [Line 251](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_order_root | context | pass |  | [Line 252](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_IVT_neg | context | pass |  | [Line 253](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_IVT_pos | context | pass |  | [Line 254](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_MVT | context | pass |  | [Line 255](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_add | context | pass |  | [Line 256](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_diff | context | pass |  | [Line 257](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_differentiable | context | pass |  | [Line 258](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_roots_finite | context | pass |  | [Line 259](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_squarefree_decomp | context | pass |  | [Line 260](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_squarefree_decomp_order | context | pass |  | [Line 261](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_poly_zero | context | pass |  | [Line 262](checks.jsonl) |
| context_hundred-theorems_089_the_factor_and_remainder_theorems_rsquarefree_roots | context | pass |  | [Line 263](checks.jsonl) |
| context_hundred-theorems_095_ptolemy_s_theorem_ptolemy | context | pass |  | [Line 264](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_bertrand | context | pass |  | [Line 265](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_fact_expand_psi | context | pass |  | [Line 266](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_fact_psi_bound_2_3 | context | pass |  | [Line 267](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_fact_psi_bound_even | context | pass |  | [Line 268](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_fact_psi_bound_odd | context | pass |  | [Line 269](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_floor_half_interval | context | pass |  | [Line 270](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_ln_fact | context | pass |  | [Line 271](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_ln_fact_bounds | context | pass |  | [Line 272](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_ln_fact_diff_bounds | context | pass |  | [Line 273](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_ln_primefact | context | pass |  | [Line 274](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_overpower_lemma | context | pass |  | [Line 275](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_induct | context | pass |  | [Line 276](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_ln_fact | context | pass |  | [Line 277](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_sustained | context | pass |  | [Line 278](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_bounds_sustained_induct | context | pass |  | [Line 279](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_double_lemma | context | pass |  | [Line 280](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_expansion_cutoff | context | pass |  | [Line 281](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_mono | context | pass |  | [Line 282](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_pos | context | pass |  | [Line 283](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_residues_compare | context | pass |  | [Line 284](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_residues_compare_2 | context | pass |  | [Line 285](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_split | context | pass |  | [Line 286](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_sqrt | context | pass |  | [Line 287](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_theta | context | pass |  | [Line 288](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_ubound_3_2 | context | pass |  | [Line 289](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_psi_ubound_log | context | pass |  | [Line 290](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_sum_expand_lemma | context | pass |  | [Line 291](checks.jsonl) |
| context_hundred-theorems_098_bertrand_s_postulate_theta_double_lemma | context | pass |  | [Line 292](checks.jsonl) |

## Unavailable context

24 selected contexts are unavailable; they remain in the candidate count.

| Target | Reason | Details |
| --- | --- | --- |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_Diff_UNIV | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 209](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_Diff_empty | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 210](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_Diff_insert | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 211](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_UNIV_not_empty | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 212](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_disjoint_insert | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 213](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_empty_Diff | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 214](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_empty_not_UNIV | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 215](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_insert_Diff | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 216](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_insert_UNIV | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 217](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_insert_subset | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 218](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_not_psubset_empty | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 219](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_empty | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 220](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_image | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 221](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_insert | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 222](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_pairwise_mono | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 223](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_psubset_subset_trans | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 224](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_psubset_trans | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 225](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_UNIV | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 226](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_antisym | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 227](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_empty | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 228](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_insert | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 229](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_psubset_trans | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 230](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_refl | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 231](checks.jsonl) |
| context_hundred-theorems_052_the_number_of_subsets_of_a_set_subset_trans | Core Set is already inherited by the HOL parent; an isolated target context is unavailable. Installing AFP does not change this restriction. | [Line 232](checks.jsonl) |

Overall OK evaluates the backend and available contexts; it does not claim unavailable contexts passed.
An entirely unavailable selection cannot pass.

Expected negative controls pass only for their specific expected rejection.
Dataset failures do not turn into backend successes or disappear from the denominator.
Representative contexts do not establish readiness for every target; use --all-targets for that scope.

Push the compact report files in this directory. Full runtime artifacts are retained locally at: /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026/20261102T195801Z-758c2958
