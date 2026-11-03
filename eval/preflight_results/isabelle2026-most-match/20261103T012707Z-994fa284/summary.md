# Isabelle2026 lab preflight

Status: **running**; overall OK: **False**.
Backend OK: **True**; available dataset checks OK: **True**.

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
| context_hol-most-match_Bumping_unbumpform | context | pass |  | [Line 18](checks.jsonl) |
| context_hol-most-match_Bumping_bumpform | context | pass |  | [Line 19](checks.jsonl) |
| context_hol-most-match_Bumping_unbumpterm | context | pass |  | [Line 20](checks.jsonl) |
| context_hol-most-match_Bumping_bumpform_interpretation | context | pass |  | [Line 21](checks.jsonl) |
| context_hol-most-match_Bumping_num_of_form_inj | context | pass |  | [Line 22](checks.jsonl) |
| context_hol-most-match_Bumping_numlist_num_of_term | context | pass |  | [Line 23](checks.jsonl) |
| context_hol-most-match_Bumping_bumpterm | context | pass |  | [Line 24](checks.jsonl) |
| context_hol-most-match_Bumping_functions_form_bumpform | context | pass |  | [Line 25](checks.jsonl) |
| context_hol-most-match_Bumping_num_of_term_inj | context | pass |  | [Line 26](checks.jsonl) |
| context_hol-most-match_Canonical_Models_valuation_exists | context | pass |  | [Line 27](checks.jsonl) |
| context_hol-most-match_Canonical_Models_interpretation_canon_of_prop | context | pass |  | [Line 28](checks.jsonl) |
| context_hol-most-match_Canonical_Models_fol_valid_imp_prop_valid | context | pass |  | [Line 29](checks.jsonl) |
| context_hol-most-match_Canonical_Models_prop_valid_imp_fol_valid | context | pass |  | [Line 30](checks.jsonl) |
| context_hol-most-match_Canonical_Models_satisfies_instances | context | pass |  | [Line 31](checks.jsonl) |
| context_hol-most-match_Canonical_Models_canon | context | pass |  | [Line 32](checks.jsonl) |
| context_hol-most-match_Canonical_Models_holds_itlist_exists | context | pass |  | [Line 33](checks.jsonl) |
| context_hol-most-match_Canonical_Models_interpretation_restrictlanguage | context | pass |  | [Line 34](checks.jsonl) |
| context_hol-most-match_Canonical_Models_lowmod_holds | context | pass |  | [Line 35](checks.jsonl) |
| context_hol-most-match_Canonical_Models_holds_canon_of_prop_general | context | pass |  | [Line 36](checks.jsonl) |
| context_hol-most-match_Canonical_Models_interpretation_extendlanguage | context | pass |  | [Line 37](checks.jsonl) |
| context_hol-most-match_Canonical_Models_compact_canon_qfree | context | pass |  | [Line 38](checks.jsonl) |
| context_hol-most-match_Canonical_Models_finite_subset_skolem | context | pass |  | [Line 39](checks.jsonl) |
| context_hol-most-match_Canonical_Models_holds_canon_of_prop | context | pass |  | [Line 40](checks.jsonl) |
| context_hol-most-match_Canonical_Models_compact_ls | context | pass |  | [Line 41](checks.jsonl) |
| context_hol-most-match_Canonical_Models_lowmod_termval | context | pass |  | [Line 42](checks.jsonl) |
| context_hol-most-match_Canonical_Models_satisfies_psatisfies | context | pass |  | [Line 43](checks.jsonl) |
| context_hol-most-match_Canonical_Models_lowmod_dom_empty | context | pass |  | [Line 44](checks.jsonl) |
| context_hol-most-match_Canonical_Models_finite_subset_instance | context | pass |  | [Line 45](checks.jsonl) |
| context_hol-most-match_Canonical_Models_uniformity | context | pass |  | [Line 46](checks.jsonl) |
| context_hol-most-match_Canonical_Models_canonical_canon_of_prop | context | pass |  | [Line 47](checks.jsonl) |
| context_hol-most-match_Canonical_Models_psatisfies_instances | context | pass |  | [Line 48](checks.jsonl) |

## Unavailable context

0 selected contexts are unavailable; they remain in the candidate count.

| Target | Reason | Details |
| --- | --- | --- |

Overall OK evaluates the backend and available contexts; it does not claim unavailable contexts passed.
An entirely unavailable selection cannot pass.

Expected negative controls pass only for their specific expected rejection.
Dataset failures do not turn into backend successes or disappear from the denominator.
Representative contexts do not establish readiness for every target; use --all-targets for that scope.

Push the compact report files in this directory. Full runtime artifacts are retained locally at: /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-most-match/20261103T012707Z-994fa284
