(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Cardinality of Equivalence Relations\<close>

theory Card_Equiv_Relations
imports
  Card_Partitions.Card_Partitions
  Bell_Numbers_Spivey.Bell_Numbers
begin

subsection \<open>Bijection between Equivalence Relations and Set Partitions\<close>

subsubsection \<open>Possibly Interesting Theorem for @{theory HOL.Equiv_Relations}\<close>

text \<open>This theorem was historically useful in this theory, but
is now after some proof refactoring not needed here anymore.
Possibly it is an interesting fact about equivalence relations, though.
\<close>

lemma equiv_quotient_eq_quotient_on_UNIV:
  assumes "equiv A R"
  shows "A // R = (UNIV // R) - {{}}"
  by sorry

subsubsection \<open>Dedicated Facts for Bijection Proof\<close>

(* TODO: rename to fit Disjoint_Sets' naming scheme and move to Disjoint_Sets *)
lemma equiv_relation_of_partition_of:
  assumes "equiv A R"
  shows "{(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X} = R"
  by sorry

subsubsection \<open>Bijection Proof\<close>

lemma bij_betw_partition_of:
  "bij_betw (\<lambda>R. A // R) {R. equiv A R} {P. partition_on A P}"
  by sorry

lemma bij_betw_partition_of_equiv_with_k_classes:
  "bij_betw (\<lambda>R. A // R) {R. equiv A R \<and> card (A // R) = k} {P. partition_on A P \<and> card P = k}"
  by sorry

subsection \<open>Finiteness of Equivalence Relations\<close>

lemma finite_equiv:
  assumes "finite A"
  shows "finite {R. equiv A R}"
  by sorry

subsection \<open>Cardinality of Equivalence Relations\<close>

theorem card_equiv_rel_eq_card_partitions:
  "card {R. equiv A R} = card {P. partition_on A P}"
  by sorry

corollary card_equiv_rel_eq_Bell:
  assumes "finite A"
  shows "card {R. equiv A R} = Bell (card A)"
  by sorry

corollary card_equiv_rel_eq_sum_Stirling:
  assumes "finite A"
  shows "card {R. equiv A R} = sum (Stirling (card A)) {..card A}"
  by sorry

theorem card_equiv_k_classes_eq_card_partitions_k_parts:
  "card {R. equiv A R \<and> card (A // R) = k} = card {P. partition_on A P \<and> card P = k}"
  by sorry

corollary
  assumes "finite A"
  shows "card {R. equiv A R \<and> card (A // R) = k} = Stirling (card A) k"
  by sorry

end
