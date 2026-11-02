(* Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Derangements\<close>

theory Derangements
imports
  Complex_Main
  "HOL-Combinatorics.Permutations"
begin
declare [[quick_and_dirty = true]]


subsection \<open>Preliminaries\<close>

subsubsection \<open>Additions to @{theory HOL.Finite_Set} Theory\<close>

lemma card_product_dependent:
  assumes "finite S" "\<forall>x \<in> S. finite (T x)"
  shows "card {(x, y). x \<in> S \<and> y \<in> T x} = (\<Sum>x \<in> S. card (T x))"
  
  sorry



subsubsection \<open>Additions to @{theory "HOL-Combinatorics.Permutations"} Theory\<close>

lemma permutes_imp_bij':
  assumes "p permutes S"
  shows "bij p"
  
  sorry


lemma permutesE:
  assumes "p permutes S"
  obtains "bij p" "\<forall>x. x \<notin> S \<longrightarrow> p x = x"
  
  sorry


lemma bij_imp_permutes':
  assumes "bij p" "\<forall>x. x \<notin> A \<longrightarrow> p x = x"
  shows  "p permutes A"
  
  sorry



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma permutes_swap:
  assumes "p permutes S"
  shows "Fun.swap x y p permutes (insert x (insert y S))"
  
  