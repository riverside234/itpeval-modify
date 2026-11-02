(*
  File:     Bertrand.thy
  Authors:  Julian Biendarra, Manuel Eberl <manuel@pruvisto.org>, Larry Paulson

  A proof of Bertrand's postulate (based on John Harrison's HOL Light proof).
  Uses reflection and the approximation tactic.
*)
theory Bertrand
  imports 
    Complex_Main
    "HOL-Number_Theory.Number_Theory"
    "HOL-Library.Discrete_Functions"
    "HOL-Decision_Procs.Approximation_Bounds"
    "HOL-Library.Code_Target_Numeral"
    Pratt_Certificate.Pratt_Certificate
begin
declare [[quick_and_dirty = true]]


subsection \<open>Auxiliary facts\<close>
 
lemma ln_2_le: "ln 2 \<le> 355 / (512 :: real)"
  
  sorry


lemma ln_2_ge: "ln 2 \<ge> (5677 / 8192 :: real)"
  
  sorry


lemma ln_2_ge': "ln (2 :: real) \<ge> 2/3" and ln_2_le': "ln (2 :: real) \<le> 16/23"
  
  sorry


lemma of_nat_ge_1_iff: "(of_nat x :: 'a :: linordered_semidom) \<ge> 1 \<longleftrightarrow> x \<ge> 1"
  
  sorry

  
lemma floor_conv_div_nat:
  "of_int (floor (real m / real n)) = real (m div n)"
  
  sorry


lemma frac_conv_mod_nat:
  "frac (real m / real n) = real (m mod n) / real n"
  
  sorry


lemma of_nat_prod_mset: "prod_mset (image_mset of_nat A) = of_nat (prod_mset A)"
  
  sorry


lemma prod_mset_pos: "(\<And>x :: 'a :: linordered_semidom. x \<in># A \<Longrightarrow> x > 0) \<Longrightarrow> prod_mset A > 0"
  
  sorry


lemma ln_msetprod:
  assumes "\<And>x. x \<in>#I \<Longrightarrow> x > 0"
  shows "(\<Sum>p::nat\<in>#I. ln p) = ln (\<Prod>p\<in>#I. p)"
  
  sorry



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma ln_fact: "ln (fact n) = (\<Sum>d=1..n. ln d)"
  
  