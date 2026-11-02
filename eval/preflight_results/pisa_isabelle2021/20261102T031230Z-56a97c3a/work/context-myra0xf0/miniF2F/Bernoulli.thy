(*  
  File:       Bernoulli.thy
  Author:     Lukas Bulwahn <lukas.bulwahn-at-gmail.com> 
  Author:     Manuel Eberl <manuel@pruvisto.org> 
*)
section \<open>Bernoulli numbers\<close>

theory Bernoulli
imports Complex_Main
begin
declare [[quick_and_dirty = true]]


subsection \<open>Preliminaries\<close>
  
lemma power_numeral_reduce: "a ^ numeral n = a * a ^ pred_numeral n"
  
  sorry


lemma fact_diff_Suc: "n < Suc m \<Longrightarrow> fact (Suc m - n) = of_nat (Suc m - n) * fact (m - n)"
  
  sorry


lemma of_nat_binomial_Suc:
  assumes "k \<le> n"
  shows   "(of_nat (Suc n choose k) :: 'a :: field_char_0) = 
             of_nat (Suc n) / of_nat (Suc n - k) * of_nat (n choose k)"
  
  sorry



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma integrals_eq:
  assumes "f 0 = g 0"
  assumes "\<And> x. ((\<lambda>x. f x - g x) has_real_derivative 0) (at x)"
  shows "f x = g x"
  
  