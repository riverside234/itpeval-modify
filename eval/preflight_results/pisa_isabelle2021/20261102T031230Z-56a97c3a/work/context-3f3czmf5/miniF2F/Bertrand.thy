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


lemma ln_fact: "ln (fact n) = (\<Sum>d=1..n. ln d)"
  
  sorry


lemma overpower_lemma:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f a \<le> g a"
  assumes "\<And>x. a \<le> x \<Longrightarrow> ((\<lambda>x. g x - f x) has_real_derivative (d x)) (at x)"
  assumes "\<And>x. a \<le> x \<Longrightarrow> d x \<ge> 0"
  assumes "a \<le> x"
  shows   "f x \<le> g x"
  
  sorry



subsection \<open>Preliminary definitions\<close>

definition primepow_even :: "nat \<Rightarrow> bool" where
  "primepow_even q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k))"

definition primepow_odd :: "nat \<Rightarrow> bool" where
  "primepow_odd q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k+1))"

abbreviation (input) isprimedivisor :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isprimedivisor q p \<equiv> prime p \<and> p dvd q"

definition pre_mangoldt :: "nat \<Rightarrow> nat" where
  "pre_mangoldt d = (if primepow d then aprimedivisor d else 1)"

definition mangoldt_even :: "nat \<Rightarrow> real" where
  "mangoldt_even d = (if primepow_even d then ln (real (aprimedivisor d)) else 0)"

definition mangoldt_odd :: "nat \<Rightarrow> real" where
  "mangoldt_odd d = (if primepow_odd d then ln (real (aprimedivisor d)) else 0)"

definition mangoldt_1 :: "nat \<Rightarrow> real" where
  "mangoldt_1 d = (if prime d then ln d else 0)"

definition psi :: "nat \<Rightarrow> real" where
  "psi n = (\<Sum>d=1..n. mangoldt d)"

definition psi_even :: "nat \<Rightarrow> real" where
  "psi_even n = (\<Sum>d=1..n. mangoldt_even d)"

definition psi_odd :: "nat \<Rightarrow> real" where
  "psi_odd n = (\<Sum>d=1..n. mangoldt_odd d)"

abbreviation (input) psi_even_2 :: "nat \<Rightarrow> real" where
  "psi_even_2 n \<equiv> (\<Sum>d=2..n. mangoldt_even d)"

abbreviation (input) psi_odd_2 :: "nat \<Rightarrow> real" where
  "psi_odd_2 n \<equiv> (\<Sum>d=2..n. mangoldt_odd d)"

definition theta :: "nat \<Rightarrow> real" where
  "theta n = (\<Sum>p=1..n. if prime p then ln (real p) else 0)"

subsection \<open>Properties of prime powers\<close>  

lemma primepow_even_imp_primepow:
  assumes "primepow_even n"
  shows   "primepow n"
  
  sorry


lemma primepow_odd_imp_primepow:
  assumes "primepow_odd n"
  shows   "primepow n"
  
  sorry


lemma primepow_odd_altdef:
  "primepow_odd n \<longleftrightarrow>
     primepow n \<and> odd (multiplicity (aprimedivisor n) n) \<and> multiplicity (aprimedivisor n) n > 1"
  
  sorry


lemma primepow_even_altdef:
  "primepow_even n \<longleftrightarrow> primepow n \<and> even (multiplicity (aprimedivisor n) n)"
  
  sorry


lemma primepow_odd_mult:
  assumes "d > Suc 0"
  shows   "primepow_odd (aprimedivisor d * d) \<longleftrightarrow> primepow_even d"
  
  sorry


lemma pre_mangoldt_primepow:
  assumes "primepow n" "aprimedivisor n = p"
  shows   "pre_mangoldt n = p"
  
  sorry


lemma pre_mangoldt_notprimepow:
  assumes "\<not>primepow n"
  shows   "pre_mangoldt n = 1"
  
  sorry


lemma primepow_cases:
  "primepow d \<longleftrightarrow>
     (  primepow_even d \<and> \<not> primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and>   primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and> \<not> primepow_odd d \<and>   prime d)"
  
  sorry



subsection \<open>Deriving a recurrence for the psi function\<close>
  
lemma ln_fact_bounds:
  assumes "n > 0"
  shows "abs(ln (fact n) - n * ln n + n) \<le> 1 + ln n"
  
  sorry


lemma ln_fact_diff_bounds:
  "abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2) \<le> 4 * ln (if n = 0 then 1 else n) + 3"
  
  sorry

  
lemma ln_primefact:
  assumes "n \<noteq> (0::nat)"
  shows   "ln n = (\<Sum>d=1..n. if primepow d \<and> d dvd n then ln (aprimedivisor d) else 0)" 
          (is "?lhs = ?rhs")
  
  sorry


context
begin

private lemma divisors:
  fixes x d::nat
  assumes "x \<in> {1..n}"
  assumes "d dvd x"
  shows "\<exists>k\<in>{1..n div d}. x = d * k"

  sorry


lemma ln_fact_conv_mangoldt: "ln (fact n) = (\<Sum>d=1..n. mangoldt d * floor (n / d))"
  
  sorry


end

context
begin

private lemma div_2_mult_2_bds:
  fixes n d :: nat
  assumes "d > 0"
  shows "0 \<le> \<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor>" "\<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor> \<le> 1"

  sorry


private lemma n_div_d_eq_1: "d \<in> {n div 2 + 1..n} \<Longrightarrow> \<lfloor>real n / real d\<rfloor> = 1"
  
  sorry

    

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma psi_bounds_ln_fact:
  shows "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n"
        "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
  
  