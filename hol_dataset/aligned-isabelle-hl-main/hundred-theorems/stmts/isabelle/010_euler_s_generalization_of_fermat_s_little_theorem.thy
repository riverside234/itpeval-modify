(*  Title:      HOL/Number_Theory/Totient.thy
    Author:     Jeremy Avigad
    Author:     Florian Haftmann
    Author:     Manuel Eberl
*)

section \<open>Fundamental facts about Euler's totient function\<close>

theory Totient
imports
  Complex_Main
  "HOL-Computational_Algebra.Primes"
  Cong
begin
  
definition totatives :: "nat \<Rightarrow> nat set" where
  "totatives n = {k \<in> {0<..n}. coprime k n}"

lemma in_totatives_iff: "k \<in> totatives n \<longleftrightarrow> k > 0 \<and> k \<le> n \<and> coprime k n"
  by sorry
  
lemma totatives_code [code]: "totatives n = Set.filter (\<lambda>k. coprime k n) {0<..n}"
  by sorry
  
lemma finite_totatives [simp]: "finite (totatives n)"
  by sorry
    
lemma totatives_subset: "totatives n \<subseteq> {0<..n}"
  by sorry
    
lemma zero_not_in_totatives [simp]: "0 \<notin> totatives n"
  by sorry
    
lemma totatives_le: "x \<in> totatives n \<Longrightarrow> x \<le> n"
  by sorry
    
lemma totatives_less: 
  assumes "x \<in> totatives n" "n > 1"
  shows   "x < n"
  by sorry

lemma totatives_0 [simp]: "totatives 0 = {}"
  by sorry

lemma totatives_1 [simp]: "totatives 1 = {Suc 0}"
  by sorry

lemma totatives_Suc_0 [simp]: "totatives (Suc 0) = {Suc 0}"
  by sorry

lemma one_in_totatives [simp]: "n > 0 \<Longrightarrow> Suc 0 \<in> totatives n"
  by sorry

lemma totatives_eq_empty_iff [simp]: "totatives n = {} \<longleftrightarrow> n = 0"
  by sorry
    
lemma minus_one_in_totatives:
  assumes "n \<ge> 2"
  shows "n - 1 \<in> totatives n"
  by sorry

lemma power_in_totatives:
  assumes "m > 1" "coprime m g"
  shows   "g ^ i mod m \<in> totatives m"
  by sorry

lemma totatives_prime_power_Suc:
  assumes "prime p"
  shows   "totatives (p ^ Suc n) = {0<..p^Suc n} - (\<lambda>m. p * m) ` {0<..p^n}"
  by sorry

lemma totatives_prime: "prime p \<Longrightarrow> totatives p = {0<..<p}"
  by sorry

lemma bij_betw_totatives:
  assumes "m1 > 1" "m2 > 1" "coprime m1 m2"
  shows   "bij_betw (\<lambda>x. (x mod m1, x mod m2)) (totatives (m1 * m2)) 
             (totatives m1 \<times> totatives m2)"
  by sorry

lemma bij_betw_totatives_gcd_eq:
  fixes n d :: nat
  assumes "d dvd n" "n > 0"
  shows   "bij_betw (\<lambda>k. k * d) (totatives (n div d)) {k\<in>{0<..n}. gcd k n = d}"
  by sorry

definition totient :: "nat \<Rightarrow> nat" where
  "totient n = card (totatives n)"
  
primrec totient_naive :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "totient_naive 0 acc n = acc"
| "totient_naive (Suc k) acc n =
     (if coprime (Suc k) n then totient_naive k (acc + 1) n else totient_naive k acc n)"
  
lemma totient_naive:
  "totient_naive k acc n = card {x \<in> {0<..k}. coprime x n} + acc"
  by sorry
  
lemma totient_code_naive [code]: "totient n = totient_naive n 0 n"
  by sorry

lemma totient_le: "totient n \<le> n"
  by sorry
  
lemma totient_less: 
  assumes "n > 1"
  shows "totient n < n"
  by sorry

lemma totient_0 [simp]: "totient 0 = 0"
  by sorry

lemma totient_Suc_0 [simp]: "totient (Suc 0) = Suc 0"
  by sorry

lemma totient_1 [simp]: "totient 1 = Suc 0"
  by sorry

lemma totient_0_iff [simp]: "totient n = 0 \<longleftrightarrow> n = 0"
  by sorry

lemma totient_gt_0_iff [simp]: "totient n > 0 \<longleftrightarrow> n > 0"
  by sorry

lemma totient_gt_1:
  assumes "n > 2"
  shows   "totient n > 1"
  by sorry

lemma card_gcd_eq_totient:
  "n > 0 \<Longrightarrow> d dvd n \<Longrightarrow> card {k\<in>{0<..n}. gcd k n = d} = totient (n div d)"
  by sorry
  
lemma totient_divisor_sum: "(\<Sum>d | d dvd n. totient d) = n"
  by sorry

lemma totient_mult_coprime:
  assumes "coprime m n"
  shows   "totient (m * n) = totient m * totient n"
  by sorry

lemma totient_prime_power_Suc:
  assumes "prime p"
  shows   "totient (p ^ Suc n) = p ^ n * (p - 1)"
  by sorry

lemma totient_prime_power:
  assumes "prime p" "n > 0"
  shows   "totient (p ^ n) = p ^ (n - 1) * (p - 1)"
  by sorry

lemma totient_imp_prime:
  assumes "totient p = p - 1" "p > 0"
  shows   "prime p"
  by sorry
    
lemma totient_prime:
  assumes "prime p"
  shows   "totient p = p - 1"
  by sorry

lemma totient_2 [simp]: "totient 2 = 1"
  and totient_3 [simp]: "totient 3 = 2"
  and totient_5 [simp]: "totient 5 = 4"
  and totient_7 [simp]: "totient 7 = 6"
  by sorry
    
lemma totient_4 [simp]: "totient 4 = 2"
  and totient_8 [simp]: "totient 8 = 4"
  and totient_9 [simp]: "totient 9 = 6"
  by sorry
    
lemma totient_6 [simp]: "totient 6 = 2"
  by sorry

lemma totient_even:
  assumes "n > 2"
  shows   "even (totient n)"
  by sorry

lemma totient_prod_coprime:
  assumes "pairwise coprime (f ` A)" "inj_on f A"
  shows   "totient (prod f A) = (\<Prod>a\<in>A. totient (f a))"
  by sorry

(* TODO Move *)
lemma prime_power_eq_imp_eq:
  fixes p q :: "'a :: factorial_semiring"
  assumes "prime p" "prime q" "m > 0"
  assumes "p ^ m = q ^ n"
  shows   "p = q"
  by sorry

lemma totient_formula1:
  assumes "n > 0"
  shows   "totient n = (\<Prod>p\<in>prime_factors n. p ^ (multiplicity p n - 1) * (p - 1))"
  by sorry

lemma totient_dvd:
  assumes "m dvd n"
  shows   "totient m dvd totient n"
  by sorry
  
lemma totient_dvd_mono:
  assumes "m dvd n" "n > 0"
  shows   "totient m \<le> totient n"
  by sorry

(* TODO Move *)
lemma prime_factors_power: "n > 0 \<Longrightarrow> prime_factors (x ^ n) = prime_factors x"
  by sorry

lemma totient_formula2:
  "real (totient n) = real n * (\<Prod>p\<in>prime_factors n. 1 - 1 / real p)"
  by sorry

lemma totient_gcd: "totient (a * b) * totient (gcd a b) = totient a * totient b * gcd a b"
  by sorry
  
lemma totient_mult: "totient (a * b) = totient a * totient b * gcd a b div totient (gcd a b)"
  by sorry

lemma of_nat_eq_1_iff: "of_nat x = (1 :: 'a :: {semiring_1, semiring_char_0}) \<longleftrightarrow> x = 1"
  by sorry

(* TODO Move *)
lemma odd_imp_coprime_nat:
  assumes "odd (n::nat)"
  shows   "coprime n 2"
  by sorry

lemma totient_double: "totient (2 * n) = (if even n then 2 * totient n else totient n)"
  by sorry

lemma totient_power_Suc: "totient (n ^ Suc m) = n ^ m * totient n"
  by sorry
  
lemma totient_power: "m > 0 \<Longrightarrow> totient (n ^ m) = n ^ (m - 1) * totient n"
  by sorry

lemma totient_gcd_lcm: "totient (gcd a b) * totient (lcm a b) = totient a * totient b"
  by sorry

end
