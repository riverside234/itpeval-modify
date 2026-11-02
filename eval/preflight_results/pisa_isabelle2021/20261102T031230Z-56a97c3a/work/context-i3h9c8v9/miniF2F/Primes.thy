(*  Title:      HOL/Computational_Algebra/Primes.thy
    Author:     Christophe Tabacznyj
    Author:     Lawrence C. Paulson
    Author:     Amine Chaieb
    Author:     Thomas M. Rasmussen
    Author:     Jeremy Avigad
    Author:     Tobias Nipkow
    Author:     Manuel Eberl

This theory deals with properties of primes. Definitions and lemmas are
proved uniformly for the natural numbers and integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on @{cite davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD". IntPrimes also defined and developed
the congruence relations on the integers. The notion was extended to
the natural numbers by Chaieb.

Jeremy Avigad combined all of these, made everything uniform for the
natural numbers and the integers, and added a number of new theorems.

Tobias Nipkow cleaned up a lot.

Florian Haftmann and Manuel Eberl put primality and prime factorisation
onto an algebraic foundation and thus generalised these concepts to 
other rings, such as polynomials. (see also the Factorial_Ring theory).

There were also previous formalisations of unique factorisation by 
Thomas Marthedal Rasmussen, Jeremy Avigad, and David Gray.
*)

section \<open>Primes\<close>

theory Primes
imports Euclidean_Algorithm
begin
declare [[quick_and_dirty = true]]


subsection \<open>Primes on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

lemma Suc_0_not_prime_nat [simp]: "\<not> prime (Suc 0)"
  
  sorry


lemma prime_ge_2_nat:
  "p \<ge> 2" if "prime p" for p :: nat
  
  sorry


lemma prime_ge_2_int:
  "p \<ge> 2" if "prime p" for p :: int
  
  sorry


lemma prime_ge_0_int: "prime p \<Longrightarrow> p \<ge> (0::int)"
  
  sorry


lemma prime_gt_0_nat: "prime p \<Longrightarrow> p > (0::nat)"
  
  sorry


lemma prime_gt_0_int: "prime p \<Longrightarrow> p > (0::int)"
  
  sorry


lemma prime_ge_1_nat: "prime p \<Longrightarrow> p \<ge> (1::nat)"
  
  sorry


lemma prime_ge_Suc_0_nat: "prime p \<Longrightarrow> p \<ge> Suc 0"
  
  sorry


lemma prime_ge_1_int: "prime p \<Longrightarrow> p \<ge> (1::int)"
  
  sorry


lemma prime_gt_1_nat: "prime p \<Longrightarrow> p > (1::nat)"
  
  sorry


lemma prime_gt_Suc_0_nat: "prime p \<Longrightarrow> p > Suc 0"
  
  sorry


lemma prime_gt_1_int: "prime p \<Longrightarrow> p > (1::int)"
  
  sorry


lemma prime_natI:
  "prime p" if "p \<ge> 2" and "\<And>m n. p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n" for p :: nat
  
  sorry


lemma prime_intI:
  "prime p" if "p \<ge> 2" and "\<And>m n. p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n" for p :: int
  
  sorry


lemma prime_elem_nat_iff [simp]:
  "prime_elem n \<longleftrightarrow> prime n" for n :: nat
  
  sorry


lemma prime_elem_iff_prime_abs [simp]:
  "prime_elem k \<longleftrightarrow> prime \<bar>k\<bar>" for k :: int
  
  sorry


lemma prime_nat_int_transfer [simp]:
  "prime (int n) \<longleftrightarrow> prime n" (is "?P \<longleftrightarrow> ?Q")
  
  sorry


lemma prime_nat_iff_prime [simp]:
  "prime (nat k) \<longleftrightarrow> prime k"
  
  sorry


lemma prime_int_nat_transfer:
  "prime k \<longleftrightarrow> k \<ge> 0 \<and> prime (nat k)"
  
  sorry


lemma prime_nat_naiveI:
  "prime p" if "p \<ge> 2" and dvd: "\<And>n. n dvd p \<Longrightarrow> n = 1 \<or> n = p" for p :: nat
  
  sorry


lemma prime_int_naiveI:
  "prime p" if "p \<ge> 2" and dvd: "\<And>k. k dvd p \<Longrightarrow> \<bar>k\<bar> = 1 \<or> \<bar>k\<bar> = p" for p :: int
  
  sorry


lemma prime_nat_iff:
  "prime (n :: nat) \<longleftrightarrow> (1 < n \<and> (\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n))"
  
  sorry


lemma prime_nat_iff':
  "prime (p :: nat) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {2..<p}. \<not> n dvd p)"
  
  sorry


lemma prime_int_iff:
  "prime (n::int) \<longleftrightarrow> (1 < n \<and> (\<forall>m. m \<ge> 0 \<and> m dvd n \<longrightarrow> m = 1 \<or> m = n))"
  
  sorry


lemma prime_int_iff':
  "prime (p :: int) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {2..<p}. \<not> n dvd p)" (is "?P \<longleftrightarrow> ?Q")
  
  sorry


lemma prime_nat_not_dvd:
  assumes "prime p" "p > n" "n \<noteq> (1::nat)"
  shows   "\<not>n dvd p"
  
  sorry


lemma prime_int_not_dvd:
  assumes "prime p" "p > n" "n > (1::int)"
  shows   "\<not>n dvd p"
  
  sorry


lemma prime_odd_nat: "prime p \<Longrightarrow> p > (2::nat) \<Longrightarrow> odd p"
  
  sorry


lemma prime_odd_int: "prime p \<Longrightarrow> p > (2::int) \<Longrightarrow> odd p"
  
  sorry


lemma prime_int_altdef:
  "prime p = (1 < p \<and> (\<forall>m::int. m \<ge> 0 \<longrightarrow> m dvd p \<longrightarrow>
    m = 1 \<or> m = p))"
  
  sorry


lemma not_prime_eq_prod_nat:
  assumes "m > 1" "\<not> prime (m::nat)"
  shows   "\<exists>n k. n = m * k \<and> 1 < m \<and> m < n \<and> 1 < k \<and> k < n"
  
  sorry



subsection \<open>Make prime naively executable\<close>

lemma prime_int_numeral_eq [simp]:
  "prime (numeral m :: int) \<longleftrightarrow> prime (numeral m :: nat)"
  
  sorry


class check_prime_by_range = normalization_semidom + discrete_linordered_semidom +
  assumes prime_iff: \<open>prime a \<longleftrightarrow> 1 < a \<and> (\<forall>d\<in>{2..a div 2}. \<not> d dvd a)\<close>
begin

lemma two_is_prime [simp]:
  \<open>prime 2\<close>
  
  sorry


end

lemma divisor_less_eq_half_nat:
  \<open>m \<le> n div 2\<close> if \<open>m dvd n\<close> \<open>m < n\<close> for m n :: nat
  
  sorry


instance nat :: check_prime_by_range
  
  sorry


lemma two_is_prime_nat [simp]:
  \<open>prime (2::nat)\<close>
  
  sorry


lemma divisor_less_eq_half_int:
  \<open>k \<le> l div 2\<close> if \<open>k dvd l\<close> \<open>k < l\<close> \<open>l \<ge> 0\<close> \<open>k \<ge> 0\<close> for k l :: int
  
  sorry


instance int :: check_prime_by_range
  
  sorry


lemma prime_nat_numeral_eq [simp]: \<comment> \<open>TODO Sieve Of Erathosthenes might speed this up\<close>
  "prime (numeral m :: nat) \<longleftrightarrow>
    (1::nat) < numeral m \<and>
    (\<forall>n::nat \<in> set [2..<Suc (numeral m div 2)]. \<not> n dvd numeral m)"
  
  sorry


context check_prime_by_range
begin

definition check_divisors :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>check_divisors l u a \<longleftrightarrow> (\<forall>d\<in>{l..u}. \<not> d dvd a)\<close>

lemma check_divisors_rec [code]:
  \<open>check_divisors l u a \<longleftrightarrow> u < l \<or> (\<not> l dvd a \<and> check_divisors (l + 1) u a)\<close>
  
  sorry


lemma prime_eq_check_divisors [code]:
  \<open>prime a \<longleftrightarrow> a > 1 \<and> check_divisors 2 (a div 2) a\<close>
  
  sorry


end


subsection \<open>Largest exponent of a prime factor\<close>

lemma prime_factor_nat:
  "n \<noteq> (1::nat) \<Longrightarrow> \<exists>p. prime p \<and> p dvd n"
  
  sorry


lemma prime_factor_int:
  fixes k :: int
  assumes "\<bar>k\<bar> \<noteq> 1"
  obtains p where "prime p" "p dvd k"
  
  sorry


text\<open>Possibly duplicates other material, but avoid the complexities of multisets.\<close>
  
lemma prime_power_cancel_less:
  assumes "prime p" and eq: "m * (p ^ k) = m' * (p ^ k')" and less: "k < k'" and "\<not> p dvd m"
  shows False
  
  sorry


lemma prime_power_cancel:
  assumes "prime p" and eq: "m * (p ^ k) = m' * (p ^ k')" and "\<not> p dvd m" "\<not> p dvd m'"
  shows "k = k'"
  
  sorry


lemma prime_power_cancel2:
  assumes "prime p" "m * (p ^ k) = m' * (p ^ k')" "\<not> p dvd m" "\<not> p dvd m'"
  obtains "m = m'" "k = k'"
  
  sorry


lemma prime_power_canonical:
  fixes m :: nat
  assumes "prime p" "m > 0"
  shows "\<exists>k n. \<not> p dvd n \<and> m = n * p ^ k"
  
  sorry



subsection \<open>Infinitely many primes\<close>

lemma next_prime_bound: "\<exists>p::nat. prime p \<and> n < p \<and> p \<le> fact n + 1"
  
  sorry


lemma bigger_prime: "\<exists>p. prime p \<and> p > (n::nat)"
  
  sorry


lemma primes_infinite: "\<not> (finite {(p::nat). prime p})"
  
  sorry


subsection \<open>Powers of Primes\<close>

text\<open>Versions for type nat only\<close>

lemma prime_product:
  fixes p::nat
  assumes "prime (p * q)"
  shows "p = 1 \<or> q = 1"
  
  sorry

lemma prime_power_mult_nat:
  fixes p :: nat
  assumes p: "prime p" and xy: "x * y = p ^ k"
  shows "\<exists>i j. x = p ^ i \<and> y = p^ j"
  
  sorry


lemma prime_power_exp_nat:
  fixes p::nat
  assumes p: "prime p" and n: "n \<noteq> 0"
    and xn: "x^n = p^k" shows "\<exists>i. x = p^i"
  
  sorry


lemma divides_primepow_nat:
  fixes p :: nat
  assumes p: "prime p"
  shows "d dvd p ^ k \<longleftrightarrow> (\<exists>i\<le>k. d = p ^ i)"
  
  sorry


lemma gcd_prime_int:
  assumes "prime (p :: int)"
  shows   "gcd p k = (if p dvd k then p else 1)"
  
  sorry



subsection \<open>Chinese Remainder Theorem Variants\<close>

lemma bezout_gcd_nat:
  fixes a::nat shows "\<exists>x y. a * x - b * y = gcd a b \<or> b * x - a * y = gcd a b"
  
  sorry


lemma gcd_bezout_sum_nat:
  fixes a::nat
  assumes "a * x + b * y = d"
  shows "gcd a b dvd d"
  
  sorry



text \<open>A binary form of the Chinese Remainder Theorem.\<close>

(* TODO: Generalise? *)
lemma chinese_remainder:
  fixes a::nat  assumes ab: "coprime a b" and a: "a \<noteq> 0" and b: "b \<noteq> 0"
  shows "\<exists>x q1 q2. x = u + q1 * a \<and> x = v + q2 * b"
  
  sorry


text \<open>Primality\<close>


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma coprime_bezout_strong:
  fixes a::nat assumes "coprime a b"  "b \<noteq> 1"
  shows "\<exists>x y. a * x = b * y + 1"
  
  