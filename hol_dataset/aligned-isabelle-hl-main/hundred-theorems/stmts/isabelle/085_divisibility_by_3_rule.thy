(*  Title:      HOL/Number_Theory/Cong.thy
    Author:     Christophe Tabacznyj
    Author:     Lawrence C. Paulson
    Author:     Amine Chaieb
    Author:     Thomas M. Rasmussen
    Author:     Jeremy Avigad

Defines congruence (notation: [x = y] (mod z)) for natural numbers and
integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on @{cite davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD".

The original theory, "IntPrimes", by Thomas M. Rasmussen, defined and
developed the congruence relations on the integers. The notion was
extended to the natural numbers by Chaieb. Jeremy Avigad combined
these, revised and tidied them, made the development uniform for the
natural numbers and the integers, and added a number of new theorems.
*)

section \<open>Congruence\<close>

theory Cong
  imports "HOL-Computational_Algebra.Primes"
begin

subsection \<open>Generic congruences\<close>
 
context unique_euclidean_semiring
begin

definition cong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    (\<open>(\<open>indent=1 notation=\<open>mixfix cong\<close>\<close>[_ = _] '(' mod _'))\<close>)
  where "[b = c] (mod a) \<longleftrightarrow> b mod a = c mod a"
  
abbreviation notcong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    (\<open>(\<open>indent=1 notation=\<open>mixfix notcong\<close>\<close>[_ \<noteq> _] '(' mod _'))\<close>)
  where "[b \<noteq> c] (mod a) \<equiv> \<not> cong b c a"

lemma cong_refl [simp]:
  "[b = b] (mod a)"
  by sorry

lemma cong_sym: 
  "[b = c] (mod a) \<Longrightarrow> [c = b] (mod a)"
  by sorry

lemma cong_sym_eq:
  "[b = c] (mod a) \<longleftrightarrow> [c = b] (mod a)"
  by sorry

lemma cong_trans [trans]:
  "[b = c] (mod a) \<Longrightarrow> [c = d] (mod a) \<Longrightarrow> [b = d] (mod a)"
  by sorry

lemma cong_mult_self_right:
  "[b * a = 0] (mod a)"
  by sorry

lemma cong_mult_self_left:
  "[a * b = 0] (mod a)"
  by sorry

lemma cong_mod_left [simp]:
  "[b mod a = c] (mod a) \<longleftrightarrow> [b = c] (mod a)"
  by sorry

lemma cong_mod_right [simp]:
  "[b = c mod a] (mod a) \<longleftrightarrow> [b = c] (mod a)"
  by sorry

lemma cong_0 [simp, presburger]:
  "[b = c] (mod 0) \<longleftrightarrow> b = c"
  by sorry

lemma cong_1 [simp, presburger]:
  "[b = c] (mod 1)"
  by sorry

lemma cong_dvd_iff:
  "a dvd b \<longleftrightarrow> a dvd c" if "[b = c] (mod a)"
  by sorry

lemma cong_0_iff: "[b = 0] (mod a) \<longleftrightarrow> a dvd b"
  by sorry

lemma cong_add:
  "[b = c] (mod a) \<Longrightarrow> [d = e] (mod a) \<Longrightarrow> [b + d = c + e] (mod a)"
  by sorry

lemma cong_mult:
  "[b = c] (mod a) \<Longrightarrow> [d = e] (mod a) \<Longrightarrow> [b * d = c * e] (mod a)"
  by sorry

lemma cong_scalar_right:
  "[b = c] (mod a) \<Longrightarrow> [b * d = c * d] (mod a)"
  by sorry

lemma cong_scalar_left:
  "[b = c] (mod a) \<Longrightarrow> [d * b = d * c] (mod a)"
  by sorry

lemma cong_pow:
  "[b = c] (mod a) \<Longrightarrow> [b ^ n = c ^ n] (mod a)"
  by sorry

lemma cong_sum:
  "[sum f A = sum g A] (mod a)" if "\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod a)"
  by sorry

lemma cong_prod:
  "[prod f A = prod g A] (mod a)" if "(\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod a))"
  by sorry

lemma mod_mult_cong_right:
  "[c mod (a * b) = d] (mod a) \<longleftrightarrow> [c = d] (mod a)"
  by sorry

lemma mod_mult_cong_left:
  "[c mod (b * a) = d] (mod a) \<longleftrightarrow> [c = d] (mod a)"
  by sorry

lemma cong_mod_leftI [simp]:
  "[b = c] (mod a) \<Longrightarrow> [b mod a = c] (mod a)"
  by sorry

lemma cong_mod_rightI [simp]:
  "[b = c] (mod a) \<Longrightarrow> [b = c mod a] (mod a)"
  by sorry

lemma cong_cmult_leftI: "[a = b] (mod m) \<Longrightarrow> [c * a = c * b] (mod (c * m))"
  by sorry

lemma cong_cmult_rightI: "[a = b] (mod m) \<Longrightarrow> [a * c = b * c] (mod (m * c))"
  by sorry

lemma cong_dvd_mono_modulus:
  assumes "[a = b] (mod m)" "m' dvd m"
  shows   "[a = b] (mod m')"
  by sorry

lemma coprime_cong_transfer_left:
  assumes "coprime a b" "[a = a'] (mod b)"
  shows   "coprime a' b"
  by sorry

lemma coprime_cong_transfer_right:
  assumes "coprime a b" "[b = b'] (mod a)"
  shows   "coprime a b'"
  by sorry

lemma coprime_cong_cong_left:
  assumes "[a = a'] (mod b)"
  shows   "coprime a b \<longleftrightarrow> coprime a' b"
  by sorry

lemma coprime_cong_cong_right:
  assumes "[b = b'] (mod a)"
  shows   "coprime a b \<longleftrightarrow> coprime a b'"
  by sorry

end

context unique_euclidean_ring
begin

lemma cong_diff:
  "[b = c] (mod a) \<Longrightarrow> [d = e] (mod a) \<Longrightarrow> [b - d = c - e] (mod a)"
  by sorry

lemma cong_diff_iff_cong_0:
  "[b - c = 0] (mod a) \<longleftrightarrow> [b = c] (mod a)" (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma cong_minus_minus_iff:
  "[- b = - c] (mod a) \<longleftrightarrow> [b = c] (mod a)"
  by sorry

lemma cong_modulus_minus_iff [iff]:
  "[b = c] (mod - a) \<longleftrightarrow> [b = c] (mod a)"
  by sorry

lemma cong_iff_dvd_diff:
  "[a = b] (mod m) \<longleftrightarrow> m dvd (a - b)"
  by sorry

lemma cong_iff_lin:
  "[a = b] (mod m) \<longleftrightarrow> (\<exists>k. b = a + m * k)" (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma cong_add_lcancel:
  "[a + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by sorry

lemma cong_add_rcancel:
  "[x + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by sorry

lemma cong_add_lcancel_0:
  "[a + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by sorry

lemma cong_add_rcancel_0:
  "[x + a = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by sorry

lemma cong_dvd_modulus:
  "[x = y] (mod n)" if "[x = y] (mod m)" and "n dvd m"
  by sorry

lemma cong_modulus_mult:
  "[x = y] (mod m)" if "[x = y] (mod m * n)"
  by sorry

lemma cong_uminus: "[x = y] (mod m) \<Longrightarrow> [-x = -y] (mod m)"
  by sorry

end

lemma cong_abs [simp]:
  "[x = y] (mod \<bar>m\<bar>) \<longleftrightarrow> [x = y] (mod m)"
  for x y :: "'a :: {unique_euclidean_ring, linordered_idom}"
  by sorry

lemma cong_square:
  "prime p \<Longrightarrow> 0 < a \<Longrightarrow> [a * a = 1] (mod p) \<Longrightarrow> [a = 1] (mod p) \<or> [a = - 1] (mod p)"
  for a p :: "'a :: {normalization_semidom, linordered_idom, unique_euclidean_ring}"
  by sorry

lemma cong_mult_rcancel:
  "[a * k = b * k] (mod m) \<longleftrightarrow> [a = b] (mod m)"
  if "coprime k m" for a k m :: "'a::{unique_euclidean_ring, ring_gcd}"
  by sorry

lemma cong_mult_lcancel:
  "[k * a = k * b] (mod m) = [a = b] (mod m)"
  if "coprime k m" for a k m :: "'a::{unique_euclidean_ring, ring_gcd}"
  by sorry

lemma coprime_cong_mult:
  "[a = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n \<Longrightarrow> [a = b] (mod m * n)"
  for a b :: "'a :: {unique_euclidean_ring, semiring_gcd}"
  by sorry

lemma cong_gcd_eq:
  "gcd a m = gcd b m" if "[a = b] (mod m)"
  for a b :: "'a :: {unique_euclidean_semiring, euclidean_semiring_gcd}"
  by sorry

lemma cong_imp_coprime:
  "[a = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> coprime b m"
  for a b :: "'a :: {unique_euclidean_semiring, euclidean_semiring_gcd}"
  by sorry

lemma cong_cong_prod_coprime:
  "[x = y] (mod (\<Prod>i\<in>A. m i))" if
    "(\<forall>i\<in>A. [x = y] (mod m i))"
    "(\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)))"
  for x y :: "'a :: {unique_euclidean_ring, semiring_gcd}"
  by sorry


subsection \<open>Congruences on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

lemma cong_int_iff:
  "[int m = int q] (mod int n) \<longleftrightarrow> [m = q] (mod n)"
  by sorry

lemma cong_Suc_0 [simp, presburger]:
  "[m = n] (mod Suc 0)"
  by sorry

lemma cong_diff_nat:
  "[a - c = b - d] (mod m)" if "[a = b] (mod m)" "[c = d] (mod m)"
    and "a \<ge> c" "b \<ge> d" for a b c d m :: nat
  by sorry

lemma cong_diff_iff_cong_0_nat:
  "[a - b = 0] (mod m) \<longleftrightarrow> [a = b] (mod m)" if "a \<ge> b" for a b :: nat
  by sorry

lemma cong_diff_iff_cong_0_nat':
  "[nat \<bar>int a - int b\<bar> = 0] (mod m) \<longleftrightarrow> [a = b] (mod m)"
  by sorry

lemma cong_altdef_nat:
  "a \<ge> b \<Longrightarrow> [a = b] (mod m) \<longleftrightarrow> m dvd (a - b)"
  for a b :: nat
  by sorry

lemma cong_altdef_nat':
  "[a = b] (mod m) \<longleftrightarrow> m dvd nat \<bar>int a - int b\<bar>"
  by sorry

lemma cong_mult_rcancel_nat:
  "[a * k = b * k] (mod m) \<longleftrightarrow> [a = b] (mod m)"
  if "coprime k m" for a k m :: nat
  by sorry

lemma cong_mult_lcancel_nat:
  "[k * a = k * b] (mod m) = [a = b] (mod m)"
  if "coprime k m" for a k m :: nat
  by sorry

lemma coprime_cong_mult_nat:
  "[a = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n \<Longrightarrow> [a = b] (mod m * n)"
  for a b :: nat
  by sorry

lemma cong_less_imp_eq_nat: "0 \<le> a \<Longrightarrow> a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  for a b :: nat
  by sorry

lemma cong_less_imp_eq_int: "0 \<le> a \<Longrightarrow> a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  for a b :: int
  by sorry

lemma cong_less_unique_nat: "0 < m \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  for a m :: nat
  by sorry

lemma cong_less_unique_int: "0 < m \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  for a m :: int
  by sorry

lemma cong_iff_lin_nat: "[a = b] (mod m) \<longleftrightarrow> (\<exists>k1 k2. b + k1 * m = a + k2 * m)"
  for a b :: nat
  by sorry

lemma cong_cong_mod_nat: "[a = b] (mod m) \<longleftrightarrow> [a mod m = b mod m] (mod m)"
  for a b :: nat
  by sorry

lemma cong_cong_mod_int: "[a = b] (mod m) \<longleftrightarrow> [a mod m = b mod m] (mod m)"
  for a b :: int
  by sorry

lemma cong_add_lcancel_nat: "[a + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  for a x y :: nat
  by sorry

lemma cong_add_rcancel_nat: "[x + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  for a x y :: nat
  by sorry

lemma cong_add_lcancel_0_nat: "[a + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  for a x :: nat
  by sorry

lemma cong_add_rcancel_0_nat: "[x + a = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  for a x :: nat
  by sorry

lemma cong_dvd_modulus_nat: "[x = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow> [x = y] (mod n)"
  for x y :: nat
  by sorry

lemma cong_to_1_nat:
  fixes a :: nat
  assumes "[a = 1] (mod n)"
  shows "n dvd (a - 1)"
  by sorry

lemma cong_0_1_nat': "[0 = Suc 0] (mod n) \<longleftrightarrow> n = Suc 0"
  by sorry

lemma cong_0_1_nat: "[0 = 1] (mod n) \<longleftrightarrow> n = 1"
  for n :: nat
  by sorry

lemma cong_0_1_int: "[0 = 1] (mod n) \<longleftrightarrow> n = 1 \<or> n = - 1"
  for n :: int
  by sorry

lemma cong_to_1'_nat: "[a = 1] (mod n) \<longleftrightarrow> a = 0 \<and> n = 1 \<or> (\<exists>m. a = 1 + m * n)"
  for a :: nat
  by sorry

lemma cong_le_nat: "y \<le> x \<Longrightarrow> [x = y] (mod n) \<longleftrightarrow> (\<exists>q. x = q * n + y)"
  for x y :: nat
  by sorry

lemma cong_solve_nat:
  fixes a :: nat
  shows "\<exists>x. [a * x = gcd a n] (mod n)"
  by sorry

lemma cong_solve_int:
  fixes a :: int
  shows "\<exists>x. [a * x = gcd a n] (mod n)"
  by sorry

lemma cong_solve_dvd_nat:
  fixes a :: nat
  assumes "gcd a n dvd d"
  shows "\<exists>x. [a * x = d] (mod n)"
  by sorry

lemma cong_solve_dvd_int:
  fixes a::int
  assumes b: "gcd a n dvd d"
  shows "\<exists>x. [a * x = d] (mod n)"
  by sorry

lemma cong_solve_coprime_nat:
  "\<exists>x. [a * x = Suc 0] (mod n)" if "coprime a n"
  by sorry

lemma cong_solve_coprime_int:
  "\<exists>x. [a * x = 1] (mod n)" if "coprime a n" for a n x :: int
  by sorry

lemma coprime_iff_invertible_nat:
  "coprime a m \<longleftrightarrow> (\<exists>x. [a * x = Suc 0] (mod m))" (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma coprime_iff_invertible_int:
  "coprime a m \<longleftrightarrow> (\<exists>x. [a * x = 1] (mod m))" (is "?P \<longleftrightarrow> ?Q") for m :: int
  by sorry

lemma coprime_iff_invertible'_nat:
  assumes "m > 0"
  shows "coprime a m \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> x < m \<and> [a * x = Suc 0] (mod m))"
  by sorry

lemma coprime_iff_invertible'_int:
  fixes m :: int
  assumes "m > 0"
  shows "coprime a m \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> x < m \<and> [a * x = 1] (mod m))"
  by sorry

lemma cong_cong_lcm_nat: "[x = y] (mod a) \<Longrightarrow> [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  for x y :: nat
  by sorry

lemma cong_cong_lcm_int: "[x = y] (mod a) \<Longrightarrow> [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  for x y :: int
  by sorry

lemma cong_cong_prod_coprime_nat:
  "[x = y] (mod (\<Prod>i\<in>A. m i))" if
    "(\<forall>i\<in>A. [x = y] (mod m i))"
    "(\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)))"
  for x y :: nat
  by sorry

lemma binary_chinese_remainder_nat:
  fixes m1 m2 :: nat
  assumes a: "coprime m1 m2"
  shows "\<exists>x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
  by sorry

lemma binary_chinese_remainder_int:
  fixes m1 m2 :: int
  assumes a: "coprime m1 m2"
  shows "\<exists>x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
  by sorry

lemma cong_modulus_mult_nat: "[x = y] (mod m * n) \<Longrightarrow> [x = y] (mod m)"
  for x y :: nat
  by sorry

lemma cong_less_modulus_unique_nat: "[x = y] (mod m) \<Longrightarrow> x < m \<Longrightarrow> y < m \<Longrightarrow> x = y"
  for x y :: nat
  by sorry

lemma binary_chinese_remainder_unique_nat:
  fixes m1 m2 :: nat
  assumes a: "coprime m1 m2"
    and nz: "m1 \<noteq> 0" "m2 \<noteq> 0"
  shows "\<exists>!x. x < m1 * m2 \<and> [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
  by sorry

lemma chinese_remainder_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
    and u :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and cop: "\<forall>i \<in> A. \<forall>j \<in> A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)"
  shows "\<exists>x. \<forall>i \<in> A. [x = u i] (mod m i)"
  by sorry

lemma coprime_cong_prod_nat: "[x = y] (mod (\<Prod>i\<in>A. m i))"
  if "\<And>i j. \<lbrakk>i \<in> A; j \<in> A; i \<noteq> j\<rbrakk> \<Longrightarrow> coprime (m i) (m j)"
    and "\<And>i. i \<in> A \<Longrightarrow> [x = y] (mod m i)" for x y :: nat
  by sorry

lemma chinese_remainder_unique_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
    and u :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and nz: "\<forall>i\<in>A. m i \<noteq> 0"
    and cop: "\<forall>i\<in>A. \<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)"
  shows "\<exists>!x. x < (\<Prod>i\<in>A. m i) \<and> (\<forall>i\<in>A. [x = u i] (mod m i))"
  by sorry

lemma (in semiring_1_cancel) of_nat_eq_iff_cong_CHAR:
  "of_nat x = (of_nat y :: 'a) \<longleftrightarrow> [x = y] (mod CHAR('a))"
  by sorry

lemma (in ring_1) of_int_eq_iff_cong_CHAR:
  "of_int x = (of_int y :: 'a) \<longleftrightarrow> [x = y] (mod int CHAR('a))"
  by sorry

text \<open>Thanks to Manuel Eberl\<close>
lemma prime_cong_4_nat_cases [consumes 1, case_names 2 cong_1 cong_3]:
  assumes "prime (p :: nat)"
  obtains "p = 2" | "[p = 1] (mod 4)" | "[p = 3] (mod 4)"
  by sorry

end
