(*  Author: John Harrison and Valentina Bruno
    Ported from "hol_light/Multivariate/complexes.ml" by L C Paulson
*)

section \<open>Polynomial Functions: Extremal Behaviour and Root Counts\<close>

theory Poly_Roots
imports Complex_Main
begin

subsection\<open>Basics about polynomial functions: extremal behaviour and root counts\<close>

lemma sub_polyfun:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows   "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) =
           (x - y) * (\<Sum>j<n. \<Sum>k= Suc j..n. a k * y^(k - Suc j) * x^j)"
sorry

lemma sub_polyfun_alt:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows   "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) =
           (x - y) * (\<Sum>j<n. \<Sum>k<n-j. a (j+k+1) * y^k * x^j)"
sorry

lemma polyfun_linear_factor:
  fixes a :: "'a::{comm_ring,monoid_mult}"
  shows  "\<exists>b. \<forall>z. (\<Sum>i\<le>n. c i * z^i) =
                  (z-a) * (\<Sum>i<n. b i * z^i) + (\<Sum>i\<le>n. c i * a^i)"
sorry

lemma polyfun_linear_factor_root:
  fixes a :: "'a::{comm_ring,monoid_mult}"
  assumes "(\<Sum>i\<le>n. c i * a^i) = 0"
  shows  "\<exists>b. \<forall>z. (\<Sum>i\<le>n. c i * z^i) = (z-a) * (\<Sum>i<n. b i * z^i)"
sorry

lemma adhoc_norm_triangle: "a + norm(y) \<le> b ==> norm(x) \<le> a ==> norm(x + y) \<le> b"
sorry

proposition polyfun_extremal_lemma:
  fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "e > 0"
    shows "\<exists>M. \<forall>z. M \<le> norm z \<longrightarrow> norm(\<Sum>i\<le>n. c i * z^i) \<le> e * norm(z) ^ Suc n"
sorry

lemma norm_lemma_xy: assumes "\<bar>b\<bar> + 1 \<le> norm(y) - a" "norm(x) \<le> a" shows "b \<le> norm(x + y)"
sorry

proposition polyfun_extremal:
  fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "\<exists>k. k \<noteq> 0 \<and> k \<le> n \<and> c k \<noteq> 0"
    shows "eventually (\<lambda>z. norm(\<Sum>i\<le>n. c i * z^i) \<ge> B) at_infinity"
sorry

proposition polyfun_rootbound:
 fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
 assumes "\<exists>k. k \<le> n \<and> c k \<noteq> 0"
   shows "finite {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<and> card {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<le> n"
sorry

corollary
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
  assumes "\<exists>k. k \<le> n \<and> c k \<noteq> 0"
    shows polyfun_rootbound_finite: "finite {z. (\<Sum>i\<le>n. c i * z^i) = 0}"
      and polyfun_rootbound_card:   "card {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<le> n"
sorry

proposition polyfun_finite_roots:
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
    shows  "finite {z. (\<Sum>i\<le>n. c i * z^i) = 0} \<longleftrightarrow> (\<exists>k. k \<le> n \<and> c k \<noteq> 0)"
sorry

lemma polyfun_eq_0:
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
    shows  "(\<forall>z. (\<Sum>i\<le>n. c i * z^i) = 0) \<longleftrightarrow> (\<forall>k. k \<le> n \<longrightarrow> c k = 0)"
sorry

theorem polyfun_eq_const:
  fixes c :: "nat \<Rightarrow> 'a::{comm_ring,real_normed_div_algebra}"
    shows  "(\<forall>z. (\<Sum>i\<le>n. c i * z^i) = k) \<longleftrightarrow> c 0 = k \<and> (\<forall>k. k \<noteq> 0 \<and> k \<le> n \<longrightarrow> c k = 0)"
sorry

end

