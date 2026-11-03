(*  Title:      HOL/Analysis/Change_Of_Vars.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section\<open>Change of Variables Theorems\<close>

theory Change_Of_Vars
  imports Vitali_Covering_Theorem Determinants

begin

subsection \<open>Measurable Shear and Stretch\<close>

proposition
  fixes a :: "real^'n"
  assumes "m \<noteq> n" and ab_ne: "cbox a b \<noteq> {}" and an: "0 \<le> a$n"
  shows measurable_shear_interval: "(\<lambda>x. \<chi> i. if i = m then x$m + x$n else x$i) ` (cbox a b) \<in> lmeasurable"
       (is  "?f ` _ \<in> _")
   and measure_shear_interval: "measure lebesgue ((\<lambda>x. \<chi> i. if i = m then x$m + x$n else x$i) ` cbox a b)
               = measure lebesgue (cbox a b)" (is "?Q")
sorry

proposition
  fixes S :: "(real^'n) set"
  assumes "S \<in> lmeasurable"
  shows measurable_stretch: "((\<lambda>x. \<chi> k. m k * x$k) ` S) \<in> lmeasurable" (is  "?f ` S \<in> _")
    and measure_stretch: "measure lebesgue ((\<lambda>x. \<chi> k. m k * x$k) ` S) = \<bar>prod m UNIV\<bar> * measure lebesgue S"
    (is "?MEQ")
sorry

proposition
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "linear f" "S \<in> lmeasurable"
  shows measurable_linear_image: "(f ` S) \<in> lmeasurable"
    and measure_linear_image: "measure lebesgue (f ` S) = \<bar>det (matrix f)\<bar> * measure lebesgue S" (is "?Q f S")
sorry

lemma
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes f: "orthogonal_transformation f" and S: "S \<in> lmeasurable"
  shows measurable_orthogonal_image: "f ` S \<in> lmeasurable"
    and measure_orthogonal_image: "measure lebesgue (f ` S) = measure lebesgue S"
sorry

proposition measure_semicontinuous_with_hausdist_explicit:
  assumes "bounded S" and neg: "negligible(frontier S)" and "e > 0"
  obtains d where "d > 0"
                  "\<And>T. \<lbrakk>T \<in> lmeasurable; \<And>y. y \<in> T \<Longrightarrow> \<exists>x. x \<in> S \<and> dist x y < d\<rbrakk>
                        \<Longrightarrow> measure lebesgue T < measure lebesgue S + e"
sorry

proposition
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> lmeasurable"
  and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  and int: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  and bounded: "\<And>x. x \<in> S \<Longrightarrow> \<bar>det (matrix (f' x))\<bar> \<le> B"
  shows measurable_bounded_differentiable_image:
       "f ` S \<in> lmeasurable"
    and measure_bounded_differentiable_image:
       "measure lebesgue (f ` S) \<le> B * measure lebesgue S" (is "?M")
sorry

lemma m_diff_image_weak:
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> lmeasurable"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
sorry

theorem
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue"
    and deriv: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and int: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  shows measurable_differentiable_image: "f ` S \<in> lmeasurable"
    and measure_differentiable_image:
       "measure lebesgue (f ` S) \<le> integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)" (is "?M")
sorry

lemma borel_measurable_simple_function_limit_increasing:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  shows "(f \<in> borel_measurable lebesgue \<and> (\<forall>x. 0 \<le> f x)) \<longleftrightarrow>
         (\<exists>g. (\<forall>n x. 0 \<le> g n x \<and> g n x \<le> f x) \<and> (\<forall>n x. g n x \<le> (g(Suc n) x)) \<and>
              (\<forall>n. g n \<in> borel_measurable lebesgue) \<and> (\<forall>n. finite(range (g n))) \<and>
              (\<forall>x. (\<lambda>n. g n x) \<longlonglongrightarrow> f x))"
         (is "?lhs = ?rhs")
sorry

subsection\<open>Borel measurable Jacobian determinant\<close>

lemma lemma_partial_derivatives0:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" and lim0: "((\<lambda>x. f x /\<^sub>R norm x) \<longlongrightarrow> 0) (at 0 within S)"
    and lb: "\<And>v. v \<noteq> 0 \<Longrightarrow> (\<exists>k>0. \<forall>e>0. \<exists>x. x \<in> S - {0} \<and> norm x < e \<and> k * norm x \<le> \<bar>v \<bullet> x\<bar>)"
  shows "f x = 0"
sorry

lemma lemma_partial_derivatives:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" and lim: "((\<lambda>x. f (x - a) /\<^sub>R norm (x - a)) \<longlongrightarrow> 0) (at a within S)"
    and lb: "\<And>v. v \<noteq> 0 \<Longrightarrow> (\<exists>k>0.  \<forall>e>0. \<exists>x \<in> S - {a}. norm(a - x) < e \<and> k * norm(a - x) \<le> \<bar>v \<bullet> (x - a)\<bar>)"
  shows "f x = 0"
sorry

proposition borel_measurable_partial_derivatives:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n"
  assumes S: "S \<in> sets lebesgue"
    and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. (matrix(f' x)$m$n)) \<in> borel_measurable (lebesgue_on S)"
sorry

theorem borel_measurable_det_Jacobian:
 fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue" and f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  shows "(\<lambda>x. det(matrix(f' x))) \<in> borel_measurable (lebesgue_on S)"
sorry

text\<open>The localisation wrt S uses the same argument for many similar results.\<close>
(*See HOL Light's MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_BOREL, etc.*)
theorem borel_measurable_lebesgue_on_preimage_borel:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue"
  shows "f \<in> borel_measurable (lebesgue_on S) \<longleftrightarrow>
         (\<forall>T. T \<in> sets borel \<longrightarrow> {x \<in> S. f x \<in> T} \<in> sets lebesgue)"
sorry

lemma sets_lebesgue_almost_borel:
  assumes "S \<in> sets lebesgue"
  obtains B N where "B \<in> sets borel" "negligible N" "B \<union> N = S"
sorry

lemma double_lebesgue_sets:
 assumes S: "S \<in> sets lebesgue" and T: "T \<in> sets lebesgue" and fim: "f ` S \<subseteq> T"
 shows "(\<forall>U. U \<in> sets lebesgue \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue) \<longleftrightarrow>
          f \<in> borel_measurable (lebesgue_on S) \<and>
          (\<forall>U. negligible U \<and> U \<subseteq> T \<longrightarrow> {x \<in> S. f x \<in> U} \<in> sets lebesgue)"
         (is "?lhs \<longleftrightarrow> _ \<and> ?rhs")
sorry

subsection\<open>Simplest case of Sard's theorem (we don't need continuity of derivative)\<close>

lemma Sard_lemma00:
  fixes P :: "'b::euclidean_space set"
  assumes "a \<ge> 0" and a: "a *\<^sub>R i \<noteq> 0" and i: "i \<in> Basis"
    and P: "P \<subseteq> {x. a *\<^sub>R i \<bullet> x = 0}"
    and "0 \<le> m" "0 \<le> e"
 obtains S where "S \<in> lmeasurable"
            and "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
            and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (DIM('b) - 1)"
sorry

text\<open>As above, but reorienting the vector (HOL Light's @text{GEOM\_BASIS\_MULTIPLE\_TAC})\<close>
lemma Sard_lemma0:
  fixes P :: "(real^'n::{finite,wellorder}) set"
  assumes "a \<noteq> 0"
    and P: "P \<subseteq> {x. a \<bullet> x = 0}" and "0 \<le> m" "0 \<le> e"
  obtains S where "S \<in> lmeasurable"
    and "{z. norm z \<le> m \<and> (\<exists>t \<in> P. norm(z - t) \<le> e)} \<subseteq> S"
    and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (CARD('n) - 1)"
sorry

text\<open>As above, but translating the sets (HOL Light's @text{GEN\_GEOM\_ORIGIN\_TAC})\<close>
lemma Sard_lemma1:
  fixes P :: "(real^'n::{finite,wellorder}) set"
   assumes P: "dim P < CARD('n)" and "0 \<le> m" "0 \<le> e"
 obtains S where "S \<in> lmeasurable"
            and "{z. norm(z - w) \<le> m \<and> (\<exists>t \<in> P. norm(z - w - t) \<le> e)} \<subseteq> S"
            and "measure lebesgue S \<le> (2 * e) * (2 * m) ^ (CARD('n) - 1)"
sorry

lemma Sard_lemma2:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n::{finite,wellorder}"
  assumes mlen: "CARD('m) \<le> CARD('n)" (is "?m \<le> ?n")
    and "B > 0" "bounded S"
    and derS: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> rank(matrix(f' x)) < CARD('n)"
    and B: "\<And>x. x \<in> S \<Longrightarrow> onorm(f' x) \<le> B"
  shows "negligible(f ` S)"
sorry

theorem baby_Sard:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n::{finite,wellorder}"
  assumes mlen: "CARD('m) \<le> CARD('n)"
    and der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> rank(matrix(f' x)) < CARD('n)"
  shows "negligible(f ` S)"
sorry


subsection\<open>A one-way version of change-of-variables not assuming injectivity. \<close>

lemma integral_on_image_ubound_weak:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
      and f: "f \<in> borel_measurable (lebesgue_on (g ` S))"
      and nonneg_fg:  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and det_int_fg: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
      and meas_gim: "\<And>T. \<lbrakk>T \<subseteq> g ` S; T \<in> sets lebesgue\<rbrakk> \<Longrightarrow> {x \<in> S. g x \<in> T} \<in> sets lebesgue"
    shows "f integrable_on (g ` S) \<and>
           integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
sorry

lemma integral_on_image_ubound_nonneg:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real"
  assumes nonneg_fg: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
      and der_g:   "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and intS: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
  shows "f integrable_on (g ` S) \<and> integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x))"
         (is "_ \<and> _ \<le> ?b")
sorry

lemma absolutely_integrable_on_image_real:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
sorry

proposition absolutely_integrable_on_image:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and intS: "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
  shows "f absolutely_integrable_on (g ` S)"
sorry

proposition integral_on_image_ubound:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes"\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f(g x)"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S"
  shows "integral (g ` S) f \<le> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x))"
sorry

subsection\<open>Change-of-variables theorem\<close>

text\<open>The classic change-of-variables theorem. We have two versions with quite general hypotheses,
the first that the transforming function has a continuous inverse, the second that the base set is
Lebesgue measurable.\<close>
lemma cov_invertible_nonneg_le:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and f0: "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "f integrable_on T \<and> (integral T f) \<le> b \<longleftrightarrow>
             (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) \<le> b"
        (is "?lhs = ?rhs")
sorry

lemma cov_invertible_nonneg_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and "\<And>y. y \<in> T \<Longrightarrow> 0 \<le> f y"
      and "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "((\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) has_integral b) S \<longleftrightarrow> (f has_integral b) T"
sorry

lemma cov_invertible_real:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real" and g :: "real^'n::_ \<Rightarrow> real^'n::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
      and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
      and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> * f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on T \<and> integral T f = b"
         (is "?lhs = ?rhs")
sorry

lemma cv_inv_version3:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and der_h: "\<And>y. y \<in> T \<Longrightarrow> (h has_derivative h' y) (at y within T)"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> h(g x) = x"
    and gh: "\<And>y. y \<in> T \<Longrightarrow> h y \<in> S \<and> g(h y) = y"
    and id: "\<And>y. y \<in> T \<Longrightarrow> h' y \<circ> g'(h y) = id"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on T \<and> integral T f = b"
sorry

lemma cv_inv_version4:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S) \<and> invertible(matrix(g' x))"
    and hg: "\<And>x. x \<in> S \<Longrightarrow> continuous_on (g ` S) h \<and> h(g x) = x"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
         \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
sorry

theorem has_absolute_integral_change_of_variables_invertible:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and hg: "\<And>x. x \<in> S \<Longrightarrow> h(g x) = x"
      and conth: "continuous_on (g ` S) h"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and> integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b \<longleftrightarrow>
         f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
    (is "?lhs = ?rhs")
sorry

theorem has_absolute_integral_change_of_variables_compact:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "compact S"
      and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
      and inj: "inj_on g S"
  shows "((\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
             integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b)"
sorry

lemma has_absolute_integral_change_of_variables_compact_family:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes compact: "\<And>n::nat. compact (F n)"
      and der_g: "\<And>x. x \<in> (\<Union>n. F n) \<Longrightarrow> (g has_derivative g' x) (at x within (\<Union>n. F n))"
      and inj: "inj_on g (\<Union>n. F n)"
  shows "((\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on (\<Union>n. F n) \<and>
             integral (\<Union>n. F n) (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
      \<longleftrightarrow> f absolutely_integrable_on (g ` (\<Union>n. F n)) \<and> integral (g ` (\<Union>n. F n)) f = b)"
sorry

theorem has_absolute_integral_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
sorry

corollary absolutely_integrable_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and "inj_on g S"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S"
sorry

corollary integral_change_of_variables:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
    and disj: "(f absolutely_integrable_on (g ` S) \<or>
        (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
  shows "integral (g ` S) f = integral S (\<lambda>x. \<bar>det (matrix (g' x))\<bar> *\<^sub>R f(g x))"
sorry

lemma has_absolute_integral_change_of_variables_1:
  fixes f :: "real \<Rightarrow> real^'n::{finite,wellorder}" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
sorry

corollary absolutely_integrable_change_of_variables_1:
  fixes f :: "real \<Rightarrow> real^'n::{finite,wellorder}" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_vector_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(f absolutely_integrable_on g ` S \<longleftrightarrow>
             (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S)"
sorry
text \<open>when @{term "n=1"}\<close>
lemma has_absolute_integral_change_of_variables_1':
  fixes f :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
sorry


subsection\<open>Change of variables for integrals: special case of linear function\<close>

lemma has_absolute_integral_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
sorry

lemma absolutely_integrable_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "(\<lambda>x. \<bar>det (matrix g)\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S
     \<longleftrightarrow> f absolutely_integrable_on (g ` S)"
sorry

lemma absolutely_integrable_on_linear_image:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
  shows "f absolutely_integrable_on (g ` S)
     \<longleftrightarrow> (f \<circ> g) absolutely_integrable_on S \<or> det(matrix g) = 0"
sorry

lemma integral_change_of_variables_linear:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'n" and g :: "real^'m::_ \<Rightarrow> real^'m::_"
  assumes "linear g"
      and "f absolutely_integrable_on (g ` S) \<or> (f \<circ> g) absolutely_integrable_on S"
    shows "integral (g ` S) f = \<bar>det (matrix g)\<bar> *\<^sub>R integral S (f \<circ> g)"
sorry

subsection\<open>Change of variable for measure\<close>

lemma has_measure_differentiable_image:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<and> measure lebesgue (f ` S) = m
     \<longleftrightarrow> ((\<lambda>x. \<bar>det (matrix (f' x))\<bar>) has_integral m) S"
sorry

lemma measurable_differentiable_image_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
      and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
sorry

lemma measurable_differentiable_image_alt:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes "S \<in> sets lebesgue"
    and "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and "inj_on f S"
  shows "f ` S \<in> lmeasurable \<longleftrightarrow> (\<lambda>x. \<bar>det (matrix (f' x))\<bar>) absolutely_integrable_on S"
sorry

lemma measure_differentiable_image_eq:
  fixes f :: "real^'n::{finite,wellorder} \<Rightarrow> real^'n::_"
  assumes S: "S \<in> sets lebesgue"
    and der_f: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and inj: "inj_on f S"
    and intS: "(\<lambda>x. \<bar>det (matrix (f' x))\<bar>) integrable_on S"
  shows "measure lebesgue (f ` S) = integral S (\<lambda>x. \<bar>det (matrix (f' x))\<bar>)"
sorry

end
