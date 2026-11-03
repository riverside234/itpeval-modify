(*  Title:      HOL/Analysis/Arcwise_Connected.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>Arcwise-Connected Sets\<close>

theory Arcwise_Connected
imports Path_Connected Ordered_Euclidean_Space "HOL-Computational_Algebra.Primes"
begin

lemma path_connected_interval [simp]:
  fixes a b::"'a::ordered_euclidean_space"
  shows "path_connected {a..b}"
sorry

lemma segment_to_closest_point:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>closed S; S \<noteq> {}\<rbrakk> \<Longrightarrow> open_segment a (closest_point S a) \<inter> S = {}"
sorry

lemma segment_to_point_exists:
  fixes S :: "'a :: euclidean_space set"
    assumes "closed S" "S \<noteq> {}"
    obtains b where "b \<in> S" "open_segment a b \<inter> S = {}"
sorry

subsection \<open>The Brouwer reduction theorem\<close>

theorem Brouwer_reduction_theorem_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "closed S" "\<phi> S"
      and \<phi>: "\<And>F. \<lbrakk>\<And>n. closed(F n); \<And>n. \<phi>(F n); \<And>n. F(Suc n) \<subseteq> F n\<rbrakk> \<Longrightarrow> \<phi>(\<Inter>(range F))"
  obtains T where "T \<subseteq> S" "closed T" "\<phi> T" "\<And>U. \<lbrakk>U \<subseteq> S; closed U; \<phi> U\<rbrakk> \<Longrightarrow> \<not> (U \<subset> T)"
sorry

corollary Brouwer_reduction_theorem:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "\<phi> S" "S \<noteq> {}"
      and \<phi>: "\<And>F. \<lbrakk>\<And>n. compact(F n); \<And>n. F n \<noteq> {}; \<And>n. \<phi>(F n); \<And>n. F(Suc n) \<subseteq> F n\<rbrakk> \<Longrightarrow> \<phi>(\<Inter>(range F))"
  obtains T where "T \<subseteq> S" "compact T" "T \<noteq> {}" "\<phi> T"
                  "\<And>U. \<lbrakk>U \<subseteq> S; closed U; U \<noteq> {}; \<phi> U\<rbrakk> \<Longrightarrow> \<not> (U \<subset> T)"
sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Arcwise Connections\<close>(*FIX ME this subsection is empty(?) *)

subsection\<open>Density of points with dyadic rational coordinates\<close>

proposition closure_dyadic_rationals:
    "closure (\<Union>k. \<Union>f \<in> Basis \<rightarrow> \<int>.
                   { \<Sum>i :: 'a :: euclidean_space \<in> Basis. (f i / 2^k) *\<^sub>R i }) = UNIV"
sorry

corollary closure_rational_coordinates:
    "closure (\<Union>f \<in> Basis \<rightarrow> \<rat>. { \<Sum>i :: 'a :: euclidean_space \<in> Basis. f i *\<^sub>R i }) = UNIV"
sorry

lemma closure_dyadic_rationals_in_convex_set:
   "\<lbrakk>convex S; interior S \<noteq> {}\<rbrakk>
        \<Longrightarrow> closure(S \<inter>
                    (\<Union>k. \<Union>f \<in> Basis \<rightarrow> \<int>.
                   { \<Sum>i :: 'a :: euclidean_space \<in> Basis. (f i / 2^k) *\<^sub>R i })) =
            closure S"
sorry

lemma closure_rationals_in_convex_set:
   "\<lbrakk>convex S; interior S \<noteq> {}\<rbrakk>
    \<Longrightarrow> closure(S \<inter> (\<Union>f \<in> Basis \<rightarrow> \<rat>. { \<Sum>i :: 'a :: euclidean_space \<in> Basis. f i *\<^sub>R i })) =
        closure S"
sorry

text\<open> Every path between distinct points contains an arc, and hence
path connection is equivalent to arcwise connection for distinct points.
The proof is based on Whyburn's "Topological Analysis".\<close>

lemma closure_dyadic_rationals_in_convex_set_pos_1:
  fixes S :: "real set"
  assumes "convex S" and intnz: "interior S \<noteq> {}" and pos: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> x"
    shows "closure(S \<inter> (\<Union>k m. {of_nat m / 2^k})) = closure S"
sorry


definition\<^marker>\<open>tag unimportant\<close> dyadics :: "'a::field_char_0 set" where "dyadics \<equiv> \<Union>k m. {of_nat m / 2^k}"

lemma real_in_dyadics [simp]: "real m \<in> dyadics"
sorry

lemma nat_neq_4k1: "of_nat m \<noteq> (4 * of_nat k + 1) / (2 * 2^n :: 'a::field_char_0)"
sorry

lemma nat_neq_4k3: "of_nat m \<noteq> (4 * of_nat k + 3) / (2 * 2^n :: 'a::field_char_0)"
sorry

lemma iff_4k:
  assumes "r = real k" "odd k"
    shows "(4 * real m + r) / (2 * 2^n) = (4 * real m' + r) / (2 * 2 ^ n') \<longleftrightarrow> m=m' \<and> n=n'"
sorry

lemma neq_4k1_k43: "(4 * real m + 1) / (2 * 2^n) \<noteq> (4 * real m' + 3) / (2 * 2 ^ n')"
sorry

lemma dyadic_413_cases:
  obtains "(of_nat m::'a::field_char_0) / 2^k \<in> Nats"
  | m' k' where "k' < k" "(of_nat m:: 'a) / 2^k = of_nat (4*m' + 1) / 2^Suc k'"
  | m' k' where "k' < k" "(of_nat m:: 'a) / 2^k = of_nat (4*m' + 3) / 2^Suc k'"
sorry

lemma dyadics_iff:
   "(dyadics :: 'a::field_char_0 set) =
    Nats \<union> (\<Union>k m. {of_nat (4*m + 1) / 2^Suc k}) \<union> (\<Union>k m. {of_nat (4*m + 3) / 2^Suc k})"
           (is "_ = ?rhs")
sorry



function\<^marker>\<open>tag unimportant\<close> (domintros) dyad_rec :: "[nat \<Rightarrow> 'a, 'a\<Rightarrow>'a, 'a\<Rightarrow>'a, real] \<Rightarrow> 'a" where
    "dyad_rec b l r (real m) = b m"
  | "dyad_rec b l r ((4 * real m + 1) / 2 ^ (Suc n)) = l (dyad_rec b l r ((2*m + 1) / 2^n))"
  | "dyad_rec b l r ((4 * real m + 3) / 2 ^ (Suc n)) = r (dyad_rec b l r ((2*m + 1) / 2^n))"
  | "x \<notin> dyadics \<Longrightarrow> dyad_rec b l r x = undefined"
  using iff_4k [of _ 1] iff_4k [of _ 3]
         apply (simp_all add: nat_neq_4k1 nat_neq_4k3 neq_4k1_k43 dyadics_iff Nats_def)
  by (fastforce simp:  field_simps)+

lemma dyadics_levels: "dyadics = (\<Union>K. \<Union>k<K. \<Union> m. {of_nat m / 2^k})"
sorry

lemma dyad_rec_level_termination:
  assumes "k < K"
  shows "dyad_rec_dom(b, l, r, real m / 2^k)"
sorry

lemma dyad_rec_termination: "x \<in> dyadics \<Longrightarrow> dyad_rec_dom(b,l,r,x)"
sorry

lemma dyad_rec_of_nat [simp]: "dyad_rec b l r (real m) = b m"
sorry

lemma dyad_rec_41 [simp]: "dyad_rec b l r ((4 * real m + 1) / 2 ^ (Suc n)) = l (dyad_rec b l r ((2*m + 1) / 2^n))"
sorry

lemma dyad_rec_43 [simp]: "dyad_rec b l r ((4 * real m + 3) / 2 ^ (Suc n)) = r (dyad_rec b l r ((2*m + 1) / 2^n))"
sorry

lemma dyad_rec_41_times2:
  assumes "n > 0"
    shows "dyad_rec b l r (2 * ((4 * real m + 1) / 2^Suc n)) = l (dyad_rec b l r (2 * (2 * real m + 1) / 2^n))"
sorry

lemma dyad_rec_43_times2:
  assumes "n > 0"
    shows "dyad_rec b l r (2 * ((4 * real m + 3) / 2^Suc n)) = r (dyad_rec b l r (2 * (2 * real m + 1) / 2^n))"
sorry

definition\<^marker>\<open>tag unimportant\<close> dyad_rec2
    where "dyad_rec2 u v lc rc x =
             dyad_rec (\<lambda>z. (u,v)) (\<lambda>(a,b). (a, lc a b (midpoint a b))) (\<lambda>(a,b). (rc a b (midpoint a b), b)) (2*x)"

abbreviation\<^marker>\<open>tag unimportant\<close> leftrec where "leftrec u v lc rc x \<equiv> fst (dyad_rec2 u v lc rc x)"
abbreviation\<^marker>\<open>tag unimportant\<close> rightrec where "rightrec u v lc rc x \<equiv> snd (dyad_rec2 u v lc rc x)"

lemma leftrec_base: "leftrec u v lc rc (real m / 2) = u"
sorry

lemma leftrec_41: "n > 0 \<Longrightarrow> leftrec u v lc rc ((4 * real m + 1) / 2 ^ (Suc n)) = leftrec u v lc rc ((2 * real m + 1) / 2^n)"
sorry

lemma leftrec_43: "n > 0 \<Longrightarrow>
             leftrec u v lc rc ((4 * real m + 3) / 2 ^ (Suc n)) =
                 rc (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n))
                 (midpoint (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n)))"
sorry

lemma rightrec_base: "rightrec u v lc rc (real m / 2) = v"
sorry

lemma rightrec_41: "n > 0 \<Longrightarrow>
             rightrec u v lc rc ((4 * real m + 1) / 2 ^ (Suc n)) =
                 lc (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n))
                 (midpoint (leftrec u v lc rc ((2 * real m + 1) / 2^n)) (rightrec u v lc rc ((2 * real m + 1) / 2^n)))"
sorry

lemma rightrec_43: "n > 0 \<Longrightarrow> rightrec u v lc rc ((4 * real m + 3) / 2 ^ (Suc n)) = rightrec u v lc rc ((2 * real m + 1) / 2^n)"
sorry

lemma dyadics_in_open_unit_interval:
   "{0<..<1} \<inter> (\<Union>k m. {real m / 2^k}) = (\<Union>k. \<Union>m \<in> {0<..<2^k}. {real m / 2^k})"
sorry

lemma padic_rational_approximation_straddle:
  assumes "\<epsilon> > 0" "p > 1"
  obtains n q r 
    where "of_int q / p^n < x" "x < of_int r / p^n" "\<bar>q / p^n - r / p^n \<bar> < \<epsilon>"
sorry

lemma padic_rational_approximation_straddle_pos:
  assumes "\<epsilon> > 0" "p > 1" "x > 0"
  obtains n q r 
    where "of_nat q / p^n < x" "x < of_nat r / p^n" "\<bar>q / p^n - r / p^n \<bar> < \<epsilon>"
sorry

lemma padic_rational_approximation_straddle_pos_le:
  assumes "\<epsilon> > 0" "p > 1" "x \<ge> 0"
  obtains n q r 
    where "of_nat q / p^n \<le> x" "x < of_nat r / p^n" "\<bar>q / p^n - r / p^n \<bar> < \<epsilon>"
sorry


subsubsection \<open>Definition by recursion on dyadic rationals in [0,1]\<close>

lemma recursion_on_dyadic_fractions:
  assumes base: "R a b"
    and step: "\<And>x y. R x y \<Longrightarrow> \<exists>z. R x z \<and> R z y" and trans: "\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
  shows "\<exists>f :: real \<Rightarrow> 'a. f 0 = a \<and> f 1 = b \<and>
               (\<forall>x \<in> dyadics \<inter> {0..1}. \<forall>y \<in> dyadics \<inter> {0..1}. x < y \<longrightarrow> R (f x) (f y))"
sorry

lemma dyadics_add:
  assumes "x \<in> dyadics" "y \<in> dyadics"
  shows "x+y \<in> dyadics"
sorry

lemma dyadics_diff:
  fixes x :: "'a::linordered_field"
  assumes "x \<in> dyadics" "y \<in> dyadics" "y \<le> x"
  shows "x-y \<in> dyadics"
sorry

theorem homeomorphic_monotone_image_interval:
  fixes f :: "real \<Rightarrow> 'a::{real_normed_vector,complete_space}"
  assumes cont_f: "continuous_on {0..1} f"
      and conn: "\<And>y. connected ({0..1} \<inter> f -` {y})"
      and f_1not0: "f 1 \<noteq> f 0"
    shows "(f ` {0..1}) homeomorphic {0..1::real}"
sorry

theorem path_contains_arc:
  fixes p :: "real \<Rightarrow> 'a::{complete_space,real_normed_vector}"
  assumes "path p" and a: "pathstart p = a" and b: "pathfinish p = b" and "a \<noteq> b"
  obtains q where "arc q" "path_image q \<subseteq> path_image p" "pathstart q = a" "pathfinish q = b"
sorry

corollary path_connected_arcwise:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  shows "path_connected S \<longleftrightarrow>
         (\<forall>x \<in> S. \<forall>y \<in> S. x \<noteq> y \<longrightarrow> (\<exists>g. arc g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y))"
        (is "?lhs = ?rhs")
sorry

corollary arc_connected_trans:
  fixes g :: "real \<Rightarrow> 'a::{complete_space,real_normed_vector}"
  assumes "arc g" "arc h" "pathfinish g = pathstart h" "pathstart g \<noteq> pathfinish h"
  obtains i where "arc i" "path_image i \<subseteq> path_image g \<union> path_image h"
                  "pathstart i = pathstart g" "pathfinish i = pathfinish h"
sorry

subsection\<open>Accessibility of frontier points\<close>

lemma dense_accessible_frontier_points:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes "open S" and opeSV: "openin (top_of_set (frontier S)) V" and "V \<noteq> {}"
  obtains g where "arc g" "g ` {0..<1} \<subseteq> S" "pathstart g \<in> S" "pathfinish g \<in> V"
sorry

lemma dense_accessible_frontier_points_connected:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes "open S" "connected S" "x \<in> S" "V \<noteq> {}"
      and ope: "openin (top_of_set (frontier S)) V"
  obtains g where "arc g" "g ` {0..<1} \<subseteq> S" "pathstart g = x" "pathfinish g \<in> V"
sorry

lemma dense_access_fp_aux:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes S: "open S" "connected S"
      and opeSU: "openin (top_of_set (frontier S)) U"
      and opeSV: "openin (top_of_set (frontier S)) V"
      and "V \<noteq> {}" "\<not> U \<subseteq> V"
  obtains g where "arc g" "pathstart g \<in> U" "pathfinish g \<in> V" "g ` {0<..<1} \<subseteq> S"
sorry

lemma dense_accessible_frontier_point_pairs:
  fixes S :: "'a::{complete_space,real_normed_vector} set"
  assumes S: "open S" "connected S"
      and opeSU: "openin (top_of_set (frontier S)) U"
      and opeSV: "openin (top_of_set (frontier S)) V"
      and "U \<noteq> {}" "V \<noteq> {}" "U \<noteq> V"
    obtains g where "arc g" "pathstart g \<in> U" "pathfinish g \<in> V" "g ` {0<..<1} \<subseteq> S"
sorry

end
