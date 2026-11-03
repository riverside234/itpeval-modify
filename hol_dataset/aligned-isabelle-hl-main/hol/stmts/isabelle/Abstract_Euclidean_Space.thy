(*  Author:  LCP, ported from HOL Light
*)

section\<open>Euclidean space and n-spheres, as subtopologies of n-dimensional space\<close>

theory Abstract_Euclidean_Space
imports Homotopy Locally
begin

subsection \<open>Euclidean spaces as abstract topologies\<close>

definition Euclidean_space :: "nat \<Rightarrow> (nat \<Rightarrow> real) topology"
  where "Euclidean_space n \<equiv> subtopology (powertop_real UNIV) {x. \<forall>i\<ge>n. x i = 0}"

lemma topspace_Euclidean_space:
   "topspace(Euclidean_space n) = {x. \<forall>i\<ge>n. x i = 0}"
sorry

lemma nontrivial_Euclidean_space: "Euclidean_space n \<noteq> trivial_topology"
sorry

lemma subset_Euclidean_space [simp]:
   "topspace(Euclidean_space m) \<subseteq> topspace(Euclidean_space n) \<longleftrightarrow> m \<le> n"
sorry

lemma topspace_Euclidean_space_alt:
  "topspace(Euclidean_space n) = (\<Inter>i \<in> {n..}. {x. x \<in> topspace(powertop_real UNIV) \<and> x i \<in> {0}})"
sorry

lemma closedin_Euclidean_space:
  "closedin (powertop_real UNIV) (topspace(Euclidean_space n))"
sorry

lemma closedin_Euclidean_imp_closed: "closedin (Euclidean_space m) S \<Longrightarrow> closed S"
sorry

lemma closedin_Euclidean_space_iff:
  "closedin (Euclidean_space m) S \<longleftrightarrow> closed S \<and> S \<subseteq> topspace (Euclidean_space m)"
  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma continuous_map_componentwise_Euclidean_space:
  "continuous_map X (Euclidean_space n) (\<lambda>x i. if i < n then f x i else 0) \<longleftrightarrow>
   (\<forall>i < n. continuous_map X euclideanreal (\<lambda>x. f x i))"
sorry

lemma continuous_map_Euclidean_space_add [continuous_intros]:
   "\<lbrakk>continuous_map X (Euclidean_space n) f; continuous_map X (Euclidean_space n) g\<rbrakk>
    \<Longrightarrow> continuous_map X (Euclidean_space n) (\<lambda>x i. f x i + g x i)"
sorry

lemma continuous_map_Euclidean_space_diff [continuous_intros]:
   "\<lbrakk>continuous_map X (Euclidean_space n) f; continuous_map X (Euclidean_space n) g\<rbrakk>
    \<Longrightarrow> continuous_map X (Euclidean_space n) (\<lambda>x i. f x i - g x i)"
sorry

lemma continuous_map_Euclidean_space_iff:
  "continuous_map (Euclidean_space m) euclidean g
   = continuous_on (topspace (Euclidean_space m)) g"
sorry

lemma cm_Euclidean_space_iff_continuous_on:
  "continuous_map (subtopology (Euclidean_space m) S) (Euclidean_space n) f
   \<longleftrightarrow> continuous_on (topspace (subtopology (Euclidean_space m) S)) f \<and>
       f \<in> (topspace (subtopology (Euclidean_space m) S)) \<rightarrow> topspace (Euclidean_space n)"
  (is "?P \<longleftrightarrow> ?Q \<and> ?R")
sorry

lemma homeomorphic_Euclidean_space_product_topology:
  "Euclidean_space n homeomorphic_space product_topology (\<lambda>i. euclideanreal) {..<n}"
sorry

lemma contractible_Euclidean_space [simp]: "contractible_space (Euclidean_space n)"
sorry

lemma path_connected_Euclidean_space: "path_connected_space (Euclidean_space n)"
sorry

lemma connected_Euclidean_space: "connected_space (Euclidean_space n)"
sorry

lemma locally_path_connected_Euclidean_space:
   "locally_path_connected_space (Euclidean_space n)"
sorry

lemma compact_Euclidean_space [simp]:
   "compact_space (Euclidean_space n) \<longleftrightarrow> n = 0"
sorry

subsection\<open>n-dimensional spheres\<close>

definition nsphere where
 "nsphere n \<equiv> subtopology (Euclidean_space (Suc n)) { x. (\<Sum>i\<le>n. x i ^ 2) = 1 }"

lemma nsphere:
   "nsphere n = subtopology (powertop_real UNIV)
                            {x. (\<Sum>i\<le>n. x i ^ 2) = 1 \<and> (\<forall>i>n. x i = 0)}"
sorry

lemma continuous_map_nsphere_projection: "continuous_map (nsphere n) euclideanreal (\<lambda>x. x k)"
sorry

lemma in_topspace_nsphere: "(\<lambda>n. if n = 0 then 1 else 0) \<in> topspace (nsphere n)"
sorry

lemma nonempty_nsphere [simp]: "(nsphere n) \<noteq> trivial_topology"
sorry

lemma subtopology_nsphere_equator:
  "subtopology (nsphere (Suc n)) {x. x(Suc n) = 0} = nsphere n"
sorry

lemma topspace_nsphere_minus1:
  assumes x: "x \<in> topspace (nsphere n)" and "x n = 0"
  shows "x \<in> topspace (nsphere (n - Suc 0))"
sorry

lemma continuous_map_nsphere_reflection:
  "continuous_map (nsphere n) (nsphere n) (\<lambda>x i. if i = k then -x i else x i)"
sorry

proposition contractible_space_upper_hemisphere:
  assumes "k \<le> n"
  shows "contractible_space(subtopology (nsphere n) {x. x k \<ge> 0})"
sorry

corollary contractible_space_lower_hemisphere:
  assumes "k \<le> n"
  shows "contractible_space(subtopology (nsphere n) {x. x k \<le> 0})"
sorry

proposition nullhomotopic_nonsurjective_sphere_map:
  assumes f: "continuous_map (nsphere p) (nsphere p) f"
    and fim: "f ` (topspace(nsphere p)) \<noteq> topspace(nsphere p)"
  obtains a where "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) f (\<lambda>x. a)"
sorry

lemma Hausdorff_Euclidean_space:
   "Hausdorff_space (Euclidean_space n)"
sorry

end
