(*  Author:     L C Paulson, University of Cambridge [ported from HOL Light, metric.ml] *)

section \<open>$F$-Sigma and $G$-Delta sets in a Topological Space\<close>

text \<open>An $F$-sigma set is a countable union of closed sets; a $G$-delta set is the dual.\<close>

theory FSigma
  imports Abstract_Topology
begin


definition fsigma_in 
  where "fsigma_in X \<equiv> countable union_of closedin X"

definition gdelta_in 
  where "gdelta_in X \<equiv> (countable intersection_of openin X) relative_to topspace X"

lemma fsigma_in_ascending:
   "fsigma_in X S \<longleftrightarrow> (\<exists>C. (\<forall>n. closedin X (C n)) \<and> (\<forall>n. C n \<subseteq> C(Suc n)) \<and> \<Union> (range C) = S)"
sorry

lemma gdelta_in_alt:
   "gdelta_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> (countable intersection_of openin X) S"
sorry

lemma fsigma_in_subset: "fsigma_in X S \<Longrightarrow> S \<subseteq> topspace X"
sorry

lemma gdelta_in_subset: "gdelta_in X S \<Longrightarrow> S \<subseteq> topspace X"
sorry

lemma closed_imp_fsigma_in: "closedin X S \<Longrightarrow> fsigma_in X S"
sorry

lemma open_imp_gdelta_in: "openin X S \<Longrightarrow> gdelta_in X S"
sorry

lemma fsigma_in_empty [iff]: "fsigma_in X {}"
sorry

lemma gdelta_in_empty [iff]: "gdelta_in X {}"
sorry

lemma fsigma_in_topspace [iff]: "fsigma_in X (topspace X)"
sorry

lemma gdelta_in_topspace [iff]: "gdelta_in X (topspace X)"
sorry

lemma fsigma_in_Union:
   "\<lbrakk>countable T; \<And>S. S \<in> T \<Longrightarrow> fsigma_in X S\<rbrakk> \<Longrightarrow> fsigma_in X (\<Union> T)"
sorry

lemma fsigma_in_Un:
   "\<lbrakk>fsigma_in X S; fsigma_in X T\<rbrakk> \<Longrightarrow> fsigma_in X (S \<union> T)"
sorry

lemma fsigma_in_Int:
   "\<lbrakk>fsigma_in X S; fsigma_in X T\<rbrakk> \<Longrightarrow> fsigma_in X (S \<inter> T)"
sorry

lemma gdelta_in_Inter:
   "\<lbrakk>countable T; T\<noteq>{}; \<And>S. S \<in> T \<Longrightarrow> gdelta_in X S\<rbrakk> \<Longrightarrow> gdelta_in X (\<Inter> T)"
sorry

lemma gdelta_in_Int:
   "\<lbrakk>gdelta_in X S; gdelta_in X T\<rbrakk> \<Longrightarrow> gdelta_in X (S \<inter> T)"
sorry

lemma gdelta_in_Un:
   "\<lbrakk>gdelta_in X S; gdelta_in X T\<rbrakk> \<Longrightarrow> gdelta_in X (S \<union> T)"
sorry

lemma fsigma_in_diff:
  assumes "fsigma_in X S" "gdelta_in X T"
  shows "fsigma_in X (S - T)"
sorry

lemma gdelta_in_diff:
  assumes "gdelta_in X S" "fsigma_in X T"
  shows "gdelta_in X (S - T)"
sorry

lemma gdelta_in_fsigma_in:
   "gdelta_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> fsigma_in X (topspace X - S)"
sorry

lemma fsigma_in_gdelta_in:
   "fsigma_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> gdelta_in X (topspace X - S)"
sorry

lemma gdelta_in_descending:
   "gdelta_in X S \<longleftrightarrow> (\<exists>C. (\<forall>n. openin X (C n)) \<and> (\<forall>n. C(Suc n) \<subseteq> C n) \<and> \<Inter>(range C) = S)" (is "?lhs=?rhs")
sorry

lemma homeomorphic_map_fsigmaness:
  assumes f: "homeomorphic_map X Y f" and "U \<subseteq> topspace X"
  shows "fsigma_in Y (f ` U) \<longleftrightarrow> fsigma_in X U"  (is "?lhs=?rhs")
sorry

lemma homeomorphic_map_fsigmaness_eq:
   "homeomorphic_map X Y f
        \<Longrightarrow> (fsigma_in X U \<longleftrightarrow> U \<subseteq> topspace X \<and> fsigma_in Y (f ` U))"
sorry

lemma homeomorphic_map_gdeltaness:
  assumes "homeomorphic_map X Y f" "U \<subseteq> topspace X"
  shows "gdelta_in Y (f ` U) \<longleftrightarrow> gdelta_in X U"
sorry

lemma homeomorphic_map_gdeltaness_eq:
   "homeomorphic_map X Y f
    \<Longrightarrow> gdelta_in X U \<longleftrightarrow> U \<subseteq> topspace X \<and> gdelta_in Y (f ` U)"
sorry

lemma fsigma_in_relative_to:
   "(fsigma_in X relative_to S) = fsigma_in (subtopology X S)"
sorry

lemma fsigma_in_subtopology:
   "fsigma_in (subtopology X U) S \<longleftrightarrow> (\<exists>T. fsigma_in X T \<and> S = T \<inter> U)"
sorry

lemma gdelta_in_relative_to:
   "(gdelta_in X relative_to S) = gdelta_in (subtopology X S)"
sorry

lemma gdelta_in_subtopology:
   "gdelta_in (subtopology X U) S \<longleftrightarrow> (\<exists>T. gdelta_in X T \<and> S = T \<inter> U)"
sorry

lemma fsigma_in_fsigma_subtopology:
   "fsigma_in X S \<Longrightarrow> (fsigma_in (subtopology X S) T \<longleftrightarrow> fsigma_in X T \<and> T \<subseteq> S)"
sorry

lemma gdelta_in_gdelta_subtopology:
   "gdelta_in X S \<Longrightarrow> (gdelta_in (subtopology X S) T \<longleftrightarrow> gdelta_in X T \<and> T \<subseteq> S)"
sorry

end
