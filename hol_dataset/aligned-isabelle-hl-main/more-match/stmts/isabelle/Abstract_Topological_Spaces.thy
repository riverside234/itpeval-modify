(*  Author:     L C Paulson, University of Cambridge [ported from HOL Light] *)

section \<open>Various Forms of Topological Spaces\<close>

theory Abstract_Topological_Spaces
  imports Lindelof_Spaces Locally Abstract_Euclidean_Space Sum_Topology FSigma
begin


subsection\<open>Connected topological spaces\<close>

lemma connected_space_eq_frontier_eq_empty:
   "connected_space X \<longleftrightarrow> (\<forall>S. S \<subseteq> topspace X \<and> X frontier_of S = {} \<longrightarrow> S = {} \<or> S = topspace X)"
sorry

lemma connected_space_frontier_eq_empty:
   "connected_space X \<and> S \<subseteq> topspace X
        \<Longrightarrow> (X frontier_of S = {} \<longleftrightarrow> S = {} \<or> S = topspace X)"
sorry

lemma connectedin_eq_subset_separated_union:
   "connectedin X C \<longleftrightarrow>
        C \<subseteq> topspace X \<and> (\<forall>S T. separatedin X S T \<and> C \<subseteq> S \<union> T \<longrightarrow> C \<subseteq> S \<or> C \<subseteq> T)" (is "?lhs=?rhs")
sorry

lemma connectedin_clopen_cases:
   "\<lbrakk>connectedin X C; closedin X T; openin X T\<rbrakk> \<Longrightarrow> C \<subseteq> T \<or> disjnt C T"
sorry

lemma connected_space_retraction_map_image:
   "\<lbrakk>retraction_map X X' r; connected_space X\<rbrakk> \<Longrightarrow> connected_space X'"
sorry

lemma connectedin_imp_perfect_gen:
  assumes X: "t1_space X" and S: "connectedin X S" and nontriv: "\<nexists>a. S = {a}"
  shows "S \<subseteq> X derived_set_of S"
sorry

lemma connectedin_imp_perfect:
  "\<lbrakk>Hausdorff_space X; connectedin X S; \<nexists>a. S = {a}\<rbrakk> \<Longrightarrow> S \<subseteq> X derived_set_of S"
sorry

subsection\<open>The notion of "separated between" (complement of "connected between)"\<close>

definition separated_between 
  where "separated_between X S T \<equiv>
        \<exists>U V. openin X U \<and> openin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> S \<subseteq> U \<and> T \<subseteq> V"

lemma separated_between_alt:
   "separated_between X S T \<longleftrightarrow>
        (\<exists>U V. closedin X U \<and> closedin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> S \<subseteq> U \<and> T \<subseteq> V)"
sorry

lemma separated_between:
   "separated_between X S T \<longleftrightarrow>
        (\<exists>U. closedin X U \<and> openin X U \<and> S \<subseteq> U \<and> T \<subseteq> topspace X - U)"
sorry

lemma separated_between_mono:
   "\<lbrakk>separated_between X S T; S' \<subseteq> S; T' \<subseteq> T\<rbrakk> \<Longrightarrow> separated_between X S' T'"
sorry

lemma separated_between_refl:
   "separated_between X S S \<longleftrightarrow> S = {}"
sorry

lemma separated_between_sym:
   "separated_between X S T \<longleftrightarrow> separated_between X T S"
sorry

lemma separated_between_imp_subset:
   "separated_between X S T \<Longrightarrow> S \<subseteq> topspace X \<and> T \<subseteq> topspace X"
sorry

lemma separated_between_empty: 
  "(separated_between X {} S \<longleftrightarrow> S \<subseteq> topspace X) \<and> (separated_between X S {} \<longleftrightarrow> S \<subseteq> topspace X)"
sorry

lemma separated_between_Un: 
  "separated_between X S (T \<union> U) \<longleftrightarrow> separated_between X S T \<and> separated_between X S U"
sorry

lemma separated_between_Un': 
  "separated_between X (S \<union> T) U \<longleftrightarrow> separated_between X S U \<and> separated_between X T U"
sorry

lemma separated_between_imp_disjoint:
   "separated_between X S T \<Longrightarrow> disjnt S T"
sorry

lemma separated_between_imp_separatedin:
   "separated_between X S T \<Longrightarrow> separatedin X S T"
sorry

lemma separated_between_full:
  assumes "S \<union> T = topspace X"
  shows "separated_between X S T \<longleftrightarrow> disjnt S T \<and> closedin X S \<and> openin X S \<and> closedin X T \<and> openin X T"
sorry

lemma separated_between_eq_separatedin:
   "S \<union> T = topspace X \<Longrightarrow> (separated_between X S T \<longleftrightarrow> separatedin X S T)"
sorry

lemma separated_between_pointwise_left:
  assumes "compactin X S"
  shows "separated_between X S T \<longleftrightarrow>
         (S = {} \<longrightarrow> T \<subseteq> topspace X) \<and> (\<forall>x \<in> S. separated_between X {x} T)"  (is "?lhs=?rhs")
sorry

lemma separated_between_pointwise_right:
   "compactin X T
        \<Longrightarrow> separated_between X S T \<longleftrightarrow> (T = {} \<longrightarrow> S \<subseteq> topspace X) \<and> (\<forall>y \<in> T. separated_between X S {y})"
sorry

lemma separated_between_closure_of:
  "S \<subseteq> topspace X \<Longrightarrow> separated_between X (X closure_of S) T \<longleftrightarrow> separated_between X S T"
sorry

lemma separated_between_closure_of':
 "T \<subseteq> topspace X \<Longrightarrow> separated_between X S (X closure_of T) \<longleftrightarrow> separated_between X S T"
sorry

lemma separated_between_closure_of_eq:
 "separated_between X S T \<longleftrightarrow> S \<subseteq> topspace X \<and> separated_between X (X closure_of S) T"
sorry

lemma separated_between_closure_of_eq':
 "separated_between X S T \<longleftrightarrow> T \<subseteq> topspace X \<and> separated_between X S (X closure_of T)"
sorry

lemma separated_between_frontier_of_eq':
  "separated_between X S T \<longleftrightarrow>
   T \<subseteq> topspace X \<and> disjnt S T \<and> separated_between X S (X frontier_of T)" (is "?lhs=?rhs")
sorry

lemma separated_between_frontier_of_eq:
  "separated_between X S T \<longleftrightarrow> S \<subseteq> topspace X \<and> disjnt S T \<and> separated_between X (X frontier_of S) T"
sorry

lemma separated_between_frontier_of:
  "\<lbrakk>S \<subseteq> topspace X; disjnt S T\<rbrakk>
   \<Longrightarrow> (separated_between X (X frontier_of S) T \<longleftrightarrow> separated_between X S T)"
sorry

lemma separated_between_frontier_of':
 "\<lbrakk>T \<subseteq> topspace X; disjnt S T\<rbrakk>
   \<Longrightarrow> (separated_between X S (X frontier_of T) \<longleftrightarrow> separated_between X S T)"
sorry

lemma connected_space_separated_between:
  "connected_space X \<longleftrightarrow> (\<forall>S T. separated_between X S T \<longrightarrow> S = {} \<or> T = {})" (is "?lhs=?rhs")
sorry

lemma connected_space_imp_separated_between_trivial:
   "connected_space X
        \<Longrightarrow> (separated_between X S T \<longleftrightarrow> S = {} \<and> T \<subseteq> topspace X \<or> S \<subseteq> topspace X \<and> T = {})"
sorry
subsection\<open>Connected components\<close>

lemma connected_component_of_subtopology_eq:
   "connected_component_of (subtopology X U) a = connected_component_of X a \<longleftrightarrow>
    connected_component_of_set X a \<subseteq> U"
sorry

lemma connected_components_of_subtopology:
  assumes "C \<in> connected_components_of X" "C \<subseteq> U"
  shows "C \<in> connected_components_of (subtopology X U)"
sorry

lemma open_in_finite_connected_components:
  assumes "finite(connected_components_of X)" "C \<in> connected_components_of X"
  shows "openin X C"
sorry

thm connected_component_of_eq_overlap

lemma connected_components_of_disjoint:
  assumes "C \<in> connected_components_of X" "C' \<in> connected_components_of X"
    shows "(disjnt C C' \<longleftrightarrow> (C \<noteq> C'))"
sorry

lemma connected_components_of_overlap:
   "\<lbrakk>C \<in> connected_components_of X; C' \<in> connected_components_of X\<rbrakk> \<Longrightarrow> C \<inter> C' \<noteq> {} \<longleftrightarrow> C = C'"
sorry

lemma pairwise_separated_connected_components_of:
   "pairwise (separatedin X) (connected_components_of X)"
sorry

lemma finite_connected_components_of_finite:
   "finite(topspace X) \<Longrightarrow> finite(connected_components_of X)"
sorry

lemma connected_component_of_unique:
   "\<lbrakk>x \<in> C; connectedin X C; \<And>C'. x \<in> C' \<and> connectedin X C' \<Longrightarrow> C' \<subseteq> C\<rbrakk>
        \<Longrightarrow> connected_component_of_set X x = C"
sorry

lemma closedin_connected_component_of_subtopology:
   "\<lbrakk>C \<in> connected_components_of (subtopology X s); X closure_of C \<subseteq> s\<rbrakk> \<Longrightarrow> closedin X C"
sorry

lemma connected_component_of_discrete_topology:
   "connected_component_of_set (discrete_topology U) x = (if x \<in> U then {x} else {})"
sorry

lemma connected_components_of_discrete_topology:
   "connected_components_of (discrete_topology U) = (\<lambda>x. {x}) ` U"
sorry

lemma connected_component_of_continuous_image:
   "\<lbrakk>continuous_map X Y f; connected_component_of X x y\<rbrakk>
        \<Longrightarrow> connected_component_of Y (f x) (f y)"
sorry

lemma homeomorphic_map_connected_component_of:
  assumes "homeomorphic_map X Y f" and x: "x \<in> topspace X"
  shows "connected_component_of_set Y (f x) = f ` (connected_component_of_set X x)"
sorry

lemma homeomorphic_map_connected_components_of:
  assumes "homeomorphic_map X Y f"
  shows "connected_components_of Y = (image f) ` (connected_components_of X)"
sorry

lemma connected_component_of_pair:
   "connected_component_of_set (prod_topology X Y) (x,y) =
        connected_component_of_set X x \<times> connected_component_of_set Y y"
sorry

lemma connected_components_of_prod_topology:
  "connected_components_of (prod_topology X Y) =
    {C \<times> D |C D. C \<in> connected_components_of X \<and> D \<in> connected_components_of Y}" (is "?lhs=?rhs")
sorry

lemma connected_component_of_product_topology:
   "connected_component_of_set (product_topology X I) x =
    (if x \<in> extensional I then PiE I (\<lambda>i. connected_component_of_set (X i) (x i)) else {})"
    (is "?lhs = If _ ?R _")
sorry

lemma connected_components_of_product_topology:
   "connected_components_of (product_topology X I) =
    {PiE I B |B. \<forall>i \<in> I. B i \<in> connected_components_of(X i)}"  (is "?lhs=?rhs")
sorry


subsection \<open>Monotone maps (in the general topological sense)\<close>


definition monotone_map 
  where "monotone_map X Y f ==
        f ` (topspace X) \<subseteq> topspace Y \<and>
        (\<forall>y \<in> topspace Y. connectedin X {x \<in> topspace X. f x = y})"

lemma monotone_map:
  "monotone_map X Y f \<longleftrightarrow>
   f ` (topspace X) \<subseteq> topspace Y \<and> (\<forall>y. connectedin X {x \<in> topspace X. f x = y})"
sorry

lemma monotone_map_in_subtopology:
   "monotone_map X (subtopology Y S) f \<longleftrightarrow> monotone_map X Y f \<and> f ` (topspace X) \<subseteq> S"
sorry

lemma monotone_map_from_subtopology:
  assumes "monotone_map X Y f" 
    "\<And>x y. \<lbrakk>x \<in> topspace X; y \<in> topspace X; x \<in> S; f x = f y\<rbrakk> \<Longrightarrow> y \<in> S"
  shows "monotone_map (subtopology X S) Y f"
sorry

lemma monotone_map_restriction:
  "monotone_map X Y f \<and> {x \<in> topspace X. f x \<in> v} = u
        \<Longrightarrow> monotone_map (subtopology X u) (subtopology Y v) f"
sorry

lemma injective_imp_monotone_map:
  assumes "f ` topspace X \<subseteq> topspace Y"  "inj_on f (topspace X)"
  shows "monotone_map X Y f"
sorry

lemma embedding_imp_monotone_map:
   "embedding_map X Y f \<Longrightarrow> monotone_map X Y f"
sorry

lemma section_imp_monotone_map:
   "section_map X Y f \<Longrightarrow> monotone_map X Y f"
sorry

lemma homeomorphic_imp_monotone_map:
   "homeomorphic_map X Y f \<Longrightarrow> monotone_map X Y f"
sorry

proposition connected_space_monotone_quotient_map_preimage:
  assumes f: "monotone_map X Y f" "quotient_map X Y f" and "connected_space Y"
  shows "connected_space X"
sorry

lemma connectedin_monotone_quotient_map_preimage:
  assumes "monotone_map X Y f" "quotient_map X Y f" "connectedin Y C" "openin Y C \<or> closedin Y C"
  shows "connectedin X {x \<in> topspace X. f x \<in> C}"
sorry

lemma monotone_open_map:
  assumes "continuous_map X Y f" "open_map X Y f" and fim: "f ` (topspace X) = topspace Y"
  shows "monotone_map X Y f \<longleftrightarrow> (\<forall>C. connectedin Y C \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> C})"
         (is "?lhs=?rhs")
sorry

lemma monotone_closed_map:
  assumes "continuous_map X Y f" "closed_map X Y f" and fim: "f ` (topspace X) = topspace Y"
  shows "monotone_map X Y f \<longleftrightarrow> (\<forall>C. connectedin Y C \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> C})" 
         (is "?lhs=?rhs")
sorry

subsection\<open>Other countability properties\<close>

definition second_countable
  where "second_countable X \<equiv>
         \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and>
             (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U))"

definition first_countable
  where "first_countable X \<equiv>
        \<forall>x \<in> topspace X.
         \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and>
             (\<forall>U. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U))"

definition separable_space
  where "separable_space X \<equiv>
        \<exists>C. countable C \<and> C \<subseteq> topspace X \<and> X closure_of C = topspace X"

lemma second_countable:
   "second_countable X \<longleftrightarrow>
        (\<exists>\<B>. countable \<B> \<and> openin X = arbitrary union_of (\<lambda>x. x \<in> \<B>))"
sorry

lemma second_countable_subtopology:
  assumes "second_countable X"
  shows "second_countable (subtopology X S)"
sorry

lemma second_countable_discrete_topology:
   "second_countable(discrete_topology U) \<longleftrightarrow> countable U" (is "?lhs=?rhs")
sorry

lemma second_countable_open_map_image:
  assumes "continuous_map X Y f" "open_map X Y f" 
   and fim: "f ` (topspace X) = topspace Y" and "second_countable X"
 shows "second_countable Y"
sorry

lemma homeomorphic_space_second_countability:
   "X homeomorphic_space Y \<Longrightarrow> (second_countable X \<longleftrightarrow> second_countable Y)"
sorry

lemma second_countable_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; second_countable X\<rbrakk> \<Longrightarrow> second_countable Y"
sorry

lemma second_countable_imp_first_countable:
   "second_countable X \<Longrightarrow> first_countable X"
sorry

lemma first_countable_subtopology:
  assumes "first_countable X"
  shows "first_countable (subtopology X S)"
sorry

lemma first_countable_discrete_topology:
   "first_countable (discrete_topology U)"
sorry

lemma first_countable_open_map_image:
  assumes "continuous_map X Y f" "open_map X Y f" 
   and fim: "f ` (topspace X) = topspace Y" and "first_countable X"
 shows "first_countable Y"
sorry

lemma homeomorphic_space_first_countability:
  "X homeomorphic_space Y \<Longrightarrow> first_countable X \<longleftrightarrow> first_countable Y"
sorry

lemma first_countable_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; first_countable X\<rbrakk> \<Longrightarrow> first_countable Y"
sorry

lemma separable_space_open_subset:
  assumes "separable_space X" "openin X S"
  shows "separable_space (subtopology X S)"
sorry

lemma separable_space_continuous_map_image:
  assumes "separable_space X" "continuous_map X Y f" 
    and fim: "f ` (topspace X) = topspace Y"
  shows "separable_space Y"
sorry

lemma separable_space_quotient_map_image:
  "\<lbrakk>quotient_map X Y q; separable_space X\<rbrakk> \<Longrightarrow> separable_space Y"
sorry

lemma separable_space_retraction_map_image:
  "\<lbrakk>retraction_map X Y r; separable_space X\<rbrakk> \<Longrightarrow> separable_space Y"
sorry

lemma homeomorphic_separable_space:
  "X homeomorphic_space Y \<Longrightarrow> (separable_space X \<longleftrightarrow> separable_space Y)"
sorry

lemma separable_space_discrete_topology:
   "separable_space(discrete_topology U) \<longleftrightarrow> countable U"
sorry

lemma second_countable_imp_separable_space:
  assumes "second_countable X"
  shows "separable_space X"
sorry

lemma second_countable_imp_Lindelof_space:
  assumes "second_countable X"
  shows "Lindelof_space X"
sorry

subsection \<open>Neigbourhood bases EXTRAS\<close>

text \<open>Neigbourhood bases: useful for "local" properties of various kinds\<close>

lemma openin_topology_neighbourhood_base_unique:
   "openin X = arbitrary union_of P \<longleftrightarrow>
        (\<forall>u. P u \<longrightarrow> openin X u) \<and> neighbourhood_base_of P X"
sorry

lemma neighbourhood_base_at_topology_base:
   "        openin X = arbitrary union_of b
        \<Longrightarrow> (neighbourhood_base_at x P X \<longleftrightarrow>
             (\<forall>w. b w \<and> x \<in> w \<longrightarrow> (\<exists>u v. openin X u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w)))"
sorry

lemma neighbourhood_base_of_unlocalized:
  assumes "\<And>S t. P S \<and> openin X t \<and> (t \<noteq> {}) \<and> t \<subseteq> S \<Longrightarrow> P t"
  shows "neighbourhood_base_of P X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>u v. openin X u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> topspace X)"
sorry

lemma neighbourhood_base_at_discrete_topology:
   "neighbourhood_base_at x P (discrete_topology u) \<longleftrightarrow> x \<in> u \<Longrightarrow> P {x}"
sorry

lemma neighbourhood_base_of_discrete_topology:
   "neighbourhood_base_of P (discrete_topology u) \<longleftrightarrow> (\<forall>x \<in> u. P {x})"
sorry

lemma second_countable_neighbourhood_base_alt:
  "second_countable X \<longleftrightarrow> 
  (\<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and> neighbourhood_base_of (\<lambda>A. A\<in>\<B>) X)"
sorry

lemma first_countable_neighbourhood_base_alt:
   "first_countable X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X)"
sorry

lemma second_countable_neighbourhood_base:
   "second_countable X \<longleftrightarrow>
        (\<exists>\<B>. countable \<B> \<and> neighbourhood_base_of (\<lambda>V. V \<in> \<B>) X)" (is "?lhs=?rhs")
sorry

lemma first_countable_neighbourhood_base:
   "first_countable X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<exists>\<B>. countable \<B> \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X)" (is "?lhs=?rhs")
sorry


subsection\<open>$T_0$ spaces and the Kolmogorov quotient\<close>

definition t0_space where
  "t0_space X \<equiv>
     \<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<noteq> y \<longrightarrow> (\<exists>U. openin X U \<and> (x \<notin> U \<longleftrightarrow> y \<in> U))"

lemma t0_space_expansive:
   "\<lbrakk>topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk> \<Longrightarrow> t0_space X \<Longrightarrow> t0_space Y"
sorry

lemma t1_imp_t0_space: "t1_space X \<Longrightarrow> t0_space X"
sorry

lemma t1_eq_symmetric_t0_space_alt:
   "t1_space X \<longleftrightarrow>
      t0_space X \<and>
      (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<in> X closure_of {y} \<longleftrightarrow> y \<in> X closure_of {x})"
sorry

lemma t1_eq_symmetric_t0_space:
  "t1_space X \<longleftrightarrow> t0_space X \<and> (\<forall>x y. x \<in> X closure_of {y} \<longleftrightarrow> y \<in> X closure_of {x})"
sorry

lemma Hausdorff_imp_t0_space:
   "Hausdorff_space X \<Longrightarrow> t0_space X"
sorry

lemma t0_space:
   "t0_space X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<noteq> y \<longrightarrow> (\<exists>C. closedin X C \<and> (x \<notin> C \<longleftrightarrow> y \<in> C)))"
sorry

lemma homeomorphic_t0_space:
  assumes "X homeomorphic_space Y"
  shows "t0_space X \<longleftrightarrow> t0_space Y"
sorry

lemma t0_space_closure_of_sing:
   "t0_space X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. X closure_of {x} = X closure_of {y} \<longrightarrow> x = y)"
sorry

lemma t0_space_discrete_topology: "t0_space (discrete_topology S)"
sorry

lemma t0_space_subtopology: "t0_space X \<Longrightarrow> t0_space (subtopology X U)"
sorry

lemma t0_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; t0_space X\<rbrakk> \<Longrightarrow> t0_space Y"
sorry

lemma t0_space_prod_topologyI: "\<lbrakk>t0_space X; t0_space Y\<rbrakk> \<Longrightarrow> t0_space (prod_topology X Y)"
sorry

lemma t0_space_prod_topology_iff:
   "t0_space (prod_topology X Y) \<longleftrightarrow> prod_topology X Y = trivial_topology \<or> t0_space X \<and> t0_space Y" (is "?lhs=?rhs")
sorry

proposition t0_space_product_topology:
   "t0_space (product_topology X I) \<longleftrightarrow> product_topology X I = trivial_topology \<or> (\<forall>i \<in> I. t0_space (X i))" 
    (is "?lhs=?rhs")
sorry


subsection \<open>Kolmogorov quotients\<close>

definition Kolmogorov_quotient 
  where "Kolmogorov_quotient X \<equiv> \<lambda>x. @y. \<forall>U. openin X U \<longrightarrow> (y \<in> U \<longleftrightarrow> x \<in> U)"

lemma Kolmogorov_quotient_in_open:
   "openin X U \<Longrightarrow> (Kolmogorov_quotient X x \<in> U \<longleftrightarrow> x \<in> U)"
sorry

lemma Kolmogorov_quotient_in_topspace:
   "Kolmogorov_quotient X x \<in> topspace X \<longleftrightarrow> x \<in> topspace X"
sorry

lemma Kolmogorov_quotient_in_closed:
  "closedin X C \<Longrightarrow> (Kolmogorov_quotient X x \<in> C \<longleftrightarrow> x \<in> C)"
sorry

lemma continuous_map_Kolmogorov_quotient:
   "continuous_map X X (Kolmogorov_quotient X)"
sorry

lemma open_map_Kolmogorov_quotient_explicit:
   "openin X U \<Longrightarrow> Kolmogorov_quotient X ` U = Kolmogorov_quotient X ` topspace X \<inter> U"
sorry

lemma open_map_Kolmogorov_quotient_gen:
   "open_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
sorry

lemma open_map_Kolmogorov_quotient:
   "open_map X (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
sorry

lemma closed_map_Kolmogorov_quotient_explicit:
   "closedin X U \<Longrightarrow> Kolmogorov_quotient X ` U = Kolmogorov_quotient X ` topspace X \<inter> U"
sorry

lemma closed_map_Kolmogorov_quotient_gen:
   "closed_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S))
     (Kolmogorov_quotient X)"
sorry

lemma closed_map_Kolmogorov_quotient:
   "closed_map X (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
sorry

lemma quotient_map_Kolmogorov_quotient_gen:
  "quotient_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
sorry

lemma quotient_map_Kolmogorov_quotient:
   "quotient_map X (subtopology X (Kolmogorov_quotient X ` topspace X)) (Kolmogorov_quotient X)"
sorry

lemma Kolmogorov_quotient_eq:
   "Kolmogorov_quotient X x = Kolmogorov_quotient X y \<longleftrightarrow>
    (\<forall>U. openin X U \<longrightarrow> (x \<in> U \<longleftrightarrow> y \<in> U))" (is "?lhs=?rhs")
sorry

lemma Kolmogorov_quotient_eq_alt:
   "Kolmogorov_quotient X x = Kolmogorov_quotient X y \<longleftrightarrow>
    (\<forall>U. closedin X U \<longrightarrow> (x \<in> U \<longleftrightarrow> y \<in> U))" (is "?lhs=?rhs")
sorry

lemma Kolmogorov_quotient_continuous_map:
  assumes "continuous_map X Y f" "t0_space Y" and x: "x \<in> topspace X"
  shows "f (Kolmogorov_quotient X x) = f x"
sorry

lemma t0_space_Kolmogorov_quotient:
  "t0_space (subtopology X (Kolmogorov_quotient X ` topspace X))"
sorry

lemma Kolmogorov_quotient_id:
   "t0_space X \<Longrightarrow> x \<in> topspace X \<Longrightarrow> Kolmogorov_quotient X x = x"
sorry

lemma Kolmogorov_quotient_idemp:
   "Kolmogorov_quotient X (Kolmogorov_quotient X x) = Kolmogorov_quotient X x"
sorry

lemma retraction_maps_Kolmogorov_quotient:
   "retraction_maps X
     (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X) id"
sorry

lemma retraction_map_Kolmogorov_quotient:
   "retraction_map X
     (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
sorry

lemma retract_of_space_Kolmogorov_quotient_image:
   "Kolmogorov_quotient X ` topspace X retract_of_space X"
sorry

lemma Kolmogorov_quotient_lift_exists:
  assumes "S \<subseteq> topspace X" "t0_space Y" and f: "continuous_map (subtopology X S) Y f"
  obtains g where "continuous_map (subtopology X (Kolmogorov_quotient X ` S)) Y g"
              "\<And>x. x \<in> S \<Longrightarrow> g(Kolmogorov_quotient X x) = f x"
sorry

subsection\<open>Closed diagonals and graphs\<close>

lemma Hausdorff_space_closedin_diagonal:
  "Hausdorff_space X \<longleftrightarrow> closedin (prod_topology X X) ((\<lambda>x. (x,x)) ` topspace X)"
sorry

lemma closed_map_diag_eq:
   "closed_map X (prod_topology X X) (\<lambda>x. (x,x)) \<longleftrightarrow> Hausdorff_space X"
sorry

lemma proper_map_diag_eq [simp]:
   "proper_map X (prod_topology X X) (\<lambda>x. (x,x)) \<longleftrightarrow> Hausdorff_space X"
sorry

lemma closedin_continuous_maps_eq:
  assumes "Hausdorff_space Y" and f: "continuous_map X Y f" and g: "continuous_map X Y g"
  shows "closedin X {x \<in> topspace X. f x = g x}"
sorry

lemma forall_in_closure_of:
  assumes "x \<in> X closure_of S" "\<And>x. x \<in> S \<Longrightarrow> P x"
    and "closedin X {x \<in> topspace X. P x}"
  shows "P x"
sorry

lemma forall_in_closure_of_eq:
  assumes x: "x \<in> X closure_of S"
    and Y: "Hausdorff_space Y" 
    and f: "continuous_map X Y f" and g: "continuous_map X Y g"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "f x = g x"
sorry

lemma retract_of_space_imp_closedin:
  assumes "Hausdorff_space X" and S: "S retract_of_space X"
  shows "closedin X S"
sorry

lemma homeomorphic_maps_graph:
   "homeomorphic_maps X (subtopology (prod_topology X Y) ((\<lambda>x. (x, f x)) ` (topspace X)))
         (\<lambda>x. (x, f x)) fst  \<longleftrightarrow>  continuous_map X Y f" 
   (is "?lhs=?rhs")
sorry


subsection \<open> KC spaces, those where all compact sets are closed.\<close>

definition kc_space 
  where "kc_space X \<equiv> \<forall>S. compactin X S \<longrightarrow> closedin X S"

lemma kc_space_euclidean: "kc_space (euclidean :: 'a::metric_space topology)"
sorry

lemma kc_space_expansive:
   "\<lbrakk>kc_space X; topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk>
      \<Longrightarrow> kc_space Y"
sorry

lemma compactin_imp_closedin_gen:
   "\<lbrakk>kc_space X; compactin X S\<rbrakk> \<Longrightarrow> closedin X S"
sorry

lemma Hausdorff_imp_kc_space: "Hausdorff_space X \<Longrightarrow> kc_space X"
sorry

lemma kc_imp_t1_space: "kc_space X \<Longrightarrow> t1_space X"
sorry

lemma kc_space_subtopology:
   "kc_space X \<Longrightarrow> kc_space(subtopology X S)"
sorry

lemma kc_space_discrete_topology:
   "kc_space(discrete_topology U)"
sorry

lemma kc_space_continuous_injective_map_preimage:
  assumes "kc_space Y" "continuous_map X Y f" and injf: "inj_on f (topspace X)"
  shows "kc_space X"
sorry

lemma kc_space_retraction_map_image:
  assumes "retraction_map X Y r" "kc_space X"
  shows "kc_space Y"
sorry

lemma homeomorphic_kc_space:
   "X homeomorphic_space Y \<Longrightarrow> kc_space X \<longleftrightarrow> kc_space Y"
sorry

lemma compact_kc_eq_maximal_compact_space:
  assumes "compact_space X"
  shows "kc_space X \<longleftrightarrow>
         (\<forall>Y. topspace Y = topspace X \<and> (\<forall>S. openin X S \<longrightarrow> openin Y S) \<and> compact_space Y \<longrightarrow> Y = X)" (is "?lhs=?rhs")
sorry

lemma continuous_imp_closed_map_gen:
   "\<lbrakk>compact_space X; kc_space Y; continuous_map X Y f\<rbrakk> \<Longrightarrow> closed_map X Y f"
sorry

lemma kc_space_compact_subtopologies:
  "kc_space X \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> kc_space(subtopology X K))" (is "?lhs=?rhs")
sorry

lemma kc_space_compact_prod_topology:
  assumes "compact_space X"
  shows "kc_space(prod_topology X X) \<longleftrightarrow> Hausdorff_space X" (is "?lhs=?rhs")
sorry

lemma kc_space_prod_topology:
   "kc_space(prod_topology X X) \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> Hausdorff_space(subtopology X K))" (is "?lhs=?rhs")
sorry

lemma kc_space_prod_topology_alt:
   "kc_space(prod_topology X X) \<longleftrightarrow>
        kc_space X \<and>
        (\<forall>K. compactin X K \<longrightarrow> Hausdorff_space(subtopology X K))"
sorry

proposition kc_space_prod_topology_left:
  assumes X: "kc_space X" and Y: "Hausdorff_space Y"
  shows "kc_space (prod_topology X Y)"
sorry

lemma kc_space_prod_topology_right:
   "\<lbrakk>Hausdorff_space X; kc_space Y\<rbrakk> \<Longrightarrow> kc_space (prod_topology X Y)"
sorry

subsection \<open>Technical results about proper maps, perfect maps, etc\<close>

lemma compact_imp_proper_map_gen:
  assumes Y: "\<And>S. \<lbrakk>S \<subseteq> topspace Y; \<And>K. compactin Y K \<Longrightarrow> compactin Y (S \<inter> K)\<rbrakk>
               \<Longrightarrow> closedin Y S"
    and fim: "f ` (topspace X) \<subseteq> topspace Y"
    and f: "continuous_map X Y f \<or> kc_space X"
    and YX: "\<And>K. compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}"
  shows "proper_map X Y f"
sorry

lemma tube_lemma_left:
  assumes W: "openin (prod_topology X Y) W" and C: "compactin X C" 
    and y: "y \<in> topspace Y" and subW: "C \<times> {y} \<subseteq> W"
  shows "\<exists>U V. openin X U \<and> openin Y V \<and> C \<subseteq> U \<and> y \<in> V \<and> U \<times> V \<subseteq> W"
sorry

lemma Wallace_theorem_prod_topology:
  assumes "compactin X K" "compactin Y L" 
    and W: "openin (prod_topology X Y) W" and subW: "K \<times> L \<subseteq> W"
  obtains U V where "openin X U" "openin Y V" "K \<subseteq> U" "L \<subseteq> V" "U \<times> V \<subseteq> W"
sorry

lemma proper_map_prod:
   "proper_map (prod_topology X Y) (prod_topology X' Y') (\<lambda>(x,y). (f x, g y)) \<longleftrightarrow>
    (prod_topology X Y) = trivial_topology \<or> proper_map X X' f \<and> proper_map Y Y' g"
   (is "?lhs \<longleftrightarrow> _ \<or> ?rhs")
sorry

lemma proper_map_paired:
  assumes "Hausdorff_space X \<and> proper_map X Y f \<and> proper_map X Z g \<or>
        Hausdorff_space Y \<and> continuous_map X Y f \<and> proper_map X Z g \<or>
        Hausdorff_space Z \<and> proper_map X Y f \<and> continuous_map X Z g"
  shows "proper_map X (prod_topology Y Z) (\<lambda>x. (f x,g x))"
sorry

lemma proper_map_pairwise:
  assumes
    "Hausdorff_space X \<and> proper_map X Y (fst \<circ> f) \<and> proper_map X Z (snd \<circ> f) \<or>
     Hausdorff_space Y \<and> continuous_map X Y (fst \<circ> f) \<and> proper_map X Z (snd \<circ> f) \<or>
     Hausdorff_space Z \<and> proper_map X Y (fst \<circ> f) \<and> continuous_map X Z (snd \<circ> f)"
  shows "proper_map X (prod_topology Y Z) f"
sorry

lemma proper_map_from_composition_right:
  assumes "Hausdorff_space Y" "proper_map X Z (g \<circ> f)" and contf: "continuous_map X Y f"
    and contg: "continuous_map Y Z g"
  shows "proper_map X Y f"
sorry

lemma perfect_map_from_composition_right:
   "\<lbrakk>Hausdorff_space Y; perfect_map X Z (g \<circ> f);
     continuous_map X Y f; continuous_map Y Z g; f ` topspace X = topspace Y\<rbrakk>
    \<Longrightarrow> perfect_map X Y f"
sorry

lemma perfect_map_from_composition_right_inj:
   "\<lbrakk>perfect_map X Z (g \<circ> f); f ` topspace X = topspace Y;
     continuous_map X Y f; continuous_map Y Z g; inj_on g (topspace Y)\<rbrakk>
    \<Longrightarrow> perfect_map X Y f"
sorry

subsection \<open>Regular spaces\<close>

text \<open>Regular spaces are *not* a priori assumed to be Hausdorff or $T_1$\<close>

definition regular_space 
  where "regular_space X \<equiv>
        \<forall>C a. closedin X C \<and> a \<in> topspace X - C
                \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V)"

lemma homeomorphic_regular_space_aux:
  assumes hom: "X homeomorphic_space Y" and X: "regular_space X"
  shows "regular_space Y"
sorry

lemma homeomorphic_regular_space:
   "X homeomorphic_space Y
        \<Longrightarrow> (regular_space X \<longleftrightarrow> regular_space Y)"
sorry

lemma regular_space:
   "regular_space X \<longleftrightarrow>
        (\<forall>C a. closedin X C \<and> a \<in> topspace X - C
              \<longrightarrow> (\<exists>U. openin X U \<and> a \<in> U \<and> disjnt C (X closure_of U)))"
sorry

lemma neighbourhood_base_of_closedin:
  "neighbourhood_base_of (closedin X) X \<longleftrightarrow> regular_space X" (is "?lhs=?rhs")
sorry

lemma regular_space_discrete_topology [simp]:
   "regular_space (discrete_topology S)"
sorry

lemma regular_space_subtopology:
 "regular_space X \<Longrightarrow> regular_space (subtopology X S)"
sorry

lemma regular_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; regular_space X\<rbrakk> \<Longrightarrow> regular_space Y"
sorry

lemma regular_t0_imp_Hausdorff_space:
   "\<lbrakk>regular_space X; t0_space X\<rbrakk> \<Longrightarrow> Hausdorff_space X"
sorry

lemma regular_t0_eq_Hausdorff_space:
   "regular_space X \<Longrightarrow> (t0_space X \<longleftrightarrow> Hausdorff_space X)"
sorry

lemma regular_t1_imp_Hausdorff_space:
   "\<lbrakk>regular_space X; t1_space X\<rbrakk> \<Longrightarrow> Hausdorff_space X"
sorry

lemma regular_t1_eq_Hausdorff_space:
   "regular_space X \<Longrightarrow> t1_space X \<longleftrightarrow> Hausdorff_space X"
sorry

lemma compact_Hausdorff_imp_regular_space:
  assumes "compact_space X" "Hausdorff_space X"
  shows "regular_space X"
sorry

lemma neighbourhood_base_of_closed_Hausdorff_space:
   "regular_space X \<and> Hausdorff_space X \<longleftrightarrow>
    neighbourhood_base_of (\<lambda>C. closedin X C \<and> Hausdorff_space(subtopology X C)) X" (is "?lhs=?rhs")
sorry

lemma locally_compact_imp_kc_eq_Hausdorff_space:
   "neighbourhood_base_of (compactin X) X \<Longrightarrow> kc_space X \<longleftrightarrow> Hausdorff_space X"
sorry

lemma regular_space_compact_closed_separation:
  assumes X: "regular_space X"
      and S: "compactin X S"
      and T: "closedin X T"
      and "disjnt S T"
    shows "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
sorry

lemma regular_space_compact_closed_sets:
   "regular_space X \<longleftrightarrow>
        (\<forall>S T. compactin X S \<and> closedin X T \<and> disjnt S T
           \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))" (is "?lhs=?rhs")
sorry

lemma regular_space_prod_topology:
   "regular_space (prod_topology X Y) \<longleftrightarrow>
        X = trivial_topology \<or> Y = trivial_topology \<or> regular_space X \<and> regular_space Y" (is "?lhs=?rhs")
sorry

lemma regular_space_product_topology:
   "regular_space (product_topology X I) \<longleftrightarrow>
    (product_topology X I) = trivial_topology \<or> (\<forall>i \<in> I. regular_space (X i))" (is "?lhs=?rhs")
sorry

lemma closed_map_paired_gen_aux:
  assumes "regular_space Y" and f: "closed_map Z X f" and g: "closed_map Z Y g"
    and clo: "\<And>y. y \<in> topspace X \<Longrightarrow> closedin Z {x \<in> topspace Z. f x = y}"
    and contg: "continuous_map Z Y g"
  shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
sorry

lemma closed_map_paired_gen:
  assumes f: "closed_map Z X f" and g: "closed_map Z Y g"
  and D: "(regular_space X \<and> continuous_map Z X f \<and> (\<forall>z \<in> topspace Y. closedin Z {x \<in> topspace Z. g x = z})
         \<or> regular_space Y \<and> continuous_map Z Y g \<and> (\<forall>y \<in> topspace X. closedin Z {x \<in> topspace Z. f x = y}))"
         (is "?RSX \<or> ?RSY")
       shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
sorry

lemma closed_map_paired:
  assumes "closed_map Z X f" and contf: "continuous_map Z X f"
          "closed_map Z Y g" and contg: "continuous_map Z Y g"
  and D: "t1_space X \<and> regular_space Y \<or> regular_space X \<and> t1_space Y"
  shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
sorry

lemma closed_map_pairwise:
  assumes  "closed_map Z X (fst \<circ> f)" "continuous_map Z X (fst \<circ> f)"
    "closed_map Z Y (snd \<circ> f)" "continuous_map Z Y (snd \<circ> f)"
    "t1_space X \<and> regular_space Y \<or> regular_space X \<and> t1_space Y"
  shows "closed_map Z (prod_topology X Y) f"
sorry

lemma continuous_imp_proper_map:
   "\<lbrakk>compact_space X; kc_space Y; continuous_map X Y f\<rbrakk> \<Longrightarrow> proper_map X Y f"
sorry

lemma tube_lemma_right:
  assumes W: "openin (prod_topology X Y) W" and C: "compactin Y C" 
    and x: "x \<in> topspace X" and subW: "{x} \<times> C \<subseteq> W"
  shows "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> C \<subseteq> V \<and> U \<times> V \<subseteq> W"
sorry

lemma closed_map_fst:
  assumes "compact_space Y"
  shows "closed_map (prod_topology X Y) X fst"
sorry

lemma closed_map_snd:
  assumes "compact_space X"
  shows "closed_map (prod_topology X Y) Y snd"
sorry

lemma closed_map_paired_closed_map_right:
   "\<lbrakk>closed_map X Y f; regular_space X;
     \<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}\<rbrakk>
    \<Longrightarrow> closed_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
sorry

lemma closed_map_paired_closed_map_left:
  assumes "closed_map X Y f"  "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "closed_map X (prod_topology Y X) (\<lambda>x. (f x, x))"
sorry

lemma closed_map_imp_closed_graph:
  assumes "closed_map X Y f" "regular_space X"
          "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "closedin (prod_topology X Y) ((\<lambda>x. (x, f x)) ` topspace X)"
sorry

lemma proper_map_paired_closed_map_right:
  assumes "closed_map X Y f" "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "proper_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
sorry

lemma proper_map_paired_closed_map_left:
  assumes "closed_map X Y f" "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "proper_map X (prod_topology Y X) (\<lambda>x. (f x, x))"
sorry

proposition regular_space_continuous_proper_map_image:
  assumes "regular_space X" and contf: "continuous_map X Y f" and pmapf: "proper_map X Y f"
    and fim: "f ` (topspace X) = topspace Y"
  shows "regular_space Y"
sorry

lemma regular_space_perfect_map_image:
   "\<lbrakk>regular_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> regular_space Y"
sorry

proposition regular_space_perfect_map_image_eq:
  assumes "Hausdorff_space X" and perf: "perfect_map X Y f"
  shows "regular_space X \<longleftrightarrow> regular_space Y" (is "?lhs=?rhs")
sorry


subsection\<open>Locally compact spaces\<close>

definition locally_compact_space 
  where "locally_compact_space X \<equiv>
    \<forall>x \<in> topspace X. \<exists>U K. openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"

lemma homeomorphic_locally_compact_spaceD:
  assumes X: "locally_compact_space X" and "X homeomorphic_space Y"
  shows "locally_compact_space Y"
sorry

lemma homeomorphic_locally_compact_space:
  assumes "X homeomorphic_space Y"
  shows "locally_compact_space X \<longleftrightarrow> locally_compact_space Y"
sorry

lemma locally_compact_space_retraction_map_image:
  assumes "retraction_map X Y r" and X: "locally_compact_space X"
  shows "locally_compact_space Y"
sorry

lemma compact_imp_locally_compact_space:
   "compact_space X \<Longrightarrow> locally_compact_space X"
sorry

lemma neighbourhood_base_imp_locally_compact_space:
   "neighbourhood_base_of (compactin X) X \<Longrightarrow> locally_compact_space X"
sorry

lemma locally_compact_imp_neighbourhood_base:
  assumes loc: "locally_compact_space X" and reg: "regular_space X"
  shows "neighbourhood_base_of (compactin X) X"
sorry

lemma Hausdorff_regular: "\<lbrakk>Hausdorff_space X; neighbourhood_base_of (compactin X) X\<rbrakk> \<Longrightarrow> regular_space X"
sorry

lemma locally_compact_Hausdorff_imp_regular_space: 
  assumes loc: "locally_compact_space X" and "Hausdorff_space X"
  shows "regular_space X"
sorry

lemma locally_compact_space_neighbourhood_base:
  "Hausdorff_space X \<or> regular_space X
        \<Longrightarrow> locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (compactin X) X"
sorry

lemma locally_compact_Hausdorff_or_regular:
   "locally_compact_space X \<and> (Hausdorff_space X \<or> regular_space X) \<longleftrightarrow> locally_compact_space X \<and> regular_space X"
sorry

lemma locally_compact_space_compact_closedin:
  assumes  "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>U K. openin X U \<and> compactin X K \<and> closedin X K \<and> x \<in> U \<and> U \<subseteq> K)"
sorry

lemma locally_compact_space_compact_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>U. openin X U \<and> compactin X (X closure_of U) \<and> x \<in> U)" (is "?lhs=?rhs")
sorry

lemma locally_compact_space_neighbourhood_base_closedin:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X" (is "?lhs=?rhs")
sorry

lemma locally_compact_space_neighbourhood_base_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>T. compactin X (X closure_of T)) X" 
         (is "?lhs=?rhs")
sorry

lemma locally_compact_space_neighbourhood_base_open_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> 
             neighbourhood_base_of (\<lambda>U. openin X U \<and> compactin X (X closure_of U)) X"
         (is "?lhs=?rhs")
sorry

lemma locally_compact_space_compact_closed_compact:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>K. compactin X K
              \<longrightarrow> (\<exists>U L. openin X U \<and> compactin X L \<and> closedin X L \<and> K \<subseteq> U \<and> U \<subseteq> L))"
         (is "?lhs=?rhs")
sorry

lemma locally_compact_regular_space_neighbourhood_base:
   "locally_compact_space X \<and> regular_space X \<longleftrightarrow>
        neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X"
sorry

lemma locally_compact_kc_space:
   "neighbourhood_base_of (compactin X) X \<and> kc_space X \<longleftrightarrow>
        locally_compact_space X \<and> Hausdorff_space X"
sorry

lemma locally_compact_kc_space_alt:
   "neighbourhood_base_of (compactin X) X \<and> kc_space X \<longleftrightarrow>
        locally_compact_space X \<and> Hausdorff_space X \<and> regular_space X"
sorry

lemma locally_compact_kc_imp_regular_space:
   "\<lbrakk>neighbourhood_base_of (compactin X) X; kc_space X\<rbrakk> \<Longrightarrow> regular_space X"
sorry

lemma kc_locally_compact_space:
   "kc_space X
    \<Longrightarrow> neighbourhood_base_of (compactin X) X \<longleftrightarrow> locally_compact_space X \<and> Hausdorff_space X \<and> regular_space X"
sorry

lemma locally_compact_space_closed_subset:
  assumes loc: "locally_compact_space X" and "closedin X S"
  shows "locally_compact_space (subtopology X S)"
sorry

lemma locally_compact_space_open_subset:
  assumes X: "Hausdorff_space X \<or> regular_space X" and loc: "locally_compact_space X" and "openin X S"
  shows "locally_compact_space (subtopology X S)"
sorry

lemma locally_compact_space_discrete_topology:
   "locally_compact_space (discrete_topology U)"
sorry

lemma locally_compact_space_continuous_open_map_image:
  "\<lbrakk>continuous_map X X' f; open_map X X' f;
    f ` topspace X = topspace X'; locally_compact_space X\<rbrakk> \<Longrightarrow> locally_compact_space X'"
sorry

lemma locally_compact_subspace_openin_closure_of:
  assumes "Hausdorff_space X" and S: "S \<subseteq> topspace X" 
    and loc: "locally_compact_space (subtopology X S)"
  shows "openin (subtopology X (X closure_of S)) S"
sorry

lemma locally_compact_subspace_closed_Int_openin:
   "\<lbrakk>Hausdorff_space X \<and> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)\<rbrakk>
        \<Longrightarrow> \<exists>C U. closedin X C \<and> openin X U \<and> C \<inter> U = S"
sorry

lemma locally_compact_subspace_open_in_closure_of_eq:
  assumes "Hausdorff_space X" and loc: "locally_compact_space X"
  shows "openin (subtopology X (X closure_of S)) S \<longleftrightarrow> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)" (is "?lhs=?rhs")
sorry

lemma locally_compact_subspace_closed_Int_openin_eq:
  assumes "Hausdorff_space X" and loc: "locally_compact_space X"
  shows "(\<exists>C U. closedin X C \<and> openin X U \<and> C \<inter> U = S) \<longleftrightarrow> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)" (is "?lhs=?rhs")
sorry

lemma dense_locally_compact_openin_Hausdorff_space:
   "\<lbrakk>Hausdorff_space X; S \<subseteq> topspace X; X closure_of S = topspace X;
     locally_compact_space (subtopology X S)\<rbrakk> \<Longrightarrow> openin X S"
sorry

lemma locally_compact_space_prod_topology:
  "locally_compact_space (prod_topology X Y) \<longleftrightarrow>
        (prod_topology X Y) = trivial_topology \<or>
        locally_compact_space X \<and> locally_compact_space Y" (is "?lhs=?rhs")
sorry

lemma locally_compact_space_product_topology:
   "locally_compact_space(product_topology X I) \<longleftrightarrow>
        product_topology X I = trivial_topology \<or>
        finite {i \<in> I. \<not> compact_space(X i)} \<and> (\<forall>i \<in> I. locally_compact_space(X i))" (is "?lhs=?rhs")
sorry

lemma locally_compact_space_sum_topology:
   "locally_compact_space (sum_topology X I) \<longleftrightarrow> (\<forall>i \<in> I. locally_compact_space (X i))" (is "?lhs=?rhs")
sorry

lemma locally_compact_space_euclidean:
  "locally_compact_space (euclidean::'a::heine_borel topology)"
sorry

lemma locally_compact_Euclidean_space:
  "locally_compact_space(Euclidean_space n)"
sorry

proposition quotient_map_prod_right:
  assumes loc: "locally_compact_space Z" 
    and reg: "Hausdorff_space Z \<or> regular_space Z" 
    and f: "quotient_map X Y f"
  shows "quotient_map (prod_topology Z X) (prod_topology Z Y) (\<lambda>(x,y). (x,f y))"
sorry

lemma quotient_map_prod_left:
  assumes loc: "locally_compact_space Z" 
    and reg: "Hausdorff_space Z \<or> regular_space Z" 
    and f: "quotient_map X Y f"
  shows "quotient_map (prod_topology X Z) (prod_topology Y Z) (\<lambda>(x,y). (f x,y))"
sorry

lemma locally_compact_space_perfect_map_preimage:
  assumes "locally_compact_space X'" and f: "perfect_map X X' f"
  shows "locally_compact_space X"
sorry
subsection\<open>Special characterizations of classes of functions into and out of R\<close>

lemma monotone_map_into_euclideanreal_alt:
  assumes "continuous_map X euclideanreal f" 
  shows "(\<forall>k. is_interval k \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> k}) \<longleftrightarrow>
         connected_space X \<and> monotone_map X euclideanreal f"  (is "?lhs=?rhs")
sorry

lemma monotone_map_into_euclideanreal:
   "\<lbrakk>connected_space X; continuous_map X euclideanreal f\<rbrakk>
    \<Longrightarrow> monotone_map X euclideanreal f \<longleftrightarrow>
        (\<forall>k. is_interval k \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> k})"
sorry

lemma monotone_map_euclideanreal_alt:
   "(\<forall>I::real set. is_interval I \<longrightarrow> is_interval {x::real. x \<in> S \<and> f x \<in> I}) \<longleftrightarrow>
    is_interval S \<and> (mono_on S f \<or> antimono_on S f)" (is "?lhs=?rhs")
sorry

lemma monotone_map_euclideanreal:
  fixes S :: "real set"
  shows
   "\<lbrakk>is_interval S; continuous_on S f\<rbrakk> \<Longrightarrow> 
    monotone_map (top_of_set S) euclideanreal f \<longleftrightarrow> (mono_on S f \<or> monotone_on S (\<le>) (\<ge>) f)"
sorry

lemma injective_eq_monotone_map:
  fixes f :: "real \<Rightarrow> real"
  assumes "is_interval S" "continuous_on S f"
  shows "inj_on f S \<longleftrightarrow> strict_mono_on S f \<or> strict_antimono_on S f"
sorry

subsection\<open>Normal spaces\<close>

definition normal_space 
  where "normal_space X \<equiv>
        \<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T 
              \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V)"

lemma normal_space_retraction_map_image:
  assumes r: "retraction_map X Y r" and X: "normal_space X"
  shows "normal_space Y"
sorry

lemma homeomorphic_normal_space:
   "X homeomorphic_space Y \<Longrightarrow> normal_space X \<longleftrightarrow> normal_space Y"
sorry

lemma normal_space:
  "normal_space X \<longleftrightarrow>
    (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
          \<longrightarrow> (\<exists>U. openin X U \<and> S \<subseteq> U \<and> disjnt T (X closure_of U)))"
sorry

lemma normal_space_alt:
   "normal_space X \<longleftrightarrow>
    (\<forall>S U. closedin X S \<and> openin X U \<and> S \<subseteq> U \<longrightarrow> (\<exists>V. openin X V \<and> S \<subseteq> V \<and> X closure_of V \<subseteq> U))"
sorry

lemma normal_space_closures:
   "normal_space X \<longleftrightarrow>
    (\<forall>S T. S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and>
              disjnt (X closure_of S) (X closure_of T)
              \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))" 
   (is "?lhs=?rhs")
sorry

lemma normal_space_disjoint_closures:
   "normal_space X \<longleftrightarrow>
    (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
          \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and>
                    disjnt (X closure_of U) (X closure_of V)))"
   (is "?lhs=?rhs")
sorry

lemma normal_space_dual:
   "normal_space X \<longleftrightarrow>
    (\<forall>U V. openin X U \<longrightarrow> openin X V \<and> U \<union> V = topspace X
          \<longrightarrow> (\<exists>S T. closedin X S \<and> closedin X T \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> S \<union> T = topspace X))"
   (is "_ = ?rhs")
sorry

lemma normal_t1_imp_Hausdorff_space:
  assumes "normal_space X" "t1_space X"
  shows "Hausdorff_space X"
sorry

lemma normal_t1_eq_Hausdorff_space:
   "normal_space X \<Longrightarrow> t1_space X \<longleftrightarrow> Hausdorff_space X"
sorry

lemma normal_t1_imp_regular_space:
   "\<lbrakk>normal_space X; t1_space X\<rbrakk> \<Longrightarrow> regular_space X"
sorry

lemma compact_Hausdorff_or_regular_imp_normal_space:
   "\<lbrakk>compact_space X; Hausdorff_space X \<or> regular_space X\<rbrakk>
        \<Longrightarrow> normal_space X"
sorry

lemma normal_space_discrete_topology:
   "normal_space(discrete_topology U)"
sorry

lemma normal_space_fsigmas:
  "normal_space X \<longleftrightarrow>
    (\<forall>S T. fsigma_in X S \<and> fsigma_in X T \<and> separatedin X S T
           \<longrightarrow> (\<exists>U B. openin X U \<and> openin X B \<and> S \<subseteq> U \<and> T \<subseteq> B \<and> disjnt U B))" (is "?lhs=?rhs")
sorry

lemma normal_space_fsigma_subtopology:
  assumes "normal_space X" "fsigma_in X S"
  shows "normal_space (subtopology X S)"
sorry

lemma normal_space_closed_subtopology:
  assumes "normal_space X" "closedin X S"
  shows "normal_space (subtopology X S)"
sorry

lemma normal_space_continuous_closed_map_image:
  assumes "normal_space X" and contf: "continuous_map X Y f" 
    and clof: "closed_map X Y f"  and fim: "f ` topspace X = topspace Y"
shows "normal_space Y"
sorry
subsection \<open>Hereditary topological properties\<close>

definition hereditarily 
  where "hereditarily P X \<equiv>
        \<forall>S. S \<subseteq> topspace X \<longrightarrow> P(subtopology X S)"

lemma hereditarily:
   "hereditarily P X \<longleftrightarrow> (\<forall>S. P(subtopology X S))"
sorry

lemma hereditarily_mono:
   "\<lbrakk>hereditarily P X; \<And>x. P x \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> hereditarily Q X"
sorry

lemma hereditarily_inc:
   "hereditarily P X \<Longrightarrow> P X"
sorry

lemma hereditarily_subtopology:
   "hereditarily P X \<Longrightarrow> hereditarily P (subtopology X S)"
sorry

lemma hereditarily_normal_space_continuous_closed_map_image:
  assumes X: "hereditarily normal_space X" and contf: "continuous_map X Y f" 
    and clof: "closed_map X Y f"  and fim: "f ` (topspace X) = topspace Y" 
  shows "hereditarily normal_space Y"
sorry

lemma homeomorphic_hereditarily_normal_space:
   "X homeomorphic_space Y
      \<Longrightarrow> (hereditarily normal_space X \<longleftrightarrow> hereditarily normal_space Y)"
sorry

lemma hereditarily_normal_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; hereditarily normal_space X\<rbrakk> \<Longrightarrow> hereditarily normal_space Y"
sorry
subsection\<open>Limits in a topological space\<close>

lemma limitin_const_iff:
  assumes "t1_space X" "\<not> trivial_limit F"
  shows "limitin X (\<lambda>k. a) l F \<longleftrightarrow> l \<in> topspace X \<and> a = l"  (is "?lhs=?rhs")
sorry

lemma compactin_sequence_with_limit:
  assumes lim: "limitin X \<sigma> l sequentially" and "S \<subseteq> range \<sigma>" and SX: "S \<subseteq> topspace X"
  shows "compactin X (insert l S)"
sorry

lemma limitin_Hausdorff_unique:
  assumes "limitin X f l1 F" "limitin X f l2 F" "\<not> trivial_limit F" "Hausdorff_space X"
  shows "l1 = l2"
sorry

lemma limitin_kc_unique:
  assumes "kc_space X" and lim1: "limitin X f l1 sequentially" and lim2: "limitin X f l2 sequentially"
  shows "l1 = l2"
sorry

lemma limitin_closedin:
  assumes lim: "limitin X f l F" 
    and "closedin X S" and ev: "eventually (\<lambda>x. f x \<in> S) F" "\<not> trivial_limit F"
  shows "l \<in> S"
sorry

subsection\<open>Quasi-components\<close>

definition quasi_component_of :: "'a topology \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
  "quasi_component_of X x y \<equiv>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        (\<forall>T. closedin X T \<and> openin X T \<longrightarrow> (x \<in> T \<longleftrightarrow> y \<in> T))"

abbreviation "quasi_component_of_set S x \<equiv> Collect (quasi_component_of S x)"

definition quasi_components_of :: "'a topology \<Rightarrow> ('a set) set"
  where
  "quasi_components_of X = quasi_component_of_set X ` topspace X"

lemma quasi_component_in_topspace:
   "quasi_component_of X x y \<Longrightarrow> x \<in> topspace X \<and> y \<in> topspace X"
sorry

lemma quasi_component_of_refl [simp]:
   "quasi_component_of X x x \<longleftrightarrow> x \<in> topspace X"
sorry

lemma quasi_component_of_sym:
   "quasi_component_of X x y \<longleftrightarrow> quasi_component_of X y x"
sorry

lemma quasi_component_of_trans:
   "\<lbrakk>quasi_component_of X x y; quasi_component_of X y z\<rbrakk> \<Longrightarrow> quasi_component_of X x z"
sorry

lemma quasi_component_of_subset_topspace:
   "quasi_component_of_set X x \<subseteq> topspace X"
sorry

lemma quasi_component_of_eq_empty:
   "quasi_component_of_set X x = {} \<longleftrightarrow> (x \<notin> topspace X)"
sorry

lemma quasi_component_of:
   "quasi_component_of X x y \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> (\<forall>T. x \<in> T \<and> closedin X T \<and> openin X T \<longrightarrow> y \<in> T)"
sorry

lemma quasi_component_of_alt:
  "quasi_component_of X x y \<longleftrightarrow>
      x \<in> topspace X \<and> y \<in> topspace X \<and>
      \<not> (\<exists>U V. openin X U \<and> openin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> x \<in> U \<and> y \<in> V)" 
  (is "?lhs = ?rhs")
sorry

lemma quasi_components_lepoll_topspace: "quasi_components_of X \<lesssim> topspace X"
sorry

lemma quasi_component_of_separated:
   "quasi_component_of X x y \<longleftrightarrow>
     x \<in> topspace X \<and> y \<in> topspace X \<and>
     \<not> (\<exists>U V. separatedin X U V \<and> U \<union> V = topspace X \<and> x \<in> U \<and> y \<in> V)"
sorry

lemma quasi_component_of_subtopology:
  "quasi_component_of (subtopology X s) x y \<Longrightarrow> quasi_component_of X x y"
sorry

lemma quasi_component_of_mono:
   "quasi_component_of (subtopology X S) x y \<and> S \<subseteq> T
        \<Longrightarrow> quasi_component_of (subtopology X T) x y"
sorry

lemma quasi_component_of_equiv:
   "quasi_component_of X x y \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> quasi_component_of X x = quasi_component_of X y"
sorry

lemma quasi_component_of_disjoint [simp]:
   "disjnt (quasi_component_of_set X x) (quasi_component_of_set X y) \<longleftrightarrow> \<not> (quasi_component_of X x y)"
sorry

lemma quasi_component_of_eq:
   "quasi_component_of X x = quasi_component_of X y \<longleftrightarrow>
    (x \<notin> topspace X \<and> y \<notin> topspace X) 
  \<or> x \<in> topspace X \<and> y \<in> topspace X \<and> quasi_component_of X x y"
sorry

lemma topspace_imp_quasi_components_of:
  assumes "x \<in> topspace X"
  obtains C where "C \<in> quasi_components_of X" "x \<in> C"
sorry

lemma Union_quasi_components_of: "\<Union> (quasi_components_of X) = topspace X"
sorry

lemma pairwise_disjoint_quasi_components_of:
   "pairwise disjnt (quasi_components_of X)"
sorry

lemma complement_quasi_components_of_Union:
  assumes "C \<in> quasi_components_of X"
  shows "topspace X - C = \<Union> (quasi_components_of X - {C})"  (is "?lhs = ?rhs")
sorry

lemma nonempty_quasi_components_of:
   "C \<in> quasi_components_of X \<Longrightarrow> C \<noteq> {}"
sorry

lemma quasi_components_of_subset:
   "C \<in> quasi_components_of X \<Longrightarrow> C \<subseteq> topspace X"
sorry

lemma quasi_component_in_quasi_components_of:
   "quasi_component_of_set X a \<in> quasi_components_of X \<longleftrightarrow> a \<in> topspace X"
sorry

lemma quasi_components_of_eq_empty [simp]:
   "quasi_components_of X = {} \<longleftrightarrow> X = trivial_topology"
sorry

lemma quasi_components_of_empty_space [simp]:
   "quasi_components_of trivial_topology = {}"
sorry

lemma quasi_component_of_set:
   "quasi_component_of_set X x =
        (if x \<in> topspace X
        then \<Inter> {t. closedin X t \<and> openin X t \<and> x \<in> t}
        else {})"
sorry

lemma closedin_quasi_component_of: "closedin X (quasi_component_of_set X x)"
sorry

lemma closedin_quasi_components_of:
   "C \<in> quasi_components_of X \<Longrightarrow> closedin X C"
sorry

lemma openin_finite_quasi_components:
  "\<lbrakk>finite(quasi_components_of X); C \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> openin X C"
sorry

lemma quasi_component_of_eq_overlap:
   "quasi_component_of X x = quasi_component_of X y \<longleftrightarrow>
      (x \<notin> topspace X \<and> y \<notin> topspace X) \<or>
      \<not> (quasi_component_of_set X x \<inter> quasi_component_of_set X y = {})"
sorry

lemma quasi_component_of_nonoverlap:
   "quasi_component_of_set X x \<inter> quasi_component_of_set X y = {} \<longleftrightarrow>
     (x \<notin> topspace X) \<or> (y \<notin> topspace X) \<or>
     \<not> (quasi_component_of X x = quasi_component_of X y)"
sorry

lemma quasi_component_of_overlap:
   "\<not> (quasi_component_of_set X x \<inter> quasi_component_of_set X y = {}) \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> quasi_component_of X x = quasi_component_of X y"
sorry

lemma quasi_components_of_disjoint:
   "\<lbrakk>C \<in> quasi_components_of X; D \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> disjnt C D \<longleftrightarrow> C \<noteq> D"
sorry

lemma quasi_components_of_overlap:
   "\<lbrakk>C \<in> quasi_components_of X; D \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> \<not> (C \<inter> D = {}) \<longleftrightarrow> C = D"
sorry

lemma pairwise_separated_quasi_components_of:
   "pairwise (separatedin X) (quasi_components_of X)"
sorry

lemma finite_quasi_components_of_finite:
   "finite(topspace X) \<Longrightarrow> finite(quasi_components_of X)"
sorry

lemma connected_imp_quasi_component_of:
  assumes "connected_component_of X x y"
  shows "quasi_component_of X x y"
sorry

lemma connected_component_subset_quasi_component_of:
   "connected_component_of_set X x \<subseteq> quasi_component_of_set X x"
sorry

lemma quasi_component_as_connected_component_Union:
   "quasi_component_of_set X x =
    \<Union> (connected_component_of_set X ` quasi_component_of_set X x)" 
    (is "?lhs = ?rhs")
sorry

lemma quasi_components_as_connected_components_Union:
  assumes "C \<in> quasi_components_of X"
  obtains \<T> where "\<T> \<subseteq> connected_components_of X" "\<Union>\<T> = C"
sorry

lemma path_imp_quasi_component_of:
   "path_component_of X x y \<Longrightarrow> quasi_component_of X x y"
sorry

lemma path_component_subset_quasi_component_of:
   "path_component_of_set X x \<subseteq> quasi_component_of_set X x"
sorry

lemma connected_space_iff_quasi_component:
   "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. quasi_component_of X x y)"
sorry

lemma connected_space_imp_quasi_component_of:
   " \<lbrakk>connected_space X; a \<in> topspace X; b \<in> topspace X\<rbrakk> \<Longrightarrow> quasi_component_of X a b"
sorry

lemma connected_space_quasi_component_set:
   "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. quasi_component_of_set X x = topspace X)"
sorry

lemma connected_space_iff_quasi_components_eq:
  "connected_space X \<longleftrightarrow>
    (\<forall>C \<in> quasi_components_of X. \<forall>D \<in> quasi_components_of X. C = D)"
sorry

lemma quasi_components_of_subset_sing:
   "quasi_components_of X \<subseteq> {S} \<longleftrightarrow> connected_space X \<and> (X = trivial_topology \<or> topspace X = S)"
sorry

lemma connected_space_iff_quasi_components_subset_sing:
   "connected_space X \<longleftrightarrow> (\<exists>a. quasi_components_of X \<subseteq> {a})"
sorry

lemma quasi_components_of_eq_singleton:
   "quasi_components_of X = {S} \<longleftrightarrow>
        connected_space X \<and> \<not> (X = trivial_topology) \<and> S = topspace X"
sorry

lemma quasi_components_of_connected_space:
   "connected_space X
        \<Longrightarrow> quasi_components_of X = (if X = trivial_topology then {} else {topspace X})"
sorry

lemma separated_between_singletons:
   "separated_between X {x} {y} \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> \<not> (quasi_component_of X x y)"
sorry

lemma quasi_component_nonseparated:
   "quasi_component_of X x y \<longleftrightarrow> x \<in> topspace X \<and> y \<in> topspace X \<and> \<not> (separated_between X {x} {y})"
sorry

lemma separated_between_quasi_component_pointwise_left:
  assumes "C \<in> quasi_components_of X"
  shows "separated_between X C S \<longleftrightarrow> (\<exists>x \<in> C. separated_between X {x} S)"  (is "?lhs = ?rhs")
sorry

lemma separated_between_quasi_component_pointwise_right:
   "C \<in> quasi_components_of X \<Longrightarrow> separated_between X S C \<longleftrightarrow> (\<exists>x \<in> C. separated_between X S {x})"
sorry

lemma separated_between_quasi_component_point:
  assumes "C \<in> quasi_components_of X"
  shows "separated_between X C {x} \<longleftrightarrow> x \<in> topspace X - C" (is "?lhs = ?rhs")
sorry

lemma separated_between_point_quasi_component:
   "C \<in> quasi_components_of X \<Longrightarrow> separated_between X {x} C \<longleftrightarrow> x \<in> topspace X - C"
sorry

lemma separated_between_quasi_component_compact:
   "\<lbrakk>C \<in> quasi_components_of X; compactin X K\<rbrakk> \<Longrightarrow> (separated_between X C K \<longleftrightarrow> disjnt C K)"
sorry

lemma separated_between_compact_quasi_component:
   "\<lbrakk>compactin X K; C \<in> quasi_components_of X\<rbrakk> \<Longrightarrow> separated_between X K C \<longleftrightarrow> disjnt K C"
sorry

lemma separated_between_quasi_components:
  assumes C: "C \<in> quasi_components_of X" and D: "D \<in> quasi_components_of X"
  shows "separated_between X C D \<longleftrightarrow> disjnt C D"   (is "?lhs = ?rhs")
sorry

lemma quasi_eq_connected_component_of_eq:
   "quasi_component_of X x = connected_component_of X x \<longleftrightarrow>
    connectedin X (quasi_component_of_set X x)"  (is "?lhs = ?rhs")
sorry

lemma connected_quasi_component_of:
  assumes "C \<in> quasi_components_of X"
  shows "C \<in> connected_components_of X \<longleftrightarrow> connectedin X C"  (is "?lhs = ?rhs")
sorry

lemma quasi_component_of_clopen_cases:
   "\<lbrakk>C \<in> quasi_components_of X; closedin X T; openin X T\<rbrakk> \<Longrightarrow> C \<subseteq> T \<or> disjnt C T"
sorry

lemma quasi_components_of_set:
  assumes "C \<in> quasi_components_of X"
  shows "\<Inter> {T. closedin X T \<and> openin X T \<and> C \<subseteq> T} = C"  (is "?lhs = ?rhs")
sorry

lemma open_quasi_eq_connected_components_of:
  assumes "openin X C"
  shows "C \<in> quasi_components_of X \<longleftrightarrow> C \<in> connected_components_of X"  (is "?lhs = ?rhs")
sorry

lemma quasi_component_of_continuous_image:
  assumes f:  "continuous_map X Y f" and qc: "quasi_component_of X x y"
  shows "quasi_component_of Y (f x) (f y)"
sorry

lemma quasi_component_of_discrete_topology:
   "quasi_component_of_set (discrete_topology U) x = (if x \<in> U then {x} else {})"
sorry

lemma quasi_components_of_discrete_topology:
   "quasi_components_of (discrete_topology U) = (\<lambda>x. {x}) ` U"
sorry

lemma homeomorphic_map_quasi_component_of:
  assumes hmf: "homeomorphic_map X Y f" and "x \<in> topspace X"
  shows "quasi_component_of_set Y (f x) = f ` (quasi_component_of_set X x)"
sorry

lemma homeomorphic_map_quasi_components_of:
  assumes "homeomorphic_map X Y f"
  shows "quasi_components_of Y = image (image f) (quasi_components_of X)"
sorry

lemma openin_quasi_component_of_locally_connected_space:
  assumes "locally_connected_space X"
  shows "openin X (quasi_component_of_set X x)"
sorry

lemma openin_quasi_components_of_locally_connected_space:
   "locally_connected_space X \<and> c \<in> quasi_components_of X
        \<Longrightarrow> openin X c"
sorry

lemma quasi_eq_connected_components_of_alt:
  "quasi_components_of X = connected_components_of X \<longleftrightarrow> (\<forall>C \<in> quasi_components_of X. connectedin X C)"
  (is "?lhs = ?rhs")
sorry

lemma connected_subset_quasi_components_of_pointwise:
   "connected_components_of X \<subseteq> quasi_components_of X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. quasi_component_of X x = connected_component_of X x)"
  (is "?lhs = ?rhs")
sorry

lemma quasi_subset_connected_components_of_pointwise:
   "quasi_components_of X \<subseteq> connected_components_of X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. quasi_component_of X x = connected_component_of X x)"
sorry

lemma quasi_eq_connected_components_of_pointwise:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. quasi_component_of X x = connected_component_of X x)"
sorry

lemma quasi_eq_connected_components_of_pointwise_alt:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
    (\<forall>x. quasi_component_of X x = connected_component_of X x)"
sorry

lemma quasi_eq_connected_components_of_inclusion:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
        connected_components_of X \<subseteq> quasi_components_of X \<or>
        quasi_components_of X \<subseteq> connected_components_of X"
sorry

lemma quasi_eq_connected_components_of:
  "finite(connected_components_of X) \<or>
      finite(quasi_components_of X) \<or>
      locally_connected_space X \<or>
      compact_space X \<and> (Hausdorff_space X \<or> regular_space X \<or> normal_space X)
      \<Longrightarrow> quasi_components_of X = connected_components_of X"
sorry

lemma quasi_eq_connected_component_of:
   "finite(connected_components_of X) \<or>
      finite(quasi_components_of X) \<or>
      locally_connected_space X \<or>
      compact_space X \<and> (Hausdorff_space X \<or> regular_space X \<or> normal_space X)
      \<Longrightarrow> quasi_component_of X x = connected_component_of X x"
sorry

subsection\<open>Additional quasicomponent and continuum properties like Boundary Bumping\<close>

lemma cut_wire_fence_theorem_gen:
  assumes "compact_space X" and X: "Hausdorff_space X \<or> regular_space X \<or> normal_space X"
    and S: "compactin X S" and T: "closedin X T"
    and dis: "\<And>C. connectedin X C \<Longrightarrow> disjnt C S \<or> disjnt C T"
  shows "separated_between X S T"
sorry

lemma cut_wire_fence_theorem:
   "\<lbrakk>compact_space X; Hausdorff_space X; closedin X S; closedin X T;
     \<And>C. connectedin X C \<Longrightarrow> disjnt C S \<or> disjnt C T\<rbrakk>
        \<Longrightarrow> separated_between X S T"
sorry

lemma separated_between_from_closed_subtopology:
  assumes XC: "separated_between (subtopology X C) S (X frontier_of C)" 
    and ST: "separated_between (subtopology X C) S T"
  shows "separated_between X S T"
sorry

lemma separated_between_from_closed_subtopology_frontier:
   "separated_between (subtopology X T) S (X frontier_of T)
        \<Longrightarrow> separated_between X S (X frontier_of T)"
sorry

lemma separated_between_from_frontier_of_closed_subtopology:
  assumes "separated_between (subtopology X T) S (X frontier_of T)"
  shows "separated_between X S (topspace X - T)"
sorry

lemma separated_between_compact_connected_component:
  assumes "locally_compact_space X" "Hausdorff_space X" 
    and C: "C \<in> connected_components_of X" 
    and "compactin X C" "closedin X T" "disjnt C T"
  shows "separated_between X C T"
sorry

lemma wilder_locally_compact_component_thm:
  assumes "locally_compact_space X" "Hausdorff_space X" 
    and "C \<in> connected_components_of X" "compactin X C" "openin X W" "C \<subseteq> W"
  obtains U V where "openin X U" "openin X V" "disjnt U V" "U \<union> V = topspace X" "C \<subseteq> U" "U \<subseteq> W"
sorry

lemma compact_quasi_eq_connected_components_of:
  assumes "locally_compact_space X" "Hausdorff_space X" "compactin X C"
  shows "C \<in> quasi_components_of X \<longleftrightarrow> C \<in> connected_components_of X"
sorry

lemma boundary_bumping_theorem_closed_gen:
  assumes "connected_space X" "locally_compact_space X" "Hausdorff_space X" "closedin X S" 
    "S \<noteq> topspace X" and C: "compactin X C" "C \<in> connected_components_of (subtopology X S)"
  shows "C \<inter> X frontier_of S \<noteq> {}"
sorry

lemma boundary_bumping_theorem_closed:
  assumes "connected_space X" "compact_space X" "Hausdorff_space X" "closedin X S" 
          "S \<noteq> topspace X" "C \<in> connected_components_of(subtopology X S)"
  shows "C \<inter> X frontier_of S \<noteq> {}"
sorry

lemma intermediate_continuum_exists:
  assumes "connected_space X" "locally_compact_space X" "Hausdorff_space X" 
    and C: "compactin X C" "connectedin X C" "C \<noteq> {}" "C \<noteq> topspace X"
    and U: "openin X U" "C \<subseteq> U"
  obtains D where "compactin X D" "connectedin X D" "C \<subset> D" "D \<subset> U"
sorry

lemma boundary_bumping_theorem_gen:
  assumes X: "connected_space X" "locally_compact_space X" "Hausdorff_space X" 
   and "S \<subset> topspace X" and C: "C \<in> connected_components_of(subtopology X S)" 
   and compC: "compactin X (X closure_of C)"
 shows "X frontier_of C \<inter> X frontier_of S \<noteq> {}"
sorry

lemma boundary_bumping_theorem:
   "\<lbrakk>connected_space X; compact_space X; Hausdorff_space X; S \<subset> topspace X; 
     C \<in> connected_components_of(subtopology X S)\<rbrakk>
    \<Longrightarrow> X frontier_of C \<inter> X frontier_of S \<noteq> {}"
sorry

subsection \<open>Compactly generated spaces (k-spaces)\<close>

text \<open>These don't have to be Hausdorff\<close>

definition k_space where
  "k_space X \<equiv>
    \<forall>S. S \<subseteq> topspace X \<longrightarrow> 
        (closedin X S \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> S)))"

lemma k_space:
   "k_space X \<longleftrightarrow>
    (\<forall>S. S \<subseteq> topspace X \<and>
         (\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> S)) \<longrightarrow> closedin X S)"
sorry

lemma k_space_open:
   "k_space X \<longleftrightarrow>
    (\<forall>S. S \<subseteq> topspace X \<and>
         (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S)) \<longrightarrow> openin X S)"
sorry

lemma k_space_alt:
   "k_space X \<longleftrightarrow>
    (\<forall>S. S \<subseteq> topspace X
        \<longrightarrow> (openin X S \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S))))"
sorry

lemma k_space_quotient_map_image:
  assumes q: "quotient_map X Y q" and X: "k_space X"
  shows "k_space Y"
sorry

lemma k_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; k_space X\<rbrakk> \<Longrightarrow> k_space Y"
sorry

lemma homeomorphic_k_space:
   "X homeomorphic_space Y \<Longrightarrow> k_space X \<longleftrightarrow> k_space Y"
sorry

lemma k_space_perfect_map_image:
   "\<lbrakk>k_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> k_space Y"
sorry

lemma locally_compact_imp_k_space:
  assumes "locally_compact_space X"
  shows "k_space X"
sorry

lemma compact_imp_k_space:
   "compact_space X \<Longrightarrow> k_space X"
sorry

lemma k_space_discrete_topology: "k_space(discrete_topology U)"
sorry

lemma k_space_closed_subtopology:
  assumes "k_space X" "closedin X C"
  shows "k_space (subtopology X C)"
sorry

lemma k_space_subtopology:
  assumes 1: "\<And>T. \<lbrakk>T \<subseteq> topspace X; T \<subseteq> S;
                   \<And>K. compactin X K \<Longrightarrow> closedin (subtopology X (K \<inter> S)) (K \<inter> T)\<rbrakk> \<Longrightarrow> closedin (subtopology X S) T"
  assumes 2: "\<And>K. compactin X K \<Longrightarrow> k_space(subtopology X (K \<inter> S))"
  shows "k_space (subtopology X S)"
sorry

lemma k_space_subtopology_open:
  assumes 1: "\<And>T. \<lbrakk>T \<subseteq> topspace X; T \<subseteq> S;
                    \<And>K. compactin X K \<Longrightarrow> openin (subtopology X (K \<inter> S)) (K \<inter> T)\<rbrakk> \<Longrightarrow> openin (subtopology X S) T"
  assumes 2: "\<And>K. compactin X K \<Longrightarrow> k_space(subtopology X (K \<inter> S))"
  shows "k_space (subtopology X S)"
sorry

lemma k_space_open_subtopology_aux:
  assumes "kc_space X" "compact_space X" "openin X V"
  shows "k_space (subtopology X V)"
sorry

lemma k_space_open_subtopology:
  assumes X: "kc_space X \<or> Hausdorff_space X \<or> regular_space X" and "k_space X" "openin X S"
  shows "k_space(subtopology X S)"
sorry

lemma k_kc_space_subtopology:
   "\<lbrakk>k_space X; kc_space X; openin X S \<or> closedin X S\<rbrakk> \<Longrightarrow> k_space(subtopology X S) \<and> kc_space(subtopology X S)"
sorry

lemma k_space_as_quotient_explicit:
  "k_space X \<longleftrightarrow> quotient_map (sum_topology (subtopology X) {K. compactin X K}) X snd"
sorry

lemma k_space_as_quotient:
  fixes X :: "'a topology"
  shows "k_space X \<longleftrightarrow> (\<exists>q. \<exists>Y:: ('a set * 'a) topology. locally_compact_space Y \<and> quotient_map Y X q)" 
         (is "?lhs=?rhs")
sorry

lemma k_space_prod_topology_left:
  assumes X: "locally_compact_space X" "Hausdorff_space X \<or> regular_space X" and "k_space Y"
  shows "k_space (prod_topology X Y)"
sorry

lemma k_space_prod_topology_right:
  assumes "k_space X" and Y: "locally_compact_space Y" "Hausdorff_space Y \<or> regular_space Y"
  shows "k_space (prod_topology X Y)"
sorry

lemma continuous_map_from_k_space:
  assumes "k_space X" and f: "\<And>K. compactin X K \<Longrightarrow> continuous_map(subtopology X K) Y f"
  shows "continuous_map X Y f"
sorry

lemma closed_map_into_k_space:
  assumes "k_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y"
    and f: "\<And>K. compactin Y K
                \<Longrightarrow> closed_map(subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f"
  shows "closed_map X Y f"
sorry
text \<open>Essentially the same proof\<close>
lemma open_map_into_k_space:
  assumes "k_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y"
    and f: "\<And>K. compactin Y K
                 \<Longrightarrow> open_map (subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f"
  shows "open_map X Y f"
sorry

lemma quotient_map_into_k_space:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "k_space Y" and cmf: "continuous_map X Y f" 
    and fim: "f ` (topspace X) = topspace Y"
    and f: "\<And>k. compactin Y k
                 \<Longrightarrow> quotient_map (subtopology X {x \<in> topspace X. f x \<in> k})
                                  (subtopology Y k) f"
  shows "quotient_map X Y f"
sorry

lemma quotient_map_into_k_space_eq:
  assumes "k_space Y" "kc_space Y"
  shows "quotient_map X Y f \<longleftrightarrow>
         continuous_map X Y f \<and> f ` (topspace X) = topspace Y \<and>
         (\<forall>K. compactin Y K
              \<longrightarrow> quotient_map (subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f)"
sorry

lemma open_map_into_k_space_eq:
  assumes "k_space Y"
  shows "open_map X Y f \<longleftrightarrow>
         f \<in> (topspace X) \<rightarrow> topspace Y \<and>
         (\<forall>k. compactin Y k
              \<longrightarrow> open_map (subtopology X {x \<in> topspace X. f x \<in> k}) (subtopology Y k) f)"
sorry

lemma closed_map_into_k_space_eq:
  assumes "k_space Y"
  shows "closed_map X Y f \<longleftrightarrow>
         f \<in> (topspace X) \<rightarrow> topspace Y \<and>
         (\<forall>k. compactin Y k
              \<longrightarrow> closed_map (subtopology X {x \<in> topspace X. f x \<in> k}) (subtopology Y k) f)"
       (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma proper_map_into_k_space:
  assumes "k_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y"
    and f: "\<And>K. compactin Y K
                 \<Longrightarrow> proper_map (subtopology X {x \<in> topspace X. f x \<in> K})
                                (subtopology Y K) f"
  shows "proper_map X Y f"
sorry

lemma proper_map_into_k_space_eq:
  assumes "k_space Y"
  shows "proper_map X Y f \<longleftrightarrow>
         f \<in> (topspace X) \<rightarrow> topspace Y \<and>
         (\<forall>K. compactin Y K
              \<longrightarrow> proper_map (subtopology X {x \<in> topspace X. f x \<in> K}) (subtopology Y K) f)"
         (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma compact_imp_proper_map:
  assumes "k_space Y" "kc_space Y" and fim: "f \<in> (topspace X) \<rightarrow> topspace Y" 
    and f: "continuous_map X Y f \<or> kc_space X" 
    and comp: "\<And>K. compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}"
  shows "proper_map X Y f"
sorry

lemma proper_eq_compact_map:
  assumes "k_space Y" "kc_space Y" 
    and f: "continuous_map X Y f \<or> kc_space X" 
  shows  "proper_map X Y f \<longleftrightarrow>
             f \<in> (topspace X) \<rightarrow> topspace Y \<and>
             (\<forall>K. compactin Y K \<longrightarrow> compactin X {x \<in> topspace X. f x \<in> K})"
         (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma compact_imp_perfect_map:
  assumes "k_space Y" "kc_space Y" and "f ` (topspace X) = topspace Y" 
    and "continuous_map X Y f" 
    and "\<And>K. compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}"
  shows "perfect_map X Y f"
sorry

end

