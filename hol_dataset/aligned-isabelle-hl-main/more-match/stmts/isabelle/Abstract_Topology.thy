(*  Author:     L C Paulson, University of Cambridge [ported from HOL Light] *)

section \<open>Operators involving abstract topology\<close>

theory Abstract_Topology
  imports
    Complex_Main
    "HOL-Library.Set_Idioms"
    "HOL-Library.FuncSet"
begin

subsection \<open>General notion of a topology as a value\<close>

definition\<^marker>\<open>tag important\<close> istopology :: "('a set \<Rightarrow> bool) \<Rightarrow> bool" where
  "istopology L \<equiv> (\<forall>S T. L S \<longrightarrow> L T \<longrightarrow> L (S \<inter> T)) \<and> (\<forall>\<K>. (\<forall>K\<in>\<K>. L K) \<longrightarrow> L (\<Union>\<K>))"

typedef\<^marker>\<open>tag important\<close> 'a topology = "{L::('a set) \<Rightarrow> bool. istopology L}"
  morphisms "openin" "topology"
  unfolding istopology_def by blast

lemma istopology_openin[iff]: "istopology(openin U)"
sorry

lemma istopology_open[iff]: "istopology open"
sorry

lemma topology_inverse' [simp]: "istopology U \<Longrightarrow> openin (topology U) = U"
sorry

lemma topology_inverse_iff: "istopology U \<longleftrightarrow> openin (topology U) = U"
sorry

lemma topology_eq: "T1 = T2 \<longleftrightarrow> (\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S)"
sorry


text\<open>The "universe": the union of all sets in the topology.\<close>
definition "topspace T = \<Union>{S. openin T S}"

subsubsection \<open>Main properties of open sets\<close>

proposition openin_clauses:
  fixes U :: "'a topology"
  shows
    "openin U {}"
    "\<And>S T. openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S\<inter>T)"
    "\<And>K. (\<forall>S \<in> K. openin U S) \<Longrightarrow> openin U (\<Union>K)"
sorry

lemma openin_subset: "openin U S \<Longrightarrow> S \<subseteq> topspace U"
sorry

lemma openin_empty[simp]: "openin U {}"
sorry

lemma openin_Int[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<inter> T)"
sorry

lemma openin_Union[intro]: "(\<And>S. S \<in> K \<Longrightarrow> openin U S) \<Longrightarrow> openin U (\<Union>K)"
sorry

lemma openin_Un[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<union> T)"
sorry

lemma openin_topspace[intro, simp]: "openin U (topspace U)"
sorry

lemma openin_subopen: "openin U S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>T. openin U T \<and> x \<in> T \<and> T \<subseteq> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma openin_INT [intro]:
  assumes "finite I"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T ((\<Inter>i \<in> I. U i) \<inter> topspace T)"
sorry

lemma openin_INT2 [intro]:
  assumes "finite I" "I \<noteq> {}"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T (\<Inter>i \<in> I. U i)"
sorry

lemma openin_Inter [intro]:
  assumes "finite \<F>" "\<F> \<noteq> {}" "\<And>X. X \<in> \<F> \<Longrightarrow> openin T X" shows "openin T (\<Inter>\<F>)"
sorry

lemma openin_Int_Inter:
  assumes "finite \<F>" "openin T U" "\<And>X. X \<in> \<F> \<Longrightarrow> openin T X" shows "openin T (U \<inter> \<Inter>\<F>)"
sorry

subsubsection \<open>Closed sets\<close>

definition\<^marker>\<open>tag important\<close> closedin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> bool" where
"closedin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> openin U (topspace U - S)"

lemma closedin_subset: "closedin U S \<Longrightarrow> S \<subseteq> topspace U"
sorry

lemma closedin_empty[simp]: "closedin U {}"
sorry

lemma closedin_topspace[intro, simp]: "closedin U (topspace U)"
sorry

lemma closedin_Un[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<union> T)"
sorry

lemma Diff_Inter[intro]: "A - \<Inter>S = \<Union>{A - s|s. s\<in>S}"
sorry

lemma closedin_Union:
  assumes "finite S" "\<And>T. T \<in> S \<Longrightarrow> closedin U T"
    shows "closedin U (\<Union>S)"
sorry

lemma closedin_Inter[intro]:
  assumes Ke: "K \<noteq> {}"
    and Kc: "\<And>S. S \<in>K \<Longrightarrow> closedin U S"
  shows "closedin U (\<Inter>K)"
sorry

lemma closedin_INT[intro]:
  assumes "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> closedin U (B x)"
  shows "closedin U (\<Inter>x\<in>A. B x)"
sorry

lemma closedin_Int[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<inter> T)"
sorry

lemma openin_closedin_eq: "openin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> closedin U (topspace U - S)"
sorry

lemma topology_finer_closedin:
  "topspace X = topspace Y \<Longrightarrow> (\<forall>S. openin Y S \<longrightarrow> openin X S) \<longleftrightarrow> (\<forall>S. closedin Y S \<longrightarrow> closedin X S)"
sorry

lemma openin_closedin: "S \<subseteq> topspace U \<Longrightarrow> (openin U S \<longleftrightarrow> closedin U (topspace U - S))"
sorry

lemma openin_diff[intro]:
  assumes oS: "openin U S"
    and cT: "closedin U T"
  shows "openin U (S - T)"
sorry

lemma closedin_diff[intro]:
  assumes oS: "closedin U S"
    and cT: "openin U T"
  shows "closedin U (S - T)"
sorry

lemma all_openin: "(\<forall>U. openin X U \<longrightarrow> P U) \<longleftrightarrow> (\<forall>U. closedin X U \<longrightarrow> P (topspace X - U))"
sorry

lemma all_closedin: "(\<forall>U. closedin X U \<longrightarrow> P U) \<longleftrightarrow> (\<forall>U. openin X U \<longrightarrow> P (topspace X - U))"
sorry

lemma ex_openin: "(\<exists>U. openin X U \<and> P U) \<longleftrightarrow> (\<exists>U. closedin X U \<and> P (topspace X - U))"
sorry

lemma ex_closedin: "(\<exists>U. closedin X U \<and> P U) \<longleftrightarrow> (\<exists>U. openin X U \<and> P (topspace X - U))"
sorry

subsection\<open>The discrete topology\<close>

definition discrete_topology where "discrete_topology U \<equiv> topology (\<lambda>S. S \<subseteq> U)"

lemma openin_discrete_topology [simp]: "openin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U"
sorry

lemma topspace_discrete_topology [simp]: "topspace(discrete_topology U) = U"
sorry

lemma closedin_discrete_topology [simp]: "closedin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U"
sorry

lemma discrete_topology_unique:
   "discrete_topology U = X \<longleftrightarrow> topspace X = U \<and> (\<forall>x \<in> U. openin X {x})" (is "?lhs = ?rhs")
sorry

lemma discrete_topology_unique_alt:
  "discrete_topology U = X \<longleftrightarrow> topspace X \<subseteq> U \<and> (\<forall>x \<in> U. openin X {x})"
sorry

lemma subtopology_eq_discrete_topology_empty:
   "X = discrete_topology {} \<longleftrightarrow> topspace X = {}"
sorry

lemma subtopology_eq_discrete_topology_sing:
   "X = discrete_topology {a} \<longleftrightarrow> topspace X = {a}"
sorry

abbreviation trivial_topology where "trivial_topology \<equiv> discrete_topology {}"

lemma null_topspace_iff_trivial [simp]: "topspace X = {} \<longleftrightarrow> X = trivial_topology"
sorry

subsection \<open>Subspace topology\<close>

definition\<^marker>\<open>tag important\<close> subtopology :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a topology" 
  where "subtopology U V = topology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"

lemma istopology_subtopology: "istopology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"
  (is "istopology ?L")
sorry

lemma openin_subtopology: "openin (subtopology U V) S \<longleftrightarrow> (\<exists>T. openin U T \<and> S = T \<inter> V)"
sorry

lemma subset_openin_subtopology:
   "\<lbrakk>openin X S; S \<subseteq> T\<rbrakk> \<Longrightarrow> openin (subtopology X T) S"
sorry

lemma openin_subtopology_Int:
   "openin X S \<Longrightarrow> openin (subtopology X T) (S \<inter> T)"
sorry

lemma openin_subtopology_Int2:
   "openin X T \<Longrightarrow> openin (subtopology X S) (S \<inter> T)"
sorry

lemma openin_subtopology_diff_closed:
   "\<lbrakk>S \<subseteq> topspace X; closedin X T\<rbrakk> \<Longrightarrow> openin (subtopology X S) (S - T)"
sorry

lemma openin_relative_to: "(openin X relative_to S) = openin (subtopology X S)"
sorry

lemma topspace_subtopology [simp]: "topspace (subtopology U V) = topspace U \<inter> V"
sorry

lemma topspace_subtopology_subset:
   "S \<subseteq> topspace X \<Longrightarrow> topspace(subtopology X S) = S"
sorry

lemma closedin_subtopology: "closedin (subtopology U V) S \<longleftrightarrow> (\<exists>T. closedin U T \<and> S = T \<inter> V)"
sorry

lemma closedin_subtopology_Int_closed:
   "closedin X T \<Longrightarrow> closedin (subtopology X S) (S \<inter> T)"
sorry

lemma closedin_subset_topspace:
   "\<lbrakk>closedin X S; S \<subseteq> T\<rbrakk> \<Longrightarrow> closedin (subtopology X T) S"
sorry

lemma closedin_relative_to:
   "(closedin X relative_to S) = closedin (subtopology X S)"
sorry

lemma openin_subtopology_refl: "openin (subtopology U V) V \<longleftrightarrow> V \<subseteq> topspace U"
sorry

lemma subtopology_trivial_iff: "subtopology X S = trivial_topology \<longleftrightarrow> X = trivial_topology \<or> topspace X \<inter> S = {}"
sorry

lemma subtopology_subtopology:
   "subtopology (subtopology X S) T = subtopology X (S \<inter> T)"
sorry

lemma openin_subtopology_alt:
     "openin (subtopology X U) S \<longleftrightarrow> S \<in> (\<lambda>T. U \<inter> T) ` Collect (openin X)"
sorry

lemma closedin_subtopology_alt:
     "closedin (subtopology X U) S \<longleftrightarrow> S \<in> (\<lambda>T. U \<inter> T) ` Collect (closedin X)"
sorry

lemma subtopology_superset:
  assumes UV: "topspace U \<subseteq> V"
  shows "subtopology U V = U"
sorry

lemma subtopology_topspace[simp]: "subtopology U (topspace U) = U"
sorry

lemma subtopology_UNIV[simp]: "subtopology U UNIV = U"
sorry

lemma subtopology_empty_iff_trivial [simp]: "subtopology X {} = trivial_topology"
sorry

lemma subtopology_restrict:
   "subtopology X (topspace X \<inter> S) = subtopology X S"
sorry

lemma openin_subtopology_empty:
  "openin (subtopology U {}) S \<longleftrightarrow> S = {}"
sorry

lemma closedin_subtopology_empty:
  "closedin (subtopology U {}) S \<longleftrightarrow> S = {}"
sorry

lemma closedin_subtopology_refl [simp]:
  "closedin (subtopology U X) X \<longleftrightarrow> X \<subseteq> topspace U"
sorry

lemma closedin_topspace_empty [simp]: "closedin trivial_topology S \<longleftrightarrow> S = {}"
sorry

lemma openin_topspace_empty [simp]:
   "openin trivial_topology S \<longleftrightarrow> S = {}"
sorry

lemma openin_imp_subset:
  "openin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
sorry

lemma closedin_imp_subset:
  "closedin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
sorry

lemma openin_open_subtopology:
     "openin X S \<Longrightarrow> openin (subtopology X S) T \<longleftrightarrow> openin X T \<and> T \<subseteq> S"
sorry

lemma closedin_closed_subtopology:
     "closedin X S \<Longrightarrow> (closedin (subtopology X S) T \<longleftrightarrow> closedin X T \<and> T \<subseteq> S)"
sorry

lemma closedin_trans_full:
   "\<lbrakk>closedin (subtopology X U) S; closedin X U\<rbrakk> \<Longrightarrow> closedin X S"
sorry

lemma openin_subtopology_Un:
    "\<lbrakk>openin (subtopology X T) S; openin (subtopology X U) S\<rbrakk>
     \<Longrightarrow> openin (subtopology X (T \<union> U)) S"
sorry

lemma closedin_subtopology_Un:
    "\<lbrakk>closedin (subtopology X T) S; closedin (subtopology X U) S\<rbrakk>
     \<Longrightarrow> closedin (subtopology X (T \<union> U)) S"
sorry

lemma openin_trans_full:
   "\<lbrakk>openin (subtopology X U) S; openin X U\<rbrakk> \<Longrightarrow> openin X S"
sorry

subsection \<open>The canonical topology from the underlying type class\<close>

abbreviation\<^marker>\<open>tag important\<close> euclidean :: "'a::topological_space topology"
  where "euclidean \<equiv> topology open"

abbreviation top_of_set :: "'a::topological_space set \<Rightarrow> 'a topology"
  where "top_of_set \<equiv> subtopology (topology open)"

lemma open_openin: "open S \<longleftrightarrow> openin euclidean S"
sorry

declare open_openin [symmetric, simp]

lemma topspace_euclidean [simp]: "topspace euclidean = UNIV"
sorry

lemma topspace_euclidean_subtopology[simp]: "topspace (top_of_set S) = S"
sorry

lemma closed_closedin: "closed S \<longleftrightarrow> closedin euclidean S"
sorry
declare closed_closedin [symmetric, simp]

lemma openin_subtopology_self [simp]: "openin (top_of_set S) S"
sorry

lemma euclidean_nontrivial [simp]: "euclidean \<noteq> trivial_topology"
sorry

subsubsection\<open>The most basic facts about the usual topology and metric on R\<close>

abbreviation euclideanreal :: "real topology"
  where "euclideanreal \<equiv> topology open"

subsection \<open>Basic "localization" results are handy for connectedness.\<close>

lemma openin_open: "openin (top_of_set U) S \<longleftrightarrow> (\<exists>T. open T \<and> (S = U \<inter> T))"
sorry

lemma openin_Int_open:
   "\<lbrakk>openin (top_of_set U) S; open T\<rbrakk>
        \<Longrightarrow> openin (top_of_set U) (S \<inter> T)"
sorry

lemma openin_open_Int[intro]: "open S \<Longrightarrow> openin (top_of_set U) (U \<inter> S)"
sorry

lemma open_openin_trans[trans]:
  "open S \<Longrightarrow> open T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> openin (top_of_set S) T"
sorry

lemma open_subset: "S \<subseteq> T \<Longrightarrow> open S \<Longrightarrow> openin (top_of_set T) S"
sorry

lemma closedin_closed: "closedin (top_of_set U) S \<longleftrightarrow> (\<exists>T. closed T \<and> S = U \<inter> T)"
sorry

lemma closedin_closed_Int: "closed S \<Longrightarrow> closedin (top_of_set U) (U \<inter> S)"
sorry

lemma closed_subset: "S \<subseteq> T \<Longrightarrow> closed S \<Longrightarrow> closedin (top_of_set T) S"
sorry

lemma closedin_closed_subset:
 "\<lbrakk>closedin (top_of_set U) V; T \<subseteq> U; S = V \<inter> T\<rbrakk>
             \<Longrightarrow> closedin (top_of_set T) S"
sorry

lemma finite_imp_closedin:
  fixes S :: "'a::t1_space set"
  shows "\<lbrakk>finite S; S \<subseteq> T\<rbrakk> \<Longrightarrow> closedin (top_of_set T) S"
sorry

lemma closedin_singleton [simp]:
  fixes a :: "'a::t1_space"
  shows "closedin (top_of_set U) {a} \<longleftrightarrow> a \<in> U"
sorry

lemma openin_euclidean_subtopology_iff:
  fixes S U :: "'a::metric_space set"
  shows "openin (top_of_set U) S \<longleftrightarrow>
    S \<subseteq> U \<and> (\<forall>x\<in>S. \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x'\<in> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma connected_openin:
      "connected S \<longleftrightarrow>
       \<not>(\<exists>E1 E2. openin (top_of_set S) E1 \<and>
                 openin (top_of_set S) E2 \<and>
                 S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
sorry

lemma connected_openin_eq:
      "connected S \<longleftrightarrow>
       \<not>(\<exists>E1 E2. openin (top_of_set S) E1 \<and>
                 openin (top_of_set S) E2 \<and>
                 E1 \<union> E2 = S \<and> E1 \<inter> E2 = {} \<and>
                 E1 \<noteq> {} \<and> E2 \<noteq> {})"
sorry

lemma connected_closedin:
      "connected S \<longleftrightarrow>
       (\<nexists>E1 E2.
        closedin (top_of_set S) E1 \<and>
        closedin (top_of_set S) E2 \<and>
        S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
       (is "?lhs = ?rhs")
sorry

lemma connected_closedin_eq:
      "connected S \<longleftrightarrow>
           \<not>(\<exists>E1 E2.
                 closedin (top_of_set S) E1 \<and>
                 closedin (top_of_set S) E2 \<and>
                 E1 \<union> E2 = S \<and> E1 \<inter> E2 = {} \<and>
                 E1 \<noteq> {} \<and> E2 \<noteq> {})"
sorry
text \<open>These "transitivity" results are handy too\<close>

lemma openin_trans[trans]:
  "openin (top_of_set T) S \<Longrightarrow> openin (top_of_set U) T \<Longrightarrow>
    openin (top_of_set U) S"
sorry

lemma openin_open_trans: "openin (top_of_set T) S \<Longrightarrow> open T \<Longrightarrow> open S"
sorry

lemma closedin_trans[trans]:
  "closedin (top_of_set T) S \<Longrightarrow> closedin (top_of_set U) T \<Longrightarrow>
    closedin (top_of_set U) S"
sorry

lemma closedin_closed_trans: "closedin (top_of_set T) S \<Longrightarrow> closed T \<Longrightarrow> closed S"
sorry

lemma openin_subtopology_Int_subset:
   "\<lbrakk>openin (top_of_set u) (u \<inter> S); v \<subseteq> u\<rbrakk> \<Longrightarrow> openin (top_of_set v) (v \<inter> S)"
sorry

lemma openin_open_eq: "open s \<Longrightarrow> (openin (top_of_set s) t \<longleftrightarrow> open t \<and> t \<subseteq> s)"
sorry

subsection\<open>Derived set (set of limit points)\<close>

definition derived_set_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl \<open>derived'_set'_of\<close> 80)
  where "X derived_set_of S \<equiv>
         {x \<in> topspace X.
                (\<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y\<noteq>x. y \<in> S \<and> y \<in> T))}"

lemma derived_set_of_restrict [simp]:
   "X derived_set_of (topspace X \<inter> S) = X derived_set_of S"
sorry

lemma in_derived_set_of:
   "x \<in> X derived_set_of S \<longleftrightarrow> x \<in> topspace X \<and> (\<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y\<noteq>x. y \<in> S \<and> y \<in> T))"
sorry

lemma derived_set_of_subset_topspace:
   "X derived_set_of S \<subseteq> topspace X"
sorry

lemma derived_set_of_subtopology:
   "(subtopology X U) derived_set_of S = U \<inter> (X derived_set_of (U \<inter> S))"
sorry

lemma derived_set_of_subset_subtopology:
   "(subtopology X S) derived_set_of T \<subseteq> S"
sorry

lemma derived_set_of_empty [simp]: "X derived_set_of {} = {}"
sorry

lemma derived_set_of_mono:
   "S \<subseteq> T \<Longrightarrow> X derived_set_of S \<subseteq> X derived_set_of T"
sorry

lemma derived_set_of_Un:
   "X derived_set_of (S \<union> T) = X derived_set_of S \<union> X derived_set_of T" (is "?lhs = ?rhs")
sorry

lemma derived_set_of_Union:
   "finite \<F> \<Longrightarrow> X derived_set_of (\<Union>\<F>) = (\<Union>S \<in> \<F>. X derived_set_of S)"
sorry

lemma derived_set_of_topspace:
  "X derived_set_of (topspace X) = {x \<in> topspace X. \<not> openin X {x}}" (is "?lhs = ?rhs")
sorry

lemma discrete_topology_unique_derived_set:
     "discrete_topology U = X \<longleftrightarrow> topspace X = U \<and> X derived_set_of U = {}"
sorry

lemma subtopology_eq_discrete_topology_eq:
   "subtopology X U = discrete_topology U \<longleftrightarrow> U \<subseteq> topspace X \<and> U \<inter> X derived_set_of U = {}"
sorry

lemma subtopology_eq_discrete_topology:
   "S \<subseteq> topspace X \<and> S \<inter> X derived_set_of S = {}
        \<Longrightarrow> subtopology X S = discrete_topology S"
sorry

lemma subtopology_eq_discrete_topology_gen:
  assumes "S \<inter> X derived_set_of S = {}"
  shows "subtopology X S = discrete_topology(topspace X \<inter> S)"
sorry

lemma subtopology_discrete_topology [simp]: 
  "subtopology (discrete_topology U) S = discrete_topology(U \<inter> S)"
sorry

lemma openin_Int_derived_set_of_subset:
   "openin X S \<Longrightarrow> S \<inter> X derived_set_of T \<subseteq> X derived_set_of (S \<inter> T)"
sorry

lemma openin_Int_derived_set_of_eq:
  assumes "openin X S"
  shows "S \<inter> X derived_set_of T = S \<inter> X derived_set_of (S \<inter> T)" (is "?lhs = ?rhs")
sorry


subsection\<open> Closure with respect to a topological space\<close>

definition closure_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr \<open>closure'_of\<close> 80)
  where "X closure_of S \<equiv> {x \<in> topspace X. \<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y \<in> S. y \<in> T)}"

lemma closure_of_restrict: "X closure_of S = X closure_of (topspace X \<inter> S)"
sorry

lemma in_closure_of:
   "x \<in> X closure_of S \<longleftrightarrow>
    x \<in> topspace X \<and> (\<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y. y \<in> S \<and> y \<in> T))"
sorry

lemma closure_of: "X closure_of S = topspace X \<inter> (S \<union> X derived_set_of S)"
sorry

lemma closure_of_alt: "X closure_of S = topspace X \<inter> S \<union> X derived_set_of S"
sorry

lemma derived_set_of_subset_closure_of:
   "X derived_set_of S \<subseteq> X closure_of S"
sorry

lemma closure_of_subtopology:
  "(subtopology X U) closure_of S = U \<inter> (X closure_of (U \<inter> S))"
sorry

lemma closure_of_empty [simp]: "X closure_of {} = {}"
sorry

lemma closure_of_topspace [simp]: "X closure_of topspace X = topspace X"
sorry

lemma closure_of_UNIV [simp]: "X closure_of UNIV = topspace X"
sorry

lemma closure_of_subset_topspace: "X closure_of S \<subseteq> topspace X"
sorry

lemma closure_of_subset_subtopology: "(subtopology X S) closure_of T \<subseteq> S"
sorry

lemma closure_of_mono: "S \<subseteq> T \<Longrightarrow> X closure_of S \<subseteq> X closure_of T"
sorry

lemma closure_of_subtopology_subset:
   "(subtopology X U) closure_of S \<subseteq> (X closure_of S)"
sorry

lemma closure_of_subtopology_mono:
   "T \<subseteq> U \<Longrightarrow> (subtopology X T) closure_of S \<subseteq> (subtopology X U) closure_of S"
sorry

lemma closure_of_Un [simp]: "X closure_of (S \<union> T) = X closure_of S \<union> X closure_of T"
sorry

lemma closure_of_Union:
   "finite \<F> \<Longrightarrow> X closure_of (\<Union>\<F>) = (\<Union>S \<in> \<F>. X closure_of S)"
sorry

lemma closure_of_subset: "S \<subseteq> topspace X \<Longrightarrow> S \<subseteq> X closure_of S"
sorry

lemma closure_of_subset_Int: "topspace X \<inter> S \<subseteq> X closure_of S"
sorry

lemma closure_of_subset_eq: "S \<subseteq> topspace X \<and> X closure_of S \<subseteq> S \<longleftrightarrow> closedin X S"
sorry

lemma closure_of_eq: "X closure_of S = S \<longleftrightarrow> closedin X S"
sorry

lemma closedin_contains_derived_set:
   "closedin X S \<longleftrightarrow> X derived_set_of S \<subseteq> S \<and> S \<subseteq> topspace X"
sorry

lemma derived_set_subset_gen:
   "X derived_set_of S \<subseteq> S \<longleftrightarrow> closedin X (topspace X \<inter> S)"
sorry

lemma derived_set_subset: "S \<subseteq> topspace X \<Longrightarrow> (X derived_set_of S \<subseteq> S \<longleftrightarrow> closedin X S)"
sorry

lemma closedin_derived_set:
     "closedin (subtopology X T) S \<longleftrightarrow>
      S \<subseteq> topspace X \<and> S \<subseteq> T \<and> (\<forall>x. x \<in> X derived_set_of S \<and> x \<in> T \<longrightarrow> x \<in> S)"
sorry

lemma closedin_Int_closure_of:
     "closedin (subtopology X S) T \<longleftrightarrow> S \<inter> X closure_of T = T"
sorry

lemma closure_of_closedin: "closedin X S \<Longrightarrow> X closure_of S = S"
sorry

lemma closure_of_eq_diff: "X closure_of S = topspace X - \<Union>{T. openin X T \<and> disjnt S T}"
sorry

lemma closedin_closure_of [simp]: "closedin X (X closure_of S)"
sorry

lemma closure_of_closure_of [simp]: "X closure_of (X closure_of S) = X closure_of S"
sorry

lemma closure_of_hull:
  assumes "S \<subseteq> topspace X" shows "X closure_of S = (closedin X) hull S"
sorry

lemma closure_of_minimal:
   "\<lbrakk>S \<subseteq> T; closedin X T\<rbrakk> \<Longrightarrow> (X closure_of S) \<subseteq> T"
sorry

lemma closure_of_minimal_eq:
   "\<lbrakk>S \<subseteq> topspace X; closedin X T\<rbrakk> \<Longrightarrow> (X closure_of S) \<subseteq> T \<longleftrightarrow> S \<subseteq> T"
sorry

lemma closure_of_unique:
   "\<lbrakk>S \<subseteq> T; closedin X T;
     \<And>T'. \<lbrakk>S \<subseteq> T'; closedin X T'\<rbrakk> \<Longrightarrow> T \<subseteq> T'\<rbrakk>
    \<Longrightarrow> X closure_of S = T"
sorry

lemma closure_of_eq_empty_gen: "X closure_of S = {} \<longleftrightarrow> disjnt (topspace X) S"
sorry

lemma closure_of_eq_empty: "S \<subseteq> topspace X \<Longrightarrow> X closure_of S = {} \<longleftrightarrow> S = {}"
sorry

lemma openin_Int_closure_of_subset:
  assumes "openin X S"
  shows "S \<inter> X closure_of T \<subseteq> X closure_of (S \<inter> T)"
sorry

lemma closure_of_openin_Int_closure_of:
  assumes "openin X S"
  shows "X closure_of (S \<inter> X closure_of T) = X closure_of (S \<inter> T)"
sorry

lemma openin_Int_closure_of_eq:
  assumes "openin X S" shows "S \<inter> X closure_of T = S \<inter> X closure_of (S \<inter> T)"  (is "?lhs = ?rhs")
sorry

lemma openin_Int_closure_of_eq_empty:
  assumes "openin X S" shows "S \<inter> X closure_of T = {} \<longleftrightarrow> S \<inter> T = {}"  (is "?lhs = ?rhs")
sorry

lemma closure_of_openin_Int_superset:
   "openin X S \<and> S \<subseteq> X closure_of T
        \<Longrightarrow> X closure_of (S \<inter> T) = X closure_of S"
sorry

lemma closure_of_openin_subtopology_Int_closure_of:
  assumes S: "openin (subtopology X U) S" and "T \<subseteq> U"
  shows "X closure_of (S \<inter> X closure_of T) = X closure_of (S \<inter> T)" (is "?lhs = ?rhs")
sorry

lemma closure_of_subtopology_open:
     "openin X U \<or> S \<subseteq> U \<Longrightarrow> (subtopology X U) closure_of S = U \<inter> X closure_of S"
sorry

lemma discrete_topology_closure_of:
     "(discrete_topology U) closure_of S = U \<inter> S"
sorry

text\<open> Interior with respect to a topological space.                             \<close>

definition interior_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr \<open>interior'_of\<close> 80)
  where "X interior_of S \<equiv> {x. \<exists>T. openin X T \<and> x \<in> T \<and> T \<subseteq> S}"

lemma interior_of_restrict:
   "X interior_of S = X interior_of (topspace X \<inter> S)"
sorry

lemma interior_of_eq: "(X interior_of S = S) \<longleftrightarrow> openin X S"
sorry

lemma interior_of_openin: "openin X S \<Longrightarrow> X interior_of S = S"
sorry

lemma interior_of_empty [simp]: "X interior_of {} = {}"
sorry

lemma interior_of_topspace [simp]: "X interior_of (topspace X) = topspace X"
sorry

lemma openin_interior_of [simp]: "openin X (X interior_of S)"
sorry

lemma interior_of_interior_of [simp]:
   "X interior_of X interior_of S = X interior_of S"
sorry

lemma interior_of_subset: "X interior_of S \<subseteq> S"
sorry

lemma interior_of_subset_closure_of: "X interior_of S \<subseteq> X closure_of S"
sorry

lemma subset_interior_of_eq: "S \<subseteq> X interior_of S \<longleftrightarrow> openin X S"
sorry

lemma interior_of_mono: "S \<subseteq> T \<Longrightarrow> X interior_of S \<subseteq> X interior_of T"
sorry

lemma interior_of_maximal: "\<lbrakk>T \<subseteq> S; openin X T\<rbrakk> \<Longrightarrow> T \<subseteq> X interior_of S"
sorry

lemma interior_of_maximal_eq: "openin X T \<Longrightarrow> T \<subseteq> X interior_of S \<longleftrightarrow> T \<subseteq> S"
sorry

lemma interior_of_unique:
   "\<lbrakk>T \<subseteq> S; openin X T; \<And>T'. \<lbrakk>T' \<subseteq> S; openin X T'\<rbrakk> \<Longrightarrow> T' \<subseteq> T\<rbrakk> \<Longrightarrow> X interior_of S = T"
sorry

lemma interior_of_subset_topspace: "X interior_of S \<subseteq> topspace X"
sorry

lemma interior_of_subset_subtopology: "(subtopology X S) interior_of T \<subseteq> S"
sorry

lemma interior_of_Int: "X interior_of (S \<inter> T) = X interior_of S \<inter> X interior_of T"  (is "?lhs = ?rhs")
sorry

lemma interior_of_Inter_subset: "X interior_of (\<Inter>\<F>) \<subseteq> (\<Inter>S \<in> \<F>. X interior_of S)"
sorry

lemma union_interior_of_subset:
   "X interior_of S \<union> X interior_of T \<subseteq> X interior_of (S \<union> T)"
sorry

lemma interior_of_eq_empty:
   "X interior_of S = {} \<longleftrightarrow> (\<forall>T. openin X T \<and> T \<subseteq> S \<longrightarrow> T = {})"
sorry

lemma interior_of_eq_empty_alt:
   "X interior_of S = {} \<longleftrightarrow> (\<forall>T. openin X T \<and> T \<noteq> {} \<longrightarrow> T - S \<noteq> {})"
sorry

lemma interior_of_Union_openin_subsets:
   "\<Union>{T. openin X T \<and> T \<subseteq> S} = X interior_of S"
sorry

lemma interior_of_complement:
   "X interior_of (topspace X - S) = topspace X - X closure_of S"
sorry

lemma interior_of_closure_of:
   "X interior_of S = topspace X - X closure_of (topspace X - S)"
sorry

lemma closure_of_interior_of:
   "X closure_of S = topspace X - X interior_of (topspace X - S)"
sorry

lemma closure_of_complement: "X closure_of (topspace X - S) = topspace X - X interior_of S"
sorry

lemma interior_of_eq_empty_complement:
  "X interior_of S = {} \<longleftrightarrow> X closure_of (topspace X - S) = topspace X"
sorry

lemma closure_of_eq_topspace:
   "X closure_of S = topspace X \<longleftrightarrow> X interior_of (topspace X - S) = {}"
sorry

lemma interior_of_subtopology_subset:
     "U \<inter> X interior_of S \<subseteq> (subtopology X U) interior_of S"
sorry

lemma interior_of_subtopology_subsets:
   "T \<subseteq> U \<Longrightarrow> T \<inter> (subtopology X U) interior_of S \<subseteq> (subtopology X T) interior_of S"
sorry

lemma interior_of_subtopology_mono:
   "\<lbrakk>S \<subseteq> T; T \<subseteq> U\<rbrakk> \<Longrightarrow> (subtopology X U) interior_of S \<subseteq> (subtopology X T) interior_of S"
sorry

lemma interior_of_subtopology_open:
  assumes "openin X U"
  shows "(subtopology X U) interior_of S = U \<inter> X interior_of S" (is "?lhs = ?rhs")
sorry

lemma dense_intersects_open:
   "X closure_of S = topspace X \<longleftrightarrow> (\<forall>T. openin X T \<and> T \<noteq> {} \<longrightarrow> S \<inter> T \<noteq> {})"
sorry

lemma interior_of_closedin_union_empty_interior_of:
  assumes "closedin X S" and disj: "X interior_of T = {}"
  shows "X interior_of (S \<union> T) = X interior_of S"
sorry

lemma interior_of_union_eq_empty:
   "closedin X S
        \<Longrightarrow> (X interior_of (S \<union> T) = {} \<longleftrightarrow>
             X interior_of S = {} \<and> X interior_of T = {})"
sorry

lemma discrete_topology_interior_of [simp]:
    "(discrete_topology U) interior_of S = U \<inter> S"
sorry
subsection \<open>Frontier with respect to topological space \<close>

definition frontier_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr \<open>frontier'_of\<close> 80)
  where "X frontier_of S \<equiv> X closure_of S - X interior_of S"

lemma frontier_of_closures:
     "X frontier_of S = X closure_of S \<inter> X closure_of (topspace X - S)"
sorry

lemma interior_of_union_frontier_of [simp]:
     "X interior_of S \<union> X frontier_of S = X closure_of S"
sorry

lemma frontier_of_restrict: "X frontier_of S = X frontier_of (topspace X \<inter> S)"
sorry

lemma closedin_frontier_of: "closedin X (X frontier_of S)"
sorry

lemma frontier_of_subset_topspace: "X frontier_of S \<subseteq> topspace X"
sorry

lemma frontier_of_subset_subtopology: "(subtopology X S) frontier_of T \<subseteq> S"
sorry

lemma frontier_of_subtopology_subset:
  "U \<inter> (subtopology X U) frontier_of S \<subseteq> (X frontier_of S)"
sorry

lemma frontier_of_subtopology_mono:
   "\<lbrakk>S \<subseteq> T; T \<subseteq> U\<rbrakk> \<Longrightarrow> (subtopology X T) frontier_of S \<subseteq> (subtopology X U) frontier_of S"
sorry

lemma clopenin_eq_frontier_of:
   "closedin X S \<and> openin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> X frontier_of S = {}"
sorry

lemma frontier_of_eq_empty:
     "S \<subseteq> topspace X \<Longrightarrow> (X frontier_of S = {} \<longleftrightarrow> closedin X S \<and> openin X S)"
sorry

lemma frontier_of_openin:
     "openin X S \<Longrightarrow> X frontier_of S = X closure_of S - S"
sorry

lemma frontier_of_openin_straddle_Int:
  assumes "openin X U" "U \<inter> X frontier_of S \<noteq> {}"
  shows "U \<inter> S \<noteq> {}" "U - S \<noteq> {}"
sorry

lemma frontier_of_subset_closedin: "closedin X S \<Longrightarrow> (X frontier_of S) \<subseteq> S"
sorry

lemma frontier_of_empty [simp]: "X frontier_of {} = {}"
sorry

lemma frontier_of_topspace [simp]: "X frontier_of topspace X = {}"
sorry

lemma frontier_of_subset_eq:
  assumes "S \<subseteq> topspace X"
  shows "(X frontier_of S) \<subseteq> S \<longleftrightarrow> closedin X S"
sorry

lemma frontier_of_complement: "X frontier_of (topspace X - S) = X frontier_of S"
sorry

lemma frontier_of_disjoint_eq:
  assumes "S \<subseteq> topspace X"
  shows "((X frontier_of S) \<inter> S = {} \<longleftrightarrow> openin X S)"
sorry

lemma frontier_of_disjoint_eq_alt:
  "S \<subseteq> (topspace X - X frontier_of S) \<longleftrightarrow> openin X S"
sorry

lemma frontier_of_Int:
     "X frontier_of (S \<inter> T) =
      X closure_of (S \<inter> T) \<inter> (X frontier_of S \<union> X frontier_of T)"
sorry

lemma frontier_of_Int_subset: "X frontier_of (S \<inter> T) \<subseteq> X frontier_of S \<union> X frontier_of T"
sorry

lemma frontier_of_Int_closedin:
  assumes "closedin X S" "closedin X T" 
  shows "X frontier_of(S \<inter> T) = X frontier_of S \<inter> T \<union> S \<inter> X frontier_of T"  (is "?lhs = ?rhs")
sorry

lemma frontier_of_Un_subset: "X frontier_of(S \<union> T) \<subseteq> X frontier_of S \<union> X frontier_of T"
sorry

lemma frontier_of_Union_subset:
   "finite \<F> \<Longrightarrow> X frontier_of (\<Union>\<F>) \<subseteq> (\<Union>T \<in> \<F>. X frontier_of T)"
sorry

lemma frontier_of_frontier_of_subset:
     "X frontier_of (X frontier_of S) \<subseteq> X frontier_of S"
sorry

lemma frontier_of_subtopology_open:
     "openin X U \<Longrightarrow> (subtopology X U) frontier_of S = U \<inter> X frontier_of S"
sorry

lemma discrete_topology_frontier_of [simp]:
     "(discrete_topology U) frontier_of S = {}"
sorry

lemma openin_subset_topspace_eq:
  assumes "disjnt S (X frontier_of U)"
  shows "openin (subtopology X U) S \<longleftrightarrow> openin X S \<and> S \<subseteq> U"
sorry


subsection\<open>Locally finite collections\<close>

definition locally_finite_in
  where
 "locally_finite_in X \<A> \<longleftrightarrow>
        (\<Union>\<A> \<subseteq> topspace X) \<and>
        (\<forall>x \<in> topspace X. \<exists>V. openin X V \<and> x \<in> V \<and> finite {U \<in> \<A>. U \<inter> V \<noteq> {}})"

lemma finite_imp_locally_finite_in:
   "\<lbrakk>finite \<A>; \<Union>\<A> \<subseteq> topspace X\<rbrakk> \<Longrightarrow> locally_finite_in X \<A>"
sorry

lemma locally_finite_in_subset:
  assumes "locally_finite_in X \<A>" "\<B> \<subseteq> \<A>"
  shows "locally_finite_in X \<B>"
sorry

lemma locally_finite_in_refinement:
  assumes \<A>: "locally_finite_in X \<A>" and f: "\<And>S. S \<in> \<A> \<Longrightarrow> f S \<subseteq> S"
  shows "locally_finite_in X (f ` \<A>)"
sorry

lemma locally_finite_in_subtopology:
  assumes \<A>: "locally_finite_in X \<A>" "\<Union>\<A> \<subseteq> S"
  shows "locally_finite_in (subtopology X S) \<A>"
sorry

lemma closedin_locally_finite_Union:
  assumes clo: "\<And>S. S \<in> \<A> \<Longrightarrow> closedin X S" and \<A>: "locally_finite_in X \<A>"
  shows "closedin X (\<Union>\<A>)"
sorry

lemma locally_finite_in_closure:
  assumes \<A>: "locally_finite_in X \<A>"
  shows "locally_finite_in X ((\<lambda>S. X closure_of S) ` \<A>)"
sorry

lemma closedin_Union_locally_finite_closure:
   "locally_finite_in X \<A> \<Longrightarrow> closedin X (\<Union>((\<lambda>S. X closure_of S) ` \<A>))"
sorry

lemma closure_of_Union_subset: "\<Union>((\<lambda>S. X closure_of S) ` \<A>) \<subseteq> X closure_of (\<Union>\<A>)"
sorry

lemma closure_of_locally_finite_Union:
  assumes "locally_finite_in X \<A>" 
  shows "X closure_of (\<Union>\<A>) = \<Union>((\<lambda>S. X closure_of S) ` \<A>)"
sorry


subsection\<^marker>\<open>tag important\<close> \<open>Continuous maps\<close>

text \<open>We will need to deal with continuous maps in terms of topologies and not in terms
of type classes, as defined below.\<close>

definition continuous_map where
  "continuous_map X Y f \<equiv>
     f \<in> topspace X \<rightarrow> topspace Y \<and>
     (\<forall>U. openin Y U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U})"

lemma continuous_map:
   "continuous_map X Y f \<longleftrightarrow>
        f ` (topspace X) \<subseteq> topspace Y \<and> (\<forall>U. openin Y U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U})"
sorry

lemma continuous_map_image_subset_topspace:
   "continuous_map X Y f \<Longrightarrow> f ` (topspace X) \<subseteq> topspace Y"
sorry

lemma continuous_map_funspace:
   "continuous_map X Y f \<Longrightarrow> f \<in> topspace X \<rightarrow> topspace Y"
sorry

lemma continuous_map_on_empty [simp]: "continuous_map trivial_topology Y f"
sorry

lemma continuous_map_on_empty2 [simp]: "continuous_map X trivial_topology f \<longleftrightarrow> X = trivial_topology"
sorry

lemma continuous_map_closedin:
   "continuous_map X Y f \<longleftrightarrow>
         f \<in> topspace X \<rightarrow> topspace Y \<and>
         (\<forall>C. closedin Y C \<longrightarrow> closedin X {x \<in> topspace X. f x \<in> C})"
sorry

lemma openin_continuous_map_preimage:
   "\<lbrakk>continuous_map X Y f; openin Y U\<rbrakk> \<Longrightarrow> openin X {x \<in> topspace X. f x \<in> U}"
sorry

lemma closedin_continuous_map_preimage:
   "\<lbrakk>continuous_map X Y f; closedin Y C\<rbrakk> \<Longrightarrow> closedin X {x \<in> topspace X. f x \<in> C}"
sorry

lemma openin_continuous_map_preimage_gen:
  assumes "continuous_map X Y f" "openin X U" "openin Y V"
  shows "openin X {x \<in> U. f x \<in> V}"
sorry

lemma closedin_continuous_map_preimage_gen:
  assumes "continuous_map X Y f" "closedin X U" "closedin Y V"
  shows "closedin X {x \<in> U. f x \<in> V}"
sorry

lemma continuous_map_image_closure_subset:
  assumes "continuous_map X Y f"
  shows "f ` (X closure_of S) \<subseteq> Y closure_of f ` S"
sorry

lemma continuous_map_subset_aux1: "continuous_map X Y f \<Longrightarrow>
       (\<forall>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
sorry

lemma continuous_map_subset_aux2:
  assumes "\<forall>S. S \<subseteq> topspace X \<longrightarrow> f ` (X closure_of S) \<subseteq> Y closure_of f ` S"
  shows "continuous_map X Y f"
sorry

lemma continuous_map_eq_image_closure_subset:
     "continuous_map X Y f \<longleftrightarrow> (\<forall>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
sorry

lemma continuous_map_eq_image_closure_subset_alt:
     "continuous_map X Y f \<longleftrightarrow> (\<forall>S. S \<subseteq> topspace X \<longrightarrow> f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
sorry

lemma continuous_map_eq_image_closure_subset_gen:
     "continuous_map X Y f \<longleftrightarrow>
        f \<in> topspace X \<rightarrow> topspace Y \<and>
        (\<forall>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
sorry

lemma continuous_map_closure_preimage_subset:
   "continuous_map X Y f
        \<Longrightarrow> X closure_of {x \<in> topspace X. f x \<in> T}
            \<subseteq> {x \<in> topspace X. f x \<in> Y closure_of T}"
sorry

lemma continuous_map_frontier_frontier_preimage_subset:
  assumes "continuous_map X Y f"
  shows "X frontier_of {x \<in> topspace X. f x \<in> T} \<subseteq> {x \<in> topspace X. f x \<in> Y frontier_of T}"
sorry

lemma topology_finer_continuous_id:
  assumes "topspace X = topspace Y" 
  shows "(\<forall>S. openin X S \<longrightarrow> openin Y S) \<longleftrightarrow> continuous_map Y X id"  (is "?lhs = ?rhs")
sorry

lemma continuous_map_const [simp]:
   "continuous_map X Y (\<lambda>x. C) \<longleftrightarrow> X = trivial_topology \<or> C \<in> topspace Y"
sorry

declare continuous_map_const [THEN iffD2, continuous_intros]

lemma continuous_map_compose [continuous_intros]:
  assumes f: "continuous_map X X' f" and g: "continuous_map X' X'' g"
  shows "continuous_map X X'' (g \<circ> f)"
sorry

lemma continuous_map_eq:
  assumes "continuous_map X X' f" and "\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x" 
  shows "continuous_map X X' g"
sorry

lemma restrict_continuous_map [simp]:
     "topspace X \<subseteq> S \<Longrightarrow> continuous_map X X' (restrict f S) \<longleftrightarrow> continuous_map X X' f"
sorry

lemma continuous_map_in_subtopology:
  "continuous_map X (subtopology X' S) f \<longleftrightarrow> continuous_map X X' f \<and> f ` (topspace X) \<subseteq> S"
  (is "?lhs = ?rhs")
sorry

lemma continuous_map_from_subtopology:
     "continuous_map X Y f \<Longrightarrow> continuous_map (subtopology X S) Y f"
sorry

lemma continuous_map_into_fulltopology:
   "continuous_map X (subtopology Y T) f \<Longrightarrow> continuous_map X Y f"
sorry

lemma continuous_map_into_subtopology:
   "\<lbrakk>continuous_map X Y f; f \<in> topspace X \<rightarrow> T\<rbrakk> \<Longrightarrow> continuous_map X (subtopology Y T) f"
sorry

lemma continuous_map_from_subtopology_mono:
     "\<lbrakk>continuous_map (subtopology X T) Y f; S \<subseteq> T\<rbrakk>
      \<Longrightarrow> continuous_map (subtopology X S) Y f"
sorry

lemma continuous_map_from_discrete_topology [simp]:
  "continuous_map (discrete_topology U) X f \<longleftrightarrow> f \<in> U \<rightarrow> topspace X"
sorry

lemma continuous_map_iff_continuous [simp]: "continuous_map (top_of_set S) euclidean g = continuous_on S g"
sorry

lemma continuous_map_iff_continuous2 [simp]: "continuous_map euclidean euclidean g = continuous_on UNIV g"
sorry

lemma continuous_map_openin_preimage_eq:
   "continuous_map X Y f \<longleftrightarrow>
        f \<in> (topspace X) \<rightarrow> topspace Y \<and> (\<forall>U. openin Y U \<longrightarrow> openin X (topspace X \<inter> f -` U))"
sorry

lemma continuous_map_closedin_preimage_eq:
   "continuous_map X Y f \<longleftrightarrow>
        f \<in> (topspace X) \<rightarrow> topspace Y \<and> (\<forall>U. closedin Y U \<longrightarrow> closedin X (topspace X \<inter> f -` U))"
sorry

lemma continuous_map_square_root: "continuous_map euclideanreal euclideanreal sqrt"
sorry

lemma continuous_map_sqrt [continuous_intros]:
   "continuous_map X euclideanreal f \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. sqrt(f x))"
sorry

lemma continuous_map_id [simp, continuous_intros]: "continuous_map X X id"
sorry
declare continuous_map_id [unfolded id_def, simp, continuous_intros]

lemma continuous_map_id_subt [simp]: "continuous_map (subtopology X S) X id"
sorry
declare continuous_map_id_subt [unfolded id_def, simp]


lemma\<^marker>\<open>tag important\<close> continuous_map_alt:
   "continuous_map T1 T2 f 
    = ((\<forall>U. openin T2 U \<longrightarrow> openin T1 (f -` U \<inter> topspace T1)) \<and> f \<in> topspace T1 \<rightarrow> topspace T2)"
sorry

lemma continuous_map_open [intro]:
  "continuous_map T1 T2 f \<Longrightarrow> openin T2 U \<Longrightarrow> openin T1 (f-`U \<inter> topspace(T1))"
sorry

lemma continuous_map_preimage_topspace [intro]:
  assumes "continuous_map T1 T2 f"
  shows "f-`(topspace T2) \<inter> topspace T1 = topspace T1"
sorry
subsection\<open>Open and closed maps (not a priori assumed continuous)\<close>

definition open_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "open_map X1 X2 f \<equiv> \<forall>U. openin X1 U \<longrightarrow> openin X2 (f ` U)"

definition closed_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "closed_map X1 X2 f \<equiv> \<forall>U. closedin X1 U \<longrightarrow> closedin X2 (f ` U)"

lemma open_map_imp_subset_topspace:
     "open_map X1 X2 f \<Longrightarrow> f \<in> (topspace X1) \<rightarrow> topspace X2"
sorry

lemma open_map_on_empty [simp]: "open_map trivial_topology Y f"
sorry

lemma closed_map_on_empty:
   "closed_map trivial_topology Y f"
sorry

lemma closed_map_const:
   "closed_map X Y (\<lambda>x. c) \<longleftrightarrow> X = trivial_topology \<or> closedin Y {c}"
sorry

lemma open_map_imp_subset:
    "\<lbrakk>open_map X1 X2 f; S \<subseteq> topspace X1\<rbrakk> \<Longrightarrow> f \<in> S \<rightarrow> topspace X2"
sorry

lemma topology_finer_open_id:
     "(\<forall>S. openin X S \<longrightarrow> openin X' S) \<longleftrightarrow> open_map X X' id"
sorry

lemma open_map_id: "open_map X X id"
sorry

lemma open_map_eq:
     "\<lbrakk>open_map X X' f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> open_map X X' g"
sorry

lemma open_map_inclusion_eq:
  "open_map (subtopology X S) X id \<longleftrightarrow> openin X (topspace X \<inter> S)"
sorry

lemma open_map_inclusion:
     "openin X S \<Longrightarrow> open_map (subtopology X S) X id"
sorry

lemma open_map_compose:
     "\<lbrakk>open_map X X' f; open_map X' X'' g\<rbrakk> \<Longrightarrow> open_map X X'' (g \<circ> f)"
sorry

lemma closed_map_imp_subset_topspace:
     "closed_map X1 X2 f \<Longrightarrow> f \<in> (topspace X1) \<rightarrow> topspace X2"
sorry

lemma closed_map_imp_subset:
     "\<lbrakk>closed_map X1 X2 f; S \<subseteq> topspace X1\<rbrakk> \<Longrightarrow> f \<in> S \<rightarrow> topspace X2"
sorry

lemma topology_finer_closed_id:
    "(\<forall>S. closedin X S \<longrightarrow> closedin X' S) \<longleftrightarrow> closed_map X X' id"
sorry

lemma closed_map_id: "closed_map X X id"
sorry

lemma closed_map_eq:
   "\<lbrakk>closed_map X X' f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> closed_map X X' g"
sorry

lemma closed_map_compose:
    "\<lbrakk>closed_map X X' f; closed_map X' X'' g\<rbrakk> \<Longrightarrow> closed_map X X'' (g \<circ> f)"
sorry

lemma closed_map_inclusion_eq:
   "closed_map (subtopology X S) X id \<longleftrightarrow>
        closedin X (topspace X \<inter> S)"
sorry

lemma closed_map_inclusion: "closedin X S \<Longrightarrow> closed_map (subtopology X S) X id"
sorry

lemma open_map_into_subtopology:
    "\<lbrakk>open_map X X' f; f \<in> topspace X \<rightarrow> S\<rbrakk> \<Longrightarrow> open_map X (subtopology X' S) f"
sorry

lemma closed_map_into_subtopology:
    "\<lbrakk>closed_map X X' f; f \<in> topspace X \<rightarrow> S\<rbrakk> \<Longrightarrow> closed_map X (subtopology X' S) f"
sorry

lemma open_map_into_discrete_topology:
    "open_map X (discrete_topology U) f \<longleftrightarrow> f \<in> (topspace X) \<rightarrow> U"
sorry

lemma closed_map_into_discrete_topology:
    "closed_map X (discrete_topology U) f \<longleftrightarrow> f \<in> (topspace X) \<rightarrow> U"
sorry

lemma bijective_open_imp_closed_map:
     "\<lbrakk>open_map X X' f; f ` (topspace X) = topspace X'; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> closed_map X X' f"
sorry

lemma bijective_closed_imp_open_map:
     "\<lbrakk>closed_map X X' f; f ` (topspace X) = topspace X'; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> open_map X X' f"
sorry

lemma open_map_from_subtopology:
     "\<lbrakk>open_map X X' f; openin X U\<rbrakk> \<Longrightarrow> open_map (subtopology X U) X' f"
sorry

lemma closed_map_from_subtopology:
     "\<lbrakk>closed_map X X' f; closedin X U\<rbrakk> \<Longrightarrow> closed_map (subtopology X U) X' f"
sorry

lemma open_map_restriction:
  assumes f: "open_map X X' f" and U: "{x \<in> topspace X. f x \<in> V} = U"
  shows "open_map (subtopology X U) (subtopology X' V) f"
sorry

lemma closed_map_restriction:
  assumes f: "closed_map X X' f" and U: "{x \<in> topspace X. f x \<in> V} = U"
  shows "closed_map (subtopology X U) (subtopology X' V) f"
sorry

lemma closed_map_closure_of_image:
   "closed_map X Y f \<longleftrightarrow>
        f \<in> topspace X \<rightarrow> topspace Y \<and>
        (\<forall>S. S \<subseteq> topspace X \<longrightarrow> Y closure_of (f ` S) \<subseteq> f ` (X closure_of S))" (is "?lhs=?rhs")
sorry

lemma open_map_interior_of_image_subset:
  "open_map X Y f \<longleftrightarrow> (\<forall>S. image f (X interior_of S) \<subseteq> Y interior_of (f ` S))"
sorry

lemma open_map_interior_of_image_subset_alt:
  "open_map X Y f \<longleftrightarrow> (\<forall>S\<subseteq>topspace X. f ` (X interior_of S) \<subseteq> Y interior_of f ` S)"
sorry

lemma open_map_interior_of_image_subset_gen:
  "open_map X Y f \<longleftrightarrow>
       (f \<in> topspace X \<rightarrow> topspace Y \<and> (\<forall>S. f ` (X interior_of S) \<subseteq> Y interior_of f ` S))"
sorry

lemma open_map_preimage_neighbourhood:
   "open_map X Y f \<longleftrightarrow>
    (f \<in> topspace X \<rightarrow> topspace Y \<and>
     (\<forall>U T. closedin X U \<and> T \<subseteq> topspace Y \<and>
            {x \<in> topspace X. f x \<in> T} \<subseteq> U \<longrightarrow>
            (\<exists>V. closedin Y V \<and> T \<subseteq> V \<and> {x \<in> topspace X. f x \<in> V} \<subseteq> U)))" (is "?lhs=?rhs")
sorry

lemma closed_map_preimage_neighbourhood:
   "closed_map X Y f \<longleftrightarrow>
        f \<in> topspace X \<rightarrow> topspace Y \<and>
        (\<forall>U T. openin X U \<and> T \<subseteq> topspace Y \<and>
              {x \<in> topspace X. f x \<in> T} \<subseteq> U
              \<longrightarrow> (\<exists>V. openin Y V \<and> T \<subseteq> V \<and>
                      {x \<in> topspace X. f x \<in> V} \<subseteq> U))" (is "?lhs=?rhs")
sorry

lemma closed_map_fibre_neighbourhood:
  "closed_map X Y f \<longleftrightarrow>
     f \<in> (topspace X) \<rightarrow> topspace Y \<and>
     (\<forall>U y. openin X U \<and> y \<in> topspace Y \<and> {x \<in> topspace X. f x = y} \<subseteq> U
     \<longrightarrow> (\<exists>V. openin Y V \<and> y \<in> V \<and> {x \<in> topspace X. f x \<in> V} \<subseteq> U))"
sorry

lemma open_map_in_subtopology:
   "openin Y S
        \<Longrightarrow> open_map X (subtopology Y S) f \<longleftrightarrow> open_map X Y f \<and> f \<in> topspace X \<rightarrow> S"
sorry

lemma open_map_from_open_subtopology:
   "\<lbrakk>openin Y S; open_map X (subtopology Y S) f\<rbrakk> \<Longrightarrow> open_map X Y f"
sorry

lemma closed_map_in_subtopology:
   "closedin Y S
        \<Longrightarrow> closed_map X (subtopology Y S) f \<longleftrightarrow> (closed_map X Y f \<and> f \<in> topspace X \<rightarrow> S)"
sorry

lemma closed_map_from_closed_subtopology:
   "\<lbrakk>closedin Y S; closed_map X (subtopology Y S) f\<rbrakk> \<Longrightarrow> closed_map X Y f"
sorry

lemma closed_map_from_composition_left:
  assumes cmf: "closed_map X Z (g \<circ> f)" and contf: "continuous_map X Y f" and fim: "f ` topspace X = topspace Y"
  shows "closed_map Y Z g"
sorry
text \<open>identical proof as the above\<close>
lemma open_map_from_composition_left:
  assumes cmf: "open_map X Z (g \<circ> f)" and contf: "continuous_map X Y f" and fim: "f ` topspace X = topspace Y"
  shows "open_map Y Z g"
sorry

lemma closed_map_from_composition_right:
  assumes cmf: "closed_map X Z (g \<circ> f)" "f \<in> topspace X \<rightarrow> topspace Y" "continuous_map Y Z g" "inj_on g (topspace Y)"
  shows "closed_map X Y f"
sorry
text \<open>identical proof as the above\<close>
lemma open_map_from_composition_right:
  assumes "open_map X Z (g \<circ> f)" "f \<in> topspace X \<rightarrow> topspace Y" "continuous_map Y Z g" "inj_on g (topspace Y)"
  shows "open_map X Y f"
sorry
subsection\<open>Quotient maps\<close>
                                      
definition quotient_map where
 "quotient_map X X' f \<longleftrightarrow>
        f ` (topspace X) = topspace X' \<and>
        (\<forall>U. U \<subseteq> topspace X' \<longrightarrow> (openin X {x. x \<in> topspace X \<and> f x \<in> U} \<longleftrightarrow> openin X' U))"

lemma quotient_map_eq:
  assumes "quotient_map X X' f" "\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x"
  shows "quotient_map X X' g"
sorry

lemma quotient_map_compose:
  assumes f: "quotient_map X X' f" and g: "quotient_map X' X'' g"
  shows "quotient_map X X'' (g \<circ> f)"
sorry

lemma quotient_map_from_composition:
  assumes f: "continuous_map X X' f" and g: "continuous_map X' X'' g" and gf: "quotient_map X X'' (g \<circ> f)"
  shows  "quotient_map X' X'' g"
sorry

lemma quotient_imp_continuous_map:
    "quotient_map X X' f \<Longrightarrow> continuous_map X X' f"
sorry

lemma quotient_imp_surjective_map:
    "quotient_map X X' f \<Longrightarrow> f ` (topspace X) = topspace X'"
sorry

lemma quotient_map_closedin:
  "quotient_map X X' f \<longleftrightarrow>
        f ` (topspace X) = topspace X' \<and>
        (\<forall>U. U \<subseteq> topspace X' \<longrightarrow> (closedin X {x. x \<in> topspace X \<and> f x \<in> U} \<longleftrightarrow> closedin X' U))"
sorry

lemma continuous_open_imp_quotient_map:
  assumes "continuous_map X X' f" and om: "open_map X X' f" and feq: "f ` (topspace X) = topspace X'"
  shows "quotient_map X X' f"
sorry

lemma continuous_closed_imp_quotient_map:
  assumes "continuous_map X X' f" and om: "closed_map X X' f" and feq: "f ` (topspace X) = topspace X'"
  shows "quotient_map X X' f"
sorry

lemma continuous_open_quotient_map:
   "\<lbrakk>continuous_map X X' f; open_map X X' f\<rbrakk> \<Longrightarrow> quotient_map X X' f \<longleftrightarrow> f ` (topspace X) = topspace X'"
sorry

lemma continuous_closed_quotient_map:
     "\<lbrakk>continuous_map X X' f; closed_map X X' f\<rbrakk> \<Longrightarrow> quotient_map X X' f \<longleftrightarrow> f ` (topspace X) = topspace X'"
sorry

lemma injective_quotient_map:
  assumes "inj_on f (topspace X)"
  shows "quotient_map X X' f \<longleftrightarrow>
         continuous_map X X' f \<and> open_map X X' f \<and> closed_map X X' f \<and> f ` (topspace X) = topspace X'"
         (is "?lhs = ?rhs")
sorry

lemma continuous_compose_quotient_map:
  assumes f: "quotient_map X X' f" and g: "continuous_map X X'' (g \<circ> f)"
  shows "continuous_map X' X'' g"
sorry

lemma continuous_compose_quotient_map_eq:
   "quotient_map X X' f \<Longrightarrow> continuous_map X X'' (g \<circ> f) \<longleftrightarrow> continuous_map X' X'' g"
sorry

lemma quotient_map_compose_eq:
   "quotient_map X X' f \<Longrightarrow> quotient_map X X'' (g \<circ> f) \<longleftrightarrow> quotient_map X' X'' g"
sorry

lemma quotient_map_restriction:
  assumes quo: "quotient_map X Y f" and U: "{x \<in> topspace X. f x \<in> V} = U" and disj: "openin Y V \<or> closedin Y V"
 shows "quotient_map (subtopology X U) (subtopology Y V) f"
sorry

lemma quotient_map_saturated_open:
     "quotient_map X Y f \<longleftrightarrow>
        continuous_map X Y f \<and> f ` (topspace X) = topspace Y \<and>
        (\<forall>U. openin X U \<and> {x \<in> topspace X. f x \<in> f ` U} \<subseteq> U \<longrightarrow> openin Y (f ` U))"
     (is "?lhs = ?rhs")
sorry

lemma quotient_map_saturated_closed:
     "quotient_map X Y f \<longleftrightarrow>
        continuous_map X Y f \<and> f ` (topspace X) = topspace Y \<and>
        (\<forall>U. closedin X U \<and> {x \<in> topspace X. f x \<in> f ` U} \<subseteq> U \<longrightarrow> closedin Y (f ` U))"
     (is "?lhs = ?rhs")
sorry

lemma quotient_map_onto_image:
  assumes "f ` topspace X \<subseteq> topspace Y" and U: "\<And>U. U \<subseteq> topspace Y \<Longrightarrow> openin X {x \<in> topspace X. f x \<in> U} = openin Y U"
  shows "quotient_map X (subtopology Y (f ` topspace X)) f"
sorry

lemma quotient_map_lift_exists:
  assumes f: "quotient_map X Y f" and h: "continuous_map X Z h" 
    and "\<And>x y. \<lbrakk>x \<in> topspace X; y \<in> topspace X; f x = f y\<rbrakk> \<Longrightarrow> h x = h y"
  obtains g where "continuous_map Y Z g" "g ` topspace Y = h ` topspace X"
                  "\<And>x. x \<in> topspace X \<Longrightarrow> g(f x) = h x"
sorry


subsection\<open> Separated Sets\<close>

definition separatedin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "separatedin X S T \<equiv>
           S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and>
           S \<inter> X closure_of T = {} \<and> T \<inter> X closure_of S = {}"

lemma separatedin_empty [simp]:
     "separatedin X S {} \<longleftrightarrow> S \<subseteq> topspace X"
     "separatedin X {} S \<longleftrightarrow> S \<subseteq> topspace X"
sorry

lemma separatedin_refl [simp]:
     "separatedin X S S \<longleftrightarrow> S = {}"
sorry

lemma separatedin_sym:
     "separatedin X S T \<longleftrightarrow> separatedin X T S"
sorry

lemma separatedin_imp_disjoint:
     "separatedin X S T \<Longrightarrow> disjnt S T"
sorry

lemma separatedin_mono:
   "\<lbrakk>separatedin X S T; S' \<subseteq> S; T' \<subseteq> T\<rbrakk> \<Longrightarrow> separatedin X S' T'"
sorry

lemma separatedin_open_sets:
     "\<lbrakk>openin X S; openin X T\<rbrakk> \<Longrightarrow> separatedin X S T \<longleftrightarrow> disjnt S T"
sorry

lemma separatedin_closed_sets:
     "\<lbrakk>closedin X S; closedin X T\<rbrakk> \<Longrightarrow> separatedin X S T \<longleftrightarrow> disjnt S T"
sorry

lemma separatedin_subtopology:
     "separatedin (subtopology X U) S T \<longleftrightarrow> S \<subseteq> U \<and> T \<subseteq> U \<and> separatedin X S T"
sorry

lemma separatedin_discrete_topology:
     "separatedin (discrete_topology U) S T \<longleftrightarrow> S \<subseteq> U \<and> T \<subseteq> U \<and> disjnt S T"
sorry

lemma separated_eq_distinguishable:
   "separatedin X {x} {y} \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        (\<exists>U. openin X U \<and> x \<in> U \<and> (y \<notin> U)) \<and>
        (\<exists>v. openin X v \<and> y \<in> v \<and> (x \<notin> v))"
sorry

lemma separatedin_Un [simp]:
   "separatedin X S (T \<union> U) \<longleftrightarrow> separatedin X S T \<and> separatedin X S U"
   "separatedin X (S \<union> T) U \<longleftrightarrow> separatedin X S U \<and> separatedin X T U"
sorry

lemma separatedin_Union:
  "finite \<F> \<Longrightarrow> separatedin X S (\<Union>\<F>) \<longleftrightarrow> S \<subseteq> topspace X \<and> (\<forall>T \<in> \<F>. separatedin X S T)"
  "finite \<F> \<Longrightarrow> separatedin X (\<Union>\<F>) S \<longleftrightarrow> (\<forall>T \<in> \<F>. separatedin X S T) \<and> S \<subseteq> topspace X"
sorry

lemma separatedin_openin_diff:
   "\<lbrakk>openin X S; openin X T\<rbrakk> \<Longrightarrow> separatedin X (S - T) (T - S)"
sorry

lemma separatedin_closedin_diff:
  assumes "closedin X S" "closedin X T"
  shows "separatedin X (S - T) (T - S)"
sorry

lemma separation_closedin_Un_gen:
     "separatedin X S T \<longleftrightarrow>
        S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and> disjnt S T \<and>
        closedin (subtopology X (S \<union> T)) S \<and>
        closedin (subtopology X (S \<union> T)) T"
sorry

lemma separation_openin_Un_gen:
     "separatedin X S T \<longleftrightarrow>
        S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and> disjnt S T \<and>
        openin (subtopology X (S \<union> T)) S \<and>
        openin (subtopology X (S \<union> T)) T"
sorry

lemma separatedin_full:
   "S \<union> T = topspace X
   \<Longrightarrow> separatedin X S T \<longleftrightarrow> disjnt S T \<and> closedin X S \<and> openin X S \<and> closedin X T \<and> openin X T"
sorry

subsection\<open>Homeomorphisms\<close>
text\<open>(1-way and 2-way versions may be useful in places)\<close>

definition homeomorphic_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
 "homeomorphic_map X Y f \<equiv> quotient_map X Y f \<and> inj_on f (topspace X)"

definition homeomorphic_maps :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where
 "homeomorphic_maps X Y f g \<equiv>
    continuous_map X Y f \<and> continuous_map Y X g \<and>
     (\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"


lemma homeomorphic_map_eq:
   "\<lbrakk>homeomorphic_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> homeomorphic_map X Y g"
sorry

lemma homeomorphic_maps_eq:
     "\<lbrakk>homeomorphic_maps X Y f g;
       \<And>x. x \<in> topspace X \<Longrightarrow> f x = f' x; \<And>y. y \<in> topspace Y \<Longrightarrow> g y = g' y\<rbrakk>
      \<Longrightarrow> homeomorphic_maps X Y f' g'"
sorry

lemma homeomorphic_maps_sym:
     "homeomorphic_maps X Y f g \<longleftrightarrow> homeomorphic_maps Y X g f"
sorry

lemma homeomorphic_maps_id:
     "homeomorphic_maps X Y id id \<longleftrightarrow> Y = X"  (is "?lhs = ?rhs")
sorry

lemma homeomorphic_map_id [simp]: "homeomorphic_map X Y id \<longleftrightarrow> Y = X"
       (is "?lhs = ?rhs")
sorry

lemma homeomorphic_map_compose:
  assumes "homeomorphic_map X Y f" "homeomorphic_map Y X'' g"
  shows "homeomorphic_map X X'' (g \<circ> f)"
sorry

lemma homeomorphic_maps_compose:
   "homeomorphic_maps X Y f h \<and>
        homeomorphic_maps Y X'' g k
        \<Longrightarrow> homeomorphic_maps X X'' (g \<circ> f) (h \<circ> k)"
sorry

lemma homeomorphic_eq_everything_map:
   "homeomorphic_map X Y f \<longleftrightarrow>
        continuous_map X Y f \<and> open_map X Y f \<and> closed_map X Y f \<and>
        f ` (topspace X) = topspace Y \<and> inj_on f (topspace X)"
sorry

lemma homeomorphic_imp_continuous_map:
     "homeomorphic_map X Y f \<Longrightarrow> continuous_map X Y f"
sorry

lemma homeomorphic_imp_open_map:
   "homeomorphic_map X Y f \<Longrightarrow> open_map X Y f"
sorry

lemma homeomorphic_imp_closed_map:
   "homeomorphic_map X Y f \<Longrightarrow> closed_map X Y f"
sorry

lemma homeomorphic_imp_surjective_map:
   "homeomorphic_map X Y f \<Longrightarrow> f ` topspace X = topspace Y"
sorry

lemma homeomorphic_imp_injective_map:
    "homeomorphic_map X Y f \<Longrightarrow> inj_on f (topspace X)"
sorry

lemma bijective_open_imp_homeomorphic_map:
   "\<lbrakk>continuous_map X Y f; open_map X Y f; f ` (topspace X) = topspace Y; inj_on f (topspace X)\<rbrakk>
        \<Longrightarrow> homeomorphic_map X Y f"
sorry

lemma bijective_closed_imp_homeomorphic_map:
   "\<lbrakk>continuous_map X Y f; closed_map X Y f; f ` (topspace X) = topspace Y; inj_on f (topspace X)\<rbrakk>
        \<Longrightarrow> homeomorphic_map X Y f"
sorry

lemma open_eq_continuous_inverse_map:
  assumes X: "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y \<and> g(f x) = x"
    and Y: "\<And>y. y \<in> topspace Y \<Longrightarrow> g y \<in> topspace X \<and> f(g y) = y"
  shows "open_map X Y f \<longleftrightarrow> continuous_map Y X g"
sorry

lemma closed_eq_continuous_inverse_map:
  assumes X: "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y \<and> g(f x) = x"
    and Y: "\<And>y. y \<in> topspace Y \<Longrightarrow> g y \<in> topspace X \<and> f(g y) = y"
  shows "closed_map X Y f \<longleftrightarrow> continuous_map Y X g"
sorry

lemma homeomorphic_maps_map:
  "homeomorphic_maps X Y f g \<longleftrightarrow>
        homeomorphic_map X Y f \<and> homeomorphic_map Y X g \<and>
        (\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
  (is "?lhs = ?rhs")
sorry

lemma homeomorphic_maps_imp_map:
    "homeomorphic_maps X Y f g \<Longrightarrow> homeomorphic_map X Y f"
sorry

lemma homeomorphic_map_maps:
     "homeomorphic_map X Y f \<longleftrightarrow> (\<exists>g. homeomorphic_maps X Y f g)"
  (is "?lhs = ?rhs")
sorry

lemma homeomorphic_maps_involution:
   "\<lbrakk>continuous_map X X f; \<And>x. x \<in> topspace X \<Longrightarrow> f(f x) = x\<rbrakk> \<Longrightarrow> homeomorphic_maps X X f f"
sorry

lemma homeomorphic_map_involution:
   "\<lbrakk>continuous_map X X f; \<And>x. x \<in> topspace X \<Longrightarrow> f(f x) = x\<rbrakk> \<Longrightarrow> homeomorphic_map X X f"
sorry

lemma homeomorphic_map_openness:
  assumes hom: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "openin Y (f ` U) \<longleftrightarrow> openin X U"
sorry

lemma homeomorphic_map_closedness:
  assumes hom: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "closedin Y (f ` U) \<longleftrightarrow> closedin X U"
sorry

lemma homeomorphic_map_openness_eq:
     "homeomorphic_map X Y f \<Longrightarrow> openin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> openin Y (f ` U)"
sorry

lemma homeomorphic_map_closedness_eq:
    "homeomorphic_map X Y f \<Longrightarrow> closedin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> closedin Y (f ` U)"
sorry

lemma all_openin_homeomorphic_image:
  assumes "homeomorphic_map X Y f"
  shows "(\<forall>V. openin Y V \<longrightarrow> P V) \<longleftrightarrow> (\<forall>U. openin X U \<longrightarrow> P(f ` U))"
sorry

lemma all_closedin_homeomorphic_image:
  assumes "homeomorphic_map X Y f"
  shows "(\<forall>V. closedin Y V \<longrightarrow> P V) \<longleftrightarrow> (\<forall>U. closedin X U \<longrightarrow> P(f ` U))"
sorry

lemma homeomorphic_map_derived_set_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y derived_set_of (f ` S) = f ` (X derived_set_of S)"
sorry

lemma homeomorphic_map_closure_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y closure_of (f ` S) = f ` (X closure_of S)"
sorry

lemma homeomorphic_map_interior_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y interior_of (f ` S) = f ` (X interior_of S)"
sorry

lemma homeomorphic_map_frontier_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y frontier_of (f ` S) = f ` (X frontier_of S)"
sorry

lemma homeomorphic_maps_subtopologies:
   "\<lbrakk>homeomorphic_maps X Y f g;  f ` (topspace X \<inter> S) = topspace Y \<inter> T\<rbrakk>
        \<Longrightarrow> homeomorphic_maps (subtopology X S) (subtopology Y T) f g"
sorry

lemma homeomorphic_maps_subtopologies_alt:
     "\<lbrakk>homeomorphic_maps X Y f g; f ` (topspace X \<inter> S) \<subseteq> T; g ` (topspace Y \<inter> T) \<subseteq> S\<rbrakk>
      \<Longrightarrow> homeomorphic_maps (subtopology X S) (subtopology Y T) f g"
sorry

lemma homeomorphic_map_subtopologies:
   "\<lbrakk>homeomorphic_map X Y f; f ` (topspace X \<inter> S) = topspace Y \<inter> T\<rbrakk>
        \<Longrightarrow> homeomorphic_map (subtopology X S) (subtopology Y T) f"
sorry

lemma homeomorphic_map_subtopologies_alt:
  assumes hom: "homeomorphic_map X Y f" 
      and S: "\<And>x. \<lbrakk>x \<in> topspace X; f x \<in> topspace Y\<rbrakk> \<Longrightarrow> f x \<in> T \<longleftrightarrow> x \<in> S"
    shows "homeomorphic_map (subtopology X S) (subtopology Y T) f"
sorry


subsection\<open>Relation of homeomorphism between topological spaces\<close>

definition homeomorphic_space (infixr \<open>homeomorphic'_space\<close> 50)
  where "X homeomorphic_space Y \<equiv> \<exists>f g. homeomorphic_maps X Y f g"

lemma homeomorphic_space_refl [iff]: "X homeomorphic_space X"
sorry

lemma homeomorphic_space_sym:
   "X homeomorphic_space Y \<longleftrightarrow> Y homeomorphic_space X"
sorry

lemma homeomorphic_space_trans [trans]:
     "\<lbrakk>X1 homeomorphic_space X2; X2 homeomorphic_space X3\<rbrakk> \<Longrightarrow> X1 homeomorphic_space X3"
sorry

lemma homeomorphic_space:
     "X homeomorphic_space Y \<longleftrightarrow> (\<exists>f. homeomorphic_map X Y f)"
sorry

lemma homeomorphic_maps_imp_homeomorphic_space:
     "homeomorphic_maps X Y f g \<Longrightarrow> X homeomorphic_space Y"
sorry

lemma homeomorphic_map_imp_homeomorphic_space:
     "homeomorphic_map X Y f \<Longrightarrow> X homeomorphic_space Y"
sorry

lemma homeomorphic_empty_space:
     "X homeomorphic_space Y \<Longrightarrow> X = trivial_topology \<longleftrightarrow> Y = trivial_topology"
sorry

lemma homeomorphic_empty_space_eq:
  assumes "X = trivial_topology"
  shows "X homeomorphic_space Y \<longleftrightarrow> Y = trivial_topology"
sorry

lemma homeomorphic_space_unfold:
  assumes "X homeomorphic_space Y"
  obtains f g where  "homeomorphic_map X Y f"  "homeomorphic_map Y X g"
    and "\<And>x. x \<in> topspace X \<Longrightarrow> g(f x) = x" "\<And>y. y \<in> topspace Y \<Longrightarrow> f(g y) = y"
    and "f \<in> topspace X \<rightarrow> topspace Y"  "g \<in> topspace Y \<rightarrow> topspace X"
sorry
subsection\<open>Connected topological spaces\<close>

definition connected_space :: "'a topology \<Rightarrow> bool" where
  "connected_space X \<equiv>
        \<not>(\<exists>E1 E2. openin X E1 \<and> openin X E2 \<and>
                  topspace X \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"

definition connectedin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> bool" where
  "connectedin X S \<equiv> S \<subseteq> topspace X \<and> connected_space (subtopology X S)"

lemma connected_spaceD:
  "\<lbrakk>connected_space X;
    openin X U; openin X V; topspace X \<subseteq> U \<union> V; U \<inter> V = {}; U \<noteq> {}; V \<noteq> {}\<rbrakk> \<Longrightarrow> False"
sorry

lemma connectedin_subset_topspace: "connectedin X S \<Longrightarrow> S \<subseteq> topspace X"
sorry

lemma connectedin_topspace:
     "connectedin X (topspace X) \<longleftrightarrow> connected_space X"
sorry

lemma connected_space_subtopology:
     "connectedin X S \<Longrightarrow> connected_space (subtopology X S)"
sorry

lemma connectedin_subtopology:
     "connectedin (subtopology X S) T \<longleftrightarrow> connectedin X T \<and> T \<subseteq> S"
sorry

lemma connected_space_eq:
     "connected_space X \<longleftrightarrow>
      (\<nexists>E1 E2. openin X E1 \<and> openin X E2 \<and> E1 \<union> E2 = topspace X \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
sorry

lemma connected_space_closedin:
     "connected_space X \<longleftrightarrow>
      (\<nexists>E1 E2. closedin X E1 \<and> closedin X E2 \<and> topspace X \<subseteq> E1 \<union> E2 \<and>
               E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})" (is "?lhs = ?rhs")
sorry

lemma connected_space_closedin_eq:
     "connected_space X \<longleftrightarrow>
       (\<nexists>E1 E2. closedin X E1 \<and> closedin X E2 \<and>
                E1 \<union> E2 = topspace X \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
sorry

lemma connected_space_clopen_in:
     "connected_space X \<longleftrightarrow>
        (\<forall>T. openin X T \<and> closedin X T \<longrightarrow> T = {} \<or> T = topspace X)"
sorry

lemma connectedin:
     "connectedin X S \<longleftrightarrow>
        S \<subseteq> topspace X \<and>
         (\<nexists>E1 E2.
             openin X E1 \<and> openin X E2 \<and>
             S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 \<inter> S = {} \<and> E1 \<inter> S \<noteq> {} \<and> E2 \<inter> S \<noteq> {})"  (is "?lhs = ?rhs")
sorry

lemma connectedinD:
     "\<lbrakk>connectedin X S; openin X E1; openin X E2; S \<subseteq> E1 \<union> E2; E1 \<inter> E2 \<inter> S = {}; E1 \<inter> S \<noteq> {}; E2 \<inter> S \<noteq> {}\<rbrakk> \<Longrightarrow> False"
sorry

lemma connectedin_iff_connected [simp]: "connectedin euclidean S \<longleftrightarrow> connected S"
sorry

lemma connectedin_closedin:
   "connectedin X S \<longleftrightarrow>
        S \<subseteq> topspace X \<and>
        \<not>(\<exists>E1 E2. closedin X E1 \<and> closedin X E2 \<and>
                  S \<subseteq> (E1 \<union> E2) \<and>
                  (E1 \<inter> E2 \<inter> S = {}) \<and>
                  \<not>(E1 \<inter> S = {}) \<and> \<not>(E2 \<inter> S = {}))"
sorry

lemma connectedin_empty [simp]: "connectedin X {}"
sorry

lemma connected_space_trivial_topology [simp]: "connected_space trivial_topology"
sorry

lemma connectedin_sing [simp]: "connectedin X {a} \<longleftrightarrow> a \<in> topspace X"
sorry

lemma connectedin_absolute [simp]:
  "connectedin (subtopology X S) S \<longleftrightarrow> connectedin X S"
sorry

lemma connectedin_Union:
  assumes \<U>: "\<And>S. S \<in> \<U> \<Longrightarrow> connectedin X S" and ne: "\<Inter>\<U> \<noteq> {}"
  shows "connectedin X (\<Union>\<U>)"
sorry

lemma connectedin_Un:
     "\<lbrakk>connectedin X S; connectedin X T; S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> connectedin X (S \<union> T)"
sorry

lemma connected_space_subconnected:
  "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. \<exists>S. connectedin X S \<and> x \<in> S \<and> y \<in> S)" (is "?lhs = ?rhs")
sorry

lemma connectedin_intermediate_closure_of:
  assumes "connectedin X S" "S \<subseteq> T" "T \<subseteq> X closure_of S"
  shows "connectedin X T"
sorry

lemma connectedin_closure_of:
     "connectedin X S \<Longrightarrow> connectedin X (X closure_of S)"
sorry

lemma connectedin_separation:
  "connectedin X S \<longleftrightarrow>
        S \<subseteq> topspace X \<and>
        (\<nexists>C1 C2. C1 \<union> C2 = S \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> C1 \<inter> X closure_of C2 = {} \<and> C2 \<inter> X closure_of C1 = {})"
sorry

lemma connectedin_eq_not_separated:
   "connectedin X S \<longleftrightarrow>
         S \<subseteq> topspace X \<and>
         (\<nexists>C1 C2. C1 \<union> C2 = S \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> separatedin X C1 C2)"
sorry

lemma connectedin_eq_not_separated_subset:
  "connectedin X S \<longleftrightarrow>
      S \<subseteq> topspace X \<and> (\<nexists>C1 C2. S \<subseteq> C1 \<union> C2 \<and> S \<inter> C1 \<noteq> {} \<and> S \<inter> C2 \<noteq> {} \<and> separatedin X C1 C2)"
sorry

lemma connected_space_eq_not_separated:
     "connected_space X \<longleftrightarrow>
      (\<nexists>C1 C2. C1 \<union> C2 = topspace X \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> separatedin X C1 C2)"
sorry

lemma connected_space_eq_not_separated_subset:
  "connected_space X \<longleftrightarrow>
    (\<nexists>C1 C2. topspace X \<subseteq> C1 \<union> C2 \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> separatedin X C1 C2)"
sorry

lemma connectedin_subset_separated_union:
     "\<lbrakk>connectedin X C; separatedin X S T; C \<subseteq> S \<union> T\<rbrakk> \<Longrightarrow> C \<subseteq> S \<or> C \<subseteq> T"
sorry

lemma connectedin_nonseparated_union:
  assumes "connectedin X S" "connectedin X T" "\<not>separatedin X S T"
  shows "connectedin X (S \<union> T)"
sorry

lemma connected_space_closures:
     "connected_space X \<longleftrightarrow>
        (\<nexists>e1 e2. e1 \<union> e2 = topspace X \<and> X closure_of e1 \<inter> X closure_of e2 = {} \<and> e1 \<noteq> {} \<and> e2 \<noteq> {})"
     (is "?lhs = ?rhs")
sorry

lemma connectedin_Int_frontier_of:
  assumes "connectedin X S" "S \<inter> T \<noteq> {}" "S - T \<noteq> {}"
  shows "S \<inter> X frontier_of T \<noteq> {}"
sorry

lemma connectedin_continuous_map_image:
  assumes f: "continuous_map X Y f" and "connectedin X S"
  shows "connectedin Y (f ` S)"
sorry

lemma connected_space_quotient_map_image:
   "\<lbrakk>quotient_map X X' q; connected_space X\<rbrakk> \<Longrightarrow> connected_space X'"
sorry

lemma homeomorphic_connected_space:
     "X homeomorphic_space Y \<Longrightarrow> connected_space X \<longleftrightarrow> connected_space Y"
sorry

lemma homeomorphic_map_connectedness:
  assumes f: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "connectedin Y (f ` U) \<longleftrightarrow> connectedin X U"
sorry

lemma homeomorphic_map_connectedness_eq:
   "homeomorphic_map X Y f
        \<Longrightarrow> connectedin X U \<longleftrightarrow>
             U \<subseteq> topspace X \<and> connectedin Y (f ` U)"
sorry

lemma connectedin_discrete_topology:
   "connectedin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U \<and> (\<exists>a. S \<subseteq> {a})"
sorry

lemma connected_space_discrete_topology:
     "connected_space (discrete_topology U) \<longleftrightarrow> (\<exists>a. U \<subseteq> {a})"
sorry

subsection\<open>Compact sets\<close>

definition compactin where
 "compactin X S \<longleftrightarrow>
     S \<subseteq> topspace X \<and>
     (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> S \<subseteq> \<Union>\<U>
          \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>))"

definition compact_space where
   "compact_space X \<equiv> compactin X (topspace X)"

lemma compact_space_alt:
   "compact_space X \<longleftrightarrow>
        (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> topspace X \<subseteq> \<Union>\<U>
            \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> topspace X \<subseteq> \<Union>\<F>))"
sorry

lemma compact_space:
   "compact_space X \<longleftrightarrow>
        (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> \<Union>\<U> = topspace X
            \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> \<Union>\<F> = topspace X))"
sorry

lemma compactinD:
  "\<lbrakk>compactin X S; \<And>U. U \<in> \<U> \<Longrightarrow> openin X U; S \<subseteq> \<Union>\<U>\<rbrakk> \<Longrightarrow> \<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>"
sorry

lemma compactin_euclidean_iff [simp]: "compactin euclidean S \<longleftrightarrow> compact S"
sorry

lemma compactin_absolute [simp]:
   "compactin (subtopology X S) S \<longleftrightarrow> compactin X S"
sorry

lemma compactin_subspace: "compactin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> compact_space (subtopology X S)"
sorry

lemma compact_space_subtopology: "compactin X S \<Longrightarrow> compact_space (subtopology X S)"
sorry

lemma compactin_subtopology: "compactin (subtopology X S) T \<longleftrightarrow> compactin X T \<and> T \<subseteq> S"
sorry

lemma compactin_subset_topspace: "compactin X S \<Longrightarrow> S \<subseteq> topspace X"
sorry

lemma compactin_contractive:
   "\<lbrakk>compactin X' S; topspace X' = topspace X;
     \<And>U. openin X U \<Longrightarrow> openin X' U\<rbrakk> \<Longrightarrow> compactin X S"
sorry

lemma finite_imp_compactin:
   "\<lbrakk>S \<subseteq> topspace X; finite S\<rbrakk> \<Longrightarrow> compactin X S"
sorry

lemma compactin_empty [iff]: "compactin X {}"
sorry

lemma compact_space_trivial_topology [simp]: "compact_space trivial_topology"
sorry

lemma finite_imp_compactin_eq:
   "finite S \<Longrightarrow> (compactin X S \<longleftrightarrow> S \<subseteq> topspace X)"
sorry

lemma compactin_sing [simp]: "compactin X {a} \<longleftrightarrow> a \<in> topspace X"
sorry

lemma closed_compactin:
  assumes XK: "compactin X K" and "C \<subseteq> K" and XC: "closedin X C"
  shows "compactin X C"
sorry

lemma closed_compactin_Inter:
  "\<lbrakk>compactin X K; K \<in> \<K>; \<And>K. K \<in> \<K> \<Longrightarrow> closedin X K\<rbrakk> \<Longrightarrow> compactin X (\<Inter>\<K>)"
sorry

lemma closedin_subtopology_Int_subset:
   "\<lbrakk>closedin (subtopology X U) (U \<inter> S); V \<subseteq> U\<rbrakk> \<Longrightarrow> closedin (subtopology X V) (V \<inter> S)"
sorry

lemma closedin_subtopology_Int_closedin:
   "\<lbrakk>closedin (subtopology X U) S; closedin X T\<rbrakk> \<Longrightarrow> closedin (subtopology X U) (S \<inter> T)"
sorry

lemma closedin_compact_space:
   "\<lbrakk>compact_space X; closedin X S\<rbrakk> \<Longrightarrow> compactin X S"
sorry

lemma compact_Int_closedin:
  assumes "compactin X S" "closedin X T" shows "compactin X (S \<inter> T)"
sorry

lemma closed_Int_compactin: "\<lbrakk>closedin X S; compactin X T\<rbrakk> \<Longrightarrow> compactin X (S \<inter> T)"
sorry

lemma compactin_Un:
  assumes S: "compactin X S" and T: "compactin X T" shows "compactin X (S \<union> T)"
sorry

lemma compactin_Union:
   "\<lbrakk>finite \<F>; \<And>S. S \<in> \<F> \<Longrightarrow> compactin X S\<rbrakk> \<Longrightarrow> compactin X (\<Union>\<F>)"
sorry

lemma compactin_subtopology_imp_compact:
  assumes "compactin (subtopology X S) K" shows "compactin X K"
sorry

lemma compact_imp_compactin_subtopology:
  assumes "compactin X K" "K \<subseteq> S" shows "compactin (subtopology X S) K"
sorry

proposition compact_space_fip:
   "compact_space X \<longleftrightarrow>
    (\<forall>\<U>. (\<forall>C\<in>\<U>. closedin X C) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> \<Inter>\<F> \<noteq> {}) \<longrightarrow> \<Inter>\<U> \<noteq> {})"
   (is "_ = ?rhs")
sorry

corollary compactin_fip:
  "compactin X S \<longleftrightarrow>
    S \<subseteq> topspace X \<and>
    (\<forall>\<U>. (\<forall>C\<in>\<U>. closedin X C) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> S \<inter> \<Inter>\<F> \<noteq> {}) \<longrightarrow> S \<inter> \<Inter>\<U> \<noteq> {})"
sorry

corollary compact_space_imp_nest:
  fixes C :: "nat \<Rightarrow> 'a set"
  assumes "compact_space X" and clo: "\<And>n. closedin X (C n)"
    and ne: "\<And>n. C n \<noteq> {}" and dec: "decseq C"
  shows "(\<Inter>n. C n) \<noteq> {}"
sorry

lemma compactin_discrete_topology:
   "compactin (discrete_topology X) S \<longleftrightarrow> S \<subseteq> X \<and> finite S" (is "?lhs = ?rhs")
sorry

lemma compact_space_discrete_topology: "compact_space(discrete_topology X) \<longleftrightarrow> finite X"
sorry

lemma compact_space_imp_Bolzano_Weierstrass:
  assumes "compact_space X" "infinite S" "S \<subseteq> topspace X"
  shows "X derived_set_of S \<noteq> {}"
sorry

lemma compactin_imp_Bolzano_Weierstrass:
   "\<lbrakk>compactin X S; infinite T \<and> T \<subseteq> S\<rbrakk> \<Longrightarrow> S \<inter> X derived_set_of T \<noteq> {}"
sorry

lemma compact_closure_of_imp_Bolzano_Weierstrass:
   "\<lbrakk>compactin X (X closure_of S); infinite T; T \<subseteq> S; T \<subseteq> topspace X\<rbrakk> \<Longrightarrow> X derived_set_of T \<noteq> {}"
sorry

lemma discrete_compactin_eq_finite:
   "S \<inter> X derived_set_of S = {} \<Longrightarrow> compactin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> finite S"
sorry

lemma discrete_compact_space_eq_finite:
   "X derived_set_of (topspace X) = {} \<Longrightarrow> (compact_space X \<longleftrightarrow> finite(topspace X))"
sorry

lemma image_compactin:
  assumes cpt: "compactin X S" and cont: "continuous_map X Y f"
  shows "compactin Y (f ` S)"
sorry

lemma homeomorphic_compact_space:
  assumes "X homeomorphic_space Y"
  shows "compact_space X \<longleftrightarrow> compact_space Y"
sorry

lemma homeomorphic_map_compactness:
  assumes hom: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "compactin Y (f ` U) \<longleftrightarrow> compactin X U"
sorry

lemma homeomorphic_map_compactness_eq:
   "homeomorphic_map X Y f
        \<Longrightarrow> compactin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> compactin Y (f ` U)"
sorry

subsection\<open>Embedding maps\<close>

definition embedding_map
  where "embedding_map X Y f \<equiv> homeomorphic_map X (subtopology Y (f ` (topspace X))) f"

lemma embedding_map_eq:
   "\<lbrakk>embedding_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> embedding_map X Y g"
sorry

lemma embedding_map_compose:
  assumes "embedding_map X X' f" "embedding_map X' X'' g"
  shows "embedding_map X X'' (g \<circ> f)"
sorry

lemma surjective_embedding_map:
   "embedding_map X Y f \<and> f ` (topspace X) = topspace Y \<longleftrightarrow> homeomorphic_map X Y f"
sorry

lemma embedding_map_in_subtopology:
   "embedding_map X (subtopology Y S) f \<longleftrightarrow> embedding_map X Y f \<and> f ` (topspace X) \<subseteq> S"  (is "?lhs = ?rhs")
sorry

lemma injective_open_imp_embedding_map:
   "\<lbrakk>continuous_map X Y f; open_map X Y f; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> embedding_map X Y f"
sorry

lemma injective_closed_imp_embedding_map:
  "\<lbrakk>continuous_map X Y f; closed_map X Y f; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> embedding_map X Y f"
sorry

lemma embedding_map_imp_homeomorphic_space:
   "embedding_map X Y f \<Longrightarrow> X homeomorphic_space (subtopology Y (f ` (topspace X)))"
sorry

lemma embedding_imp_closed_map:
   "\<lbrakk>embedding_map X Y f; closedin Y (f ` topspace X)\<rbrakk> \<Longrightarrow> closed_map X Y f"
sorry

lemma embedding_imp_closed_map_eq:
   "embedding_map X Y f \<Longrightarrow> (closed_map X Y f \<longleftrightarrow> closedin Y (f ` topspace X))"
sorry

subsection\<open>Retraction and section maps\<close>

definition retraction_maps :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "retraction_maps X Y f g \<equiv>
           continuous_map X Y f \<and> continuous_map Y X g \<and> (\<forall>x \<in> topspace Y. f(g x) = x)"

definition section_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "section_map X Y f \<equiv> \<exists>g. retraction_maps Y X g f"

definition retraction_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "retraction_map X Y f \<equiv> \<exists>g. retraction_maps X Y f g"

lemma retraction_maps_eq:
   "\<lbrakk>retraction_maps X Y f g; \<And>x. x \<in> topspace X \<Longrightarrow> f x = f' x; \<And>x. x \<in> topspace Y \<Longrightarrow> g x = g' x\<rbrakk>
        \<Longrightarrow> retraction_maps X Y f' g'"
sorry

lemma section_map_eq:
   "\<lbrakk>section_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> section_map X Y g"
sorry

lemma retraction_map_eq:
   "\<lbrakk>retraction_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> retraction_map X Y g"
sorry

lemma homeomorphic_imp_retraction_maps:
   "homeomorphic_maps X Y f g \<Longrightarrow> retraction_maps X Y f g"
sorry

lemma section_and_retraction_eq_homeomorphic_map:
   "section_map X Y f \<and> retraction_map X Y f \<longleftrightarrow> homeomorphic_map X Y f"  (is "?lhs = ?rhs")
sorry

lemma section_imp_embedding_map:
   "section_map X Y f \<Longrightarrow> embedding_map X Y f"
sorry

lemma retraction_imp_quotient_map:
  assumes "retraction_map X Y f"
  shows "quotient_map X Y f"
sorry

lemma retraction_maps_compose:
   "\<lbrakk>retraction_maps X Y f f'; retraction_maps Y Z g g'\<rbrakk> \<Longrightarrow> retraction_maps X Z (g \<circ> f) (f' \<circ> g')"
sorry

lemma retraction_map_compose:
   "\<lbrakk>retraction_map X Y f; retraction_map Y Z g\<rbrakk> \<Longrightarrow> retraction_map X Z (g \<circ> f)"
sorry

lemma section_map_compose:
   "\<lbrakk>section_map X Y f; section_map Y Z g\<rbrakk> \<Longrightarrow> section_map X Z (g \<circ> f)"
sorry

lemma surjective_section_eq_homeomorphic_map:
   "section_map X Y f \<and> f ` (topspace X) = topspace Y \<longleftrightarrow> homeomorphic_map X Y f"
sorry

lemma surjective_retraction_or_section_map:
   "f ` (topspace X) = topspace Y \<Longrightarrow> retraction_map X Y f \<or> section_map X Y f \<longleftrightarrow> retraction_map X Y f"
sorry

lemma retraction_imp_surjective_map:
   "retraction_map X Y f \<Longrightarrow> f ` (topspace X) = topspace Y"
sorry

lemma section_imp_injective_map:
   "\<lbrakk>section_map X Y f; x \<in> topspace X; y \<in> topspace X\<rbrakk> \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
sorry

lemma retraction_maps_to_retract_maps:
   "retraction_maps X Y r s
        \<Longrightarrow> retraction_maps X (subtopology X (s ` (topspace Y))) (s \<circ> r) id"
sorry

subsection \<open>Continuity\<close>

lemma continuous_on_open:
  "continuous_on S f \<longleftrightarrow>
    (\<forall>T. openin (top_of_set (f ` S)) T \<longrightarrow>
      openin (top_of_set S) (S \<inter> f -` T))"
sorry

lemma continuous_on_closed:
  "continuous_on S f \<longleftrightarrow>
    (\<forall>T. closedin (top_of_set (f ` S)) T \<longrightarrow>
      closedin (top_of_set S) (S \<inter> f -` T))"
sorry

lemma continuous_on_imp_closedin:
  assumes "continuous_on S f" "closedin (top_of_set (f ` S)) T"
  shows "closedin (top_of_set S) (S \<inter> f -` T)"
sorry

lemma continuous_map_subtopology_eu [simp]:
  "continuous_map (top_of_set S) (subtopology euclidean T) h \<longleftrightarrow> continuous_on S h \<and> h ` S \<subseteq> T"
sorry

lemma continuous_map_euclidean_top_of_set:
  assumes eq: "f -` S = UNIV" and cont: "continuous_on UNIV f"
  shows "continuous_map euclidean (top_of_set S) f"
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Half-global and completely global cases\<close>

lemma continuous_openin_preimage_gen:
  assumes "continuous_on S f"  "open T"
  shows "openin (top_of_set S) (S \<inter> f -` T)"
sorry

lemma continuous_closedin_preimage:
  assumes "continuous_on S f" and "closed T"
  shows "closedin (top_of_set S) (S \<inter> f -` T)"
sorry

lemma continuous_openin_preimage_eq:
   "continuous_on S f \<longleftrightarrow> (\<forall>T. open T \<longrightarrow> openin (top_of_set S) (S \<inter> f -` T))"
sorry

lemma continuous_closedin_preimage_eq:
   "continuous_on S f \<longleftrightarrow>
    (\<forall>T. closed T \<longrightarrow> closedin (top_of_set S) (S \<inter> f -` T))"
sorry

lemma continuous_open_preimage:
  assumes contf: "continuous_on S f" and "open S" "open T"
  shows "open (S \<inter> f -` T)"
sorry

lemma continuous_closed_preimage:
  assumes contf: "continuous_on S f" and "closed S" "closed T"
  shows "closed (S \<inter> f -` T)"
sorry

lemma continuous_open_vimage: "open S \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> open (f -` S)"
sorry

lemma continuous_closed_vimage: "closed S \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> closed (f -` S)"
sorry

lemma Times_in_interior_subtopology:
  assumes "(x, y) \<in> U" "openin (top_of_set (S \<times> T)) U"
  obtains V W where "openin (top_of_set S) V" "x \<in> V"
                    "openin (top_of_set T) W" "y \<in> W" "(V \<times> W) \<subseteq> U"
sorry

lemma closedin_Times:
  "closedin (top_of_set S) S' \<Longrightarrow> closedin (top_of_set T) T' \<Longrightarrow>
    closedin (top_of_set (S \<times> T)) (S' \<times> T')"
sorry

lemma openin_Times:
  "openin (top_of_set S) S' \<Longrightarrow> openin (top_of_set T) T' \<Longrightarrow>
    openin (top_of_set (S \<times> T)) (S' \<times> T')"
sorry

lemma openin_Times_eq:
  fixes S :: "'a::topological_space set" and T :: "'b::topological_space set"
  shows
    "openin (top_of_set (S \<times> T)) (S' \<times> T') \<longleftrightarrow>
      S' = {} \<or> T' = {} \<or> openin (top_of_set S) S' \<and> openin (top_of_set T) T'"
    (is "?lhs = ?rhs")
sorry

lemma Lim_transform_within_openin:
  assumes f: "(f \<longlongrightarrow> l) (at a within T)"
    and "openin (top_of_set T) S" "a \<in> S"
    and eq: "\<And>x. \<lbrakk>x \<in> S; x \<noteq> a\<rbrakk> \<Longrightarrow> f x = g x"
  shows "(g \<longlongrightarrow> l) (at a within T)"
sorry

lemma continuous_on_open_gen:
  assumes "f \<in> S \<rightarrow> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. openin (top_of_set T) U
                  \<longrightarrow> openin (top_of_set S) (S \<inter> f -` U))"
     (is "?lhs = ?rhs")
sorry

lemma continuous_openin_preimage:
  "\<lbrakk>continuous_on S f; f \<in> S \<rightarrow> T; openin (top_of_set T) U\<rbrakk>
        \<Longrightarrow> openin (top_of_set S) (S \<inter> f -` U)"
sorry

lemma continuous_on_closed_gen:
  assumes "f \<in> S \<rightarrow> T"
  shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. closedin (top_of_set T) U
                  \<longrightarrow> closedin (top_of_set S) (S \<inter> f -` U))"
sorry

lemma continuous_closedin_preimage_gen:
  assumes "continuous_on S f" "f \<in> S \<rightarrow> T" "closedin (top_of_set T) U"
    shows "closedin (top_of_set S) (S \<inter> f -` U)"
sorry

lemma continuous_transform_within_openin:
  assumes "continuous (at a within T) f"
    and "openin (top_of_set T) S" "a \<in> S"
    and eq: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "continuous (at a within T) g"
sorry

subsection\<^marker>\<open>tag important\<close> \<open>The topology generated by some (open) subsets\<close>

text \<open>In the definition below of a generated topology, the \<open>Empty\<close> case is not necessary,
as it follows from \<open>UN\<close> taking for \<open>K\<close> the empty set. However, it is convenient to have,
and is never a problem in proofs, so I prefer to write it down explicitly.

We do not require \<open>UNIV\<close> to be an open set, as this will not be the case in applications. (We are
thinking of a topology on a subset of \<open>UNIV\<close>, the remaining part of \<open>UNIV\<close> being irrelevant.)\<close>

inductive generate_topology_on for S where
  Empty: "generate_topology_on S {}"
| Int: "generate_topology_on S a \<Longrightarrow> generate_topology_on S b \<Longrightarrow> generate_topology_on S (a \<inter> b)"
| UN: "(\<And>k. k \<in> K \<Longrightarrow> generate_topology_on S k) \<Longrightarrow> generate_topology_on S (\<Union>K)"
| Basis: "s \<in> S \<Longrightarrow> generate_topology_on S s"

lemma istopology_generate_topology_on:
  "istopology (generate_topology_on S)"
sorry

text \<open>The basic property of the topology generated by a set \<open>S\<close> is that it is the
smallest topology containing all the elements of \<open>S\<close>:\<close>

lemma generate_topology_on_coarsest:
  assumes T: "istopology T" "\<And>s. s \<in> S \<Longrightarrow> T s"
          and gen: "generate_topology_on S s0"
  shows "T s0"
sorry

abbreviation\<^marker>\<open>tag unimportant\<close> topology_generated_by::"('a set set) \<Rightarrow> ('a topology)"
  where "topology_generated_by S \<equiv> topology (generate_topology_on S)"

lemma openin_topology_generated_by_iff:
  "openin (topology_generated_by S) s \<longleftrightarrow> generate_topology_on S s"
sorry

lemma openin_topology_generated_by:
  "openin (topology_generated_by S) s \<Longrightarrow> generate_topology_on S s"
sorry

lemma topology_generated_by_topspace [simp]:
  "topspace (topology_generated_by S) = (\<Union>S)"
sorry

lemma topology_generated_by_Basis:
  "s \<in> S \<Longrightarrow> openin (topology_generated_by S) s"
sorry

lemma generate_topology_on_Inter:
  "\<lbrakk>finite \<F>; \<And>K. K \<in> \<F> \<Longrightarrow> generate_topology_on \<S> K; \<F> \<noteq> {}\<rbrakk> \<Longrightarrow> generate_topology_on \<S> (\<Inter>\<F>)"
sorry

subsection\<open>Topology bases and sub-bases\<close>

lemma istopology_base_alt:
   "istopology (arbitrary union_of P) \<longleftrightarrow>
    (\<forall>S T. (arbitrary union_of P) S \<and> (arbitrary union_of P) T
           \<longrightarrow> (arbitrary union_of P) (S \<inter> T))"
sorry

lemma istopology_base_eq:
   "istopology (arbitrary union_of P) \<longleftrightarrow>
    (\<forall>S T. P S \<and> P T \<longrightarrow> (arbitrary union_of P) (S \<inter> T))"
sorry

lemma istopology_base:
   "(\<And>S T. \<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<inter> T)) \<Longrightarrow> istopology (arbitrary union_of P)"
sorry

lemma openin_topology_base_unique:
   "openin X = arbitrary union_of P \<longleftrightarrow>
        (\<forall>V. P V \<longrightarrow> openin X V) \<and> (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V. P V \<and> x \<in> V \<and> V \<subseteq> U))"
   (is "?lhs = ?rhs")
sorry

lemma topology_base_unique:
  assumes "\<And>S. P S \<Longrightarrow> openin X S"
          "\<And>U x. \<lbrakk>openin X U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>B. P B \<and> x \<in> B \<and> B \<subseteq> U"
  shows   "topology (arbitrary union_of P) = X"
sorry

lemma topology_bases_eq_aux:
   "\<lbrakk>(arbitrary union_of P) S;
     \<And>U x. \<lbrakk>P U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>V. Q V \<and> x \<in> V \<and> V \<subseteq> U\<rbrakk>
        \<Longrightarrow> (arbitrary union_of Q) S"
sorry

lemma topology_bases_eq:
   "\<lbrakk>\<And>U x. \<lbrakk>P U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>V. Q V \<and> x \<in> V \<and> V \<subseteq> U;
    \<And>V x. \<lbrakk>Q V; x \<in> V\<rbrakk> \<Longrightarrow> \<exists>U. P U \<and> x \<in> U \<and> U \<subseteq> V\<rbrakk>
        \<Longrightarrow> topology (arbitrary union_of P) =
            topology (arbitrary union_of Q)"
sorry

lemma istopology_subbase:
   "istopology (arbitrary union_of (finite intersection_of P relative_to S))"
sorry

lemma openin_subbase:
  "openin (topology (arbitrary union_of (finite intersection_of B relative_to U))) S
   \<longleftrightarrow> (arbitrary union_of (finite intersection_of B relative_to U)) S"
sorry

lemma topspace_subbase [simp]:
   "topspace(topology (arbitrary union_of (finite intersection_of B relative_to U))) = U" (is "?lhs = _")
sorry

lemma minimal_topology_subbase:
  assumes X: "\<And>S. P S \<Longrightarrow> openin X S" and "openin X U"
  and S: "openin(topology(arbitrary union_of (finite intersection_of P relative_to U))) S"
shows "openin X S"
sorry

lemma istopology_subbase_UNIV:
   "istopology (arbitrary union_of (finite intersection_of P))"
sorry

lemma generate_topology_on_eq:
  "generate_topology_on S = arbitrary union_of finite' intersection_of (\<lambda>x. x \<in> S)" (is "?lhs = ?rhs")
sorry

lemma continuous_on_generated_topo_iff:
  "continuous_map T1 (topology_generated_by S) f \<longleftrightarrow>
      ((\<forall>U. U \<in> S \<longrightarrow> openin T1 (f-`U \<inter> topspace(T1))) \<and> (f`(topspace T1) \<subseteq> (\<Union> S)))"
sorry

lemma continuous_on_generated_topo:
  assumes "\<And>U. U \<in>S \<Longrightarrow> openin T1 (f-`U \<inter> topspace(T1))"
          "f`(topspace T1) \<subseteq> (\<Union> S)"
  shows "continuous_map T1 (topology_generated_by S) f"
sorry

subsection\<open>Continuity via bases/subbases, hence upper and lower semicontinuity\<close>

lemma continuous_map_into_topology_base:
  assumes P: "openin Y = arbitrary union_of P"
    and f: "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y"
    and ope: "\<And>U. P U \<Longrightarrow> openin X {x \<in> topspace X. f x \<in> U}"
  shows "continuous_map X Y f"
sorry

lemma continuous_map_into_topology_base_eq:
  assumes P: "openin Y = arbitrary union_of P"
  shows
   "continuous_map X Y f \<longleftrightarrow>
    f \<in> topspace X \<rightarrow> topspace Y \<and> (\<forall>U. P U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U})"
 (is "?lhs=?rhs")
sorry

lemma continuous_map_into_topology_subbase:
  fixes U P
  defines "Y \<equiv> topology(arbitrary union_of (finite intersection_of P relative_to U))"
  assumes f: "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y"
    and ope: "\<And>U. P U \<Longrightarrow> openin X {x \<in> topspace X. f x \<in> U}"
  shows "continuous_map X Y f"
sorry

lemma continuous_map_into_topology_subbase_eq:
  assumes "Y = topology(arbitrary union_of (finite intersection_of P relative_to U))"
  shows
   "continuous_map X Y f \<longleftrightarrow>
    f \<in> topspace X \<rightarrow> topspace Y \<and> (\<forall>U. P U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U})"
   (is "?lhs=?rhs")
sorry

lemma subbase_subtopology_euclidean:
  fixes U :: "'a::order_topology set"
  shows
  "topology
    (arbitrary union_of
      (finite intersection_of (\<lambda>x. x \<in> range greaterThan \<union> range lessThan) relative_to U))
 = subtopology euclidean U"
sorry

lemma continuous_map_upper_lower_semicontinuous_lt_gen:
  fixes U :: "'a::order_topology set"
  shows "continuous_map X (subtopology euclidean U) f \<longleftrightarrow>
         (\<forall>x \<in> topspace X. f x \<in> U) \<and>
         (\<forall>a. openin X {x \<in> topspace X. f x > a}) \<and>
         (\<forall>a. openin X {x \<in> topspace X. f x < a})"
sorry

lemma continuous_map_upper_lower_semicontinuous_lt:
  fixes f :: "'a \<Rightarrow> 'b::order_topology"
  shows "continuous_map X euclidean f \<longleftrightarrow>
         (\<forall>a. openin X {x \<in> topspace X. f x > a}) \<and>
         (\<forall>a. openin X {x \<in> topspace X. f x < a})"
sorry

lemma Int_Collect_imp_eq: "A \<inter> {x. x\<in>A \<longrightarrow> P x} = {x\<in>A. P x}"
sorry

lemma continuous_map_upper_lower_semicontinuous_le_gen:
  shows
    "continuous_map X (subtopology euclideanreal U) f \<longleftrightarrow>
         (\<forall>x \<in> topspace X. f x \<in> U) \<and>
         (\<forall>a. closedin X {x \<in> topspace X. f x \<ge> a}) \<and>
         (\<forall>a. closedin X {x \<in> topspace X. f x \<le> a})"
sorry

lemma continuous_map_upper_lower_semicontinuous_le:
   "continuous_map X euclideanreal f \<longleftrightarrow>
         (\<forall>a. closedin X {x \<in> topspace X. f x \<ge> a}) \<and>
         (\<forall>a. closedin X {x \<in> topspace X. f x \<le> a})"
sorry

lemma continuous_map_upper_lower_semicontinuous_lte_gen:
   "continuous_map X (subtopology euclideanreal U) f \<longleftrightarrow>
         (\<forall>x \<in> topspace X. f x \<in> U) \<and>
         (\<forall>a. openin X {x \<in> topspace X. f x < a}) \<and>
         (\<forall>a. closedin X {x \<in> topspace X. f x \<le> a})"
sorry

lemma continuous_map_upper_lower_semicontinuous_lte:
   "continuous_map X euclideanreal f \<longleftrightarrow>
         (\<forall>a. openin X {x \<in> topspace X. f x < a}) \<and>
         (\<forall>a. closedin X {x \<in> topspace X. f x \<le> a})"
sorry

subsection\<^marker>\<open>tag important\<close> \<open>Pullback topology\<close>

text \<open>Pulling back a topology by map gives again a topology. \<open>subtopology\<close> is
a special case of this notion, pulling back by the identity. We introduce the general notion as
we will need it to define the strong operator topology on the space of continuous linear operators,
by pulling back the product topology on the space of all functions.\<close>

text \<open>\<open>pullback_topology A f T\<close> is the pullback of the topology \<open>T\<close> by the map \<open>f\<close> on
the set \<open>A\<close>.\<close>

definition\<^marker>\<open>tag important\<close> pullback_topology::"('a set) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b topology) \<Rightarrow> ('a topology)"
  where "pullback_topology A f T = topology (\<lambda>S. \<exists>U. openin T U \<and> S = f-`U \<inter> A)"

lemma istopology_pullback_topology:
  "istopology (\<lambda>S. \<exists>U. openin T U \<and> S = f-`U \<inter> A)"
sorry

lemma openin_pullback_topology:
  "openin (pullback_topology A f T) S \<longleftrightarrow> (\<exists>U. openin T U \<and> S = f-`U \<inter> A)"
sorry

lemma topspace_pullback_topology:
  "topspace (pullback_topology A f T) = f-`(topspace T) \<inter> A"
sorry

proposition continuous_map_pullback [intro]:
  assumes "continuous_map T1 T2 g"
  shows "continuous_map (pullback_topology A f T1) T2 (g o f)"
sorry

proposition continuous_map_pullback' [intro]:
  assumes "continuous_map T1 T2 (f o g)" "topspace T1 \<subseteq> g-`A"
  shows "continuous_map T1 (pullback_topology A f T2) g"
sorry

subsection\<open>Proper maps (not a priori assumed continuous) \<close>

definition proper_map
  where
 "proper_map X Y f \<equiv>
        closed_map X Y f \<and> (\<forall>y \<in> topspace Y. compactin X {x \<in> topspace X. f x = y})"

lemma proper_imp_closed_map:
   "proper_map X Y f \<Longrightarrow> closed_map X Y f"
sorry

lemma proper_map_imp_subset_topspace:
   "proper_map X Y f \<Longrightarrow> f \<in> (topspace X) \<rightarrow> topspace Y"
sorry

lemma proper_map_restriction:
  assumes "proper_map X Y f" "{x \<in> topspace X. f x \<in> V} = U"
  shows "proper_map (subtopology X U) (subtopology Y V) f"
sorry

lemma closed_injective_imp_proper_map:
  assumes f: "closed_map X Y f" and inj: "inj_on f (topspace X)"
  shows "proper_map X Y f"
sorry

lemma injective_imp_proper_eq_closed_map:
   "inj_on f (topspace X) \<Longrightarrow> (proper_map X Y f \<longleftrightarrow> closed_map X Y f)"
sorry

lemma homeomorphic_imp_proper_map:
   "homeomorphic_map X Y f \<Longrightarrow> proper_map X Y f"
sorry

lemma compactin_proper_map_preimage:
  assumes f: "proper_map X Y f" and "compactin Y K"
  shows "compactin X {x. x \<in> topspace X \<and> f x \<in> K}"
sorry

lemma compact_space_proper_map_preimage:
  assumes f: "proper_map X Y f" and fim: "f ` (topspace X) = topspace Y" and "compact_space Y"
  shows "compact_space X"
sorry

lemma proper_map_alt:
   "proper_map X Y f \<longleftrightarrow>
    closed_map X Y f \<and> (\<forall>K. compactin Y K \<longrightarrow> compactin X {x. x \<in> topspace X \<and> f x \<in> K})"
sorry

lemma proper_map_on_empty [simp]: "proper_map trivial_topology Y f"
sorry

lemma proper_map_id [simp]:
   "proper_map X X id"
sorry

lemma proper_map_compose:
  assumes "proper_map X Y f" "proper_map Y Z g"
  shows "proper_map X Z (g \<circ> f)"
sorry

lemma proper_map_const:
   "proper_map X Y (\<lambda>x. c) \<longleftrightarrow> compact_space X \<and> (X = trivial_topology \<or> closedin Y {c})"
sorry

lemma proper_map_inclusion:
   "S \<subseteq> topspace X \<Longrightarrow> proper_map (subtopology X S) X id \<longleftrightarrow> closedin X S \<and> (\<forall>k. compactin X k \<longrightarrow> compactin X (S \<inter> k))"
sorry

lemma proper_map_into_subtopology:
   "\<lbrakk>proper_map X Y f; f \<in> topspace X \<rightarrow> C\<rbrakk> \<Longrightarrow> proper_map X (subtopology Y C) f"
sorry

lemma proper_map_from_composition_left:
  assumes gf: "proper_map X Z (g \<circ> f)" and contf: "continuous_map X Y f" and fim: "f ` topspace X = topspace Y"
  shows "proper_map Y Z g"
sorry

lemma proper_map_from_composition_right_inj:
  assumes gf: "proper_map X Z (g \<circ> f)" and fim: "f \<in> topspace X \<rightarrow> topspace Y" 
    and contf: "continuous_map Y Z g" and inj: "inj_on g (topspace Y)"
  shows "proper_map X Y f"
sorry

subsection\<open>Perfect maps (proper, continuous and surjective)\<close>

definition perfect_map 
  where "perfect_map X Y f \<equiv> continuous_map X Y f \<and> proper_map X Y f \<and> f ` (topspace X) = topspace Y"

lemma homeomorphic_imp_perfect_map:
   "homeomorphic_map X Y f \<Longrightarrow> perfect_map X Y f"
sorry

lemma perfect_imp_quotient_map:
   "perfect_map X Y f \<Longrightarrow> quotient_map X Y f"
sorry

lemma homeomorphic_eq_injective_perfect_map:
   "homeomorphic_map X Y f \<longleftrightarrow> perfect_map X Y f \<and> inj_on f (topspace X)"
sorry

lemma perfect_injective_eq_homeomorphic_map:
   "perfect_map X Y f \<and> inj_on f (topspace X) \<longleftrightarrow> homeomorphic_map X Y f"
sorry

lemma perfect_map_id [simp]: "perfect_map X X id"
sorry

lemma perfect_map_compose:
   "\<lbrakk>perfect_map X Y f; perfect_map Y Z g\<rbrakk> \<Longrightarrow> perfect_map X Z (g \<circ> f)"
sorry

lemma perfect_imp_continuous_map:
   "perfect_map X Y f \<Longrightarrow> continuous_map X Y f"
sorry

lemma perfect_imp_closed_map:
   "perfect_map X Y f \<Longrightarrow> closed_map X Y f"
sorry

lemma perfect_imp_proper_map:
   "perfect_map X Y f \<Longrightarrow> proper_map X Y f"
sorry

lemma perfect_imp_surjective_map:
   "perfect_map X Y f \<Longrightarrow> f ` (topspace X) = topspace Y"
sorry

lemma perfect_map_from_composition_left:
  assumes "perfect_map X Z (g \<circ> f)" and "continuous_map X Y f"
    and "continuous_map Y Z g" and "f ` topspace X = topspace Y"
  shows "perfect_map Y Z g"
sorry

end
