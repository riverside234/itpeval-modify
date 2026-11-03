section \<open>Abstract Metric Spaces\<close>

theory Abstract_Metric_Spaces
  imports Elementary_Metric_Spaces Abstract_Limits Abstract_Topological_Spaces
begin

(*Avoid a clash with the existing metric_space locale (from the type class)*)
locale Metric_space =
  fixes M :: "'a set" and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes nonneg [simp]: "\<And>x y. 0 \<le> d x y"
  assumes commute: "\<And>x y. d x y = d y x"
  assumes zero [simp]: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> d x y = 0 \<longleftrightarrow> x=y"
  assumes triangle: "\<And>x y z. \<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d x y + d y z"

text \<open>Link with the type class version\<close>
interpretation Met_TC: Metric_space UNIV dist
  by (simp add: dist_commute dist_triangle Metric_space.intro)

context Metric_space
begin

lemma subspace: "M' \<subseteq> M \<Longrightarrow> Metric_space M' d"
sorry

lemma abs_mdist [simp] : "\<bar>d x y\<bar> = d x y"
sorry

lemma mdist_pos_less: "\<lbrakk>x \<noteq> y; x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> 0 < d x y"
sorry

lemma mdist_zero [simp]: "x \<in> M \<Longrightarrow> d x x = 0"
sorry

lemma mdist_pos_eq [simp]: "\<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> 0 < d x y \<longleftrightarrow> x \<noteq> y"
sorry

lemma triangle': "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d x y + d z y"
sorry

lemma triangle'': "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d y x + d y z"
sorry

lemma mdist_reverse_triangle: "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> \<bar>d x y - d y z\<bar> \<le> d x z"
sorry

text\<open> Open and closed balls                                                                \<close>

definition mball where "mball x r \<equiv> {y. x \<in> M \<and> y \<in> M \<and> d x y < r}"
definition mcball where "mcball x r \<equiv> {y. x \<in> M \<and> y \<in> M \<and> d x y \<le> r}"

lemma in_mball [simp]: "y \<in> mball x r \<longleftrightarrow> x \<in> M \<and> y \<in> M \<and> d x y < r"
sorry

lemma centre_in_mball_iff [iff]: "x \<in> mball x r \<longleftrightarrow> x \<in> M \<and> 0 < r"
sorry

lemma mball_subset_mspace: "mball x r \<subseteq> M"
sorry

lemma mball_eq_empty: "mball x r = {} \<longleftrightarrow> (x \<notin> M) \<or> r \<le> 0"
sorry

lemma mball_subset: "\<lbrakk>d x y + a \<le> b; y \<in> M\<rbrakk> \<Longrightarrow> mball x a \<subseteq> mball y b"
sorry

lemma disjoint_mball: "r + r' \<le> d x x' \<Longrightarrow> disjnt (mball x r) (mball x' r')"
sorry

lemma mball_subset_concentric: "r \<le> s \<Longrightarrow> mball x r \<subseteq> mball x s"
sorry

lemma in_mcball [simp]: "y \<in> mcball x r \<longleftrightarrow> x \<in> M \<and> y \<in> M \<and> d x y \<le> r"
sorry

lemma centre_in_mcball_iff [iff]: "x \<in> mcball x r \<longleftrightarrow> x \<in> M \<and> 0 \<le> r"
sorry

lemma mcball_eq_empty: "mcball x r = {} \<longleftrightarrow> (x \<notin> M) \<or> r < 0"
sorry

lemma mcball_subset_mspace: "mcball x r \<subseteq> M"
sorry

lemma mball_subset_mcball: "mball x r \<subseteq> mcball x r"
sorry

lemma mcball_subset: "\<lbrakk>d x y + a \<le> b; y \<in> M\<rbrakk> \<Longrightarrow> mcball x a \<subseteq> mcball y b"
sorry

lemma mcball_subset_concentric: "r \<le> s \<Longrightarrow> mcball x r \<subseteq> mcball x s"
sorry

lemma mcball_subset_mball: "\<lbrakk>d x y + a < b; y \<in> M\<rbrakk> \<Longrightarrow> mcball x a \<subseteq> mball y b"
sorry

lemma mcball_subset_mball_concentric: "a < b \<Longrightarrow> mcball x a \<subseteq> mball x b"
sorry

end



subsection \<open>Metric topology                                                           \<close>

context Metric_space
begin

definition mopen where 
  "mopen U \<equiv> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r>0. mball x r \<subseteq> U))"

definition mtopology :: "'a topology" where 
  "mtopology \<equiv> topology mopen"

lemma is_topology_metric_topology [iff]: "istopology mopen"
sorry

lemma openin_mtopology: "openin mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r>0. mball x r \<subseteq> U))"
sorry

lemma topspace_mtopology [simp]: "topspace mtopology = M"
sorry

lemma subtopology_mspace [simp]: "subtopology mtopology M = mtopology"
sorry

lemma open_in_mspace [iff]: "openin mtopology M"
sorry

lemma closedin_mspace [iff]: "closedin mtopology M"
sorry

lemma openin_mball [iff]: "openin mtopology (mball x r)"
sorry

lemma mtopology_base:
   "mtopology = topology(arbitrary union_of (\<lambda>U. \<exists>x \<in> M. \<exists>r>0. U = mball x r))"
sorry

lemma closedin_metric:
   "closedin mtopology C \<longleftrightarrow> C \<subseteq> M \<and> (\<forall>x. x \<in> M - C \<longrightarrow> (\<exists>r>0. disjnt C (mball x r)))"  (is "?lhs = ?rhs")
sorry

lemma closedin_mcball [iff]: "closedin mtopology (mcball x r)"
sorry

lemma mball_iff_mcball: "(\<exists>r>0. mball x r \<subseteq> U) = (\<exists>r>0. mcball x r \<subseteq> U)"
sorry

lemma openin_mtopology_mcball:
  "openin mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r. 0 < r \<and> mcball x r \<subseteq> U))"
sorry

lemma metric_derived_set_of:
  "mtopology derived_set_of S = {x \<in> M. \<forall>r>0. \<exists>y\<in>S. y\<noteq>x \<and> y \<in> mball x r}" (is "?lhs=?rhs")
sorry

lemma metric_closure_of:
   "mtopology closure_of S = {x \<in> M. \<forall>r>0. \<exists>y \<in> S. y \<in> mball x r}"
sorry

lemma metric_closure_of_alt:
  "mtopology closure_of S = {x \<in> M. \<forall>r>0. \<exists>y \<in> S. y \<in> mcball x r}"
sorry

lemma metric_interior_of:
   "mtopology interior_of S = {x \<in> M. \<exists>\<epsilon>>0. mball x \<epsilon> \<subseteq> S}" (is "?lhs=?rhs")
sorry

lemma metric_interior_of_alt:
   "mtopology interior_of S = {x \<in> M. \<exists>\<epsilon>>0. mcball x \<epsilon> \<subseteq> S}"
sorry

lemma in_interior_of_mball:
   "x \<in> mtopology interior_of S \<longleftrightarrow> x \<in> M \<and> (\<exists>\<epsilon>>0. mball x \<epsilon> \<subseteq> S)"
sorry

lemma in_interior_of_mcball:
   "x \<in> mtopology interior_of S \<longleftrightarrow> x \<in> M \<and> (\<exists>\<epsilon>>0. mcball x \<epsilon> \<subseteq> S)"
sorry

lemma Hausdorff_space_mtopology: "Hausdorff_space mtopology"
sorry

subsection\<open>Bounded sets\<close>

definition mbounded where "mbounded S \<longleftrightarrow> (\<exists>x B. S \<subseteq> mcball x B)"

lemma mbounded_pos: "mbounded S \<longleftrightarrow> (\<exists>x B. 0 < B \<and> S \<subseteq> mcball x B)"
sorry

lemma mbounded_alt:
  "mbounded S \<longleftrightarrow> S \<subseteq> M \<and> (\<exists>B. \<forall>x \<in> S. \<forall>y \<in> S. d x y \<le> B)"
sorry

lemma mbounded_alt_pos:
  "mbounded S \<longleftrightarrow> S \<subseteq> M \<and> (\<exists>B>0. \<forall>x \<in> S. \<forall>y \<in> S. d x y \<le> B)"
sorry

lemma mbounded_subset: "\<lbrakk>mbounded T; S \<subseteq> T\<rbrakk> \<Longrightarrow> mbounded S"
sorry

lemma mbounded_subset_mspace: "mbounded S \<Longrightarrow> S \<subseteq> M"
sorry

lemma mbounded:
   "mbounded S \<longleftrightarrow> S = {} \<or> (\<forall>x \<in> S. x \<in> M) \<and> (\<exists>y B. y \<in> M \<and> (\<forall>x \<in> S. d y x \<le> B))"
sorry

lemma mbounded_empty [iff]: "mbounded {}"
sorry

lemma mbounded_mcball: "mbounded (mcball x r)"
sorry

lemma mbounded_mball [iff]: "mbounded (mball x r)"
sorry

lemma mbounded_insert: "mbounded (insert a S) \<longleftrightarrow> a \<in> M \<and> mbounded S"
sorry

lemma mbounded_Int: "mbounded S \<Longrightarrow> mbounded (S \<inter> T)"
sorry

lemma mbounded_Un: "mbounded (S \<union> T) \<longleftrightarrow> mbounded S \<and> mbounded T" (is "?lhs=?rhs")
sorry

lemma mbounded_Union:
  "\<lbrakk>finite \<F>; \<And>X. X \<in> \<F> \<Longrightarrow> mbounded X\<rbrakk> \<Longrightarrow> mbounded (\<Union>\<F>)"
sorry

lemma mbounded_closure_of:
   "mbounded S \<Longrightarrow> mbounded (mtopology closure_of S)"
sorry

lemma mbounded_closure_of_eq:
   "S \<subseteq> M \<Longrightarrow> (mbounded (mtopology closure_of S) \<longleftrightarrow> mbounded S)"
sorry

lemma maxdist_thm:
  assumes "mbounded S"
      and "x \<in> S"
      and "y \<in> S"
    shows  "d x y = (SUP z\<in>S. \<bar>d x z - d z y\<bar>)"
sorry

lemma metric_eq_thm: "\<lbrakk>S \<subseteq> M; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> (x = y) = (\<forall>z\<in>S. d x z = d y z)"
sorry

lemma compactin_imp_mbounded:
  assumes "compactin mtopology S"
  shows "mbounded S"
sorry



end (*Metric_space*)

lemma mcball_eq_cball [simp]: "Met_TC.mcball = cball"
sorry

lemma mball_eq_ball [simp]: "Met_TC.mball = ball"
sorry

lemma mopen_eq_open [simp]: "Met_TC.mopen = open"
sorry

lemma limitin_iff_tendsto [iff]: "limitin Met_TC.mtopology \<sigma> x F = tendsto \<sigma> x F"
sorry

lemma mtopology_is_euclidean [simp]: "Met_TC.mtopology = euclidean"
sorry

lemma mbounded_iff_bounded [iff]: "Met_TC.mbounded A \<longleftrightarrow> bounded A"
sorry

subsection\<open>Subspace of a metric space\<close>

locale Submetric = Metric_space + 
  fixes A
  assumes subset: "A \<subseteq> M"

sublocale Submetric \<subseteq> sub: Metric_space A d
  by (simp add: subset subspace)

context Submetric
begin 

lemma mball_submetric_eq: "sub.mball a r = (if a \<in> A then A \<inter> mball a r else {})"
and mcball_submetric_eq: "sub.mcball a r = (if a \<in> A then A \<inter> mcball a r else {})"
sorry

lemma mtopology_submetric: "sub.mtopology = subtopology mtopology A"
sorry

lemma mbounded_submetric: "sub.mbounded T \<longleftrightarrow> mbounded T \<and> T \<subseteq> A"
sorry

end

lemma (in Metric_space) submetric_empty [iff]: "Submetric M d {}"
sorry


subsection \<open>Abstract type of metric spaces\<close>

typedef 'a metric = "{(M::'a set,d). Metric_space M d}"
  morphisms "dest_metric" "metric"
proof -
  have "Metric_space {} (\<lambda>x y. 0)"
    by (auto simp: Metric_space_def)
  then show ?thesis
    by blast
qed

definition mspace where "mspace m \<equiv> fst (dest_metric m)"

definition mdist where "mdist m \<equiv> snd (dest_metric m)"

lemma Metric_space_mspace_mdist [iff]: "Metric_space (mspace m) (mdist m)"
sorry

lemma mdist_nonneg [simp]: "\<And>x y. 0 \<le> mdist m x y"
sorry

lemma mdist_commute: "\<And>x y. mdist m x y = mdist m y x"
sorry

lemma mdist_zero [simp]: "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m\<rbrakk> \<Longrightarrow> mdist m x y = 0 \<longleftrightarrow> x=y"
sorry

lemma mdist_triangle: "\<And>x y z. \<lbrakk>x \<in> mspace m; y \<in> mspace m; z \<in> mspace m\<rbrakk> \<Longrightarrow> mdist m x z \<le> mdist m x y + mdist m y z"
sorry

lemma (in Metric_space) mspace_metric[simp]: 
  "mspace (metric (M,d)) = M"
sorry

lemma (in Metric_space) mdist_metric[simp]: 
  "mdist (metric (M,d)) = d"
sorry

lemma metric_collapse [simp]: "metric (mspace m, mdist m) = m"
sorry

definition mtopology_of :: "'a metric \<Rightarrow> 'a topology"
  where "mtopology_of \<equiv> \<lambda>m. Metric_space.mtopology (mspace m) (mdist m)"

lemma topspace_mtopology_of [simp]: "topspace (mtopology_of m) = mspace m"
sorry

lemma (in Metric_space) mtopology_of [simp]:
  "mtopology_of (metric (M,d)) = mtopology"
sorry

definition "mball_of \<equiv> \<lambda>m. Metric_space.mball (mspace m) (mdist m)"

lemma in_mball_of [simp]: "y \<in> mball_of m x r \<longleftrightarrow> x \<in> mspace m \<and> y \<in> mspace m \<and> mdist m x y < r"
sorry

lemma (in Metric_space) mball_of [simp]:
  "mball_of (metric (M,d)) = mball"
sorry
definition "mcball_of \<equiv> \<lambda>m. Metric_space.mcball (mspace m) (mdist m)"

lemma in_mcball_of [simp]: "y \<in> mcball_of m x r \<longleftrightarrow> x \<in> mspace m \<and> y \<in> mspace m \<and> mdist m x y \<le> r"
sorry

lemma (in Metric_space) mcball_of [simp]:
  "mcball_of (metric (M,d)) = mcball"
sorry

definition "euclidean_metric \<equiv> metric (UNIV,dist)"

lemma mspace_euclidean_metric [simp]: "mspace euclidean_metric = UNIV"
sorry

lemma mdist_euclidean_metric [simp]: "mdist euclidean_metric = dist"
sorry

lemma mtopology_of_euclidean [simp]: "mtopology_of euclidean_metric = euclidean"
sorry

text \<open>Allows reference to the current metric space within the locale as a value\<close>
definition (in Metric_space) "Self \<equiv> metric (M,d)"

lemma (in Metric_space) mspace_Self [simp]: "mspace Self = M"
sorry

lemma (in Metric_space) mdist_Self [simp]: "mdist Self = d"
sorry

text\<open> Subspace of a metric space\<close>

definition submetric where
  "submetric \<equiv> \<lambda>m S. metric (S \<inter> mspace m, mdist m)"

lemma mspace_submetric [simp]: "mspace (submetric m S) = S \<inter> mspace m"
sorry

lemma mdist_submetric [simp]: "mdist (submetric m S) = mdist m"
sorry

lemma submetric_UNIV [simp]: "submetric m UNIV = m"
sorry

lemma submetric_submetric [simp]:
   "submetric (submetric m S) T = submetric m (S \<inter> T)"
sorry

lemma submetric_mspace [simp]:
   "submetric m (mspace m) = m"
sorry

lemma submetric_restrict:
   "submetric m S = submetric m (mspace m \<inter> S)"
sorry

lemma mtopology_of_submetric: "mtopology_of (submetric m A) = subtopology (mtopology_of m) A"
sorry


subsection\<open>The discrete metric\<close>

locale discrete_metric =
  fixes M :: "'a set"

definition (in discrete_metric) dd :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  where "dd \<equiv> \<lambda>x y::'a. if x=y then 0 else 1"

lemma metric_M_dd: "Metric_space M discrete_metric.dd"
sorry

sublocale discrete_metric \<subseteq> disc: Metric_space M dd
  by (simp add: metric_M_dd)


lemma (in discrete_metric) mopen_singleton:
  assumes "x \<in> M" shows "disc.mopen {x}"
sorry

lemma (in discrete_metric) mtopology_discrete_metric:
   "disc.mtopology = discrete_topology M"
sorry

lemma (in discrete_metric) discrete_ultrametric:
   "dd x z \<le> max (dd x y) (dd y z)"
sorry

lemma (in discrete_metric) dd_le1: "dd x y \<le> 1"
sorry

lemma (in discrete_metric) mbounded_discrete_metric: "disc.mbounded S \<longleftrightarrow> S \<subseteq> M"
sorry

subsection\<open>Metrizable spaces\<close>

definition metrizable_space where
  "metrizable_space X \<equiv> \<exists>M d. Metric_space M d \<and> X = Metric_space.mtopology M d"

lemma (in Metric_space) metrizable_space_mtopology: "metrizable_space mtopology"
sorry

lemma (in Metric_space) first_countable_mtopology: "first_countable mtopology"
sorry

lemma metrizable_imp_first_countable:
   "metrizable_space X \<Longrightarrow> first_countable X"
sorry

lemma openin_mtopology_eq_open [simp]: "openin Met_TC.mtopology = open"
sorry

lemma closedin_mtopology_eq_closed [simp]: "closedin Met_TC.mtopology = closed"
sorry

lemma compactin_mtopology_eq_compact [simp]: "compactin Met_TC.mtopology = compact"
sorry

lemma metrizable_space_discrete_topology [simp]:
   "metrizable_space(discrete_topology U)"
sorry

lemma empty_metrizable_space: "metrizable_space trivial_topology"
sorry

lemma metrizable_space_subtopology:
  assumes "metrizable_space X"
  shows "metrizable_space(subtopology X S)"
sorry

lemma homeomorphic_metrizable_space_aux:
  assumes "X homeomorphic_space Y" "metrizable_space X"
  shows "metrizable_space Y"
sorry

lemma homeomorphic_metrizable_space:
  assumes "X homeomorphic_space Y"
  shows "metrizable_space X \<longleftrightarrow> metrizable_space Y"
sorry

lemma metrizable_space_retraction_map_image:
   "retraction_map X Y r \<and> metrizable_space X
        \<Longrightarrow> metrizable_space Y"
sorry

lemma metrizable_imp_Hausdorff_space:
   "metrizable_space X \<Longrightarrow> Hausdorff_space X"
sorry


(**
lemma metrizable_imp_kc_space:
   "metrizable_space X \<Longrightarrow> kc_space X"
oops
  MESON_TAC[METRIZABLE_IMP_HAUSDORFF_SPACE; HAUSDORFF_IMP_KC_SPACE]);;

lemma kc_space_mtopology:
   "kc_space mtopology"
oops
  REWRITE_TAC[GSYM FORALL_METRIZABLE_SPACE; METRIZABLE_IMP_KC_SPACE]);;
**)

lemma metrizable_imp_t1_space:
   "metrizable_space X \<Longrightarrow> t1_space X"
sorry

lemma closed_imp_gdelta_in:
  assumes X: "metrizable_space X" and S: "closedin X S"
  shows "gdelta_in X S"
sorry

lemma open_imp_fsigma_in:
   "\<lbrakk>metrizable_space X; openin X S\<rbrakk> \<Longrightarrow> fsigma_in X S"
sorry

lemma metrizable_space_euclidean:
  "metrizable_space (euclidean :: 'a::metric_space topology)"
sorry

lemma (in Metric_space) regular_space_mtopology:
   "regular_space mtopology"
sorry

lemma metrizable_imp_regular_space:
   "metrizable_space X \<Longrightarrow> regular_space X"
sorry

lemma regular_space_euclidean:
 "regular_space (euclidean :: 'a::metric_space topology)"
sorry
subsection\<open>Limits at a point in a topological space\<close>

lemma (in Metric_space) eventually_atin_metric:
   "eventually P (atin mtopology a) \<longleftrightarrow>
        (a \<in> M \<longrightarrow> (\<exists>\<delta>>0. \<forall>x. x \<in> M \<and> 0 < d x a \<and> d x a < \<delta> \<longrightarrow> P x))"  (is "?lhs=?rhs")
sorry

subsection \<open>Normal spaces and metric spaces\<close>

lemma (in Metric_space) normal_space_mtopology:
   "normal_space mtopology"
sorry

lemma metrizable_imp_normal_space:
   "metrizable_space X \<Longrightarrow> normal_space X"
sorry

subsection\<open>Topological limitin in metric spaces\<close>


lemma (in Metric_space) limitin_mspace:
   "limitin mtopology f l F \<Longrightarrow> l \<in> M"
sorry

lemma (in Metric_space) limitin_metric_unique:
   "\<lbrakk>limitin mtopology f l1 F; limitin mtopology f l2 F; F \<noteq> bot\<rbrakk> \<Longrightarrow> l1 = l2"
sorry

lemma (in Metric_space) limitin_metric:
   "limitin mtopology f l F \<longleftrightarrow> l \<in> M \<and> (\<forall>\<epsilon>>0. eventually (\<lambda>x. f x \<in> M \<and> d (f x) l < \<epsilon>) F)"  
   (is "?lhs=?rhs")
sorry

lemma (in Metric_space) limit_metric_sequentially:
   "limitin mtopology f l sequentially \<longleftrightarrow>
     l \<in> M \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. f n \<in> M \<and> d (f n) l < \<epsilon>)"
sorry

lemma (in Submetric) limitin_submetric_iff:
   "limitin sub.mtopology f l F \<longleftrightarrow>
     l \<in> A \<and> eventually (\<lambda>x. f x \<in> A) F \<and> limitin mtopology f l F" (is "?lhs=?rhs")
sorry

lemma (in Metric_space) metric_closedin_iff_sequentially_closed:
   "closedin mtopology S \<longleftrightarrow>
    S \<subseteq> M \<and> (\<forall>\<sigma> l. range \<sigma> \<subseteq> S \<and> limitin mtopology \<sigma> l sequentially \<longrightarrow> l \<in> S)" (is "?lhs=?rhs")
sorry

lemma (in Metric_space) limit_atin_metric:
   "limitin X f y (atin mtopology x) \<longleftrightarrow>
      y \<in> topspace X \<and>
      (x \<in> M
       \<longrightarrow> (\<forall>V. openin X V \<and> y \<in> V
               \<longrightarrow> (\<exists>\<delta>>0.  \<forall>x'. x' \<in> M \<and> 0 < d x' x \<and> d x' x < \<delta> \<longrightarrow> f x' \<in> V)))"
sorry

lemma (in Metric_space) limitin_metric_dist_null:
   "limitin mtopology f l F \<longleftrightarrow> l \<in> M \<and> eventually (\<lambda>x. f x \<in> M) F \<and> ((\<lambda>x. d (f x) l) \<longlongrightarrow> 0) F"
sorry

subsection\<open>Cauchy sequences and complete metric spaces\<close>

context Metric_space
begin

definition MCauchy :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "MCauchy \<sigma> \<equiv> range \<sigma> \<subseteq> M \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>)"

definition mcomplete
  where "mcomplete \<equiv> (\<forall>\<sigma>. MCauchy \<sigma> \<longrightarrow> (\<exists>x. limitin mtopology \<sigma> x sequentially))"

lemma mcomplete_empty [iff]: "Metric_space.mcomplete {} d"
sorry

lemma MCauchy_imp_MCauchy_suffix: "MCauchy \<sigma> \<Longrightarrow> MCauchy (\<sigma> \<circ> (+)n)"
sorry

lemma mcomplete:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<sigma>. (\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M) \<and>
     (\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>) \<longrightarrow>
     (\<exists>x. limitin mtopology \<sigma> x sequentially))" (is "?lhs=?rhs")
sorry

lemma mcomplete_empty_mspace: "M = {} \<Longrightarrow> mcomplete"
sorry

lemma MCauchy_const [simp]: "MCauchy (\<lambda>n. a) \<longleftrightarrow> a \<in> M"
sorry

lemma convergent_imp_MCauchy:
  assumes "range \<sigma> \<subseteq> M" and lim: "limitin mtopology \<sigma> l sequentially"
  shows "MCauchy \<sigma>"
sorry

lemma mcomplete_alt:
   "mcomplete \<longleftrightarrow> (\<forall>\<sigma>. MCauchy \<sigma> \<longleftrightarrow> range \<sigma> \<subseteq> M \<and> (\<exists>x. limitin mtopology \<sigma> x sequentially))"
sorry

lemma MCauchy_subsequence:
  assumes "strict_mono r" "MCauchy \<sigma>"
  shows "MCauchy (\<sigma> \<circ> r)"
sorry

lemma MCauchy_offset:
  assumes cau: "MCauchy (\<sigma> \<circ> (+)k)" and \<sigma>: "\<And>n. n < k \<Longrightarrow> \<sigma> n \<in> M" 
  shows "MCauchy \<sigma>"
sorry

lemma MCauchy_convergent_subsequence:
  assumes cau: "MCauchy \<sigma>" and "strict_mono r" 
     and lim: "limitin mtopology (\<sigma> \<circ> r) a sequentially"
  shows "limitin mtopology \<sigma> a sequentially"
sorry

lemma MCauchy_interleaving_gen:
  "MCauchy (\<lambda>n. if even n then x(n div 2) else y(n div 2)) \<longleftrightarrow>
    (MCauchy x \<and> MCauchy y \<and> (\<lambda>n. d (x n) (y n)) \<longlonglongrightarrow> 0)" (is "?lhs=?rhs")
sorry

lemma MCauchy_interleaving:
   "MCauchy (\<lambda>n. if even n then \<sigma>(n div 2) else a) \<longleftrightarrow>
    range \<sigma> \<subseteq> M \<and> limitin mtopology \<sigma> a sequentially"  (is "?lhs=?rhs")
sorry

lemma mcomplete_nest:
   "mcomplete \<longleftrightarrow>
      (\<forall>C::nat \<Rightarrow>'a set. (\<forall>n. closedin mtopology (C n)) \<and>
          (\<forall>n. C n \<noteq> {}) \<and> decseq C \<and> (\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>)
          \<longrightarrow> \<Inter> (range C) \<noteq> {})" (is "?lhs=?rhs")
sorry

lemma mcomplete_nest_sing:
   "mcomplete \<longleftrightarrow>
    (\<forall>C. (\<forall>n. closedin mtopology (C n)) \<and>
          (\<forall>n. C n \<noteq> {}) \<and> decseq C \<and> (\<forall>e>0. \<exists>n a. C n \<subseteq> mcball a e)
         \<longrightarrow> (\<exists>l. l \<in> M \<and> \<Inter> (range C) = {l}))"
sorry

lemma mcomplete_fip:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C \<in> \<C>. closedin mtopology C) \<and>
         (\<forall>e>0. \<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a e) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {})
        \<longrightarrow> \<Inter> \<C> \<noteq> {})" 
   (is "?lhs = ?rhs")
sorry

lemma mcomplete_fip_sing:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C\<in>\<C>. closedin mtopology C) \<and>
     (\<forall>e>0. \<exists>c a. c \<in> \<C> \<and> c \<subseteq> mcball a e) \<and>
     (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {}) \<longrightarrow>
     (\<exists>l. l \<in> M \<and> \<Inter> \<C> = {l}))"
   (is "?lhs = ?rhs")
sorry

end

definition mcomplete_of :: "'a metric \<Rightarrow> bool"
  where "mcomplete_of \<equiv> \<lambda>m. Metric_space.mcomplete (mspace m) (mdist m)"

lemma (in Metric_space) mcomplete_of [simp]: "mcomplete_of (metric (M,d)) = mcomplete"
sorry

lemma mcomplete_trivial: "Metric_space.mcomplete {} (\<lambda>x y. 0)"
sorry

lemma mcomplete_trivial_singleton: "Metric_space.mcomplete {\<lambda>x. a} (\<lambda>x y. 0)"
sorry

lemma MCauchy_iff_Cauchy [iff]: "Met_TC.MCauchy = Cauchy"
sorry

lemma mcomplete_iff_complete [iff]:
  "Met_TC.mcomplete TYPE('a::metric_space) \<longleftrightarrow> complete (UNIV::'a set)"
sorry

context Submetric
begin 

lemma MCauchy_submetric:
   "sub.MCauchy \<sigma> \<longleftrightarrow> range \<sigma> \<subseteq> A \<and> MCauchy \<sigma>"
sorry

lemma closedin_mcomplete_imp_mcomplete:
  assumes clo: "closedin mtopology A" and "mcomplete"
  shows "sub.mcomplete"
sorry

lemma sequentially_closedin_mcomplete_imp_mcomplete:
  assumes "mcomplete" and "\<And>\<sigma> l. range \<sigma> \<subseteq> A \<and> limitin mtopology \<sigma> l sequentially \<Longrightarrow> l \<in> A"
  shows "sub.mcomplete"
sorry

end

context Metric_space
begin

lemma mcomplete_Un:
  assumes A: "Submetric M d A" "Metric_space.mcomplete A d" 
      and B: "Submetric M d B" "Metric_space.mcomplete B d"
  shows   "Submetric M d (A \<union> B)" "Metric_space.mcomplete (A \<union> B) d"
sorry

lemma mcomplete_Union:
  assumes "finite \<S>"
    and "\<And>A. A \<in> \<S> \<Longrightarrow> Submetric M d A" "\<And>A. A \<in> \<S> \<Longrightarrow> Metric_space.mcomplete A d"
  shows   "Submetric M d (\<Union>\<S>)" "Metric_space.mcomplete (\<Union>\<S>) d"
sorry

lemma mcomplete_Inter:
  assumes "finite \<S>" "\<S> \<noteq> {}"
    and sub: "\<And>A. A \<in> \<S> \<Longrightarrow> Submetric M d A" 
    and comp: "\<And>A. A \<in> \<S> \<Longrightarrow> Metric_space.mcomplete A d"
  shows "Submetric M d (\<Inter>\<S>)" "Metric_space.mcomplete (\<Inter>\<S>) d"
sorry

lemma mcomplete_Int:
  assumes A: "Submetric M d A" "Metric_space.mcomplete A d" 
      and B: "Submetric M d B" "Metric_space.mcomplete B d"
    shows   "Submetric M d (A \<inter> B)" "Metric_space.mcomplete (A \<inter> B) d"
sorry

subsection\<open>Totally bounded subsets of metric spaces\<close>

definition mtotally_bounded 
  where "mtotally_bounded S \<equiv> \<forall>\<epsilon>>0. \<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"

lemma mtotally_bounded_empty [iff]: "mtotally_bounded {}"
sorry

lemma finite_imp_mtotally_bounded:
   "\<lbrakk>finite S; S \<subseteq> M\<rbrakk> \<Longrightarrow> mtotally_bounded S"
sorry

lemma mtotally_bounded_imp_subset: "mtotally_bounded S \<Longrightarrow> S \<subseteq> M"
sorry

lemma mtotally_bounded_sing [simp]:
   "mtotally_bounded {x} \<longleftrightarrow> x \<in> M"
sorry

lemma mtotally_bounded_Un:
  assumes  "mtotally_bounded S" "mtotally_bounded T"
  shows "mtotally_bounded (S \<union> T)"
sorry

lemma mtotally_bounded_Union:
  assumes "finite f" "\<And>S. S \<in> f \<Longrightarrow> mtotally_bounded S"
  shows "mtotally_bounded (\<Union>f)"
sorry

lemma mtotally_bounded_imp_mbounded:
  assumes "mtotally_bounded S"
  shows "mbounded S"
sorry

lemma mtotally_bounded_sequentially:
  "mtotally_bounded S \<longleftrightarrow>
    S \<subseteq> M \<and> (\<forall>\<sigma>::nat \<Rightarrow> 'a. range \<sigma> \<subseteq> S \<longrightarrow> (\<exists>r. strict_mono r \<and> MCauchy (\<sigma> \<circ> r)))"
  (is "_ \<longleftrightarrow> _ \<and> ?rhs")
sorry

lemma mtotally_bounded_subset:
   "\<lbrakk>mtotally_bounded S; T \<subseteq> S\<rbrakk> \<Longrightarrow> mtotally_bounded T"
sorry

lemma mtotally_bounded_submetric:
  assumes "mtotally_bounded S" "S \<subseteq> T" "T \<subseteq> M"
  shows "Metric_space.mtotally_bounded T d S"
sorry

lemma mtotally_bounded_absolute:
   "mtotally_bounded S \<longleftrightarrow> S \<subseteq> M \<and> Metric_space.mtotally_bounded S d S "
sorry

lemma mtotally_bounded_closure_of:
  assumes "mtotally_bounded S"
  shows "mtotally_bounded (mtopology closure_of S)"
sorry

lemma mtotally_bounded_closure_of_eq:
   "S \<subseteq> M \<Longrightarrow> mtotally_bounded (mtopology closure_of S) \<longleftrightarrow> mtotally_bounded S"
sorry

lemma mtotally_bounded_cauchy_sequence:
  assumes "MCauchy \<sigma>"
  shows "mtotally_bounded (range \<sigma>)"
sorry

lemma MCauchy_imp_mbounded:
   "MCauchy \<sigma> \<Longrightarrow> mbounded (range \<sigma>)"
sorry

subsection\<open>Compactness in metric spaces\<close>

lemma Bolzano_Weierstrass_property:
  assumes "S \<subseteq> U" "S \<subseteq> M"
  shows
   "(\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> U \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)) \<longleftrightarrow>
    (\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> U \<inter> mtopology derived_set_of T \<noteq> {})"  (is "?lhs=?rhs")
sorry

subsubsection \<open>More on Bolzano Weierstrass\<close>

lemma Bolzano_Weierstrass_A: 
  assumes "compactin mtopology S" "T \<subseteq> S" "infinite T"
  shows "S \<inter> mtopology derived_set_of T \<noteq> {}"
sorry

lemma Bolzano_Weierstrass_B:
  fixes \<sigma> :: "nat \<Rightarrow> 'a"
  assumes "S \<subseteq> M" "range \<sigma> \<subseteq> S"
    and "\<And>T. \<lbrakk>T \<subseteq> S \<and> infinite T\<rbrakk> \<Longrightarrow> S \<inter> mtopology derived_set_of T \<noteq> {}"
  shows "\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
sorry

lemma Bolzano_Weierstrass_C:
  assumes "S \<subseteq> M"
  assumes "\<And>\<sigma>:: nat \<Rightarrow> 'a. range \<sigma> \<subseteq> S \<Longrightarrow>
                (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)"
  shows "mtotally_bounded S"
sorry

lemma Bolzano_Weierstrass_D:
  assumes "S \<subseteq> M" "S \<subseteq> \<Union>\<C>" and opeU: "\<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U"
  assumes \<section>: "(\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially))"
  shows "\<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
sorry

lemma Bolzano_Weierstrass_E:
  assumes "mtotally_bounded S" "S \<subseteq> M"
  and S: "\<And>\<C>. \<lbrakk>\<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U; S \<subseteq> \<Union>\<C>\<rbrakk> \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
  shows "compactin mtopology S"
sorry

lemma compactin_eq_Bolzano_Weierstrass:
  "compactin mtopology S \<longleftrightarrow>
   S \<subseteq> M \<and> (\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> S \<inter> mtopology derived_set_of T \<noteq> {})"
sorry

lemma compactin_sequentially:
  shows "compactin mtopology S \<longleftrightarrow>
        S \<subseteq> M \<and>
        ((\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)))"
sorry

lemma compactin_imp_mtotally_bounded: 
  "compactin mtopology S \<Longrightarrow> mtotally_bounded S"
sorry

lemma lebesgue_number:
    "\<lbrakk>compactin mtopology S; S \<subseteq> \<Union>\<C>; \<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U\<rbrakk>
    \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
sorry

lemma compact_space_sequentially:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> M
         \<longrightarrow> (\<exists>l r. l \<in> M \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially))"
sorry

lemma compact_space_eq_Bolzano_Weierstrass:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>S. S \<subseteq> M \<and> infinite S \<longrightarrow> mtopology derived_set_of S \<noteq> {})"
sorry

lemma compact_space_nest:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>C. (\<forall>n::nat. closedin mtopology (C n)) \<and> (\<forall>n. C n \<noteq> {}) \<and> decseq C \<longrightarrow> \<Inter>(range C) \<noteq> {})"
   (is "?lhs=?rhs")
sorry

lemma (in discrete_metric) mcomplete_discrete_metric: "disc.mcomplete"
sorry

lemma compact_space_imp_mcomplete: "compact_space mtopology \<Longrightarrow> mcomplete"
sorry

lemma (in Submetric) compactin_imp_mcomplete:
   "compactin mtopology A \<Longrightarrow> sub.mcomplete"
sorry

lemma (in Submetric) mcomplete_imp_closedin:
  assumes "sub.mcomplete"
  shows "closedin mtopology A"
sorry

lemma (in Submetric) closedin_eq_mcomplete:
   "mcomplete \<Longrightarrow> (closedin mtopology A \<longleftrightarrow> sub.mcomplete)"
sorry

lemma compact_space_eq_mcomplete_mtotally_bounded:
   "compact_space mtopology \<longleftrightarrow> mcomplete \<and> mtotally_bounded M"
sorry

lemma compact_closure_of_imp_mtotally_bounded:
   "\<lbrakk>compactin mtopology (mtopology closure_of S); S \<subseteq> M\<rbrakk>
      \<Longrightarrow> mtotally_bounded S"
sorry

lemma mtotally_bounded_eq_compact_closure_of:
  assumes "mcomplete"
  shows "mtotally_bounded S \<longleftrightarrow> S \<subseteq> M \<and> compactin mtopology (mtopology closure_of S)"
  (is "?lhs=?rhs")
sorry

lemma compact_closure_of_eq_Bolzano_Weierstrass:
   "compactin mtopology (mtopology closure_of S) \<longleftrightarrow>
    (\<forall>T. infinite T \<and> T \<subseteq> S \<and> T \<subseteq> M \<longrightarrow> mtopology derived_set_of T \<noteq> {})"  (is "?lhs=?rhs")
sorry

end

lemma (in discrete_metric) mtotally_bounded_discrete_metric:
   "disc.mtotally_bounded S \<longleftrightarrow> finite S \<and> S \<subseteq> M" (is "?lhs=?rhs")
sorry


context Metric_space
begin

lemma derived_set_of_infinite_openin_metric:
   "mtopology derived_set_of S =
    {x \<in> M. \<forall>U. x \<in> U \<and> openin mtopology U \<longrightarrow> infinite(S \<inter> U)}"
sorry

lemma derived_set_of_infinite_1: 
  assumes "infinite (S \<inter> mball x \<epsilon>)" 
  shows "infinite (S \<inter> mcball x \<epsilon>)"
sorry

lemma derived_set_of_infinite_2:
  assumes "openin mtopology U" "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> infinite (S \<inter> mcball x \<epsilon>)" and "x \<in> U"
  shows "infinite (S \<inter> U)"
sorry

lemma derived_set_of_infinite_mball:
  "mtopology derived_set_of S = {x \<in> M. \<forall>e>0. infinite(S \<inter> mball x e)}"
sorry

lemma derived_set_of_infinite_mcball:
  "mtopology derived_set_of S = {x \<in> M. \<forall>e>0. infinite(S \<inter> mcball x e)}"
sorry
end

subsection\<open>Continuous functions on metric spaces\<close>

context Metric_space
begin

lemma continuous_map_to_metric:
   "continuous_map X mtopology f \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>\<epsilon>>0. \<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. f y \<in> mball (f x) \<epsilon>))"
   (is "?lhs=?rhs")
sorry

lemma continuous_map_from_metric:
   "continuous_map mtopology X f \<longleftrightarrow>
    f \<in> M \<rightarrow> topspace X \<and>
    (\<forall>a \<in> M. \<forall>U. openin X U \<and> f a \<in> U \<longrightarrow> (\<exists>r>0. \<forall>x. x \<in> M \<and> d a x < r \<longrightarrow> f x \<in> U))"
sorry

text \<open>An abstract formulation, since the limits do not have to be sequential\<close>
lemma continuous_map_uniform_limit:
  assumes contf: "\<forall>\<^sub>F \<xi> in F. continuous_map X mtopology (f \<xi>)"
    and dfg: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F \<xi> in F. \<forall>x \<in> topspace X. g x \<in> M \<and> d (f \<xi> x) (g x) < \<epsilon>"
    and nontriv: "\<not> trivial_limit F"
  shows "continuous_map X mtopology g"
sorry

lemma continuous_map_uniform_limit_alt:
  assumes contf: "\<forall>\<^sub>F \<xi> in F. continuous_map X mtopology (f \<xi>)"
    and gim: "g \<in> topspace X \<rightarrow> M"
    and dfg: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F \<xi> in F. \<forall>x \<in> topspace X. d (f \<xi> x) (g x) < \<epsilon>"
    and nontriv: "\<not> trivial_limit F"
  shows "continuous_map X mtopology g"
sorry

lemma continuous_map_uniformly_Cauchy_limit:
  assumes "mcomplete"
  assumes contf: "\<forall>\<^sub>F n in sequentially. continuous_map X mtopology (f n)"
    and Cauchy': "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>m n x. N \<le> m \<longrightarrow> N \<le> n \<longrightarrow> x \<in> topspace X \<longrightarrow> d (f m x) (f n x) < \<epsilon>"
  obtains g where
    "continuous_map X mtopology g"
    "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. d (f n x) (g x) < \<epsilon>"
sorry

lemma metric_continuous_map:
  assumes "Metric_space M' d'"
  shows
   "continuous_map mtopology (Metric_space.mtopology M' d') f \<longleftrightarrow>
    f ` M \<subseteq> M' \<and> (\<forall>a \<in> M. \<forall>\<epsilon>>0. \<exists>\<delta>>0.  (\<forall>x. x \<in> M \<and> d a x < \<delta> \<longrightarrow> d' (f a) (f x) < \<epsilon>))"
   (is "?lhs = ?rhs")
sorry

end (*Metric_space*)


subsection \<open>Completely metrizable spaces\<close>

text \<open>These spaces are topologically complete\<close>

definition completely_metrizable_space where
 "completely_metrizable_space X \<equiv> 
     \<exists>M d. Metric_space M d \<and> Metric_space.mcomplete M d \<and> X = Metric_space.mtopology M d"

lemma empty_completely_metrizable_space: 
  "completely_metrizable_space trivial_topology"
sorry

lemma completely_metrizable_imp_metrizable_space:
   "completely_metrizable_space X \<Longrightarrow> metrizable_space X"
sorry

lemma (in Metric_space) completely_metrizable_space_mtopology:
   "mcomplete \<Longrightarrow> completely_metrizable_space mtopology"
sorry

lemma completely_metrizable_space_discrete_topology:
   "completely_metrizable_space (discrete_topology U)"
sorry

lemma completely_metrizable_space_euclidean:
    "completely_metrizable_space (euclidean:: 'a::complete_space topology)"
sorry

lemma completely_metrizable_space_closedin:
  assumes X: "completely_metrizable_space X" and S: "closedin X S"
  shows "completely_metrizable_space(subtopology X S)"
sorry

lemma completely_metrizable_space_cbox: "completely_metrizable_space (top_of_set (cbox a b))"
sorry

lemma homeomorphic_completely_metrizable_space_aux:
  assumes homXY: "X homeomorphic_space Y" and X: "completely_metrizable_space X"
  shows "completely_metrizable_space Y"
sorry

lemma homeomorphic_completely_metrizable_space:
   "X homeomorphic_space Y
        \<Longrightarrow> completely_metrizable_space X \<longleftrightarrow> completely_metrizable_space Y"
sorry

lemma completely_metrizable_space_retraction_map_image:
  assumes r: "retraction_map X Y r" and X: "completely_metrizable_space X"
  shows "completely_metrizable_space Y"
sorry



subsection \<open>Product metric\<close>

text\<open>For the nicest fit with the main Euclidean theories, we choose the Euclidean product, 
though other definitions of the product work.\<close>


definition "prod_dist \<equiv> \<lambda>d1 d2 (x,y) (x',y'). sqrt(d1 x x' ^ 2 + d2 y y' ^ 2)"

locale Metric_space12 = M1: Metric_space M1 d1 + M2: Metric_space M2 d2 for M1 d1 M2 d2

lemma (in Metric_space12) prod_metric: "Metric_space (M1 \<times> M2) (prod_dist d1 d2)"
sorry

sublocale Metric_space12 \<subseteq> Prod_metric: Metric_space "M1\<times>M2" "prod_dist d1 d2" 
  by (simp add: prod_metric)

text \<open>For easy reference to theorems outside of the locale\<close>
lemma Metric_space12_mspace_mdist:
  "Metric_space12 (mspace m1) (mdist m1) (mspace m2) (mdist m2)"
sorry

definition prod_metric where
 "prod_metric \<equiv> \<lambda>m1 m2. metric (mspace m1 \<times> mspace m2, prod_dist (mdist m1) (mdist m2))"

lemma submetric_prod_metric:
   "submetric (prod_metric m1 m2) (S \<times> T) = prod_metric (submetric m1 S) (submetric m2 T)"
sorry

lemma mspace_prod_metric [simp]:"
  mspace (prod_metric m1 m2) = mspace m1 \<times> mspace m2"
sorry

lemma mdist_prod_metric [simp]: 
  "mdist (prod_metric m1 m2) = prod_dist (mdist m1) (mdist m2)"
sorry

lemma prod_dist_dist [simp]: "prod_dist dist dist = dist"
sorry

lemma prod_metric_euclidean [simp]:
  "prod_metric euclidean_metric euclidean_metric = euclidean_metric"
sorry

context Metric_space12
begin

lemma component_le_prod_metric:
   "d1 x1 x2 \<le> prod_dist d1 d2 (x1,y1) (x2,y2)" "d2 y1 y2 \<le> prod_dist d1 d2 (x1,y1) (x2,y2)"
sorry

lemma prod_metric_le_components:
  "\<lbrakk>x1 \<in> M1; y1 \<in> M1; x2 \<in> M2; y2 \<in> M2\<rbrakk>
    \<Longrightarrow> prod_dist d1 d2 (x1,x2) (y1,y2) \<le> d1 x1 y1 + d2 x2 y2"
sorry

lemma mball_prod_metric_subset:
   "Prod_metric.mball (x,y) r \<subseteq> M1.mball x r \<times> M2.mball y r"
sorry

lemma mcball_prod_metric_subset:
   "Prod_metric.mcball (x,y) r \<subseteq> M1.mcball x r \<times> M2.mcball y r"
sorry

lemma mball_subset_prod_metric:
   "M1.mball x1 r1 \<times> M2.mball x2 r2 \<subseteq> Prod_metric.mball (x1,x2) (r1 + r2)"
sorry

lemma mcball_subset_prod_metric:
   "M1.mcball x1 r1 \<times> M2.mcball x2 r2 \<subseteq> Prod_metric.mcball (x1,x2) (r1 + r2)"
sorry

lemma mtopology_prod_metric:
  "Prod_metric.mtopology = prod_topology M1.mtopology M2.mtopology"
sorry

lemma MCauchy_prod_metric:
   "Prod_metric.MCauchy \<sigma> \<longleftrightarrow> M1.MCauchy (fst \<circ> \<sigma>) \<and> M2.MCauchy (snd \<circ> \<sigma>)"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma mcomplete_prod_metric:
  "Prod_metric.mcomplete \<longleftrightarrow> M1 = {} \<or> M2 = {} \<or> M1.mcomplete \<and> M2.mcomplete"
  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma mbounded_prod_metric:
   "Prod_metric.mbounded U \<longleftrightarrow> M1.mbounded  (fst ` U) \<and> M2.mbounded (snd ` U)"
sorry

lemma mbounded_Times:
   "Prod_metric.mbounded (S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> M1.mbounded S \<and> M2.mbounded T"
sorry

lemma mtotally_bounded_Times:
   "Prod_metric.mtotally_bounded (S \<times> T) \<longleftrightarrow>
    S = {} \<or> T = {} \<or> M1.mtotally_bounded S \<and> M2.mtotally_bounded T"
    (is "?lhs \<longleftrightarrow> _")
sorry

lemma mtotally_bounded_prod_metric:
   "Prod_metric.mtotally_bounded U \<longleftrightarrow>
    M1.mtotally_bounded (fst ` U) \<and> M2.mtotally_bounded (snd ` U)" (is "?lhs \<longleftrightarrow> ?rhs")
sorry

end


lemma metrizable_space_prod_topology:
   "metrizable_space (prod_topology X Y) \<longleftrightarrow>
    (prod_topology X Y) = trivial_topology \<or> metrizable_space X \<and> metrizable_space Y"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma completely_metrizable_space_prod_topology:
   "completely_metrizable_space (prod_topology X Y) \<longleftrightarrow>
    (prod_topology X Y) = trivial_topology \<or>
    completely_metrizable_space X \<and> completely_metrizable_space Y"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry
 
    
subsection\<open>More sequential characterizations in a metric space\<close>

context Metric_space
begin
  
definition decreasing_dist :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool"
    where "decreasing_dist \<sigma> x \<equiv> (\<forall>m n. m < n \<longrightarrow> d (\<sigma> n) x < d (\<sigma> m) x)"

lemma decreasing_dist_imp_inj: "decreasing_dist \<sigma> a \<Longrightarrow> inj \<sigma>"
sorry

lemma eventually_atin_within_metric:
   "eventually P (atin_within mtopology a S) \<longleftrightarrow>
    (a \<in> M \<longrightarrow> (\<exists>\<delta>>0. \<forall>x. x \<in> M \<and> x \<in> S \<and> 0 < d x a \<and> d x a < \<delta> \<longrightarrow> P x))" (is "?lhs=?rhs")
sorry

lemma eventually_atin_within_A:
  assumes 
    "(\<And>\<sigma>. \<lbrakk>range \<sigma> \<subseteq> (S \<inter> M) - {a}; decreasing_dist \<sigma> a;
          inj \<sigma>; limitin mtopology \<sigma> a sequentially\<rbrakk>
      \<Longrightarrow> eventually (\<lambda>n. P (\<sigma> n)) sequentially)"
  shows "eventually P (atin_within mtopology a S)"
sorry

lemma eventually_atin_within_B:
  assumes ev: "eventually P (atin_within mtopology a S)" 
    and ran: "range \<sigma> \<subseteq> (S \<inter> M) - {a}"
    and lim: "limitin mtopology \<sigma> a sequentially"
  shows "eventually (\<lambda>n. P (\<sigma> n)) sequentially"
sorry

lemma eventually_atin_within_sequentially:
     "eventually P (atin_within mtopology a S) \<longleftrightarrow>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> (S \<inter> M) - {a} \<and>
            limitin mtopology \<sigma> a sequentially
            \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
sorry

lemma eventually_atin_within_sequentially_inj:
     "eventually P (atin_within mtopology a S) \<longleftrightarrow>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> (S \<inter> M) - {a} \<and> inj \<sigma> \<and>
            limitin mtopology \<sigma> a sequentially
            \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
sorry

lemma eventually_atin_within_sequentially_decreasing:
     "eventually P (atin_within mtopology a S) \<longleftrightarrow>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> (S \<inter> M) - {a} \<and> decreasing_dist \<sigma> a \<and>
            limitin mtopology \<sigma> a sequentially
            \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
sorry

lemma eventually_atin_sequentially:
   "eventually P (atin mtopology a) \<longleftrightarrow>
    (\<forall>\<sigma>. range \<sigma> \<subseteq> M - {a} \<and> limitin mtopology \<sigma> a sequentially
         \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
sorry

lemma eventually_atin_sequentially_inj:
   "eventually P (atin mtopology a) \<longleftrightarrow>
    (\<forall>\<sigma>. range \<sigma> \<subseteq> M - {a} \<and> inj \<sigma> \<and>
        limitin mtopology \<sigma> a sequentially
        \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
sorry

lemma eventually_atin_sequentially_decreasing:
   "eventually P (atin mtopology a) \<longleftrightarrow>
    (\<forall>\<sigma>. range \<sigma> \<subseteq> M - {a} \<and> decreasing_dist \<sigma> a \<and>
         limitin mtopology \<sigma> a sequentially
        \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
sorry

end

context Metric_space12
begin

lemma limit_atin_sequentially_within:
  "limitin M2.mtopology f l (atin_within M1.mtopology a S) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> M1 - {a} \<and>
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
sorry

lemma limit_atin_sequentially_within_inj:
  "limitin M2.mtopology f l (atin_within M1.mtopology a S) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> M1 - {a} \<and> inj \<sigma> \<and>
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
sorry

lemma limit_atin_sequentially_within_decreasing:
  "limitin M2.mtopology f l (atin_within M1.mtopology a S) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> M1 - {a} \<and> M1.decreasing_dist \<sigma> a \<and> 
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
sorry

lemma limit_atin_sequentially:
   "limitin M2.mtopology f l (atin M1.mtopology a) \<longleftrightarrow>
        l \<in> M2 \<and>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> M1 - {a} \<and>
            limitin M1.mtopology \<sigma> a sequentially
            \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
sorry

lemma limit_atin_sequentially_inj:
   "limitin M2.mtopology f l (atin M1.mtopology a) \<longleftrightarrow>
        l \<in> M2 \<and>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> M1 - {a} \<and> inj \<sigma> \<and>
            limitin M1.mtopology \<sigma> a sequentially
            \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
sorry

lemma limit_atin_sequentially_decreasing:
  "limitin M2.mtopology f l (atin M1.mtopology a) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> M1 - {a} \<and> M1.decreasing_dist \<sigma> a \<and> 
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
sorry

end

text \<open>An experiment: same result as within the locale, but using metric space variables\<close>
lemma limit_atin_sequentially_within:
  "limitin (mtopology_of m2) f l (atin_within (mtopology_of m1) a S) \<longleftrightarrow>
     l \<in> mspace m2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> mspace m1 - {a} \<and>
          limitin (mtopology_of m1) \<sigma> a sequentially
          \<longrightarrow> limitin (mtopology_of m2) (f \<circ> \<sigma>) l sequentially)"
sorry

context Metric_space
begin

lemma atin_within_imp_M:
   "atin_within mtopology x S \<noteq> bot \<Longrightarrow> x \<in> M"
sorry

lemma atin_within_sequentially_sequence:
  assumes "atin_within mtopology x S \<noteq> bot"
  obtains \<sigma> where "range \<sigma> \<subseteq> S \<inter> M - {x}" 
          "decreasing_dist \<sigma> x" "inj \<sigma>" "limitin mtopology \<sigma> x sequentially"
sorry

lemma derived_set_of_sequentially:
  "mtopology derived_set_of S =
   {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M - {x} \<and> limitin mtopology \<sigma> x sequentially}"
sorry

lemma derived_set_of_sequentially_alt:
  "mtopology derived_set_of S =
   {x. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> limitin mtopology \<sigma> x sequentially}"
sorry

lemma derived_set_of_sequentially_inj:
   "mtopology derived_set_of S =
    {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M - {x} \<and> inj \<sigma> \<and> limitin mtopology \<sigma> x sequentially}"
sorry

lemma derived_set_of_sequentially_inj_alt:
   "mtopology derived_set_of S =
    {x. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> inj \<sigma> \<and> limitin mtopology \<sigma> x sequentially}"
sorry

lemma derived_set_of_sequentially_decreasing:
   "mtopology derived_set_of S =
    {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> decreasing_dist \<sigma> x \<and> limitin mtopology \<sigma> x sequentially}"
sorry

lemma derived_set_of_sequentially_decreasing_alt:
   "mtopology derived_set_of S =
    {x. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> decreasing_dist \<sigma> x \<and> limitin mtopology \<sigma> x sequentially}"
sorry

lemma closure_of_sequentially:
   "mtopology closure_of S = 
    {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M \<and> limitin mtopology \<sigma> x sequentially}"
sorry

end (*Metric_space*)
    

subsection \<open>Three strong notions of continuity for metric spaces\<close>

subsubsection \<open>Lipschitz continuity\<close>

definition Lipschitz_continuous_map 
  where "Lipschitz_continuous_map \<equiv> 
      \<lambda>m1 m2 f. f \<in> mspace m1 \<rightarrow> mspace m2 \<and>
        (\<exists>B. \<forall>x \<in> mspace m1. \<forall>y \<in> mspace m1. mdist m2 (f x) (f y) \<le> B * mdist m1 x y)"

lemma Lipschitz_continuous_map_image: 
  "Lipschitz_continuous_map m1 m2 f \<Longrightarrow> f \<in> mspace m1 \<rightarrow> mspace m2"
sorry

lemma Lipschitz_continuous_map_pos:
   "Lipschitz_continuous_map m1 m2 f \<longleftrightarrow>
    f \<in> mspace m1 \<rightarrow> mspace m2 \<and>
        (\<exists>B>0. \<forall>x \<in> mspace m1. \<forall>y \<in> mspace m1. mdist m2 (f x) (f y) \<le> B * mdist m1 x y)"
sorry

lemma Lipschitz_continuous_map_eq:
  assumes "Lipschitz_continuous_map m1 m2 f" "\<And>x. x \<in> mspace m1 \<Longrightarrow> f x = g x"
  shows "Lipschitz_continuous_map m1 m2 g"
sorry

lemma Lipschitz_continuous_map_from_submetric:
  assumes "Lipschitz_continuous_map m1 m2 f"
  shows "Lipschitz_continuous_map (submetric m1 S) m2 f"
sorry

lemma Lipschitz_continuous_map_from_submetric_mono:
   "\<lbrakk>Lipschitz_continuous_map (submetric m1 T) m2 f; S \<subseteq> T\<rbrakk>
           \<Longrightarrow> Lipschitz_continuous_map (submetric m1 S) m2 f"
sorry

lemma Lipschitz_continuous_map_into_submetric:
   "Lipschitz_continuous_map m1 (submetric m2 S) f \<longleftrightarrow>
        f \<in> mspace m1 \<rightarrow> S \<and> Lipschitz_continuous_map m1 m2 f"
sorry

lemma Lipschitz_continuous_map_const:
  "Lipschitz_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow>
        mspace m1 = {} \<or> c \<in> mspace m2"
sorry

lemma Lipschitz_continuous_map_id:
   "Lipschitz_continuous_map m1 m1 (\<lambda>x. x)"
sorry

lemma Lipschitz_continuous_map_compose:
  assumes f: "Lipschitz_continuous_map m1 m2 f" and g: "Lipschitz_continuous_map m2 m3 g"
  shows "Lipschitz_continuous_map m1 m3 (g \<circ> f)"
sorry

subsubsection \<open>Uniform continuity\<close>

definition uniformly_continuous_map 
  where "uniformly_continuous_map \<equiv> 
      \<lambda>m1 m2 f. f \<in> mspace m1 \<rightarrow> mspace m2 \<and>
        (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x \<in> mspace m1. \<forall>y \<in> mspace m1. 
                           mdist m1 y x < \<delta> \<longrightarrow> mdist m2 (f y) (f x) < \<epsilon>)"

lemma uniformly_continuous_map_funspace: 
  "uniformly_continuous_map m1 m2 f \<Longrightarrow> f \<in> mspace m1 \<rightarrow> mspace m2"
sorry

lemma ucmap_A:
  assumes "uniformly_continuous_map m1 m2 f"
  and "(\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0"
    and "range \<rho> \<subseteq> mspace m1" "range \<sigma> \<subseteq> mspace m1"
  shows "(\<lambda>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n))) \<longlonglongrightarrow> 0"
sorry

lemma ucmap_B:
  assumes \<section>: "\<And>\<rho> \<sigma>. \<lbrakk>range \<rho> \<subseteq> mspace m1; range \<sigma> \<subseteq> mspace m1;
              (\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0\<rbrakk>
              \<Longrightarrow> (\<lambda>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n))) \<longlonglongrightarrow> 0"
    and "0 < \<epsilon>"
    and \<rho>: "range \<rho> \<subseteq> mspace m1"
    and \<sigma>: "range \<sigma> \<subseteq> mspace m1"
    and "(\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0"
  shows "\<exists>n. mdist m2 (f (\<rho> (n::nat))) (f (\<sigma> n)) < \<epsilon>"
sorry

lemma ucmap_C: 
  assumes \<section>: "\<And>\<rho> \<sigma> \<epsilon>. \<lbrakk>\<epsilon> > 0; range \<rho> \<subseteq> mspace m1; range \<sigma> \<subseteq> mspace m1;
                       ((\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0)\<rbrakk>
                      \<Longrightarrow> \<exists>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n)) < \<epsilon>"
    and fim: "f \<in> mspace m1 \<rightarrow> mspace m2"
  shows "uniformly_continuous_map m1 m2 f"
sorry

lemma uniformly_continuous_map_sequentially:
  "uniformly_continuous_map m1 m2 f \<longleftrightarrow>
    f \<in> mspace m1 \<rightarrow> mspace m2 \<and>
    (\<forall>\<rho> \<sigma>. range \<rho> \<subseteq> mspace m1 \<and> range \<sigma> \<subseteq> mspace m1 \<and> (\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0
          \<longrightarrow> (\<lambda>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n))) \<longlonglongrightarrow> 0)"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma uniformly_continuous_map_sequentially_alt:
    "uniformly_continuous_map m1 m2 f \<longleftrightarrow>
      f \<in> mspace m1 \<rightarrow> mspace m2 \<and>
      (\<forall>\<epsilon>>0. \<forall>\<rho> \<sigma>. range \<rho> \<subseteq> mspace m1 \<and> range \<sigma> \<subseteq> mspace m1 \<and>
            ((\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0)
            \<longrightarrow> (\<exists>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n)) < \<epsilon>))"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma uniformly_continuous_map_eq:
   "\<lbrakk>\<And>x. x \<in> mspace m1 \<Longrightarrow> f x = g x; uniformly_continuous_map m1 m2 f\<rbrakk>
      \<Longrightarrow> uniformly_continuous_map m1 m2 g"
sorry

lemma uniformly_continuous_map_from_submetric:
  assumes "uniformly_continuous_map m1 m2 f"
  shows "uniformly_continuous_map (submetric m1 S) m2 f"
sorry

lemma uniformly_continuous_map_from_submetric_mono:
   "\<lbrakk>uniformly_continuous_map (submetric m1 T) m2 f; S \<subseteq> T\<rbrakk>
           \<Longrightarrow> uniformly_continuous_map (submetric m1 S) m2 f"
sorry

lemma uniformly_continuous_map_into_submetric:
   "uniformly_continuous_map m1 (submetric m2 S) f \<longleftrightarrow>
        f \<in> mspace m1 \<rightarrow> S \<and> uniformly_continuous_map m1 m2 f"
sorry

lemma uniformly_continuous_map_const:
  "uniformly_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow>
        mspace m1 = {} \<or> c \<in> mspace m2"
sorry

lemma uniformly_continuous_map_id [simp]:
   "uniformly_continuous_map m1 m1 (\<lambda>x. x)"
sorry

lemma uniformly_continuous_map_compose:
  assumes f: "uniformly_continuous_map m1 m2 f" and g: "uniformly_continuous_map m2 m3 g"
  shows "uniformly_continuous_map m1 m3 (g \<circ> f)"
sorry

lemma uniformly_continuous_map_real_const [simp]:
   "uniformly_continuous_map m euclidean_metric (\<lambda>x. c)"
sorry

text \<open>Equivalence between "abstract" and "type class" notions\<close>
lemma uniformly_continuous_map_euclidean [simp]:
  "uniformly_continuous_map (submetric euclidean_metric S) euclidean_metric f
     = uniformly_continuous_on S f"
sorry

subsubsection \<open>Cauchy continuity\<close>

definition Cauchy_continuous_map where
 "Cauchy_continuous_map \<equiv>
  \<lambda>m1 m2 f. \<forall>\<sigma>. Metric_space.MCauchy (mspace m1) (mdist m1) \<sigma> 
            \<longrightarrow> Metric_space.MCauchy (mspace m2) (mdist m2) (f \<circ> \<sigma>)"

lemma Cauchy_continuous_map_euclidean [simp]:
  "Cauchy_continuous_map (submetric euclidean_metric S) euclidean_metric f
     = Cauchy_continuous_on S f"
sorry

lemma Cauchy_continuous_map_funspace:
  assumes "Cauchy_continuous_map m1 m2 f"
  shows "f \<in> mspace m1 \<rightarrow> mspace m2"
sorry

lemma Cauchy_continuous_map_eq:
   "\<lbrakk>\<And>x. x \<in> mspace m1 \<Longrightarrow> f x = g x; Cauchy_continuous_map m1 m2 f\<rbrakk>
      \<Longrightarrow> Cauchy_continuous_map m1 m2 g"
sorry

lemma Cauchy_continuous_map_from_submetric:
  assumes "Cauchy_continuous_map m1 m2 f"
  shows "Cauchy_continuous_map (submetric m1 S) m2 f"
sorry

lemma Cauchy_continuous_map_from_submetric_mono:
   "\<lbrakk>Cauchy_continuous_map (submetric m1 T) m2 f; S \<subseteq> T\<rbrakk>
           \<Longrightarrow> Cauchy_continuous_map (submetric m1 S) m2 f"
sorry

lemma Cauchy_continuous_map_into_submetric:
   "Cauchy_continuous_map m1 (submetric m2 S) f \<longleftrightarrow>
   f \<in> mspace m1 \<rightarrow> S \<and> Cauchy_continuous_map m1 m2 f"  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma Cauchy_continuous_map_const [simp]:
  "Cauchy_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow> mspace m1 = {} \<or> c \<in> mspace m2"
sorry

lemma Cauchy_continuous_map_id [simp]:
   "Cauchy_continuous_map m1 m1 (\<lambda>x. x)"
sorry

lemma Cauchy_continuous_map_compose:
  assumes f: "Cauchy_continuous_map m1 m2 f" and g: "Cauchy_continuous_map m2 m3 g"
  shows "Cauchy_continuous_map m1 m3 (g \<circ> f)"
sorry

lemma Lipschitz_imp_uniformly_continuous_map:
  assumes "Lipschitz_continuous_map m1 m2 f"
  shows "uniformly_continuous_map m1 m2 f"
sorry

lemma uniformly_imp_Cauchy_continuous_map:
   "uniformly_continuous_map m1 m2 f \<Longrightarrow> Cauchy_continuous_map m1 m2 f"
sorry

lemma locally_Cauchy_continuous_map:
  assumes "\<epsilon> > 0"
    and \<section>: "\<And>x. x \<in> mspace m1 \<Longrightarrow> Cauchy_continuous_map (submetric m1 (mball_of m1 x \<epsilon>)) m2 f"
  shows "Cauchy_continuous_map m1 m2 f"
sorry

context Metric_space12
begin

lemma Cauchy_continuous_imp_continuous_map:
  assumes "Cauchy_continuous_map (metric (M1,d1)) (metric (M2,d2)) f"
  shows "continuous_map M1.mtopology M2.mtopology f"
sorry

lemma continuous_imp_Cauchy_continuous_map:
  assumes "M1.mcomplete"
    and f: "continuous_map M1.mtopology M2.mtopology f"
  shows "Cauchy_continuous_map (metric (M1,d1)) (metric (M2,d2)) f"
sorry

end

text \<open>The same outside the locale\<close>
lemma Cauchy_continuous_imp_continuous_map:
  assumes "Cauchy_continuous_map m1 m2 f"
  shows "continuous_map (mtopology_of m1) (mtopology_of m2) f"
sorry

lemma continuous_imp_Cauchy_continuous_map:
  assumes "Metric_space.mcomplete (mspace m1) (mdist m1)"
    and "continuous_map (mtopology_of m1) (mtopology_of m2) f"
  shows "Cauchy_continuous_map m1 m2 f"
sorry

lemma uniformly_continuous_imp_continuous_map:
   "uniformly_continuous_map m1 m2 f
        \<Longrightarrow> continuous_map (mtopology_of m1) (mtopology_of m2) f"
sorry

lemma Lipschitz_continuous_imp_continuous_map:
   "Lipschitz_continuous_map m1 m2 f
     \<Longrightarrow> continuous_map (mtopology_of m1) (mtopology_of m2) f"
sorry

lemma Lipschitz_imp_Cauchy_continuous_map:
   "Lipschitz_continuous_map m1 m2 f
        \<Longrightarrow> Cauchy_continuous_map m1 m2 f"
sorry

lemma Cauchy_imp_uniformly_continuous_map:
  assumes f: "Cauchy_continuous_map m1 m2 f"
    and tbo: "Metric_space.mtotally_bounded (mspace m1) (mdist m1) (mspace m1)"
  shows "uniformly_continuous_map m1 m2 f"
sorry

lemma continuous_imp_uniformly_continuous_map:
   "compact_space (mtopology_of m1) \<and>
        continuous_map (mtopology_of m1) (mtopology_of m2) f
        \<Longrightarrow> uniformly_continuous_map m1 m2 f"
sorry

lemma continuous_eq_Cauchy_continuous_map:
   "Metric_space.mcomplete (mspace m1) (mdist m1) \<Longrightarrow> 
    continuous_map (mtopology_of m1) (mtopology_of m2) f \<longleftrightarrow> Cauchy_continuous_map m1 m2 f"
sorry

lemma continuous_eq_uniformly_continuous_map:
   "compact_space (mtopology_of m1) 
    \<Longrightarrow> continuous_map (mtopology_of m1) (mtopology_of m2) f \<longleftrightarrow>
        uniformly_continuous_map m1 m2 f"
sorry

lemma Cauchy_eq_uniformly_continuous_map:
   "Metric_space.mtotally_bounded (mspace m1) (mdist m1) (mspace m1)
    \<Longrightarrow> Cauchy_continuous_map m1 m2 f \<longleftrightarrow> uniformly_continuous_map m1 m2 f"
sorry

lemma Lipschitz_continuous_map_projections:
  "Lipschitz_continuous_map (prod_metric m1 m2) m1 fst"
  "Lipschitz_continuous_map (prod_metric m1 m2) m2 snd"
sorry

lemma Lipschitz_continuous_map_pairwise:
   "Lipschitz_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow>
    Lipschitz_continuous_map m m1 (fst \<circ> f) \<and> Lipschitz_continuous_map m m2 (snd \<circ> f)"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma uniformly_continuous_map_pairwise:
   "uniformly_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow> 
    uniformly_continuous_map m m1 (fst \<circ> f) \<and> uniformly_continuous_map m m2 (snd \<circ> f)"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma Cauchy_continuous_map_pairwise:
   "Cauchy_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow> Cauchy_continuous_map m m1 (fst \<circ> f) \<and> Cauchy_continuous_map m m2 (snd \<circ> f)"
sorry

lemma Lipschitz_continuous_map_paired:
   "Lipschitz_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        Lipschitz_continuous_map m m1 f \<and> Lipschitz_continuous_map m m2 g"
sorry

lemma uniformly_continuous_map_paired:
   "uniformly_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        uniformly_continuous_map m m1 f \<and> uniformly_continuous_map m m2 g"
sorry

lemma Cauchy_continuous_map_paired:
   "Cauchy_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        Cauchy_continuous_map m m1 f \<and> Cauchy_continuous_map m m2 g"
sorry

lemma mbounded_Lipschitz_continuous_image:
  assumes f: "Lipschitz_continuous_map m1 m2 f" and S: "Metric_space.mbounded (mspace m1) (mdist m1) S"
  shows "Metric_space.mbounded (mspace m2) (mdist m2) (f`S)"
sorry

lemma mtotally_bounded_Cauchy_continuous_image:
  assumes f: "Cauchy_continuous_map m1 m2 f" and S: "Metric_space.mtotally_bounded (mspace m1) (mdist m1) S"
  shows "Metric_space.mtotally_bounded (mspace m2) (mdist m2) (f ` S)"
sorry

lemma Lipschitz_coefficient_pos:
  assumes "x \<in> mspace m" "y \<in> mspace m" "f x \<noteq> f y" 
    and "f \<in> mspace m \<rightarrow> mspace m2" 
    and "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m\<rbrakk>
            \<Longrightarrow> mdist m2 (f x) (f y) \<le> k * mdist m x y"
  shows  "0 < k"
sorry

lemma Lipschitz_continuous_map_metric:
   "Lipschitz_continuous_map (prod_metric m m) euclidean_metric (\<lambda>(x,y). mdist m x y)"
sorry

lemma Lipschitz_continuous_map_mdist:
  assumes f: "Lipschitz_continuous_map m m' f" 
    and g: "Lipschitz_continuous_map m m' g"
  shows "Lipschitz_continuous_map m euclidean_metric (\<lambda>x. mdist m' (f x) (g x))"
    (is "Lipschitz_continuous_map m _ ?h")
sorry

lemma uniformly_continuous_map_mdist:
  assumes f: "uniformly_continuous_map m m' f" 
    and g: "uniformly_continuous_map m m' g"
  shows "uniformly_continuous_map m euclidean_metric (\<lambda>x. mdist m' (f x) (g x))"
    (is "uniformly_continuous_map m _ ?h")
sorry

lemma Cauchy_continuous_map_mdist:
  assumes f: "Cauchy_continuous_map m m' f" 
    and g: "Cauchy_continuous_map m m' g"
  shows "Cauchy_continuous_map m euclidean_metric (\<lambda>x. mdist m' (f x) (g x))"
    (is "Cauchy_continuous_map m _ ?h")
sorry

lemma mtopology_of_prod_metric [simp]:
    "mtopology_of (prod_metric m1 m2) = prod_topology (mtopology_of m1) (mtopology_of m2)"
sorry

lemma continuous_map_metric:
   "continuous_map (prod_topology (mtopology_of m) (mtopology_of m)) euclidean
      (\<lambda>(x,y). mdist m x y)"
sorry

lemma continuous_map_mdist_alt:
  assumes "continuous_map X (prod_topology (mtopology_of m) (mtopology_of m)) f"
  shows "continuous_map X euclidean (\<lambda>x. case_prod (mdist m) (f x))"
    (is "continuous_map _ _ ?h")
sorry

lemma continuous_map_mdist [continuous_intros]:
  assumes f: "continuous_map X (mtopology_of m) f" 
      and g: "continuous_map X (mtopology_of m) g"
  shows "continuous_map X euclidean (\<lambda>x. mdist m (f x) (g x))"
    (is "continuous_map X _ ?h")
sorry

lemma continuous_on_mdist:
   "a \<in> mspace m \<Longrightarrow> continuous_map (mtopology_of m) euclidean (mdist m a)"
sorry

subsection \<open>Isometries\<close>

lemma (in Metric_space12) isometry_imp_embedding_map:
  assumes fim: "f \<in> M1 \<rightarrow> M2" and d: "\<And>x y. \<lbrakk>x \<in> M1; y \<in> M1\<rbrakk> \<Longrightarrow> d2 (f x) (f y) = d1 x y"
  shows "embedding_map M1.mtopology M2.mtopology f"
sorry

lemma (in Metric_space12) isometry_imp_homeomorphic_map:
  assumes fim: "f ` M1 = M2" and d: "\<And>x y. \<lbrakk>x \<in> M1; y \<in> M1\<rbrakk> \<Longrightarrow> d2 (f x) (f y) = d1 x y"
  shows "homeomorphic_map M1.mtopology M2.mtopology f"
sorry

subsection\<open>"Capped" equivalent bounded metrics and general product metrics\<close>

definition (in Metric_space) capped_dist where
  "capped_dist \<equiv> \<lambda>\<delta> x y. if \<delta> > 0 then min \<delta> (d x y) else d x y"

lemma (in Metric_space) capped_dist: "Metric_space M (capped_dist \<delta>)"
sorry


definition capped_metric where
  "capped_metric \<delta> m \<equiv> metric(mspace m, Metric_space.capped_dist (mdist m) \<delta>)"

lemma capped_metric:
  "capped_metric \<delta> m = (if \<delta> \<le> 0 then m else metric(mspace m, \<lambda>x y. min \<delta> (mdist m x y)))"
sorry

lemma capped_metric_mspace [simp]:
  "mspace (capped_metric \<delta> m) = mspace m"
sorry

lemma capped_metric_mdist:
  "mdist (capped_metric \<delta> m) = (\<lambda>x y. if \<delta> \<le> 0 then mdist m x y else min \<delta> (mdist m x y))"
sorry

lemma mdist_capped_le: "mdist (capped_metric \<delta> m) x y \<le> mdist m x y"
sorry

lemma mdist_capped: "\<delta> > 0 \<Longrightarrow> mdist (capped_metric \<delta> m) x y \<le> \<delta>"
sorry

lemma mball_of_capped_metric [simp]: 
  assumes "x \<in> mspace m" "r > \<delta>" "\<delta> > 0" 
  shows "mball_of (capped_metric \<delta> m) x r = mspace m"
sorry

lemma Metric_space_capped_dist[simp]:
  "Metric_space (mspace m) (Metric_space.capped_dist (mdist m) \<delta>)"
sorry

lemma mtopology_capped_metric:
  "mtopology_of(capped_metric \<delta> m) = mtopology_of m"
sorry

text \<open>Might have been easier to prove this within the locale to start with (using Self)\<close>
lemma (in Metric_space) mtopology_capped_metric:
  "Metric_space.mtopology M (capped_dist \<delta>) = mtopology"
sorry

lemma (in Metric_space) MCauchy_capped_metric:
  "Metric_space.MCauchy M (capped_dist \<delta>) \<sigma> \<longleftrightarrow> MCauchy \<sigma>"
sorry

lemma (in Metric_space) mcomplete_capped_metric:
   "Metric_space.mcomplete M (capped_dist \<delta>) \<longleftrightarrow> mcomplete"
sorry

lemma bounded_equivalent_metric:
  assumes "\<delta> > 0"
  obtains m' where "mspace m' = mspace m" "mtopology_of m' = mtopology_of m" "\<And>x y. mdist m' x y < \<delta>"
sorry

text \<open>A technical lemma needed below\<close>
lemma Sup_metric_cartesian_product:
  fixes I m
  defines "S \<equiv> PiE I (mspace \<circ> m)"
  defines "D \<equiv> \<lambda>x y. if x \<in> S \<and> y \<in> S then SUP i\<in>I. mdist (m i) (x i) (y i) else 0"
  defines "m' \<equiv> metric(S,D)"
  assumes "I \<noteq> {}"
    and c: "\<And>i x y. \<lbrakk>i \<in> I; x \<in> mspace(m i); y \<in> mspace(m i)\<rbrakk> \<Longrightarrow> mdist (m i) x y \<le> c"
  shows "Metric_space S D" 
    and "\<forall>x \<in> S. \<forall>y \<in> S. \<forall>b. D x y \<le> b \<longleftrightarrow> (\<forall>i \<in> I. mdist (m i) (x i) (y i) \<le> b)"  (is "?the2")
sorry

lemma metrizable_topology_A:
  assumes "metrizable_space (product_topology X I)"
  shows "(product_topology X I) = trivial_topology \<or> (\<forall>i \<in> I. metrizable_space (X i))"
sorry

lemma metrizable_topology_C:
  assumes "completely_metrizable_space (product_topology X I)"
  shows "(product_topology X I) = trivial_topology \<or> (\<forall>i \<in> I. completely_metrizable_space (X i))"
sorry

lemma metrizable_topology_B:
  fixes a X I
  defines "L \<equiv> {i \<in> I. \<nexists>a. topspace (X i) \<subseteq> {a}}"
  assumes "topspace (product_topology X I) \<noteq> {}"
    and met: "metrizable_space (product_topology X I)"
    and "\<And>i. i \<in> I \<Longrightarrow> metrizable_space (X i)"
  shows  "countable L"
sorry

lemma metrizable_topology_DD:
  assumes "topspace (product_topology X I) \<noteq> {}"
    and co: "countable {i \<in> I. \<nexists>a. topspace (X i) \<subseteq> {a}}"
    and m: "\<And>i. i \<in> I \<Longrightarrow> X i = mtopology_of (m i)"
  obtains M d where "Metric_space M d" "product_topology X I = Metric_space.mtopology M d"
                    "(\<And>i. i \<in> I \<Longrightarrow> mcomplete_of (m i)) \<Longrightarrow> Metric_space.mcomplete M d"
sorry

lemma metrizable_topology_D:
  assumes "topspace (product_topology X I) \<noteq> {}"
    and co: "countable {i \<in> I. \<nexists>a. topspace (X i) \<subseteq> {a}}"
    and met: "\<And>i. i \<in> I \<Longrightarrow> metrizable_space (X i)"
  shows "metrizable_space (product_topology X I)"
sorry

lemma metrizable_topology_E:
  assumes "topspace (product_topology X I) \<noteq> {}"
    and "countable {i \<in> I. \<nexists>a. topspace (X i) \<subseteq> {a}}"
    and met: "\<And>i. i \<in> I \<Longrightarrow> completely_metrizable_space (X i)"
  shows "completely_metrizable_space (product_topology X I)"
sorry

proposition metrizable_space_product_topology:
  "metrizable_space (product_topology X I) \<longleftrightarrow>
        (product_topology X I) = trivial_topology \<or>
        countable {i \<in> I. \<not> (\<exists>a. topspace(X i) \<subseteq> {a})} \<and>
        (\<forall>i \<in> I. metrizable_space (X i))"
sorry

proposition completely_metrizable_space_product_topology:
  "completely_metrizable_space (product_topology X I) \<longleftrightarrow>
        (product_topology X I) = trivial_topology \<or>
        countable {i \<in> I. \<not> (\<exists>a. topspace(X i) \<subseteq> {a})} \<and>
        (\<forall>i \<in> I. completely_metrizable_space (X i))"
sorry

lemma completely_metrizable_Euclidean_space:
  "completely_metrizable_space(Euclidean_space n)"
sorry

lemma metrizable_Euclidean_space:
   "metrizable_space(Euclidean_space n)"
sorry

lemma locally_connected_Euclidean_space:
   "locally_connected_space(Euclidean_space n)"
sorry
end
