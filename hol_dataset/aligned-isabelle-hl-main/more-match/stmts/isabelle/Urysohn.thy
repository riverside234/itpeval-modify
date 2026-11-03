(*  Title:      HOL/Analysis/Urysohn.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>The Urysohn lemma, its consequences and other advanced material about metric spaces\<close>

theory Urysohn
imports Abstract_Topological_Spaces Abstract_Metric_Spaces Infinite_Sum Arcwise_Connected
begin

subsection \<open>Urysohn lemma and Tietze's theorem\<close>

proposition Urysohn_lemma:
  fixes a b :: real
  assumes "normal_space X" "closedin X S" "closedin X T" "disjnt S T" "a \<le> b" 
  obtains f where "continuous_map X (top_of_set {a..b}) f" "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
sorry

lemma Urysohn_lemma_alt:
  fixes a b :: real
  assumes "normal_space X" "closedin X S" "closedin X T" "disjnt S T"
  obtains f where "continuous_map X euclideanreal f" "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
sorry

lemma normal_space_iff_Urysohn_gen_alt:
  assumes "a \<noteq> b"
  shows "normal_space X \<longleftrightarrow>
         (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
                \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f ` S \<subseteq> {a} \<and> f ` T \<subseteq> {b}))"
 (is "?lhs=?rhs")
sorry

lemma normal_space_iff_Urysohn_gen:
  fixes a b::real
  shows
   "a < b \<Longrightarrow> 
      normal_space X \<longleftrightarrow>
        (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
               \<longrightarrow> (\<exists>f. continuous_map X (top_of_set {a..b}) f \<and>
                        f ` S \<subseteq> {a} \<and> f ` T \<subseteq> {b}))"
sorry

lemma normal_space_iff_Urysohn_alt:
   "normal_space X \<longleftrightarrow>
     (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and>
                   f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}))"
sorry

lemma normal_space_iff_Urysohn:
   "normal_space X \<longleftrightarrow>
     (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
            \<longrightarrow> (\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and> 
                               f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}))"
sorry

lemma normal_space_perfect_map_image:
   "\<lbrakk>normal_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> normal_space Y"
sorry

lemma Hausdorff_normal_space_closed_continuous_map_image:
   "\<lbrakk>normal_space X; closed_map X Y f; continuous_map X Y f;
     f ` topspace X = topspace Y; t1_space Y\<rbrakk>
    \<Longrightarrow> Hausdorff_space Y"
sorry

lemma normal_Hausdorff_space_closed_continuous_map_image:
   "\<lbrakk>normal_space X; Hausdorff_space X; closed_map X Y f;
     continuous_map X Y f; f ` topspace X = topspace Y\<rbrakk>
    \<Longrightarrow> normal_space Y \<and> Hausdorff_space Y"
sorry

lemma Lindelof_cover:
  assumes "regular_space X" and "Lindelof_space X" and "S \<noteq> {}" 
    and clo: "closedin X S" "closedin X T" "disjnt S T"
  obtains h :: "nat \<Rightarrow> 'a set" where 
    "\<And>n. openin X (h n)" "\<And>n. disjnt T (X closure_of (h n))" and  "S \<subseteq> \<Union>(range h)"
sorry

lemma regular_Lindelof_imp_normal_space:
  assumes "regular_space X" and "Lindelof_space X"
  shows "normal_space X"
sorry

theorem Tietze_extension_closed_real_interval:
  assumes "normal_space X" and "closedin X S"
    and contf: "continuous_map (subtopology X S) euclideanreal f"
    and fim: "f ` S \<subseteq> {a..b}" and "a \<le> b"
  obtains g 
  where "continuous_map X euclideanreal g" 
        "\<And>x. x \<in> S \<Longrightarrow> g x = f x" "g ` topspace X \<subseteq> {a..b}"
sorry

theorem Tietze_extension_realinterval:
  assumes XS: "normal_space X" "closedin X S" and T: "is_interval T" "T \<noteq> {}" 
    and contf: "continuous_map (subtopology X S) euclideanreal f" 
    and "f ` S \<subseteq> T"
  obtains g where "continuous_map X euclideanreal g"  "g ` topspace X \<subseteq> T"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma normal_space_iff_Tietze:
   "normal_space X \<longleftrightarrow>
    (\<forall>f S. closedin X S \<and>
           continuous_map (subtopology X S) euclidean f
           \<longrightarrow> (\<exists>g:: 'a \<Rightarrow> real. continuous_map X euclidean g \<and> (\<forall>x \<in> S. g x = f x)))" 
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

subsection \<open>Random metric space stuff\<close>

lemma metrizable_imp_k_space:
  assumes "metrizable_space X"
  shows "k_space X"
sorry

lemma (in Metric_space) k_space_mtopology: "k_space mtopology"
sorry

lemma k_space_euclideanreal: "k_space (euclidean :: 'a::metric_space topology)"
sorry

subsection\<open>Hereditarily normal spaces\<close>

lemma hereditarily_B:
  assumes "\<And>S T. separatedin X S T
      \<Longrightarrow> \<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  shows "hereditarily normal_space X"
sorry

lemma hereditarily_C: 
  assumes "separatedin X S T" and norm: "\<And>U. openin X U \<Longrightarrow> normal_space (subtopology X U)"
  shows "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
sorry

lemma hereditarily_normal_space: 
  "hereditarily normal_space X \<longleftrightarrow> (\<forall>U. openin X U \<longrightarrow> normal_space(subtopology X U))"
sorry

lemma hereditarily_normal_separation:
  "hereditarily normal_space X \<longleftrightarrow>
        (\<forall>S T. separatedin X S T
             \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))"
sorry

lemma metrizable_imp_hereditarily_normal_space:
   "metrizable_space X \<Longrightarrow> hereditarily normal_space X"
sorry

lemma metrizable_space_separation:
   "\<lbrakk>metrizable_space X; separatedin X S T\<rbrakk>
    \<Longrightarrow> \<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
sorry

lemma hereditarily_normal_separation_pairwise:
   "hereditarily normal_space X \<longleftrightarrow>
    (\<forall>\<U>. finite \<U> \<and> (\<forall>S \<in> \<U>. S \<subseteq> topspace X) \<and> pairwise (separatedin X) \<U>
        \<longrightarrow> (\<exists>\<F>. (\<forall>S \<in> \<U>. openin X (\<F> S) \<and> S \<subseteq> \<F> S) \<and>
                pairwise (\<lambda>S T. disjnt (\<F> S) (\<F> T)) \<U>))"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma hereditarily_normal_space_perfect_map_image:
   "\<lbrakk>hereditarily normal_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> hereditarily normal_space Y"
sorry

lemma regular_second_countable_imp_hereditarily_normal_space:
  assumes "regular_space X \<and> second_countable X"
  shows  "hereditarily normal_space X"
sorry

subsection\<open>Completely regular spaces\<close>

definition completely_regular_space where
 "completely_regular_space X \<equiv>
    \<forall>S x. closedin X S \<and> x \<in> topspace X - S
          \<longrightarrow> (\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and>
                  f x = 0 \<and> (f ` S \<subseteq> {1}))"

lemma homeomorphic_completely_regular_space_aux:
  assumes X: "completely_regular_space X" and hom: "X homeomorphic_space Y"
  shows "completely_regular_space Y"
sorry

lemma homeomorphic_completely_regular_space:
  assumes "X homeomorphic_space Y"
  shows "completely_regular_space X \<longleftrightarrow> completely_regular_space Y"
sorry

lemma completely_regular_space_alt:
   "completely_regular_space X \<longleftrightarrow>
     (\<forall>S x. closedin X S \<longrightarrow> x \<in> topspace X - S
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}))"
sorry


text \<open>As above, but with @{term openin}\<close>
lemma completely_regular_space_alt':
   "completely_regular_space X \<longleftrightarrow>
     (\<forall>S x. openin X S \<longrightarrow> x \<in> S
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` (topspace X - S) \<subseteq> {1}))"
sorry

lemma completely_regular_space_gen_alt:
  fixes a b::real
  assumes "a \<noteq> b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. closedin X S \<longrightarrow> x \<in> topspace X - S
               \<longrightarrow> (\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> (f ` S \<subseteq> {b})))"
sorry

text \<open>As above, but with @{term openin}\<close>
lemma completely_regular_space_gen_alt':
  fixes a b::real
  assumes "a \<noteq> b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. openin X S \<longrightarrow> x \<in> S
               \<longrightarrow> (\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> (f ` (topspace X - S) \<subseteq> {b})))"
sorry

lemma completely_regular_space_gen:
  fixes a b::real
  assumes "a < b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. closedin X S \<and> x \<in> topspace X - S
               \<longrightarrow> (\<exists>f. continuous_map X (top_of_set {a..b}) f \<and> f x = a \<and> f ` S \<subseteq> {b}))"
sorry

lemma normal_imp_completely_regular_space_A:
  assumes "normal_space X" "t1_space X"
  shows "completely_regular_space X"
sorry

lemma normal_imp_completely_regular_space_B:
  assumes "normal_space X" "regular_space X"
  shows "completely_regular_space X"
sorry

lemma normal_imp_completely_regular_space_gen:
   "\<lbrakk>normal_space X; t1_space X \<or> Hausdorff_space X \<or> regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space X"
sorry

lemma normal_imp_completely_regular_space:
   "\<lbrakk>normal_space X; Hausdorff_space X \<or> regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space X"
sorry

lemma (in Metric_space) completely_regular_space_mtopology:
   "completely_regular_space mtopology"
sorry

lemma metrizable_imp_completely_regular_space:
   "metrizable_space X \<Longrightarrow> completely_regular_space X"
sorry

lemma completely_regular_space_discrete_topology:
   "completely_regular_space(discrete_topology U)"
sorry

lemma completely_regular_space_subtopology:
  assumes "completely_regular_space X"
  shows "completely_regular_space (subtopology X S)"
sorry

lemma completely_regular_space_retraction_map_image:
   " \<lbrakk>retraction_map X Y r; completely_regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space Y"
sorry

lemma completely_regular_imp_regular_space:
  assumes "completely_regular_space X" 
  shows "regular_space X"
sorry

proposition locally_compact_regular_imp_completely_regular_space:
  assumes "locally_compact_space X" "Hausdorff_space X \<or> regular_space X"
  shows "completely_regular_space X"
sorry

lemma completely_regular_eq_regular_space:
   "locally_compact_space X
        \<Longrightarrow> (completely_regular_space X \<longleftrightarrow> regular_space X)"
sorry

lemma completely_regular_space_prod_topology:
   "completely_regular_space (prod_topology X Y) \<longleftrightarrow>
      (prod_topology X Y) = trivial_topology \<or>
      completely_regular_space X \<and> completely_regular_space Y" (is "?lhs=?rhs")
sorry

proposition completely_regular_space_product_topology:
   "completely_regular_space (product_topology X I) \<longleftrightarrow>
    (\<exists>i\<in>I. X i = trivial_topology) \<or> (\<forall>i \<in> I. completely_regular_space (X i))" 
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma zero_dimensional_imp_completely_regular_space:
  assumes "X dim_le 0" 
  shows "completely_regular_space X"
sorry

lemma zero_dimensional_imp_regular_space: "X dim_le 0 \<Longrightarrow> regular_space X"
sorry

lemma (in Metric_space) t1_space_mtopology:
   "t1_space mtopology"
sorry

subsection\<open>More generally, the k-ification functor\<close>

definition kification_open 
  where "kification_open \<equiv> 
          \<lambda>X S. S \<subseteq> topspace X \<and> (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S))"

definition kification 
  where "kification X \<equiv> topology (kification_open X)"

lemma istopology_kification_open: "istopology (kification_open X)"
sorry

lemma openin_kification:
   "openin (kification X) U \<longleftrightarrow>
        U \<subseteq> topspace X \<and>
        (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> U))"
sorry

lemma openin_kification_finer:
   "openin X S \<Longrightarrow> openin (kification X) S"
sorry

lemma topspace_kification [simp]:
   "topspace(kification X) = topspace X"
sorry

lemma closedin_kification:
   "closedin (kification X) U \<longleftrightarrow>
      U \<subseteq> topspace X \<and>
      (\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> U))"
sorry

lemma closedin_kification_finer: "closedin X S \<Longrightarrow> closedin (kification X) S"
sorry

lemma kification_eq_self: "kification X = X \<longleftrightarrow> k_space X"
sorry

lemma compactin_kification [simp]:
   "compactin (kification X) K \<longleftrightarrow> compactin X K" (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma compact_space_kification [simp]:
   "compact_space(kification X) \<longleftrightarrow> compact_space X"
sorry

lemma kification_kification [simp]:
   "kification(kification X) = kification X"
sorry

lemma k_space_kification [iff]: "k_space(kification X)"
sorry

lemma continuous_map_into_kification:
  assumes "k_space X"
  shows "continuous_map X (kification Y) f \<longleftrightarrow> continuous_map X Y f" (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma continuous_map_from_kification:
   "continuous_map X Y f \<Longrightarrow> continuous_map (kification X) Y f"
sorry

lemma continuous_map_kification:
   "continuous_map X Y f \<Longrightarrow> continuous_map (kification X) (kification Y) f"
sorry

lemma subtopology_kification_compact:
  assumes "compactin X K"
  shows "subtopology (kification X) K = subtopology X K"
sorry

lemma subtopology_kification_finer:
  assumes "openin (subtopology (kification X) S) U"
  shows "openin (kification (subtopology X S)) U"
sorry

lemma proper_map_from_kification:
  assumes "k_space Y"
  shows "proper_map (kification X) Y f \<longleftrightarrow> proper_map X Y f"   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma perfect_map_from_kification:
   "\<lbrakk>k_space Y; perfect_map X Y f\<rbrakk> \<Longrightarrow> perfect_map(kification X) Y f"
sorry

lemma k_space_perfect_map_image_eq:
  assumes "Hausdorff_space X" "perfect_map X Y f"
  shows "k_space X \<longleftrightarrow> k_space Y"
sorry


subsection\<open>One-point compactifications and the Alexandroff extension construction\<close>

lemma one_point_compactification_dense:
   "\<lbrakk>compact_space X; \<not> compactin X (topspace X - {a})\<rbrakk> \<Longrightarrow> X closure_of (topspace X - {a}) = topspace X"
sorry

lemma one_point_compactification_interior:
   "\<lbrakk>compact_space X; \<not> compactin X (topspace X - {a})\<rbrakk> \<Longrightarrow> X interior_of {a} = {}"
sorry

proposition kc_space_one_point_compactification_gen:
  assumes "compact_space X"
  shows "kc_space X \<longleftrightarrow>
         openin X (topspace X - {a}) \<and> (\<forall>K. compactin X K \<and> a\<notin>K \<longrightarrow> closedin X K) \<and>
         k_space (subtopology X (topspace X - {a})) \<and> kc_space (subtopology X (topspace X - {a}))"
 (is "?lhs \<longleftrightarrow> ?rhs")
sorry

  
inductive Alexandroff_open for X where
  base: "openin X U \<Longrightarrow> Alexandroff_open X (Some ` U)"
| ext: "\<lbrakk>compactin X C; closedin X C\<rbrakk> \<Longrightarrow> Alexandroff_open X (insert None (Some ` (topspace X - C)))"

hide_fact (open) base ext

lemma Alexandroff_open_iff: "Alexandroff_open X S \<longleftrightarrow>
   (\<exists>U. (S = Some ` U \<and> openin X U) \<or> (S = insert None (Some ` (topspace X - U)) \<and> compactin X U \<and> closedin X U))"
sorry

lemma Alexandroff_open_Un_aux:
  assumes U: "openin X U" and "Alexandroff_open X T"
  shows  "Alexandroff_open X (Some ` U \<union> T)"
sorry

lemma Alexandroff_open_Un:
  assumes "Alexandroff_open X S" and "Alexandroff_open X T"
  shows "Alexandroff_open X (S \<union> T)"
sorry

lemma Alexandroff_open_Int_aux:
  assumes U: "openin X U" and "Alexandroff_open X T"
  shows  "Alexandroff_open X (Some ` U \<inter> T)"
sorry

proposition istopology_Alexandroff_open: "istopology (Alexandroff_open X)"
sorry

definition Alexandroff_compactification where
  "Alexandroff_compactification X \<equiv> topology (Alexandroff_open X)"

lemma openin_Alexandroff_compactification:
   "openin(Alexandroff_compactification X) V \<longleftrightarrow>
        (\<exists>U. openin X U \<and> V = Some ` U) \<or>
        (\<exists>C. compactin X C \<and> closedin X C \<and> V = insert None (Some ` (topspace X - C)))"
sorry

lemma topspace_Alexandroff_compactification [simp]:
   "topspace(Alexandroff_compactification X) = insert None (Some ` topspace X)"
   (is "?lhs = ?rhs")
sorry

lemma closedin_Alexandroff_compactification:
   "closedin (Alexandroff_compactification X) C \<longleftrightarrow>
      (\<exists>K. compactin X K \<and> closedin X K \<and> C = Some ` K) \<or>
      (\<exists>U. openin X U \<and> C = topspace(Alexandroff_compactification X) - Some ` U)"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma openin_Alexandroff_compactification_image_Some [simp]:
   "openin(Alexandroff_compactification X) (Some ` U) \<longleftrightarrow> openin X U"
sorry

lemma closedin_Alexandroff_compactification_image_Some [simp]:
   "closedin (Alexandroff_compactification X) (Some ` K) \<longleftrightarrow> compactin X K \<and> closedin X K"
sorry

lemma open_map_Some: "open_map X (Alexandroff_compactification X) Some"
sorry

lemma continuous_map_Some: "continuous_map X (Alexandroff_compactification X) Some"
sorry

lemma embedding_map_Some: "embedding_map X (Alexandroff_compactification X) Some"
sorry

lemma compact_space_Alexandroff_compactification [simp]:
   "compact_space(Alexandroff_compactification X)"
sorry

lemma topspace_Alexandroff_compactification_delete:
   "topspace(Alexandroff_compactification X) - {None} = Some ` topspace X"
sorry

lemma Alexandroff_compactification_dense:
  assumes "\<not> compact_space X"
  shows "(Alexandroff_compactification X) closure_of (Some ` topspace X) =
         topspace(Alexandroff_compactification X)"
sorry

lemma t0_space_one_point_compactification:
  assumes "compact_space X \<and> openin X (topspace X - {a})"
  shows "t0_space X \<longleftrightarrow> t0_space (subtopology X (topspace X - {a}))"
   (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma t0_space_Alexandroff_compactification [simp]:
   "t0_space (Alexandroff_compactification X) \<longleftrightarrow> t0_space X"
sorry

lemma t1_space_one_point_compactification:
  assumes Xa: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "t1_space X \<longleftrightarrow> t1_space (subtopology X (topspace X - {a}))"  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma closedin_Alexandroff_I: 
  assumes "compactin (Alexandroff_compactification X) K" "K \<subseteq> Some ` topspace X"
          "closedin (Alexandroff_compactification X) T" "K = T \<inter> Some ` topspace X"
  shows "closedin (Alexandroff_compactification X) K"
sorry

lemma t1_space_Alexandroff_compactification [simp]:
  "t1_space(Alexandroff_compactification X) \<longleftrightarrow> t1_space X"
sorry

lemma kc_space_one_point_compactification:
  assumes "compact_space X"
    and ope: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk>
                \<Longrightarrow> closedin X K"
  shows "kc_space X \<longleftrightarrow>
         k_space (subtopology X (topspace X - {a})) \<and> kc_space (subtopology X (topspace X - {a}))"
sorry

lemma kc_space_Alexandroff_compactification:
  "kc_space(Alexandroff_compactification X) \<longleftrightarrow> (k_space X \<and> kc_space X)" (is "kc_space ?Y = _")
sorry

proposition regular_space_one_point_compactification:
  assumes "compact_space X" and ope: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "regular_space X \<longleftrightarrow>
           regular_space (subtopology X (topspace X - {a})) \<and> locally_compact_space (subtopology X (topspace X - {a}))" 
    (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma regular_space_Alexandroff_compactification:
  "regular_space(Alexandroff_compactification X) \<longleftrightarrow> regular_space X \<and> locally_compact_space X" 
  (is "regular_space ?Y = ?rhs")
sorry

lemma Hausdorff_space_one_point_compactification:
  assumes "compact_space X" and  "openin X (topspace X - {a})"
    and "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "Hausdorff_space X \<longleftrightarrow>
           Hausdorff_space (subtopology X (topspace X - {a})) \<and> locally_compact_space (subtopology X (topspace X - {a}))" 
    (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma Hausdorff_space_Alexandroff_compactification:
   "Hausdorff_space(Alexandroff_compactification X) \<longleftrightarrow> Hausdorff_space X \<and> locally_compact_space X"
sorry

lemma completely_regular_space_Alexandroff_compactification:
   "completely_regular_space(Alexandroff_compactification X) \<longleftrightarrow>
        completely_regular_space X \<and> locally_compact_space X"
sorry

proposition Hausdorff_space_one_point_compactification_asymmetric_prod:
  assumes "compact_space X"
  shows "Hausdorff_space X \<longleftrightarrow>
         kc_space (prod_topology X (subtopology X (topspace X - {a}))) \<and>
         k_space (prod_topology X (subtopology X (topspace X - {a})))"  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma Hausdorff_space_Alexandroff_compactification_asymmetric_prod:
   "Hausdorff_space(Alexandroff_compactification X) \<longleftrightarrow>
        kc_space(prod_topology (Alexandroff_compactification X) X) \<and>
        k_space(prod_topology (Alexandroff_compactification X) X)"
    (is "Hausdorff_space ?Y = ?rhs")
sorry

lemma kc_space_as_compactification_unique:
  assumes "kc_space X" "compact_space X"
  shows "openin X U \<longleftrightarrow>
         (if a \<in> U then U \<subseteq> topspace X \<and> compactin X (topspace X - U)
                   else openin (subtopology X (topspace X - {a})) U)"
sorry

lemma kc_space_as_compactification_unique_explicit:
  assumes "kc_space X" "compact_space X"
  shows "openin X U \<longleftrightarrow>
         (if a \<in> U then U \<subseteq> topspace X \<and>
                     compactin (subtopology X (topspace X - {a})) (topspace X - U) \<and>
                     closedin (subtopology X (topspace X - {a})) (topspace X - U)
                else openin (subtopology X (topspace X - {a})) U)"
sorry

lemma Alexandroff_compactification_unique:
  assumes "kc_space X" "compact_space X" and a: "a \<in> topspace X"
  shows "Alexandroff_compactification (subtopology X (topspace X - {a})) homeomorphic_space X"
        (is "?Y homeomorphic_space X")
sorry


subsection\<open>Extending continuous maps "pointwise" in a regular space\<close>

lemma continuous_map_on_intermediate_closure_of:
  assumes Y: "regular_space Y" 
    and T: "T \<subseteq> X closure_of S" 
    and f: "\<And>t. t \<in> T \<Longrightarrow> limitin Y f (f t) (atin_within X t S)"
  shows "continuous_map (subtopology X T) Y f"
sorry

lemma continuous_map_on_intermediate_closure_of_eq:
  assumes "regular_space Y" "S \<subseteq> T" and Tsub: "T \<subseteq> X closure_of S"
  shows "continuous_map (subtopology X T) Y f \<longleftrightarrow> (\<forall>t \<in> T. limitin Y f (f t) (atin_within X t S))"
        (is "?lhs \<longleftrightarrow> ?rhs")
sorry

lemma continuous_map_extension_pointwise_alt:
  assumes \<section>: "regular_space Y" "S \<subseteq> T" "T \<subseteq> X closure_of S"
    and f: "continuous_map (subtopology X S) Y f"
    and lim: "\<And>t. t \<in> T-S \<Longrightarrow> \<exists>l. limitin Y f l (atin_within X t S)"
  obtains g where "continuous_map (subtopology X T) Y g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma continuous_map_extension_pointwise:
  assumes "regular_space Y" "S \<subseteq> T" and Tsub: "T \<subseteq> X closure_of S"
    and ex: " \<And>x. x \<in> T \<Longrightarrow> \<exists>g. continuous_map (subtopology X (insert x S)) Y g \<and>
                     (\<forall>x \<in> S. g x = f x)"
  obtains g where "continuous_map (subtopology X T) Y g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry


subsection\<open>Extending Cauchy continuous functions to the closure\<close>

lemma Cauchy_continuous_map_extends_to_continuous_closure_of_aux:
  assumes m2: "mcomplete_of m2" and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> mspace m1"
  obtains g 
  where "continuous_map (subtopology (mtopology_of m1) (mtopology_of m1 closure_of S)) 
                        (mtopology_of m2) g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma Cauchy_continuous_map_extends_to_continuous_closure_of:
  assumes "mcomplete_of m2" 
    and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "continuous_map (subtopology (mtopology_of m1) ((mtopology_of m1) closure_of S)) 
                        (mtopology_of m2) g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma Cauchy_continuous_map_extends_to_continuous_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
    and T: "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) g" 
         "(\<forall>x \<in> S. g x = f x)"
sorry

text \<open>Technical lemma helpful for porting particularly ugly HOL Light proofs\<close>
lemma all_in_closure_of:
  assumes P: "\<forall>x \<in> S. P x" and clo: "closedin X {x \<in> topspace X. P x}"
  shows "\<forall>x \<in> X closure_of S. P x"
sorry

lemma Lipschitz_continuous_map_on_intermediate_closure_aux:
  assumes lcf: "Lipschitz_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and Tsub: "T \<subseteq> (mtopology_of m1) closure_of S"
    and cmf: "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
    and "S \<subseteq> mspace m1"
  shows "Lipschitz_continuous_map (submetric m1 T) m2 f"
sorry

lemma Lipschitz_continuous_map_on_intermediate_closure:
  assumes "Lipschitz_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" "T \<subseteq> (mtopology_of m1) closure_of S"
    and "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
  shows "Lipschitz_continuous_map (submetric m1 T) m2 f"
sorry

lemma Lipschitz_continuous_map_extends_to_closure_of:
  assumes m2: "mcomplete_of m2" 
    and f: "Lipschitz_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "Lipschitz_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma Lipschitz_continuous_map_extends_to_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and "Lipschitz_continuous_map (submetric m1 S) m2 f"
    and "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "Lipschitz_continuous_map (submetric m1 T) m2 g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

text \<open>This proof uses the same trick to extend the function's domain to its closure\<close>
lemma uniformly_continuous_map_on_intermediate_closure_aux:
  assumes ucf: "uniformly_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and Tsub: "T \<subseteq> (mtopology_of m1) closure_of S"
    and cmf: "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
    and "S \<subseteq> mspace m1"
  shows "uniformly_continuous_map (submetric m1 T) m2 f"
sorry

lemma uniformly_continuous_map_on_intermediate_closure:
  assumes "uniformly_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and"T \<subseteq> (mtopology_of m1) closure_of S"
    and "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
  shows "uniformly_continuous_map (submetric m1 T) m2 f"
sorry

lemma uniformly_continuous_map_extends_to_closure_of:
  assumes m2: "mcomplete_of m2" 
    and f: "uniformly_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "uniformly_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma uniformly_continuous_map_extends_to_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and "uniformly_continuous_map (submetric m1 S) m2 f"
    and "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "uniformly_continuous_map (submetric m1 T) m2 g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma Cauchy_continuous_map_on_intermediate_closure_aux:
  assumes ucf: "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and Tsub: "T \<subseteq> (mtopology_of m1) closure_of S"
    and cmf: "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
    and "S \<subseteq> mspace m1"
  shows "Cauchy_continuous_map (submetric m1 T) m2 f"
sorry

lemma Cauchy_continuous_map_on_intermediate_closure:
  assumes "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "S \<subseteq> T" and "T \<subseteq> (mtopology_of m1) closure_of S"
    and "continuous_map (subtopology (mtopology_of m1) T) (mtopology_of m2) f"
  shows "Cauchy_continuous_map (submetric m1 T) m2 f"
sorry

lemma Cauchy_continuous_map_extends_to_closure_of:
  assumes m2: "mcomplete_of m2" 
    and f: "Cauchy_continuous_map (submetric m1 S) m2 f"
  obtains g 
  where "Cauchy_continuous_map (submetric m1 (mtopology_of m1 closure_of S)) m2 g" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma Cauchy_continuous_map_extends_to_intermediate_closure_of:
  assumes "mcomplete_of m2" 
    and "Cauchy_continuous_map (submetric m1 S) m2 f"
    and "T \<subseteq> mtopology_of m1 closure_of S"
  obtains g 
  where "Cauchy_continuous_map (submetric m1 T) m2 g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry
subsection\<open>Metric space of bounded functions\<close>

context Metric_space
begin

definition fspace :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) set" where 
  "fspace \<equiv> \<lambda>S. {f. f`S \<subseteq> M \<and> f \<in> extensional S \<and> mbounded (f`S)}"

definition fdist :: "['b set, 'b \<Rightarrow> 'a, 'b \<Rightarrow> 'a] \<Rightarrow> real" where 
  "fdist \<equiv> \<lambda>S f g. if f \<in> fspace S \<and> g \<in> fspace S \<and> S \<noteq> {} 
                    then Sup ((\<lambda>x. d (f x) (g x)) ` S) else 0"

lemma fspace_empty [simp]: "fspace {} = {\<lambda>x. undefined}"
sorry

lemma fdist_empty [simp]: "fdist {} = (\<lambda>x y. 0)"
sorry

lemma fspace_in_M: "\<lbrakk>f \<in> fspace S; x \<in> S\<rbrakk> \<Longrightarrow> f x \<in> M"
sorry

lemma bdd_above_dist:
  assumes f: "f \<in> fspace S" and g: "g \<in> fspace S" and "S \<noteq> {}"
  shows "bdd_above ((\<lambda>u. d (f u) (g u)) ` S)"
sorry

lemma Metric_space_funspace: "Metric_space (fspace S) (fdist S)"
sorry

end


definition funspace where
  "funspace S m \<equiv> metric (Metric_space.fspace (mspace m) (mdist m) S, 
                          Metric_space.fdist (mspace m) (mdist m) S)"

lemma mspace_funspace [simp]:
  "mspace (funspace S m) = Metric_space.fspace (mspace m) (mdist m) S"
sorry

lemma mdist_funspace [simp]:
  "mdist (funspace S m) = Metric_space.fdist (mspace m) (mdist m) S"
sorry

lemma funspace_imp_welldefined:
   "\<lbrakk>f \<in> mspace (funspace S m); x \<in> S\<rbrakk> \<Longrightarrow> f x \<in> mspace m"
sorry

lemma funspace_imp_extensional:
   "f \<in> mspace (funspace S m) \<Longrightarrow> f \<in> extensional S"
sorry

lemma funspace_imp_bounded_image:
   "f \<in> mspace (funspace S m) \<Longrightarrow> Metric_space.mbounded (mspace m) (mdist m) (f ` S)"
sorry

lemma funspace_imp_bounded:
   "f \<in> mspace (funspace S m) \<Longrightarrow> S = {} \<or> (\<exists>c B. \<forall>x \<in> S. mdist m c (f x) \<le> B)"
sorry

lemma (in Metric_space) funspace_imp_bounded2:
  assumes "f \<in> fspace S" "g \<in> fspace S"
  obtains B where "\<And>x. x \<in> S \<Longrightarrow> d (f x) (g x) \<le> B"
sorry

lemma funspace_imp_bounded2:
  assumes "f \<in> mspace (funspace S m)" "g \<in> mspace (funspace S m)"
  obtains B where "\<And>x. x \<in> S \<Longrightarrow> mdist m (f x) (g x) \<le> B"
sorry

lemma (in Metric_space) funspace_mdist_le:
  assumes fg: "f \<in> fspace S" "g \<in> fspace S" and "S \<noteq> {}"
  shows "fdist S f g \<le> a \<longleftrightarrow> (\<forall>x \<in> S. d (f x) (g x) \<le> a)"
sorry

lemma funspace_mdist_le:
  assumes "f \<in> mspace (funspace S m)" "g \<in> mspace (funspace S m)" and "S \<noteq> {}"
  shows "mdist (funspace S m) f g \<le> a \<longleftrightarrow> (\<forall>x \<in> S. mdist m (f x) (g x) \<le> a)"
sorry

lemma (in Metric_space) mcomplete_funspace:
  assumes "mcomplete"
  shows "mcomplete_of (funspace S Self)"
sorry



subsection\<open>Metric space of continuous bounded functions\<close>

definition cfunspace where
  "cfunspace X m \<equiv> submetric (funspace (topspace X) m) {f. continuous_map X (mtopology_of m) f}"

lemma mspace_cfunspace [simp]:
  "mspace (cfunspace X m) = 
     {f. f \<in> topspace X \<rightarrow> mspace m \<and> f \<in> extensional (topspace X) \<and>
         Metric_space.mbounded (mspace m) (mdist m) (f ` (topspace X)) \<and>
         continuous_map X (mtopology_of m) f}"
sorry

lemma mdist_cfunspace_eq_mdist_funspace:
  "mdist (cfunspace X m) = mdist (funspace (topspace X) m)"
sorry

lemma cfunspace_subset_funspace:
   "mspace (cfunspace X m) \<subseteq> mspace (funspace (topspace X) m)"
sorry

lemma cfunspace_mdist_le:
   "\<lbrakk>f \<in> mspace (cfunspace X m); g \<in> mspace (cfunspace X m); topspace X \<noteq> {}\<rbrakk>
     \<Longrightarrow> mdist (cfunspace X m) f g \<le> a \<longleftrightarrow> (\<forall>x \<in> topspace X. mdist m (f x) (g x) \<le> a)"
sorry

lemma cfunspace_imp_bounded2:
  assumes "f \<in> mspace (cfunspace X m)" "g \<in> mspace (cfunspace X m)"
  obtains B where "\<And>x. x \<in> topspace X \<Longrightarrow> mdist m (f x) (g x) \<le> B"
sorry

lemma cfunspace_mdist_lt:
   "\<lbrakk>compactin X (topspace X); f \<in> mspace (cfunspace X m);
     g \<in> mspace (cfunspace X m); mdist (cfunspace X m) f g < a;
     x \<in> topspace X\<rbrakk>
     \<Longrightarrow> mdist m (f x) (g x) < a"
sorry

lemma mdist_cfunspace_le:
  assumes "0 \<le> B" and B: "\<And>x. x \<in> topspace X \<Longrightarrow> mdist m (f x) (g x) \<le> B"
  shows "mdist (cfunspace X m) f g \<le> B"
sorry

lemma mdist_cfunspace_imp_mdist_le:
   "\<lbrakk>f \<in> mspace (cfunspace X m); g \<in> mspace (cfunspace X m);
     mdist (cfunspace X m) f g \<le> a; x \<in> topspace X\<rbrakk> \<Longrightarrow> mdist m (f x) (g x) \<le> a"
sorry

lemma compactin_mspace_cfunspace:
   "compactin X (topspace X)
     \<Longrightarrow> mspace (cfunspace X m) =
          {f. (\<forall>x \<in> topspace X. f x \<in> mspace m) \<and>
               f \<in> extensional (topspace X) \<and>
               continuous_map X (mtopology_of m) f}"
sorry

lemma (in Metric_space) mcomplete_cfunspace:
  assumes "mcomplete"
  shows "mcomplete_of (cfunspace X Self)"
sorry


subsection\<open>Existence of completion for any metric space M as a subspace of M=>R\<close>

lemma (in Metric_space) metric_completion_explicit:
  obtains f :: "['a,'a] \<Rightarrow> real" and S where
      "S \<subseteq> mspace(funspace M euclidean_metric)"
      "mcomplete_of (submetric (funspace M euclidean_metric) S)"
      "f \<in> M \<rightarrow> S"
      "mtopology_of(funspace M euclidean_metric) closure_of f ` M = S"
      "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk>
            \<Longrightarrow> mdist (funspace M euclidean_metric) (f x) (f y) = d x y"
sorry

lemma (in Metric_space) metric_completion:
  obtains f :: "['a,'a] \<Rightarrow> real" and m' where
    "mcomplete_of m'"
    "f \<in> M \<rightarrow> mspace m' "
    "mtopology_of m' closure_of f ` M = mspace m'"
    "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> mdist m' (f x) (f y) = d x y"
sorry

lemma metrizable_space_completion:
  assumes "metrizable_space X"
  obtains f :: "['a,'a] \<Rightarrow> real" and Y where
       "completely_metrizable_space Y" "embedding_map X Y f"
                "Y closure_of (f ` (topspace X)) = topspace Y"
sorry


subsection\<open>Contractions\<close>

lemma (in Metric_space) contraction_imp_unique_fixpoint:
  assumes "f x = x" "f y = y"
    and "f \<in> M \<rightarrow> M"
    and "k < 1"
    and "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> d (f x) (f y) \<le> k * d x y"
    and "x \<in> M" "y \<in> M"
  shows "x = y"
sorry

text \<open>Banach Fixed-Point Theorem (aka, Contraction Mapping Principle)\<close>
lemma (in Metric_space) Banach_fixedpoint_thm:
  assumes mcomplete and "M \<noteq> {}" and fim: "f \<in> M \<rightarrow> M"    
    and "k < 1"
    and con: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> d (f x) (f y) \<le> k * d x y"
  obtains x where "x \<in> M" "f x = x"
sorry


subsection\<open> The Baire Category Theorem\<close>

text \<open>Possibly relevant to the theorem "Baire" in Elementary Normed Spaces\<close>

lemma (in Metric_space) metric_Baire_category:
  assumes "mcomplete" "countable \<G>"
  and "\<And>T. T \<in> \<G> \<Longrightarrow> openin mtopology T \<and> mtopology closure_of T = M"
shows "mtopology closure_of \<Inter>\<G> = M"
sorry

lemma (in Metric_space) metric_Baire_category_alt:
  assumes "mcomplete" "countable \<G>"
    and empty: "\<And>T. T \<in> \<G> \<Longrightarrow> closedin mtopology T \<and> mtopology interior_of T = {}"
  shows "mtopology interior_of \<Union>\<G> = {}"
sorry



text \<open>Since all locally compact Hausdorff spaces are regular, the disjunction in the HOL Light version is redundant.\<close>
lemma Baire_category_aux:
  assumes "locally_compact_space X" "regular_space X" 
    and "countable \<G>"
    and empty: "\<And>G. G \<in> \<G> \<Longrightarrow> closedin X G \<and> X interior_of G = {}"
  shows "X interior_of \<Union>\<G> = {}"
sorry

lemma Baire_category_alt:
  assumes "completely_metrizable_space X \<or> locally_compact_space X \<and> regular_space X" 
    and "countable \<G>"
    and "\<And>T. T \<in> \<G> \<Longrightarrow> closedin X T \<and> X interior_of T = {}"
  shows "X interior_of \<Union>\<G> = {}"
sorry

lemma Baire_category:
  assumes "completely_metrizable_space X \<or> locally_compact_space X \<and> regular_space X" 
    and "countable \<G>"
    and top: "\<And>T. T \<in> \<G> \<Longrightarrow> openin X T \<and> X closure_of T = topspace X"
  shows "X closure_of \<Inter>\<G> = topspace X"
sorry


subsection\<open>Sierpinski-Hausdorff type results about countable closed unions\<close>

lemma locally_connected_not_countable_closed_union:
  assumes "topspace X \<noteq> {}" and csX: "connected_space X"
    and lcX: "locally_connected_space X"
    and X: "completely_metrizable_space X \<or> locally_compact_space X \<and> Hausdorff_space X"
    and "countable \<U>" and pwU: "pairwise disjnt \<U>"
    and clo: "\<And>C. C \<in> \<U> \<Longrightarrow> closedin X C \<and> C \<noteq> {}"
    and UU_eq: "\<Union>\<U> = topspace X"
  shows "\<U> = {topspace X}"
sorry

lemma real_Sierpinski_lemma:
  fixes a b::real
  assumes "a \<le> b"
    and "countable \<U>" and pwU: "pairwise disjnt \<U>"
    and clo: "\<And>C. C \<in> \<U> \<Longrightarrow> closed C \<and> C \<noteq> {}"
    and "\<Union>\<U> = {a..b}"
  shows "\<U> = {{a..b}}"
sorry


subsection\<open>The Tychonoff embedding\<close>

lemma completely_regular_space_cube_embedding_explicit:
  assumes "completely_regular_space X" "Hausdorff_space X"
  shows "embedding_map X
             (product_topology (\<lambda>f. top_of_set {0..1::real})
                (mspace (submetric (cfunspace X euclidean_metric)
                  {f. f \<in> topspace X \<rightarrow> {0..1}})) )
             (\<lambda>x. \<lambda>f \<in> mspace (submetric (cfunspace X euclidean_metric) {f. f \<in> topspace X \<rightarrow> {0..1}}).
              f x)"
sorry

lemma completely_regular_space_cube_embedding:
  fixes X :: "'a topology"
  assumes "completely_regular_space X" "Hausdorff_space X"
  obtains K:: "('a\<Rightarrow>real)set" and e
    where "embedding_map X (product_topology (\<lambda>f. top_of_set {0..1::real}) K) e"
sorry

subsection \<open>Urysohn and Tietze analogs for completely regular spaces\<close>

text\<open>"Urysohn and Tietze analogs for completely regular spaces if (()) set is 
assumed compact instead of closed. Note that Hausdorffness is *not* required: inside () proof 
we factor through the Kolmogorov quotient." -- John Harrison\<close>

lemma Urysohn_completely_regular_closed_compact:
  fixes a b::real
  assumes "a \<le> b" "completely_regular_space X" "closedin X S" "compactin X T" "disjnt S T"
  obtains f where "continuous_map X (subtopology euclidean {a..b}) f" "f ` T \<subseteq> {a}" "f ` S \<subseteq> {b}"
sorry

lemma Urysohn_completely_regular_compact_closed:
  fixes a b::real
  assumes "a \<le> b" "completely_regular_space X" "compactin X S" "closedin X T" "disjnt S T"
  obtains f where "continuous_map X (subtopology euclidean {a..b}) f" "f ` T \<subseteq> {a}" "f ` S \<subseteq> {b}"
sorry

lemma Urysohn_completely_regular_compact_closed_alt:
  fixes a b::real
  assumes "completely_regular_space X" "compactin X S" "closedin X T" "disjnt S T"
  obtains f where "continuous_map X euclideanreal f" "f ` T \<subseteq> {a}" "f ` S \<subseteq> {b}"
sorry

lemma Tietze_extension_comp_reg_aux:
  fixes T :: "real set"
  assumes "completely_regular_space X" "Hausdorff_space X" "compactin X S" 
    and T: "is_interval T" "T\<noteq>{}" 
    and contf: "continuous_map (subtopology X S) euclidean f" and fim: "f`S \<subseteq> T"
  obtains g where "continuous_map X euclidean g" "g ` topspace X \<subseteq> T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma Tietze_extension_completely_regular:
  assumes "completely_regular_space X" "compactin X S" "is_interval T" "T \<noteq> {}" 
    and contf: "continuous_map (subtopology X S) euclidean f" and fim: "f`S \<subseteq> T"
  obtains g where "continuous_map X euclideanreal g" "g ` topspace X \<subseteq> T" 
    "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

subsection\<open>Size bounds on connected or path-connected spaces\<close>

lemma connected_space_imp_card_ge_alt:
  assumes "connected_space X" "completely_regular_space X" "closedin X S" "S \<noteq> {}" "S \<noteq> topspace X"
  shows "(UNIV::real set) \<lesssim> topspace X"
sorry

lemma connected_space_imp_card_ge_gen:
  assumes "connected_space X" "normal_space X" "closedin X S" "closedin X T" "S \<noteq> {}" "T \<noteq> {}" "disjnt S T"
  shows "(UNIV::real set) \<lesssim> topspace X"
sorry

lemma connected_space_imp_card_ge:
  assumes "connected_space X" "normal_space X" "t1_space X" and nosing: "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "(UNIV::real set) \<lesssim> topspace X"
sorry

lemma connected_space_imp_infinite_gen:
   "\<lbrakk>connected_space X; t1_space X; \<nexists>a. topspace X \<subseteq> {a}\<rbrakk> \<Longrightarrow> infinite(topspace X)"
sorry

lemma connected_space_imp_infinite:
   "\<lbrakk>connected_space X; Hausdorff_space X; \<nexists>a. topspace X \<subseteq> {a}\<rbrakk> \<Longrightarrow> infinite(topspace X)"
sorry

lemma connected_space_imp_infinite_alt:
  assumes "connected_space X" "regular_space X" "closedin X S" "S \<noteq> {}" "S \<noteq> topspace X"
  shows "infinite(topspace X)"
sorry

lemma path_connected_space_imp_card_ge:
  assumes "path_connected_space X" "Hausdorff_space X" and nosing: "\<not> (\<exists>x. topspace X \<subseteq> {x})"
  shows "(UNIV::real set) \<lesssim> topspace X"
sorry

lemma connected_space_imp_uncountable:
  assumes "connected_space X" "regular_space X" "Hausdorff_space X" "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "\<not> countable(topspace X)"
sorry

lemma path_connected_space_imp_uncountable:
  assumes "path_connected_space X" "t1_space X" and nosing: "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "\<not> countable(topspace X)"
sorry


subsection\<open>Lavrentiev extension etc\<close>

lemma (in Metric_space) convergent_eq_zero_oscillation_gen:
  assumes "mcomplete" and fim: "f \<in> (topspace X \<inter> S) \<rightarrow> M"
  shows "(\<exists>l. limitin mtopology f l (atin_within X a S)) \<longleftrightarrow>
         M \<noteq> {} \<and>
         (a \<in> topspace X
            \<longrightarrow> (\<forall>\<epsilon>>0. \<exists>U. openin X U \<and> a \<in> U \<and>
                           (\<forall>x \<in> (S \<inter> U) - {a}. \<forall>y \<in> (S \<inter> U) - {a}. d (f x) (f y) < \<epsilon>)))"
sorry

text \<open>The HOL Light proof uses some ugly tricks to share common parts of what are two separate proofs for the two cases\<close>
lemma (in Metric_space) gdelta_in_points_of_convergence_within:
  assumes "mcomplete"
    and f: "continuous_map (subtopology X S) mtopology f \<or> t1_space X \<and> f \<in> S \<rightarrow> M"
  shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin mtopology f l (atin_within X x S)}"
sorry

lemma gdelta_in_points_of_convergence_within:
  assumes Y: "completely_metrizable_space Y"
    and f: "continuous_map (subtopology X S) Y f \<or> t1_space X \<and> f \<in> S \<rightarrow> topspace Y"
  shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin Y f l (atin_within X x S)}"
sorry

lemma Lavrentiev_extension_gen:
  assumes "S \<subseteq> topspace X" and Y: "completely_metrizable_space Y" 
    and contf: "continuous_map (subtopology X S) Y f"
  obtains U g where "gdelta_in X U" "S \<subseteq> U" 
            "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g" 
             "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma Lavrentiev_extension:
  assumes "S \<subseteq> topspace X" 
    and X: "metrizable_space X \<or> topspace X \<subseteq> X closure_of S" 
    and Y: "completely_metrizable_space Y" 
    and contf: "continuous_map (subtopology X S) Y f"
  obtains U g where "gdelta_in X U" "S \<subseteq> U" "U \<subseteq> X closure_of S"
            "continuous_map (subtopology X U) Y g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

subsection\<open>Embedding in products and hence more about completely metrizable spaces\<close>

lemma (in Metric_space) gdelta_homeomorphic_space_closedin_product:
  assumes S: "\<And>i. i \<in> I \<Longrightarrow> openin mtopology (S i)"
  obtains T where "closedin (prod_topology mtopology (powertop_real I)) T"
                  "subtopology mtopology (\<Inter>i \<in> I. S i) homeomorphic_space
                   subtopology (prod_topology mtopology (powertop_real I)) T"
sorry

lemma gdelta_homeomorphic_space_closedin_product:
  assumes "metrizable_space X" and "\<And>i. i \<in> I \<Longrightarrow> openin X (S i)"
  obtains T where "closedin (prod_topology X (powertop_real I)) T"
                  "subtopology X (\<Inter>i \<in> I. S i) homeomorphic_space
                   subtopology (prod_topology X (powertop_real I)) T"
sorry

lemma open_homeomorphic_space_closedin_product:
  assumes "metrizable_space X" and "openin X S"
  obtains T where "closedin (prod_topology X euclideanreal) T"
    "subtopology X S homeomorphic_space
                   subtopology (prod_topology X euclideanreal) T"
sorry

lemma completely_metrizable_space_gdelta_in_alt:
  assumes X: "completely_metrizable_space X" 
    and S: "(countable intersection_of openin X) S"
  shows "completely_metrizable_space (subtopology X S)"
sorry

lemma completely_metrizable_space_gdelta_in:
   "\<lbrakk>completely_metrizable_space X; gdelta_in X S\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S)"
sorry

lemma completely_metrizable_space_openin:
   "\<lbrakk>completely_metrizable_space X; openin X S\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S)"
sorry

lemma (in Metric_space) locally_compact_imp_completely_metrizable_space:
  assumes "locally_compact_space mtopology"
  shows "completely_metrizable_space mtopology"
sorry

lemma locally_compact_imp_completely_metrizable_space:
  assumes "metrizable_space X" and "locally_compact_space X"
  shows "completely_metrizable_space X"
sorry

lemma completely_metrizable_space_imp_gdelta_in:
  assumes X: "metrizable_space X" and "S \<subseteq> topspace X" 
    and XS: "completely_metrizable_space (subtopology X S)"
  shows "gdelta_in X S"
sorry

lemma completely_metrizable_space_eq_gdelta_in:
   "\<lbrakk>completely_metrizable_space X; S \<subseteq> topspace X\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S) \<longleftrightarrow> gdelta_in X S"
sorry

lemma gdelta_in_eq_completely_metrizable_space:
   "completely_metrizable_space X
    \<Longrightarrow> gdelta_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> completely_metrizable_space (subtopology X S)"
sorry

subsection\<open> Theorems from Kuratowski\<close>

text\<open>Kuratowski, Remark on an Invariance Theorem, \emph{Fundamenta Mathematicae} \textbf{37} (1950), pp. 251-252. 
 The idea is that in suitable spaces, to show "number of components of the complement" (without 
 distinguishing orders of infinity) is a homeomorphic invariant, it 
 suffices to show it for closed subsets. Kuratowski states the main result 
 for a "locally connected continuum", and seems clearly to be implicitly   
 assuming that means metrizable. We call out the general topological       
 hypotheses more explicitly, which do not however include connectedness.   \<close>

lemma separation_by_closed_intermediates_count:
  assumes X: "hereditarily normal_space X"
    and "finite \<U>"
    and pwU: "pairwise (separatedin X) \<U>"
    and nonempty: "{} \<notin> \<U>"
    and UU: "\<Union>\<U> = topspace X - S"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>\<V>. \<V> \<approx> \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
sorry

lemma separation_by_closed_intermediates_gen:
  assumes X: "hereditarily normal_space X"
    and discon: "\<not> connectedin X (topspace X - S)"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk> \<Longrightarrow> \<not> connectedin X (topspace X - D)"
sorry

lemma separation_by_closed_intermediates_eq_count:
  fixes n::nat
  assumes lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
  shows "(\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>\<U>.  \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D)))"
         (is "?lhs = ?rhs")
sorry

lemma separation_by_closed_intermediates_eq_gen:
  assumes "locally_connected_space X" "hereditarily normal_space X"
  shows "\<not> connectedin X (topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S \<longrightarrow> \<not> connectedin X (topspace X - D)))"
    (is "?lhs = ?rhs")
sorry

lemma lepoll_connnected_components_connectedin:
  assumes "\<And>C. C \<in> \<U> \<Longrightarrow> connectedin X C"  "\<Union>\<U> = topspace X"
  shows "connected_components_of X \<lesssim> \<U>"
sorry

lemma lepoll_connected_components_alt:
  "{..<n::nat} \<lesssim> connected_components_of X \<longleftrightarrow>
    n = 0 \<or> (\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X)"
  (is "?lhs \<longleftrightarrow> ?rhs")
sorry


subsection\<open>A perfect set in common cases must have at least the cardinality of the continuum\<close>

lemma (in Metric_space) lepoll_perfect_set:
  assumes "mcomplete"
    and "mtopology derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
sorry

lemma lepoll_perfect_set_aux:
  assumes lcX: "locally_compact_space X" and hsX: "Hausdorff_space X"
    and eq: "X derived_set_of topspace X = topspace X" and "topspace X \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> topspace X"
sorry

lemma lepoll_perfect_set:
  assumes X: "completely_metrizable_space X \<or> locally_compact_space X \<and> Hausdorff_space X"
    and S: "X derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
sorry

lemma Kuratowski_aux1:
  assumes "\<And>S T. R S T \<Longrightarrow> R T S"
  shows "(\<forall>S T n. R S T \<longrightarrow> (f S \<approx> {..<n::nat} \<longleftrightarrow> f T \<approx> {..<n::nat})) \<longleftrightarrow>
         (\<forall>n S T. R S T \<longrightarrow> {..<n::nat} \<lesssim> f S \<longrightarrow> {..<n::nat} \<lesssim> f T)"
         (is "?lhs = ?rhs")
sorry

lemma Kuratowski_aux2:
   "pairwise (separatedin (subtopology X (topspace X - S))) \<U> \<and> {} \<notin> \<U> \<and>
     \<Union>\<U> = topspace(subtopology X (topspace X - S)) \<longleftrightarrow>
     pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
sorry

proposition Kuratowski_component_number_invariance_aux:
  assumes "compact_space X" and HsX: "Hausdorff_space X" 
    and lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
    and hom: "(subtopology X S) homeomorphic_space (subtopology X T)"
    and leXS: "{..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - S))"
  assumes \<section>: "\<And>S T.
              \<lbrakk>closedin X S; closedin X T; (subtopology X S) homeomorphic_space (subtopology X T);
              {..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - S))\<rbrakk>
              \<Longrightarrow> {..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - T))"
  shows "{..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - T))"
sorry

theorem Kuratowski_component_number_invariance:
  assumes "compact_space X" "Hausdorff_space X" "locally_connected_space X" "hereditarily normal_space X"
  shows "((\<forall>S T n.
              closedin X S \<and> closedin X T \<and>
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})) \<longleftrightarrow>
           (\<forall>S T n.
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})))"
         (is "?lhs = ?rhs")
sorry

end
