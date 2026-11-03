section \<open>Elementary Group Constructions\<close>

(*  Title:      HOL/Algebra/Elementary_Groups.thy
    Author:     LC Paulson, ported from HOL Light
*)

theory Elementary_Groups
imports Generated_Groups "HOL-Library.Infinite_Set"
begin

subsection\<open>Direct sum/product lemmas\<close>

locale group_disjoint_sum = group G + AG: subgroup A G + BG: subgroup B G for G (structure) and A B
begin

lemma subset_one: "A \<inter> B \<subseteq> {\<one>} \<longleftrightarrow> A \<inter> B = {\<one>}"
sorry

lemma sub_id_iff: "A \<inter> B \<subseteq> {\<one>} \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = \<one> \<longrightarrow> x = \<one> \<and> y = \<one>)"
        (is "?lhs = ?rhs")
sorry

lemma cancel: "A \<inter> B \<subseteq> {\<one>} \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. \<forall>x'\<in>A. \<forall>y'\<in>B. x \<otimes> y = x' \<otimes> y' \<longrightarrow> x = x' \<and> y = y')"
        (is "?lhs = ?rhs")
sorry

lemma commuting_imp_normal1:
  assumes sub: "carrier G \<subseteq> A <#> B"
     and mult: "\<And>x y. \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
   shows "A \<lhd> G"
sorry

lemma commuting_imp_normal2:
  assumes"carrier G \<subseteq> A <#> B"  "\<And>x y. \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
  shows "B \<lhd> G"
sorry

lemma (in group) normal_imp_commuting:
  assumes "A \<lhd> G" "B \<lhd> G" "A \<inter> B \<subseteq> {\<one>}" "x \<in> A" "y \<in> B"
  shows "x \<otimes> y = y \<otimes> x"
sorry

lemma normal_eq_commuting:
  assumes "carrier G \<subseteq> A <#> B" "A \<inter> B \<subseteq> {\<one>}"
  shows "A \<lhd> G \<and> B \<lhd> G \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
sorry

lemma (in group) hom_group_mul_rev:
  assumes "(\<lambda>(x,y). x \<otimes> y) \<in> hom (subgroup_generated G A \<times>\<times> subgroup_generated G B) G"
          (is "?h \<in> hom ?P G")
   and "x \<in> carrier G" "y \<in> carrier G" "x \<in> A" "y \<in> B"
 shows "x \<otimes> y = y \<otimes> x"
sorry

lemma hom_group_mul_eq:
   "(\<lambda>(x,y). x \<otimes> y) \<in> hom (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
         (is "?lhs = ?rhs")
sorry

lemma epi_group_mul_eq:
   "(\<lambda>(x,y). x \<otimes> y) \<in> epi (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A <#> B = carrier G \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
sorry

lemma mon_group_mul_eq:
    "(\<lambda>(x,y). x \<otimes> y) \<in> mon (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B = {\<one>} \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
sorry

lemma iso_group_mul_alt:
    "(\<lambda>(x,y). x \<otimes> y) \<in> iso (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B = {\<one>} \<and> A <#> B = carrier G \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
sorry

lemma iso_group_mul_eq:
    "(\<lambda>(x,y). x \<otimes> y) \<in> iso (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B = {\<one>} \<and> A <#> B = carrier G \<and> A \<lhd> G \<and> B \<lhd> G"
sorry

lemma (in group) iso_group_mul_gen:
  assumes "A \<lhd> G" "B \<lhd> G"
  shows "(\<lambda>(x,y). x \<otimes> y) \<in> iso (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B \<subseteq> {\<one>} \<and> A <#> B = carrier G"
sorry

lemma iso_group_mul:
  assumes "comm_group G"
  shows "((\<lambda>(x,y). x \<otimes> y) \<in> iso (DirProd (subgroup_generated G A) (subgroup_generated G B)) G
     \<longleftrightarrow> A \<inter> B \<subseteq> {\<one>} \<and> A <#> B = carrier G)"
sorry

end


subsection\<open>The one-element group on a given object\<close>

definition singleton_group :: "'a \<Rightarrow> 'a monoid"
  where "singleton_group a = \<lparr>carrier = {a}, monoid.mult = (\<lambda>x y. a), one = a\<rparr>"

lemma singleton_group [simp]: "group (singleton_group a)"
sorry

lemma singleton_abelian_group [simp]: "comm_group (singleton_group a)"
sorry

lemma carrier_singleton_group [simp]: "carrier (singleton_group a) = {a}"
sorry

lemma (in group) hom_into_singleton_iff [simp]:
  "h \<in> hom G (singleton_group a) \<longleftrightarrow> h \<in> carrier G \<rightarrow> {a}"
sorry

declare group.hom_into_singleton_iff [simp]

lemma (in group) id_hom_singleton: "id \<in> hom (singleton_group \<one>) G"
sorry

subsection\<open>Similarly, trivial groups\<close>

definition trivial_group :: "('a, 'b) monoid_scheme \<Rightarrow> bool"
  where "trivial_group G \<equiv> group G \<and> carrier G = {one G}"

lemma trivial_imp_finite_group:
   "trivial_group G \<Longrightarrow> finite(carrier G)"
sorry

lemma trivial_singleton_group [simp]: "trivial_group(singleton_group a)"
sorry

lemma (in group) trivial_group_subset:
   "trivial_group G \<longleftrightarrow> carrier G \<subseteq> {one G}"
sorry

lemma (in group) trivial_group: "trivial_group G \<longleftrightarrow> (\<exists>a. carrier G = {a})"
sorry

lemma (in group) trivial_group_alt:
   "trivial_group G \<longleftrightarrow> (\<exists>a. carrier G \<subseteq> {a})"
sorry

lemma (in group) trivial_group_subgroup_generated:
  assumes "S \<subseteq> {one G}"
  shows "trivial_group(subgroup_generated G S)"
sorry

lemma (in group) trivial_group_subgroup_generated_eq:
  "trivial_group(subgroup_generated G s) \<longleftrightarrow> carrier G \<inter> s \<subseteq> {one G}"
sorry

lemma isomorphic_group_triviality1:
  assumes "G \<cong> H" "group H" "trivial_group G"
  shows "trivial_group H"
sorry

lemma isomorphic_group_triviality:
  assumes "G \<cong> H" "group G" "group H"
  shows "trivial_group G \<longleftrightarrow> trivial_group H"
sorry

lemma (in group_hom) kernel_from_trivial_group:
   "trivial_group G \<Longrightarrow> kernel G H h = carrier G"
sorry

lemma (in group_hom) image_from_trivial_group:
   "trivial_group G \<Longrightarrow> h ` carrier G = {one H}"
sorry

lemma (in group_hom) kernel_to_trivial_group:
   "trivial_group H \<Longrightarrow> kernel G H h = carrier G"
sorry

subsection\<open>The additive group of integers\<close>

definition integer_group
  where "integer_group = \<lparr>carrier = UNIV, monoid.mult = (+), one = (0::int)\<rparr>"

lemma group_integer_group [simp]: "group integer_group"
sorry

lemma carrier_integer_group [simp]: "carrier integer_group = UNIV"
sorry

lemma one_integer_group [simp]: "\<one>\<^bsub>integer_group\<^esub> = 0"
sorry

lemma mult_integer_group [simp]: "x \<otimes>\<^bsub>integer_group\<^esub> y = x + y"
sorry

lemma inv_integer_group [simp]: "inv\<^bsub>integer_group\<^esub> x = -x"
sorry

lemma abelian_integer_group: "comm_group integer_group"
sorry

lemma group_nat_pow_integer_group [simp]:
  fixes n::nat and x::int
  shows "pow integer_group x n = int n * x"
sorry

lemma group_int_pow_integer_group [simp]:
  fixes n::int and x::int
  shows "pow integer_group x n = n * x"
sorry

lemma (in group) hom_integer_group_pow:
   "x \<in> carrier G \<Longrightarrow> pow G x \<in> hom integer_group G"
sorry

subsection\<open>Additive group of integers modulo n (n = 0 gives just the integers)\<close>

definition integer_mod_group :: "nat \<Rightarrow> int monoid"
  where
  "integer_mod_group n \<equiv>
     if n = 0 then integer_group
     else \<lparr>carrier = {0..<int n}, monoid.mult = (\<lambda>x y. (x+y) mod int n), one = 0\<rparr>"

lemma carrier_integer_mod_group:
  "carrier(integer_mod_group n) = (if n=0 then UNIV else {0..<int n})"
sorry

lemma one_integer_mod_group[simp]: "one(integer_mod_group n) = 0"
sorry

lemma mult_integer_mod_group[simp]: "monoid.mult(integer_mod_group n) = (\<lambda>x y. (x + y) mod int n)"
sorry

lemma group_integer_mod_group [simp]: "group (integer_mod_group n)"
sorry

lemma inv_integer_mod_group[simp]:
  "x \<in> carrier (integer_mod_group n) \<Longrightarrow> m_inv(integer_mod_group n) x = (-x) mod int n"
sorry

lemma pow_integer_mod_group [simp]:
  fixes m::nat
  shows "pow (integer_mod_group n) x m = (int m * x) mod int n"
sorry

lemma int_pow_integer_mod_group:
  "pow (integer_mod_group n) x m = (m * x) mod int n"
sorry

lemma abelian_integer_mod_group [simp]: "comm_group(integer_mod_group n)"
sorry

lemma integer_mod_group_0 [simp]: "0 \<in> carrier(integer_mod_group n)"
sorry

lemma integer_mod_group_1 [simp]: "1 \<in> carrier(integer_mod_group n) \<longleftrightarrow> (n \<noteq> 1)"
sorry

lemma trivial_integer_mod_group: "trivial_group(integer_mod_group n) \<longleftrightarrow> n = 1"
  (is "?lhs = ?rhs")
sorry


subsection\<open>Cyclic groups\<close>

lemma (in group) subgroup_of_powers:
  "x \<in> carrier G \<Longrightarrow> subgroup (range (\<lambda>n::int. x [^] n)) G"
sorry

lemma (in group) carrier_subgroup_generated_by_singleton:
  assumes "x \<in> carrier G"
  shows "carrier(subgroup_generated G {x}) = (range (\<lambda>n::int. x [^] n))"
sorry


definition cyclic_group
  where "cyclic_group G \<equiv> \<exists>x \<in> carrier G. subgroup_generated G {x} = G"

lemma (in group) cyclic_group:
  "cyclic_group G \<longleftrightarrow> (\<exists>x \<in> carrier G. carrier G = range (\<lambda>n::int. x [^] n))"
sorry

lemma cyclic_integer_group [simp]: "cyclic_group integer_group"
sorry

lemma nontrivial_integer_group [simp]: "\<not> trivial_group integer_group"
sorry

lemma (in group) cyclic_imp_abelian_group:
  "cyclic_group G \<Longrightarrow> comm_group G"
sorry

lemma trivial_imp_cyclic_group:
   "trivial_group G \<Longrightarrow> cyclic_group G"
sorry

lemma (in group) cyclic_group_alt:
   "cyclic_group G \<longleftrightarrow> (\<exists>x. subgroup_generated G {x} = G)"
sorry

lemma (in group) cyclic_group_generated:
  "cyclic_group (subgroup_generated G {x})"
sorry

lemma (in group) cyclic_group_epimorphic_image:
  assumes "h \<in> epi G H" "cyclic_group G" "group H"
  shows "cyclic_group H"
sorry

lemma isomorphic_group_cyclicity:
   "\<lbrakk>G \<cong> H; group G; group H\<rbrakk> \<Longrightarrow> cyclic_group G \<longleftrightarrow> cyclic_group H"
sorry

end
