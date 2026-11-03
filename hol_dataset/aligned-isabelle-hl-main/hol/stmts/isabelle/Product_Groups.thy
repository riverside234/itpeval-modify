(*  Title:      HOL/Algebra/Product_Groups.thy
    Author:     LC Paulson (ported from HOL Light)
*)

section \<open>Product and Sum Groups\<close>

theory Product_Groups
  imports Elementary_Groups "HOL-Library.Equipollence" 
  
begin

subsection \<open>Product of a Family of Groups\<close>

definition product_group:: "'a set \<Rightarrow> ('a \<Rightarrow> ('b, 'c) monoid_scheme) \<Rightarrow> ('a \<Rightarrow> 'b) monoid"
  where "product_group I G \<equiv> \<lparr>carrier = (\<Pi>\<^sub>E i\<in>I. carrier (G i)),
                              monoid.mult = (\<lambda>x y. (\<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> y i)),
                              one = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)\<rparr>"

lemma carrier_product_group [simp]: "carrier(product_group I G) = (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
sorry

lemma one_product_group [simp]: "one(product_group I G) = (\<lambda>i\<in>I. one (G i))"
sorry

lemma mult_product_group [simp]: "(\<otimes>\<^bsub>product_group I G\<^esub>) = (\<lambda>x y. \<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> y i)"
sorry

lemma product_group [simp]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" shows "group (product_group I G)"
sorry

lemma inv_product_group [simp]:
  assumes "f \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "inv\<^bsub>product_group I G\<^esub> f = (\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> f i)"
sorry

lemma trivial_product_group: "trivial_group(product_group I G) \<longleftrightarrow> (\<forall>i \<in> I. trivial_group(G i))"
 (is "?lhs = ?rhs")
sorry

lemma PiE_subgroup_product_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "subgroup (PiE I H) (product_group I G) \<longleftrightarrow> (\<forall>i \<in> I. subgroup (H i) (G i))"
    (is "?lhs = ?rhs")
sorry

lemma product_group_subgroup_generated:
  assumes "\<And>i. i \<in> I \<Longrightarrow> subgroup (H i) (G i)" and gp: "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "product_group I (\<lambda>i. subgroup_generated (G i) (H i))
       = subgroup_generated (product_group I G) (PiE I H)"
sorry

lemma finite_product_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows
   "finite (carrier (product_group I G)) \<longleftrightarrow>
    finite {i. i \<in> I \<and> ~ trivial_group(G i)} \<and> (\<forall>i \<in> I. finite(carrier(G i)))"
sorry

subsection \<open>Sum of a Family of Groups\<close>

definition sum_group :: "'a set \<Rightarrow> ('a \<Rightarrow> ('b, 'c) monoid_scheme) \<Rightarrow> ('a \<Rightarrow> 'b) monoid"
  where "sum_group I G \<equiv>
        subgroup_generated
         (product_group I G)
         {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"

lemma subgroup_sum_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "subgroup {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}
                  (product_group I G)"
sorry

lemma carrier_sum_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "carrier(sum_group I G) = {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
sorry

lemma one_sum_group [simp]: "\<one>\<^bsub>sum_group I G\<^esub> = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)"
sorry

lemma mult_sum_group [simp]: "(\<otimes>\<^bsub>sum_group I G\<^esub>) = (\<lambda>x y. (\<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> y i))"
sorry

lemma sum_group [simp]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" shows "group (sum_group I G)"
sorry

lemma inv_sum_group [simp]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and x: "x \<in> carrier (sum_group I G)"
  shows "m_inv (sum_group I G) x = (\<lambda>i\<in>I. m_inv (G i) (x i))"
sorry


thm group.subgroups_Inter (*REPLACE*)
theorem subgroup_Inter:
  assumes subgr: "(\<And>H. H \<in> A \<Longrightarrow> subgroup H G)"
    and not_empty: "A \<noteq> {}"
  shows "subgroup (\<Inter>A) G"
sorry

thm group.subgroups_Inter_pair (*REPLACE*)
lemma subgroup_Int:
  assumes "subgroup I G" "subgroup J G"
  shows "subgroup (I \<inter> J) G" using subgroup_Inter[ where ?A = "{I,J}"]
sorry


lemma sum_group_subgroup_generated:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and sg: "\<And>i. i \<in> I \<Longrightarrow> subgroup (H i) (G i)"
  shows "sum_group I (\<lambda>i. subgroup_generated (G i) (H i)) = subgroup_generated (sum_group I G) (PiE I H)"
sorry

lemma iso_product_groupI:
  assumes iso: "\<And>i. i \<in> I \<Longrightarrow> G i \<cong> H i"
    and G: "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and H: "\<And>i. i \<in> I \<Longrightarrow> group (H i)"
  shows "product_group I G \<cong> product_group I H" (is "?IG \<cong> ?IH")
sorry

lemma iso_sum_groupI:
  assumes iso: "\<And>i. i \<in> I \<Longrightarrow> G i \<cong> H i"
    and G: "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and H: "\<And>i. i \<in> I \<Longrightarrow> group (H i)"
  shows "sum_group I G \<cong> sum_group I H" (is "?IG \<cong> ?IH")
sorry

end
