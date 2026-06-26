(*  Title:      HOL/Algebra/Coset.thy
    Authors:    Florian Kammueller, L C Paulson, Stephan Hohe

With additional contributions from Martin Baillon and Paulo Emílio de Vilhena.
*)

theory Coset
imports Group
begin

section \<open>Cosets and Quotient Groups\<close>

definition
  r_coset    :: "[_, 'a set, 'a] \<Rightarrow> 'a set"    (infixl \<open>#>\<index>\<close> 60)
  where "H #>\<^bsub>G\<^esub> a = (\<Union>h\<in>H. {h \<otimes>\<^bsub>G\<^esub> a})"

definition
  l_coset    :: "[_, 'a, 'a set] \<Rightarrow> 'a set"    (infixl \<open><#\<index>\<close> 60)
  where "a <#\<^bsub>G\<^esub> H = (\<Union>h\<in>H. {a \<otimes>\<^bsub>G\<^esub> h})"

definition
  RCOSETS  :: "[_, 'a set] \<Rightarrow> ('a set)set"
    (\<open>(\<open>open_block notation=\<open>prefix rcosets\<close>\<close>rcosets\<index> _)\<close> [81] 80)
  where "rcosets\<^bsub>G\<^esub> H = (\<Union>a\<in>carrier G. {H #>\<^bsub>G\<^esub> a})"

definition
  set_mult  :: "[_, 'a set ,'a set] \<Rightarrow> 'a set" (infixl \<open><#>\<index>\<close> 60)
  where "H <#>\<^bsub>G\<^esub> K = (\<Union>h\<in>H. \<Union>k\<in>K. {h \<otimes>\<^bsub>G\<^esub> k})"

definition
  SET_INV :: "[_,'a set] \<Rightarrow> 'a set"
    (\<open>(\<open>open_block notation=\<open>prefix set_inv\<close>\<close>set'_inv\<index> _)\<close> [81] 80)
  where "set_inv\<^bsub>G\<^esub> H = (\<Union>h\<in>H. {inv\<^bsub>G\<^esub> h})"


locale normal = subgroup + group +
  assumes coset_eq: "(\<forall>x \<in> carrier G. H #> x = x <# H)"

abbreviation
  normal_rel :: "['a set, ('a, 'b) monoid_scheme] \<Rightarrow> bool"  (infixl \<open>\<lhd>\<close> 60) where
  "H \<lhd> G \<equiv> normal H G"

lemma (in comm_group) subgroup_imp_normal: "subgroup A G \<Longrightarrow> A \<lhd> G"
  by sorry

lemma l_coset_eq_set_mult: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  fixes G (structure)
  shows "x <# H = {x} <#> H"
  by sorry

lemma r_coset_eq_set_mult: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  fixes G (structure)
  shows "H #> x = H <#> {x}"
  by sorry

lemma (in subgroup) rcosets_non_empty: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "R \<in> rcosets H"
  shows "R \<noteq> {}"
  by sorry

lemma (in group) diff_neutralizes: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup H G" "R \<in> rcosets H"
  shows "\<And>r1 r2. \<lbrakk> r1 \<in> R; r2 \<in> R \<rbrakk> \<Longrightarrow> r1 \<otimes> (inv r2) \<in> H"
  by sorry

lemma mono_set_mult: "\<lbrakk> H \<subseteq> H'; K \<subseteq> K' \<rbrakk> \<Longrightarrow> H <#>\<^bsub>G\<^esub> K \<subseteq> H' <#>\<^bsub>G\<^esub> K'" \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  by sorry


subsection \<open>Stable Operations for Subgroups\<close>

lemma set_mult_consistent [simp]: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "N <#>\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> K = N <#>\<^bsub>G\<^esub> K"
  by sorry

lemma r_coset_consistent [simp]: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "I #>\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> h = I #>\<^bsub>G\<^esub> h"
  by sorry

lemma l_coset_consistent [simp]: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "h <#\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> I = h <#\<^bsub>G\<^esub> I"
  by sorry


subsection \<open>Basic Properties of set multiplication\<close>

lemma (in group) setmult_subset_G:
  assumes "H \<subseteq> carrier G" "K \<subseteq> carrier G"
  shows "H <#> K \<subseteq> carrier G" using assms
  by sorry

lemma (in monoid) set_mult_closed:
  assumes "H \<subseteq> carrier G" "K \<subseteq> carrier G"
  shows "H <#> K \<subseteq> carrier G"
  by sorry

lemma (in group) set_mult_assoc: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "M \<subseteq> carrier G" "H \<subseteq> carrier G" "K \<subseteq> carrier G"
  shows "(M <#> H) <#> K = M <#> (H <#> K)"
  by sorry



subsection \<open>Basic Properties of Cosets\<close>

lemma (in group) coset_mult_assoc:
  assumes "M \<subseteq> carrier G" "g \<in> carrier G" "h \<in> carrier G"
  shows "(M #> g) #> h = M #> (g \<otimes> h)"
  by sorry

lemma (in group) coset_assoc:
  assumes "x \<in> carrier G" "y \<in> carrier G" "H \<subseteq> carrier G"
  shows "x <# (H #> y) = (x <# H) #> y"
  by sorry

lemma (in group) coset_mult_one [simp]: "M \<subseteq> carrier G ==> M #> \<one> = M"
  by sorry

lemma (in group) coset_mult_inv1:
  assumes "M #> (x \<otimes> (inv y)) = M"
    and "x \<in> carrier G" "y \<in> carrier G" "M \<subseteq> carrier G"
  shows "M #> x = M #> y" using assms
  by sorry

lemma (in group) coset_mult_inv2:
  assumes "M #> x = M #> y"
    and "x \<in> carrier G"  "y \<in> carrier G" "M \<subseteq> carrier G"
  shows "M #> (x \<otimes> (inv y)) = M " using assms
  by sorry

lemma (in group) coset_join1:
  assumes "H #> x = H"
    and "x \<in> carrier G" "subgroup H G"
  shows "x \<in> H"
  by sorry

lemma (in group) solve_equation:
  assumes "subgroup H G" "x \<in> H" "y \<in> H"
  shows "\<exists>h \<in> H. y = h \<otimes> x"
  by sorry

lemma (in group_hom) inj_on_one_iff:
   "inj_on h (carrier G) \<longleftrightarrow> (\<forall>x. x \<in> carrier G \<longrightarrow> h x = one H \<longrightarrow> x = one G)"
  by sorry

lemma inj_on_one_iff':
   "\<lbrakk>h \<in> hom G H; group G; group H\<rbrakk> \<Longrightarrow> inj_on h (carrier G) \<longleftrightarrow> (\<forall>x. x \<in> carrier G \<longrightarrow> h x = one H \<longrightarrow> x = one G)"
  by sorry

lemma mon_iff_hom_one:
   "\<lbrakk>group G; group H\<rbrakk> \<Longrightarrow> f \<in> mon G H \<longleftrightarrow> f \<in> hom G H \<and> (\<forall>x. x \<in> carrier G \<and> f x = \<one>\<^bsub>H\<^esub> \<longrightarrow> x = \<one>\<^bsub>G\<^esub>)"
  by sorry

lemma (in group_hom) iso_iff: "h \<in> iso G H \<longleftrightarrow> carrier H \<subseteq> h ` carrier G \<and> (\<forall>x\<in>carrier G. h x = \<one>\<^bsub>H\<^esub> \<longrightarrow> x = \<one>)"
  by sorry

lemma (in group) repr_independence:
  assumes "y \<in> H #> x" "x \<in> carrier G" "subgroup H G"
  shows "H #> x = H #> y" using assms
  by sorry

lemma (in group) coset_join2:
  assumes "x \<in> carrier G" "subgroup H G" "x \<in> H"
  shows "H #> x = H" using assms
  \<comment> \<open>Alternative proof is to put \<^term>\<open>x=\<one>\<close> in \<open>repr_independence\<close>.\<close>
  by sorry

lemma (in group) coset_join3:
  assumes "x \<in> carrier G" "subgroup H G" "x \<in> H"
  shows "x <# H = H"
  by sorry

lemma (in monoid) r_coset_subset_G:
  "\<lbrakk> H \<subseteq> carrier G; x \<in> carrier G \<rbrakk> \<Longrightarrow> H #> x \<subseteq> carrier G"
  by sorry

lemma (in group) rcosI:
  "\<lbrakk> h \<in> H; H \<subseteq> carrier G; x \<in> carrier G \<rbrakk> \<Longrightarrow> h \<otimes> x \<in> H #> x"
  by sorry

lemma (in group) rcosetsI:
     "\<lbrakk>H \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow> H #> x \<in> rcosets H"
  by sorry

lemma (in group) rcos_self:
  "\<lbrakk> x \<in> carrier G; subgroup H G \<rbrakk> \<Longrightarrow> x \<in> H #> x"
  by sorry

text (in group) \<open>Opposite of @{thm [source] "repr_independence"}\<close>
lemma (in group) repr_independenceD:
  assumes "subgroup H G" "y \<in> carrier G"
    and "H #> x = H #> y"
  shows "y \<in> H #> x"
  by sorry

text \<open>Elements of a right coset are in the carrier\<close>
lemma (in subgroup) elemrcos_carrier:
  assumes "group G" "a \<in> carrier G"
    and "a' \<in> H #> a"
  shows "a' \<in> carrier G"
  by sorry

lemma (in subgroup) rcos_const:
  assumes "group G" "h \<in> H"
  shows "H #> h = H"
  by sorry

lemma (in subgroup) rcos_module_imp:
  assumes "group G" "x \<in> carrier G"
    and "x' \<in> H #> x"
  shows "(x' \<otimes> inv x) \<in> H"
  by sorry

lemma (in subgroup) rcos_module_rev:
  assumes "group G" "x \<in> carrier G" "x' \<in> carrier G"
    and "(x' \<otimes> inv x) \<in> H"
  shows "x' \<in> H #> x"
  by sorry

text \<open>Module property of right cosets\<close>
lemma (in subgroup) rcos_module:
  assumes "group G" "x \<in> carrier G" "x' \<in> carrier G"
  shows "(x' \<in> H #> x) = (x' \<otimes> inv x \<in> H)"
  by sorry

text \<open>Right cosets are subsets of the carrier.\<close>
lemma (in subgroup) rcosets_carrier:
  assumes "group G" "X \<in> rcosets H"
  shows "X \<subseteq> carrier G"
  by sorry


text \<open>Multiplication of general subsets\<close>

lemma (in comm_group) mult_subgroups:
  assumes HG: "subgroup H G" and KG: "subgroup K G"
  shows "subgroup (H <#> K) G"
  by sorry

lemma (in subgroup) lcos_module_rev:
  assumes "group G" "x \<in> carrier G" "x' \<in> carrier G"
    and "(inv x \<otimes> x') \<in> H"
  shows "x' \<in> x <# H"
  by sorry


subsection \<open>Normal subgroups\<close>

lemma normal_imp_subgroup: "H \<lhd> G \<Longrightarrow> subgroup H G"
  by sorry

lemma (in group) normalI:
  "subgroup H G \<Longrightarrow> (\<forall>x \<in> carrier G. H #> x = x <# H) \<Longrightarrow> H \<lhd> G"
  by sorry

lemma (in normal) inv_op_closed1:
  assumes "x \<in> carrier G" and "h \<in> H"
  shows "(inv x) \<otimes> h \<otimes> x \<in> H"
  by sorry

lemma (in normal) inv_op_closed2:
  assumes "x \<in> carrier G" and "h \<in> H"
  shows "x \<otimes> h \<otimes> (inv x) \<in> H"
  by sorry

lemma (in comm_group) normal_iff_subgroup:
  "N \<lhd> G \<longleftrightarrow> subgroup N G"
  by sorry


text\<open>Alternative characterization of normal subgroups\<close>
lemma (in group) normal_inv_iff:
     "(N \<lhd> G) =
      (subgroup N G \<and> (\<forall>x \<in> carrier G. \<forall>h \<in> N. x \<otimes> h \<otimes> (inv x) \<in> N))"
      (is "_ = ?rhs")
  by sorry

corollary (in group) normal_invI:
  assumes "subgroup N G" and "\<And>x h. \<lbrakk> x \<in> carrier G; h \<in> N \<rbrakk> \<Longrightarrow> x \<otimes> h \<otimes> inv x \<in> N"
  shows "N \<lhd> G"
  by sorry

corollary (in group) normal_invE:
  assumes "N \<lhd> G"
  shows "subgroup N G" and "\<And>x h. \<lbrakk> x \<in> carrier G; h \<in> N \<rbrakk> \<Longrightarrow> x \<otimes> h \<otimes> inv x \<in> N"
  by sorry

lemma (in group) one_is_normal: "{\<one>} \<lhd> G"
  by sorry

text \<open>The intersection of two normal subgroups is, again, a normal subgroup.\<close>
lemma (in group) normal_subgroup_intersect:
  assumes "M \<lhd> G" and "N \<lhd> G" shows "M \<inter> N \<lhd> G"
  by sorry


text \<open>Being a normal subgroup is preserved by surjective homomorphisms.\<close>

lemma (in normal) surj_hom_normal_subgroup:
  assumes \<phi>: "group_hom G F \<phi>"
  assumes \<phi>surj: "\<phi> ` (carrier G) = carrier F"
  shows "(\<phi> ` H) \<lhd> F"
  by sorry

text \<open>Being a normal subgroup is preserved by group isomorphisms.\<close>
lemma iso_normal_subgroup:
  assumes \<phi>: "\<phi> \<in> iso G F" "group G" "group F" "H \<lhd> G"
  shows "(\<phi> ` H) \<lhd> F"
  by sorry

text \<open>The set product of two normal subgroups is a normal subgroup.\<close>
lemma (in group) setmult_lcos_assoc:
  "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> (x <# H) <#> K = x <# (H <#> K)"
  by sorry

subsection\<open>More Properties of Left Cosets\<close>

lemma (in group) l_repr_independence:
  assumes "y \<in> x <# H" "x \<in> carrier G" and HG: "subgroup H G"
  shows "x <# H = y <# H"
  by sorry

lemma (in group) lcos_m_assoc:
  "\<lbrakk> M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G \<rbrakk> \<Longrightarrow> g <# (h <# M) = (g \<otimes> h) <# M"
  by sorry

lemma (in group) lcos_mult_one: "M \<subseteq> carrier G \<Longrightarrow> \<one> <# M = M"
  by sorry

lemma (in group) l_coset_subset_G:
  "\<lbrakk> H \<subseteq> carrier G; x \<in> carrier G \<rbrakk> \<Longrightarrow> x <# H \<subseteq> carrier G"
  by sorry

lemma (in group) l_coset_carrier:
  "\<lbrakk> y \<in> x <# H; x \<in> carrier G; subgroup H G \<rbrakk> \<Longrightarrow> y \<in> carrier G"
  by sorry

lemma (in group) l_coset_swap:
  assumes "y \<in> x <# H" "x \<in> carrier G" "subgroup H G"
  shows "x \<in> y <# H"
  by sorry

lemma (in group) subgroup_mult_id:
  assumes "subgroup H G"
  shows "H <#> H = H"
  by sorry


subsubsection \<open>Set of Inverses of an \<open>r_coset\<close>.\<close>

lemma (in normal) rcos_inv:
  assumes x:     "x \<in> carrier G"
  shows "set_inv (H #> x) = H #> (inv x)"
  by sorry


subsubsection \<open>Theorems for \<open><#>\<close> with \<open>#>\<close> or \<open><#\<close>.\<close>

lemma (in group) setmult_rcos_assoc:
  "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow>
    H <#> (K #> x) = (H <#> K) #> x"
  by sorry

lemma (in group) rcos_assoc_lcos:
  "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow>
   (H #> x) <#> K = H <#> (x <# K)"
  by sorry

lemma (in normal) rcos_mult_step1:
  "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow>
   (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
  by sorry

lemma (in normal) rcos_mult_step2:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
  by sorry

lemma (in normal) rcos_mult_step3:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H <#> (H #> x)) #> y = H #> (x \<otimes> y)"
  by sorry

lemma (in normal) rcos_sum:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = H #> (x \<otimes> y)"
  by sorry

lemma (in normal) rcosets_mult_eq: "M \<in> rcosets H \<Longrightarrow> H <#> M = M"
  \<comment> \<open>generalizes \<open>subgroup_mult_id\<close>\<close>
  by sorry


subsubsection\<open>An Equivalence Relation\<close>

definition
  r_congruent :: "[('a,'b)monoid_scheme, 'a set] \<Rightarrow> ('a*'a)set"
    (\<open>(\<open>open_block notation=\<open>prefix rcong\<close>\<close>rcong\<index> _)\<close>)
  where "rcong\<^bsub>G\<^esub> H = {(x,y). x \<in> carrier G \<and> y \<in> carrier G \<and> inv\<^bsub>G\<^esub> x \<otimes>\<^bsub>G\<^esub> y \<in> H}"


lemma (in subgroup) equiv_rcong:
   assumes "group G"
   shows "equiv (carrier G) (rcong H)"
  by sorry

text\<open>Equivalence classes of \<open>rcong\<close> correspond to left cosets.
  Was there a mistake in the definitions? I'd have expected them to
  correspond to right cosets.\<close>

(* CB: This is correct, but subtle.
   We call H #> a the right coset of a relative to H.  According to
   Jacobson, this is what the majority of group theory literature does.
   He then defines the notion of congruence relation ~ over monoids as
   equivalence relation with a ~ a' & b ~ b' \<Longrightarrow> a*b ~ a'*b'.
   Our notion of right congruence induced by K: rcong K appears only in
   the context where K is a normal subgroup.  Jacobson doesn't name it.
   But in this context left and right cosets are identical.
*)

lemma (in subgroup) l_coset_eq_rcong:
  assumes "group G"
  assumes a: "a \<in> carrier G"
  shows "a <# H = (rcong H) `` {a}"
  by sorry


subsubsection\<open>Two Distinct Right Cosets are Disjoint\<close>

lemma (in group) rcos_equation:
  assumes "subgroup H G"
  assumes p: "ha \<otimes> a = h \<otimes> b" "a \<in> carrier G" "b \<in> carrier G" "h \<in> H" "ha \<in> H" "hb \<in> H"
  shows "hb \<otimes> a \<in> (\<Union>h\<in>H. {h \<otimes> b})"
  by sorry

lemma (in group) rcos_disjoint:
  assumes "subgroup H G"
  shows "pairwise disjnt (rcosets H)"
  by sorry


subsection \<open>Further lemmas for \<open>r_congruent\<close>\<close>

text \<open>The relation is a congruence\<close>

lemma (in normal) congruent_rcong:
  shows "congruent2 (rcong H) (rcong H) (\<lambda>a b. a \<otimes> b <# H)"
  by sorry


subsection \<open>Order of a Group and Lagrange's Theorem\<close>

definition
  order :: "('a, 'b) monoid_scheme \<Rightarrow> nat"
  where "order S = card (carrier S)"

lemma iso_same_order:
  assumes "\<phi> \<in> iso G H"
  shows "order G = order H"
  by sorry

lemma (in monoid) order_gt_0_iff_finite: "0 < order G \<longleftrightarrow> finite (carrier G)"
  by sorry

lemma (in group) order_one_triv_iff:
  shows "(order G = 1) = (carrier G = {\<one>})"
  by sorry

lemma (in group) rcosets_part_G:
  assumes "subgroup H G"
  shows "\<Union>(rcosets H) = carrier G"
  by sorry

lemma (in group) cosets_finite:
     "\<lbrakk>c \<in> rcosets H;  H \<subseteq> carrier G;  finite (carrier G)\<rbrakk> \<Longrightarrow> finite c"
  by sorry

text\<open>The next two lemmas support the proof of \<open>card_cosets_equal\<close>.\<close>
lemma (in group) inj_on_f:
  assumes "H \<subseteq> carrier G" and a: "a \<in> carrier G"
  shows "inj_on (\<lambda>y. y \<otimes> inv a) (H #> a)"
  by sorry

lemma (in group) inj_on_g:
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> a) H"
  by sorry

(* ************************************************************************** *)

lemma (in group) card_cosets_equal:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G"
  shows "\<exists>f. bij_betw f H R"
  by sorry

corollary (in group) card_rcosets_equal:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G"
  shows "card H = card R"
  by sorry

corollary (in group) rcosets_finite:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G" "finite H"
  shows "finite R"
  by sorry

(* ************************************************************************** *)

lemma (in group) rcosets_subset_PowG:
     "subgroup H G  \<Longrightarrow> rcosets H \<subseteq> Pow(carrier G)"
  by sorry

proposition (in group) lagrange_finite:
  assumes "finite(carrier G)" and HG: "subgroup H G"
  shows "card(rcosets H) * card(H) = order(G)"
  by sorry

theorem (in group) lagrange:
  assumes "subgroup H G"
  shows "card (rcosets H) * card H = order G"
  by sorry

text \<open>The cardinality of the right cosets of the trivial subgroup is the cardinality of the group itself:\<close>
corollary (in group) card_rcosets_triv:
  assumes "finite (carrier G)"
  shows "card (rcosets {\<one>}) = order G"
  by sorry

subsection \<open>Quotient Groups: Factorization of a Group\<close>

definition
  FactGroup :: "[('a,'b) monoid_scheme, 'a set] \<Rightarrow> ('a set) monoid" (infixl \<open>Mod\<close> 65)
    \<comment> \<open>Actually defined for groups rather than monoids\<close>
   where "FactGroup G H = \<lparr>carrier = rcosets\<^bsub>G\<^esub> H, mult = set_mult G, one = H\<rparr>"

lemma (in normal) setmult_closed:
     "\<lbrakk>K1 \<in> rcosets H; K2 \<in> rcosets H\<rbrakk> \<Longrightarrow> K1 <#> K2 \<in> rcosets H"
  by sorry

lemma (in normal) setinv_closed:
     "K \<in> rcosets H \<Longrightarrow> set_inv K \<in> rcosets H"
  by sorry

lemma (in normal) rcosets_assoc:
     "\<lbrakk>M1 \<in> rcosets H; M2 \<in> rcosets H; M3 \<in> rcosets H\<rbrakk>
      \<Longrightarrow> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)"
  by sorry

lemma (in subgroup) subgroup_in_rcosets:
  assumes "group G"
  shows "H \<in> rcosets H"
  by sorry

lemma (in normal) rcosets_inv_mult_group_eq:
     "M \<in> rcosets H \<Longrightarrow> set_inv M <#> M = H"
  by sorry

theorem (in normal) factorgroup_is_group: "group (G Mod H)"
  by sorry

lemma carrier_FactGroup: "carrier(G Mod N) = (\<lambda>x. r_coset G N x) ` carrier G"
  by sorry

lemma one_FactGroup [simp]: "one(G Mod N) = N"
  by sorry

lemma mult_FactGroup [simp]: "monoid.mult (G Mod N) = set_mult G"
  by sorry

lemma (in normal) inv_FactGroup:
  assumes "X \<in> carrier (G Mod H)"
  shows "inv\<^bsub>G Mod H\<^esub> X = set_inv X"
  by sorry

text\<open>The coset map is a homomorphism from \<^term>\<open>G\<close> to the quotient group
  \<^term>\<open>G Mod H\<close>\<close>
lemma (in normal) r_coset_hom_Mod:
  "(\<lambda>a. H #> a) \<in> hom G (G Mod H)"
  by sorry


lemma (in comm_group) set_mult_commute:
  assumes "N \<subseteq> carrier G" "x \<in> rcosets N" "y \<in> rcosets N"
  shows "x <#> y = y <#> x"
  by sorry

lemma (in comm_group) abelian_FactGroup:
  assumes "subgroup N G" shows "comm_group(G Mod N)"
  by sorry


lemma FactGroup_universal:
  assumes "h \<in> hom G H" "N \<lhd> G"
    and h: "\<And>x y. \<lbrakk>x \<in> carrier G; y \<in> carrier G; r_coset G N x = r_coset G N y\<rbrakk> \<Longrightarrow> h x = h y"
  obtains g
  where "g \<in> hom (G Mod N) H" "\<And>x. x \<in> carrier G \<Longrightarrow> g(r_coset G N x) = h x"
  by sorry


lemma (in normal) FactGroup_pow:
  fixes k::nat
  assumes "a \<in> carrier G"
  shows "pow (FactGroup G H) (r_coset G H a) k = r_coset G H (pow G a k)"
  by sorry

lemma (in normal) FactGroup_int_pow:
  fixes k::int
  assumes "a \<in> carrier G"
  shows "pow (FactGroup G H) (r_coset G H a) k = r_coset G H (pow G a k)"
  by sorry


subsection\<open>The First Isomorphism Theorem\<close>

text\<open>The quotient by the kernel of a homomorphism is isomorphic to the
  range of that homomorphism.\<close>

definition
  kernel :: "('a, 'm) monoid_scheme \<Rightarrow> ('b, 'n) monoid_scheme \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> 'a set"
    \<comment> \<open>the kernel of a homomorphism\<close>
  where "kernel G H h = {x. x \<in> carrier G \<and> h x = \<one>\<^bsub>H\<^esub>}"

lemma (in group_hom) subgroup_kernel: "subgroup (kernel G H h) G"
  by sorry

text\<open>The kernel of a homomorphism is a normal subgroup\<close>
lemma (in group_hom) normal_kernel: "(kernel G H h) \<lhd> G"
  by sorry

lemma iso_kernel_image:
  assumes "group G" "group H"
  shows "f \<in> iso G H \<longleftrightarrow> f \<in> hom G H \<and> kernel G H f = {\<one>\<^bsub>G\<^esub>} \<and> f ` carrier G = carrier H"
    (is "?lhs = ?rhs")
  by sorry


lemma (in group_hom) FactGroup_nonempty:
  assumes "X \<in> carrier (G Mod kernel G H h)"
  shows "X \<noteq> {}"
  by sorry


lemma (in group_hom) FactGroup_universal_kernel:
  assumes "N \<lhd> G" and h: "N \<subseteq> kernel G H h"
  obtains g where "g \<in> hom (G Mod N) H" "\<And>x. x \<in> carrier G \<Longrightarrow> g(r_coset G N x) = h x"
  by sorry

lemma (in group_hom) FactGroup_the_elem_mem:
  assumes X: "X \<in> carrier (G Mod (kernel G H h))"
  shows "the_elem (h`X) \<in> carrier H"
  by sorry

lemma (in group_hom) FactGroup_hom:
     "(\<lambda>X. the_elem (h`X)) \<in> hom (G Mod (kernel G H h)) H"
  by sorry


text\<open>Lemma for the following injectivity result\<close>
lemma (in group_hom) FactGroup_subset:
  assumes "g \<in> carrier G" "g' \<in> carrier G" "h g = h g'"
  shows "kernel G H h #> g \<subseteq> kernel G H h #> g'"
  by sorry

lemma (in group_hom) FactGroup_inj_on:
     "inj_on (\<lambda>X. the_elem (h ` X)) (carrier (G Mod kernel G H h))"
  by sorry

text\<open>If the homomorphism \<^term>\<open>h\<close> is onto \<^term>\<open>H\<close>, then so is the
homomorphism from the quotient group\<close>
lemma (in group_hom) FactGroup_onto:
  assumes h: "h ` carrier G = carrier H"
  shows "(\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h) = carrier H"
  by sorry


text\<open>If \<^term>\<open>h\<close> is a homomorphism from \<^term>\<open>G\<close> onto \<^term>\<open>H\<close>, then the
 quotient group \<^term>\<open>G Mod (kernel G H h)\<close> is isomorphic to \<^term>\<open>H\<close>.\<close>
theorem (in group_hom) FactGroup_iso_set:
  "h ` carrier G = carrier H
   \<Longrightarrow> (\<lambda>X. the_elem (h`X)) \<in> iso (G Mod (kernel G H h)) H"
  by sorry

corollary (in group_hom) FactGroup_iso :
  "h ` carrier G = carrier H
   \<Longrightarrow> (G Mod (kernel G H h))\<cong> H"
  by sorry


lemma (in group_hom) trivial_hom_iff: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "h ` (carrier G) = { \<one>\<^bsub>H\<^esub> } \<longleftrightarrow> kernel G H h = carrier G"
  by sorry

lemma (in group_hom) trivial_ker_imp_inj: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "kernel G H h = { \<one> }"
  shows "inj_on h (carrier G)"
  by sorry

lemma (in group_hom) inj_iff_trivial_ker:
  shows "inj_on h (carrier G) \<longleftrightarrow> kernel G H h = { \<one> }"
  by sorry

lemma (in group_hom) induced_group_hom':
  assumes "subgroup I G" shows "group_hom (G \<lparr> carrier := I \<rparr>) H h"
  by sorry

lemma (in group_hom) inj_on_subgroup_iff_trivial_ker:
  assumes "subgroup I G"
  shows "inj_on h I \<longleftrightarrow> kernel (G \<lparr> carrier := I \<rparr>) H h = { \<one> }"
  by sorry

lemma set_mult_hom:
  assumes "h \<in> hom G H" "I \<subseteq> carrier G" and "J \<subseteq> carrier G"
  shows "h ` (I <#>\<^bsub>G\<^esub> J) = (h ` I) <#>\<^bsub>H\<^esub> (h ` J)"
  by sorry

corollary coset_hom:
  assumes "h \<in> hom G H" "I \<subseteq> carrier G" "a \<in> carrier G"
  shows "h ` (a <#\<^bsub>G\<^esub> I) = h a <#\<^bsub>H\<^esub> (h ` I)" and "h ` (I #>\<^bsub>G\<^esub> a) = (h ` I) #>\<^bsub>H\<^esub> h a"
  by sorry

corollary (in group_hom) set_mult_ker_hom:
  assumes "I \<subseteq> carrier G"
  shows "h ` (I <#> (kernel G H h)) = h ` I" and "h ` ((kernel G H h) <#> I) = h ` I"
  by sorry

subsubsection\<open>Trivial homomorphisms\<close>

definition trivial_homomorphism where
 "trivial_homomorphism G H f \<equiv> f \<in> hom G H \<and> (\<forall>x \<in> carrier G. f x = one H)"

lemma trivial_homomorphism_kernel:
   "trivial_homomorphism G H f \<longleftrightarrow> f \<in> hom G H \<and> kernel G H f = carrier G"
  by sorry

lemma (in group) trivial_homomorphism_image:
   "trivial_homomorphism G H f \<longleftrightarrow> f \<in> hom G H \<and> f ` carrier G = {one H}"
  by sorry


subsection \<open>Image kernel theorems\<close>

lemma group_Int_image_ker:
  assumes f: "f \<in> hom G H" and g: "g \<in> hom H K" 
    and "inj_on (g \<circ> f) (carrier G)" "group G" "group H" "group K"
  shows "(f ` carrier G) \<inter> (kernel H K g) = {\<one>\<^bsub>H\<^esub>}"
  by sorry


lemma group_sum_image_ker:
  assumes f: "f \<in> hom G H" and g: "g \<in> hom H K" and eq: "(g \<circ> f) ` (carrier G) = carrier K"
     and "group G" "group H" "group K"
  shows "set_mult H (f ` carrier G) (kernel H K g) = carrier H" (is "?lhs = ?rhs")
  by sorry


lemma group_sum_ker_image:
  assumes f: "f \<in> hom G H" and g: "g \<in> hom H K" and eq: "(g \<circ> f) ` (carrier G) = carrier K"
     and "group G" "group H" "group K"
   shows "set_mult H (kernel H K g) (f ` carrier G) = carrier H" (is "?lhs = ?rhs")
  by sorry

lemma group_semidirect_sum_ker_image:
  assumes "(g \<circ> f) \<in> iso G K" "f \<in> hom G H" "g \<in> hom H K" "group G" "group H" "group K"
  shows "(kernel H K g) \<inter> (f ` carrier G) = {\<one>\<^bsub>H\<^esub>}"
        "kernel H K g <#>\<^bsub>H\<^esub> (f ` carrier G) = carrier H"
  by sorry

lemma group_semidirect_sum_image_ker:
  assumes f: "f \<in> hom G H" and g: "g \<in> hom H K" and iso: "(g \<circ> f) \<in> iso G K"
     and "group G" "group H" "group K"
   shows "(f ` carrier G) \<inter> (kernel H K g) = {\<one>\<^bsub>H\<^esub>}"
          "f ` carrier G <#>\<^bsub>H\<^esub> (kernel H K g) = carrier H"
  by sorry



subsection \<open>Factor Groups and Direct product\<close>

lemma (in group) DirProd_normal : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "H \<times> N \<lhd> G \<times>\<times> K"
  by sorry

lemma (in group) FactGroup_DirProd_multiplication_iso_set : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "(\<lambda> (X, Y). X \<times> Y) \<in> iso  ((G Mod H) \<times>\<times> (K Mod N)) (G \<times>\<times> K Mod H \<times> N)"
  by sorry

corollary (in group) FactGroup_DirProd_multiplication_iso_1 : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "  ((G Mod H) \<times>\<times> (K Mod N)) \<cong> (G \<times>\<times> K Mod H \<times> N)"
  by sorry

corollary (in group) FactGroup_DirProd_multiplication_iso_2 : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "(G \<times>\<times> K Mod H \<times> N) \<cong> ((G Mod H) \<times>\<times> (K Mod N))"
  by sorry

subsubsection "More Lemmas about set multiplication"

text \<open>A group multiplied by a subgroup stays the same\<close>
lemma (in group) set_mult_carrier_idem:
  assumes "subgroup H G"
  shows "(carrier G) <#> H = carrier G"
  by sorry

text \<open>Same lemma as above, but everything is included in a subgroup\<close>
lemma (in group) set_mult_subgroup_idem:
  assumes HG: "subgroup H G" and NG: "subgroup N (G \<lparr> carrier := H \<rparr>)"
  shows "H <#> N = H"
  by sorry

text \<open>A normal subgroup is commutative with set multiplication\<close>
lemma (in group) commut_normal:
  assumes "subgroup H G" and "N\<lhd>G"
  shows "H<#>N = N<#>H"
  by sorry

text \<open>Same lemma as above, but everything is included in a subgroup\<close>
lemma (in group) commut_normal_subgroup:
  assumes "subgroup H G" and "N \<lhd> (G\<lparr> carrier := H \<rparr>)"
    and "subgroup K (G \<lparr> carrier := H \<rparr>)"
  shows "K <#> N = N <#> K"
  by sorry


subsubsection "Lemmas about intersection and normal subgroups"
text \<open>Mostly by Jakob von Raumer\<close>

lemma (in group) normal_inter:
  assumes "subgroup H G"
    and "subgroup K G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
  shows "(H1\<inter>K)\<lhd>(G\<lparr>carrier:= (H\<inter>K)\<rparr>)"
  by sorry

lemma (in group) normal_Int_subgroup:
  assumes "subgroup H G"
    and "N \<lhd> G"
  shows "(N\<inter>H) \<lhd> (G\<lparr>carrier := H\<rparr>)"
  by sorry

lemma (in group) normal_restrict_supergroup:
  assumes "subgroup S G" "N \<lhd> G" "N \<subseteq> S"
  shows "N \<lhd> (G\<lparr>carrier := S\<rparr>)"
  by sorry

text \<open>A subgroup relation survives factoring by a normal subgroup.\<close>
lemma (in group) normal_subgroup_factorize:
  assumes "N \<lhd> G" and "N \<subseteq> H" and "subgroup H G"
  shows "subgroup (rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N) (G Mod N)"
  by sorry

text \<open>A normality relation survives factoring by a normal subgroup.\<close>
lemma (in group) normality_factorization:
  assumes NG: "N \<lhd> G" and NH: "N \<subseteq> H" and HG: "H \<lhd> G"
  shows "(rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N) \<lhd> (G Mod N)"
  by sorry

text \<open>Factorizing by the trivial subgroup is an isomorphism.\<close>
lemma (in group) trivial_factor_iso:
  shows "the_elem \<in> iso (G Mod {\<one>}) G"
  by sorry

text \<open>And the dual theorem to the previous one: Factorizing by the group itself gives the trivial group\<close>

lemma (in group) self_factor_iso:
  shows "(\<lambda>X. the_elem ((\<lambda>x. \<one>) ` X)) \<in> iso (G Mod (carrier G)) (G\<lparr> carrier := {\<one>} \<rparr>)"
  by sorry

text \<open>Factoring by a normal subgroups yields the trivial group iff the subgroup is the whole group.\<close>
lemma (in normal) fact_group_trivial_iff:
  assumes "finite (carrier G)"
  shows "(carrier (G Mod H) = {\<one>\<^bsub>G Mod H\<^esub>}) \<longleftrightarrow> (H = carrier G)"
  by sorry

text \<open>The union of all the cosets contained in a subgroup of a quotient group acts as a represenation for that subgroup.\<close>

lemma (in normal) factgroup_subgroup_union_char:
  assumes "subgroup A (G Mod H)"
  shows "(\<Union>A) = {x \<in> carrier G. H #> x \<in> A}"
  by sorry

lemma (in normal) factgroup_subgroup_union_subgroup:
  assumes "subgroup A (G Mod H)"
  shows "subgroup (\<Union>A) G"
  by sorry

lemma (in normal) factgroup_subgroup_union_normal:
  assumes "A \<lhd> (G Mod H)"
  shows "\<Union>A \<lhd> G"
  by sorry

lemma (in normal) factgroup_subgroup_union_factor:
  assumes "subgroup A (G Mod H)"
  shows "A = rcosets\<^bsub>G\<lparr>carrier := \<Union>A\<rparr>\<^esub> H"
  by sorry


section  \<open>Flattening the type of group carriers\<close>

text \<open>Flattening here means to convert the type of group elements from 'a set to 'a.
This is possible whenever the empty set is not an element of the group. By Jakob von Raumer\<close>


definition flatten where
  "flatten (G::('a set, 'b) monoid_scheme) rep = \<lparr>carrier=(rep ` (carrier G)),
      monoid.mult=(\<lambda> x y. rep ((the_inv_into (carrier G) rep x) \<otimes>\<^bsub>G\<^esub> (the_inv_into (carrier G) rep y))), 
      one=rep \<one>\<^bsub>G\<^esub> \<rparr>"

lemma flatten_set_group_hom:
  assumes group: "group G"
  assumes inj: "inj_on rep (carrier G)"
  shows "rep \<in> hom G (flatten G rep)"
  by sorry

lemma flatten_set_group:
  assumes "group G" "inj_on rep (carrier G)"
  shows "group (flatten G rep)"
  by sorry

lemma (in normal) flatten_set_group_mod_inj:
  shows "inj_on (\<lambda>U. SOME g. g \<in> U) (carrier (G Mod H))"
  by sorry

lemma (in normal) flatten_set_group_mod:
  shows "group (flatten (G Mod H) (\<lambda>U. SOME g. g \<in> U))"
  by sorry

lemma (in normal) flatten_set_group_mod_iso:
  shows "(\<lambda>U. SOME g. g \<in> U) \<in> iso (G Mod H) (flatten (G Mod H) (\<lambda>U. SOME g. g \<in> U))"
  by sorry

end
