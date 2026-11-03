(*  Title:      HOL/Algebra/Group.thy
    Author:     Clemens Ballarin, started 4 February 2003

Based on work by Florian Kammueller, L C Paulson and Markus Wenzel.
With additional contributions from Martin Baillon and Paulo Emílio de Vilhena.
*)

theory Group
imports Complete_Lattice "HOL-Library.FuncSet"
begin

section \<open>Monoids and Groups\<close>

subsection \<open>Definitions\<close>

text \<open>
  Definitions follow \<^cite>\<open>"Jacobson:1985"\<close>.
\<close>

record 'a monoid =  "'a partial_object" +
  mult    :: "['a, 'a] \<Rightarrow> 'a" (infixl \<open>\<otimes>\<index>\<close> 70)
  one     :: 'a (\<open>\<one>\<index>\<close>)

definition m_inv :: "('a, 'b) monoid_scheme => 'a => 'a"
  where "m_inv G x = (THE y. y \<in> carrier G \<and> x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> \<and> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)"

open_bundle m_inv_syntax
begin
notation m_inv  (\<open>(\<open>open_block notation=\<open>prefix inv\<close>\<close>inv\<index> _)\<close> [81] 80)
end

definition
  Units :: "_ => 'a set"
  \<comment> \<open>The set of invertible elements\<close>
  where "Units G = {y. y \<in> carrier G \<and> (\<exists>x \<in> carrier G. x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> \<and> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)}"

locale monoid =
  fixes G (structure)
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
      and m_assoc:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk>
          \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
      and one_closed [intro, simp]: "\<one> \<in> carrier G"
      and l_one [simp]: "x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
      and r_one [simp]: "x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x"

lemma monoidI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and r_one: "!!x. x \<in> carrier G ==> x \<otimes> \<one> = x"
  shows "monoid G"
  by sorry

lemma (in monoid) Units_closed [dest]:
  "x \<in> Units G ==> x \<in> carrier G"
  by sorry

lemma (in monoid) one_unique:
  assumes "u \<in> carrier G"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> u \<otimes> x = x"
  shows "u = \<one>"
  by sorry

lemma (in monoid) inv_unique:
  assumes eq: "y \<otimes> x = \<one>"  "x \<otimes> y' = \<one>"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "y' \<in> carrier G"
  shows "y = y'"
  by sorry

lemma (in monoid) Units_m_closed [simp, intro]:
  assumes x: "x \<in> Units G" and y: "y \<in> Units G"
  shows "x \<otimes> y \<in> Units G"
  by sorry

lemma (in monoid) Units_one_closed [intro, simp]:
  "\<one> \<in> Units G"
  by sorry

lemma (in monoid) Units_inv_closed [intro, simp]:
  "x \<in> Units G ==> inv x \<in> carrier G"
  by sorry

lemma (in monoid) Units_l_inv_ex:
  "x \<in> Units G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  by sorry

lemma (in monoid) Units_r_inv_ex:
  "x \<in> Units G ==> \<exists>y \<in> carrier G. x \<otimes> y = \<one>"
  by sorry

lemma (in monoid) Units_l_inv [simp]:
  "x \<in> Units G ==> inv x \<otimes> x = \<one>"
  by sorry

lemma (in monoid) Units_r_inv [simp]:
  "x \<in> Units G ==> x \<otimes> inv x = \<one>"
  by sorry

lemma (in monoid) inv_one [simp]:
  "inv \<one> = \<one>"
  by sorry

lemma (in monoid) Units_inv_Units [intro, simp]:
  "x \<in> Units G ==> inv x \<in> Units G"
  by sorry

lemma (in monoid) Units_l_cancel [simp]:
  "[| x \<in> Units G; y \<in> carrier G; z \<in> carrier G |] ==>
   (x \<otimes> y = x \<otimes> z) = (y = z)"
  by sorry

lemma (in monoid) Units_inv_inv [simp]:
  "x \<in> Units G ==> inv (inv x) = x"
  by sorry

lemma (in monoid) inv_inj_on_Units:
  "inj_on (m_inv G) (Units G)"
  by sorry

lemma (in monoid) Units_inv_comm:
  assumes inv: "x \<otimes> y = \<one>"
    and G: "x \<in> Units G"  "y \<in> Units G"
  shows "y \<otimes> x = \<one>"
  by sorry

lemma (in monoid) carrier_not_empty: "carrier G \<noteq> {}"
  by sorry

(* Jacobson defines submonoid here. *)
(* Jacobson defines the order of a monoid here. *)


subsection \<open>Groups\<close>

text \<open>
  A group is a monoid all of whose elements are invertible.
\<close>

locale group = monoid +
  assumes Units: "carrier G <= Units G"

lemma (in group) is_group [iff]: "group G" by (rule group_axioms)

lemma (in group) is_monoid [iff]: "monoid G"
  by sorry

theorem groupI:
  fixes G (structure)
  assumes m_closed [simp]:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed [simp]: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one [simp]: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "group G"
  by sorry

lemma (in monoid) group_l_invI:
  assumes l_inv_ex:
    "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "group G"
  by sorry

lemma (in group) Units_eq [simp]:
  "Units G = carrier G"
  by sorry

lemma (in group) inv_closed [intro, simp]:
  "x \<in> carrier G ==> inv x \<in> carrier G"
  by sorry

lemma (in group) l_inv_ex [simp]:
  "x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  by sorry

lemma (in group) r_inv_ex [simp]:
  "x \<in> carrier G ==> \<exists>y \<in> carrier G. x \<otimes> y = \<one>"
  by sorry

lemma (in group) l_inv [simp]:
  "x \<in> carrier G ==> inv x \<otimes> x = \<one>"
  by sorry


subsection \<open>Cancellation Laws and Basic Properties\<close>

lemma (in group) inv_eq_1_iff [simp]:
  assumes "x \<in> carrier G" shows "inv\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<longleftrightarrow> x = \<one>\<^bsub>G\<^esub>"
  by sorry

lemma (in group) r_inv [simp]:
  "x \<in> carrier G ==> x \<otimes> inv x = \<one>"
  by sorry

lemma (in group) right_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (y \<otimes> x = z \<otimes> x) = (y = z)"
  by sorry

lemma (in group) inv_inv [simp]:
  "x \<in> carrier G ==> inv (inv x) = x"
  by sorry

lemma (in group) inv_inj:
  "inj_on (m_inv G) (carrier G)"
  by sorry

lemma (in group) inv_mult_group:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv y \<otimes> inv x"
  by sorry

lemma (in group) inv_comm:
  "[| x \<otimes> y = \<one>; x \<in> carrier G; y \<in> carrier G |] ==> y \<otimes> x = \<one>"
  by sorry

lemma (in group) inv_equality:
     "[|y \<otimes> x = \<one>; x \<in> carrier G; y \<in> carrier G|] ==> inv x = y"
  by sorry

lemma (in group) inv_solve_left:
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> a = inv b \<otimes> c \<longleftrightarrow> c = b \<otimes> a"
  by sorry

lemma (in group) inv_solve_left':
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> inv b \<otimes> c = a \<longleftrightarrow> c = b \<otimes> a"
  by sorry

lemma (in group) inv_solve_right:
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> a = b \<otimes> inv c \<longleftrightarrow> b = a \<otimes> c"
  by sorry

lemma (in group) inv_solve_right':
  "\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> b \<otimes> inv c = a \<longleftrightarrow> b = a \<otimes> c"
  by sorry
  

subsection \<open>Power\<close>

consts
  pow :: "[('a, 'm) monoid_scheme, 'a, 'b::semiring_1] => 'a"  (infixr \<open>[^]\<index>\<close> 75)

overloading nat_pow == "pow :: [_, 'a, nat] => 'a"
begin
  definition "nat_pow G a n = rec_nat \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a) n"
end

lemma (in monoid) nat_pow_closed [intro, simp]:
  "x \<in> carrier G ==> x [^] (n::nat) \<in> carrier G"
  by sorry

lemma (in monoid) nat_pow_0 [simp]:
  "x [^] (0::nat) = \<one>"
  by sorry

lemma (in monoid) nat_pow_Suc [simp]:
  "x [^] (Suc n) = x [^] n \<otimes> x"
  by sorry

lemma (in monoid) nat_pow_one [simp]:
  "\<one> [^] (n::nat) = \<one>"
  by sorry

lemma (in monoid) nat_pow_mult:
  "x \<in> carrier G ==> x [^] (n::nat) \<otimes> x [^] m = x [^] (n + m)"
  by sorry

lemma (in monoid) nat_pow_comm:
  "x \<in> carrier G \<Longrightarrow> (x [^] (n::nat)) \<otimes> (x [^] (m :: nat)) = (x [^] m) \<otimes> (x [^] n)"
  by sorry

lemma (in monoid) nat_pow_Suc2:
  "x \<in> carrier G \<Longrightarrow> x [^] (Suc n) = x \<otimes> (x [^] n)"
  by sorry

lemma (in monoid) nat_pow_pow:
  "x \<in> carrier G ==> (x [^] n) [^] m = x [^] (n * m::nat)"
  by sorry

lemma (in monoid) nat_pow_consistent:
  "x [^] (n :: nat) = x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> n"
  by sorry

lemma nat_pow_0 [simp]: "x [^]\<^bsub>G\<^esub> (0::nat) = \<one>\<^bsub>G\<^esub>"
  by sorry

lemma nat_pow_Suc [simp]: "x [^]\<^bsub>G\<^esub> (Suc n) = (x [^]\<^bsub>G\<^esub> n)\<otimes>\<^bsub>G\<^esub> x"
  by sorry

lemma (in group) nat_pow_inv:
  assumes "x \<in> carrier G" shows "(inv x) [^] (i :: nat) = inv (x [^] i)"
  by sorry

overloading int_pow == "pow :: [_, 'a, int] => 'a"
begin
  definition "int_pow G a z =
   (let p = rec_nat \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a)
    in if z < 0 then inv\<^bsub>G\<^esub> (p (nat (-z))) else p (nat z))"
end

lemma int_pow_int: "x [^]\<^bsub>G\<^esub> (int n) = x [^]\<^bsub>G\<^esub> n"
  by sorry

lemma pow_nat:
  assumes "i\<ge>0"
  shows "x [^]\<^bsub>G\<^esub> nat i = x [^]\<^bsub>G\<^esub> i"
  by sorry

lemma int_pow_0 [simp]: "x [^]\<^bsub>G\<^esub> (0::int) = \<one>\<^bsub>G\<^esub>"
  by sorry

lemma int_pow_def2: "a [^]\<^bsub>G\<^esub> z =
   (if z < 0 then inv\<^bsub>G\<^esub> (a [^]\<^bsub>G\<^esub> (nat (-z))) else a [^]\<^bsub>G\<^esub> (nat z))"
  by sorry

lemma (in group) int_pow_one [simp]:
  "\<one> [^] (z::int) = \<one>"
  by sorry

lemma (in group) int_pow_closed [intro, simp]:
  "x \<in> carrier G ==> x [^] (i::int) \<in> carrier G"
  by sorry

lemma (in group) int_pow_1 [simp]:
  "x \<in> carrier G \<Longrightarrow> x [^] (1::int) = x"
  by sorry

lemma (in group) int_pow_neg:
  "x \<in> carrier G \<Longrightarrow> x [^] (-i::int) = inv (x [^] i)"
  by sorry

lemma (in group) int_pow_neg_int: "x \<in> carrier G \<Longrightarrow> x [^] -(int n) = inv (x [^] n)"
  by sorry

lemma (in group) int_pow_mult:
  assumes "x \<in> carrier G" shows "x [^] (i + j::int) = x [^] i \<otimes> x [^] j"
  by sorry

lemma (in group) int_pow_inv:
  "x \<in> carrier G \<Longrightarrow> (inv x) [^] (i :: int) = inv (x [^] i)"
  by sorry

lemma (in group) int_pow_pow:
  assumes "x \<in> carrier G"
  shows "(x [^] (n :: int)) [^] (m :: int) = x [^] (n * m :: int)"
  by sorry

lemma (in group) int_pow_diff:
  "x \<in> carrier G \<Longrightarrow> x [^] (n - m :: int) = x [^] n \<otimes> inv (x [^] m)"
  by sorry

lemma (in group) inj_on_multc: "c \<in> carrier G \<Longrightarrow> inj_on (\<lambda>x. x \<otimes> c) (carrier G)"
  by sorry

lemma (in group) inj_on_cmult: "c \<in> carrier G \<Longrightarrow> inj_on (\<lambda>x. c \<otimes> x) (carrier G)"
  by sorry


lemma (in monoid) group_commutes_pow:
  fixes n::nat
  shows "\<lbrakk>x \<otimes> y = y \<otimes> x; x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x [^] n \<otimes> y = y \<otimes> x [^] n"
  by sorry

lemma (in monoid) pow_mult_distrib:
  assumes eq: "x \<otimes> y = y \<otimes> x" and xy: "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] (n::nat) = x [^] n \<otimes> y [^] n"
  by sorry

lemma (in group) int_pow_mult_distrib:
  assumes eq: "x \<otimes> y = y \<otimes> x" and xy: "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] (i::int) = x [^] i \<otimes> y [^] i"
  by sorry

lemma (in group) pow_eq_div2:
  fixes m n :: nat
  assumes x_car: "x \<in> carrier G"
  assumes pow_eq: "x [^] m = x [^] n"
  shows "x [^] (m - n) = \<one>"
  by sorry

subsection \<open>Submonoids\<close>

locale submonoid = \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
    and one_closed [simp]: "\<one> \<in> H"

lemma (in submonoid) is_submonoid: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "submonoid H G" by (rule submonoid_axioms)

lemma (in submonoid) mem_carrier [simp]: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "x \<in> H \<Longrightarrow> x \<in> carrier G"
  by sorry

lemma (in submonoid) submonoid_is_monoid [intro]: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "monoid G"
  shows "monoid (G\<lparr>carrier := H\<rparr>)"
  by sorry

lemma submonoid_nonempty: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "~ submonoid {} G"
  by sorry

lemma (in submonoid) finite_monoid_imp_card_positive: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "finite (carrier G) ==> 0 < card H"
  by sorry


lemma (in monoid) monoid_incl_imp_submonoid : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "H \<subseteq> carrier G"
and "monoid (G\<lparr>carrier := H\<rparr>)"
shows "submonoid H G"
  by sorry

lemma (in monoid) inv_unique': \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows "\<lbrakk> x \<otimes> y = \<one>; y \<otimes> x = \<one> \<rbrakk> \<Longrightarrow> y = inv x"
  by sorry

lemma (in monoid) m_inv_monoid_consistent: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "x \<in> Units (G \<lparr> carrier := H \<rparr>)" and "submonoid H G"
  shows "inv\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> x = inv x"
  by sorry

subsection \<open>Subgroups\<close>

locale subgroup =
  fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
    and one_closed [simp]: "\<one> \<in> H"
    and m_inv_closed [intro,simp]: "x \<in> H \<Longrightarrow> inv x \<in> H"

lemma (in subgroup) is_subgroup:
  "subgroup H G" by (rule subgroup_axioms)

declare (in subgroup) group.intro [intro]

lemma (in subgroup) mem_carrier [simp]:
  "x \<in> H \<Longrightarrow> x \<in> carrier G"
  by sorry

lemma (in subgroup) subgroup_is_group [intro]:
  assumes "group G"
  shows "group (G\<lparr>carrier := H\<rparr>)"
  by sorry

lemma (in group) triv_subgroup: "subgroup {\<one>} G"
  by sorry

lemma subgroup_is_submonoid:
  assumes "subgroup H G" shows "submonoid H G"
  by sorry

lemma (in group) subgroup_Units:
  assumes "subgroup H G" shows "H \<subseteq> Units (G \<lparr> carrier := H \<rparr>)"
  by sorry

lemma (in group) m_inv_consistent [simp]:
  assumes "subgroup H G" "x \<in> H"
  shows "inv\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> x = inv x"
  by sorry

lemma (in group) int_pow_consistent: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup H G" "x \<in> H"
  shows "x [^] (n :: int) = x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> n"
  by sorry

text \<open>
  Since \<^term>\<open>H\<close> is nonempty, it contains some element \<^term>\<open>x\<close>.  Since
  it is closed under inverse, it contains \<open>inv x\<close>.  Since
  it is closed under product, it contains \<open>x \<otimes> inv x = \<one>\<close>.
\<close>

lemma (in group) one_in_subset:
  "\<lbrakk>H \<subseteq> carrier G; H \<noteq> {}; \<forall>a \<in> H. inv a \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<otimes> b \<in> H\<rbrakk>
   \<Longrightarrow> \<one> \<in> H"
  by sorry

text \<open>A characterization of subgroups: closed, non-empty subset.\<close>

lemma (in group) subgroupI:
  assumes subset: "H \<subseteq> carrier G" and non_empty: "H \<noteq> {}"
    and inv: "!!a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and mult: "!!a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
  shows "subgroup H G"
  by sorry

lemma (in group) subgroupE:
  assumes "subgroup H G"
  shows "H \<subseteq> carrier G"
    and "H \<noteq> {}"
    and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and "\<And>a b. \<lbrakk> a \<in> H; b \<in> H \<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
  by sorry

declare monoid.one_closed [iff] group.inv_closed [simp]
  monoid.l_one [simp] monoid.r_one [simp] group.inv_inv [simp]

lemma subgroup_nonempty:
  "\<not> subgroup {} G"
  by sorry

lemma (in subgroup) finite_imp_card_positive: "finite (carrier G) \<Longrightarrow> 0 < card H"
  by sorry

lemma (in subgroup) subgroup_is_submonoid : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "submonoid H G"
  by sorry

lemma (in group) submonoid_subgroupI : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "submonoid H G"
    and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
  shows "subgroup H G"
  by sorry

lemma (in group) group_incl_imp_subgroup: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "H \<subseteq> carrier G"
    and "group (G\<lparr>carrier := H\<rparr>)"
  shows "subgroup H G"
  by sorry


subsection \<open>Direct Products\<close>

definition
  DirProd :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<times> 'b) monoid" (infixr \<open>\<times>\<times>\<close> 80) where
  "G \<times>\<times> H =
    \<lparr>carrier = carrier G \<times> carrier H,
     mult = (\<lambda>(g, h) (g', h'). (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')),
     one = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)\<rparr>"

lemma DirProd_monoid:
  assumes "monoid G" and "monoid H"
  shows "monoid (G \<times>\<times> H)"
  by sorry


text\<open>Does not use the previous result because it's easier just to use auto.\<close>
lemma DirProd_group:
  assumes "group G" and "group H"
  shows "group (G \<times>\<times> H)"
  by sorry

lemma carrier_DirProd [simp]: "carrier (G \<times>\<times> H) = carrier G \<times> carrier H"
  by sorry

lemma one_DirProd [simp]: "\<one>\<^bsub>G \<times>\<times> H\<^esub> = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)"
  by sorry

lemma mult_DirProd [simp]: "(g, h) \<otimes>\<^bsub>(G \<times>\<times> H)\<^esub> (g', h') = (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')"
  by sorry

lemma mult_DirProd': "x \<otimes>\<^bsub>(G \<times>\<times> H)\<^esub> y = (fst x \<otimes>\<^bsub>G\<^esub> fst y, snd x \<otimes>\<^bsub>H\<^esub> snd y)"
  by sorry

lemma DirProd_assoc: "(G \<times>\<times> H \<times>\<times> I) = (G \<times>\<times> (H \<times>\<times> I))"
  by sorry

lemma inv_DirProd [simp]:
  assumes "group G" and "group H"
  assumes g: "g \<in> carrier G"
      and h: "h \<in> carrier H"
  shows "m_inv (G \<times>\<times> H) (g, h) = (inv\<^bsub>G\<^esub> g, inv\<^bsub>H\<^esub> h)"
  by sorry

lemma DirProd_subgroups :
  assumes "group G"
    and "subgroup H G"
    and "group K"
    and "subgroup I K"
  shows "subgroup (H \<times> I) (G \<times>\<times> K)"
  by sorry

subsection \<open>Homomorphisms (mono and epi) and Isomorphisms\<close>

definition
  hom :: "_ => _ => ('a => 'b) set" where
  "hom G H =
    {h. h \<in> carrier G \<rightarrow> carrier H \<and>
      (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y)}"

lemma homI:
  "\<lbrakk>\<And>x. x \<in> carrier G \<Longrightarrow> h x \<in> carrier H;
    \<And>x y. \<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y\<rbrakk> \<Longrightarrow> h \<in> hom G H"
  by sorry

lemma hom_carrier: "h \<in> hom G H \<Longrightarrow> h ` carrier G \<subseteq> carrier H"
  by sorry

lemma hom_in_carrier: "\<lbrakk>h \<in> hom G H; x \<in> carrier G\<rbrakk> \<Longrightarrow> h x \<in> carrier H"
  by sorry

lemma hom_compose:
  "\<lbrakk> f \<in> hom G H; g \<in> hom H I \<rbrakk> \<Longrightarrow> g \<circ> f \<in> hom G I"
  by sorry

lemma (in group) hom_restrict:
  assumes "h \<in> hom G H" and "\<And>g. g \<in> carrier G \<Longrightarrow> h g = t g" shows "t \<in> hom G H"
  by sorry

lemma (in group) hom_compose:
  "[|h \<in> hom G H; i \<in> hom H I|] ==> compose (carrier G) i h \<in> hom G I"
  by sorry

lemma (in group) restrict_hom_iff [simp]:
  "(\<lambda>x. if x \<in> carrier G then f x else g x) \<in> hom G H \<longleftrightarrow> f \<in> hom G H"
  by sorry

definition iso :: "_ => _ => ('a => 'b) set"
  where "iso G H = {h. h \<in> hom G H \<and> bij_betw h (carrier G) (carrier H)}"

definition is_iso :: "_ \<Rightarrow> _ \<Rightarrow> bool" (infixr \<open>\<cong>\<close> 60)
  where "G \<cong> H = (iso G H  \<noteq> {})"

definition mon where "mon G H = {f \<in> hom G H. inj_on f (carrier G)}"

definition epi where "epi G H = {f \<in> hom G H. f ` (carrier G) = carrier H}"

lemma isoI:
  "\<lbrakk>h \<in> hom G H; bij_betw h (carrier G) (carrier H)\<rbrakk> \<Longrightarrow> h \<in> iso G H"
  by sorry

lemma is_isoI: "h \<in> iso G H \<Longrightarrow> G \<cong> H"
  by sorry

lemma epi_iff_subset:
   "f \<in> epi G G' \<longleftrightarrow> f \<in> hom G G' \<and> carrier G' \<subseteq> f ` carrier G"
  by sorry

lemma iso_iff_mon_epi: "f \<in> iso G H \<longleftrightarrow> f \<in> mon G H \<and> f \<in> epi G H"
  by sorry

lemma iso_set_refl: "(\<lambda>x. x) \<in> iso G G"
  by sorry

lemma id_iso: "id \<in> iso G G"
  by sorry

corollary iso_refl [simp]: "G \<cong> G"
  by sorry

lemma iso_iff:
   "h \<in> iso G H \<longleftrightarrow> h \<in> hom G H \<and> h ` (carrier G) = carrier H \<and> inj_on h (carrier G)"
  by sorry

lemma iso_imp_homomorphism:
   "h \<in> iso G H \<Longrightarrow> h \<in> hom G H"
  by sorry

lemma trivial_hom:
   "group H \<Longrightarrow> (\<lambda>x. one H) \<in> hom G H"
  by sorry

lemma (in group) hom_eq:
  assumes "f \<in> hom G H" "\<And>x. x \<in> carrier G \<Longrightarrow> f' x = f x"
  shows "f' \<in> hom G H"
  by sorry

lemma (in group) iso_eq:
  assumes "f \<in> iso G H" "\<And>x. x \<in> carrier G \<Longrightarrow> f' x = f x"
  shows "f' \<in> iso G H"
  by sorry

lemma (in group) iso_set_sym:
  assumes "h \<in> iso G H"
  shows "inv_into (carrier G) h \<in> iso H G"
  by sorry

corollary (in group) iso_sym: "G \<cong> H \<Longrightarrow> H \<cong> G"
  by sorry

lemma iso_set_trans:
  "\<lbrakk>h \<in> Group.iso G H; i \<in> Group.iso H I\<rbrakk> \<Longrightarrow> i \<circ> h \<in> Group.iso G I"
  by sorry

corollary iso_trans [trans]: "\<lbrakk>G \<cong> H ; H \<cong> I\<rbrakk> \<Longrightarrow> G \<cong> I"
  by sorry

lemma iso_same_card: "G \<cong> H \<Longrightarrow> card (carrier G) = card (carrier H)"
  by sorry

lemma iso_finite: "G \<cong> H \<Longrightarrow> finite(carrier G) \<longleftrightarrow> finite(carrier H)"
  by sorry

lemma mon_compose:
   "\<lbrakk>f \<in> mon G H; g \<in> mon H K\<rbrakk> \<Longrightarrow> (g \<circ> f) \<in> mon G K"
  by sorry

lemma mon_compose_rev:
   "\<lbrakk>f \<in> hom G H; g \<in> hom H K; (g \<circ> f) \<in> mon G K\<rbrakk> \<Longrightarrow> f \<in> mon G H"
  by sorry

lemma epi_compose:
   "\<lbrakk>f \<in> epi G H; g \<in> epi H K\<rbrakk> \<Longrightarrow> (g \<circ> f) \<in> epi G K"
  by sorry

lemma epi_compose_rev:
   "\<lbrakk>f \<in> hom G H; g \<in> hom H K; (g \<circ> f) \<in> epi G K\<rbrakk> \<Longrightarrow> g \<in> epi H K"
  by sorry

lemma iso_compose_rev:
   "\<lbrakk>f \<in> hom G H; g \<in> hom H K; (g \<circ> f) \<in> iso G K\<rbrakk> \<Longrightarrow> f \<in> mon G H \<and> g \<in> epi H K"
  by sorry

lemma epi_iso_compose_rev:
  assumes "f \<in> epi G H" "g \<in> hom H K" "(g \<circ> f) \<in> iso G K"
  shows "f \<in> iso G H \<and> g \<in> iso H K"
  by sorry

lemma mon_left_invertible:
   "\<lbrakk>f \<in> hom G H; \<And>x. x \<in> carrier G \<Longrightarrow> g(f x) = x\<rbrakk> \<Longrightarrow> f \<in> mon G H"
  by sorry

lemma epi_right_invertible:
   "\<lbrakk>g \<in> hom H G; f \<in> carrier G \<rightarrow> carrier H; \<And>x. x \<in> carrier G \<Longrightarrow> g(f x) = x\<rbrakk> \<Longrightarrow> g \<in> epi H G"
  by sorry

lemma (in monoid) hom_imp_img_monoid: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "monoid (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)" (is "monoid ?h_img")
  by sorry

lemma (in group) hom_imp_img_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "group (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)" (is "group ?h_img")
  by sorry

lemma (in group) iso_imp_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "G \<cong> H" and "monoid H"
  shows "group H"
  by sorry

corollary (in group) iso_imp_img_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> iso G H"
  shows "group (H \<lparr> one := h \<one> \<rparr>)"
  by sorry

subsubsection \<open>HOL Light's concept of an isomorphism pair\<close>

definition group_isomorphisms
  where
 "group_isomorphisms G H f g \<equiv>
        f \<in> hom G H \<and> g \<in> hom H G \<and>
        (\<forall>x \<in> carrier G. g(f x) = x) \<and>
        (\<forall>y \<in> carrier H. f(g y) = y)"

lemma group_isomorphisms_sym: "group_isomorphisms G H f g \<Longrightarrow> group_isomorphisms H G g f"
  by sorry

lemma group_isomorphisms_imp_iso: "group_isomorphisms G H f g \<Longrightarrow> f \<in> iso G H"
  by sorry

lemma (in group) iso_iff_group_isomorphisms:
  "f \<in> iso G H \<longleftrightarrow> (\<exists>g. group_isomorphisms G H f g)"
  by sorry


subsubsection \<open>Involving direct products\<close>

lemma DirProd_commute_iso_set:
  shows "(\<lambda>(x,y). (y,x)) \<in> iso (G \<times>\<times> H) (H \<times>\<times> G)"
  by sorry

corollary DirProd_commute_iso :
"(G \<times>\<times> H) \<cong> (H \<times>\<times> G)"
  by sorry

lemma DirProd_assoc_iso_set:
  shows "(\<lambda>(x,y,z). (x,(y,z))) \<in> iso (G \<times>\<times> H \<times>\<times> I) (G \<times>\<times> (H \<times>\<times> I))"
  by sorry

lemma (in group) DirProd_iso_set_trans:
  assumes "g \<in> iso G G2"
    and "h \<in> iso H I"
  shows "(\<lambda>(x,y). (g x, h y)) \<in> iso (G \<times>\<times> H) (G2 \<times>\<times> I)"
  by sorry

corollary (in group) DirProd_iso_trans :
  assumes "G \<cong> G2" and "H \<cong> I"
  shows "G \<times>\<times> H \<cong> G2 \<times>\<times> I"
  by sorry

lemma hom_pairwise: "f \<in> hom G (DirProd H K) \<longleftrightarrow> (fst \<circ> f) \<in> hom G H \<and> (snd \<circ> f) \<in> hom G K"
  by sorry

lemma hom_paired:
   "(\<lambda>x. (f x,g x)) \<in> hom G (DirProd H K) \<longleftrightarrow> f \<in> hom G H \<and> g \<in> hom G K"
  by sorry

lemma hom_paired2:
  assumes "group G" "group H"
  shows "(\<lambda>(x,y). (f x,g y)) \<in> hom (DirProd G H) (DirProd G' H') \<longleftrightarrow> f \<in> hom G G' \<and> g \<in> hom H H'"
  by sorry

lemma iso_paired2:
  assumes "group G" "group H"
  shows "(\<lambda>(x,y). (f x,g y)) \<in> iso (DirProd G H) (DirProd G' H') \<longleftrightarrow> f \<in> iso G G' \<and> g \<in> iso H H'"
  by sorry

lemma hom_of_fst:
  assumes "group H"
  shows "(f \<circ> fst) \<in> hom (DirProd G H) K \<longleftrightarrow> f \<in> hom G K"
  by sorry

lemma hom_of_snd:
  assumes "group G"
  shows "(f \<circ> snd) \<in> hom (DirProd G H) K \<longleftrightarrow> f \<in> hom H K"
  by sorry


subsection\<open>The locale for a homomorphism between two groups\<close>

text\<open>Basis for homomorphism proofs: we assume two groups \<^term>\<open>G\<close> and
  \<^term>\<open>H\<close>, with a homomorphism \<^term>\<open>h\<close> between them\<close>
locale group_hom = G?: group G + H?: group H for G (structure) and H (structure) +
  fixes h
  assumes homh [simp]: "h \<in> hom G H"

declare group_hom.homh [simp]

lemma (in group_hom) hom_mult [simp]:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y"
  by sorry

lemma (in group_hom) hom_closed [simp]:
  "x \<in> carrier G ==> h x \<in> carrier H"
  by sorry

lemma (in group_hom) one_closed: "h \<one> \<in> carrier H"
  by sorry

lemma (in group_hom) hom_one [simp]: "h \<one> = \<one>\<^bsub>H\<^esub>"
  by sorry

lemma hom_one:
  assumes "h \<in> hom G H" "group G" "group H"
  shows "h (one G) = one H"
  by sorry

lemma hom_mult:
  "\<lbrakk>h \<in> hom G H; x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y"
  by sorry

lemma (in group_hom) inv_closed [simp]:
  "x \<in> carrier G ==> h (inv x) \<in> carrier H"
  by sorry

lemma (in group_hom) hom_inv [simp]:
  assumes "x \<in> carrier G" shows "h (inv x) = inv\<^bsub>H\<^esub> (h x)"
  by sorry

lemma (in group) int_pow_is_hom: \<^marker>\<open>contributor \<open>Joachim Breitner\<close>\<close>
  "x \<in> carrier G \<Longrightarrow> (([^]) x) \<in> hom \<lparr> carrier = UNIV, mult = (+), one = 0::int \<rparr> G "
  by sorry

lemma (in group_hom) img_is_subgroup: "subgroup (h ` (carrier G)) H" \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  by sorry

lemma (in group_hom) subgroup_img_is_subgroup: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup I G"
  shows "subgroup (h ` I) H"
  by sorry

lemma (in subgroup) iso_subgroup: \<^marker>\<open>contributor \<open>Jakob von Raumer\<close>\<close>
  assumes "group G" "group F"
  assumes "\<phi> \<in> iso G F"
  shows "subgroup (\<phi> ` H) F"
  by sorry

lemma (in group_hom) induced_group_hom: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup I G"
  shows "group_hom (G \<lparr> carrier := I \<rparr>) (H \<lparr> carrier := h ` I \<rparr>) h"
  by sorry

text \<open>An isomorphism restricts to an isomorphism of subgroups.\<close>

lemma iso_restrict:
  assumes "\<phi> \<in> iso G F"
  assumes groups: "group G" "group F"
  assumes HG: "subgroup H G"
  shows "(restrict \<phi> H) \<in> iso (G\<lparr>carrier := H\<rparr>) (F\<lparr>carrier := \<phi> ` H\<rparr>)"
  by sorry

lemma (in group) canonical_inj_is_hom: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup H G"
  shows "group_hom (G \<lparr> carrier := H \<rparr>) G id"
  by sorry

lemma (in group_hom) hom_nat_pow: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "x \<in> carrier G \<Longrightarrow> h (x [^] (n :: nat)) = (h x) [^]\<^bsub>H\<^esub> n"
  by sorry

lemma (in group_hom) hom_int_pow: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "x \<in> carrier G \<Longrightarrow> h (x [^] (n :: int)) = (h x) [^]\<^bsub>H\<^esub> n"
  by sorry

lemma hom_nat_pow:
  "\<lbrakk>h \<in> hom G H; x \<in> carrier G; group G; group H\<rbrakk> \<Longrightarrow> h (x [^]\<^bsub>G\<^esub> (n :: nat)) = (h x) [^]\<^bsub>H\<^esub> n"
  by sorry

lemma hom_int_pow:
  "\<lbrakk>h \<in> hom G H; x \<in> carrier G; group G; group H\<rbrakk> \<Longrightarrow> h (x [^]\<^bsub>G\<^esub> (n :: int)) = (h x) [^]\<^bsub>H\<^esub> n"
  by sorry

subsection \<open>Commutative Structures\<close>

text \<open>
  Naming convention: multiplicative structures that are commutative
  are called \emph{commutative}, additive structures are called
  \emph{Abelian}.
\<close>

locale comm_monoid = monoid +
  assumes m_comm: "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"

lemma (in comm_monoid) m_lcomm:
  "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk> \<Longrightarrow>
   x \<otimes> (y \<otimes> z) = y \<otimes> (x \<otimes> z)"
  by sorry

lemmas (in comm_monoid) m_ac = m_assoc m_comm m_lcomm

lemma comm_monoidI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_monoid G"
  by sorry

lemma (in monoid) monoid_comm_monoidI:
  assumes m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_monoid G"
  by sorry

lemma (in comm_monoid) submonoid_is_comm_monoid :
  assumes "submonoid H G"
  shows "comm_monoid (G\<lparr>carrier := H\<rparr>)"
  by sorry

locale comm_group = comm_monoid + group

lemma (in group) group_comm_groupI:
  assumes m_comm: "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_group G"
  by sorry

lemma comm_groupI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "comm_group G"
  by sorry

lemma comm_groupE:
  fixes G (structure)
  assumes "comm_group G"
  shows "\<And>x y. \<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
    and "\<one> \<in> carrier G"
    and "\<And>x y z. \<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and "\<And>x y. \<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  by sorry

lemma (in comm_group) inv_mult:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv x \<otimes> inv y"
  by sorry

lemma (in comm_monoid) nat_pow_distrib:
  fixes n::nat
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] n = x [^] n \<otimes> y [^] n"
  by sorry

lemma (in comm_group) int_pow_distrib:
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] (i::int) = x [^] i \<otimes> y [^] i"
  by sorry

lemma (in comm_monoid) hom_imp_img_comm_monoid: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "comm_monoid (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)" (is "comm_monoid ?h_img")
  by sorry

lemma (in comm_group) hom_group_mult:
  assumes "f \<in> hom H G" "g \<in> hom H G"
 shows "(\<lambda>x. f x \<otimes>\<^bsub>G\<^esub> g x) \<in> hom H G"
  by sorry

lemma (in comm_group) hom_imp_img_comm_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "comm_group (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)"
  by sorry

lemma (in comm_group) iso_imp_img_comm_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> iso G H"
  shows "comm_group (H \<lparr> one := h \<one>\<^bsub>G\<^esub> \<rparr>)"
  by sorry

lemma (in comm_group) iso_imp_comm_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "G \<cong> H" "monoid H"
  shows "comm_group H"
  by sorry

(*A subgroup of a subgroup is a subgroup of the group*)
lemma (in group) incl_subgroup:
  assumes "subgroup J G"
    and "subgroup I (G\<lparr>carrier:=J\<rparr>)"
  shows "subgroup I G" unfolding subgroup_def
  by sorry

(*A subgroup included in another subgroup is a subgroup of the subgroup*)
lemma (in group) subgroup_incl:
  assumes "subgroup I G" and "subgroup J G" and "I \<subseteq> J"
  shows "subgroup I (G \<lparr> carrier := J \<rparr>)"
  by sorry


subsection \<open>The Lattice of Subgroups of a Group\<close>

text_raw \<open>\label{sec:subgroup-lattice}\<close>

theorem (in group) subgroups_partial_order:
  "partial_order \<lparr>carrier = {H. subgroup H G}, eq = (=), le = (\<subseteq>)\<rparr>"
  by sorry

lemma (in group) subgroup_self:
  "subgroup (carrier G) G"
  by sorry

lemma (in group) subgroup_imp_group:
  "subgroup H G ==> group (G\<lparr>carrier := H\<rparr>)"
  by sorry

lemma (in group) subgroup_mult_equality:
  "\<lbrakk> subgroup H G; h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow>  h1 \<otimes>\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> h2 = h1 \<otimes> h2"
  by sorry

theorem (in group) subgroups_Inter:
  assumes subgr: "(\<And>H. H \<in> A \<Longrightarrow> subgroup H G)"
    and not_empty: "A \<noteq> {}"
  shows "subgroup (\<Inter>A) G"
  by sorry

lemma (in group) subgroups_Inter_pair :
  assumes "subgroup I G" "subgroup J G" shows "subgroup (I\<inter>J) G" 
  by sorry

theorem (in group) subgroups_complete_lattice:
  "complete_lattice \<lparr>carrier = {H. subgroup H G}, eq = (=), le = (\<subseteq>)\<rparr>"
    (is "complete_lattice ?L")
  by sorry

subsection\<open>The units in any monoid give rise to a group\<close>

text \<open>Thanks to Jeremy Avigad. The file Residues.thy provides some infrastructure to use
  facts about the unit group within the ring locale.
\<close>

definition units_of :: "('a, 'b) monoid_scheme \<Rightarrow> 'a monoid"
  where "units_of G =
    \<lparr>carrier = Units G, Group.monoid.mult = Group.monoid.mult G, one  = one G\<rparr>"

lemma (in monoid) units_group: "group (units_of G)"
  by sorry

lemma (in comm_monoid) units_comm_group: "comm_group (units_of G)"
  by sorry

lemma units_of_carrier: "carrier (units_of G) = Units G"
  by sorry

lemma units_of_mult: "mult (units_of G) = mult G"
  by sorry

lemma units_of_one: "one (units_of G) = one G"
  by sorry

lemma (in monoid) units_of_inv:
  assumes "x \<in> Units G"
  shows "m_inv (units_of G) x = m_inv G x"
  by sorry

lemma units_of_units [simp] : "Units (units_of G) = Units G"
  by sorry

lemma (in group) surj_const_mult: "a \<in> carrier G \<Longrightarrow> (\<lambda>x. a \<otimes> x) ` carrier G = carrier G"
  by sorry

lemma (in group) l_cancel_one [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x \<otimes> a = x \<longleftrightarrow> a = one G"
  by sorry

lemma (in group) r_cancel_one [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> a \<otimes> x = x \<longleftrightarrow> a = one G"
  by sorry

lemma (in group) l_cancel_one' [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x = x \<otimes> a \<longleftrightarrow> a = one G"
  by sorry

lemma (in group) r_cancel_one' [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x = a \<otimes> x \<longleftrightarrow> a = one G"
  by sorry

declare pow_nat [simp] (*causes looping if added above, especially with int_pow_def2*)

end
