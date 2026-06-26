(*  Title:       Tarski's geometry
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

section "Tarski's geometry"

theory Tarski
  imports Complex_Main Miscellany Metric
begin

subsection "The axioms"
text \<open>The axioms, and all theorems beginning with \emph{th}
  followed by a number, are based on corresponding axioms and
  theorems in \<^cite>\<open>"schwabhauser"\<close>.\<close>

locale tarski_first3 =
  fixes C :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"     (\<open>_ _ \<congruent> _ _\<close> [99,99,99,99] 50)
  assumes A1: "\<forall>a b. a b \<congruent> b a"
  and A2: "\<forall>a b p q r s. a b \<congruent> p q \<and> a b \<congruent> r s \<longrightarrow> p q \<congruent> r s"
  and A3: "\<forall>a b c. a b \<congruent> c c \<longrightarrow> a = b"

locale tarski_first5 = tarski_first3 +
  fixes B :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  assumes A4: "\<forall>q a b c. \<exists>x. B q a x \<and> a x \<congruent> b c"
  and A5: "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> B a b c \<and> B a' b' c'
                                               \<and> a b \<congruent> a' b' \<and> b c \<congruent> b' c' \<and> a d \<congruent> a' d' \<and> b d \<congruent> b' d'
                                       \<longrightarrow> c d \<congruent> c' d'"

locale tarski_absolute_space = tarski_first5 +
  assumes A6: "\<forall>a b. B a b a \<longrightarrow> a = b"
  and A7: "\<forall>a b c p q. B a p c \<and> B b q c \<longrightarrow> (\<exists>x. B p x b \<and> B q x a)"
  and A11: "\<forall>X Y. (\<exists>a. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B a x y)
                        \<longrightarrow> (\<exists>b. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B x b y)"

locale tarski_absolute = tarski_absolute_space +
  assumes A8: "\<exists>a b c. \<not> B a b c \<and> \<not> B b c a \<and> \<not> B c a b"
  and A9: "\<forall>p q a b c. p \<noteq> q \<and> a p \<congruent> a q \<and> b p \<congruent> b q \<and> c p \<congruent> c q
                             \<longrightarrow> B a b c \<or> B b c a \<or> B c a b"

locale tarski_space = tarski_absolute_space +
  assumes A10: "\<forall>a b c d t. B a d t \<and> B b d c \<and> a \<noteq> d 
                                    \<longrightarrow> (\<exists>x y. B a b x \<and> B a c y \<and> B x t y)"

locale tarski = tarski_absolute + tarski_space

subsection "Semimetric spaces satisfy the first three axioms"

context semimetric
begin
  definition smC :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" (\<open>_ _ \<congruent>\<^sub>s\<^sub>m _ _\<close> [99,99,99,99] 50)
    where [simp]: "a b \<congruent>\<^sub>s\<^sub>m c d \<equiv> dist a b = dist c d"
end

sublocale semimetric < tarski_first3 smC
proof
  from symm show "\<forall>a b. a b \<congruent>\<^sub>s\<^sub>m b a" by simp
  show "\<forall>a b p q r s. a b \<congruent>\<^sub>s\<^sub>m p q \<and> a b \<congruent>\<^sub>s\<^sub>m r s \<longrightarrow> p q \<congruent>\<^sub>s\<^sub>m r s" by simp
  show "\<forall>a b c. a b \<congruent>\<^sub>s\<^sub>m c c \<longrightarrow> a = b" by simp
qed

subsection "Some consequences of the first three axioms"

context tarski_first3
begin
  notation %invisible C (\<open>_ _ \<equiv> _ _\<close> [99,99,99,99] 50)
  lemma A1': "a b \<congruent> b a"
  by sorry

  lemma A2': "\<lbrakk>a b \<congruent> p q; a b \<congruent> r s\<rbrakk> \<Longrightarrow> p q \<congruent> r s"
  by sorry

  lemma A3': "a b \<congruent> c c \<Longrightarrow> a = b"
  by sorry

  theorem th2_1: "a b \<congruent> a b"
  by sorry

  theorem th2_2: "a b \<congruent> c d \<Longrightarrow> c d \<congruent> a b"
  by sorry

  theorem th2_3: "\<lbrakk>a b \<congruent> c d; c d \<congruent> e f\<rbrakk> \<Longrightarrow> a b \<congruent> e f"
  by sorry

  theorem th2_4: "a b \<congruent> c d \<Longrightarrow> b a \<congruent> c d"
  by sorry

  theorem th2_5: "a b \<congruent> c d \<Longrightarrow> a b \<congruent> d c"
  by sorry

  definition is_segment :: "'p set \<Rightarrow> bool" where
  "is_segment X \<equiv> \<exists>x y. X = {x, y}"

  definition segments :: "'p set set" where
  "segments = {X. is_segment X}"

  definition SC :: "'p set \<Rightarrow> 'p set \<Rightarrow> bool" where
  "SC X Y \<equiv> \<exists>w x y z. X = {w, x} \<and> Y = {y, z} \<and> w x \<congruent> y z"

  definition SC_rel :: "('p set \<times> 'p set) set" where
  "SC_rel = {(X, Y) | X Y. SC X Y}"

  lemma left_segment_congruence:
    assumes "{a, b} = {p, q}" and "p q \<congruent> c d"
    shows "a b \<congruent> c d"
  by sorry

  lemma right_segment_congruence:
    assumes "{c, d} = {p, q}" and "a b \<congruent> p q"
    shows "a b \<congruent> c d"
  by sorry

  lemma C_SC_equiv: "a b \<congruent> c d = SC {a, b} {c, d}"
  by sorry

  lemma SC_rel_subset: "SC_rel \<subseteq> segments \<times> segments"
  by sorry

  lemmas SC_refl = th2_1 [simplified]

  lemma SC_rel_refl: "refl_on segments SC_rel"
  by sorry

  lemma SC_sym:
    assumes "SC X Y"
    shows "SC Y X"
  by sorry

  lemma SC_sym': "SC X Y = SC Y X"
  by sorry

  lemma SC_rel_sym: "sym SC_rel"
  by sorry

  lemma SC_trans:
    assumes "SC X Y" and "SC Y Z"
    shows "SC X Z"
  by sorry

  lemma SC_rel_trans: "trans SC_rel"
  by sorry

  lemma A3_reversed:
    assumes "a a \<congruent> b c"
    shows "b = c"
  by sorry
  
  lemma equiv_segments_SC_rel: "equiv segments SC_rel"
  by sorry
    
end

subsection "Some consequences of the first five axioms"

context tarski_first5
begin
  lemma A4': "\<exists>x. B q a x \<and> a x \<congruent> b c"
  by sorry

  theorem th2_8: "a a \<congruent> b b"
  by sorry

  definition OFS :: "['p,'p,'p,'p,'p,'p,'p,'p] \<Rightarrow> bool" where
   "OFS a b c d a' b' c' d' \<equiv>
      B a b c \<and> B a' b' c' \<and> a b \<congruent> a' b' \<and> b c \<congruent> b' c' \<and> a d \<congruent> a' d' \<and> b d \<congruent> b' d'"

  lemma A5': "\<lbrakk>OFS a b c d a' b' c' d'; a \<noteq> b\<rbrakk> \<Longrightarrow> c d \<congruent> c' d'"
  by sorry

  theorem th2_11:
    assumes hypotheses:
      "B a b c"
      "B a' b' c'"
      "a b \<congruent> a' b'"
      "b c \<congruent> b' c'"
    shows "a c \<congruent> a' c'"
  by sorry

  lemma A4_unique:
    assumes "q \<noteq> a" and "B q a x" and "a x \<congruent> b c"
    and "B q a x'" and "a x' \<congruent> b c"
    shows "x = x'"
  by sorry

  theorem th2_12:
    assumes "q \<noteq> a"
    shows "\<exists>!x. B q a x \<and> a x \<congruent> b c"
  by sorry
end

subsection "Simple theorems about betweenness"

theorem (in tarski_first5) th3_1: "B a b b"
  by sorry

context tarski_absolute_space
begin
  lemma A6':
    assumes "B a b a"
    shows "a = b"
  by sorry
    
  lemma A7':
    assumes "B a p c" and "B b q c"
    shows "\<exists>x. B p x b \<and> B q x a"
  by sorry

  lemma A11':
    assumes "\<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B a x y"
    shows "\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B x b y"
  by sorry

  theorem th3_2:
    assumes "B a b c"
    shows "B c b a"
  by sorry

  theorem th3_4:
    assumes "B a b c" and "B b a c"
    shows "a = b"
  by sorry

  theorem th3_5_1:
    assumes "B a b d" and "B b c d"
    shows "B a b c"
  by sorry

  theorem th3_6_1:
    assumes "B a b c" and "B a c d"
    shows "B b c d"
  by sorry

  theorem th3_7_1:
    assumes "b \<noteq> c" and "B a b c" and "B b c d"
    shows "B a c d"
  by sorry

  theorem th3_7_2:
    assumes "b \<noteq> c" and "B a b c" and "B b c d"
    shows "B a b d"
  by sorry
end

subsection "Simple theorems about congruence and betweenness"

definition (in tarski_first5) Col :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "Col a b c \<equiv> B a b c \<or> B b c a \<or> B c a b"

end
