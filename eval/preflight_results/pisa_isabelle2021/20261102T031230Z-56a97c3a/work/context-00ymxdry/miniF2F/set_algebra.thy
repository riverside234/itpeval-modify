theory set_algebra
  imports Main
begin
declare [[quick_and_dirty = true]]


definition sUnion :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  where "sUnion A B \<equiv> \<lambda>x. A x \<or> B x"

definition sInter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  where "sInter A B \<equiv> \<lambda>x. A x \<and> B x"

definition sCompl :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  where "sCompl A \<equiv> \<lambda>x. \<not> A x"


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma inter_distrib_left:
  "\<forall>x. sInter A (sUnion B C) x \<longleftrightarrow> sUnion (sInter A B) (sInter A C) x"
  