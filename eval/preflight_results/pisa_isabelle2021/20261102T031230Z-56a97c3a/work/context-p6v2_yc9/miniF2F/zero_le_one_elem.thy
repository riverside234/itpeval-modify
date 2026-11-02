theory zero_le_one_elem
  imports Main
begin
declare [[quick_and_dirty = true]]


locale zero_le_one_setup =
  fixes decEq      :: "'m \<Rightarrow> 'm \<Rightarrow> bool"
    and zero       :: "'a"
    and one        :: "'a"
    and le         :: "'a \<Rightarrow> 'a \<Rightarrow> bool"   (infix "\<preceq>" 50)
    and le_antisym :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes le_refl      : "\<And>x. x \<preceq> x"
    and   le_trans     : "\<And>x y z. x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
    and   zero_le_one  : "zero \<preceq> one"
    and   zero_le_zero : "zero \<preceq> zero"
    and   le_antisym   : "\<And>x y. x \<preceq> y \<Longrightarrow> y \<preceq> x \<Longrightarrow> x = y"
begin

definition One_matrix :: "'m \<Rightarrow> 'm \<Rightarrow> 'a"
  where "One_matrix i j \<equiv> if decEq i j then one else zero"

definition Zero_matrix :: "'m \<Rightarrow> 'm \<Rightarrow> 'a"
  where "Zero_matrix \<equiv> \<lambda>_ _. zero"

definition matrix_le :: "('m \<Rightarrow> 'm \<Rightarrow> 'a) \<Rightarrow> ('m \<Rightarrow> 'm \<Rightarrow> 'a) \<Rightarrow> bool"
  where "matrix_le A B \<equiv> \<forall>i j. A i j \<preceq> B i j"

definition matrix_eq :: "('m \<Rightarrow> 'm \<Rightarrow> 'a) \<Rightarrow> ('m \<Rightarrow> 'm \<Rightarrow> 'a) \<Rightarrow> bool"
  where "matrix_eq A B \<equiv> \<forall>i j. A i j = B i j"

lemma zero_le_one_elem: "zero \<preceq> One_matrix i j"
  sorry
lemma Zero_le_One_matrix: "matrix_le Zero_matrix One_matrix"
  sorry

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma matrix_le_refl: "matrix_le A A"
  