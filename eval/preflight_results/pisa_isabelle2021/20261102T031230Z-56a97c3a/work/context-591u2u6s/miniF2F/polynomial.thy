theory polynomial
  imports Main
begin
declare [[quick_and_dirty = true]]







datatype mynat = Nat_O | Nat_S mynat

fun mynat_add :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
  "mynat_add Nat_O m = m"
| "mynat_add (Nat_S n') m = Nat_S (mynat_add n' m)"

lemma mynat_add_O_left: "mynat_add Nat_O m = m"
  sorry
lemma mynat_add_S_left: "mynat_add (Nat_S n) m = Nat_S (mynat_add n m)"
  sorry
inductive mynat_le :: "mynat \<Rightarrow> mynat \<Rightarrow> bool" where
  le_n : "mynat_le n n"
| le_S : "mynat_le n m \<Longrightarrow> mynat_le n (Nat_S m)"

lemma mynat_zero_le: "mynat_le Nat_O n"
  sorry

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma mynat_add_zero_r: "mynat_add n Nat_O = n"
  