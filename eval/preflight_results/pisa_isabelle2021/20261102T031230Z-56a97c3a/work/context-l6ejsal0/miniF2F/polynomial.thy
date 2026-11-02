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

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma mynat_add_S_left: "mynat_add (Nat_S n) m = Nat_S (mynat_add n m)"
  