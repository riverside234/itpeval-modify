theory comp_commute
  imports Main
begin
declare [[quick_and_dirty = true]]


definition myComp :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "myComp g f \<equiv> \<lambda>x. g (f x)"

definition myId :: "'a \<Rightarrow> 'a"
  where "myId \<equiv> \<lambda>x. x"



lemma comp_assoc:
  "myComp h (myComp g f) = myComp (myComp h g) f"
  sorry
lemma comp_id_l:
  "myComp myId f = f"
  sorry

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma comp_id_r:
  "myComp f myId = f"
  