theory galois
  imports Main
begin
declare [[quick_and_dirty = true]]






locale field_like =
  fixes zero_F one_F :: "'f"
    and add_F :: "'f \<Rightarrow> 'f \<Rightarrow> 'f"  (infixl "+F" 65)
    and mul_F :: "'f \<Rightarrow> 'f \<Rightarrow> 'f"  (infixl "*F" 70)
    and opp_F :: "'f \<Rightarrow> 'f"
    and inv_F :: "'f \<Rightarrow> 'f"
  assumes add_comm    : "\<And>x y. x +F y = y +F x"
    and   add_assoc   : "\<And>x y z. (x +F y) +F z = x +F (y +F z)"
    and   add_zero    : "\<And>x. x +F zero_F = x"
    and   add_inv_l   : "\<And>x. opp_F x +F x = zero_F"
    and   mul_comm    : "\<And>x y. x *F y = y *F x"
    and   mul_assoc   : "\<And>x y z. (x *F y) *F z = x *F (y *F z)"
    and   mul_one_l   : "\<And>x. one_F *F x = x"
    and   mul_inv_l   : "\<And>x. x \<noteq> zero_F \<Longrightarrow> inv_F x *F x = one_F"
    and   distrib_l   : "\<And>x y z. x *F (y +F z) = (x *F y) +F (x *F z)"
    and   zero_neq_one: "zero_F \<noteq> one_F"
    and   inv_nonzero : "\<And>x. x \<noteq> zero_F \<Longrightarrow> inv_F x \<noteq> zero_F"
begin


lemma zero_add: "zero_F +F x = x"
  sorry
lemma mul_one_r: "x *F one_F = x"
  sorry

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma mul_inv_r: "x \<noteq> zero_F \<Longrightarrow> x *F inv_F x = one_F"
  