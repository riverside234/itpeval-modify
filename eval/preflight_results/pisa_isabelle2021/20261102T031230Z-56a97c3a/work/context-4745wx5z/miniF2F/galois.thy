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
lemma mul_inv_r: "x \<noteq> zero_F \<Longrightarrow> x *F inv_F x = one_F"
  sorry


lemma add_cancel_l: "x +F y = x +F z \<Longrightarrow> y = z"
  sorry
lemma add_cancel_r: "y +F x = z +F x \<Longrightarrow> y = z"
  sorry
lemma mul_cancel_l: "x \<noteq> zero_F \<Longrightarrow> x *F y = x *F z \<Longrightarrow> y = z"
  sorry
lemma mul_cancel_r: "x \<noteq> zero_F \<Longrightarrow> y *F x = z *F x \<Longrightarrow> y = z"
  sorry
lemma inv_unique: "x \<noteq> zero_F \<Longrightarrow> x *F y = one_F \<Longrightarrow> y = inv_F x"
  sorry
lemma inv_involutive: "x \<noteq> zero_F \<Longrightarrow> inv_F (inv_F x) = x"
  sorry
end









locale tower =
  fixes S    :: "'p \<Rightarrow> bool"
    and mp   :: "'p \<Rightarrow> 'p"
    and splt :: "'p \<Rightarrow> bool"
  assumes scalar_tower : "\<And>p q. S p \<Longrightarrow> S (mp q) \<Longrightarrow> S q"
    and   map_solv     : "\<And>p. S p \<Longrightarrow> S (mp p)"
    and   splits_solv  : "\<And>p. splt p \<Longrightarrow> S p"
begin

lemma gal_isSolvable_tower:
  "S p \<Longrightarrow> S (mp q) \<Longrightarrow> S q"
  sorry

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma gal_isSolvable_double_tower:
  "S p \<Longrightarrow> S (mp q) \<Longrightarrow> S (mp r) \<Longrightarrow> S r"
  