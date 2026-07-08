theory galois
  imports Main
begin





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
  by (simp add: add_comm add_zero)

lemma mul_one_r: "x *F one_F = x"
  by (simp add: mul_comm mul_one_l)

lemma mul_inv_r: "x \<noteq> zero_F \<Longrightarrow> x *F inv_F x = one_F"
proof -
  assume hx: "x \<noteq> zero_F"
  have "x *F inv_F x = inv_F x *F x" by (rule mul_comm)
  also have "\<dots> = one_F"             by (rule mul_inv_l[OF hx])
  finally show ?thesis .
qed



lemma add_cancel_l: "x +F y = x +F z \<Longrightarrow> y = z"
proof -
  assume H: "x +F y = x +F z"
  have "y = opp_F x +F (x +F y)"
    by (simp add: add_assoc [symmetric] add_inv_l zero_add)
  also have "\<dots> = opp_F x +F (x +F z)" using H by simp
  also have "\<dots> = z"
    by (simp add: add_assoc [symmetric] add_inv_l zero_add)
  finally show ?thesis .
qed

lemma add_cancel_r: "y +F x = z +F x \<Longrightarrow> y = z"
proof -
  assume H: "y +F x = z +F x"
  have "x +F y = x +F z" by (metis H add_comm)
  then show ?thesis by (rule add_cancel_l)
qed

lemma mul_cancel_l: "x \<noteq> zero_F \<Longrightarrow> x *F y = x *F z \<Longrightarrow> y = z"
proof -
  assume hx: "x \<noteq> zero_F" and H: "x *F y = x *F z"
  have "y = one_F *F y"                  by (simp add: mul_one_l)
  also have "\<dots> = (inv_F x *F x) *F y"  by (simp add: mul_inv_l hx)
  also have "\<dots> = inv_F x *F (x *F y)"  by (simp add: mul_assoc)
  also have "\<dots> = inv_F x *F (x *F z)"  using H by simp
  also have "\<dots> = (inv_F x *F x) *F z"  by (simp add: mul_assoc)
  also have "\<dots> = one_F *F z"           by (simp add: mul_inv_l hx)
  also have "\<dots> = z"                    by (simp add: mul_one_l)
  finally show ?thesis .
qed

lemma mul_cancel_r: "x \<noteq> zero_F \<Longrightarrow> y *F x = z *F x \<Longrightarrow> y = z"
proof -
  assume hx: "x \<noteq> zero_F" and H: "y *F x = z *F x"
  have "x *F y = x *F z" by (metis H mul_comm)
  then show ?thesis by (rule mul_cancel_l[OF hx])
qed

lemma inv_unique: "x \<noteq> zero_F \<Longrightarrow> x *F y = one_F \<Longrightarrow> y = inv_F x"
proof -
  assume hx: "x \<noteq> zero_F" and H: "x *F y = one_F"
  have "y = one_F *F y"                 by (simp add: mul_one_l)
  also have "\<dots> = (inv_F x *F x) *F y" by (simp add: mul_inv_l hx)
  also have "\<dots> = inv_F x *F (x *F y)" by (simp add: mul_assoc)
  also have "\<dots> = inv_F x *F one_F"    using H by simp
  also have "\<dots> = inv_F x"             by (simp add: mul_one_r)
  finally show ?thesis .
qed

lemma inv_involutive: "x \<noteq> zero_F \<Longrightarrow> inv_F (inv_F x) = x"
proof -
  assume hx: "x \<noteq> zero_F"
  have "x = inv_F (inv_F x)"
    using inv_unique[OF inv_nonzero[OF hx] mul_inv_l[OF hx]] .
  then show ?thesis by simp
qed

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
  by (rule scalar_tower)

lemma gal_isSolvable_double_tower:
  "S p \<Longrightarrow> S (mp q) \<Longrightarrow> S (mp r) \<Longrightarrow> S r"
  by (blast intro: scalar_tower)

lemma gal_isSolvable_triple_tower:
  "S p \<Longrightarrow> S (mp q) \<Longrightarrow> S (mp r) \<Longrightarrow> S (mp s) \<Longrightarrow> S s"
  by (blast intro: scalar_tower)

lemma gal_isSolvable_quadruple_tower:
  "S p \<Longrightarrow> S (mp q) \<Longrightarrow> S (mp r) \<Longrightarrow> S (mp s) \<Longrightarrow> S (mp t) \<Longrightarrow> S t"
  by (blast intro: scalar_tower)

lemma gal_isSolvable_map_poly:
  "S p \<Longrightarrow> S (mp p)"
  by (rule map_solv)

lemma gal_isSolvable_of_split:
  "splt p \<Longrightarrow> S p"
  by (rule splits_solv)

lemma gal_isSolvable_split_tower:
  "splt q \<Longrightarrow> S q"
  by (rule splits_solv)

lemma gal_isSolvable_two_step_map:
  "S p \<Longrightarrow> S (mp (mp p))"
  by (blast intro: map_solv)

lemma gal_isSolvable_three_step_map:
  "S p \<Longrightarrow> S (mp (mp (mp p)))"
  by (blast intro: map_solv)

lemma gal_isSolvable_map_poly_comp:
  "S p \<Longrightarrow> S (mp (mp p))"
  by (blast intro: map_solv)

lemma gal_isSolvable_mutual_split:
  "splt p \<Longrightarrow> splt q \<Longrightarrow> S p \<and> S q"
  by (blast intro: splits_solv)

lemma gal_isSolvable_map_after_split:
  "splt p \<Longrightarrow> S (mp p)"
  by (blast intro: splits_solv map_solv)

lemma gal_isSolvable_tower_split:
  "splt q \<Longrightarrow> S (mp r) \<Longrightarrow> S r"
  by (blast intro: scalar_tower splits_solv)

end

end
