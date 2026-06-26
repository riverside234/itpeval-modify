theory integral_comp_neg_Iic
  imports Main
begin

locale integrals_setup =
  fixes zero one  :: "'r"
    and add       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "+R" 65)
    and opp       :: "'r \<Rightarrow> 'r"
    and mul       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "*R" 70)
    and leR       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "\<le>R" 50)
    and ltR       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "<R" 50)
    and absR      :: "'r \<Rightarrow> 'r"
    and sigma     :: "('r \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> 'r"

  assumes
    add_comm      : "\<And>x y.   x +R y = y +R x"
    and add_assoc : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and add_zero  : "\<And>x.     x +R zero = x"
    and add_opp   : "\<And>x.     opp x +R x = zero"
    and add_right_cancel : "\<And>x y z. x +R z = y +R z \<Longrightarrow> x = y"
    and mul_comm  : "\<And>x y.   x *R y = y *R x"
    and mul_assoc : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and mul_one   : "\<And>x.     x *R one = x"
    and dist_l    : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
    and opp_inv   : "\<And>x.     opp (opp x) = x"
    and add_le_compat : "\<And>x y z. x \<le>R y \<Longrightarrow> (x +R z) \<le>R (y +R z)"
    and le_opp    : "\<And>x y.   x \<le>R y \<Longrightarrow> opp y \<le>R opp x"
    and le_antisymm : "\<And>x y. x \<le>R y \<Longrightarrow> y \<le>R x \<Longrightarrow> x = y"
    and lt_opp    : "\<And>x y.   x <R y \<Longrightarrow> opp y <R opp x"
    and le_refl   : "\<And>x.     x \<le>R x"
    and le_trans  : "\<And>x y z. x \<le>R y \<Longrightarrow> y \<le>R z \<Longrightarrow> x \<le>R z"
    and le_total  : "\<And>x y.   x \<le>R y \<or> y \<le>R x"
    and lt_def    : "\<And>x y.   (x <R y) \<longleftrightarrow> (x \<le>R y \<and> x \<noteq> y)"
    and abs_pos   : "\<And>x.     zero \<le>R x \<Longrightarrow> absR x = x"
    and abs_neg   : "\<And>x.     x \<le>R zero \<Longrightarrow> absR x = opp x"
    and abs_nonneg : "\<And>x.    zero \<le>R absR x"
    and abs_opp   : "\<And>x.     absR (opp x) = absR x"
    and abs_triangle : "\<And>x y. absR (x +R y) \<le>R (absR x +R absR y)"

    and sigma_mul_const : "\<And>D f c. sigma D (\<lambda>x. c *R f x) = c *R sigma D f"
    and sigma_congr : "\<And>D f g. (\<forall>x. D x \<longrightarrow> f x = g x) \<Longrightarrow> sigma D f = sigma D g"
    and sigma_zero  : "\<And>D.     sigma D (\<lambda>_. zero) = zero"
    and sigma_add   : "\<And>D f g. sigma D (\<lambda>x. f x +R g x) = sigma D f +R sigma D g"
    and sigma_union_disjoint :
          "\<And>D E f. (\<forall>x. D x \<longrightarrow> E x \<longrightarrow> False) \<Longrightarrow>
            sigma (\<lambda>x. D x \<or> E x) f = sigma D f +R sigma E f"
    and sigma_le    : "\<And>D f g. (\<forall>x. D x \<longrightarrow> f x \<le>R g x) \<Longrightarrow> sigma D f \<le>R sigma D g"
    and sigma_dom_congr :
          "\<And>D E f. (\<forall>x. D x \<longleftrightarrow> E x) \<Longrightarrow> sigma D f = sigma E f"
begin





definition Iic :: "'r \<Rightarrow> 'r \<Rightarrow> bool" where "Iic c x \<equiv> x \<le>R c"
definition Ioi :: "'r \<Rightarrow> 'r \<Rightarrow> bool" where "Ioi c x \<equiv> c <R x"
definition Iio :: "'r \<Rightarrow> 'r \<Rightarrow> bool" where "Iio c x \<equiv> x <R c"

definition preimage :: "('r \<Rightarrow> 'r) \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "preimage g D x \<equiv> D (g x)"





lemma add_opp_r: "x +R opp x = zero"
  using add_opp[of x] add_comm[of x "opp x"] by simp





lemma lt_irrefl: "\<not> (x <R x)"
  using lt_def by blast

lemma lt_trans_strict: "x <R y \<Longrightarrow> y <R z \<Longrightarrow> x <R z"
  using lt_def le_trans by blast





lemma preimage_union:
  "preimage g (\<lambda>x. D x \<or> E x) x \<longleftrightarrow> preimage g D x \<or> preimage g E x"
  unfolding preimage_def by blast

lemma preimage_inter:
  "preimage g (\<lambda>x. D x \<and> E x) x \<longleftrightarrow> preimage g D x \<and> preimage g E x"
  unfolding preimage_def by blast

lemma preimage_neg_Ioi: "preimage opp (Ioi c) x \<longleftrightarrow> x <R opp c"
  unfolding preimage_def Ioi_def
  by (metis lt_opp opp_inv)

lemma preimage_neg_Iic: "preimage opp (Iic c) x \<longleftrightarrow> opp c \<le>R x"
  unfolding preimage_def Iic_def
  by (metis le_opp opp_inv)

lemma preimage_comp:
  "preimage g (preimage h D) x \<longleftrightarrow> preimage (\<lambda>x. h (g x)) D x"
  unfolding preimage_def by simp





lemma integral_neg: "sigma D (\<lambda>x. opp (f x)) = opp (sigma D f)"
proof -
  have h: "sigma D (\<lambda>x. opp (f x)) +R sigma D f =
           opp (sigma D f) +R sigma D f"
  proof -
    have lhs: "sigma D (\<lambda>x. opp (f x)) +R sigma D f = zero"
    proof -
      have "sigma D (\<lambda>x. opp (f x)) +R sigma D f =
            sigma D (\<lambda>x. opp (f x) +R f x)"
        by (rule sigma_add[symmetric])
      also have "\<dots> = sigma D (\<lambda>_. zero)"
        by (rule sigma_congr) (simp add: add_opp)
      also have "\<dots> = zero"
        by (rule sigma_zero)
      finally show ?thesis .
    qed
    have rhs: "opp (sigma D f) +R sigma D f = zero"
      by (rule add_opp)
    show ?thesis by (simp only: lhs rhs)
  qed
  from add_right_cancel[OF h] show ?thesis .
qed

lemma integral_sub:
  "sigma D (\<lambda>x. f x +R opp (g x)) = sigma D f +R opp (sigma D g)"
  by (simp add: sigma_add integral_neg)





lemma sigma_empty: "sigma (\<lambda>_. False) f = zero"
proof -
  have "sigma (\<lambda>_. False) f = sigma (\<lambda>_. False) (\<lambda>_. zero)"
    by (rule sigma_congr) blast
  thus ?thesis by (simp add: sigma_zero)
qed





lemma sigma_bilinear:
  "sigma D (\<lambda>x. (c *R f x) +R (d *R g x)) =
   (c *R sigma D f) +R (d *R sigma D g)"
  by (simp add: sigma_add sigma_mul_const)





lemma sigma_le_monotone:
  "(\<forall>x. D x \<longrightarrow> f x \<le>R g x) \<Longrightarrow> sigma D f \<le>R sigma D g"
  by (rule sigma_le)

lemma sigma_nonneg:
  "(\<forall>x. D x \<longrightarrow> zero \<le>R f x) \<Longrightarrow> zero \<le>R sigma D f"
proof -
  assume h: "\<forall>x. D x \<longrightarrow> zero \<le>R f x"
  have "sigma D (\<lambda>_. zero) \<le>R sigma D f"
    by (rule sigma_le) (simp add: h)
  thus ?thesis by (simp add: sigma_zero)
qed





lemma sigma_split:
  "sigma D f =
   sigma (\<lambda>x. D x \<and> P x) f +R sigma (\<lambda>x. D x \<and> \<not> P x) f"
proof -
  let ?E = "\<lambda>x. D x \<and> P x"
  let ?F = "\<lambda>x. D x \<and> \<not> P x"
  have dom_eq: "\<forall>x. D x \<longleftrightarrow> (?E x \<or> ?F x)" by blast
  have "sigma D f = sigma (\<lambda>x. ?E x \<or> ?F x) f"
    by (rule sigma_dom_congr) (rule dom_eq)
  also have "\<dots> = sigma ?E f +R sigma ?F f"
    by (rule sigma_union_disjoint) blast
  finally show ?thesis .
qed





lemma sigma_preimage_neg_Ioi:
  "sigma (preimage opp (Ioi c)) f = sigma (Iio (opp c)) f"
  by (rule sigma_dom_congr) (simp add: preimage_neg_Ioi Iio_def)





lemma sigma_abs_bound:
  "absR (sigma D f) \<le>R sigma D (\<lambda>x. absR (f x))"
proof -
  let ?P    = "\<lambda>x. zero \<le>R f x"
  let ?E    = "\<lambda>x. D x \<and> ?P x"
  let ?F    = "\<lambda>x. D x \<and> \<not> ?P x"
  let ?Ipos = "sigma ?E f"
  let ?Ineg = "sigma ?F f"

  have split: "sigma D f = ?Ipos +R ?Ineg"
    by (rule sigma_split)


  have Hpos_nonneg: "zero \<le>R ?Ipos"
    by (rule sigma_nonneg) blast


  have Hfx_le0: "\<forall>x. ?F x \<longrightarrow> f x \<le>R zero"
    using le_total by blast


  have Hneg_nonpos: "?Ineg \<le>R zero"
  proof -
    have "?Ineg \<le>R sigma ?F (\<lambda>_. zero)"
      by (rule sigma_le) (simp add: Hfx_le0)
    thus ?thesis by (simp add: sigma_zero)
  qed


  have Hpos_eq: "absR ?Ipos = sigma ?E (\<lambda>x. absR (f x))"
  proof -
    have "absR ?Ipos = ?Ipos"
      by (rule abs_pos[OF Hpos_nonneg])
    also have "\<dots> = sigma ?E (\<lambda>x. absR (f x))"
      by (rule sigma_congr) (auto simp add: abs_pos)
    finally show ?thesis .
  qed


  have Hneg_eq: "absR ?Ineg = sigma ?F (\<lambda>x. absR (f x))"
  proof -
    have "absR ?Ineg = opp ?Ineg"
      by (rule abs_neg[OF Hneg_nonpos])
    also have "\<dots> = sigma ?F (\<lambda>x. opp (f x))"
      by (simp add: integral_neg)
    also have "\<dots> = sigma ?F (\<lambda>x. absR (f x))"
      by (rule sigma_congr) (auto simp add: abs_neg Hfx_le0)
    finally show ?thesis .
  qed


  have split_abs:
    "sigma D (\<lambda>x. absR (f x)) =
     sigma ?E (\<lambda>x. absR (f x)) +R sigma ?F (\<lambda>x. absR (f x))"
    by (rule sigma_split)


  have step1: "absR (?Ipos +R ?Ineg) \<le>R absR ?Ipos +R absR ?Ineg"
    by (rule abs_triangle)
  have step2: "absR ?Ipos +R absR ?Ineg = sigma D (\<lambda>x. absR (f x))"
    by (simp only: Hpos_eq Hneg_eq split_abs[symmetric])
  have h1: "absR (sigma D f) \<le>R absR ?Ipos +R absR ?Ineg"
    by (simp only: split, rule step1)
  show ?thesis
    by (rule le_trans[OF h1], simp only: step2[symmetric], rule le_refl)
qed

end

end
