theory limits_uniqueness
  imports Main
begin

locale abs_field =
  fixes zero    :: "'r"
    and one     :: "'r"
    and add     :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "+R" 65)
    and mul     :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "*R" 70)
    and opp     :: "'r \<Rightarrow> 'r"
    and absV    :: "'r \<Rightarrow> 'r"
    and le      :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "\<preceq>" 50)
    and lt      :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "\<prec>" 50)

    and natLe   :: "'n \<Rightarrow> 'n \<Rightarrow> bool"
    and natMax  :: "'n \<Rightarrow> 'n \<Rightarrow> 'n"
  assumes le_max_left    : "\<And>x y. natLe x (natMax x y)"
    and   le_max_right   : "\<And>x y. natLe y (natMax x y)"
    and   add_comm       : "\<And>x y. x +R y = y +R x"
    and   add_assoc      : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and   add_zero       : "\<And>x. x +R zero = x"
    and   add_opp        : "\<And>x. x +R opp x = zero"
    and   opp_add        : "\<And>x y. opp (x +R y) = opp x +R opp y"
    and   le_refl        : "\<And>x. x \<preceq> x"
    and   le_trans       : "\<And>x y z. x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
    and   add_le_add     : "\<And>a b c d. a \<preceq> b \<Longrightarrow> c \<preceq> d \<Longrightarrow> a +R c \<preceq> b +R d"
    and   abs_nonneg     : "\<And>x. zero \<preceq> absV x"
    and   abs_triangle   : "\<And>x y. absV (x +R y) \<preceq> absV x +R absV y"
    and   abs_sub_symm   : "\<And>x y. absV (x +R opp y) = absV (y +R opp x)"
    and   sub_decomp     : "\<And>x y z. x +R opp z = (x +R opp y) +R (y +R opp z)"
    and   sub_eq_zero    : "\<And>x y. x +R opp y = zero \<Longrightarrow> x = y"
    and   eq_of_forall_eps2 :
            "\<And>x. (\<forall>eps. zero \<prec> eps \<longrightarrow> absV x \<preceq> eps +R eps) \<Longrightarrow> x = zero"
begin





definition sub :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
  where "sub x y \<equiv> x +R opp y"

definition limit :: "('n \<Rightarrow> 'r) \<Rightarrow> 'r \<Rightarrow> bool"
  where "limit u l \<equiv>
    \<forall>eps. zero \<prec> eps \<longrightarrow>
      (\<exists>N. \<forall>n. natLe N n \<longrightarrow> absV (sub (u n) l) \<preceq> eps)"





lemma sub_self_zero: "sub x x = zero"
  unfolding sub_def by (rule add_opp)

lemma sub_decomp_lem: "sub x z = (sub x y) +R (sub y z)"
  unfolding sub_def by (rule sub_decomp)

lemma abs_sub_triangle:
  "absV (sub x z) \<preceq> absV (sub x y) +R absV (sub y z)"
proof -
  have "sub x z = sub x y +R sub y z" by (rule sub_decomp_lem)
  hence "absV (sub x z) = absV (sub x y +R sub y z)" by simp
  also have "\<dots> \<preceq> absV (sub x y) +R absV (sub y z)" by (rule abs_triangle)
  finally show ?thesis .
qed

lemma abs_sub_symm_lem: "absV (sub x y) = absV (sub y x)"
  unfolding sub_def by (rule abs_sub_symm)





theorem limit_unique:
  assumes Hl: "limit u l" and Hm: "limit u m"
  shows "l = m"
proof -

  have Hbound: "\<forall>eps. zero \<prec> eps \<longrightarrow> absV (sub l m) \<preceq> eps +R eps"
  proof (intro allI impI)
    fix eps assume Heps: "zero \<prec> eps"
    from Hl Heps obtain N1
      where HN1: "\<forall>n. natLe N1 n \<longrightarrow> absV (sub (u n) l) \<preceq> eps"
      unfolding limit_def by blast
    from Hm Heps obtain N2
      where HN2: "\<forall>n. natLe N2 n \<longrightarrow> absV (sub (u n) m) \<preceq> eps"
      unfolding limit_def by blast
    define N where "N \<equiv> natMax N1 N2"
    have H1 : "absV (sub (u N) l) \<preceq> eps"
      using HN1 le_max_left unfolding N_def by blast
    have H2 : "absV (sub (u N) m) \<preceq> eps"
      using HN2 le_max_right unfolding N_def by blast
    have Htri : "absV (sub l m) \<preceq> absV (sub l (u N)) +R absV (sub (u N) m)"
      by (rule abs_sub_triangle)
    have H1' : "absV (sub l (u N)) \<preceq> eps"
      using H1 by (simp add: abs_sub_symm_lem)
    show "absV (sub l m) \<preceq> eps +R eps"
      using le_trans[OF Htri] add_le_add[OF H1' H2] by blast
  qed

  have Hz : "sub l m = zero"
    using Hbound by (rule eq_of_forall_eps2)
  show "l = m"
    using sub_eq_zero[OF Hz[unfolded sub_def]] .
qed

end

end
