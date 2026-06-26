theory supinf
  imports Main
begin

locale complete_ordered_field =
  fixes zero_nat  :: "'n"
    and succ      :: "'n \<Rightarrow> 'n"
    and nat_le    :: "'n \<Rightarrow> 'n \<Rightarrow> bool"
    and zero one  :: "'r"
    and add       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "+R" 65)
    and mul       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "*R" 70)
    and opp inv   :: "'r \<Rightarrow> 'r"
    and rle       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "\<le>R" 50)
    and rlt       :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "<R" 50)
    and rabs      :: "'r \<Rightarrow> 'r"
    and inr       :: "'n \<Rightarrow> 'r"
  assumes nat_le_refl   : "\<And>n. nat_le n n"
    and   le_succ_of_le : "\<And>n m. nat_le n m \<Longrightarrow> nat_le n (succ m)"
    and   le_succ       : "\<And>n. nat_le n (succ n)"
    and   add_comm      : "\<And>x y. x +R y = y +R x"
    and   add_assoc     : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and   add_zero      : "\<And>x. x +R zero = x"
    and   add_opp       : "\<And>x. opp x +R x = zero"
    and   mul_comm      : "\<And>x y. x *R y = y *R x"
    and   mul_assoc     : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and   mul_one       : "\<And>x. x *R one = x"
    and   dist_l        : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
    and   sub_zero      : "\<And>x. x +R opp zero = x"
    and   rle_refl      : "\<And>x. x \<le>R x"
    and   rle_trans     : "\<And>x y z. x \<le>R y \<Longrightarrow> y \<le>R z \<Longrightarrow> x \<le>R z"
    and   rle_antisym   : "\<And>x y. x \<le>R y \<Longrightarrow> y \<le>R x \<Longrightarrow> x = y"
    and   rlt_def       : "\<And>x y. (x <R y) \<longleftrightarrow> (x \<le>R y \<and> x \<noteq> y)"
    and   rle_abs       : "\<And>x. x +R opp zero \<le>R rabs x"
    and   rinv_pos      : "\<And>x. zero <R x \<Longrightarrow> zero <R inv x"
    and   rplus_le_compat_l : "\<And>x y z. y \<le>R z \<Longrightarrow> x +R y \<le>R x +R z"
    and   rinv_involutive    : "\<And>x. zero <R x \<Longrightarrow> inv (inv x) = x"
    and   inr_pos       : "\<And>n. zero <R inr (succ n)"
    and   inr_le        : "\<And>m n. nat_le m n \<Longrightarrow> inr m \<le>R inr n"
    and   inr_zero      : "inr zero_nat = zero"
    and   inr_succ      : "\<And>n. inr (succ n) = inr n +R one"
    and   rtotal_order  : "\<And>x y. (x <R y) \<or> x = y \<or> (y <R x)"
    and   rle_inv_contravar :
            "\<And>a b. zero <R a \<Longrightarrow> zero <R b \<Longrightarrow> a \<le>R b \<Longrightarrow> inv b \<le>R inv a"
    and   eps_between   :
            "\<And>x y. x <R y \<Longrightarrow> \<exists>eps. zero <R eps \<and> x +R eps <R y"
    and   archimedean   : "\<And>x. \<exists>n. x \<le>R inr n"
    and   completeness  :
            "\<And>A. (\<exists>ub. \<forall>a. A a \<longrightarrow> ub \<le>R a) \<Longrightarrow>
              \<exists>sup. (\<forall>a. A a \<longrightarrow> a \<le>R sup) \<and>
                    (\<forall>y. (\<forall>a. A a \<longrightarrow> a \<le>R y) \<longrightarrow> sup \<le>R y)"
begin





lemma add_opp_r: "x +R opp x = zero"
  using add_opp[of x] add_comm[of x "opp x"] by simp

lemma rlt_le: "x <R y \<Longrightarrow> x \<le>R y"
  using rlt_def by blast

lemma rlt_ne: "x <R y \<Longrightarrow> x \<noteq> y"
  using rlt_def by blast

lemma rlt_intro: "x \<le>R y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x <R y"
  using rlt_def by blast





definition up_bounds :: "('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "up_bounds A x \<equiv> \<forall>a. A a \<longrightarrow> a \<le>R x"

definition is_maximum :: "'r \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_maximum a A \<equiv> A a \<and> up_bounds A a"

definition low_bounds :: "('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "low_bounds A x \<equiv> \<forall>a. A a \<longrightarrow> x \<le>R a"

definition is_inf :: "'r \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_inf x A \<equiv> is_maximum x (low_bounds A)"

definition limit :: "('n \<Rightarrow> 'r) \<Rightarrow> 'r \<Rightarrow> bool"
  where "limit u l \<equiv>
    \<forall>eps. zero <R eps \<longrightarrow>
      (\<exists>N. \<forall>n. nat_le N n \<longrightarrow> rabs (u n +R opp l) \<le>R eps)"





lemma add_sub_cancel_r: "a +R (b +R opp a) = b"
proof -
  have "a +R (b +R opp a) = b +R (a +R opp a)"
  proof -
    have "a +R (b +R opp a) = (a +R b) +R opp a" by (rule add_assoc [symmetric])
    also have "\<dots> = (b +R a) +R opp a"           by (simp add: add_comm)
    also have "\<dots> = b +R (a +R opp a)"            by (rule add_assoc)
    finally show ?thesis .
  qed
  also have "\<dots> = b +R zero" by (simp add: add_opp_r)
  also have "\<dots> = b"         by (rule add_zero)
  finally show ?thesis .
qed





lemma rabs_pos: "t \<le>R rabs t"
  using rle_abs[of t] sub_zero[of t] by simp





lemma unique_max:
  assumes "is_maximum x A" "is_maximum y A"
  shows "x = y"
proof -
  from assms(1) have hxA: "A x" and hx: "up_bounds A x"
    unfolding is_maximum_def by blast+
  from assms(2) have hyA: "A y" and hy: "up_bounds A y"
    unfolding is_maximum_def by blast+
  have "x \<le>R y" using hy hxA unfolding up_bounds_def by blast
  have "y \<le>R x" using hx hyA unfolding up_bounds_def by blast
  show ?thesis by (rule rle_antisym) fact+
qed





lemma inf_lt:
  assumes hinf: "is_inf x A" and hlt: "x <R y"
  shows "\<exists>a. A a \<and> a <R y"
proof (rule ccontr)
  assume hnex: "\<not> (\<exists>a. A a \<and> a <R y)"
  from hinf have hxlb : "low_bounds A x"
           and  hmax  : "\<And>z. low_bounds A z \<Longrightarrow> z \<le>R x"
    unfolding is_inf_def is_maximum_def up_bounds_def by blast+
  have hlby: "low_bounds A y"
    unfolding low_bounds_def
  proof (intro allI impI)
    fix a assume ha: "A a"
    from hnex have not_lt: "\<not> (a <R y)" using ha by blast
    show "y \<le>R a"
      using rtotal_order[of y a] rlt_le rle_refl not_lt by blast
  qed
  have hyx: "y \<le>R x" by (rule hmax[OF hlby])
  have hxy: "x \<le>R y" using hlt rlt_le by blast
  have "x = y" by (rule rle_antisym) fact+
  moreover have "x \<noteq> y" using hlt rlt_ne by blast
  ultimately show False by blast
qed





lemma le_of_le_add_eps:
  assumes H: "\<forall>eps. zero <R eps \<longrightarrow> y \<le>R x +R eps"
  shows "y \<le>R x"
proof (rule ccontr)
  assume hne: "\<not> y \<le>R x"
  have hgt: "x <R y"
    using rtotal_order[of x y] hne rlt_le rle_refl by blast
  obtain eps where heps: "zero <R eps" and hxp: "x +R eps <R y"
    using eps_between[OF hgt] by blast
  have hyle  : "y \<le>R x +R eps"      using H heps by blast
  have hxple : "x +R eps \<le>R y"      using hxp rlt_le by blast
  have heq   : "x +R eps = y"        by (rule rle_antisym) fact+
  have hneq  : "x +R eps \<noteq> y"       using hxp rlt_ne by blast
  from heq hneq show False by blast
qed





lemma le_lim:
  assumes hlim : "limit u x"
      and hle  : "\<forall>n. y \<le>R u n"
  shows "y \<le>R x"
proof -
  have key : "\<forall>eps. zero <R eps \<longrightarrow> y \<le>R x +R eps"
  proof (intro allI impI)
    fix eps assume heps: "zero <R eps"
    from hlim heps obtain N
      where HN: "\<forall>n. nat_le N n \<longrightarrow> rabs (u n +R opp x) \<le>R eps"
      unfolding limit_def by blast
    have hyuN : "y \<le>R u N" using hle by blast
    have heq  : "x +R (u N +R opp x) = u N"
      using add_sub_cancel_r[of x "u N"] by (simp add: add_comm)
    have huNx : "u N \<le>R x +R (u N +R opp x)"
      by (subst heq; rule rle_refl)
    have hepN : "rabs (u N +R opp x) \<le>R eps"
      using HN nat_le_refl[of N] by blast
    have hchain : "u N +R opp x \<le>R eps"
      by (rule rle_trans[OF rabs_pos hepN])
    have hcompat : "x +R (u N +R opp x) \<le>R x +R eps"
      by (rule rplus_le_compat_l[OF hchain])
    have huNxeps : "u N \<le>R x +R eps"
      by (rule rle_trans[OF huNx hcompat])
    show "y \<le>R x +R eps"
      by (rule rle_trans[OF hyuN huNxeps])
  qed
  show ?thesis by (rule le_of_le_add_eps[OF key])
qed





lemma inv_succ_pos: "zero <R inv (inr (succ n))"
  by (rule rinv_pos[OF inr_pos])





lemma limit_inv_succ:
  assumes heps: "zero <R eps"
  shows "\<exists>N. \<forall>n. nat_le N n \<longrightarrow> inv (inr (succ n)) \<le>R eps"
proof -
  define x where "x \<equiv> inv eps"
  have hx_pos: "zero <R x" unfolding x_def by (rule rinv_pos[OF heps])
  obtain N where harch: "x \<le>R inr N" using archimedean by blast
  define N1 where "N1 \<equiv> succ N"
  show ?thesis
  proof (intro exI[of _ N1] allI impI)
    fix n assume hn: "nat_le N1 n"
    have hINR_le: "inr N1 \<le>R inr (succ n)"
      by (rule inr_le, rule le_succ_of_le[OF hn])
    have hINR_pos: "zero <R inr (succ n)" by (rule inr_pos)
    have hINR_N_pos: "zero <R inr N1" unfolding N1_def by (rule inr_pos)
    have step1: "inv (inr (succ n)) \<le>R inv (inr N1)"
      by (rule rle_inv_contravar[OF hINR_N_pos hINR_pos hINR_le])
    have harch1: "x \<le>R inr N1"
      unfolding N1_def
      using rle_trans[OF harch inr_le[OF le_succ[of N]]] .
    have step2: "inv (inr N1) \<le>R inv x"
      by (rule rle_inv_contravar[OF hx_pos hINR_N_pos harch1])
    have step3: "inv x = eps"
      unfolding x_def by (rule rinv_involutive[OF heps])
    show "inv (inr (succ n)) \<le>R eps"
      using rle_trans[OF step1 step2] step3 by simp
  qed
qed

end

end
