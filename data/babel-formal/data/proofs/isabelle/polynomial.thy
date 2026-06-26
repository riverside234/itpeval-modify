theory polynomial
  imports Main
begin






datatype mynat = Nat_O | Nat_S mynat

fun mynat_add :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
  "mynat_add Nat_O m = m"
| "mynat_add (Nat_S n') m = Nat_S (mynat_add n' m)"

lemma mynat_add_O_left: "mynat_add Nat_O m = m"
  by simp

lemma mynat_add_S_left: "mynat_add (Nat_S n) m = Nat_S (mynat_add n m)"
  by simp

inductive mynat_le :: "mynat \<Rightarrow> mynat \<Rightarrow> bool" where
  le_n : "mynat_le n n"
| le_S : "mynat_le n m \<Longrightarrow> mynat_le n (Nat_S m)"

lemma mynat_zero_le: "mynat_le Nat_O n"
  by (induction n) (auto intro: mynat_le.intros)

lemma mynat_add_zero_r: "mynat_add n Nat_O = n"
  by (induction n) auto

lemma mynat_succ_le_succ: "mynat_le n m \<Longrightarrow> mynat_le (Nat_S n) (Nat_S m)"
  by (induction rule: mynat_le.induct) (auto intro: mynat_le.intros)

lemma mynat_add_S_r: "mynat_add m (Nat_S n) = Nat_S (mynat_add m n)"
  by (induction m) auto

lemma mynat_add_comm: "mynat_add n m = mynat_add m n"
  by (induction n) (auto simp: mynat_add_zero_r mynat_add_S_r)





datatype 'a mylist = NilL | ConsL 'a "'a mylist"

inductive InL :: "'a \<Rightarrow> 'a mylist \<Rightarrow> bool" where
  In_head : "InL x (ConsL x xs)"
| In_tail : "InL x xs \<Longrightarrow> InL x (ConsL y xs)"

inductive NoDupL :: "'a mylist \<Rightarrow> bool" where
  ND_nil  : "NoDupL NilL"
| ND_cons : "\<not> InL x xs \<Longrightarrow> NoDupL xs \<Longrightarrow> NoDupL (ConsL x xs)"

fun lengthL :: "'a mylist \<Rightarrow> mynat" where
  "lengthL NilL = Nat_O"
| "lengthL (ConsL _ rest) = Nat_S (lengthL rest)"





locale polynomial_setup =
  fixes zero_r :: "'r"
    and one_r  :: "'r"
    and opp_r  :: "'r \<Rightarrow> 'r"
    and add_r  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl \<open>+R\<close> 65)
    and mul_r  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl \<open>*R\<close> 70)
    and zero_p :: "'p"
    and one_p  :: "'p"
    and opp_p  :: "'p \<Rightarrow> 'p"
    and add_p  :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"  (infixl \<open>+P\<close> 65)
    and mul_p  :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"  (infixl \<open>*P\<close> 70)
    and degree   :: "'p \<Rightarrow> mynat"
    and monomial :: "mynat \<Rightarrow> 'r \<Rightarrow> 'p"
    and eval     :: "'p \<Rightarrow> 'r \<Rightarrow> 'r"
  assumes
    r_one_neq_zero  : "one_r \<noteq> zero_r"
  and r_add_comm    : "\<And>x y.   x +R y = y +R x"
  and r_add_assoc   : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
  and r_add_zero    : "\<And>x.     x +R zero_r = x"
  and r_add_opp     : "\<And>x.     x +R opp_r x = zero_r"
  and r_mul_comm    : "\<And>x y.   x *R y = y *R x"
  and r_mul_assoc   : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
  and r_mul_one     : "\<And>x.     x *R one_r = x"
  and r_dist_l      : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
  and r_mul_zero    : "\<And>x.     x *R zero_r = zero_r"
  and r_no_zero_div : "\<And>x y.   x *R y = zero_r \<Longrightarrow> x = zero_r \<or> y = zero_r"
  and p_one_neq_zero : "one_p \<noteq> zero_p"
  and p_add_comm    : "\<And>x y.   x +P y = y +P x"
  and p_add_assoc   : "\<And>x y z. (x +P y) +P z = x +P (y +P z)"
  and p_add_zero    : "\<And>x.     x +P zero_p = x"
  and p_add_opp     : "\<And>x.     x +P opp_p x = zero_p"
  and p_mul_comm    : "\<And>x y.   x *P y = y *P x"
  and p_mul_assoc   : "\<And>x y z. (x *P y) *P z = x *P (y *P z)"
  and p_mul_one     : "\<And>x.     x *P one_p = x"
  and p_dist_l      : "\<And>x y z. x *P (y +P z) = (x *P y) +P (x *P z)"
  and p_mul_zero    : "\<And>x.     x *P zero_p = zero_p"
  and p_no_zero_div : "\<And>x y.   x *P y = zero_p \<Longrightarrow> x = zero_p \<or> y = zero_p"
  and deg_zero      : "degree zero_p = Nat_O"
  and eval_add      : "\<And>p q x. eval (p +P q) x = eval p x +R eval q x"
  and eval_mul      : "\<And>p q x. eval (p *P q) x = eval p x *R eval q x"
  and eval_C_ax     : "\<And>c x.   eval (monomial Nat_O c) x = c"
  and eval_X_ax     : "\<And>x.     eval (monomial (Nat_S Nat_O) one_r) x = x"
  and deg_C_ax      : "\<And>c.     c \<noteq> zero_r \<Longrightarrow> degree (monomial Nat_O c) = Nat_O"
  and deg_constant  : "\<And>p.     (degree p = Nat_O) \<longleftrightarrow> (\<exists>c. p = monomial Nat_O c)"
  and deg_X_minus_ax : "\<And>a.    degree (monomial (Nat_S Nat_O) one_r +P monomial Nat_O (opp_r a)) = Nat_S Nat_O"
  and deg_mul       : "\<And>p q.   p \<noteq> zero_p \<Longrightarrow> q \<noteq> zero_p \<Longrightarrow>
                                 degree (p *P q) = mynat_add (degree p) (degree q)"
  and C_zero_ax     : "monomial Nat_O zero_r = zero_p"
  and C_one_ax      : "monomial Nat_O one_r = one_p"
  and euclid_X_minus_ax :
       "\<And>p a. \<exists>q r.
          p = q *P (monomial (Nat_S Nat_O) one_r +P monomial Nat_O (opp_r a)) +P r
          \<and> degree r = Nat_O"
begin





definition X :: "'p" where
  "X = monomial (Nat_S Nat_O) one_r"

definition C :: "'r \<Rightarrow> 'p" where
  "C c = monomial Nat_O c"

definition X_minus :: "'r \<Rightarrow> 'p" where
  "X_minus a = X +P C (opp_r a)"

fun poly_of_roots :: "'r mylist \<Rightarrow> 'p" where
  "poly_of_roots NilL = one_p"
| "poly_of_roots (ConsL a xs) = X_minus a *P poly_of_roots xs"

definition is_root :: "'r \<Rightarrow> 'p \<Rightarrow> bool" where
  "is_root a p \<longleftrightarrow> eval p a = zero_r"





lemma X_minus_unfold:
  "X_minus a = monomial (Nat_S Nat_O) one_r +P monomial Nat_O (opp_r a)"
  unfolding X_minus_def X_def C_def by simp

lemma eval_C: "eval (C c) x = c"
  unfolding C_def by (rule eval_C_ax)

lemma eval_X: "eval X x = x"
  unfolding X_def by (rule eval_X_ax)

lemma deg_X_minus: "degree (X_minus a) = Nat_S Nat_O"
  by (simp only: X_minus_unfold deg_X_minus_ax)

lemma C_zero: "C zero_r = zero_p"
  unfolding C_def by (rule C_zero_ax)

lemma C_one: "C one_r = one_p"
  unfolding C_def by (rule C_one_ax)

lemma deg_C: "c \<noteq> zero_r \<Longrightarrow> degree (C c) = Nat_O"
  unfolding C_def by (rule deg_C_ax)

lemma euclid_X_minus: "\<exists>q r. p = q *P X_minus a +P r \<and> degree r = Nat_O"
  using euclid_X_minus_ax[of p a]
  by (simp only: X_minus_unfold)





lemma r_opp_add: "opp_r x +R x = zero_r"
  by (metis r_add_comm r_add_opp)

lemma r_add_zero_l: "zero_r +R x = x"
  by (metis r_add_comm r_add_zero)





lemma sub_eq_zero_l: "x +R opp_r y = zero_r \<Longrightarrow> x = y"
proof -
  assume h: "x +R opp_r y = zero_r"
  have opp_cancel: "opp_r y +R y = zero_r"
    by (metis r_add_comm r_add_opp)
  have "x = x +R zero_r"
    by (simp only: r_add_zero)
  also have "\<dots> = x +R (opp_r y +R y)"
    by (simp only: opp_cancel)
  also have "\<dots> = (x +R opp_r y) +R y"
    by (simp only: r_add_assoc)
  also have "\<dots> = zero_r +R y"
    by (simp only: h)
  also have "\<dots> = y +R zero_r"
    by (simp only: r_add_comm)
  also have "\<dots> = y"
    by (simp only: r_add_zero)
  finally show "x = y" .
qed





lemma eval_X_minus: "eval (X_minus a) b = b +R opp_r a"
  unfolding X_minus_def
  by (simp only: eval_add eval_X eval_C)





lemma X_minus_nonzero: "X_minus a \<noteq> zero_p"
proof
  assume h: "X_minus a = zero_p"
  have hdeg: "degree (X_minus a) = Nat_S Nat_O" by (rule deg_X_minus)
  have h1: "degree zero_p = Nat_S Nat_O" by (simp only: h[symmetric] hdeg)
  then show False using deg_zero by simp
qed





lemma p_add_zero_l: "zero_p +P x = x"
  by (metis p_add_comm p_add_zero)

lemma p_mul_zero_l: "zero_p *P x = zero_p"
  by (metis p_mul_comm p_mul_zero)

lemma p_mul_one_l: "one_p *P x = x"
  by (metis p_mul_comm p_mul_one)





lemma root_factor: "is_root a p \<Longrightarrow> \<exists>q. p = q *P X_minus a"
proof -
  assume hp: "is_root a p"
  obtain q r where heq: "p = q *P X_minus a +P r" and hdeg: "degree r = Nat_O"
    using euclid_X_minus[of p a] by blast

  have hr0: "eval r a = zero_r"
  proof -
    have hpz: "eval p a = zero_r"
      using hp unfolding is_root_def .
    have h1: "eval (q *P X_minus a) a +R eval r a = zero_r"
      using hpz by (simp only: heq eval_add)
    have h2: "eval (q *P X_minus a) a = eval q a *R zero_r"
      by (simp only: eval_mul eval_X_minus r_add_opp)
    have h3: "eval (q *P X_minus a) a = zero_r"
      by (simp only: h2 r_mul_zero)
    have h4: "zero_r +R eval r a = zero_r"
      by (rule h1[simplified h3])
    show ?thesis using h4[simplified r_add_zero_l] .
  qed

  obtain c where hc: "r = monomial Nat_O c"
    using deg_constant[of r] hdeg by blast

  have hcz: "c = zero_r"
    using hr0 by (simp only: hc eval_C_ax)

  have hrz: "r = zero_p"
    by (simp only: hc hcz C_zero_ax)

  show "\<exists>q. p = q *P X_minus a"
    by (rule exI[of _ q], simp only: heq hrz p_add_zero)
qed





lemma root_transfer:
  "p = q *P X_minus a \<Longrightarrow> b \<noteq> a \<Longrightarrow> is_root b p \<Longrightarrow> is_root b q"
proof -
  assume hp:  "p = q *P X_minus a"
  assume hba: "b \<noteq> a"
  assume hpb: "is_root b p"
  have h_zero: "eval q b *R eval (X_minus a) b = zero_r"
    using hpb unfolding is_root_def hp by (simp only: eval_mul)
  have hxb: "eval (X_minus a) b = b +R opp_r a"
    by (rule eval_X_minus)
  have hmul: "eval q b *R (b +R opp_r a) = zero_r"
    by (metis h_zero hxb)
  have hdisj: "eval q b = zero_r \<or> b +R opp_r a = zero_r"
    by (rule r_no_zero_div[OF hmul])
  show "is_root b q" unfolding is_root_def
  proof (rule ccontr)
    assume hne: "eval q b \<noteq> zero_r"
    have hba': "b +R opp_r a = zero_r" using hdisj hne by blast
    have "b = a" by (rule sub_eq_zero_l[OF hba'])
    then show False using hba by blast
  qed
qed





lemma roots_le_degree:
  "NoDupL xs \<Longrightarrow> (\<forall>a. InL a xs \<longrightarrow> is_root a p) \<Longrightarrow> p \<noteq> zero_p \<Longrightarrow>
   mynat_le (lengthL xs) (degree p)"
proof (induction xs arbitrary: p)
  case NilL
  show ?case by (simp only: lengthL.simps, rule mynat_zero_le)
next
  case (ConsL x xs)
  from ConsL.prems(1) have hnd_tl: "NoDupL xs" and hnotin: "\<not> InL x xs"
    by (auto elim: NoDupL.cases)
  have InLx: "InL x (ConsL x xs)" by (rule InL.In_head)
  have ha: "is_root x p"
    using ConsL.prems(2)[rule_format, OF InLx] .
  obtain q where hpq: "p = q *P X_minus x"
    using root_factor[OF ha] by blast
  have qnz: "q \<noteq> zero_p"
  proof
    assume hq: "q = zero_p"
    have "p = zero_p"
      by (simp only: hpq hq p_mul_zero_l)
    then show False using ConsL.prems(3) by blast
  qed
  have hdeg: "degree p = Nat_S (degree q)"
  proof -
    have hxnz: "X_minus x \<noteq> zero_p" by (rule X_minus_nonzero)
    have hmul: "degree (q *P X_minus x) = mynat_add (degree q) (degree (X_minus x))"
      by (rule deg_mul[OF qnz hxnz])
    have hxd: "degree (X_minus x) = Nat_S Nat_O" by (rule deg_X_minus)
    have h1: "degree p = mynat_add (degree q) (Nat_S Nat_O)"
      by (simp only: hpq hmul hxd)
    show ?thesis
      by (simp only: h1 mynat_add_S_r mynat_add_zero_r)
  qed
  have hF: "\<forall>b. InL b xs \<longrightarrow> is_root b q"
  proof (intro allI impI)
    fix b assume hb: "InL b xs"
    have hba: "b \<noteq> x" using hb hnotin by blast
    have hbroot: "is_root b p"
      using ConsL.prems(2) InL.In_tail[OF hb] by blast
    show "is_root b q"
      by (rule root_transfer[OF hpq hba hbroot])
  qed
  have ihRes: "mynat_le (lengthL xs) (degree q)"
    by (rule ConsL.IH[OF hnd_tl hF qnz])
  show ?case
    by (simp only: lengthL.simps hdeg, rule mynat_succ_le_succ[OF ihRes])
qed





lemma constant_root_zero:
  "degree p = Nat_O \<Longrightarrow> is_root a p \<Longrightarrow> p = zero_p"
proof -
  assume hdeg: "degree p = Nat_O"
  assume hroot: "is_root a p"
  obtain c where hc: "p = monomial Nat_O c"
    using deg_constant[of p] hdeg by blast
  have hcz: "c = zero_r"
    using hroot unfolding is_root_def hc by (simp only: eval_C_ax)
  show "p = zero_p"
    by (simp only: hc hcz C_zero_ax)
qed





lemma root_of_product:
  "is_root a (p *P q) \<Longrightarrow> is_root a p \<or> is_root a q"
proof -
  assume h: "is_root a (p *P q)"
  have hmul: "eval p a *R eval q a = zero_r"
    using h unfolding is_root_def by (simp only: eval_mul)
  have hdisj: "eval p a = zero_r \<or> eval q a = zero_r"
    by (rule r_no_zero_div[OF hmul])
  then show "is_root a p \<or> is_root a q"
    unfolding is_root_def by blast
qed





lemma root_scale_constant:
  "c \<noteq> zero_r \<Longrightarrow> (is_root a p \<longleftrightarrow> is_root a (C c *P p))"
proof -
  assume hc: "c \<noteq> zero_r"
  show "is_root a p \<longleftrightarrow> is_root a (C c *P p)"
  proof
    assume hp: "is_root a p"
    have hpa0: "eval p a = zero_r" using hp unfolding is_root_def .
    have hmul: "c *R eval p a = zero_r"
      by (simp only: hpa0 r_mul_zero)
    show "is_root a (C c *P p)"
      unfolding is_root_def
      by (simp only: eval_mul eval_C hmul)
  next
    assume hcp: "is_root a (C c *P p)"
    have hmul: "c *R eval p a = zero_r"
      using hcp unfolding is_root_def by (simp only: eval_mul eval_C)
    have hdisj: "c = zero_r \<or> eval p a = zero_r"
      by (rule r_no_zero_div[OF hmul])
    show "is_root a p" unfolding is_root_def
      using hdisj hc by blast
  qed
qed





lemma poly_of_roots_nonzero: "poly_of_roots xs \<noteq> zero_p"
proof (induction xs)
  case NilL
  show ?case by (simp only: poly_of_roots.simps, rule p_one_neq_zero)
next
  case (ConsL a xs)
  show ?case
  proof
    assume h: "poly_of_roots (ConsL a xs) = zero_p"
    have h': "X_minus a *P poly_of_roots xs = zero_p"
    proof -
      have heq: "poly_of_roots (ConsL a xs) = X_minus a *P poly_of_roots xs"
        by (simp only: poly_of_roots.simps)
      show ?thesis using heq h by simp
    qed
    have hdisj: "X_minus a = zero_p \<or> poly_of_roots xs = zero_p"
      by (rule p_no_zero_div[OF h'])
    from hdisj show False
    proof
      assume "X_minus a = zero_p" then show False using X_minus_nonzero by blast
    next
      assume "poly_of_roots xs = zero_p" then show False using ConsL.IH by blast
    qed
  qed
qed





lemma deg_poly_of_roots: "degree (poly_of_roots xs) = lengthL xs"
proof (induction xs)
  case NilL
  have h1: "poly_of_roots NilL = one_p" by simp
  have h2: "degree one_p = Nat_O"
    by (simp only: C_one_ax[symmetric] deg_C_ax[OF r_one_neq_zero])
  show ?case by (simp only: h1 h2 lengthL.simps)
next
  case (ConsL a xs)
  have hx: "X_minus a \<noteq> zero_p" by (rule X_minus_nonzero)
  have hp: "poly_of_roots xs \<noteq> zero_p" by (rule poly_of_roots_nonzero)
  have hmul: "degree (X_minus a *P poly_of_roots xs) =
              mynat_add (degree (X_minus a)) (degree (poly_of_roots xs))"
    by (rule deg_mul[OF hx hp])
  have hxd: "degree (X_minus a) = Nat_S Nat_O" by (rule deg_X_minus)
  have hrec: "degree (poly_of_roots xs) = lengthL xs" by (rule ConsL.IH)
  show ?case
    by (simp only: poly_of_roots.simps hmul hxd hrec mynat_add.simps lengthL.simps)
qed





lemma root_factor_list:
  "NoDupL xs \<Longrightarrow> (\<forall>a. InL a xs \<longrightarrow> is_root a p) \<Longrightarrow>
   \<exists>q. p = q *P poly_of_roots xs"
proof (induction xs arbitrary: p)
  case NilL
  show ?case
    by (rule exI[of _ p], simp only: poly_of_roots.simps p_mul_one)
next
  case (ConsL a xs)
  from ConsL.prems(1) have hnd': "NoDupL xs" and hnotin: "\<not> InL a xs"
    by (auto elim: NoDupL.cases)
  have InLa: "InL a (ConsL a xs)" by (rule InL.In_head)
  have ha: "is_root a p" using ConsL.prems(2)[rule_format, OF InLa] .
  obtain r where hpr: "p = r *P X_minus a"
    using root_factor[OF ha] by blast
  have hF: "\<forall>b. InL b xs \<longrightarrow> is_root b r"
  proof (intro allI impI)
    fix b assume hb: "InL b xs"
    have hba: "b \<noteq> a" using hb hnotin by blast
    have hbroot: "is_root b p" using ConsL.prems(2) InL.In_tail[OF hb] by blast
    show "is_root b r" by (rule root_transfer[OF hpr hba hbroot])
  qed
  obtain q where hrq: "r = q *P poly_of_roots xs"
    using ConsL.IH[of r, OF hnd' hF] by blast
  show ?case
  proof (rule exI[of _ q])
    have step1: "p = (q *P poly_of_roots xs) *P X_minus a"
      by (simp only: hpr hrq)
    have step2: "(q *P poly_of_roots xs) *P X_minus a =
                  q *P (poly_of_roots xs *P X_minus a)"
      by (simp only: p_mul_assoc)
    have step3: "poly_of_roots xs *P X_minus a = X_minus a *P poly_of_roots xs"
      by (simp only: p_mul_comm)
    have step4: "X_minus a *P poly_of_roots xs = poly_of_roots (ConsL a xs)"
      by (simp only: poly_of_roots.simps)
    show "p = q *P poly_of_roots (ConsL a xs)"
      by (simp only: step1 step2 step3 step4)
  qed
qed





lemma degree_factorisation:
  "p = q *P poly_of_roots xs \<Longrightarrow> q \<noteq> zero_p \<Longrightarrow>
   degree p = mynat_add (degree q) (lengthL xs)"
proof -
  assume hp: "p = q *P poly_of_roots xs"
  assume hq: "q \<noteq> zero_p"
  have hz: "poly_of_roots xs \<noteq> zero_p" by (rule poly_of_roots_nonzero)
  have h1: "degree p = degree (q *P poly_of_roots xs)"
    by (simp only: hp)
  have h2: "degree (q *P poly_of_roots xs) = mynat_add (degree q) (degree (poly_of_roots xs))"
    by (rule deg_mul[OF hq hz])
  have h3: "degree (poly_of_roots xs) = lengthL xs"
    by (rule deg_poly_of_roots)
  show ?thesis
    by (simp only: h1 h2 h3)
qed

end

end
