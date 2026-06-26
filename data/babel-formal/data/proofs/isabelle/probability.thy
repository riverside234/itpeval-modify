theory probability
  imports Main
begin

datatype 'a mylist = NilL | ConsL 'a "'a mylist"

primrec mapL :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mylist \<Rightarrow> 'b mylist" where
  "mapL f NilL        = NilL"
| "mapL f (ConsL x xs) = ConsL (f x) (mapL f xs)"

primrec fold_addL :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a mylist \<Rightarrow> 'a" where
  "fold_addL add z NilL        = z"
| "fold_addL add z (ConsL x xs) = add x (fold_addL add z xs)"

inductive InL :: "'a \<Rightarrow> 'a mylist \<Rightarrow> bool" where
  In_head : "InL x (ConsL x xs)"
| In_tail : "InL x xs \<Longrightarrow> InL x (ConsL y xs)"

inductive NoDupL :: "'a mylist \<Rightarrow> bool" where
  ND_nil  : "NoDupL NilL"
| ND_cons : "\<lbrakk>\<not> InL x xs; NoDupL xs\<rbrakk> \<Longrightarrow> NoDupL (ConsL x xs)"

type_synonym 'a event = "'a \<Rightarrow> bool"

definition ev_false :: "'a event" where "ev_false \<equiv> \<lambda>_. False"
definition ev_true  :: "'a event" where "ev_true  \<equiv> \<lambda>_. True"
definition ev_inter :: "'a event \<Rightarrow> 'a event \<Rightarrow> 'a event"
  where "ev_inter A B \<equiv> \<lambda>\<omega>. A \<omega> \<and> B \<omega>"
definition ev_union :: "'a event \<Rightarrow> 'a event \<Rightarrow> 'a event"
  where "ev_union A B \<equiv> \<lambda>\<omega>. A \<omega> \<or> B \<omega>"
definition ev_compl :: "'a event \<Rightarrow> 'a event"
  where "ev_compl A \<equiv> \<lambda>\<omega>. \<not> A \<omega>"
definition ev_diff  :: "'a event \<Rightarrow> 'a event \<Rightarrow> 'a event"
  where "ev_diff A B \<equiv> \<lambda>\<omega>. A \<omega> \<and> \<not> B \<omega>"

definition disjoint :: "'a event \<Rightarrow> 'a event \<Rightarrow> bool"
  where "disjoint A B \<equiv> \<forall>\<omega>. \<not> (A \<omega> \<and> B \<omega>)"

fun pairwise_disjoint :: "('a event) mylist \<Rightarrow> bool" where
  "pairwise_disjoint NilL = True"
| "pairwise_disjoint (ConsL _ NilL) = True"
| "pairwise_disjoint (ConsL A (ConsL B xs)) =
     (disjoint A B \<and>
      (\<forall>C. InL C (ConsL B xs) \<longrightarrow> disjoint A C) \<and>
      pairwise_disjoint (ConsL B xs))"

primrec bigUnion :: "('a event) mylist \<Rightarrow> 'a event" where
  "bigUnion NilL         = ev_false"
| "bigUnion (ConsL A xs) = ev_union A (bigUnion xs)"



lemma ev_inter_comm:
  "\<forall>\<omega>. ev_inter A B \<omega> \<longleftrightarrow> ev_inter B A \<omega>"
  unfolding ev_inter_def by blast

lemma ev_union_comm:
  "\<forall>\<omega>. ev_union A B \<omega> \<longleftrightarrow> ev_union B A \<omega>"
  unfolding ev_union_def by blast

lemma ev_inter_assoc:
  "\<forall>\<omega>. ev_inter (ev_inter A B) C \<omega> \<longleftrightarrow> ev_inter A (ev_inter B C) \<omega>"
  unfolding ev_inter_def by blast

lemma ev_union_assoc:
  "\<forall>\<omega>. ev_union (ev_union A B) C \<omega> \<longleftrightarrow> ev_union A (ev_union B C) \<omega>"
  unfolding ev_union_def by blast

lemma ev_inter_distrib_left:
  "\<forall>\<omega>. ev_inter A (ev_union B C) \<omega> \<longleftrightarrow> ev_union (ev_inter A B) (ev_inter A C) \<omega>"
  unfolding ev_inter_def ev_union_def by blast


lemma disjoint_bigUnion:
  "(\<forall>C. InL C xs \<longrightarrow> disjoint A C) \<Longrightarrow> disjoint A (bigUnion xs)"
proof (induction xs)
  case NilL
  show ?case by (simp add: disjoint_def ev_false_def)
next
  case (ConsL B xs)
  have hB: "disjoint A B"
    using ConsL.prems In_head[of B xs] by blast
  have hxs: "\<forall>C. InL C xs \<longrightarrow> disjoint A C"
    using ConsL.prems by (blast intro: In_tail)
  have hIH: "disjoint A (bigUnion xs)"
    by (rule ConsL.IH[OF hxs])
  show ?case
    using hB hIH
    by (metis disjoint_def ev_inter_def ev_union_def bigUnion.simps(2))
qed

locale probability_setup =
  fixes zero one :: "'r"
    and add       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "+R" 65)
    and opp       :: "'r \<Rightarrow> 'r"
    and mul       :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"   (infixl "*R" 70)
    and prob      :: "('a \<Rightarrow> bool) \<Rightarrow> 'r"
    and cprob     :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'r"

  assumes
    add_comm      : "\<And>x y.   x +R y = y +R x"
    and add_assoc : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and add_zero  : "\<And>x.     x +R zero = x"
    and add_opp   : "\<And>x.     x +R opp x = zero"
    and mul_comm  : "\<And>x y.   x *R y = y *R x"
    and mul_assoc : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and mul_one   : "\<And>x.     x *R one = x"
    and dist_l    : "\<And>x y z. x *R (y +R z) = (x *R y) +R (x *R z)"
    and mul_zero  : "\<And>x.     x *R zero = zero"
    and opp_zero  : "opp zero = zero"
    and opp_opp   : "\<And>x.     opp (opp x) = x"
    and opp_mul_right : "\<And>x y. x *R opp y = opp (x *R y)"
    and opp_mul_left  : "\<And>x y. opp x *R y = opp (x *R y)"

    and prob_ext  : "\<And>A B. (\<forall>\<omega>. A \<omega> \<longleftrightarrow> B \<omega>) \<Longrightarrow> prob A = prob B"
    and prob_false_ax : "prob ev_false = zero"
    and prob_true_ax  : "prob ev_true  = one"
    and prob_union_ax :
          "\<And>A B. prob (ev_union A B) =
           prob A +R (prob B +R opp (prob (ev_inter A B)))"
    and prob_compl_ax : "\<And>A. prob (ev_compl A) = one +R opp (prob A)"
    and cprob_mul     : "\<And>A B. prob (ev_inter A B) = cprob A B *R prob B"
    and prob_union_disjoint :
          "\<And>A B. disjoint A B \<Longrightarrow>
           prob (ev_union A B) = prob A +R prob B"
    and disjoint_head_tail :
          "\<And>A xs. pairwise_disjoint (ConsL A xs) \<Longrightarrow>
           disjoint A (bigUnion xs)"
    and indep_compl_both_ax :
          "\<And>A B. prob (ev_inter A B) = prob A *R prob B \<Longrightarrow>
           prob (ev_inter (ev_compl A) (ev_compl B)) =
           prob (ev_compl A) *R prob (ev_compl B)"
    and inclusion_exclusion_three :
          "\<And>A B C.
           prob (ev_union (ev_union A B) C) =
           prob A +R (prob B +R (prob C +R
             opp (prob (ev_inter A B) +R
                  (prob (ev_inter A C) +R
                   (prob (ev_inter B C) +R
                    opp (prob (ev_inter (ev_inter A B) C)))))))"
begin





lemma zero_add: "zero +R x = x"
  using add_comm[of zero x] add_zero[of x] by simp

lemma add_opp_comm: "opp x +R x = zero"
  using add_opp[of x] add_comm[of x "opp x"] by simp


lemma sub_of_eq: "a = b +R c \<Longrightarrow> c = a +R opp b"
proof -
  assume h: "a = b +R c"
  have "a +R opp b = (b +R c) +R opp b" by (simp only: h)
  also have "\<dots> = b +R (c +R opp b)" by (rule add_assoc)
  also have "\<dots> = b +R (opp b +R c)"
    by (simp only: add_comm[of c "opp b"])
  also have "\<dots> = (b +R opp b) +R c" by (rule add_assoc[symmetric])
  also have "\<dots> = zero +R c" by (simp only: add_opp)
  also have "\<dots> = c +R zero" by (rule add_comm)
  also have "\<dots> = c" by (rule add_zero)
  finally show ?thesis by (rule sym)
qed





definition indep :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "indep A B \<equiv> prob (ev_inter A B) = prob A *R prob B"





lemma prob_union_comm:
  "prob (ev_union A B) = prob (ev_union B A)"
  by (rule prob_ext) (auto simp: ev_union_def)

lemma prob_union_idem:
  "prob (ev_union A A) = prob A"
proof -
  have hcap: "prob (ev_inter A A) = prob A"
    by (rule prob_ext) (simp add: ev_inter_def)
  have "prob (ev_union A A) =
        prob A +R (prob A +R opp (prob A))"
    by (simp only: prob_union_ax hcap)
  also have "\<dots> = prob A +R zero" by (simp only: add_opp)
  also have "\<dots> = prob A"        by (rule add_zero)
  finally show ?thesis .
qed





lemma prob_diff:
  "prob (ev_diff A B) = prob A +R opp (prob (ev_inter A B))"
proof -
  have heq_diff: "prob (ev_diff A B) = prob (ev_inter A (ev_compl B))"
    by (rule prob_ext) (simp add: ev_diff_def ev_inter_def ev_compl_def)
  have hdisjoint: "disjoint (ev_inter A B) (ev_inter A (ev_compl B))"
    unfolding disjoint_def ev_inter_def ev_compl_def by blast
  have hpart: "\<forall>\<omega>. A \<omega> \<longleftrightarrow> ev_union (ev_inter A B) (ev_inter A (ev_compl B)) \<omega>"
    unfolding ev_union_def ev_inter_def ev_compl_def by blast
  have hsumA: "prob A = prob (ev_inter A B) +R prob (ev_inter A (ev_compl B))"
  proof -
    have h1: "prob A = prob (ev_union (ev_inter A B) (ev_inter A (ev_compl B)))"
      by (rule prob_ext) (rule hpart)
    show ?thesis by (simp only: h1, rule prob_union_disjoint[OF hdisjoint])
  qed
  have hsub: "prob (ev_inter A (ev_compl B)) = prob A +R opp (prob (ev_inter A B))"
    by (rule sub_of_eq[OF hsumA])
  show ?thesis by (simp only: heq_diff hsub)
qed





lemma bayes_symm:
  "cprob A B *R prob B = cprob B A *R prob A"
proof -
  have h1: "cprob A B *R prob B = prob (ev_inter A B)"
    by (rule cprob_mul[symmetric])
  have h2: "prob (ev_inter A B) = prob (ev_inter B A)"
    by (rule prob_ext) (rule ev_inter_comm)
  have h3: "prob (ev_inter B A) = cprob B A *R prob A"
    by (rule cprob_mul)
  show ?thesis by (simp only: h1 h2 h3)
qed





lemma law_total_prob:
  "prob A =
   cprob A B *R prob B +R cprob A (ev_compl B) *R prob (ev_compl B)"
proof -
  have hpart: "\<forall>\<omega>. A \<omega> \<longleftrightarrow> ev_union (ev_inter A B) (ev_inter A (ev_compl B)) \<omega>"
    unfolding ev_union_def ev_inter_def ev_compl_def by blast
  have hdisjoint: "disjoint (ev_inter A B) (ev_inter A (ev_compl B))"
    unfolding disjoint_def ev_inter_def ev_compl_def by blast
  have hsumA: "prob A = prob (ev_inter A B) +R prob (ev_inter A (ev_compl B))"
  proof -
    have h1: "prob A = prob (ev_union (ev_inter A B) (ev_inter A (ev_compl B)))"
      by (rule prob_ext) (rule hpart)
    show ?thesis by (simp only: h1, rule prob_union_disjoint[OF hdisjoint])
  qed
  have h1: "prob (ev_inter A B) = cprob A B *R prob B"
    by (rule cprob_mul)
  have h2: "prob (ev_inter A (ev_compl B)) = cprob A (ev_compl B) *R prob (ev_compl B)"
    by (rule cprob_mul)
  show ?thesis by (simp only: hsumA h1 h2)
qed





lemma prob_union_indep:
  "indep A B \<Longrightarrow>
   prob (ev_union A B) =
   prob A +R (prob B +R opp (prob A *R prob B))"
proof -
  assume hI: "indep A B"
  have hIeq: "prob (ev_inter A B) = prob A *R prob B"
    using hI unfolding indep_def .
  show ?thesis by (simp only: prob_union_ax hIeq)
qed





lemma indep_symm: "indep A B \<Longrightarrow> indep B A"
proof -
  assume hI: "indep A B"
  have hIeq: "prob (ev_inter A B) = prob A *R prob B"
    using hI unfolding indep_def .
  have hcap: "prob (ev_inter B A) = prob (ev_inter A B)"
    by (rule prob_ext) (rule ev_inter_comm)
  show "indep B A"
    unfolding indep_def
    by (simp only: hcap hIeq mul_comm)
qed

lemma indep_compl_right: "indep A B \<Longrightarrow> indep A (ev_compl B)"
proof -
  assume hI: "indep A B"
  have hIeq: "prob (ev_inter A B) = prob A *R prob B"
    using hI unfolding indep_def .

  have h1: "prob (ev_inter A (ev_compl B)) = prob A +R opp (prob (ev_inter A B))"
  proof -
    have heq: "prob (ev_diff A B) = prob (ev_inter A (ev_compl B))"
      by (rule prob_ext) (simp add: ev_diff_def ev_inter_def ev_compl_def)
    show ?thesis using prob_diff by (simp only: heq[symmetric])
  qed

  have h2: "prob (ev_inter A (ev_compl B)) =
            prob A +R opp (prob A *R prob B)"
    by (simp only: h1 hIeq)

  have halg: "prob A +R opp (prob A *R prob B) =
              prob A *R prob (ev_compl B)"
  proof -
    have rhs_eq: "prob A *R prob (ev_compl B) =
                  prob A +R opp (prob A *R prob B)"
    proof -
      have "prob A *R prob (ev_compl B) = prob A *R (one +R opp (prob B))"
        by (simp only: prob_compl_ax)
      also have "\<dots> = prob A *R one +R prob A *R opp (prob B)"
        by (rule dist_l)
      also have "\<dots> = prob A +R prob A *R opp (prob B)"
        by (simp only: mul_one)
      also have "\<dots> = prob A +R opp (prob A *R prob B)"
        by (simp only: opp_mul_right)
      finally show ?thesis .
    qed
    show ?thesis by (rule rhs_eq[symmetric])
  qed
  show "indep A (ev_compl B)"
    unfolding indep_def by (simp only: h2 halg)
qed

lemma indep_compl_left: "indep A B \<Longrightarrow> indep (ev_compl A) B"
proof -
  assume hI: "indep A B"
  have hBA  : "indep B A"             by (rule indep_symm[OF hI])
  have hBcA : "indep B (ev_compl A)"  by (rule indep_compl_right[OF hBA])
  show ?thesis                         by (rule indep_symm[OF hBcA])
qed

lemma indep_compl_both: "indep A B \<Longrightarrow> indep (ev_compl A) (ev_compl B)"
  unfolding indep_def
  by (rule indep_compl_both_ax)





lemma prob_bigUnion_disjoint:
  "pairwise_disjoint xs \<Longrightarrow>
   prob (bigUnion xs) = fold_addL (+R) zero (mapL prob xs)"
proof (induction xs)
  case NilL
  show ?case
    by (simp add: prob_false_ax)
next
  case (ConsL A xs)
  assume hpw: "pairwise_disjoint (ConsL A xs)"
  show "prob (bigUnion (ConsL A xs)) = fold_addL (+R) zero (mapL prob (ConsL A xs))"
  proof (cases xs)
    case NilL
    have hunion: "prob (ev_union A ev_false) = prob A"
      by (rule prob_ext) (simp add: ev_union_def ev_false_def)
    show ?thesis
      by (simp add: NilL add_zero hunion)
  next
    case (ConsL B xs')

    have hpw_exp: "disjoint A B \<and>
                   (\<forall>C. InL C (ConsL B xs') \<longrightarrow> disjoint A C) \<and>
                   pairwise_disjoint (ConsL B xs')"
      using hpw by (simp add: ConsL)
    have hpw' : "pairwise_disjoint (ConsL B xs')"
      using hpw_exp by blast

    have hAdisj: "disjoint A (bigUnion (ConsL B xs'))"
    proof -
      have "\<forall>C. InL C (ConsL B xs') \<longrightarrow> disjoint A C"
        using hpw_exp by blast
      from disjoint_bigUnion[OF this] show ?thesis .
    qed

    have hU: "prob (bigUnion (ConsL A (ConsL B xs'))) =
              prob A +R prob (bigUnion (ConsL B xs'))"
    proof -
      have eq: "bigUnion (ConsL A (ConsL B xs')) =
                ev_union A (bigUnion (ConsL B xs'))"
        by simp
      show ?thesis by (simp only: eq, rule prob_union_disjoint[OF hAdisj])
    qed

    have hIH: "prob (bigUnion (ConsL B xs')) =
               fold_addL (+R) zero (mapL prob (ConsL B xs'))"
    proof -
      have hpw_xs: "pairwise_disjoint xs" by (simp add: ConsL hpw')
      from ConsL.IH[OF hpw_xs] show ?thesis by (simp add: ConsL)
    qed
    show ?thesis
      by (simp only: ConsL hU hIH mapL.simps fold_addL.simps)
  qed
qed





lemma prob_bigUnion_disjoint_zero:
  "pairwise_disjoint xs \<Longrightarrow>
   (\<forall>A. InL A xs \<longrightarrow> prob A = zero) \<Longrightarrow>
   prob (bigUnion xs) = zero"
proof (induction xs)
  case NilL
  show ?case by (simp add: prob_false_ax)
next
  case (ConsL A xs)
  assume hpw   : "pairwise_disjoint (ConsL A xs)"
  assume hzero : "\<forall>B. InL B (ConsL A xs) \<longrightarrow> prob B = zero"
  show "prob (bigUnion (ConsL A xs)) = zero"
  proof (cases xs)
    case NilL
    have hA0: "prob A = zero" using hzero In_head[of A xs] by blast
    have hunion: "prob (ev_union A ev_false) = prob A"
      by (rule prob_ext) (simp add: ev_union_def ev_false_def)
    show ?thesis by (simp add: NilL hunion hA0)
  next
    case (ConsL B xs')
    have hpw_exp: "disjoint A B \<and>
                   (\<forall>C. InL C (ConsL B xs') \<longrightarrow> disjoint A C) \<and>
                   pairwise_disjoint (ConsL B xs')"
      using hpw by (simp add: ConsL)
    then obtain hpw' where hpw': "pairwise_disjoint (ConsL B xs')"
      by blast
    have hAdisj: "disjoint A (bigUnion (ConsL B xs'))"
    proof -
      have "\<forall>C. InL C (ConsL B xs') \<longrightarrow> disjoint A C"
        using hpw_exp by blast
      from disjoint_bigUnion[OF this] show ?thesis .
    qed
    have hA0: "prob A = zero"
      using hzero In_head[of A xs] by blast
    have htailzero: "\<forall>C. InL C (ConsL B xs') \<longrightarrow> prob C = zero"
    proof (intro allI impI)
      fix C
      assume hC: "InL C (ConsL B xs')"
      have "InL C (ConsL A (ConsL B xs'))"
        by (rule In_tail[OF hC])
      then show "prob C = zero"
        using hzero ConsL by blast
    qed
    have htail0: "prob (bigUnion (ConsL B xs')) = zero"
    proof -
      have hpw_xs: "pairwise_disjoint xs"
        using hpw' by (simp add: ConsL)
      have hzero_xs: "\<And>C. InL C xs \<Longrightarrow> prob C = zero"
        using htailzero by (simp add: ConsL)
      have hzero_xs_obj: "\<forall>C. InL C xs \<longrightarrow> prob C = zero"
        using hzero_xs by blast
      have "prob (bigUnion xs) = zero"
        using ConsL.IH[OF hpw_xs] hzero_xs_obj by blast
      then show ?thesis by (simp add: ConsL)
    qed
    have hU: "prob (bigUnion (ConsL A (ConsL B xs'))) =
              prob A +R prob (bigUnion (ConsL B xs'))"
    proof -
      have eq: "bigUnion (ConsL A (ConsL B xs')) =
                ev_union A (bigUnion (ConsL B xs'))"
        by simp
      show ?thesis by (simp only: eq, rule prob_union_disjoint[OF hAdisj])
    qed
    have hfull0: "prob (bigUnion (ConsL A (ConsL B xs'))) = zero"
      using hU hA0 htail0 by (simp add: add_zero)
    have hfull0': "prob (ev_union A (ev_union B (bigUnion xs'))) = zero"
      using hfull0 by simp
    show ?thesis
      by (simp add: ConsL hfull0')
  qed
qed

end

end
