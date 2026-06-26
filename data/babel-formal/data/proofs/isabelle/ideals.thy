theory ideals
  imports Main
begin

locale cring =
  fixes zero :: "'r"
    and one  :: "'r"
    and add  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "+R" 65)
    and mul  :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "*R" 70)
    and opp  :: "'r \<Rightarrow> 'r"
  assumes add_comm  : "\<And>x y. x +R y = y +R x"
    and   add_assoc : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and   add_zero  : "\<And>x. x +R zero = x"
    and   add_opp   : "\<And>x. x +R opp x = zero"
    and   mul_comm  : "\<And>x y. x *R y = y *R x"
    and   mul_assoc : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and   mul_one   : "\<And>x. x *R one = x"
    and   dist_l    : "\<And>a x y. a *R (x +R y) = (a *R x) +R (a *R y)"
    and   opp_add   : "\<And>x y. opp (x +R y) = opp x +R opp y"
begin


lemma add_left_comm: "x +R (y +R z) = y +R (x +R z)"
proof -
  have "x +R (y +R z) = (x +R y) +R z" by (rule add_assoc [symmetric])
  also have "\<dots> = (y +R x) +R z"       by (simp add: add_comm)
  also have "\<dots> = y +R (x +R z)"       by (rule add_assoc)
  finally show ?thesis .
qed

lemma zero_add: "zero +R x = x"
  by (simp add: add_comm add_zero)





definition IsIdeal :: "('r \<Rightarrow> bool) \<Rightarrow> bool"
  where "IsIdeal I \<equiv>
    I zero \<and>
    (\<forall>x y. I x \<longrightarrow> I y \<longrightarrow> I (x +R y)) \<and>
    (\<forall>x.   I x \<longrightarrow> I (opp x)) \<and>
    (\<forall>a x. I x \<longrightarrow> I (a *R x))"





definition Inter :: "('i \<Rightarrow> 'r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "Inter F \<equiv> \<lambda>x. \<forall>i. F i x"

lemma inter_isIdeal:
  assumes h: "\<forall>i. IsIdeal (F i)"
  shows "IsIdeal (Inter F)"
  unfolding IsIdeal_def Inter_def
  using h unfolding IsIdeal_def
  by blast





definition isum :: "('r \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool"
  where "isum I J \<equiv> \<lambda>x. \<exists>a b. I a \<and> J b \<and> x = a +R b"

lemma sum_isIdeal:
  assumes hI: "IsIdeal I" and hJ: "IsIdeal J"
  shows "IsIdeal (isum I J)"
proof -
  from hI have hI0   : "I zero"
           and hIadd : "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> I (x +R y)"
           and hIopp : "\<And>x. I x \<Longrightarrow> I (opp x)"
           and hImul : "\<And>a x. I x \<Longrightarrow> I (a *R x)"
    unfolding IsIdeal_def by blast+
  from hJ have hJ0   : "J zero"
           and hJadd : "\<And>x y. J x \<Longrightarrow> J y \<Longrightarrow> J (x +R y)"
           and hJopp : "\<And>x. J x \<Longrightarrow> J (opp x)"
           and hJmul : "\<And>a x. J x \<Longrightarrow> J (a *R x)"
    unfolding IsIdeal_def by blast+
  show ?thesis
    unfolding IsIdeal_def isum_def
  proof (intro conjI allI impI)

    show "\<exists>a b. I a \<and> J b \<and> zero = a +R b"
      using hI0 hJ0 by (metis add_zero)


    fix x y
    assume hx: "\<exists>a b. I a \<and> J b \<and> x = a +R b"
    assume hy: "\<exists>a b. I a \<and> J b \<and> y = a +R b"
    show "\<exists>a b. I a \<and> J b \<and> x +R y = a +R b"
    proof -
      from hx obtain a  b  where ha  : "I a"  and hb  : "J b"  and hxeq : "x = a  +R b"  by blast
      from hy obtain a' b' where ha' : "I a'" and hb' : "J b'" and hyeq : "y = a' +R b'" by blast
      have rearrange : "(a +R b) +R (a' +R b') = (a +R a') +R (b +R b')"
      proof -
        have "(a +R b) +R (a' +R b') = a +R (b +R (a' +R b'))"  by (rule add_assoc)
        also have "\<dots> = a +R (a' +R (b +R b'))"                  by (simp add: add_left_comm)
        also have "\<dots> = (a +R a') +R (b +R b')"                  by (rule add_assoc [symmetric])
        finally show ?thesis .
      qed
      show ?thesis
        using ha ha' hb hb' hxeq hyeq rearrange
        by (metis hIadd hJadd)
    qed


    fix x
    assume hx: "\<exists>a b. I a \<and> J b \<and> x = a +R b"
    show "\<exists>a b. I a \<and> J b \<and> opp x = a +R b"
    proof -
      from hx obtain a b where ha: "I a" and hb: "J b" and hxeq: "x = a +R b" by blast
      have "opp (a +R b) = opp a +R opp b" by (rule opp_add)
      with hxeq ha hb hIopp hJopp show ?thesis by blast
    qed


    fix c x
    assume hx: "\<exists>a b. I a \<and> J b \<and> x = a +R b"
    show "\<exists>a b. I a \<and> J b \<and> c *R x = a +R b"
    proof -
      from hx obtain a b where ha: "I a" and hb: "J b" and hxeq: "x = a +R b" by blast
      have "c *R (a +R b) = (c *R a) +R (c *R b)" by (rule dist_l)
      with hxeq ha hb hImul hJmul show ?thesis by blast
    qed
  qed
qed

end

end
