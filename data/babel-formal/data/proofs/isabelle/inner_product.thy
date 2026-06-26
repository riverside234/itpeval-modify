theory inner_product
  imports Main
begin

locale inner_product =
  fixes zero_R one_R :: "'r"
    and add_R :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "+R" 65)
    and mul_R :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"  (infixl "*R" 70)
    and opp_R :: "'r \<Rightarrow> 'r"
    and zeroV :: "'v"
    and addV  :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"  (infixl "+V" 65)
    and oppV  :: "'v \<Rightarrow> 'v"
    and smul  :: "'r \<Rightarrow> 'v \<Rightarrow> 'v"
    and ip    :: "'v \<Rightarrow> 'v \<Rightarrow> 'r"

  assumes add_R_comm    : "\<And>x y. x +R y = y +R x"
    and   add_R_assoc   : "\<And>x y z. (x +R y) +R z = x +R (y +R z)"
    and   add_R_zero    : "\<And>x. x +R zero_R = x"
    and   zero_R_add    : "\<And>x. zero_R +R x = x"
    and   add_R_opp     : "\<And>x. x +R opp_R x = zero_R"
    and   mul_R_comm    : "\<And>x y. x *R y = y *R x"
    and   mul_R_assoc   : "\<And>x y z. (x *R y) *R z = x *R (y *R z)"
    and   mul_R_one     : "\<And>x. x *R one_R = x"
    and   mul_opp_one   : "\<And>x. opp_R one_R *R x = opp_R x"
    and   opp_R_opp     : "\<And>x. opp_R (opp_R x) = x"

    and   addV_comm     : "\<And>u v. u +V v = v +V u"
    and   addV_assoc    : "\<And>u v w. (u +V v) +V w = u +V (v +V w)"
    and   addV_zero     : "\<And>u. u +V zeroV = u"
    and   smul_addV     : "\<And>a u v. smul a (u +V v) = smul a u +V smul a v"
    and   one_smul      : "\<And>u. smul one_R u = u"
    and   opp_smul_one  : "\<And>u. oppV u = smul (opp_R one_R) u"

    and   lin_left_add  : "\<And>u v w. ip (u +V v) w = ip u w +R ip v w"
    and   lin_left_smul : "\<And>a u v. ip (smul a u) v = a *R ip u v"
    and   lin_right_add : "\<And>u v w. ip u (v +V w) = ip u v +R ip u w"
    and   lin_right_smul: "\<And>a u v. ip u (smul a v) = a *R ip u v"
    and   ip_symm       : "\<And>u v. ip u v = ip v u"
begin





definition subV :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"  (infixl "-V" 65)
  where "u -V v \<equiv> u +V oppV v"

lemma add_R_left_comm: "x +R (y +R z) = y +R (x +R z)"
proof -
  have "x +R (y +R z) = (x +R y) +R z" by (rule add_R_assoc [symmetric])
  also have "\<dots> = (y +R x) +R z"       by (simp add: add_R_comm)
  also have "\<dots> = y +R (x +R z)"       by (rule add_R_assoc)
  finally show ?thesis .
qed





lemma ip_neg_left: "ip (oppV u) v = opp_R (ip u v)"
proof -
  have "ip (oppV u) v = ip (smul (opp_R one_R) u) v" by (simp add: opp_smul_one)
  also have "\<dots> = opp_R one_R *R ip u v"              by (rule lin_left_smul)
  also have "\<dots> = opp_R (ip u v)"                     by (rule mul_opp_one)
  finally show ?thesis .
qed

lemma ip_neg_right: "ip u (oppV v) = opp_R (ip u v)"
proof -
  have "ip u (oppV v) = ip u (smul (opp_R one_R) v)" by (simp add: opp_smul_one)
  also have "\<dots> = opp_R one_R *R ip u v"              by (rule lin_right_smul)
  also have "\<dots> = opp_R (ip u v)"                     by (rule mul_opp_one)
  finally show ?thesis .
qed





lemma ip_add_add:
  "ip (u +V v) (u +V v) =
    (ip u u +R ip v u) +R (ip u v +R ip v v)"
proof -
  have H : "ip (u +V v) (u +V v) = ip (u +V v) u +R ip (u +V v) v"
    by (rule lin_right_add)
  have H1: "ip (u +V v) u = ip u u +R ip v u" by (rule lin_left_add)
  have H2: "ip (u +V v) v = ip u v +R ip v v" by (rule lin_left_add)
  show ?thesis by (simp add: H H1 H2)
qed





lemma ip_neg_neg: "ip (oppV v) (oppV v) = ip v v"
proof -
  have "ip (oppV v) (oppV v) = opp_R (ip (oppV v) v)" by (rule ip_neg_right)
  also have "\<dots> = opp_R (opp_R (ip v v))"
    by (simp add: ip_neg_left)
  also have "\<dots> = ip v v" by (rule opp_R_opp)
  finally show ?thesis .
qed

lemma ip_sub_sub:
  "ip (u -V v) (u -V v) =
    (ip u u +R opp_R (ip v u)) +R (opp_R (ip u v) +R ip v v)"
proof -
  have H : "ip (u -V v) (u -V v)
          = ip (u -V v) u +R ip (u -V v) (oppV v)"
    unfolding subV_def by (rule lin_right_add)
  have H1: "ip (u -V v) u
          = ip u u +R ip (oppV v) u"
    unfolding subV_def by (rule lin_left_add)
  have H2: "ip (u -V v) (oppV v)
          = ip u (oppV v) +R ip (oppV v) (oppV v)"
    unfolding subV_def by (rule lin_left_add)
  have Hn1: "ip (oppV v) u = opp_R (ip v u)"   by (rule ip_neg_left)
  have Hn2: "ip u (oppV v) = opp_R (ip u v)"   by (rule ip_neg_right)
  have Hnn: "ip (oppV v) (oppV v) = ip v v"    by (rule ip_neg_neg)
  show ?thesis by (simp add: H H1 H2 Hn1 Hn2 Hnn)
qed





lemma pythagoras:
  assumes h: "ip u v = zero_R"
  shows "ip (u +V v) (u +V v) = ip u u +R ip v v"
proof -
  have hvu: "ip v u = zero_R" by (simp add: ip_symm h)
  have "ip (u +V v) (u +V v) = (ip u u +R ip v u) +R (ip u v +R ip v v)"
    by (rule ip_add_add)
  also have "\<dots> = (ip u u +R zero_R) +R (zero_R +R ip v v)"
    by (simp add: h hvu)
  also have "\<dots> = ip u u +R ip v v"
    by (simp add: add_R_zero zero_R_add)
  finally show ?thesis .
qed





lemma parallelogram:
  "ip (u +V v) (u +V v) +R ip (u -V v) (u -V v) =
    ((ip u u +R ip v u) +R (ip u v +R ip v v)) +R
    ((ip u u +R opp_R (ip v u)) +R (opp_R (ip u v) +R ip v v))"
  by (simp add: ip_add_add ip_sub_sub)

end

end
