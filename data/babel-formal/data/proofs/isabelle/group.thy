theory group
  imports Main
begin



locale group =
  fixes mul :: "'a => 'a => 'a"  (infixl "**" 70)
    and one :: "'a"
    and inv :: "'a => 'a"
  assumes mul_assoc : "a ** (b ** c) = (a ** b) ** c"
    and   mul_one   : "a ** one = a"
    and   one_mul   : "one ** a = a"
    and   mul_inv_l : "inv a ** a = one"
    and   mul_inv_r : "a ** inv a = one"
begin



lemma mul_left_cancel:
  assumes h: "a ** b = a ** c"
  shows "b = c"
proof -
  have "inv a ** (a ** b) = inv a ** (a ** c)"
    using h by simp
  then show ?thesis
    by (simp add: mul_assoc mul_inv_l one_mul)
qed

lemma mul_right_cancel:
  assumes h: "b ** a = c ** a"
  shows "b = c"
proof -
  have "(b ** a) ** inv a = (c ** a) ** inv a"
    using h by simp
  then show ?thesis
    by (simp add: mul_assoc [symmetric] mul_inv_r mul_one)
qed

lemma inv_inv: "inv (inv a) = a"
proof (rule mul_right_cancel)
  show "inv (inv a) ** inv a = a ** inv a"
    by (simp add: mul_inv_l mul_inv_r)
qed

lemma inv_mul: "inv (a ** b) = inv b ** inv a"
proof (rule mul_right_cancel)
  have lhs: "inv (a ** b) ** (a ** b) = one"
    by (simp add: mul_inv_l)
  have rhs: "(inv b ** inv a) ** (a ** b) = one"
    by (simp add: mul_assoc mul_assoc [symmetric] mul_inv_l one_mul mul_inv_l)
  show "inv (a ** b) ** (a ** b) = (inv b ** inv a) ** (a ** b)"
    by (simp add: lhs rhs)
qed

lemma inv_eq_of_mul_eq_one:
  assumes h: "a ** b = one"
  shows "b = inv a"
proof -
  have "inv a ** (a ** b) = inv a ** one"
    using h by simp
  then show ?thesis
    by (simp add: mul_assoc mul_inv_l one_mul mul_one)
qed

end




locale group_comm = group +
  assumes mul_comm : "a ** b = b ** a"
begin

lemma mul_rotate': "a ** (b ** c) = b ** (c ** a)"
proof -
  have "a ** (b ** c) = (b ** c) ** a" by (simp add: mul_comm)
  also have "... = b ** (c ** a)" by (simp only: mul_assoc [symmetric])
  finally show ?thesis .
qed

end




locale group_action =
  group mul one inv
    for mul :: "'a => 'a => 'a"  (infixl "**" 70)
    and one :: "'a"
    and inv :: "'a => 'a" +
  fixes act :: "'a => 'b => 'b"  (infixr "acts" 73)
  assumes act_one : "one acts x = x"
    and   act_mul : "(g ** h) acts x = g acts (h acts x)"
begin



lemma act_inv: "inv g acts (g acts x) = x"
proof -
  have "(inv g ** g) acts x = x"
    by (simp add: mul_inv_l act_one)
  then show ?thesis
    by (simp add: act_mul)
qed

lemma act_inv_r: "g acts (inv g acts x) = x"
proof -
  have "(g ** inv g) acts x = x"
    by (simp add: mul_inv_r act_one)
  then show ?thesis
    by (simp add: act_mul)
qed

definition orbit :: "'b => 'b => bool"
  where "orbit x y == (EX g. g acts x = y)"

definition stabilizer :: "'b => 'a => bool"
  where "stabilizer x g == g acts x = x"

lemma orbit_refl: "orbit x x"
  unfolding orbit_def
  by (rule exI[of _ one]) (simp add: act_one)

lemma orbit_sym:
  assumes "orbit x y"
  shows "orbit y x"
proof -
  obtain g where hg: "g acts x = y"
    using assms unfolding orbit_def by blast
  show ?thesis
    unfolding orbit_def
    by (rule exI[of _ "inv g"])
       (simp add: hg [symmetric] act_mul [symmetric] mul_inv_l act_one)
qed

lemma orbit_trans:
  assumes "orbit x y" "orbit y z"
  shows "orbit x z"
proof -
  obtain g1 where hg1: "g1 acts x = y"
    using assms(1) unfolding orbit_def by blast
  obtain g2 where hg2: "g2 acts y = z"
    using assms(2) unfolding orbit_def by blast
  show ?thesis
    unfolding orbit_def
    by (rule exI[of _ "g2 ** g1"])
       (simp add: act_mul hg1 hg2)
qed

lemma orbit_partition:
  assumes hxy: "orbit x y"
  shows "orbit x z = orbit y z"
proof
  assume hz: "orbit x z"
  obtain g1 where hg1: "g1 acts x = y"
    using hxy unfolding orbit_def by blast
  obtain g2 where hg2: "g2 acts x = z"
    using hz unfolding orbit_def by blast
  show "orbit y z"
    unfolding orbit_def
  proof (rule exI[of _ "g2 ** inv g1"])
    have h1: "inv g1 acts y = x"
    proof -
      have "inv g1 acts y = inv g1 acts (g1 acts x)" by (simp add: hg1)
      also have "... = x" by (simp add: act_inv)
      finally show ?thesis .
    qed
    show "(g2 ** inv g1) acts y = z"
      by (simp add: act_mul h1 hg2)
  qed
next
  assume hz: "orbit y z"
  obtain g1 where hg1: "g1 acts x = y"
    using hxy unfolding orbit_def by blast
  obtain g2 where hg2: "g2 acts y = z"
    using hz unfolding orbit_def by blast
  show "orbit x z"
    unfolding orbit_def
    by (rule exI[of _ "g2 ** g1"])
       (simp add: act_mul hg1 hg2)
qed

lemma stabilizer_mul:
  assumes "stabilizer x g" "stabilizer x h"
  shows "stabilizer x (g ** h)"
  using assms unfolding stabilizer_def
  by (simp add: act_mul)

lemma stabilizer_inv:
  assumes hg: "stabilizer x g"
  shows "stabilizer x (inv g)"
  unfolding stabilizer_def
  using hg unfolding stabilizer_def
  by (metis act_inv act_mul mul_inv_l act_one)

lemma stabilizer_one: "stabilizer x one"
  unfolding stabilizer_def
  by (simp add: act_one)

lemma stabilizer_conjugate:
  assumes hh: "stabilizer x h"
  shows "stabilizer (g acts x) (g ** h ** inv g)"
  using assms unfolding stabilizer_def
  by (simp add: act_mul act_inv)

lemma stabilizer_conjugate_orbit:
  assumes hxy: "g acts x = y"
  shows "stabilizer y h = stabilizer x (inv g ** h ** g)"
proof
  assume hy: "stabilizer y h"
  show "stabilizer x (inv g ** h ** g)"
    unfolding stabilizer_def
  proof -
    have hy': "h acts y = y" using hy unfolding stabilizer_def .
    have h1: "(inv g ** h ** g) acts x = inv g acts (h acts (g acts x))"
      by (simp add: act_mul)
    have h2: "h acts (g acts x) = g acts x" by (simp add: hxy hy')
    show "(inv g ** h ** g) acts x = x" by (simp add: h1 h2 act_inv)
  qed
next
  assume hh: "stabilizer x (inv g ** h ** g)"
  show "stabilizer y h"
    unfolding stabilizer_def
  proof -
    have hh': "(inv g ** h ** g) acts x = x"
      using hh unfolding stabilizer_def .
    have expand: "inv g acts (h acts (g acts x)) = x"
      by (simp add: act_mul [symmetric] mul_assoc hh')
    have hacts: "h acts (g acts x) = g acts x"
      using act_inv_r [of g "h acts (g acts x)"] expand by simp
    show "h acts y = y" by (simp add: hxy [symmetric] hacts)
  qed
qed

end

end
