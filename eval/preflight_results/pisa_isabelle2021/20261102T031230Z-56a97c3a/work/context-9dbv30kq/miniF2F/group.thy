theory group
  imports Main
begin
declare [[quick_and_dirty = true]]




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
  sorry

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma mul_right_cancel:
  assumes h: "b ** a = c ** a"
  shows "b = c"
  