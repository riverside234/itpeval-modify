class Group (G : Type) where
  inv : G → G
  one : G
  mul : G → G → G
  mul_assoc : ∀ a b c : G, mul a (mul b c) = mul (mul a b) c
  mul_one   : ∀ a : G, mul a one = a
  one_mul   : ∀ a : G, mul one a = a
  mul_inv_l : ∀ a : G, mul (inv a) a = one
  mul_inv_r : ∀ a : G, mul a (inv a) = one

namespace Group

infixl:70 " * " => Group.mul
postfix:max "⁻¹" => Group.inv

class GroupComm (G : Type) [Group G] where
  mul_comm : ∀ a b : G, a * b = b * a

section MulRotate
  variable {G : Type} [Group G] [GroupComm G]

  theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
    rw [GroupComm.mul_comm]
    rw [← Group.mul_assoc]

end MulRotate
section GroupLemmas
  variable {G : Type} [Group G]

  theorem mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
    have h' : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw [h]
    repeat rw [Group.mul_assoc] at h'
    repeat rw [Group.mul_inv_l] at h'
    repeat rw [Group.one_mul] at h'
    exact h'

  theorem mul_right_cancel (a b c : G) (h : b * a = c * a) : b = c := by
    have h' : (b * a) * a⁻¹ = (c * a) * a⁻¹ := by rw [h]
    repeat rw [← Group.mul_assoc] at h'
    repeat rw [Group.mul_inv_r] at h'
    repeat rw [Group.mul_one] at h'
    exact h'

  theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
    have h : (a⁻¹)⁻¹ * a⁻¹ = a * a⁻¹ := by
      rw [Group.mul_inv_l, Group.mul_inv_r]
    exact mul_right_cancel _ _ _ h

  theorem inv_mul (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
    have h : (a * b)⁻¹ * (a * b) = (b⁻¹ * a⁻¹) * (a * b) := by
      rw [Group.mul_inv_l]
      repeat rw [← Group.mul_assoc]
      rw [Group.mul_assoc (a⁻¹) a b]
      rw [Group.mul_inv_l]
      rw [Group.one_mul]
      rw [Group.mul_inv_l]
    exact mul_right_cancel _ _ _ h

  theorem inv_eq_of_mul_eq_one (a b : G) (h : a * b = one) : b = a⁻¹ := by
    have h' : a⁻¹ * (a * b) = a⁻¹ * one := by rw [h]
    rw [Group.mul_assoc, Group.mul_inv_l, Group.one_mul, Group.mul_one] at h'
    exact h'

end GroupLemmas

class Act (G : Type) (X : Type) [Group G] where
  act : G → X → X
  act_one : ∀ x : X, act one x = x
  act_mul : ∀ g h : G, ∀ x : X, act (g * h) x = act g (act h x)


section ActionLemmas
  variable {G : Type} {X : Type}
  [Group G] [Act G X]

  infixr:73 " • " => Act.act

  theorem act_inv (g : G) (x : X) : g⁻¹ • (g • x) = x := by
    have h : (g⁻¹ * g) • x = x := by
      rw [Group.mul_inv_l]
      apply Act.act_one
    rw [Act.act_mul] at h
    exact h

  theorem act_inv_r (g : G) (x : X) : g • (g⁻¹ • x) = x := by
    have h : (g * g⁻¹) • x = x := by
      rw [Group.mul_inv_r]
      apply Act.act_one
    rw [Act.act_mul] at h
    exact h

  def orbit {G : Type} {X : Type} [Group G] [Act G X] (x : X) : X → Prop :=
    fun y => ∃ g : G, g • x = y

  def stabilizer (x : X) : G → Prop := fun g => g • x = x

  theorem orbit_refl
    (x : X) : orbit (G:=G) x x := by
    exists one
    exact Act.act_one x

  theorem orbit_sym (x y : X) (h : orbit (G:=G) x y) : orbit (G:=G) y x := by
    rcases h with ⟨g, hg⟩
    exists g⁻¹
    rw [← hg, ← Act.act_mul, Group.mul_inv_l, Act.act_one]

  theorem orbit_trans (x y z : X) (h1 : orbit (G:=G) x y) (h2 : orbit (G:=G) y z) : orbit (G:=G) x z := by
    rcases h1 with ⟨g1, hg1⟩
    rcases h2 with ⟨g2, hg2⟩
    exists (g2 * g1)
    rw [Act.act_mul, hg1, hg2]

  theorem orbit_partition (x y : X) (hxy : orbit (G:=G) x y) (z : X) :
      orbit (G:=G) x z ↔ orbit (G:=G) y z := by
    constructor
    · intro hz
      rcases hxy with ⟨g1, hg1⟩
      rcases hz with ⟨g2, hg2⟩
      exists (g2 * g1⁻¹)
      rw [Act.act_mul, ← hg1]
      repeat rw [← Act.act_mul]
      rw [← Group.mul_assoc, Group.mul_inv_l, Group.mul_one]
      exact hg2
    · intro hz
      rcases hxy with ⟨g1, hg1⟩
      rcases hz with ⟨g2, hg2⟩
      exists (g2 * g1)
      rw [Act.act_mul, hg1, hg2]

  theorem stabilizer_mul (x : X) (g h : G)
    (hg : stabilizer x g) (hh : stabilizer x h) : stabilizer x (g * h) := by
    unfold stabilizer at *
    rw [Act.act_mul, hh, hg]

  theorem stabilizer_inv (x : X) (g : G) (hg : stabilizer x g) : stabilizer x g⁻¹ := by
    dsimp [stabilizer] at *
    calc
      g⁻¹ • x = g⁻¹ • (g • x) := by rw [hg]
      _ = (g⁻¹ * g) • x := by rw [Act.act_mul]
      _ = x := by rw [mul_inv_l, Act.act_one]

  theorem stabilizer_one (x : X) : stabilizer (G:=G) x one := by
    unfold stabilizer
    apply Act.act_one

  theorem stabilizer_conjugate (x : X) (g h : G)
    (hh : stabilizer x h) : stabilizer (g • x) (g * h * g⁻¹) := by
    unfold stabilizer at *
    rw [← Act.act_mul, ← Group.mul_assoc, Group.mul_inv_l, Group.mul_one, Act.act_mul, hh]

  theorem stabilizer_conjugate_orbit (x y : X) (g : G) (hxy : g • x = y) (h : G) :
      stabilizer y h ↔ stabilizer x (g⁻¹ * h * g) := by
    unfold stabilizer
    constructor
    · intro hy
      rw [<- hxy] at hy
      have hy' : g⁻¹ • h • (g • x) = x := by
        rw [hy]
        rw [<- Act.act_mul]
        rw [mul_inv_l, Act.act_one]
      repeat rw [Act.act_mul]
      exact hy'
    · intro hh
      have hh' : g • ((g⁻¹ * h * g) • x) = g • x := by rw [hh]
      rw [hxy] at hh'
      simp [mul_assoc, <- Act.act_mul, mul_inv_r, one_mul] at hh'
      rw [Act.act_mul] at hh'
      rw [hxy] at hh'
      exact hh'

end ActionLemmas

end Group
