class RField (R : Type) where
  zero   : R
  one    : R
  add    : R → R → R
  opp    : R → R
  mul    : R → R → R
  le     : R → R → Prop
  lt     : R → R → Prop
  abs    : R → R

  add_comm      : ∀ x y, add x y = add y x
  add_assoc     : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero      : ∀ x, add x zero = x
  add_opp       : ∀ x, add (opp x) x = zero
  add_right_cancel : ∀ x y z, add x z = add y z → x = y

  mul_comm      : ∀ x y, mul x y = mul y x
  mul_assoc     : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_one       : ∀ x, mul x one = x
  dist_l        : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  opp_involutive : ∀ x, opp (opp x) = x

  add_le_compat : ∀ x y z, le x y → le (add x z) (add y z)
  mul_le_compat : ∀ x y z, le zero z → le x y → le (mul x z) (mul y z)
  zero_le_one   : le zero one
  le_total      : ∀ x y, le x y ∨ le y x

  le_dec : ∀ x y, (le x y) ∨ ¬ (le x y)

  le_opp        : ∀ x y, le x y → le (opp y) (opp x)
  le_antisymm   : ∀ x y, le x y → le y x → x = y
  lt_opp        : ∀ x y, lt x y → lt (opp y) (opp x)
  le_refl       : ∀ x, le x x
  le_trans      : ∀ x y z, le x y → le y z → le x z
  lt_def        : ∀ x y, lt x y ↔ (le x y ∧ x ≠ y)

  abs_pos       : ∀ x, le zero x → abs x = x
  abs_neg       : ∀ x, le x zero → abs x = opp x
  abs_nonneg    : ∀ x, le zero (abs x)
  abs_opp       : ∀ x, abs (opp x) = abs x
  abs_triangle  : ∀ x y, le (abs (add x y)) (add (abs x) (abs y))

class Integral (R : Type) [RField R] where
  sigma       : (R → Prop) → (R → R) → R
  sigma_mul_const : ∀ (D : R → Prop) (f : R → R) (c : R),
    sigma D (fun x => RField.mul c (f x)) = RField.mul c (sigma D f)
  sigma_congr : ∀ D f g, (∀ x, D x → f x = g x) → sigma D f = sigma D g
  sigma_zero  : ∀ D, sigma D (fun _ => RField.zero) = RField.zero
  sigma_add   : ∀ D f g, sigma D (fun x => RField.add (f x) (g x)) = RField.add (sigma D f) (sigma D g)

  sigma_union_disjoint : ∀ (D E : R → Prop) (f : R → R),
    (∀ x, D x → E x → False) →
    sigma (fun x => D x ∨ E x) f = RField.add (sigma D f) (sigma E f)
  sigma_le : ∀ D f g, (∀ x, D x → RField.le (f x) (g x)) → RField.le (sigma D f) (sigma D g)
  sigma_dom_congr : ∀ D E f, (∀ x, D x ↔ E x) → sigma D f = sigma E f

namespace Integrals

variable {R : Type} [RF : RField R] [I : Integral R]
open RField
open Integral

-- Notations
prefix:100 "-" => opp
infixl:65 " + " => add
infixl:70 " * " => mul
infixl:70 " <= " => le
infixl:70 " < " => lt

-- Domains
def Iic (c : R) : R → Prop := fun x => x <= c
def Ioi (c : R) : R → Prop := fun x => c < x
def Iio (c : R) : R → Prop := fun x => x < c
def union (D E : R → Prop) : R → Prop := fun x => D x ∨ E x
def inter (D E : R → Prop) : R → Prop := fun x => D x ∧ E x

-- Lemma lt_irrefl
theorem lt_irrefl (x : R) : ¬ (x < x) :=
by
  intro H2
  rw [lt_def] at H2
  rcases H2 with ⟨Hle, Hneq⟩
  exact Hneq rfl

-- Lemma lt_trans_strict
theorem lt_trans_strict (x y z : R) (Hxy : x < y) (Hyz : y < z) : x < z :=
by
  rw [lt_def] at *
  constructor
  · apply le_trans _ _ _ Hxy.1 Hyz.1
  · intro Heq
    subst z
    rcases Hxy with ⟨Hxy_le, Hxy_neq⟩
    rcases Hyz with ⟨Hyz_le, Hyz_neq⟩
    apply Hxy_neq
    apply le_antisymm <;> assumption

-- Preimage
def preimage (g : R → R) (D : R → Prop) : R → Prop :=
  fun x => D (g x)

theorem preimage_union (D E : R → Prop) (g : R → R) (x : R) :
  preimage g (union D E) x ↔ preimage g D x ∨ preimage g E x :=
by
  unfold preimage union; trivial

theorem preimage_inter (D E : R → Prop) (g : R → R) (x : R) :
  preimage g (inter D E) x ↔ preimage g D x ∧ preimage g E x :=
by
  unfold preimage inter; trivial

theorem preimage_neg_Ioi (c x : R) :
  preimage opp (Ioi c) x ↔ x < opp c :=
by
  unfold preimage Ioi
  constructor
  · intro Ha
    have := lt_opp c (opp x) Ha
    rw [opp_involutive] at this
    exact this
  · intro Ha
    have := lt_opp x (opp c) Ha
    rw [opp_involutive] at this
    exact this

theorem preimage_neg_Iic (c x : R) :
  preimage opp (Iic c) x ↔ Iic x (opp c) :=
by
  unfold preimage Iic
  constructor
  · intro Ha
    have h := le_opp (-x) c Ha
    rw [opp_involutive] at h
    exact h
  · intro Ha
    have h := le_opp (-c) x Ha
    rw [opp_involutive] at h
    exact h

theorem preimage_comp (D : R → Prop) (g h : R → R) (x : R) :
  preimage g (preimage h D) x ↔ preimage (fun x => h (g x)) D x :=
by
  rfl

theorem integral_neg (D : R → Prop) (f : R → R) :
  sigma D (fun x => opp (f x)) = opp (sigma D f) :=
by
  apply add_right_cancel
    (sigma D (fun x => opp (f x)))
    (opp (sigma D f))
    (sigma D f)
  rw [add_opp]
  rw [←sigma_add]
  have Hpointwise : ∀ x, D x → opp (f x) + f x = zero :=
    by intros x _; rw [add_opp]
  rw [sigma_congr D (fun x => opp (f x) + f x) (fun _ => zero) Hpointwise]
  rw [sigma_zero]

theorem integral_sub (D : R → Prop) (f g : R → R) :
  sigma D (fun x => add (f x) (opp (g x))) = add (sigma D f) (opp (sigma D g)) :=
by
  rw [sigma_add]
  rw [integral_neg]

theorem sigma_empty (f : R → R) :
  sigma (fun _ => False) f = zero :=
by
  have : sigma (fun _ => False) f = sigma (fun _ => False) (fun _ => zero) :=
    by
      apply sigma_congr
      intros x Ha
      cases Ha
  rw [this, sigma_zero]

theorem sigma_bilinear (D : R → Prop) (f g : R → R) (c d : R) :
  sigma D (fun x => add (mul c (f x)) (mul d (g x))) =
    add (mul c (sigma D f)) (mul d (sigma D g)) :=
by
  rw [sigma_add]
  rw [sigma_mul_const]
  rw [sigma_mul_const]

theorem sigma_le_monotone (D : R → Prop) (f g : R → R) :
  (∀ x, D x → le (f x) (g x)) → le (sigma D f) (sigma D g) :=
by
  exact sigma_le D f g

theorem sigma_nonneg (D : R → Prop) (f : R → R) :
  (∀ x, D x → le zero (f x)) → le zero (sigma D f) :=
by
  intro H0f
  rw [←sigma_zero D]
  exact sigma_le D (fun x => zero) f H0f

theorem sigma_split (D : R → Prop) (P : R → Prop) (f : R → R)
  (P_dec : ∀ x, D x → P x ∨ ¬ P x) :
  sigma D f =
    add (sigma (fun x => D x ∧ P x) f)
        (sigma (fun x => D x ∧ ¬ P x) f) :=
by
  let E := fun x => D x ∧ P x
  let F := fun x => D x ∧ ¬ P x
  have Disj : ∀ x, E x → F x → False := by
    intros x Ex Fx
    let ⟨HDx, HPx⟩ := Ex
    let ⟨_, HnPx⟩ := Fx
    exact HnPx HPx
  have EqDom : ∀ x, D x ↔ (E x ∨ F x) := by
    intro x; constructor
    · intro HDx
      cases P_dec x HDx with
      | inl HPx => left; exact ⟨HDx, HPx⟩
      | inr HnPx => right; exact ⟨HDx, HnPx⟩
    · intro h
      cases h with
      | inl hE =>
        exact hE.1
      | inr hF =>
        exact hF.1
  rw [sigma_dom_congr D (fun x => E x ∨ F x) f EqDom]
  exact sigma_union_disjoint E F f Disj

theorem sigma_preimage_neg_Ioi (f : R → R) (c : R) :
  sigma (preimage opp (Ioi c)) f = sigma (Iio (opp c)) f :=
by
  apply sigma_dom_congr
  intro x; exact preimage_neg_Ioi c x

theorem sigma_abs_bound (D : R → Prop) (f : R → R) :
  le (abs (sigma D f)) (sigma D (fun x => abs (f x))) :=
by
  let P := fun x => zero <= f x
  have P_dec : ∀ x, D x → P x ∨ ¬ P x :=
    fun x _ => le_dec zero (f x)
  rw [sigma_split D P f P_dec]
  let I_pos := sigma (fun x => D x ∧ P x) f
  let I_neg := sigma (fun x => D x ∧ ¬ P x) f
  apply le_trans (abs (I_pos + I_neg)) (abs I_pos + abs I_neg) (sigma D (fun x => abs (f x)))
  · exact abs_triangle I_pos I_neg
  have Hpos_nonneg : zero <= I_pos :=
    sigma_nonneg (fun x => D x ∧ P x) f (by intros x h; exact h.2)
  have Hpos_eq : abs I_pos = sigma (fun x => D x ∧ P x) (fun x => abs (f x)) :=
    by
      rw [abs_pos I_pos Hpos_nonneg]
      apply sigma_congr; intros x h; symm; exact abs_pos (f x) h.2
  have Hfx_le0 : ∀ x, D x ∧ ¬ P x → f x <= zero :=
    fun x h =>
      match le_total zero (f x) with
      | Or.inl H3 => False.elim (h.2 H3)
      | Or.inr H3 => H3
  have Hneg_nonpos : sigma (fun x => D x ∧ ¬P x) f <= zero :=
    by
      apply le_trans _ (sigma (fun x => D x ∧ ¬P x) (fun _ => zero))
      · exact sigma_le (fun x => D x ∧ ¬ P x) f (fun _ => zero) Hfx_le0
      · rw [sigma_zero]; exact le_refl zero
  have Hneg_eq : abs I_neg = sigma (fun x => D x ∧ ¬P x) (fun x => abs (f x)) :=
    by
      rw [abs_neg I_neg Hneg_nonpos]
      rw [←integral_neg]
      apply sigma_congr; intros x Hx; symm; apply abs_neg; apply Hfx_le0; exact Hx
  rw [Hpos_eq, Hneg_eq]
  rw [sigma_split D P (fun x => abs (f x)) P_dec]
  exact le_refl _

end Integrals
