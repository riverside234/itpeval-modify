class CompleteOrderedField where
  R       : Type
  NatAlt  : Type
  zero_nat : NatAlt
  Succ : NatAlt -> NatAlt
  NatAltle : NatAlt -> NatAlt -> Prop

  zero    : R
  one     : R
  add     : R → R → R
  mul     : R → R → R
  opp     : R → R
  inv     : R → R
  Rle     : R → R → Prop
  Rlt     : R → R → Prop
  Rabs    : R → R
  INR     : NatAlt → R

  NatAltle_n : ∀ n : NatAlt, NatAltle n n
  le_succ_of_le : ∀ n m: NatAlt, NatAltle n m → NatAltle n (Succ m)
  le_succ : ∀ n : NatAlt, NatAltle n (Succ n)

  add_comm      : ∀ x y : R, add x y = add y x
  add_assoc     : ∀ x y z : R, add (add x y) z = add x (add y z)
  add_zero      : ∀ x : R, add x zero = x
  add_opp       : ∀ x : R, add (opp x) x = zero
  mul_comm      : ∀ x y : R, mul x y = mul y x
  mul_assoc     : ∀ x y z : R, mul (mul x y) z = mul x (mul y z)
  mul_one       : ∀ x : R, mul x one = x
  dist_l        : ∀ x y z : R, mul x (add y z) = add (mul x y) (mul x z)
  sub_zero      : ∀ x : R, add x (opp zero) = x
  Rle_refl      : ∀ x : R, Rle x x
  Rle_trans     : ∀ x y z : R, Rle x y → Rle y z → Rle x z
  Rle_antisym   : ∀ x y : R, Rle x y → Rle y x → x = y
  Rlt_def       : ∀ x y : R, Rlt x y ↔ (Rle x y ∧ x ≠ y)
  Rle_abs       : ∀ x : R, Rle (add x (opp zero)) (Rabs x)
  Rinv_0_lt_compat : ∀ x : R, Rlt zero x → Rlt zero (inv x)
  Rplus_le_compat_l : ∀ x y z : R, Rle y z → Rle (add x y) (add x z)
  Rinv_involutive   : ∀ x : R, Rlt zero x → inv (inv x) = x
  INR_pos       : ∀ n, Rlt zero (INR (Succ n))
  INR_le        : ∀ m n, (NatAltle m n) → Rle (INR m) (INR n)
  INR_0         : INR zero_nat = zero
  INR_S         : ∀ n, INR (Succ n) = add (INR n) one
  Rtotal_order  : ∀ x y : R, Rlt x y ∨ x = y ∨ Rlt y x
  Rle_inv_contravar : ∀ a b : R, Rlt zero a → Rlt zero b → Rle a b → Rle (inv b) (inv a)
  eps_between   : ∀ x y : R, Rlt x y → ∃ eps, Rlt zero eps ∧ Rlt (add x eps) y
  archimedean   : ∀ x : R, ∃ n, Rle x (INR n)
  completeness  : ∀ (A : R → Prop),
    (∃ ub, ∀ a, A a → Rle ub a) →
    ∃ sup, (∀ a, A a → Rle a sup) ∧ ∀ y, (∀ a, A a → Rle a y) → Rle sup y

namespace SupInf

variable [F : CompleteOrderedField]
open CompleteOrderedField (R zero one add mul opp inv Rle Rlt Rabs INR NatAltle)

infixl:65 " + " => add
infixl:70 " * " => mul
prefix:100 "-" => opp
notation x " - " y:65 => add x (opp y)
prefix:100 "/" => inv
infixl:70 " <= " => NatAltle
infixl:70 " <=R " => Rle
infixl:70 " <R " => Rlt
infixl:70 " >R " => (fun x y => Rlt y x)
notation "|" x "|" => Rabs x


local notation "R" => F.R

def up_bounds (A : R → Prop) : R → Prop :=
  fun x => ∀ a, A a → a <=R x

def is_maximum (a : R) (A : R → Prop) : Prop :=
  A a ∧ up_bounds A a

infix:70 " is_a_max_of " => is_maximum

theorem add_sub_cancel_r (a b : R) :
    a + (b - a) = b := by
  rw [←F.add_assoc]
  rw [F.add_comm]
  rw [←F.add_assoc]
  rw [F.add_opp]
  rw [F.add_comm]
  rw [F.add_zero]

theorem Rabs_pos (t : R) : t <=R |t| := by
  have H := F.Rle_abs t
  rw [F.sub_zero] at H
  exact H

theorem unique_max (A : R → Prop) (x y : R) :
    x is_a_max_of A → y is_a_max_of A → x = y := by
  rintro ⟨HxA, Hx⟩ ⟨HyA, Hy⟩
  apply F.Rle_antisym
  · apply Hy; exact HxA
  · apply Hx; exact HyA

def low_bounds (A : R → Prop) : R → Prop :=
  fun x => ∀ a, A a → x <=R a

def is_inf (x : R) (A : R → Prop) : Prop :=
  is_maximum x (low_bounds A)

infix:70 " is_an_inf_of " => is_inf

axiom classic : ∀ P : Prop, P ∨ ¬P

theorem inf_lt (A : R → Prop) (x : R) :
    x is_an_inf_of A → ∀ y, x <R y → ∃ a, A a ∧ a <R y := by
  intro Hinf y Hlt
  rcases Hinf with ⟨Hlow, Hmax⟩
  cases classic (∃ a, A a ∧ a <R y) with
  | inl Hex => exact Hex
  | inr Hnex =>
      have Hlb : low_bounds A y :=
        fun a Ha =>
          match F.Rtotal_order y a with
          | Or.inl Hya =>
              (F.Rlt_def y a).mp Hya |>.1
          | Or.inr (Or.inl Heq) =>
              Heq ▸ F.Rle_refl y
          | Or.inr (Or.inr Hay) =>
              False.elim (Hnex ⟨a, Ha, Hay⟩)
      let Hmax_y := Hmax y Hlb
      specialize Hmax y Hlb
      let ⟨Hxly, Hneq⟩ := (F.Rlt_def x y).mp Hlt
      have Hxy := F.Rle_antisym x y Hxly Hmax_y
      subst Hxy
      contradiction


theorem le_of_le_add_eps (x y : R) :
    (∀ eps, eps >R F.zero → y <=R (x + eps)) → y <=R x := by
  intro H
  match F.Rtotal_order y x with
  | Or.inl Hlt =>
      exact (F.Rlt_def y x).mp Hlt |>.1
  | Or.inr (Or.inl Heq) =>
      rw [Heq]; exact F.Rle_refl x
  | Or.inr (Or.inr Hgt) =>
      obtain ⟨eps, Heps, Hxp⟩ := F.eps_between x y Hgt
      specialize H eps Heps
      let ⟨Hxp_le, Hxp_neq⟩ := (F.Rlt_def (x + eps) y).mp Hxp
      exfalso
      apply Hxp_neq
      exact F.Rle_antisym (x + eps) y Hxp_le H


def limit (u : F.NatAlt → R) (l : R) : Prop :=
  ∀ eps, eps >R F.zero → ∃ N : F.NatAlt, ∀ n : F.NatAlt, N <= n → |u n - l| <=R eps

theorem le_lim (x y : R) (u : F.NatAlt → R) :
    limit u x → (∀ n : F.NatAlt, y <=R u n) → y <=R x := by
  intros Hlim Hle
  apply le_of_le_add_eps
  intro eps Heps
  obtain ⟨N, HN⟩ := Hlim eps Heps
  apply F.Rle_trans y (u N) (x + eps) (Hle N)
  apply F.Rle_trans (u N) (x + (u N - x)) (x + eps)
  · rw [add_sub_cancel_r]
    exact F.Rle_refl (u N)
  · apply F.Rplus_le_compat_l
    apply F.Rle_trans (u N - x) (|u N - x|) eps
    · apply Rabs_pos
    · exact HN N (F.NatAltle_n N)

theorem inv_succ_pos (n : F.NatAlt) : F.zero <R /F.INR (F.Succ n) := by
  apply F.Rinv_0_lt_compat
  apply F.INR_pos

theorem limit_inv_succ (eps : R) (Heps : eps >R F.zero) :
    ∃ N, ∀ n : F.NatAlt, N <= n → /F.INR (F.Succ n) <=R eps := by
  let x := /eps
  have Hx_pos : F.zero <R x := by
    apply F.Rinv_0_lt_compat
    exact Heps
  obtain ⟨N, Harch⟩ := F.archimedean x
  let N1 := F.Succ N
  exists N1
  intros n Hn
  have H_INR_le : F.INR N1 <=R F.INR (F.Succ n) :=
    F.INR_le N1 (F.Succ n) (F.le_succ_of_le N1 n Hn)
  have H_INR_pos : F.zero <R F.INR (F.Succ n) :=
    F.INR_pos n
  have H_INR_N_pos : F.zero <R F.INR N1 :=
    F.INR_pos N
  apply F.Rle_trans
  · exact F.Rle_inv_contravar (F.INR N1) (F.INR (F.Succ n)) H_INR_N_pos H_INR_pos H_INR_le
  have Harch1 : x <=R F.INR N1 := F.Rle_trans x (F.INR N) (F.INR N1) Harch (F.INR_le N N1 (F.le_succ N))
  apply F.Rle_trans
  · exact F.Rle_inv_contravar x (F.INR N1) Hx_pos H_INR_N_pos Harch1
  rw [F.Rinv_involutive _ Heps]
  exact F.Rle_refl eps

end SupInf
