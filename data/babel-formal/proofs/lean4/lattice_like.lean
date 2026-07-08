universe u

class LatticeLike (A : Type u) where
  le   : A → A → Prop
  inf  : A → A → A
  sup  : A → A → A

  le_refl  : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisym : ∀ {x y}, le x y → le y x → x = y

  le_inf_left  : ∀ a b, le (inf a b) a
  le_inf_right : ∀ a b, le (inf a b) b
  le_inf_intro : ∀ {c a b}, le c a → le c b → le c (inf a b)

  le_sup_left  : ∀ a b, le a (sup a b)
  le_sup_right : ∀ a b, le b (sup a b)
  sup_le_intro : ∀ {a b c}, le a c → le b c → le (sup a b) c

namespace LatticeLike

variable {A : Type u} [L : LatticeLike A]

infix:50 " ≤ " => LatticeLike.le
infixl:65 " ⊓ " => LatticeLike.inf
infixl:70 " ⊔ " => LatticeLike.sup

theorem inf_comm (a b : A) : a ⊓ b = b ⊓ a :=
by
  apply LatticeLike.le_antisym
  · have h1 : a ⊓ b ≤ b := LatticeLike.le_inf_right a b
    have h2 : a ⊓ b ≤ a := LatticeLike.le_inf_left a b
    have : a ⊓ b ≤ b ⊓ a := LatticeLike.le_inf_intro h1 h2
    exact this
  · have h1 : b ⊓ a ≤ a := LatticeLike.le_inf_right b a
    have h2 : b ⊓ a ≤ b := LatticeLike.le_inf_left b a
    have : b ⊓ a ≤ a ⊓ b := LatticeLike.le_inf_intro h1 h2
    exact this

theorem sup_comm (a b : A) : a ⊔ b = b ⊔ a :=
by
  apply LatticeLike.le_antisym
  · have Ha : a ≤ b ⊔ a := LatticeLike.le_sup_right b a
    have Hb : b ≤ b ⊔ a := LatticeLike.le_sup_left b a
    have : a ⊔ b ≤ b ⊔ a := LatticeLike.sup_le_intro Ha Hb
    exact this
  · have Hb : b ≤ a ⊔ b := LatticeLike.le_sup_right a b
    have Ha : a ≤ a ⊔ b := LatticeLike.le_sup_left a b
    have : b ⊔ a ≤ a ⊔ b := LatticeLike.sup_le_intro Hb Ha
    exact this

theorem inf_assoc (a b c : A) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
by
  apply LatticeLike.le_antisym
  · have h1 : (a ⊓ b) ⊓ c ≤ a ⊓ b := LatticeLike.le_inf_left _ _
    have h2 : a ⊓ b ≤ a := LatticeLike.le_inf_left _ _
    have h3 : (a ⊓ b) ⊓ c ≤ a := LatticeLike.le_trans h1 h2
    have h4 : (a ⊓ b) ⊓ c ≤ c := LatticeLike.le_inf_right _ _
    have h5 : (a ⊓ b) ⊓ c ≤ b ⊓ c := LatticeLike.le_inf_intro
      (show (a ⊓ b) ⊓ c ≤ b from LatticeLike.le_trans (LatticeLike.le_inf_left _ _) (LatticeLike.le_inf_right _ _))
      h4
    have : (a ⊓ b) ⊓ c ≤ a ⊓ (b ⊓ c) :=
      LatticeLike.le_inf_intro h3 h5
    exact this
  · have h1 : a ⊓ (b ⊓ c) ≤ a := LatticeLike.le_inf_left _ _
    have h2 : a ⊓ (b ⊓ c) ≤ b ⊓ c := LatticeLike.le_inf_right _ _
    have h3 : b ⊓ c ≤ b := LatticeLike.le_inf_left _ _
    have h4 : a ⊓ (b ⊓ c) ≤ b := LatticeLike.le_trans h2 h3
    have h5 : a ⊓ (b ⊓ c) ≤ c := LatticeLike.le_trans h2 (LatticeLike.le_inf_right _ _)
    have : a ⊓ (b ⊓ c) ≤ (a ⊓ b) ⊓ c :=
      LatticeLike.le_inf_intro (LatticeLike.le_inf_intro h1 h4) h5
    exact this

theorem sup_assoc (a b c : A) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) :=
by
  apply LatticeLike.le_antisym
  · have Ha_to : a ≤ a ⊔ (b ⊔ c) := LatticeLike.le_sup_left _ _
    have Hb_bc : b ≤ b ⊔ c := LatticeLike.le_sup_left _ _
    have Hb_to : b ≤ a ⊔ (b ⊔ c) := LatticeLike.le_trans Hb_bc (LatticeLike.le_sup_right _ _)
    have Hab_to : a ⊔ b ≤ a ⊔ (b ⊔ c) := LatticeLike.sup_le_intro Ha_to Hb_to
    have Hc_bc : c ≤ b ⊔ c := LatticeLike.le_sup_right _ _
    have Hc_to : c ≤ a ⊔ (b ⊔ c) := LatticeLike.le_trans Hc_bc (LatticeLike.le_sup_right _ _)
    have : (a ⊔ b) ⊔ c ≤ a ⊔ (b ⊔ c) := LatticeLike.sup_le_intro Hab_to Hc_to
    exact this
  · have Ha_ab : a ≤ a ⊔ b := LatticeLike.le_sup_left _ _
    have Hab_to : a ⊔ b ≤ (a ⊔ b) ⊔ c := LatticeLike.le_sup_left _ _
    have Ha_to : a ≤ (a ⊔ b) ⊔ c := LatticeLike.le_trans Ha_ab Hab_to
    have Hb_ab : b ≤ a ⊔ b := LatticeLike.le_sup_right _ _
    have Hb_to : b ≤ (a ⊔ b) ⊔ c := LatticeLike.le_trans Hb_ab Hab_to
    have Hc_to : c ≤ (a ⊔ b) ⊔ c := LatticeLike.le_sup_right _ _
    have Hbc_to : b ⊔ c ≤ (a ⊔ b) ⊔ c := LatticeLike.sup_le_intro Hb_to Hc_to
    have : a ⊔ (b ⊔ c) ≤ (a ⊔ b) ⊔ c := LatticeLike.sup_le_intro Ha_to Hbc_to
    exact this

theorem inf_absorption (a b : A) : a ⊓ (a ⊔ b) = a :=
by
  apply LatticeLike.le_antisym
  · have h1 : a ⊓ (a ⊔ b) ≤ a := LatticeLike.le_inf_left _ _
    exact h1
  · have h1 : a ≤ a := LatticeLike.le_refl _
    have h2 : a ≤ a ⊔ b := LatticeLike.le_sup_left _ _
    have : a ≤ a ⊓ (a ⊔ b) := LatticeLike.le_inf_intro h1 h2
    exact this

theorem sup_absorption (a b : A) : a ⊔ (a ⊓ b) = a :=
by
  apply LatticeLike.le_antisym
  · have h1 : a ≤ a := LatticeLike.le_refl _
    have h2 : a ⊓ b ≤ a := LatticeLike.le_inf_left _ _
    have : a ⊔ (a ⊓ b) ≤ a := LatticeLike.sup_le_intro h1 h2
    exact this
  · have h1 : a ≤ a ⊔ (a ⊓ b) := LatticeLike.le_sup_left _ _
    exact h1

end LatticeLike
