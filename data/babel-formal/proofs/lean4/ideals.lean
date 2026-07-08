class CRing (R : Type) where
  zero  : R
  one   : R
  add   : R → R → R
  mul   : R → R → R
  opp   : R → R

  add_comm  : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero  : ∀ x, add x zero = x
  add_opp   : ∀ x, add x (opp x) = zero

  mul_comm  : ∀ x y, mul x y = mul y x
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_one   : ∀ x, mul x one = x
  dist_l    : ∀ a x y, mul a (add x y) = add (mul a x) (mul a y)
  opp_add   : ∀ x y, opp (add x y) = add (opp x) (opp y)

namespace Ideals

variable {R : Type} [CR : CRing R]
open CRing

infixl:65 "+R" => CRing.add
infixl:70 "*R" => CRing.mul
prefix:100 "-R" => CRing.opp

def IsIdeal (I : R → Prop) : Prop :=
  (I CR.zero) ∧
  (∀ x y, I x → I y → I (x +R y)) ∧
  (∀ x, I x → I (-R x)) ∧
  (∀ a x, I x → I (a *R x))

def Inter {ι : Type} (F : ι → (R → Prop)) : R → Prop :=
  fun x => ∀ i, F i x

theorem inter_isIdeal {ι : Type} (F : ι → (R → Prop))
  (h : ∀ i, IsIdeal (F i)) : IsIdeal (Inter F) :=
by
  unfold IsIdeal Inter at *
  constructor
  · intro i; exact (h i).1
  constructor
  · intro x y hx hy i
    exact (h i).2.1 x y (hx i) (hy i)
  constructor
  · intro x hx i; exact (h i).2.2.1 x (hx i)
  · intro a x hx i; exact (h i).2.2.2 a x (hx i)

def sum (I J : R → Prop) : R → Prop :=
  fun x => ∃ a b, I a ∧ J b ∧ x = a +R b

theorem sum_isIdeal (I J : R → Prop) (hI : IsIdeal I) (hJ : IsIdeal J) :
  IsIdeal (sum I J) :=
by
  unfold IsIdeal sum at *
  constructor
  · exists CR.zero, CR.zero
    constructor
    · exact hI.1
    constructor
    · exact hJ.1
    · simp [CR.add_zero]
  constructor
  · intro x y hx hy
    rcases hx with ⟨a, b, ha, hb, rfl⟩
    rcases hy with ⟨a', b', ha', hb', rfl⟩
    have hadd : (a +R b) +R (a' +R b') = (a +R a') +R (b +R b') := by
      have := by
        calc
          (a +R b) +R (a' +R b')
              = ((a +R b) +R a') +R b' := by simp [CR.add_assoc]
          _   = (a +R (b +R a')) +R b' := by simp [CR.add_assoc]
          _   = (a +R (a' +R b)) +R b' := by simp [CR.add_comm]
          _   = ((a +R a') +R b) +R b' := by simp [CR.add_assoc]
          _   = (a +R a') +R (b +R b') := by simp [CR.add_assoc]
      exact this
    have hsumA : I (a +R a') := hI.2.1 a a' ha ha'
    have hsumB : J (b +R b') := hJ.2.1 b b' hb hb'
    exact ⟨a +R a', b +R b', hsumA, hsumB, hadd⟩
  constructor
  · intro x hx
    rcases hx with ⟨a, b, ha, hb, rfl⟩
    have : -R (a +R b) = (-R a) +R (-R b) := CR.opp_add a b
    have ha' : I (-R a) := hI.2.2.1 a ha
    have hb' : J (-R b) := hJ.2.2.1 b hb
    exact ⟨-R a, -R b, ha', hb', this⟩
  · intro c x hx
    rcases hx with ⟨a, b, ha, hb, rfl⟩
    have : c *R (a +R b) = (c *R a) +R (c *R b) := CR.dist_l c a b
    have ha' : I (c *R a) := hI.2.2.2 c a ha
    have hb' : J (c *R b) := hJ.2.2.2 c b hb
    exact ⟨c *R a, c *R b, ha', hb', this⟩

end Ideals
