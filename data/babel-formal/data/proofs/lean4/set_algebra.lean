






universe u

namespace SetAlgebra

variable {X : Type u}

axiom classic : ∀ P : Prop, P ∨ ¬ P

def sUnion (A B : X → Prop) : X → Prop := fun x => A x ∨ B x
def sInter (A B : X → Prop) : X → Prop := fun x => A x ∧ B x
def sCompl (A : X → Prop) : X → Prop := fun x => ¬ A x

infixl:65  " ∪s " => sUnion
infixl:70  " ∩s " => sInter
prefix:100 "ᶜs" => sCompl

theorem inter_distrib_left (A B C : X → Prop) :
  ∀ x, (A ∩s (B ∪s C)) x ↔ ((A ∩s B) ∪s (A ∩s C)) x :=
by
  intro x; constructor
  · intro h; rcases h with ⟨hA, hBC⟩; cases hBC with
    | inl hB => exact Or.inl ⟨hA, hB⟩
    | inr hC => exact Or.inr ⟨hA, hC⟩
  · intro h; cases h with
    | inl hAB => exact ⟨hAB.1, Or.inl hAB.2⟩
    | inr hAC => exact ⟨hAC.1, Or.inr hAC.2⟩

theorem inter_distrib_right (A B C : X → Prop) :
  ∀ x, ((A ∪s B) ∩s C) x ↔ ((A ∩s C) ∪s (B ∩s C)) x :=
by
  intro x; constructor
  · intro h; rcases h with ⟨hAB, hC⟩; cases hAB with
    | inl hA => exact Or.inl ⟨hA, hC⟩
    | inr hB => exact Or.inr ⟨hB, hC⟩
  · intro h; cases h with
    | inl hAC => exact ⟨Or.inl hAC.1, hAC.2⟩
    | inr hBC => exact ⟨Or.inr hBC.1, hBC.2⟩

theorem de_morgan_union (A B : X → Prop) :
  ∀ x, (ᶜs (A ∪s B)) x ↔ (ᶜs A ∩s ᶜs B) x :=
by
  intro x; constructor
  · intro h; exact ⟨fun hA => h (Or.inl hA), fun hB => h (Or.inr hB)⟩
  · intro h; intro hAB; cases h with
    | intro hA hB => cases hAB with
      | inl hA' => exact (hA hA')
      | inr hB' => exact (hB hB')

theorem de_morgan_inter (A B : X → Prop) :
  ∀ x, (ᶜs (A ∩s B)) x ↔ (ᶜs A ∪s ᶜs B) x :=
by
  intro x; constructor
  · intro h
    cases classic (A x) with
    | inl hA =>
        right; intro hB; exact h ⟨hA, hB⟩
    | inr hA =>
        left; exact hA
  · intro h; intro hAB; cases hAB with
    | intro hA hB => cases h with
      | inl hA' => exact hA' hA
      | inr hB' => exact hB' hB

end SetAlgebra
