universe u v w

namespace CompCommute

variable {α : Type u} {β : Type v} {γ : Type w}

def comp {α β γ} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
def id {α} : α → α := fun x => x

axiom comp_assoc : ∀ {α β γ δ} (h : γ → δ) (g : β → γ) (f : α → β), comp h (comp g f) = comp (comp h g) f
axiom comp_id_l  : ∀ {α β} (f : α → β), comp (id) f = f
axiom comp_id_r  : ∀ {α β} (f : α → β), comp f id = f

def commute {α} (f g : α → α) : Prop := comp f g = comp g f

theorem commute_symm {α} (f g : α → α) : commute f g → commute g f :=
by
  intro H
  have : comp f g = comp g f := H
  have Hsym : comp g f = comp f g := by
    exact Eq.symm this
  exact Hsym

theorem commute_with_id_l {α} (f : α → α) : commute f (id) :=
by
  unfold commute
  have H1 : comp f id = f := comp_id_r f
  have H2 : comp id f = f := comp_id_l f
  have : comp f id = comp id f := by
    simp [H1, H2]
  exact this

theorem commute_with_id_r {α} (f : α → α) : commute (id) f :=
by
  unfold commute
  have H1 : comp id f = f := comp_id_l f
  have H2 : comp f id = f := comp_id_r f
  have : comp id f = comp f id := by
    simp [H1, H2]
  exact this

theorem commute_refl {α} (f : α → α) : commute f f :=
by
  unfold commute
  rfl

theorem commute_congr {α} (f1 f2 g1 g2 : α → α) :
  f1 = f2 → g1 = g2 → commute f1 g1 → commute f2 g2 :=
by
  intro Hf Hg Hc
  subst Hf
  subst Hg
  exact Hc

theorem commute_transport_left_id {α} (f g : α → α) :
  commute f g → commute (comp (id) f) g :=
by
  intro H
  unfold commute at *
  simpa [comp_id_l] using H

theorem commute_transport_right_id {α} (f g : α → α) :
  commute f g → commute f (comp (id) g) :=
by
  intro H
  unfold commute at *
  simpa [comp_id_l] using H

end CompCommute
