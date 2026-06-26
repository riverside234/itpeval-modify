class AddMonoid (R : Type) where
  zero      : R
  add       : R → R → R
  add_zero  : ∀ x, add x zero = x
  add_comm  : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)

namespace CircleAverage
variable {R : Type} [AddMonoid R]

axiom integral       : (R → R) → R
axiom integral_ext   : ∀ (g h : R → R), (∀ θ, g θ = h θ) → integral g = integral h
axiom integral_const : ∀ (c : R), integral (fun _ => c) = c
axiom integral_add   : ∀ (f g : R → R),
  integral (fun θ => AddMonoid.add (f θ) (g θ)) =
  AddMonoid.add (integral f) (integral g)
axiom integral_shift : ∀ (f : R → R) (c : R),
  integral (fun θ => f (AddMonoid.add θ c)) = integral f

def circleMap (c θ : R) : R := AddMonoid.add θ c
noncomputable def circleAverage (f : R → R) (c : R) : R :=
  integral (fun θ => f (circleMap c θ))

theorem circleMap_zero (θ : R) :
  circleMap AddMonoid.zero θ = θ := by
  dsimp [circleMap]
  rw [AddMonoid.add_zero]

theorem circleAverage_zero (f : R → R) :
  circleAverage f AddMonoid.zero = integral f := by
  dsimp [circleAverage]
  apply integral_ext; intro θ
  dsimp [circleMap]
  rw [AddMonoid.add_zero]

theorem circleAverage_add (f g : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (f z) (g z)) c =
  AddMonoid.add (circleAverage f c) (circleAverage g c) := by
  dsimp [circleAverage]
  rw [integral_add]

theorem circleAverage_fun_add (f : R → R) (c : R) :
  circleAverage (fun z => f (AddMonoid.add z c)) AddMonoid.zero =
  circleAverage f c := by
  dsimp [circleAverage, circleMap]
  apply integral_ext; intro θ
  rw [AddMonoid.add_comm]
  rw [←AddMonoid.add_assoc]
  rw [AddMonoid.add_zero]
  rw [AddMonoid.add_comm]

theorem circleMap_add (c d θ : R) :
  circleMap (AddMonoid.add c d) θ =
  circleMap c (circleMap d θ) := by
  dsimp [circleMap]
  rw [AddMonoid.add_comm c d]
  rw [AddMonoid.add_assoc]

theorem circleAverage_shift (f : R → R) (c d : R) :
  circleAverage f (AddMonoid.add c d) =
  circleAverage (fun z => f (AddMonoid.add z d)) c := by
  dsimp [circleAverage]
  apply integral_ext; intro θ
  dsimp [circleMap]
  rw [AddMonoid.add_assoc]

theorem circleAverage_const (k c : R) :
  circleAverage (fun _ => k) c = k := by
  dsimp [circleAverage]
  rw [integral_const]

theorem circleAverage_add_const (f : R → R) (k c : R) :
  circleAverage (fun z => AddMonoid.add (f z) k) c =
  AddMonoid.add (circleAverage f c) k := by
  dsimp [circleAverage]
  rw [integral_add]
  rw [integral_const]

theorem circleAverage_comm_add (f g : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (f z) (g z)) c =
  circleAverage (fun z => AddMonoid.add (g z) (f z)) c := by
  dsimp [circleAverage]
  apply integral_ext; intro θ
  dsimp [circleMap]
  rw [AddMonoid.add_comm]

theorem circleAverage_add_assoc (f g h : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (AddMonoid.add (f z) (g z)) (h z)) c =
  AddMonoid.add (circleAverage f c)
              (AddMonoid.add (circleAverage g c) (circleAverage h c)) := by
  dsimp [circleAverage]
  rw [integral_add]
  rw [integral_add]
  rw [AddMonoid.add_assoc]

theorem circleAverage_center_comm (f : R → R) (c d : R) :
  circleAverage f (AddMonoid.add c d) =
  circleAverage f (AddMonoid.add d c) := by
  dsimp [circleAverage, circleMap]
  apply integral_ext; intro θ
  simp [AddMonoid.add_comm]

theorem circleAverage_center_independent (f : R → R) (c : R) :
  circleAverage f c = integral f := by
  dsimp [circleAverage]
  apply integral_shift

theorem circleAverage_center_eq (f : R → R) (c d : R) :
  circleAverage f c = circleAverage f d := by
  have h1 := circleAverage_center_independent f c
  have h2 := circleAverage_center_independent f d
  exact Eq.trans h1 (Eq.symm h2)

theorem circleAverage_idempotent (f : R → R) (c : R) :
  circleAverage (fun z => circleAverage f z) c = circleAverage f c := by
  dsimp [circleAverage]
  have h1 := by
    apply integral_ext; intro θ
    apply circleAverage_center_independent f (circleMap c θ)
  have h2 := integral_const (integral f)
  have h3 := circleAverage_center_independent f c
  exact Eq.trans (Eq.trans h1 h2) (Eq.symm h3)

theorem circleAverage_of_zero_integral (f : R → R) (c : R) (H : integral f = AddMonoid.zero) :
  circleAverage f c = AddMonoid.zero := by
  rw [circleAverage_center_independent f c]
  exact H

theorem circleAverage_linear (f g : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (f z) (g z)) c =
  AddMonoid.add (circleAverage f c) (circleAverage g c) := by
  dsimp [circleAverage]
  rw [integral_add]

theorem circleAverage_shift_commute (f : R → R) (c d : R) :
  circleAverage (fun z => f (circleMap d z)) c =
  circleAverage f (AddMonoid.add c d) := by
  dsimp [circleAverage, circleMap]
  apply integral_ext; intro θ
  rw [AddMonoid.add_assoc]

end CircleAverage
