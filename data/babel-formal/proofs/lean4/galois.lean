class Field (F : Type) where
  zero_F    : F
  one_F     : F
  add_F     : F → F → F
  mul_F     : F → F → F
  opp_F     : F → F
  inv_F     : F → F

  add_comm    : ∀ x y, add_F x y = add_F y x
  add_assoc   : ∀ x y z, add_F (add_F x y) z = add_F x (add_F y z)
  add_zero    : ∀ x, add_F x zero_F = x
  add_inv_l   : ∀ x, add_F (opp_F x) x = zero_F

  mul_comm    : ∀ x y, mul_F x y = mul_F y x
  mul_assoc   : ∀ x y z, mul_F (mul_F x y) z = mul_F x (mul_F y z)
  mul_one_l   : ∀ x, mul_F one_F x = x
  mul_inv_l   : ∀ x, x ≠ zero_F → mul_F (inv_F x) x = one_F

  distrib_l   : ∀ x y z, mul_F x (add_F y z) = add_F (mul_F x y) (mul_F x z)

  zero_neq_one : zero_F ≠ one_F
  inv_nonzero  : ∀ x, x ≠ zero_F → inv_F x ≠ zero_F

namespace FieldProperties
variable {F : Type} [HF : Field F]
open Field

infixl:65 "+" => add_F
infixl:70 "*" => mul_F
prefix:100 "-" => opp_F
prefix:100 "/" => inv_F

theorem add_cancel_l (x y z : F) : x + y = x + z → y = z := by
  intro H
  have H₁ := congrArg (fun w => -x + w) H
  change -x + (x+y) = -x + (x+z) at H₁
  rw [← add_assoc]       at H₁
  rw [add_inv_l]         at H₁
  rw [add_comm]          at H₁
  rw [add_zero]          at H₁
  rw [<- add_assoc, add_comm, add_inv_l]          at H₁
  rw [add_zero]          at H₁
  exact H₁

theorem add_cancel_r (x y z : F) : y + x = z + x → y = z := by
  intro H
  rw [add_comm y x, add_comm z x] at H
  apply add_cancel_l
  assumption

theorem mul_cancel_l (x y z : F) (h : x ≠ zero_F) : x * y = x * z → y = z := by
  intro H
  have H₁ := congrArg (fun w => inv_F x * w) H
  change inv_F x * (x * y) = inv_F x * (x * z) at H₁

  rw [← mul_assoc]        at H₁
  rw [mul_inv_l _ h]      at H₁
  rw [mul_one_l]          at H₁
  rw [← mul_assoc]        at H₁
  rw [mul_inv_l _ h]      at H₁
  rw [mul_one_l]          at H₁

  exact H₁

theorem mul_cancel_r (x y z : F) (h : x ≠ zero_F) : y * x = z * x → y = z := by
  intro H
  rw [mul_comm y x, mul_comm z x] at H
  apply mul_cancel_l x y z h
  assumption

theorem inv_unique (x y : F) (h : x ≠ zero_F) (H : x * y = one_F) : y = inv_F x := by
  have H₁ := congrArg (fun w => inv_F x * w) H
  change inv_F x * (x * y) = inv_F x * one_F at H₁
  rw [← mul_assoc]    at H₁
  rw [mul_inv_l _ h]  at H₁
  rw [mul_one_l]      at H₁
  rw [mul_comm]       at H₁
  rw [mul_one_l]      at H₁
  exact H₁

theorem inv_involutive (x : F) (h : x ≠ zero_F) : inv_F (inv_F x) = x := by
  apply Eq.symm
  apply inv_unique
  · exact inv_nonzero x h
  · exact mul_inv_l x h

end FieldProperties

class IsSolvable (G : Type) : Prop

namespace Tower
variable {polynomial      : Type → Type}
variable {SplittingField  : ∀ {F : Type}, polynomial F → Type}
variable {algebraMap      : ∀ {F K : Type}, F → K}
variable {Splits          : ∀ {F K : Type}, polynomial F → (F → K) → Prop}
variable {map_poly        : ∀ {F K : Type}, polynomial F → (F → K) → polynomial K}
variable {Gal             : ∀ {F : Type}, polynomial F → Type}

variable {F : Type}
variable (p q r s t : polynomial F)
variable (K L : Type)

axiom map_poly_comp : ∀ {F K L : Type} (p : polynomial F)
  (f : F → K) (g : K → L), map_poly (map_poly p f) g = map_poly p (fun x => g (f x))
axiom isSolvable_of_isScalarTower : ∀ {F K : Type} {p q : polynomial F},
  IsSolvable (Gal p) → IsSolvable (Gal (map_poly q (@algebraMap F K))) → IsSolvable (Gal q)
axiom isSolvable_map_poly : ∀ {F K : Type} (p : polynomial F),
  IsSolvable (Gal p) → IsSolvable (Gal (map_poly p (@algebraMap F K)))
axiom isSolvable_of_splits : ∀ {F K : Type} (p : polynomial F) (f : F → K),
  Splits p f → IsSolvable (Gal p)

theorem gal_isSolvable_tower
  (hp : IsSolvable (Gal p))
  (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p))))) :
  IsSolvable (Gal q) := by
  apply isSolvable_of_isScalarTower hp hq

theorem gal_isSolvable_double_tower
  (hp : IsSolvable (Gal p))
  (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p)))))
  (hr : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q))))) :
  IsSolvable (Gal r) := by
  have Hq := isSolvable_of_isScalarTower hp hq
  apply isSolvable_of_isScalarTower Hq hr

theorem gal_isSolvable_triple_tower
  (hp : IsSolvable (Gal p))
  (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p)))))
  (hr : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q)))))
  (hs : IsSolvable (Gal (map_poly s (@algebraMap F (SplittingField r))))) :
  IsSolvable (Gal s) := by
  have Hq := isSolvable_of_isScalarTower hp hq
  have Hr := isSolvable_of_isScalarTower Hq hr
  apply isSolvable_of_isScalarTower Hr hs

theorem gal_isSolvable_quadruple_tower
  (hp : IsSolvable (Gal p))
  (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p)))))
  (hr : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q)))))
  (hs : IsSolvable (Gal (map_poly s (@algebraMap F (SplittingField r)))))
  (ht : IsSolvable (Gal (map_poly t (@algebraMap F (SplittingField s))))) :
  IsSolvable (Gal t) := by
  have Hq := isSolvable_of_isScalarTower hp hq
  have Hr := isSolvable_of_isScalarTower Hq hr
  have Hs := isSolvable_of_isScalarTower Hr hs
  apply isSolvable_of_isScalarTower Hs ht

theorem gal_isSolvable_map_poly (hp : IsSolvable (Gal p)) :
  IsSolvable (Gal (map_poly p (@algebraMap F K))) := by
  apply isSolvable_map_poly p hp

theorem gal_isSolvable_of_split
  (hsplit : Splits p (@algebraMap F (SplittingField p))) :
  IsSolvable (Gal p) := by
  apply isSolvable_of_splits p (@algebraMap F (SplittingField p)) hsplit

theorem gal_isSolvable_split_tower
  (hsplit : Splits q (@algebraMap F (SplittingField p))) :
  IsSolvable (Gal q) := by
  apply isSolvable_of_splits q (@algebraMap F (SplittingField p)) hsplit

theorem gal_isSolvable_two_step_map (hp : IsSolvable (Gal p)) :
  IsSolvable (Gal (map_poly (map_poly p (@algebraMap F K)) (@algebraMap K L))) := by
  apply isSolvable_map_poly
  apply isSolvable_map_poly
  exact hp

theorem gal_isSolvable_three_step_map {M : Type}
  (hp : IsSolvable (Gal p)) :
  IsSolvable (Gal (map_poly (map_poly (map_poly p (@algebraMap F K))
                                           (@algebraMap K L))
                                 (@algebraMap L M))) := by
  apply isSolvable_map_poly
  apply isSolvable_map_poly
  apply isSolvable_map_poly
  exact hp

theorem gal_isSolvable_map_poly_comp (hp : IsSolvable (Gal p)) :
  IsSolvable (Gal (map_poly (map_poly p (@algebraMap F K)) (@algebraMap K L))) := by
  apply isSolvable_map_poly
  apply isSolvable_map_poly
  exact hp

theorem gal_isSolvable_mutual_split
  (hsplit_p : Splits p (@algebraMap F (SplittingField q)))
  (hsplit_q : Splits q (@algebraMap F (SplittingField p))) :
  IsSolvable (Gal p) ∧ IsSolvable (Gal q) := by
  constructor
  · apply isSolvable_of_splits p (@algebraMap F (SplittingField q)) hsplit_p
  · apply isSolvable_of_splits q (@algebraMap F (SplittingField p)) hsplit_q

theorem gal_isSolvable_tower_split
  (hsplit_q : Splits q (@algebraMap F (SplittingField p)))
  (hr : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q))))) :
  IsSolvable (Gal r) := by
  apply isSolvable_of_isScalarTower
  · apply isSolvable_of_splits
    exact hsplit_q
  · exact hr

theorem gal_isSolvable_map_after_split
  (hsplit : Splits p (@algebraMap F (SplittingField p))) :
  IsSolvable (Gal (map_poly p (@algebraMap F K))) := by
  apply isSolvable_map_poly
  apply isSolvable_of_splits
  exact hsplit

end Tower
