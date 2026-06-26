inductive mynat : Type
| O  : mynat
| S  : mynat → mynat
deriving DecidableEq

open mynat

def mynat_add : mynat → mynat → mynat
| O,        m => m
| (S n'),   m => S (mynat_add n' m)

theorem mynat_add_O_left (m : mynat) :
  mynat_add O m = m := rfl

theorem mynat_add_S_left (n m : mynat) :
  mynat_add (S n) m = S (mynat_add n m) := rfl

inductive mynat_le : mynat → mynat → Prop
| le_n  : ∀ n, mynat_le n n
| le_S  : ∀ n m, mynat_le n m → mynat_le n (S m)

open mynat_le

theorem mynat_zero_le (n : mynat) : mynat_le O n := by
  induction n with
  | O =>
      exact le_n O
  | S n ih =>
      exact le_S O n ih

theorem mynat_add_zero_r : ∀ n, mynat_add n O = n
| O      => rfl
| (S n') => by
  simp [mynat_add, mynat_add_zero_r n']

theorem mynat_succ_le_succ {n m : mynat} :
  mynat_le n m → mynat_le (S n) (S m) := by
  intro h; induction h with
  | le_n =>
      exact le_n (S n)
  | le_S m h ih =>
      exact le_S (S n) (S m) ih

theorem mynat_add_S_r : ∀ m n, mynat_add m (S n) = S (mynat_add m n)
| O,      n => rfl
| (S m'), n => by
  simp [mynat_add, mynat_add_S_r m' n]

theorem mynat_add_comm : ∀ n m, mynat_add n m = mynat_add m n
| O,      m => by simp [mynat_add, mynat_add_zero_r]
| (S n'), m => by
  simp [mynat_add, mynat_add_comm n' m, mynat_add_S_r m n']

inductive mylist (A : Type) : Type
| nilL  : mylist A
| consL : A → mylist A → mylist A

namespace mylist

notation h "::L" t => mylist.consL  h t

end mylist

open mylist


inductive InL {A : Type} (x : A) : mylist A → Prop
| In_head : ∀ xs, InL x (x ::L xs)
| In_tail : ∀ y xs, InL (x := x) xs → InL (x := x) (y ::L xs)

inductive NoDupL {A : Type} : mylist A → Prop
| ND_nil  : NoDupL mylist.nilL
| ND_cons : ∀ x xs, (¬ InL x xs) → NoDupL xs → NoDupL (x ::L xs)

def lengthL {A : Type} : mylist A → mynat
| mylist.nilL    => O
| (_ ::L tl)=> S (lengthL tl)

class ring (R : Type) where
  (zero      : R)
  (opp       : R → R)
  (one       : R)
  (add       : R → R → R)
  (mul       : R → R → R)

  (one_neq_zero  : one ≠ zero)

  (add_comm  : ∀ x y,    add x y = add y x)
  (add_assoc : ∀ x y z,  add (add x y) z = add x (add y z))
  (add_zero  : ∀ x,      add x zero = x)
  (add_opp   : ∀ x,      add x (opp x) = zero)

  (mul_comm  : ∀ x y,    mul x y = mul y x)
  (mul_assoc : ∀ x y z,  mul (mul x y) z = mul x (mul y z))
  (mul_one   : ∀ x,      mul x one = x)
  (dist_l    : ∀ x y z,  mul x (add y z) = add (mul x y) (mul x z))
  (mul_zero  : ∀ x,      mul x zero = zero)

  (no_zero_div :
    ∀ x y, mul x y = zero → x = zero ∨ y = zero)

notation:35 "-R " x   => ring.opp x
section Polynomial

variable {R : Type} [rR : ring R]
variable {polynomial : Type} [rP : ring polynomial]


variable (degree    : polynomial → mynat)
variable (monomial  : mynat → R → polynomial)
variable (eval      : polynomial → R → R)



local notation:55 x " -R " y => rR.add x (rR.opp y)


def X (monomial : mynat → R → polynomial) : polynomial :=
  monomial (S O) rR.one

def C (monomial : mynat → R → polynomial) (c : R) : polynomial :=
  monomial O c

def X_minus (monomial : mynat → R → polynomial) (a : R) : polynomial :=
  rP.add (X monomial) (C monomial (rR.opp a))


axiom C_zero    : C monomial rR.zero = rP.zero
axiom C_one     : C monomial rR.one  = rP.one

axiom deg_zero  : degree rP.zero = O

axiom eval_add  : ∀ (p q : polynomial) (x : R), eval (rP.add p q) x = rR.add (eval p x) (eval q x)
axiom eval_mul  : ∀ (p q : polynomial) (x : R), eval (rP.mul p q) x = rR.mul (eval p x) (eval q x)
axiom eval_C    : ∀ (c : R) (x : R),   eval (C monomial c) x = c
axiom eval_X    : ∀ (x : R),     eval (X monomial) x     = x

axiom deg_C        : ∀ (c : R), c ≠ rR.zero → degree (C monomial c) = O
axiom deg_constant : ∀ (p : polynomial), degree p = O ↔ ∃ c : R, p = C monomial c
axiom deg_X_minus  : ∀ (a : R), degree (X_minus monomial a) = S O
axiom deg_mul      : ∀ (p q : polynomial), p ≠ rP.zero → q ≠ rP.zero →
                      degree (rP.mul p q) = mynat_add (degree p) (degree q)



axiom euclid_X_minus :
  ∀ p a, ∃ (q r' : polynomial),
    (p = rP.add (rP.mul q (X_minus monomial a)) r') ∧ (degree r' = O)







theorem sub_eq_zero_l : ∀ a b : R, rR.add a (rR.opp b) = rR.zero → a = b := by
  intro a b h
  have h' : rR.add (rR.add a (rR.opp b)) b = rR.add rR.zero b := by
    simpa using congrArg (fun t : R => rR.add t b) h

  have := h'



  have L1 : rR.add (rR.add a (rR.opp b)) b = rR.add a (rR.add (rR.opp b) b) := by
    simpa using (rR.add_assoc a (rR.opp b) b)
  have L2 : rR.add (rR.opp b) b = rR.zero := by
    calc
      rR.add (rR.opp b) b = rR.add b (rR.opp b) := by simpa using (rR.add_comm (rR.opp b) b)
      _ = rR.zero := by simpa using (rR.add_opp b)
  have L3 : rR.add a (rR.add (rR.opp b) b) = rR.add a rR.zero := by simp [L2]
  have L4 : rR.add a rR.zero = a := rR.add_zero a

  have R1 : rR.add rR.zero b = b := by
    calc
      rR.add rR.zero b = rR.add b rR.zero := by simpa using (rR.add_comm rR.zero b)
      _ = b := by simpa using (rR.add_zero b)

  have : a = b := by
    simpa [L1, L2, L3, L4, R1] using h'
  exact this


def is_root (eval : polynomial → R → R) (a : R) (p : polynomial) : Prop := eval p a = rR.zero




theorem root_factor
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (a : R) :
  is_root eval a p → ∃ q : polynomial, p = rP.mul q (X_minus monomial a)
:= by
  intro hp
  --
  rcases (euclid_X_minus (degree := degree) (monomial := monomial) p a) with
    ⟨q, r, h_eq, h_deg⟩

  have hr0 : eval r a = rR.zero := by

    have hsum : eval (rP.add (rP.mul q (X_minus monomial a)) r) a = rR.zero := by
      simpa [h_eq] using hp

    have hsum' : rR.add (eval (rP.mul q (X_minus monomial a)) a) (eval r a) = rR.zero := by
      simpa [eval_add] using hsum

    have hmul : eval (rP.mul q (X_minus monomial a)) a
                  = rR.mul (eval q a) (eval (X_minus monomial a) a) := by
      simp [eval_mul]
    have : rR.add (rR.mul (eval q a) (eval (X_minus monomial a) a)) (eval r a) = rR.zero := by
      simpa [hmul] using hsum'

    have hx : eval (X_minus monomial a) a = rR.add a (rR.opp a) := by
      simp [X_minus, eval_add, eval_X, eval_C]
    have : rR.add (rR.mul (eval q a) (rR.add a (rR.opp a))) (eval r a) = rR.zero := by
      simpa [hx] using this
    have : rR.add (rR.mul (eval q a) rR.zero) (eval r a) = rR.zero := by
      simpa [rR.add_opp] using this
    have : rR.add rR.zero (eval r a) = rR.zero := by
      simpa [rR.mul_zero] using this
    have : rR.add (eval r a) rR.zero = rR.zero := by
      simpa [rR.add_comm] using this
    simpa [rR.add_zero] using this

  rcases (deg_constant (degree := degree) (monomial := monomial) r).mp h_deg with ⟨c, hc⟩
  subst hc

  have : c = rR.zero := by
    simpa [eval_C] using hr0
  subst this

  have : p = rP.mul q (X_minus monomial a) := by
    simpa [C_zero, rP.add_zero] using h_eq
  exact ⟨q, this⟩

theorem root_transfer
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p q : polynomial) (a b : R) :
  p = rP.mul q (X_minus monomial a) →
  b ≠ a →
  is_root eval b p →
  is_root eval b q
:= by
  intro hp hba hpb

  have := hpb
  have hb0 :
    eval (rP.mul q (X_minus monomial a)) b = rR.zero := by
    simpa [hp] using hpb
  have : rR.mul (eval q b) (eval (X_minus monomial a) b) = rR.zero := by
    simpa [eval_mul] using hb0

  have hx : eval (X_minus monomial a) b
              = rR.add b (rR.opp a) := by
    simp [X_minus, eval_add, eval_X, eval_C]

  have h' := rR.no_zero_div (eval q b) (b -R a) (by simpa [hx] using this)
  rcases h' with hq | hba'
  · exact hq
  · have : b = a := sub_eq_zero_l (a := b) (b := a) hba'
    exact (hba this).elim


theorem roots_le_degree
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (xs : mylist R) :
  NoDupL xs →
  (∀ a, InL a xs → is_root eval a p) →
  p ≠ rP.zero →
  mynat_le (lengthL xs) (degree p)
:= by
  intro hnd hrt hp0

  have main : ∀ (xs : mylist R), NoDupL xs →
      ∀ (p : polynomial), (∀ a, InL a xs → is_root eval a p) → p ≠ rP.zero →
      mynat_le (lengthL xs) (degree p) := by
    intro xs
    induction xs with
    | nilL =>
        intro _ p _ _
        simpa using mynat_zero_le (degree p)
    | consL a xs ih =>
        intro hnd_xs p hrt' hp0'

        have ha : is_root eval a p :=
          hrt' a (InL.In_head xs)

        rcases root_factor degree monomial eval p a ha with ⟨q, hpq⟩

        cases hnd_xs with
        | ND_cons _ _ hnotin hnd_tl =>

            have qnz : q ≠ rP.zero := by
              intro h
              have hq0 : rP.mul q (X_minus monomial a) = rP.zero := by
                simp [h, rP.mul_comm, rP.mul_zero]
              have : p = rP.zero := by simp [hpq, hq0]
              exact hp0' this

            have xnz : (X_minus monomial a) ≠ rP.zero := by
              intro h
              have hx0 : rP.mul q (X_minus monomial a) = rP.zero := by
                simp [h, rP.mul_zero]
              have : p = rP.zero := by simp [hpq, hx0]
              exact hp0' this

            have hdeg : degree p = S (degree q) := by
              have := (deg_mul (degree := degree)
                          (p := q) (q := X_minus monomial a)) qnz xnz


              simpa [hpq, deg_X_minus, mynat_add_comm, mynat_add_zero_r, mynat_add_S_r] using this

            have hF : ∀ b, InL b xs → is_root eval b q := by
              intro b hb

              have hba : b ≠ a := by
                intro hbaeq; subst hbaeq
                exact hnotin hb

              have hbroot : is_root eval b p :=
                hrt' b (InL.In_tail (y := a) (xs := xs) hb)

              exact root_transfer degree monomial eval p q a b hpq hba hbroot

            have ihRes := ih hnd_tl q hF qnz

            simpa [hdeg, lengthL] using mynat_succ_le_succ ihRes

  exact main xs hnd p hrt hp0


def poly_of_roots (monomial : mynat → R → polynomial) : mylist R → polynomial
| mylist.nilL       => rP.one
| mylist.consL a xs => rP.mul (X_minus monomial a) (poly_of_roots monomial xs)


theorem X_minus_nonzero
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial) :
  ∀ a, (X_minus monomial a) ≠ rP.zero := by
  intro a h
  have hdeg : degree (X_minus monomial a) = S O :=
    deg_X_minus (degree := degree) (monomial := monomial) a
  have : degree rP.zero = S O := by simpa [h] using hdeg
  have : O = S O := by simp [deg_zero] at this
  cases this


theorem constant_root_zero
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (a : R) :
  degree p = O → is_root eval a p → p = rP.zero := by
  intro hdeg hroot
  rcases (deg_constant (degree := degree) (monomial := monomial) p).mp hdeg with ⟨c, hc⟩
  subst hc
  have : c = rR.zero := by simpa [is_root, eval_C] using hroot
  subst this
  simp [C_zero]


theorem root_of_product
  (eval : polynomial → R → R)
  (p q : polynomial) (a : R) :
  is_root eval a (rP.mul p q) → is_root eval a p ∨ is_root eval a q := by
  intro hpq
  have : rR.mul (eval p a) (eval q a) = rR.zero := by simpa [is_root, eval_mul] using hpq
  simpa [is_root] using rR.no_zero_div (eval p a) (eval q a) this


theorem root_scale_constant
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (c a : R) :
  c ≠ rR.zero → (is_root eval a p ↔ is_root eval a (rP.mul (C monomial c) p)) := by
  intro hc
  constructor
  · intro hp


    have hpa0 : eval p a = rR.zero := hp
    have : rR.mul c (eval p a) = rR.zero := by
      simp [hpa0, rR.mul_zero]
    simpa [is_root, eval_mul, eval_C] using this
  · intro hcp
    have hz : rR.mul c (eval p a) = rR.zero := by
      simpa [is_root, eval_mul, eval_C] using hcp
    have hdisj : c = rR.zero ∨ eval p a = rR.zero := rR.no_zero_div c (eval p a) hz
    cases hdisj with
    | inl hcz => exact (hc hcz).elim
    | inr hp0 => simpa [is_root] using hp0


theorem poly_of_roots_nonzero
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial) :
  ∀ (xs : mylist R), poly_of_roots monomial xs ≠ rP.zero
| mylist.nilL => rP.one_neq_zero
| mylist.consL a xs =>
    by
      intro h

      have := rP.no_zero_div (X_minus monomial a) (poly_of_roots monomial xs) h
      rcases this with hx | hxs
      · exact (X_minus_nonzero (degree := degree) (monomial := monomial) a) hx
      · exact (poly_of_roots_nonzero (degree := degree) (monomial := monomial) xs) hxs


theorem deg_poly_of_roots
  (xs : mylist R) :
  degree (poly_of_roots monomial xs) = lengthL xs := by
  induction xs with
  | nilL =>
      calc
        degree (poly_of_roots monomial mylist.nilL)
            = degree rP.one := by simp [poly_of_roots]
        _   = degree (C monomial rR.one) := by simp [C_one]
        _   = O := by simp [deg_C, rR.one_neq_zero]
  | consL a xs ih =>
      have hx : (X_minus monomial a) ≠ rP.zero :=
        X_minus_nonzero (degree := degree) (monomial := monomial) a
      have hp : (poly_of_roots monomial xs) ≠ rP.zero :=
        poly_of_roots_nonzero (degree := degree) (monomial := monomial) xs
      have hmul :
          degree (poly_of_roots monomial (mylist.consL a xs))
            = mynat_add (degree (X_minus monomial a))
                        (degree (poly_of_roots monomial xs)) := by
        simpa [poly_of_roots] using
          (deg_mul (degree := degree)
            (p := X_minus monomial a) (q := poly_of_roots monomial xs) hx hp)

      have hxdeg : degree (X_minus monomial a) = S O :=
        deg_X_minus (degree := degree) (monomial := monomial) a

      have hstep :
          degree (poly_of_roots monomial (mylist.consL a xs))
            = S (degree (poly_of_roots monomial xs)) := by
        simpa [hxdeg, mynat_add_comm, mynat_add_S_r, mynat_add_zero_r] using hmul

      simpa [lengthL, hstep] using congrArg S ih


theorem root_factor_list
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R) :
  ∀ (p : polynomial) (xs : mylist R),
    NoDupL xs →
    (∀ a, InL a xs → is_root eval a p) →
    ∃ q, p = rP.mul q (poly_of_roots monomial xs)
:= by
  intro p xs; revert p
  induction xs with
  | nilL =>
      intro p _ _
      exact ⟨p, by simp [poly_of_roots, rP.mul_one]⟩
  | consL a xs ih =>
      intro p hnd hroots

      cases hnd with
      | ND_cons _ _ hnotin hnd' =>

          have Ha : InL a (a ::L xs) := InL.In_head xs
          have hroot_pa : is_root eval a p := hroots a Ha
          rcases root_factor (degree := degree) (monomial := monomial) (eval := eval) p a hroot_pa with ⟨q, hpq⟩

          have Hq : ∀ b, InL b xs → is_root eval b q := by
            intro b hb
            have hba : b ≠ a := by
              intro hbaeq; subst hbaeq; exact hnotin hb
            have hbroot : is_root eval b p := hroots b (InL.In_tail (y := a) (xs := xs) hb)
            exact root_transfer (degree := degree) (monomial := monomial) (eval := eval)
              p q a b hpq hba hbroot

          rcases ih q hnd' Hq with ⟨q0, hq0⟩
          refine ⟨q0, ?_⟩



          calc
            p = rP.mul q (X_minus monomial a) := by simp [hpq]
            _ = rP.mul (rP.mul q0 (poly_of_roots monomial xs)) (X_minus monomial a) := by
                  simp [hq0]
            _ = rP.mul q0 (rP.mul (poly_of_roots monomial xs) (X_minus monomial a)) := by
                  simp [rP.mul_assoc]
            _ = rP.mul q0 (rP.mul (X_minus monomial a) (poly_of_roots monomial xs)) := by
                  simp [rP.mul_comm]



theorem degree_factorisation :
  ∀ (p : polynomial) (xs : mylist R) (q : polynomial),
    p = rP.mul q (poly_of_roots monomial xs) →
    q ≠ rP.zero →
    degree p = mynat_add (degree q) (lengthL xs)
:= by
  intro p xs q hp hq
  have hz : poly_of_roots monomial xs ≠ rP.zero :=
    poly_of_roots_nonzero (degree := degree) (monomial := monomial) xs
  simp [hp,
         (deg_mul (degree := degree) _ _ hq hz),
         deg_poly_of_roots (degree := degree) (monomial := monomial) xs]

end Polynomial
