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

inductive mylist (A : Type) : Type
| nilL  : mylist A
| consL : A → mylist A → mylist A

namespace mylist

notation h "::L" t => mylist.consL h t

def mapL {A B : Type} (f : A → B) : mylist A → mylist B
| mylist.nilL    => mylist.nilL
| (x ::L xs)     => f x ::L mapL f xs

def fold_add {R : Type} (add : R → R → R) (z : R) : mylist R → R
| mylist.nilL    => z
| (x ::L xs)     => add x (fold_add add z xs)

end mylist

open mylist

inductive InL {A : Type} (x : A) : mylist A → Prop
| In_head : ∀ xs, InL x (x ::L xs)
| In_tail : ∀ y xs, InL (x := x) xs → InL (x := x) (y ::L xs)

inductive NoDupL {A : Type} : mylist A → Prop
| ND_nil  : NoDupL mylist.nilL
| ND_cons : ∀ x xs, (¬ InL x xs) → NoDupL xs → NoDupL (x ::L xs)

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

section Probability

variable {R : Type} [rR : ring R]
variable {Ω : Type}

def event (Ω : Type) := Ω → Prop

def ev_false : event Ω := fun _ => False
def ev_true  : event Ω := fun _ => True

def ev_inter (A B : event Ω) : event Ω := fun ω => A ω ∧ B ω
def ev_union (A B : event Ω) : event Ω := fun ω => A ω ∨ B ω
def ev_compl (A : event Ω)   : event Ω := fun ω => ¬ A ω
def ev_diff (A B : event Ω)  : event Ω := fun ω => A ω ∧ ¬ B ω

theorem ev_inter_comm (A B : event Ω) : ∀ ω, (ev_inter A B) ω ↔ (ev_inter B A) ω := by
  intro ω; constructor <;> intro h
  · exact And.intro h.right h.left
  · exact And.intro h.right h.left

theorem ev_union_comm (A B : event Ω) : ∀ ω, (ev_union A B) ω ↔ (ev_union B A) ω := by
  intro ω; constructor <;> intro h
  · cases h with
    | inl hA => exact Or.inr hA
    | inr hB => exact Or.inl hB
  · cases h with
    | inl hB => exact Or.inr hB
    | inr hA => exact Or.inl hA

theorem ev_inter_assoc (A B C : event Ω) : ∀ ω,
  (ev_inter (ev_inter A B) C) ω ↔ (ev_inter A (ev_inter B C)) ω := by
  intro ω; constructor <;> intro h
  · rcases h with ⟨hAB, hC⟩; rcases hAB with ⟨hA, hB⟩; exact ⟨hA, ⟨hB, hC⟩⟩
  · rcases h with ⟨hA, hBC⟩; rcases hBC with ⟨hB, hC⟩; exact ⟨⟨hA, hB⟩, hC⟩

theorem ev_union_assoc (A B C : event Ω) : ∀ ω,
  (ev_union (ev_union A B) C) ω ↔ (ev_union A (ev_union B C)) ω := by
  intro ω; constructor <;> intro h
  · rcases h with h | h
    · rcases h with hA | hB
      · exact Or.inl hA
      · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr h)
  · rcases h with hA | hBC
    · exact Or.inl (Or.inl hA)
    · rcases hBC with hB | hC
      · exact Or.inl (Or.inr hB)
      · exact Or.inr hC

theorem ev_inter_distrib_left (A B C : event Ω) : ∀ ω,
  (ev_inter A (ev_union B C)) ω ↔ (ev_union (ev_inter A B) (ev_inter A C)) ω := by
  intro ω; constructor <;> intro h
  · rcases h with ⟨hA, hBC⟩; rcases hBC with hB | hC
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hC⟩
  · rcases h with hAB | hAC
    · rcases hAB with ⟨hA, hB⟩; exact ⟨hA, Or.inl hB⟩
    · rcases hAC with ⟨hA, hC⟩; exact ⟨hA, Or.inr hC⟩

def disjoint (A B : event Ω) : Prop := ∀ ω, ¬ ((ev_inter A B) ω)

def pairwise_disjoint : mylist (event Ω) → Prop
| mylist.nilL      => True
| (_ ::L mylist.nilL) => True
| (A ::L (B ::L xs))  => disjoint A B ∧ (∀ C, InL C (B ::L xs) → disjoint A C) ∧ pairwise_disjoint (B ::L xs)

def bigUnion : mylist (event Ω) → event Ω
| mylist.nilL      => ev_false
| (A ::L xs)       => ev_union A (bigUnion xs)

variable (prob : event Ω → R)

axiom prob_ext : ∀ {A B : event Ω}, (∀ ω, A ω ↔ B ω) → prob A = prob B
axiom prob_false : prob ev_false = rR.zero
axiom prob_true  : prob ev_true  = rR.one

axiom prob_union : ∀ (A B : event Ω),
  prob (ev_union A B) = rR.add (prob A) (rR.add (prob B) (rR.opp (prob (ev_inter A B))))

axiom prob_compl : ∀ (A : event Ω), prob (ev_compl A) = rR.add rR.one (rR.opp (prob A))

axiom em : ∀ p : Prop, p ∨ ¬ p

axiom cprob : event Ω → event Ω → R
axiom cprob_mul : ∀ A B, prob (ev_inter A B) = rR.mul (cprob A B) (prob B)

def indep (A B : event Ω) : Prop := prob (ev_inter A B) = rR.mul (prob A) (prob B)

local notation:55 x " -R " y => rR.add x (rR.opp y)

axiom opp_zero  : rR.opp rR.zero = rR.zero
axiom opp_opp   : ∀ x, rR.opp (rR.opp x) = x
axiom opp_mul_right : ∀ x y, rR.mul x (rR.opp y) = rR.opp (rR.mul x y)
axiom opp_mul_left  : ∀ x y, rR.mul (rR.opp x) y = rR.opp (rR.mul x y)

axiom prob_union_disjoint : ∀ (A B : event Ω), disjoint A B → prob (ev_union A B) = rR.add (prob A) (prob B)
axiom disjoint_head_tail : ∀ (A : event Ω) (xs : mylist (event Ω)), pairwise_disjoint (A ::L xs) → disjoint A (bigUnion xs)

theorem prob_union_comm (A B : event Ω) :
  prob (ev_union A B) = prob (ev_union B A) := by
  have h₁ := prob_union (prob := prob) A B
  have h₂ := prob_union (prob := prob) B A
  have hcap : prob (ev_inter A B) = prob (ev_inter B A) := by
    have := prob_ext (prob := prob) (A := ev_inter A B) (B := ev_inter B A) (ev_inter_comm A B)
    exact this
  have hunion : prob (ev_union A B) = prob (ev_union B A) := by
    exact prob_ext (prob := prob) (A := ev_union A B) (B := ev_union B A) (ev_union_comm A B)
  exact hunion

theorem prob_union_idem (A : event Ω) :
  prob (ev_union A A) = prob A := by
  have h := prob_union (prob := prob) A A
  -- (A ∧ A) ↔ A, written as a pure term (no `by`)
  have hAA : ∀ ω, ev_inter A A ω ↔ A ω :=
    fun ω => Iff.intro (fun h => h.left) (fun h => And.intro h h)
  have hcap : prob (ev_inter A A) = prob A :=
    prob_ext (prob := prob) (A := ev_inter A A) (B := A) hAA
  have h2 : rR.add (prob A) (rR.opp (prob A)) = rR.zero := rR.add_opp (prob A)
  have h3 : rR.add (prob A) (rR.add (prob A) (rR.opp (prob A))) = rR.add (prob A) rR.zero := by simp [h2]
  have h4 : rR.add (prob A) rR.zero = prob A := rR.add_zero (prob A)
  have : prob (ev_union A A) = rR.add (prob A) (rR.add (prob A) (rR.opp (prob A))) := by
    simpa [hcap]
    using h
  simpa [h3, h4]





theorem prob_diff (A B : event Ω) :
  prob (ev_diff A B) = prob A -R prob (ev_inter A B) := by
  have hpart : ∀ ω, (A ω) ↔ (ev_union (ev_inter A B) (ev_inter A (ev_compl B))) ω := by
    intro ω; constructor
    · intro hA
      have hb := em (B ω)
      cases hb with
      | inl hB => exact Or.inl ⟨hA, hB⟩
      | inr hB => exact Or.inr ⟨hA, hB⟩
    · intro hU; cases hU with
      | inl hAB => exact hAB.left
      | inr hAcB => exact hAcB.left
  have hcap_disj : ∀ ω, (ev_inter (ev_inter A B) (ev_inter A (ev_compl B))) ω ↔ False := by
    intro ω; constructor <;> intro h
    · rcases h with ⟨hAB, hAcB⟩; exact hAcB.right hAB.right
    · cases h
  have hAeq := prob_ext (prob := prob) (A := A) (B := ev_union (ev_inter A B) (ev_inter A (ev_compl B))) hpart
  have hcap0 : prob (ev_inter (ev_inter A B) (ev_inter A (ev_compl B))) = rR.zero := by
    have := prob_ext (prob := prob) (A := ev_inter (ev_inter A B) (ev_inter A (ev_compl B))) (B := ev_false) hcap_disj
    simpa [prob_false] using this
  have h := prob_union (prob := prob) (ev_inter A B) (ev_inter A (ev_compl B))
  have hsumA : prob A = rR.add (prob (ev_inter A B)) (prob (ev_inter A (ev_compl B))) := by
    have : prob A = prob (ev_union (ev_inter A B) (ev_inter A (ev_compl B))) := by
      simpa using hAeq
    have hU := h
    have hzero_opp : rR.opp (prob (ev_inter (ev_inter A B) (ev_inter A (ev_compl B)))) = rR.opp rR.zero := by
      simp [hcap0]
    have hopp0 : rR.opp rR.zero = rR.zero := opp_zero
    simpa [this, hzero_opp, hopp0, rR.add_assoc, rR.add_zero]
      using hU
  have heq_diff : prob (ev_diff A B) = prob (ev_inter A (ev_compl B)) := by
    exact prob_ext (prob := prob) (A := ev_diff A B) (B := ev_inter A (ev_compl B)) (by intro ω; constructor <;> intro h; exact h; exact h)
  have hsub : rR.add (prob A) (rR.opp (prob (ev_inter A B)))
              = prob (ev_inter A (ev_compl B)) := by
    calc
      rR.add (prob A) (rR.opp (prob (ev_inter A B)))
          = rR.add (rR.add (prob (ev_inter A B)) (prob (ev_inter A (ev_compl B)))) (rR.opp (prob (ev_inter A B))) := by
              simp [hsumA]
      _ = rR.add (prob (ev_inter A B)) (rR.add (prob (ev_inter A (ev_compl B))) (rR.opp (prob (ev_inter A B)))) := by
              simpa using (rR.add_assoc (prob (ev_inter A B)) (prob (ev_inter A (ev_compl B))) (rR.opp (prob (ev_inter A B))))
      _ = rR.add (rR.add (prob (ev_inter A (ev_compl B))) (rR.opp (prob (ev_inter A B)))) (prob (ev_inter A B)) := by
              simpa using (rR.add_comm (prob (ev_inter A B)) (rR.add (prob (ev_inter A (ev_compl B))) (rR.opp (prob (ev_inter A B)))))
      _ = rR.add (prob (ev_inter A (ev_compl B))) (rR.add (rR.opp (prob (ev_inter A B))) (prob (ev_inter A B))) := by
              simpa using (rR.add_assoc (prob (ev_inter A (ev_compl B))) (rR.opp (prob (ev_inter A B))) (prob (ev_inter A B)))
      _ = rR.add (prob (ev_inter A (ev_compl B))) (rR.add (prob (ev_inter A B)) (rR.opp (prob (ev_inter A B)))) := by
              have := rR.add_comm (rR.opp (prob (ev_inter A B))) (prob (ev_inter A B))
              simpa using congrArg (fun t => rR.add (prob (ev_inter A (ev_compl B))) t) this
      _ = rR.add (prob (ev_inter A (ev_compl B))) rR.zero := by
              simp [rR.add_opp]
      _ = prob (ev_inter A (ev_compl B)) := by
              simp [rR.add_zero]
  simpa [heq_diff] using hsub.symm

theorem bayes_symm (A B : event Ω) :
  rR.mul (cprob A B) (prob B) = rR.mul (cprob B A) (prob A) := by
  calc
    rR.mul (cprob A B) (prob B) = prob (ev_inter A B) := by simpa using (cprob_mul (prob := prob) A B).symm
    _ = prob (ev_inter B A) := by
          have := prob_ext (prob := prob) (A := ev_inter A B) (B := ev_inter B A) (ev_inter_comm A B)
          simpa using this
    _ = rR.mul (cprob B A) (prob A) := by simpa using (cprob_mul (prob := prob) B A)

theorem law_total_prob (A B : event Ω) :
  prob A = rR.add (rR.mul (cprob A B) (prob B)) (rR.mul (cprob A (ev_compl B)) (prob (ev_compl B))) := by
  have hpart : ∀ ω, (A ω) ↔ (ev_union (ev_inter A B) (ev_inter A (ev_compl B))) ω := by
    intro ω; constructor
    · intro hA; cases em (B ω) with
      | inl hB => exact Or.inl ⟨hA, hB⟩
      | inr hB => exact Or.inr ⟨hA, hB⟩
    · intro hU; cases hU with
      | inl hAB  => exact hAB.left
      | inr hAcB => exact hAcB.left
  have hAeq := prob_ext (prob := prob) (A := A) (B := ev_union (ev_inter A B) (ev_inter A (ev_compl B))) hpart
  have hcap0 : prob (ev_inter (ev_inter A B) (ev_inter A (ev_compl B))) = rR.zero := by
    have : ∀ ω, (ev_inter (ev_inter A B) (ev_inter A (ev_compl B))) ω ↔ False := by
      intro ω; constructor <;> intro h
      · rcases h with ⟨hAB, hAcB⟩; exact hAcB.right hAB.right
      · cases h
    have := prob_ext (prob := prob) (A := ev_inter (ev_inter A B) (ev_inter A (ev_compl B))) (B := ev_false) this
    simpa [prob_false] using this
  have h := prob_union (prob := prob) (ev_inter A B) (ev_inter A (ev_compl B))
  have hsumA : prob A = rR.add (prob (ev_inter A B)) (prob (ev_inter A (ev_compl B))) := by
    have : prob A = prob (ev_union (ev_inter A B) (ev_inter A (ev_compl B))) := by
      simpa using hAeq
    have hU := h
    have hzero_opp : rR.opp (prob (ev_inter (ev_inter A B) (ev_inter A (ev_compl B)))) = rR.opp rR.zero := by
      simp [hcap0]
    have hopp0 : rR.opp rR.zero = rR.zero := opp_zero
    simpa [this, hzero_opp, hopp0, rR.add_assoc, rR.add_zero]
      using hU
  simp [hsumA, cprob_mul (prob := prob) A B, cprob_mul (prob := prob) A (ev_compl B)]

theorem prob_union_indep (A B : event Ω) :
  indep (prob := prob) A B →
  prob (ev_union A B) = rR.add (prob A) (rR.add (prob B) (rR.opp (rR.mul (prob A) (prob B)))) := by
  intro hI
  have hU := prob_union (prob := prob) A B
  have hIeq : prob (ev_inter A B) = rR.mul (prob A) (prob B) := hI
  simpa [hIeq] using hU

theorem indep_compl_right (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) A (ev_compl B) := by
  intro hI
  have hdiff := prob_diff (prob := prob) A B
  have heq_diff : prob (ev_inter A (ev_compl B)) = rR.add (prob A) (rR.opp (prob (ev_inter A B))) := by
    have hset : prob (ev_diff A B) = prob (ev_inter A (ev_compl B)) :=
      prob_ext (prob := prob) (A := ev_diff A B) (B := ev_inter A (ev_compl B))
        (by intro ω; constructor <;> intro h <;> exact h)
    simpa [hset] using hdiff
  have hIeq : prob (ev_inter A B) = rR.mul (prob A) (prob B) := hI
  have hlhs : prob (ev_inter A (ev_compl B)) = rR.add (prob A) (rR.opp (rR.mul (prob A) (prob B))) := by
    simpa [hIeq]
      using heq_diff
  have hdist : rR.add (rR.mul (prob A) rR.one) (rR.mul (prob A) (rR.opp (prob B)))
                = rR.mul (prob A) (rR.add rR.one (rR.opp (prob B))) := by
    simpa using (rR.dist_l (prob A) rR.one (rR.opp (prob B))).symm
  have hmul1 : rR.mul (prob A) rR.one = prob A := rR.mul_one (prob A)
  have hmul2 : rR.mul (prob A) (rR.opp (prob B)) = rR.opp (rR.mul (prob A) (prob B)) := by
    simpa using (opp_mul_right (prob A) (prob B))
  have halg : rR.add (prob A) (rR.opp (rR.mul (prob A) (prob B)))
              = rR.mul (prob A) (rR.add rR.one (rR.opp (prob B))) := by
    simpa [hmul1, hmul2] using hdist
  have : prob (ev_inter A (ev_compl B)) = rR.mul (prob A) (prob (ev_compl B)) := by
    simpa [prob_compl (prob := prob) B, halg] using hlhs
  exact this

theorem indep_symm (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) B A := by
  intro hI
  unfold indep at hI
  unfold indep
  have hcap : prob (ev_inter B A) = prob (ev_inter A B) := by
    have := prob_ext (prob := prob) (A := ev_inter B A) (B := ev_inter A B) (ev_inter_comm B A)
    simpa using this
  have hmul : rR.mul (prob A) (prob B) = rR.mul (prob B) (prob A) := by
    simpa using (rR.mul_comm (prob A) (prob B))
  calc
    prob (ev_inter B A) = prob (ev_inter A B) := hcap
    _ = rR.mul (prob A) (prob B) := hI
    _ = rR.mul (prob B) (prob A) := by simpa using hmul

theorem indep_compl_left (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) (ev_compl A) B := by
  intro hI
  have hBA : indep (prob := prob) B A := indep_symm (prob := prob) A B hI
  have hBnotA : indep (prob := prob) B (ev_compl A) :=
    indep_compl_right (prob := prob) B A hBA
  exact indep_symm (prob := prob) B (ev_compl A) hBnotA

axiom indep_compl_both (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) (ev_compl A) (ev_compl B)

theorem prob_bigUnion_disjoint
  (xs : mylist (event Ω))
  (hp : pairwise_disjoint xs) :
  prob (bigUnion xs)
    = mylist.fold_add rR.add rR.zero (mylist.mapL prob xs) := by
  revert hp
  induction xs with
  | nilL =>
      intro _
      simp [bigUnion, mylist.fold_add, mylist.mapL, prob_false]
  | consL A xs ih =>
      intro hp
      cases xs with
      | nilL =>
          have hunionA : prob (ev_union A ev_false) = prob A :=
            prob_ext (prob := prob) (A := ev_union A ev_false) (B := A)
              (by
                intro ω; constructor
                · intro h; cases h with
                  | inl hA => exact hA
                  | inr hf => exact False.elim hf
                · intro hA; exact Or.inl hA)
          simp [bigUnion, mylist.fold_add, mylist.mapL, rR.add_zero, hunionA]
      | consL B xs' =>
          rcases hp with ⟨hAB, hrest, hpw⟩
          have hAdisj : disjoint A (bigUnion (B ::L xs')) :=
            disjoint_head_tail A (B ::L xs') (by
              exact And.intro hAB (And.intro hrest hpw))
          have hU' :
              prob (bigUnion (A ::L (B ::L xs'))) =
              rR.add (prob A) (prob (bigUnion (B ::L xs'))) := by
            simpa [bigUnion] using
              (prob_union_disjoint (prob := prob) A (bigUnion (B ::L xs')) hAdisj)
          have htail :
              prob (bigUnion (B ::L xs')) =
              mylist.fold_add rR.add rR.zero (mylist.mapL prob (B ::L xs')) :=
            ih hpw
          have hsum :
              prob (bigUnion (A ::L (B ::L xs'))) =
              rR.add (prob A)
                (mylist.fold_add rR.add rR.zero (mylist.mapL prob (B ::L xs'))) := by
            simpa [htail] using hU'
          simpa [bigUnion, mylist.mapL, mylist.fold_add, rR.add_assoc] using hsum

theorem prob_bigUnion_disjoint_zero
  (xs : mylist (event Ω))
  (hp : pairwise_disjoint xs)
  (hzero : ∀ A, InL A xs → prob A = rR.zero) :
  prob (bigUnion xs) = rR.zero := by
  revert hp hzero
  induction xs with
  | nilL =>
      intro _ _
      simp [bigUnion, prob_false]
  | consL A xs ih =>
      intro hp hzero
      cases xs with
      | nilL =>
          have hA0 : prob A = ring.zero := hzero A (InL.In_head _)
          have hunionA : prob (ev_union A ev_false) = prob A :=
            prob_ext (prob := prob) (A := ev_union A ev_false) (B := A)
              (by
                intro ω; constructor
                · intro h; cases h with
                  | inl hA => exact hA
                  | inr hf => exact False.elim hf
                · intro hA; exact Or.inl hA)
          simp [bigUnion, hunionA, hA0]
      | consL B xs' =>
          rcases hp with ⟨hAB, hrest, hpw⟩
          have hAdisj : disjoint A (bigUnion (B ::L xs')) :=
            disjoint_head_tail A (B ::L xs') (by exact And.intro hAB (And.intro hrest hpw))
          have hA0 : prob A = rR.zero := hzero A (InL.In_head _)
          have htail0 : ∀ C, InL C (B ::L xs') → prob C = rR.zero := by
            intro C hC; exact hzero C (InL.In_tail (y := A) (xs := B ::L xs') hC)
          have htail : prob (bigUnion (B ::L xs')) = rR.zero := ih hpw htail0
          have hU :
            prob (bigUnion (A ::L (B ::L xs'))) =
            rR.add (prob A) (prob (bigUnion (B ::L xs'))) := by
            simpa [bigUnion] using
              (prob_union_disjoint (prob := prob) A (bigUnion (B ::L xs')) hAdisj)
          have hsum00 :
            rR.add (prob A) (prob (bigUnion (B ::L xs'))) =
            rR.add rR.zero rR.zero := by
            simp [hA0, htail]
          have : prob (bigUnion (A ::L (B ::L xs'))) =
                rR.add rR.zero rR.zero := by
            simpa [hsum00] using hU
          have hz : rR.add rR.zero rR.zero = rR.zero := by
            simp [rR.add_zero]
          simp [this, hz]



axiom inclusion_exclusion_three (A B C : event Ω) :
  prob (ev_union (ev_union A B) C)
    = rR.add (prob A)
      (rR.add (prob B)
        (rR.add (prob C)
          (rR.opp (rR.add (prob (ev_inter A B))
                 (rR.add (prob (ev_inter A C))
                         (rR.add (prob (ev_inter B C))
                                 (rR.opp (prob (ev_inter (ev_inter A B) C)))))))))

end Probability
