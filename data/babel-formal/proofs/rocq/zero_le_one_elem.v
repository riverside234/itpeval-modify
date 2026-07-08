Class DecidableEqAlt (A : Type) := {
  dec_eq : forall x y : A, {x = y} + {x <> y}
}.

Class ZeroAlt (A : Type) := zero : A.
Class OneAlt  (A : Type) := one  : A.

Class Preorder (A : Type) := {
  le                  : A -> A -> Prop;
  Preorder_Reflexive  : forall x,       le x x;
  Preorder_Transitive : forall x y z,   le x y -> le y z -> le x z
}.

Infix "≤" := le (at level 70, no associativity).

Class ZeroLEOneClass (A : Type)
      `{ZeroAlt A} `{OneAlt A} `{Preorder A} := {
  zero_le_one : zero ≤ (one : A);
  zero_le_zero : zero ≤ (zero : A)
}.

Section Matrix.
  Variable (m : Type).
  Context `{DecidableEqAlt m}.

  Variable (α : Type).
  Context `{ZeroLEOneClass α}.

  Definition matrix := m -> m -> α.

  Definition One_matrix : matrix :=
    fun i j => if dec_eq i j then one else zero.

  Lemma zero_le_one_elem (i j : m) :
    zero ≤ (One_matrix : matrix) i j.
  Proof.
    unfold One_matrix; simpl.
    destruct (dec_eq i j) as [->|neq].
    - apply zero_le_one.
    - apply zero_le_zero.
  Qed.

  Definition Zero_matrix : matrix := fun _ _ => zero.

  Definition matrix_le (A B : matrix) : Prop :=
    forall i j, A i j ≤ B i j.
  Infix "≤ₘ" := matrix_le (at level 70).

  Lemma Zero_le_One_matrix : Zero_matrix ≤ₘ One_matrix.
  Proof.
    unfold matrix_le, Zero_matrix; intros i j.
    unfold One_matrix; simpl.
    destruct (dec_eq i j) as [->|neq].
    - apply zero_le_one.
    - apply zero_le_zero.
  Qed.

  Lemma matrix_le_refl (A : matrix) : A ≤ₘ A.
  Proof.
    unfold matrix_le; intros i j; apply Preorder_Reflexive.
  Qed.

  Lemma matrix_le_trans (A B C : matrix) :
    A ≤ₘ B -> B ≤ₘ C -> A ≤ₘ C.
  Proof.
    intros HAB HBC i j.
    apply Preorder_Transitive with (y := B i j); [apply HAB | apply HBC].
  Qed.

  Definition matrix_eq (A B : matrix) : Prop :=
    forall i j, A i j = B i j.
  Infix "≃ₘ" := matrix_eq (at level 70).

  Lemma matrix_eq_refl (A : matrix) : A ≃ₘ A.
  Proof.
    unfold matrix_eq; intros i j; reflexivity.
  Qed.

  Lemma matrix_eq_sym (A B : matrix) : A ≃ₘ B -> B ≃ₘ A.
  Proof.
    unfold matrix_eq; intros Ha i j; symmetry; apply Ha.
  Qed.

  Lemma matrix_eq_trans (A B C : matrix) :
    A ≃ₘ B -> B ≃ₘ C -> A ≃ₘ C.
  Proof.
    unfold matrix_eq; intros HAB HBC i j.
    etransitivity; [apply HAB| apply HBC].
  Qed.

  Lemma matrix_eq_le (A B : matrix) :
    A ≃ₘ B -> A ≤ₘ B /\ B ≤ₘ A.
  Proof.
    intro Heq; split.
    - unfold matrix_le; intros i j.
      rewrite <- (Heq i j); apply Preorder_Reflexive.
    - unfold matrix_le; intros i j.
      rewrite   (Heq i j); apply Preorder_Reflexive.
  Qed.

  Class PartialOrder (A : Type) `{Preorder A} := {
    le_antisym : forall x y, x ≤ y -> y ≤ x -> x = y
  }.
  Context {PO : PartialOrder α}.

  Lemma matrix_le_antisymm (A B : matrix) :
    A ≤ₘ B -> B ≤ₘ A -> A ≃ₘ B.
  Proof.
    intros HAB HBA i j.
    apply (@le_antisym α H2 PO); [apply (HAB i j) | apply (HBA i j)].
  Qed.
End Matrix.
