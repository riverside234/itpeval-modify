Section SetAlgebra.
  Variable X : Type.
  Axiom classic : forall P:Prop, P \/ ~P.

  Definition sUnion (A B : X -> Prop) : X -> Prop := fun x => A x \/ B x.
  Definition sInter (A B : X -> Prop) : X -> Prop := fun x => A x /\ B x.
  Definition sCompl (A : X -> Prop) : X -> Prop := fun x => ~ A x.

  Lemma inter_distrib_left (A B C : X -> Prop) :
    forall x, (sInter A (sUnion B C)) x <-> (sUnion (sInter A B) (sInter A C)) x.
  Proof.
    intro x; split; intros H.
    - destruct H as [HA [HB|HC]]; [left|right]; split; assumption.
    - destruct H as [[HA HB]|[HA HC]]; split; try assumption; [left|right]; assumption.
  Qed.

  Lemma inter_distrib_right (A B C : X -> Prop) :
    forall x, (sInter (sUnion A B) C) x <-> (sUnion (sInter A C) (sInter B C)) x.
  Proof.
    intro x; split; intros H.
    - destruct H as [[HA|HB] HC]; [left|right]; split; assumption.
    - destruct H as [[HA HC]|[HB HC]]; split; try assumption; [left|right]; assumption.
  Qed.

  Lemma de_morgan_union (A B : X -> Prop) :
    forall x, (sCompl (sUnion A B)) x <-> (sInter (sCompl A) (sCompl B)) x.
  Proof.
    intro x; split; intros H.
    - split; intro H'; apply H; [left|right]; assumption.
    - intros [HA|HB]; destruct H as [H1 H2]; [apply H1|apply H2]; assumption.
  Qed.

  Lemma de_morgan_inter (A B : X -> Prop) :
    forall x, (sCompl (sInter A B)) x <-> (sUnion (sCompl A) (sCompl B)) x.
  Proof.
    intro x; split; intros H.
    - destruct (classic (A x)) as [HA|HnA].
      + right; intro HB; apply H; split; assumption.
      + left; exact HnA.
    - intros [HA HB]; destruct H as [HnA|HnB]; [apply HnA in HA|apply HnB in HB]; contradiction.
  Qed.

End SetAlgebra.
