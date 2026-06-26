



Section Graph.
  Variable V : Type.
  Definition Edge := V -> V -> Prop.

  Inductive Path (E : Edge) : V -> V -> Prop :=
  | Pnil  : forall v, Path E v v
  | Pstep : forall u v w, Path E u v -> E v w -> Path E u w.

  Lemma path_refl (E : Edge) (v : V) : Path E v v.
  Proof. apply Pnil. Qed.

  Fixpoint append_right (E : Edge) (v w : V) (p2 : Path E v w)
           {struct p2} : forall u : V, Path E u v -> Path E u w :=
    match p2 with
    | @Pnil _ v0 => fun _ p1 => p1
    | @Pstep _ v0 y z pv Eyz => fun u p1 => Pstep E u y z (append_right E v0 y pv u p1) Eyz
    end.

  Lemma trans (E : Edge) (u v w : V) :
    Path E u v -> Path E v w -> Path E u w.
  Proof. intros p1 p2; exact (append_right E v w p2 u p1). Qed.

  Definition undirected (E : Edge) : Prop := forall x y, E x y -> E y x.




  Lemma concat_edge_right (E : Edge) (u v w : V) :
    Path E u v -> E v w -> Path E u w.
  Proof. intros p evw; now apply (Pstep _ _ _ _ p evw). Qed.

  Lemma concat (E : Edge) (u v w : V) :
    Path E u v -> Path E v w -> Path E u w.
  Proof. intros; eapply trans; eauto. Qed.


  Lemma edge_path (E : Edge) (u v : V) : E u v -> Path E u v.
  Proof.
    intro euv.
    refine (Pstep E u u v _ euv).
    apply Pnil.
  Qed.

  Lemma concat_edge_left (E : Edge) (u v w : V) :
    E u v -> Path E v w -> Path E u w.
  Proof.
    intros euv pvw.
    eapply trans; [apply edge_path; exact euv|exact pvw].
  Qed.

  Lemma concat3 (E : Edge) (u v w t : V) :
    Path E u v -> Path E v w -> Path E w t -> Path E u t.
  Proof.
    intros puv pvw pwt.
    eapply trans; [eapply trans; eauto|assumption].
  Qed.

  Definition Erev (E : Edge) : Edge := fun x y => E y x.

  Lemma reverse_in_Erev (E : Edge) (u v : V) :
    Path E u v -> Path (Erev E) v u.
  Proof.
    intro p; induction p.
    - apply Pnil.
    - eapply trans; [|apply IHp].
      eapply Pstep; [apply Pnil|assumption].
  Qed.

  Lemma cycle_refl (E : Edge) (v w : V) :
    Path E v w -> Path E w v -> Path E v v.
  Proof. intros pvw pwv; eapply trans; eauto. Qed.

End Graph.
