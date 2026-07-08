Class AddMonoid (R : Type) := {
  zero      : R;
  add       : R -> R -> R;
  add_zero  : forall x, add x zero = x;
  add_comm  : forall x y, add x y = add y x;
  add_assoc : forall x y z, add (add x y) z = add x (add y z)
}.

Section CircleAverage.
  Context {R : Type} {M : AddMonoid R}.

  Axiom integral       : (R -> R) -> R.
  Axiom integral_ext   : forall g h,
      (forall θ, g θ = h θ) ->
      integral g = integral h.
  Axiom integral_const : forall c,
      integral (fun _ => c) = c.
  Axiom integral_add   : forall f g,
      integral (fun θ => add (f θ) (g θ)) =
      add (integral f) (integral g).

  Axiom integral_shift : forall f c,
    integral (fun θ => f (add θ c)) = integral f.


  Definition circleMap (c θ : R) : R := add θ c.

  Definition circleAverage (f : R -> R) (c : R) : R :=
    integral (fun θ => f (circleMap c θ)).

  Lemma circleMap_zero :
    forall θ, circleMap zero θ = θ.
  Proof.
    intros θ; unfold circleMap.
    rewrite add_zero; reflexivity.
  Qed.

  Lemma circleAverage_zero :
    forall f, circleAverage f zero = integral f.
  Proof.
    intros f; unfold circleAverage.
    apply integral_ext; intros θ.
    now rewrite circleMap_zero.
  Qed.

  Lemma circleAverage_add :
    forall f g c,
      circleAverage (fun z => add (f z) (g z)) c =
      add (circleAverage f c) (circleAverage g c).
  Proof.
    intros f g c; unfold circleAverage.
    rewrite integral_add; reflexivity.
  Qed.

  Theorem circleAverage_fun_add :
    forall f c,
      circleAverage (fun z => f (add z c)) zero =
      circleAverage f c.
  Proof.
    intros f c.
    unfold circleAverage, circleMap.
    apply integral_ext; intro θ.
    rewrite add_comm.
    rewrite <- (add_assoc c θ zero).
    rewrite add_zero.
    rewrite add_comm.
    reflexivity.
  Qed.

 Lemma circleMap_add :
    forall c d θ,
      circleMap (add c d) θ =
      circleMap c (circleMap d θ).
  Proof.
    intros c d θ; unfold circleMap.
    rewrite add_comm with (x := c) (y := d).
    rewrite add_assoc.
    rewrite <- add_assoc.
    reflexivity.
  Qed.

  Lemma circleAverage_shift :
    forall f c d,
      circleAverage f (add c d) =
      circleAverage (fun z => f (add z d)) c.
  Proof.
    intros f c d.
    unfold circleAverage.
    apply integral_ext; intro θ.
    unfold circleMap.
    rewrite add_assoc; reflexivity.
  Qed.

  Lemma circleAverage_const :
    forall k c, circleAverage (fun _ => k) c = k.
  Proof.
    intros k c; unfold circleAverage.
    rewrite integral_const; reflexivity.
  Qed.

  Lemma circleAverage_add_const :
    forall f k c,
      circleAverage (fun z => add (f z) k) c =
      add (circleAverage f c) k.
  Proof.
    intros f k c; unfold circleAverage.
    replace (fun θ => add (f (circleMap c θ)) k)
      with (fun θ => add (f (circleMap c θ)) ((fun _ => k) θ))
      by reflexivity.
    rewrite integral_add.
    rewrite integral_const.
    reflexivity.
  Qed.

  Lemma circleAverage_comm_add :
    forall f g c,
      circleAverage (fun z => add (f z) (g z)) c =
      circleAverage (fun z => add (g z) (f z)) c.
  Proof.
    intros f g c; unfold circleAverage.
    apply integral_ext; intro θ.
    rewrite add_comm; reflexivity.
  Qed.

  Lemma circleAverage_add_assoc :
    forall f g h c,
      circleAverage (fun z => add (add (f z) (g z)) (h z)) c =
      add (circleAverage f c)
          (add (circleAverage g c) (circleAverage h c)).
  Proof.
    intros f g h c; unfold circleAverage.

    replace
      (fun θ => add (add (f (circleMap c θ)) (g (circleMap c θ)))
                    (h (circleMap c θ)))
      with
      (fun θ => add (add (f (circleMap c θ)) (g (circleMap c θ)))
                    ((fun θ => h (circleMap c θ)) θ))
      by reflexivity.
    rewrite integral_add.

    replace
      (integral (fun θ => add (f (circleMap c θ)) (g (circleMap c θ))))
      with
      (add (integral (fun θ => f (circleMap c θ)))
           (integral (fun θ => g (circleMap c θ))))
      by (rewrite integral_add; reflexivity).

    rewrite add_assoc.
    reflexivity.
  Qed.

  Lemma circleAverage_center_comm :
    forall f c d,
      circleAverage f (add c d) =
      circleAverage f (add d c).
  Proof.
    intros f c d.
    unfold circleAverage, circleMap.
    apply integral_ext; intro θ.
    rewrite (f_equal (fun x => add θ x) (add_comm c d)).
    reflexivity.
  Qed.
  Lemma circleAverage_center_independent :
    forall f c,
      circleAverage f c = integral f.
  Proof.
    intros f c; unfold circleAverage; apply integral_shift.
  Qed.

  Lemma circleAverage_center_eq :
    forall f c d,
      circleAverage f c = circleAverage f d.
  Proof.
    intros f c d.
    rewrite (circleAverage_center_independent f c).
    rewrite (circleAverage_center_independent f d).
    reflexivity.
  Qed.

  Lemma circleAverage_idempotent :
  forall f c,
    circleAverage (fun z => circleAverage f z) c = circleAverage f c.
  Proof.
    intros f c.
    rewrite (circleAverage_center_independent f c).
    unfold circleAverage.
    rewrite <- (integral_const (integral f)).
    apply integral_ext with (h := fun _ => integral f).
    intros θ.
    apply (circleAverage_center_independent f (circleMap c θ)).
  Qed.

  Lemma circleAverage_of_zero_integral :
    forall f c,
      integral f = zero -> circleAverage f c = zero.
  Proof.
    intros f c H.
    rewrite circleAverage_center_independent.
    assumption.
  Qed.

  Lemma circleAverage_linear :
    forall f g c,
      circleAverage (fun z => add (f z) (g z)) c =
      add (circleAverage f c) (circleAverage g c).
  Proof.
    intros f g c.
    unfold circleAverage.
    rewrite integral_add.
    reflexivity.
  Qed.
  
  Lemma circleAverage_shift_commute :
    forall f c d,
      circleAverage (fun z => f (circleMap d z)) c =
      circleAverage f (add c d).
  Proof.
    intros f c d.
    unfold circleAverage, circleMap.
    apply integral_ext.
    intros θ; rewrite add_assoc; reflexivity.
  Qed.
End CircleAverage.
