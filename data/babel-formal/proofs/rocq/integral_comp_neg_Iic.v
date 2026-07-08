
Class RField (R : Type) := {
  zero   : R;
  one    : R;
  add    : R -> R -> R;
  opp    : R -> R;
  mul    : R -> R -> R;
  le     : R -> R -> Prop;
  lt     : R -> R -> Prop;
  abs    : R -> R;

  add_comm      : forall x y, add x y = add y x;
  add_assoc     : forall x y z, add (add x y) z = add x (add y z);
  add_zero      : forall x, add x zero = x;
  add_opp       : forall x, add (opp x) x = zero;
  add_right_cancel : forall x y z, add x z = add y z -> x = y;

  mul_comm      : forall x y, mul x y = mul y x;
  mul_assoc     : forall x y z, mul (mul x y) z = mul x (mul y z);
  mul_one       : forall x, mul x one = x;
  dist_l        : forall x y z, mul x (add y z) = add (mul x y) (mul x z);
  opp_involutive : forall x, opp (opp x) = x;

  add_le_compat : forall x y z, le x y -> le (add x z) (add y z);
  mul_le_compat : forall x y z, le zero z -> le x y -> le (mul x z) (mul y z);
  zero_le_one   : le zero one;
  le_total      : forall x y, le x y \/ le y x;
  
  le_dec : forall x y, { le x y } + { ~ le x y };

  le_opp        : forall x y, le x y -> le (opp y) (opp x);
  le_antisymm   : forall x y, le x y -> le y x -> x = y;
  lt_opp        : forall x y, lt x y -> lt (opp y) (opp x);
  le_refl       : forall x, le x x;
  le_trans      : forall x y z, le x y -> le y z -> le x z;
  lt_def        : forall x y, lt x y <-> (le x y /\ x <> y);

  abs_pos       : forall x, le zero  x -> abs x = x;
  abs_neg       : forall x, le x zero -> abs x = opp x;
  abs_nonneg    : forall x, le zero (abs x);
  abs_opp       : forall x, abs (opp x) = abs x;
  abs_triangle  : forall x y, le (abs (add x y)) (add (abs x) (abs y));
}.


Class Integral (R : Type) `{RField R} := {
  sigma       : (R -> Prop) -> (R -> R) -> R;
  sigma_mul_const : forall (D : R -> Prop) (f : R -> R) (c : R),
    sigma D (fun x => mul c (f x)) = mul c (sigma D f);
  sigma_congr : forall D f g,
    (forall x, D x -> f x = g x) -> sigma D f = sigma D g;
  sigma_zero  : forall D, sigma D (fun _ => zero) = zero;
  sigma_add   : forall D f g,
    sigma D (fun x => add (f x) (g x)) = add (sigma D f) (sigma D g);

  sigma_union_disjoint : forall (D E : R -> Prop) (f : R -> R),
    (forall x, D x -> E x -> False) ->
    sigma (fun x => D x \/ E x) f = add (sigma D f) (sigma E f);
  sigma_le : forall D f g,
    (forall x, D x -> le (f x) (g x)) -> le (sigma D f) (sigma D g);
  sigma_dom_congr : forall D E f,
    (forall x, D x <-> E x) -> sigma D f = sigma E f
}.

Section Integrals.
  Variable (R : Type).
  Context `{RField R} `{Integral R}.

  Notation "- x" := (opp x) : integral_scope.
  Infix "+" := add : integral_scope.
  Infix "*" := mul : integral_scope.
  Infix "<=" := le : integral_scope.
  Infix "<"  := lt : integral_scope.
  Open Scope integral_scope.

  Definition Iic (c : R) : R -> Prop := fun x => x <= c.
  Definition Ioi (c : R) : R -> Prop := fun x => c < x.
  Definition Iio (c : R) : R -> Prop := fun x => x < c.
  Definition union (D E : R -> Prop) : R -> Prop := fun x => D x \/ E x.
  Definition inter (D E : R -> Prop) : R -> Prop := fun x => D x /\ E x.

  Lemma lt_irrefl : forall x, ~ lt x x.
  Proof.
    intros x H2. apply lt_def in H2.
    destruct H2 as [Hle Hneq].
    apply Hneq.
    trivial.
  Qed.

  Lemma lt_trans_strict : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z Hxy Hyz.
    apply lt_def. split.
    - apply le_trans with (y := y).
      + apply (proj1 (lt_def x y)). assumption.
      + apply (proj1 (lt_def y z)). assumption.
    - intros Heq. subst z.
      apply lt_def in Hxy.
      apply lt_def in Hyz.
      destruct Hxy as [Hxy_le Hxy_neq].
      destruct Hyz as [Hyz_le Hyz_neq].
      apply Hxy_neq.
      apply le_antisymm; assumption.
  Qed.


  Definition preimage (g : R -> R) (D : R -> Prop) : R -> Prop :=
    fun x => D (g x).

  Lemma preimage_union (D E : R -> Prop) (g : R -> R) (x : R) :
    preimage g (union D E) x <-> preimage g D x \/ preimage g E x.
  Proof.
    unfold preimage, union; simpl; tauto.
  Qed.

  Lemma preimage_inter (D E : R -> Prop) (g : R -> R) (x : R) :
    preimage g (inter D E) x <-> preimage g D x /\ preimage g E x.
  Proof.
    unfold preimage, inter; simpl; tauto.
  Qed.

  Lemma preimage_neg_Ioi (c x : R) :
    preimage opp (Ioi c) x <-> lt x (opp c).
  Proof.
    unfold preimage, Ioi; simpl.
    split; intro Ha; apply lt_opp in Ha; rewrite opp_involutive in Ha; assumption.
  Qed.

  Lemma preimage_neg_Iic (c x: R) :
     preimage opp (Iic c) x <-> Iic x (opp c).
  Proof.
    unfold preimage, Iic; simpl.
    split; intro Ha; apply le_opp in Ha; rewrite opp_involutive in Ha; exact Ha.
  Qed.

  Lemma preimage_comp (D : R -> Prop) (g h: R -> R) :
    forall x, preimage g (preimage h D) x <-> preimage (fun x => h (g x)) D x.
  Proof.
    intros x.
    unfold preimage.
    split; trivial.
  Qed.

  Lemma integral_neg (D : R -> Prop) (f: R -> R) :
  sigma D (fun x => opp (f x)) = opp (sigma D f).
  Proof.
    apply (add_right_cancel _ _ (sigma D f)).
    rewrite add_comm, <- sigma_add.
    rewrite (sigma_congr D
              (fun x => add (f x) (opp (f x)))
              (fun _ => zero)).
    - rewrite sigma_zero, add_opp; reflexivity.
    - intros x _; rewrite <- add_comm; apply add_opp.
  Qed.

  Lemma integral_sub (D : R -> Prop) (f g: R -> R):
    sigma D (fun x => add (f x) (opp (g x))) = add (sigma D f) (opp (sigma D g)).
  Proof.
    rewrite sigma_add.
    rewrite integral_neg.
    reflexivity.
  Qed.

  Lemma sigma_empty (f : R -> R) :
    sigma (fun _ => False) f = zero.
  Proof.
    transitivity (sigma (fun _ => False) (fun _ => zero)).
    - apply sigma_congr.
      intros x Ha; inversion Ha.
    - apply sigma_zero.
  Qed.

  Lemma sigma_bilinear (D : R -> Prop) (f g: R -> R) (c d: R) :
    sigma D (fun x => add (mul c (f x)) (mul d (g x))) =
      add (mul c (sigma D f)) (mul d (sigma D g)).
  Proof.
    rewrite sigma_add.
    rewrite sigma_mul_const.
    rewrite sigma_mul_const.
    reflexivity.
  Qed.

  Lemma sigma_le_monotone (D : R -> Prop) (f g: R -> R) :
    (forall x, D x -> le (f x) (g x)) ->
    le (sigma D f) (sigma D g).
  Proof.
    intros Ha. apply sigma_le; assumption.
  Qed.

  Lemma sigma_nonneg (D : R -> Prop) (f: R -> R) :
    (forall x, D x -> le zero (f x)) ->
    le zero (sigma D f).
  Proof.
    intros H0f; rewrite <- (sigma_zero D); apply sigma_le; assumption.
  Qed.

  Lemma sigma_split (D : R -> Prop) (P : R -> Prop) (f : R -> R)
  (P_dec : forall x, D x -> P x \/ ~ P x) :
    sigma D f =
      add (sigma (fun x => D x /\ P x) f)
          (sigma (fun x => D x /\ ~ P x) f).
  Proof.
    set (E := fun x => D x /\ P x) in *.
    set (F := fun x => D x /\ ~ P x) in *.
    assert (Disj: forall x, E x -> F x -> False).
    { unfold E, F; intros x [HDx HPx] [_ HnPx]; apply HnPx; assumption. }
    assert (EqDom: forall x, D x <-> (E x \/ F x)).
    { intros x; unfold E, F; split.
      - intros HDx. destruct (P_dec x HDx) as [HPx | HnPx].
        + left; split; assumption.
        + right; split; assumption.
      - intros [[HDx _] | [HDx _]]; assumption.
    }
    rewrite (sigma_dom_congr D (fun x => E x \/ F x) f EqDom).
    apply sigma_union_disjoint; assumption.
  Qed.

  Lemma sigma_preimage_neg_Ioi (f: R -> R) (c: R) :
    sigma (preimage opp (Ioi c)) f = sigma (Iio (opp c)) f.
  Proof.
    apply sigma_dom_congr; intros x; apply preimage_neg_Ioi.
  Qed.

  Lemma sigma_abs_bound {D f} :
    le (abs (sigma D f)) (sigma D (fun x => abs (f x))).
  Proof.
    set (P := fun x => zero <= f x).
    assert (P_dec : forall x, D x -> P x \/ ~ P x).
    { intros x _. destruct (le_dec zero (f x)); auto. }

    rewrite (sigma_split D P f P_dec).
    set (I_pos := sigma (fun x => D x /\ P x) f).
    set (I_neg := sigma (fun x => D x /\ ~ P x) f).

    apply (le_trans _ (abs I_pos + abs I_neg)).
    - apply abs_triangle.
    - assert (Hpos_nonneg : zero <= I_pos).
      { apply sigma_nonneg; intros x [HD HP]; exact HP. }
      assert (Hpos_eq : abs I_pos = sigma (fun x => D x /\ P x) (fun x => abs (f x))).
      { rewrite abs_pos; [|exact Hpos_nonneg].
        apply sigma_congr; intros x [HD HP].
        symmetry; apply abs_pos; exact HP. }

      assert (Hfx_le0 : forall x, D x /\ ~ P x -> f x <= zero).
      { intros x [HD HnP]; unfold P in HnP.
        destruct (le_total zero (f x)) as [H3|H3]; [contradiction|exact H3]. }

      assert (Hneg_nonpos : sigma (fun x => D x /\ ~P x) f <= zero).
      { apply (le_trans _ (sigma (fun x => D x /\ ~P x) (fun _ => zero))).
        - apply sigma_le; intros x Hx; apply Hfx_le0; exact Hx.
        - rewrite sigma_zero; apply le_refl. }

      assert (Hneg_eq : abs I_neg = sigma (fun x => D x /\ ~P x) (fun x => abs (f x))).
      { rewrite abs_neg; [|exact Hneg_nonpos].
        unfold I_neg.
        rewrite <- integral_neg.
        apply sigma_congr; intros x Hx.
        symmetry; apply abs_neg; apply Hfx_le0; exact Hx. }

      rewrite Hpos_eq, Hneg_eq.
      rewrite (sigma_split D P (fun x => abs (f x)) P_dec).
      apply le_refl.
  Qed.


End Integrals.
