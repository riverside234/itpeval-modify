Inductive mynat : Type :=
| O : mynat
| S : mynat -> mynat.

Fixpoint mynat_add (n m : mynat) : mynat :=
  match n with
  | O    => m
  | S n' => S (mynat_add n' m)
  end.

Inductive mynat_le : mynat -> mynat -> Prop :=
| le_n : forall n,            mynat_le n n
| le_S : forall n m, mynat_le n m -> mynat_le n (S m).

Lemma mynat_zero_le (n : mynat) : mynat_le O n.
Proof.
  induction n as [|n IH].
  - apply le_n.
  - apply le_S, IH.
Qed.

Lemma mynat_add_zero_r : forall n, mynat_add n O = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - now rewrite IHn.
Qed.

Lemma mynat_succ_le_succ (n m : mynat) :
  mynat_le n m -> mynat_le (S n) (S m).
Proof.
  induction 1.
  - apply le_n.
  - apply le_S, IHmynat_le.
Qed.

Lemma mynat_add_S_r : forall m n,
  mynat_add m (S n) = S (mynat_add m n).
Proof.
  intros m n.
  induction m as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma mynat_add_comm : forall n m, mynat_add n m = mynat_add m n.
Proof.
  induction n as [|n IH]; intros m; simpl.
  - rewrite mynat_add_zero_r.
    reflexivity.
  - rewrite IH.
    rewrite mynat_add_S_r.
    reflexivity.
Qed.

Inductive mylist (A : Type) : Type :=
| nilL  : mylist A
| consL : A -> mylist A -> mylist A.

Arguments nilL  {A}.
Arguments consL {A} _ _.
Infix "::L" := consL (at level 60, right associativity).

Inductive InL {A : Type} (x : A) : mylist A -> Prop :=
| In_head : forall xs,      InL x (x ::L xs)
| In_tail : forall y xs, InL x xs -> InL x (y ::L xs).

Inductive NoDupL {A : Type} : mylist A -> Prop :=
| ND_nil  : NoDupL nilL
| ND_cons : forall x xs, (~ InL x xs) -> NoDupL xs -> NoDupL (x ::L xs).

Fixpoint lengthL {A : Type} (xs : mylist A) : mynat :=
  match xs with
  | nilL      => O
  | _ ::L tl  => S (lengthL tl)
  end.

Class ring (R : Type) := {
  zero      : R;
  opp       : R -> R;
  one       : R;
  add       : R -> R -> R;
  mul       : R -> R -> R;

  one_neq_zero  : one <> zero;

  add_comm  : forall x y,    add x y = add y x;
  add_assoc : forall x y z,  add (add x y) z = add x (add y z);
  add_zero  : forall x,      add x zero = x;
  add_opp   : forall x,      add x (opp x) = zero;

  mul_comm  : forall x y,    mul x y = mul y x;
  mul_assoc : forall x y z,  mul (mul x y) z = mul x (mul y z);
  mul_one   : forall x,      mul x one = x;
  dist_l    : forall x y z,  mul x (add y z) = add (mul x y) (mul x z);
  mul_zero  : forall x,      mul x zero = zero;
  
  no_zero_div :
    forall x y, mul x y = zero -> x = zero \/ y = zero
}.

Notation "x +R y" := (add x y) (at level 50, left associativity).
Notation "-R x"    := (opp x)    (at level 35).
Notation "x -R y"  := (add x (opp y)) (at level 55).
Notation "x *R y"  := (mul x y)  (at level 40).

Section Polynomial.
  Context {R : Type} `{ring R}.

  Context {polynomial : Type} `{ring polynomial}.

  Variable degree    : polynomial -> mynat.
  Variable monomial  : mynat -> R -> polynomial.

  Variable eval : polynomial -> R -> R.

  Definition X          : polynomial := monomial (S O) one.
  Definition C (c:R)    : polynomial := monomial O c.
  Definition X_minus (a:R) : polynomial := X +R C (-R a).

  Axiom C_zero : C zero = zero.
  Axiom C_one         : C one = one.

  Axiom deg_zero      : degree zero = O.

  Axiom eval_add     : forall p q x,     eval (p +R q) x = eval p x +R eval q x.
  Axiom eval_mul     : forall p q x,     eval (p *R q) x = eval p x *R eval q x.
  Axiom eval_C       : forall c x,       eval (C c) x   = c.
  Axiom eval_X       : forall x,         eval X x       = x.

  Axiom deg_C        : forall c, c <> zero -> degree (C c) = O.
  Axiom deg_constant : forall p, degree p = O <-> exists c, p = C c.
  Axiom deg_X_minus  : forall a,         degree (X_minus a) = S O.
  Axiom deg_mul      : forall p q,
    p <> zero -> q <> zero ->
    degree (p *R q) = mynat_add (degree p) (degree q).

   Axiom euclid_X_minus :
    forall p a, exists q r,
      p = q *R X_minus a +R r
      /\ degree r = O.

  
  Lemma sub_eq_zero_l `{ring R} : forall a b, a -R b = zero -> a = b.
  Proof.
    intros a b H2.
    assert (H': (a +R opp b) +R b = zero +R b).
    {
      rewrite H2.
      reflexivity.
    }
    rewrite add_assoc in H'.
    rewrite add_comm with (x:=opp b) (y:=b) in H'.
    rewrite add_opp in H'.
    rewrite add_zero in H'.
    rewrite add_comm, add_zero in H'.
    exact H'.
  Qed.

  Lemma root_factor :
    forall p a, eval p a = zero ->
      exists q, p = q *R X_minus a.
  Proof.
    intros p a Hp.
    destruct (euclid_X_minus p a) as (q & r & Heq & Hdr).

    assert (eval r a = zero).
    {
      rewrite Heq in Hp.
      rewrite (eval_add (q *R X_minus a) r a) in Hp.
      rewrite (eval_mul q (X_minus a) a)      in Hp.
      unfold X_minus in Hp.
      rewrite (eval_add X (C (-R a)) a)        in Hp.
      rewrite (eval_X a)                      in Hp.
      rewrite (eval_C (-R a) a)               in Hp.
      rewrite add_opp     in Hp.
      rewrite mul_zero    in Hp.
      rewrite add_comm, add_zero in Hp.
      assumption.
    }
    destruct (proj1 (deg_constant r) Hdr) as (c & Hr_eq).
    subst r.
    rewrite eval_C in H1.
    subst c.
    rewrite C_zero in Heq.
    rewrite add_zero in Heq.
    now exists q.
  Qed.

  Lemma root_transfer :
    forall p q a b,
      p = q *R X_minus a ->
      b <> a ->
      eval p b = zero ->
      eval q b = zero.
  Proof.
    intros p q a b Hp Hba Hb.
    rewrite Hp in Hb.
    rewrite eval_mul in Hb.
    unfold X_minus in Hb.
    rewrite !eval_add, eval_X, eval_C in Hb.
    apply no_zero_div in Hb.
    destruct Hb as [Hq | Hba'].
    - exact Hq.
    - apply sub_eq_zero_l in Hba'.
      congruence.
  Qed.

  Definition root (a:R) (p:polynomial) : Prop := eval p a = zero.

  Theorem roots_le_degree :
    forall p (xs:mylist R),
      NoDupL xs ->
      (forall a, InL a xs -> root a p) ->
      p <> zero ->
      mynat_le (lengthL xs) (degree p).
  Proof.
    intros p xs Hnd Hrt Hnz.
    revert p Hrt Hnz.
    induction xs as [|a xs IH]; intros p Hrt Hnz.
    - simpl. apply mynat_zero_le.
    - simpl in *. 
      assert (Ha : root a p) by (apply Hrt; constructor).
      destruct (root_factor p a Ha) as [q Hpq].
      inversion Hnd as [| x0 xs0 Hnotin Hnd_xs]; subst x0 xs0; clear Hnd.
      assert (q <> zero) as qnz.
      { 
        intro G.
        rewrite G in Hpq.
        rewrite mul_comm in Hpq.
        rewrite mul_zero in Hpq.
        exact (Hnz Hpq).
      }
      assert (X_minus a <> zero) as xnz.
      { 
        intro G.
        rewrite G in Hpq.
        rewrite mul_zero in Hpq.
        exact (Hnz Hpq).
      }
      assert (Hdeg : degree p = S (degree q)).
      { 
        rewrite Hpq.
        rewrite (deg_mul q (X_minus a) qnz xnz).
        rewrite deg_X_minus.
        rewrite mynat_add_comm.
        reflexivity. 
      }
      rewrite Hdeg.
      apply mynat_succ_le_succ.
      assert (Hf : forall b, InL b xs -> root b q).
      { 
        intros b Hb.
        apply (root_transfer p q a b Hpq).
        - intro Heq; subst b; apply Hnotin; assumption.
        - apply Hrt; constructor 2; assumption.
      }
      apply IH; auto.

  Qed.

  Fixpoint poly_of_roots (xs : mylist R) : polynomial :=
  match xs with
  | nilL        => one
  | consL a xs' => X_minus a *R poly_of_roots xs'
  end.

  Lemma X_minus_nonzero : forall a, X_minus a <> zero.
  Proof.
    intros a Ha.
    specialize (deg_X_minus a) as Hdeg.
    rewrite Ha in Hdeg.
    rewrite deg_zero in Hdeg.
    discriminate Hdeg.
  Qed.

  Lemma constant_root_zero :
    forall p a, degree p = O -> root a p -> p = zero.
  Proof.
    intros p a Hdeg Hroot.
    destruct (proj1 (deg_constant p) Hdeg) as [c Hpc].
    subst p.
    unfold root in Hroot; rewrite eval_C in Hroot.
    subst c.
    rewrite C_zero; reflexivity.
  Qed.

  Lemma root_of_product :
    forall p q a, root a (p *R q) -> root a p \/ root a q.
  Proof.
    intros p q a Hpq.
    unfold root in *; rewrite eval_mul in Hpq.
    apply no_zero_div in Hpq; tauto.
  Qed.

  Lemma root_scale_constant :
    forall p c a, c <> zero -> (root a p <-> root a (C c *R p)).
  Proof.
    intros p c a Hc.
    split.
    - intros Hp; unfold root in *.
      rewrite eval_mul, eval_C, Hp, mul_zero; reflexivity.
    - intros Hcp; unfold root in *.
      rewrite eval_mul, eval_C in Hcp.
      apply no_zero_div in Hcp; tauto.
  Qed.

  Lemma poly_of_roots_nonzero : forall xs, poly_of_roots xs <> zero.
  Proof.
    induction xs as [|a xs IH]; simpl.
    - exact one_neq_zero.
    - intro Ha; apply no_zero_div in Ha; destruct Ha as [Ha|Ha]; 
        [apply X_minus_nonzero in Ha | apply IH in Ha]; contradiction.
  Qed.

  Lemma deg_poly_of_roots :
    forall xs, degree (poly_of_roots xs) = lengthL xs.
  Proof.
    induction xs as [|a xs IH]; simpl.
    - rewrite <- C_one, deg_C; [reflexivity|exact one_neq_zero].
    - pose proof (X_minus_nonzero a) as Hx.
      pose proof (poly_of_roots_nonzero xs) as Hp.
      rewrite deg_mul; try assumption.
      rewrite deg_X_minus, IH.
      rewrite mynat_add_comm.
      rewrite mynat_add_S_r, mynat_add_zero_r.
      reflexivity.
  Qed.


  Lemma root_factor_list :
  forall p xs,
    NoDupL xs ->
    (forall a, InL a xs -> root a p) ->
    exists q, p = q *R poly_of_roots xs.
  Proof.
    intros p xs.
    induction xs as [| a xs IH] in p |- *.
    - exists p; simpl; rewrite mul_one; reflexivity.
    - intros Hnd Hroots.
    inversion Hnd as [| a' xs' Hnotin Hnd']; subst a' xs'.
    assert (Ha : InL a (a ::L xs)) by constructor.
    pose proof (Hroots a Ha) as Hroot_pa.
    destruct (root_factor p a Hroot_pa) as [q Hpq].
    assert (Hroots_q : forall b, InL b xs -> root b q).
    {
      intros b Hb.
      assert (Hba : b <> a) by (intro E; subst b; apply Hnotin; assumption).
      pose proof (Hroots b (In_tail b a xs Hb)) as Hroot_b.
      eapply root_transfer; eauto.
    }
    destruct (IH q Hnd' Hroots_q) as [q0 Hq0].
    exists q0.
    simpl. rewrite Hpq. rewrite Hq0. rewrite mul_assoc.
    rewrite (mul_comm (poly_of_roots xs) (X_minus a)).
    reflexivity.
  Qed.

  Lemma degree_factorisation :
    forall p xs q,
      p = q *R poly_of_roots xs ->
      q <> zero ->
      degree p = mynat_add (degree q) (lengthL xs).
  Proof.
    intros p xs q Hp Hq.
    rewrite Hp.
    rewrite deg_mul; try assumption; try apply poly_of_roots_nonzero.
    rewrite deg_poly_of_roots. reflexivity.
  Qed.

End Polynomial.
