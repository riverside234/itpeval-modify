Class Group (G : Type) := {
  inv : G -> G;
  one : G;
  mul : G -> G -> G;
  mul_assoc : forall a b c, mul a (mul b  c) = mul (mul a b) c;
  mul_one   : forall a, mul a one = a;
  one_mul   : forall a, mul one a = a;
  mul_inv_l : forall a, mul (inv a) a = one;
  mul_inv_r : forall a, mul a (inv a) = one
}.

Infix "*" := mul (at level 40, left associativity).
Notation "1" := one.
Notation "x ^-1" := (inv x) (at level 35, right associativity).


Class GroupComm   (G : Type) `{Group G} := {
  mul_comm : forall a b, a * b = b * a
}.

Section MulRotate.
  Variable G : Type.
  Context `{GroupComm G}.

  Lemma mul_rotate' (a b c : G) : a * (b * c) = b * (c * a).
  Proof.
    rewrite mul_comm.
    rewrite <- mul_assoc.
    trivial.
  Qed.
End MulRotate.

Section GroupLemmas.
  Context {G : Type} `{Group G}.

  Lemma mul_left_cancel (a b c : G) :
        a * b = a * c -> b = c.
  Proof.
    intro Ha.
    assert (H' : a^-1 * (a * b) = a^-1 * (a * c)).
    { now rewrite Ha. }

    repeat rewrite mul_assoc in H'.
    repeat rewrite mul_inv_l in H'.
    repeat rewrite one_mul    in H'.
    exact H'.
  Qed.

  Lemma mul_right_cancel (a b c : G) :
        b * a = c * a -> b = c.
  Proof.
    intro Ha.
    assert (H' : (b * a) * a^-1 = (c * a) * a^-1).
    { now rewrite Ha. }
    repeat rewrite <- mul_assoc in H'.
    repeat rewrite mul_inv_r in H'.
    repeat rewrite mul_one in H'.
    exact H'.
  Qed.

  Lemma inv_inv (a : G) : (a^-1)^-1 = a.
  Proof.
    assert (Ha : (a^-1)^-1 * a^-1 = a * a^-1).
    { now rewrite mul_inv_l, mul_inv_r. }
    apply mul_right_cancel in Ha.
    exact Ha.
  Qed.

  Lemma inv_mul (a b : G) :
        (a * b)^-1 = b^-1 * a^-1.
  Proof.
    assert (Ha : (a * b)^-1 * (a * b) = (b^-1 * a^-1) * (a * b)).
    { rewrite mul_inv_l.
      repeat rewrite <- mul_assoc.
      rewrite (mul_assoc (inv a) a b).
      rewrite mul_inv_l.
      rewrite one_mul.
      rewrite mul_inv_l.
      reflexivity.
    }
    apply mul_right_cancel in Ha.
    exact Ha.
  Qed.

  Lemma inv_eq_of_mul_eq_one (a b : G) :
        a * b = 1 -> b = a^-1.
  Proof.
    intro Ha.
    assert (H' : a^-1 * (a * b) = a^-1 * 1).
    { now rewrite Ha. }
    rewrite mul_assoc in H'.
    rewrite mul_inv_l in H'.
    rewrite one_mul  in H'.
    rewrite mul_one  in H'.
    exact H'.
  Qed.

End GroupLemmas.

Class Act (G X : Type) `{Group G}:= 
{
  act : G -> X -> X;
  act_one : forall x, act 1 x = x;
  act_mul : forall g h x, act (g * h) x = act g  (act h x)

}.
Infix "•" := act (at level 50, left associativity).


Section ActionLemmas.
  Context {G X : Type} `{Act G X}.

  Lemma act_inv (g : G) (x : X) :
        g^-1 • (g • x) = x.
  Proof.
    assert (Ha : (g^-1 * g) • x = x).
    { rewrite mul_inv_l.
      apply act_one.
    }
    rewrite act_mul in Ha.
    exact Ha.
  Qed.

  Lemma act_inv_r (g : G) (x : X) :
        g • (g^-1 • x) = x.
  Proof.
    assert (Ha : (g * g^-1) • x = x).
    { rewrite mul_inv_r.
      apply act_one.
    }
    rewrite act_mul in Ha.
    exact Ha.
  Qed.

  Definition orbit (x : X) : X -> Prop :=
    fun y => exists g : G, g • x = y.

  Definition stabilizer (x : X) : G -> Prop :=
    fun g => g • x = x.

  Lemma orbit_refl (x : X) : orbit x x.
  Proof.
    exists 1.
    apply act_one.
  Qed.

  Lemma orbit_sym (x y : X) :
        orbit x y -> orbit y x.
  Proof.
    intros [g Hg].
    exists (g^-1).
    rewrite <- Hg.
    rewrite <- act_mul.
    rewrite mul_inv_l.
    apply act_one.
  Qed.

  Lemma orbit_trans (x y z : X) :
        orbit x y -> orbit y z -> orbit x z.
  Proof.
    intros [g1 Hg1] [g2 Hg2].
    exists (g2 * g1).
    rewrite act_mul.
    rewrite Hg1, Hg2.
    reflexivity.
  Qed.

  Lemma orbit_partition (x y : X) :
        orbit x y -> forall z, orbit x z <-> orbit y z.
  Proof.
    intros Hxy z.
    split; intros Hz.
    - destruct Hxy as [g1 Hg1].
      destruct Hz as [g2 Hg2].
      exists (g2 * g1^-1).
      rewrite act_mul.
      rewrite <- Hg1.
      repeat rewrite <- act_mul.
      rewrite <- mul_assoc.
      rewrite mul_inv_l.
      rewrite mul_one.
      exact Hg2.
    - destruct Hxy as [g1 Hg1].
      destruct Hz as [g2 Hg2].
      exists (g2 * g1).
      rewrite act_mul.
      rewrite Hg1.
      exact Hg2.
  Qed.

  Lemma stabilizer_mul (x : X) (g h : G) :
        stabilizer x g -> stabilizer x h -> stabilizer x (g * h).
  Proof.
    intros Hg Hh.
    unfold stabilizer in *.
    rewrite act_mul.
    rewrite Hh, Hg.
    reflexivity.
  Qed.

  Lemma stabilizer_inv (x : X) (g : G) :
        stabilizer x g -> stabilizer x (g^-1).
  Proof.
    intro Hg.
    unfold stabilizer in *.
    apply (f_equal (fun y => g^-1 • y)) in Hg.
    rewrite <- act_mul in Hg.
    rewrite mul_inv_l in Hg.
    rewrite act_one in Hg.
    symmetry.
    exact Hg.
  Qed.

  Lemma stabilizer_one (x : X) :
        stabilizer x 1.
  Proof.
    unfold stabilizer.
    apply act_one.
  Qed.

  Lemma stabilizer_conjugate (x : X) (g h : G) :
        stabilizer x h -> stabilizer (g • x) (g * h * g^-1).
  Proof.
    intro Hh.
    unfold stabilizer in *.
    rewrite <- act_mul.
    rewrite <- mul_assoc.
    rewrite mul_inv_l.
    rewrite mul_one.
    rewrite act_mul.
    rewrite Hh.
    reflexivity.
  Qed.

  Lemma stabilizer_conjugate_orbit (x y : X) (g : G) :
        g • x = y ->
        forall h, stabilizer y h <-> stabilizer x (g^-1 * h * g).
  Proof.
    intro Hxy.
    intro h.
    unfold stabilizer.
    split; intro Hh.
    - rewrite <- Hxy in Hh.
      rewrite <- mul_assoc.
      rewrite act_mul.
      rewrite act_mul.
      rewrite Hh.
      rewrite act_inv.
      reflexivity.
    - rewrite <- mul_assoc in Hh.
      repeat rewrite act_mul in Hh.
      apply (f_equal (fun y0 => g • y0)) in Hh.
      repeat rewrite Hxy in Hh.
      rewrite <- act_mul in Hh.
      rewrite mul_inv_r in Hh.
      rewrite <- act_mul in Hh.
      rewrite one_mul in Hh.
      assumption.
  Qed.

End ActionLemmas.
