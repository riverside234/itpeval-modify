Class AbsField := {
  R0   : Type;
  zero : R0;
  one  : R0;
  add  : R0 -> R0 -> R0;
  mul  : R0 -> R0 -> R0;
  opp  : R0 -> R0;
  abs  : R0 -> R0;
  leR  : R0 -> R0 -> Prop;
  ltR  : R0 -> R0 -> Prop;


  N0       : Type;
  Nle      : N0 -> N0 -> Prop;
  Nmax     : N0 -> N0 -> N0;
  Nle_max_l : forall x y, Nle x (Nmax x y);
  Nle_max_r : forall x y, Nle y (Nmax x y);

  add_comm  : forall x y, add x y = add y x;
  add_assoc : forall x y z, add (add x y) z = add x (add y z);
  add_zero  : forall x, add x zero = x;
  add_opp   : forall x, add x (opp x) = zero;
  mul_comm  : forall x y, mul x y = mul y x;
  mul_assoc : forall x y z, mul (mul x y) z = mul x (mul y z);
  mul_one   : forall x, mul x one = x;

  le_refl   : forall x, leR x x;
  le_trans  : forall x y z, leR x y -> leR y z -> leR x z;
  add_le_add : forall a b c d, leR a b -> leR c d -> leR (add a c) (add b d);

  abs_nonneg : forall x, leR zero (abs x);
  abs_triangle : forall x y, leR (abs (add x y)) (add (abs x) (abs y));
  abs_opp : forall x, abs (opp x) = abs x;
  abs_sub_symm : forall x y, abs (add x (opp y)) = abs (add y (opp x));
  sub_decomp : forall x y z, add x (opp z) = add (add x (opp y)) (add y (opp z));
  sub_eq_zero : forall x y, add x (opp y) = zero -> x = y;


  eq_of_forall_eps2 : forall x, (forall eps, ltR zero eps -> leR (abs x) (add eps eps)) -> x = zero
}.

Section Limits.
  Context {A : AbsField}.

  Infix "+R" := add (at level 65).
  Notation "-R x" := (opp x) (at level 100).

  Definition sub (x y : R0) : R0 := add x (opp y).

  Definition limit (u : N0 -> R0) (l : R0) : Prop :=
    forall eps, ltR zero eps -> exists N, forall n, Nle N n -> leR (abs (sub (u n) l)) eps.

  Lemma abs_sub_triangle (x y z : R0) :
    leR (abs (sub x z)) (add (abs (sub x y)) (abs (sub y z))).
  Proof.
    unfold sub.
    rewrite (sub_decomp x y z).
    apply abs_triangle.
  Qed.

  Theorem limit_unique (u : N0 -> R0) (l m : R0) :
    limit u l -> limit u m -> l = m.
  Proof.
    intros Hl Hm.
    assert (Hbound: forall eps, ltR zero eps -> leR (abs (sub l m)) (add eps eps)).
    { intros eps Heps.
      destruct (Hl eps Heps) as [N1 HN1].
      destruct (Hm eps Heps) as [N2 HN2].
      set (N := Nmax N1 N2).
      assert (H1u: leR (abs (sub (u N) l)) eps).
      { apply HN1. apply Nle_max_l. }
      assert (H1: leR (abs (sub l (u N))) eps).
      { unfold sub in H1u. rewrite abs_sub_symm in H1u. fold sub in H1u. exact H1u. }
      assert (H2: leR (abs (sub (u N) m)) eps).
      { apply HN2. apply Nle_max_r. }
      assert (Htri: leR (abs (sub l m)) (add (abs (sub l (u N))) (abs (sub (u N) m)))) by apply abs_sub_triangle.
      eapply le_trans; [exact Htri|].
      apply add_le_add; [exact H1|exact H2].
    }
    assert (Hz: sub l m = zero).
    { apply eq_of_forall_eps2. exact Hbound. }
    unfold sub in Hz.
    now apply sub_eq_zero in Hz.
  Qed.

End Limits.
