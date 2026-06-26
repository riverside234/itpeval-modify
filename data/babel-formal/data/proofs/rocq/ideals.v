(*
  ideals.v — Self-contained commutative ring ideals (Coq)

  We axiomatize a commutative ring R and define ideals as predicates
  closed under 0, addition, additive inverse, and left-multiplication.
  We prove: intersection of a family of ideals is an ideal; sum of two
  ideals is an ideal.
*)

Require Import Coq.Init.Logic.

Class CRing := {
  R     : Type;
  zero  : R;
  one   : R;
  add   : R -> R -> R;
  mul   : R -> R -> R;
  opp   : R -> R;

  add_comm  : forall x y, add x y = add y x;
  add_assoc : forall x y z, add (add x y) z = add x (add y z);
  add_zero  : forall x, add x zero = x;
  zero_add  : forall x, add zero x = x;
  add_opp   : forall x, add x (opp x) = zero;

  mul_comm  : forall x y, mul x y = mul y x;
  mul_assoc : forall x y z, mul (mul x y) z = mul x (mul y z);
  mul_one   : forall x, mul x one = x;
  dist_l    : forall a x y, mul a (add x y) = add (mul a x) (mul a y);
  opp_add   : forall x y, opp (add x y) = add (opp x) (opp y)
}.

Section Ideals.
  Context {K : CRing}.

  Infix "+R" := add (at level 65).
  Infix "*R" := mul (at level 70).
  Notation "-R x" := (opp x) (at level 100).

  Record IsIdeal (I : R -> Prop) : Prop := {
    ideal_zero : I zero;
    ideal_add  : forall x y, I x -> I y -> I (x +R y);
    ideal_opp  : forall x, I x -> I (-R x);
    ideal_mul  : forall a x, I x -> I (a *R x)
  }.

  (* Intersection of a family of ideals *)
  Definition Inter {I : Type} (F : I -> R -> Prop) : R -> Prop :=
    fun x => forall i, F i x.

  Lemma inter_isIdeal {I : Type} (F : I -> R -> Prop)
    (h : forall i, IsIdeal (F i)) : IsIdeal (Inter F).
  Proof.
    constructor; unfold Inter.
    - intro i; exact (ideal_zero (F i) (h i)).
    - intros x y hx hy i; exact (ideal_add (F i) (h i) x y (hx i) (hy i)).
    - intros x hx i; exact (ideal_opp (F i) (h i) x (hx i)).
    - intros a x hx i; exact (ideal_mul (F i) (h i) a x (hx i)).
  Qed.

  (* Sum of two ideals *)
  Definition sum (I J : R -> Prop) : R -> Prop :=
    fun x => exists a b, I a /\ J b /\ (a +R b) = x.

  Lemma sum_isIdeal (I J : R -> Prop)
    (hI : IsIdeal I) (hJ : IsIdeal J) : IsIdeal (sum I J).
  Proof.
    unfold sum.
    constructor.
    - exists zero, zero; repeat split.
      + exact (ideal_zero I hI).
      + exact (ideal_zero J hJ).
      + rewrite add_zero. reflexivity.
    - intros x y [a [b [Ha [Hb Hx]]]] [a' [b' [Ha' [Hb' Hy]]]].
      subst x; subst y.
      assert (Hreassoc : (a +R b) +R (a' +R b') = (a +R a') +R (b +R b')).
      { rewrite add_assoc.
        rewrite <- add_assoc with (x:=b) (y:=a') (z:=b').
        rewrite add_comm with (x:=b) (y:=a').
        rewrite add_assoc.
        rewrite <- add_assoc with (x:=a) (y:=a') (z:=(b +R b')).
        reflexivity. }
      pose proof (ideal_add I hI a a' Ha Ha') as HA.
      pose proof (ideal_add J hJ b b' Hb Hb') as HB.
      exists (a +R a'), (b +R b'); repeat split; try tauto.
      now rewrite <- Hreassoc.
    - intros x [a [b [Ha [Hb Hx]]]]; subst x.
      pose proof (ideal_opp I hI a Ha) as Ha'.
      pose proof (ideal_opp J hJ b Hb) as Hb'.
      exists (-R a), (-R b). repeat split; try tauto.
      now rewrite opp_add.
    - intros c x [a [b [Ha [Hb Hx]]]]; subst x.
      rewrite dist_l.
      pose proof (ideal_mul I hI c a Ha) as Ha'.
      pose proof (ideal_mul J hJ c b Hb) as Hb'.
      now exists (c *R a), (c *R b).
  Qed.

End Ideals.
