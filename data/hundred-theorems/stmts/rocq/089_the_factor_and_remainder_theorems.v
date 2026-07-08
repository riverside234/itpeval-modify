(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop nmodule algebra divalg decfield poly.

(******************************************************************************)
(* This file provides a library for the basic theory of Euclidean and pseudo- *)
(* Euclidean division for polynomials over non trivial ring structures.       *)
(* The library defines two versions of the pseudo-euclidean division: one for *)
(* coefficients in a (not necessarily commutative) non-trivial ring structure *)
(* and one for coefficients equipped with a structure of integral domain.     *)
(* From the latter we derive the definition of the usual Euclidean division   *)
(* for coefficients in a field. Only the definition of the pseudo-division    *)
(* for coefficients in an integral domain is exported by default and benefits *)
(* from notations.                                                            *)
(* Also, the only theory exported by default is the one of division for       *)
(* polynomials with coefficients in a field.                                  *)
(* Other definitions and facts are qualified using name spaces indicating the *)
(* hypotheses made on the structure of coefficients and the properties of the *)
(* polynomial one divides with.                                               *)
(*                                                                            *)
(* Pdiv.Field (exported by the present library):                              *)
(*          edivp p q == pseudo-division of p by q with p q : {poly R} where  *)
(*                       R is an idomainType.                                 *)
(*                       Computes (k, quo, rem) : nat * {poly r} * {poly R},  *)
(*                       such that size rem < size q and:                     *)
(*                       + if lead_coef q is not a unit, then:                *)
(*                         (lead_coef q ^+ k) *: p = q * quo + rem            *)
(*                       + else if lead_coef q is a unit, then:               *)
(*                         p = q * quo + rem and k = 0                        *)
(*             p %/ q == quotient (second component) computed by (edivp p q). *)
(*             p %% q == remainder (third component) computed by (edivp p q). *)
(*          scalp p q == exponent (first component) computed by (edivp p q).  *)
(*             p %| q == tests the nullity of the remainder of the            *)
(*                       pseudo-division of p by q.                           *)
(*         rgcdp p q  == Pseudo-greater common divisor obtained by performing *)
(*                       the Euclidean algorithm on p and q using redivp as   *)
(*                       Euclidean division.                                  *)
(*             p %= q == p and q are associate polynomials, i.e., p %| q and  *)
(*                       q %| p, or equivalently, p = c *: q for some nonzero *)
(*                       constant c.                                          *)
(*           gcdp p q == Pseudo-greater common divisor obtained by performing *)
(*                       the Euclidean algorithm on p and q using  edivp as   *)
(*                       Euclidean division.                                  *)
(*          egcdp p q == The pair of Bezout coefficients: if e := egcdp p q,  *)
(*                       then size e.1 <= size q, size e.2 <= size p, and     *)
(*                       gcdp p q %= e.1 * p + e.2 * q                        *)
(*       coprimep p q == p and q are coprime, i.e., (gcdp p q) is a nonzero   *)
(*                       constant.                                            *)
(*          gdcop q p == greatest divisor of p which is coprime to q.         *)
(* irreducible_poly p <-> p has only trivial (constant) divisors.             *)
(*            mup x q == multplicity of x as a root of q                      *)
(*                                                                            *)
(* Pdiv.Idomain: theory available for edivp and the related operation under   *)
(*    the sole assumption that the ring of coefficients is canonically an     *)
(*    integral domain (R : idomainType).                                      *)
(*                                                                            *)
(* Pdiv.IdomainMonic:  theory available for edivp and the related operations  *)
(*    under the assumption that the ring of coefficients is canonically       *)
(*    and integral domain (R : idomainType) an the divisor is monic.          *)
(*                                                                            *)
(* Pdiv.IdomainUnit: theory available for edivp and the related operations    *)
(*    under the assumption that the ring of coefficients is canonically an    *)
(*    integral domain (R : idomainType) and the leading coefficient of the    *)
(*    divisor is a unit.                                                      *)
(*                                                                            *)
(* Pdiv.ClosedField: theory available for edivp and the related operation     *)
(*    under the sole assumption that the ring of coefficients is canonically  *)
(*    an algebraically closed field (R : closedField).                        *)
(*                                                                            *)
(*  Pdiv.Ring :                                                               *)
(*   redivp p q == pseudo-division of p by q with p q : {poly R} where R is   *)
(*                 a nzRingType.                                              *)
(*                 Computes (k, quo, rem) : nat * {poly r} * {poly R},        *)
(*                 such that if rem = 0 then quo * q = p * (lead_coef q ^+ k) *)
(*                                                                            *)
(*   rdivp p q  == quotient (second component) computed by (redivp p q).      *)
(*   rmodp p q  == remainder (third component) computed by (redivp p q).      *)
(*   rscalp p q == exponent (first component) computed by (redivp p q).       *)
(*   rdvdp p q  == tests the nullity of the remainder of the pseudo-division  *)
(*                 of p by q.                                                 *)
(*   rgcdp p q  == analogue of gcdp for coefficients in a nzRingType.         *)
(*   rgdcop p q == analogue of gdcop for coefficients in a nzRingType.        *)
(*rcoprimep p q == analogue of coprimep p q for coefficients in a nzRingType. *)
(*                                                                            *)
(* Pdiv.RingComRreg : theory of the operations defined in Pdiv.Ring, when the *)
(*   ring of coefficients is canonically commutative (R : comNzRingType) and  *)
(*   the leading coefficient of the divisor is both right regular and         *)
(*   commutes as a constant polynomial with the divisor itself                *)
(*                                                                            *)
(* Pdiv.RingMonic : theory of the operations defined in Pdiv.Ring, under the  *)
(*   assumption that the divisor is monic.                                    *)
(*                                                                            *)
(* Pdiv.UnitRing: theory of the operations defined in Pdiv.Ring, when the     *)
(*   ring R of coefficients is canonically with units (R : unitRingType).     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "p %= q" (at level 70, no associativity).

Local Notation simp := Monoid.simpm.

Module Pdiv.

Module CommonRing.

Section RingPseudoDivision.

Variable R : nzRingType.
Implicit Types d p q r : {poly R}.

(* Pseudo division, defined on an arbitrary ring *)
Definition redivp_rec (q : {poly R}) :=
  let sq := size q in
  let cq := lead_coef q in
   fix loop (k : nat) (qq r : {poly R})(n : nat) {struct n} :=
    if size r < sq then (k, qq, r) else
    let m := (lead_coef r) *: 'X^(size r - sq) in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
       if n is n1.+1 then loop k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

Definition redivp_expanded_def p q :=
   if q == 0 then (0, 0, p) else redivp_rec q 0 0 p (size p).
Fact redivp_key : unit.
Proof.
Admitted.
Definition redivp : {poly R} -> {poly R} -> nat * {poly R} * {poly R} :=
  locked_with redivp_key redivp_expanded_def.
Canonical redivp_unlockable := [unlockable fun redivp].

Definition rdivp p q := ((redivp p q).1).2.
Definition rmodp p q := (redivp p q).2.
Definition rscalp p q := ((redivp p q).1).1.
Definition rdvdp p q := rmodp q p == 0.
(*Definition rmultp := [rel m d | rdvdp d m].*)
Lemma redivp_def p q : redivp p q = (rscalp p q, rdivp p q, rmodp p q).
Proof.
Admitted.

Lemma rdiv0p p : rdivp 0 p = 0.
Proof.
Admitted.

Lemma rdivp0 p : rdivp p 0 = 0.
Proof.
Admitted.

Lemma rdivp_small p q : size p < size q -> rdivp p q = 0.
Proof.
Admitted.

Lemma leq_rdivp p q : size (rdivp p q) <= size p.
Proof.
Admitted.

Lemma rmod0p p : rmodp 0 p = 0.
Proof.
Admitted.

Lemma rmodp0 p : rmodp p 0 = p.
Proof.
Admitted.

Lemma rscalp_small p q : size p < size q -> rscalp p q = 0.
Proof.
Admitted.

Lemma ltn_rmodp p q : (size (rmodp p q) < size q) = (q != 0).
Proof.
Admitted.

Lemma ltn_rmodpN0 p q : q != 0 -> size (rmodp p q) < size q.
Proof.
Admitted.

Lemma rmodp1 p : rmodp p 1 = 0.
Proof.
Admitted.

Lemma rmodp_small p q : size p < size q -> rmodp p q = p.
Proof.
Admitted.

Lemma leq_rmodp m d : size (rmodp m d) <= size m.
Proof.
Admitted.

Lemma rmodpC p c : c != 0 -> rmodp p c%:P = 0.
Proof.
Admitted.

Lemma rdvdp0 d : rdvdp d 0.
Proof.
Admitted.

Lemma rdvd0p n : rdvdp 0 n = (n == 0).
Proof.
Admitted.

Lemma rdvd0pP n : reflect (n = 0) (rdvdp 0 n).
Proof.
Admitted.

Lemma rdvdpN0 p q : rdvdp p q -> q != 0 -> p != 0.
Proof.
Admitted.

Lemma rdvdp1 d : rdvdp d 1 = (size d == 1).
Proof.
Admitted.

Lemma rdvd1p m : rdvdp 1 m.
Proof.
Admitted.

Lemma Nrdvdp_small (n d : {poly R}) :
  n != 0 -> size n < size d -> rdvdp d n = false.
Proof.
Admitted.

Lemma rmodp_eq0P p q : reflect (rmodp p q = 0) (rdvdp q p).
Proof.
Admitted.

Lemma rmodp_eq0 p q : rdvdp q p -> rmodp p q = 0.
Proof.
Admitted.

Lemma rdvdp_leq p q : rdvdp p q -> q != 0 -> size p <= size q.
Proof.
Admitted.

Definition rgcdp p q :=
  let: (p1, q1) := if size p < size q then (q, p) else (p, q) in
  if p1 == 0 then q1 else
  let fix loop (n : nat) (pp qq : {poly R}) {struct n} :=
      let rr := rmodp pp qq in
      if rr == 0 then qq else
      if n is n1.+1 then loop n1 qq rr else rr in
  loop (size p1) p1 q1.

Lemma rgcd0p : left_id 0 rgcdp.
Proof.
Admitted.

Lemma rgcdp0 : right_id 0 rgcdp.
Proof.
Admitted.

Lemma rgcdpE p q :
  rgcdp p q = if size p < size q
    then rgcdp (rmodp q p) p else rgcdp (rmodp p q) q.
Proof.
Admitted.

Variant comm_redivp_spec m d : nat * {poly R} * {poly R} -> Type :=
  ComEdivnSpec k (q r : {poly R}) of
   (GRing.comm d (lead_coef d)%:P -> m * (lead_coef d ^+ k)%:P = q * d + r) &
   (d != 0 -> size r < size d) : comm_redivp_spec m d (k, q, r).

Lemma comm_redivpP m d : comm_redivp_spec m d (redivp m d).
Proof.
Admitted.

Lemma rmodpp p : GRing.
Proof.
Admitted.

Definition rcoprimep (p q : {poly R}) := size (rgcdp p q) == 1.

Fixpoint rgdcop_rec q p n :=
  if n is m.+1 then
      if rcoprimep p q then p
        else rgdcop_rec q (rdivp p (rgcdp p q)) m
    else (q == 0)%:R.

Definition rgdcop q p := rgdcop_rec q p (size p).

Lemma rgdcop0 q : rgdcop q 0 = (q == 0)%:R.
Proof.
Admitted.

End RingPseudoDivision.

End CommonRing.

Module RingComRreg.

Import CommonRing.

Section ComRegDivisor.

Variable R : nzRingType.
Variable d : {poly R}.
Hypothesis Cdl : GRing.comm d (lead_coef d)%:P.
Hypothesis Rreg : GRing.rreg (lead_coef d).

Implicit Types p q r : {poly R}.

Lemma redivp_eq q r :
    size r < size d ->
    let k := (redivp (q * d + r) d).
Proof.
Admitted.

(* this is a bad name *)
Lemma rdivp_eq p :
  p * (lead_coef d ^+ (rscalp p d))%:P = (rdivp p d) * d + (rmodp p d).
Proof.
Admitted.

(* section variables impose an inconvenient order on parameters *)
Lemma eq_rdvdp k q1 p:
  p * ((lead_coef d)^+ k)%:P = q1 * d -> rdvdp d p.
Proof.
Admitted.

Variant rdvdp_spec p q : {poly R} -> bool -> Type :=
  | Rdvdp k q1 & p * ((lead_coef q)^+ k)%:P = q1 * q : rdvdp_spec p q 0 true
  | RdvdpN & rmodp p q != 0 : rdvdp_spec p q (rmodp p q) false.

(* Is that version useable ? *)

Lemma rdvdp_eqP p : rdvdp_spec p d (rmodp p d) (rdvdp d p).
Proof.
Admitted.

Lemma rdvdp_mull p : rdvdp d (p * d).
Proof.
Admitted.

Lemma rmodp_mull p : rmodp (p * d) d = 0.
Proof.
Admitted.

Lemma rmodpp : rmodp d d = 0.
Proof.
Admitted.

Lemma rdivpp : rdivp d d = (lead_coef d ^+ rscalp d d)%:P.
Proof.
Admitted.

Lemma rdvdpp : rdvdp d d.
Proof.
Admitted.

Lemma rdivpK p : rdvdp d p ->
  rdivp p d * d = p * (lead_coef d ^+ rscalp p d)%:P.
Proof.
Admitted.

End ComRegDivisor.

End RingComRreg.

Module RingMonic.

Import CommonRing.

Import RingComRreg.

Section RingMonic.

Variable R : nzRingType.
Implicit Types p q r : {poly R}.

Section MonicDivisor.

Variable d : {poly R}.
Hypothesis mond : d \is monic.

Lemma redivp_eq q r : size r < size d ->
  let k := (redivp (q * d + r) d).
Proof.
Admitted.

Lemma rdivp_eq p : p = rdivp p d * d + rmodp p d.
Proof.
Admitted.

Lemma rdivpp : rdivp d d = 1.
Proof.
Admitted.

Lemma rdivp_addl_mul_small q r : size r < size d -> rdivp (q * d + r) d = q.
Proof.
Admitted.

Lemma rdivp_addl_mul q r : rdivp (q * d + r) d = q + rdivp r d.
Proof.
Admitted.

Lemma rdivpDl q r : rdvdp d q -> rdivp (q + r) d = rdivp q d + rdivp r d.
Proof.
Admitted.

Lemma rdivpDr q r : rdvdp d r -> rdivp (q + r) d = rdivp q d + rdivp r d.
Proof.
Admitted.

Lemma rdivp_mull p : rdivp (p * d) d = p.
Proof.
Admitted.

Lemma rmodp_mull p : rmodp (p * d) d = 0.
Proof.
Admitted.

Lemma rmodpp : rmodp d d = 0.
Proof.
Admitted.

Lemma rmodp_addl_mul_small q r : size r < size d -> rmodp (q * d + r) d = r.
Proof.
Admitted.

Lemma rmodp_id (p : {poly R}) : rmodp (rmodp p d) d = rmodp p d.
Proof.
Admitted.

Lemma rmodpD p q : rmodp (p + q) d = rmodp p d + rmodp q d.
Proof.
Admitted.

Lemma rmodpN p : rmodp (- p) d = - (rmodp p d).
Proof.
Admitted.

Lemma rmodpB p q : rmodp (p - q) d = rmodp p d - rmodp q d.
Proof.
Admitted.

Lemma rmodpZ a p : rmodp (a *: p) d = a *: (rmodp p d).
Proof.
Admitted.

Lemma rmodp_sum (I : Type) (r : seq I) (P : pred I) (F : I -> {poly R}) :
   rmodp (\sum_(i <- r | P i) F i) d = (\sum_(i <- r | P i) (rmodp (F i) d)).
Proof.
Admitted.

Lemma rmodp_mulmr p q : rmodp (p * (rmodp q d)) d = rmodp (p * q) d.
Proof.
Admitted.

Lemma rdvdpp : rdvdp d d.
Proof.
Admitted.

(* section variables impose an inconvenient order on parameters *)
Lemma eq_rdvdp q1 p : p = q1 * d -> rdvdp d p.
Proof.
Admitted.

Lemma rdvdp_mull p : rdvdp d (p * d).
Proof.
Admitted.

Lemma rdvdpP p : reflect (exists qq, p = qq * d) (rdvdp d p).
Proof.
Admitted.

Lemma rdivpK p : rdvdp d p -> (rdivp p d) * d = p.
Proof.
Admitted.

End MonicDivisor.

Lemma drop_poly_rdivp n p : drop_poly n p = rdivp p 'X^n.
Proof.
Admitted.

Lemma take_poly_rmodp n p : take_poly n p = rmodp p 'X^n.
Proof.
Admitted.

End RingMonic.

Section ComRingMonic.

Variable R : comNzRingType.
Implicit Types p q r : {poly R}.
Variable d : {poly R}.
Hypothesis mond : d \is monic.

Lemma rmodp_mulml p q : rmodp (rmodp p d * q) d = rmodp (p * q) d.
Proof.
Admitted.

Lemma rmodpX p n : rmodp ((rmodp p d) ^+ n) d = rmodp (p ^+ n) d.
Proof.
Admitted.

Lemma rmodp_compr p q : rmodp (p \Po (rmodp q d)) d = (rmodp (p \Po q) d).
Proof.
Admitted.

End ComRingMonic.

End RingMonic.

Module Ring.

Include CommonRing.
Import RingMonic.

Section ExtraMonicDivisor.

Variable R : nzRingType.

Implicit Types d p q r : {poly R}.

Lemma rdivp1 p : rdivp p 1 = p.
Proof.
Admitted.

Lemma rdvdp_XsubCl p x : rdvdp ('X - x%:P) p = root p x.
Proof.
Admitted.

Lemma polyXsubCP p x : reflect (p.
Proof.
Admitted.

Lemma root_factor_theorem p x : root p x = (rdvdp ('X - x%:P) p).
Proof.
Admitted.

End ExtraMonicDivisor.

End Ring.

Module ComRing.

Import Ring.

Import RingComRreg.

Section CommutativeRingPseudoDivision.

Variable R : comNzRingType.

Implicit Types d p q m n r : {poly R}.

Variant redivp_spec (m d : {poly R}) : nat * {poly R} * {poly R} -> Type :=
  EdivnSpec k (q r: {poly R}) of
    (lead_coef d ^+ k) *: m = q * d + r &
   (d != 0 -> size r < size d) : redivp_spec m d (k, q, r).

Lemma redivpP m d : redivp_spec m d (redivp m d).
Proof.
Admitted.

Lemma rdivp_eq d p :
  (lead_coef d ^+ rscalp p d) *: p = rdivp p d * d + rmodp p d.
Proof.
Admitted.

Lemma rdvdp_eqP d p : rdvdp_spec p d (rmodp p d) (rdvdp d p).
Proof.
Admitted.

Lemma rdvdp_eq q p :
  rdvdp q p = (lead_coef q ^+ rscalp p q *: p == rdivp p q * q).
Proof.
Admitted.

End CommutativeRingPseudoDivision.

End ComRing.

Module UnitRing.

Import Ring.

Section UnitRingPseudoDivision.

Variable R : unitRingType.
Implicit Type p q r d : {poly R}.

Lemma uniq_roots_rdvdp p rs :
  all (root p) rs -> uniq_roots rs -> rdvdp (\prod_(z <- rs) ('X - z%:P)) p.
Proof.
Admitted.

End UnitRingPseudoDivision.

End UnitRing.

Module IdomainDefs.

Import Ring.

Section IDomainPseudoDivisionDefs.

Variable R : idomainType.
Implicit Type p q r d : {poly R}.

Definition edivp_expanded_def p q :=
  let: (k, d, r) as edvpq := redivp p q in
  if lead_coef q \in GRing.unit then
    (0, (lead_coef q)^-k *: d, (lead_coef q)^-k *: r)
  else edvpq.
Fact edivp_key : unit.
Proof.
Admitted.
Definition edivp := locked_with edivp_key edivp_expanded_def.
Canonical edivp_unlockable := [unlockable fun edivp].

Definition divp p q := ((edivp p q).1).2.
Definition modp p q := (edivp p q).2.
Definition scalp p q := ((edivp p q).1).1.
Definition dvdp p q := modp q p == 0.
Definition eqp p q := (dvdp p q) && (dvdp q p).

End IDomainPseudoDivisionDefs.

Notation "m %/ d" := (divp m d) : ring_scope.
Notation "m %% d" := (modp m d) : ring_scope.
Notation "p %| q" := (dvdp p q) : ring_scope.
Notation "p %= q" := (eqp p q) : ring_scope.
End IdomainDefs.

Module WeakIdomain.

Import Ring ComRing UnitRing IdomainDefs.

Section WeakTheoryForIDomainPseudoDivision.

Variable R : idomainType.
Implicit Type p q r d : {poly R}.

Lemma edivp_def p q : edivp p q = (scalp p q, divp p q, modp p q).
Proof.
Admitted.

Lemma edivp_redivp p q : (lead_coef q \in GRing.
Proof.
Admitted.

Lemma divpE p q :
  p %/ q = if lead_coef q \in GRing.
Proof.
Admitted.

Lemma modpE p q :
  p %% q = if lead_coef q \in GRing.
Proof.
Admitted.

Lemma scalpE p q :
  scalp p q = if lead_coef q \in GRing.
Proof.
Admitted.

Lemma dvdpE p q : (p %| q) = rdvdp p q.
Proof.
Admitted.

Lemma lc_expn_scalp_neq0 p q : lead_coef q ^+ scalp p q != 0.
Proof.
Admitted.

Hint Resolve lc_expn_scalp_neq0 : core.

Variant edivp_spec (m d : {poly R}) :
                                    nat * {poly R} * {poly R} -> bool -> Type :=
|Redivp_spec k (q r: {poly R}) of
  (lead_coef d ^+ k) *: m = q * d + r & lead_coef d \notin GRing.unit &
  (d != 0 -> size r < size d) : edivp_spec m d (k, q, r) false
|Fedivp_spec (q r: {poly R}) of m = q * d + r & (lead_coef d \in GRing.unit) &
  (d != 0 -> size r < size d) : edivp_spec m d (0, q, r) true.

(* There are several ways to state this fact. The most appropriate statement*)
(* might be polished in light of usage. *)
Lemma edivpP m d : edivp_spec m d (edivp m d) (lead_coef d \in GRing.
Proof.
Admitted.

Lemma edivp_eq d q r : size r < size d -> lead_coef d \in GRing.
Proof.
Admitted.

Lemma divp_eq p q : (lead_coef q ^+ scalp p q) *: p = (p %/ q) * q + (p %% q).
Proof.
Admitted.

Lemma dvdp_eq q p : (q %| p) = (lead_coef q ^+ scalp p q *: p == (p %/ q) * q).
Proof.
Admitted.

Lemma divpK d p : d %| p -> p %/ d * d = (lead_coef d ^+ scalp p d) *: p.
Proof.
Admitted.

Lemma divpKC d p : d %| p -> d * (p %/ d) = (lead_coef d ^+ scalp p d) *: p.
Proof.
Admitted.

Lemma dvdpP q p :
  reflect (exists2 cqq, cqq.
Proof.
Admitted.

Lemma mulpK p q : q != 0 -> p * q %/ q = lead_coef q ^+ scalp (p * q) q *: p.
Proof.
Admitted.

Lemma mulKp p q : q != 0 -> q * p %/ q = lead_coef q ^+ scalp (p * q) q *: p.
Proof.
Admitted.

Lemma divpp p : p != 0 -> p %/ p = (lead_coef p ^+ scalp p p)%:P.
Proof.
Admitted.

End WeakTheoryForIDomainPseudoDivision.

#[global] Hint Resolve lc_expn_scalp_neq0 : core.

End WeakIdomain.

Module CommonIdomain.

Import Ring ComRing UnitRing IdomainDefs WeakIdomain.

Section IDomainPseudoDivision.

Variable R : idomainType.
Implicit Type p q r d m n : {poly R}.

Lemma scalp0 p : scalp p 0 = 0.
Proof.
Admitted.

Lemma divp_small p q : size p < size q -> p %/ q = 0.
Proof.
Admitted.

Lemma leq_divp p q : (size (p %/ q) <= size p).
Proof.
Admitted.

Lemma div0p p : 0 %/ p = 0.
Proof.
Admitted.

Lemma divp0 p : p %/ 0 = 0.
Proof.
Admitted.

Lemma divp1 m : m %/ 1 = m.
Proof.
Admitted.

Lemma modp0 p : p %% 0 = p.
Proof.
Admitted.

Lemma mod0p p : 0 %% p = 0.
Proof.
Admitted.

Lemma modp1 p : p %% 1 = 0.
Proof.
Admitted.

Hint Resolve divp0 divp1 mod0p modp0 modp1 : core.

Lemma modp_small p q : size p < size q -> p %% q = p.
Proof.
Admitted.

Lemma modpC p c : c != 0 -> p %% c%:P = 0.
Proof.
Admitted.

Lemma modp_mull p q : (p * q) %% q = 0.
Proof.
Admitted.

Lemma modp_mulr d p : (d * p) %% d = 0.
Proof.
Admitted.

Lemma modpp d : d %% d = 0.
Proof.
Admitted.

Lemma ltn_modp p q : (size (p %% q) < size q) = (q != 0).
Proof.
Admitted.

Lemma ltn_divpl d q p : d != 0 ->
   (size (q %/ d) < size p) = (size q < size (p * d)).
Proof.
Admitted.

Lemma leq_divpr d p q : d != 0 ->
   (size p <= size (q %/ d)) = (size (p * d) <= size q).
Proof.
Admitted.

Lemma divpN0 d p : d != 0 -> (p %/ d != 0) = (size d <= size p).
Proof.
Admitted.

Lemma size_divp p q : q != 0 -> size (p %/ q) = (size p - (size q).
Proof.
Admitted.

Lemma ltn_modpN0 p q : q != 0 -> size (p %% q) < size q.
Proof.
Admitted.

Lemma modp_id p q : (p %% q) %% q = p %% q.
Proof.
Admitted.

Lemma leq_modp m d : size (m %% d) <= size m.
Proof.
Admitted.

Lemma dvdp0 d : d %| 0.
Proof.
Admitted.

Hint Resolve dvdp0 : core.

Lemma dvd0p p : (0 %| p) = (p == 0).
Proof.
Admitted.

Lemma dvd0pP p : reflect (p = 0) (0 %| p).
Proof.
Admitted.

Lemma dvdpN0 p q : p %| q -> q != 0 -> p != 0.
Proof.
Admitted.

Lemma dvdp1 d : (d %| 1) = (size d == 1).
Proof.
Admitted.

Lemma dvd1p m : 1 %| m.
Proof.
Admitted.

Lemma gtNdvdp p q : p != 0 -> size p < size q -> (q %| p) = false.
Proof.
Admitted.

Lemma modp_eq0P p q : reflect (p %% q = 0) (q %| p).
Proof.
Admitted.

Lemma modp_eq0 p q : (q %| p) -> p %% q = 0.
Proof.
Admitted.

Lemma leq_divpl d p q :
  d %| p -> (size (p %/ d) <= size q) = (size p <= size (q * d)).
Proof.
Admitted.

Lemma dvdp_leq p q : q != 0 -> p %| q -> size p <= size q.
Proof.
Admitted.

Lemma eq_dvdp c quo q p : c != 0 -> c *: p = quo * q -> q %| p.
Proof.
Admitted.

Lemma dvdpp d : d %| d.
Proof.
Admitted.

Hint Resolve dvdpp : core.

Lemma divp_dvd p q : p %| q -> (q %/ p) %| q.
Proof.
Admitted.

Lemma dvdp_mull m d n : d %| n -> d %| m * n.
Proof.
Admitted.

Lemma dvdp_mulr n d m : d %| m -> d %| m * n.
Proof.
Admitted.

Hint Resolve dvdp_mull dvdp_mulr : core.

Lemma dvdp_mul d1 d2 m1 m2 : d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
Admitted.

Lemma dvdp_addr m d n : d %| m -> (d %| m + n) = (d %| n).
Proof.
Admitted.

Lemma dvdp_addl n d m : d %| n -> (d %| m + n) = (d %| m).
Proof.
Admitted.

Lemma dvdp_add d m n : d %| m -> d %| n -> d %| m + n.
Proof.
Admitted.

Lemma dvdp_add_eq d m n : d %| m + n -> (d %| m) = (d %| n).
Proof.
Admitted.

Lemma dvdp_subr d m n : d %| m -> (d %| m - n) = (d %| n).
Proof.
Admitted.

Lemma dvdp_subl d m n : d %| n -> (d %| m - n) = (d %| m).
Proof.
Admitted.

Lemma dvdp_sub d m n : d %| m -> d %| n -> d %| m - n.
Proof.
Admitted.

Lemma dvdp_mod d n m : d %| n -> (d %| m) = (d %| m %% n).
Proof.
Admitted.

Lemma dvdp_trans : transitive (@dvdp R).
Proof.
Admitted.

Lemma dvdp_mulIl p q : p %| p * q.
Proof.
Admitted.

Lemma dvdp_mulIr p q : q %| p * q.
Proof.
Admitted.

Lemma dvdp_mul2r r p q : r != 0 -> (p * r %| q * r) = (p %| q).
Proof.
Admitted.

Lemma dvdp_mul2l r p q: r != 0 -> (r * p %| r * q) = (p %| q).
Proof.
Admitted.

Lemma ltn_divpr d p q :
  d %| q -> (size p < size (q %/ d)) = (size (p * d) < size q).
Proof.
Admitted.

Lemma dvdp_exp d k p : 0 < k -> d %| p -> d %| (p ^+ k).
Proof.
Admitted.

Lemma dvdp_exp2l d k l : k <= l -> d ^+ k %| d ^+ l.
Proof.
Admitted.

Lemma dvdp_Pexp2l d k l : 1 < size d -> (d ^+ k %| d ^+ l) = (k <= l).
Proof.
Admitted.

Lemma dvdp_exp2r p q k : p %| q -> p ^+ k %| q ^+ k.
Proof.
Admitted.

Lemma dvdp_exp_sub p q k l: p != 0 ->
  (p ^+ k %| q * p ^+ l) = (p ^+ (k - l) %| q).
Proof.
Admitted.

Lemma dvdp_XsubCl p x : (('X - x%:P) %| p) = root p x.
Proof.
Admitted.

Lemma root_dvdp p q x : p %| q -> root p x -> root q x.
Proof.
Admitted.

Lemma polyXsubCP p x : reflect (p.
Proof.
Admitted.

Lemma eqp_div_XsubC p c :
  (p == (p %/ ('X - c%:P)) * ('X - c%:P)) = ('X - c%:P %| p).
Proof.
Admitted.

Lemma root_factor_theorem p x : root p x = (('X - x%:P) %| p).
Proof.
Admitted.

Lemma uniq_roots_dvdp p rs : all (root p) rs -> uniq_roots rs ->
  (\prod_(z <- rs) ('X - z%:P)) %| p.
Proof.
Admitted.

Lemma root_bigmul x (ps : seq {poly R}) :
  ~~root (\big[*%R/1]_(p <- ps) p) x = all (fun p => ~~ root p x) ps.
Proof.
Admitted.

Lemma eqpP m n :
  reflect (exists2 c12, (c12.
Proof.
Admitted.

Lemma eqp_eq p q: p %= q -> (lead_coef q) *: p = (lead_coef p) *: q.
Proof.
Admitted.

Lemma eqpxx : reflexive (@eqp R).
Proof.
Admitted.

Hint Resolve eqpxx : core.

Lemma eqpW p q : p = q -> p %= q.
Proof.
Admitted.

Lemma eqp_sym : symmetric (@eqp R).
Proof.
Admitted.

Lemma eqp_trans : transitive (@eqp R).
Proof.
Admitted.

Lemma eqp_ltrans : left_transitive (@eqp R).
Proof.
Admitted.

Lemma eqp_rtrans : right_transitive (@eqp R).
Proof.
Admitted.

Lemma eqp0 p : (p %= 0) = (p == 0).
Proof.
Admitted.

Lemma eqp01 : (0 %= (1 : {poly R})) = false.
Proof.
Admitted.

Lemma eqp_scale p c : c != 0 -> c *: p %= p.
Proof.
Admitted.

Lemma eqp_size p q : p %= q -> size p = size q.
Proof.
Admitted.

Lemma size_poly_eq1 p : (size p == 1) = (p %= 1).
Proof.
Admitted.

Lemma polyXsubC_eqp1 (x : R) : ('X - x%:P %= 1) = false.
Proof.
Admitted.

Lemma dvdp_eqp1 p q : p %| q -> q %= 1 -> p %= 1.
Proof.
Admitted.

Lemma eqp_dvdr q p d: p %= q -> (d %| p) = (d %| q).
Proof.
Admitted.

Lemma eqp_dvdl d2 d1 p : d1 %= d2 -> (d1 %| p) = (d2 %| p).
Proof.
Admitted.

Lemma dvdpZr c m n : c != 0 -> (m %| c *: n) = (m %| n).
Proof.
Admitted.

Lemma dvdpZl c m n : c != 0 -> (c *: m %| n) = (m %| n).
Proof.
Admitted.

Lemma dvdpNl d p : ((- d) %| p) = (d %| p).
Proof.
Admitted.

Lemma dvdpNr d p : (d %| (- p)) = (d %| p).
Proof.
Admitted.

Lemma eqp_mul2r r p q : r != 0 -> (p * r %= q * r) = (p %= q).
Proof.
Admitted.

Lemma eqp_mul2l r p q: r != 0 -> (r * p %= r * q) = (p %= q).
Proof.
Admitted.

Lemma eqp_mull r p q: q %= r -> p * q %= p * r.
Proof.
Admitted.

Lemma eqp_mulr q p r : p %= q -> p * r %= q * r.
Proof.
Admitted.

Lemma eqp_exp p q k : p %= q -> p ^+ k %= q ^+ k.
Proof.
Admitted.

Lemma polyC_eqp1 (c : R) : (c%:P %= 1) = (c != 0).
Proof.
Admitted.

Lemma dvdUp d p: d %= 1 -> d %| p.
Proof.
Admitted.

Lemma dvdp_size_eqp p q : p %| q -> (size p == size q) = (p %= q).
Proof.
Admitted.

Lemma eqp_root p q : p %= q -> root p =1 root q.
Proof.
Admitted.

Lemma eqp_rmod_mod p q : rmodp p q %= modp p q.
Proof.
Admitted.

Lemma eqp_rdiv_div p q : rdivp p q %= divp p q.
Proof.
Admitted.

Lemma dvd_eqp_divl d p q (dvd_dp : d %| q) (eq_pq : p %= q) :
  p %/ d %= q %/ d.
Proof.
Admitted.

Definition gcdp p q :=
  let: (p1, q1) := if size p < size q then (q, p) else (p, q) in
  if p1 == 0 then q1 else
  let fix loop (n : nat) (pp qq : {poly R}) {struct n} :=
      let rr := modp pp qq in
      if rr == 0 then qq else
      if n is n1.+1 then loop n1 qq rr else rr in
  loop (size p1) p1 q1.
Arguments gcdp : simpl never.

Lemma gcd0p : left_id 0 gcdp.
Proof.
Admitted.

Lemma gcdp0 : right_id 0 gcdp.
Proof.
Admitted.

Lemma gcdpE p q :
  gcdp p q = if size p < size q
    then gcdp (modp q p) p else gcdp (modp p q) q.
Proof.
Admitted.

Lemma size_gcd1p p : size (gcdp 1 p) = 1.
Proof.
Admitted.

Lemma size_gcdp1 p : size (gcdp p 1) = 1.
Proof.
Admitted.

Lemma gcdpp : idempotent_op gcdp.
Proof.
Admitted.

Lemma dvdp_gcdlr p q : (gcdp p q %| p) && (gcdp p q %| q).
Proof.
Admitted.

Lemma dvdp_gcdl p q : gcdp p q %| p.
Proof.
Admitted.

Lemma dvdp_gcdr p q :gcdp p q %| q.
Proof.
Admitted.

Lemma leq_gcdpl p q : p != 0 -> size (gcdp p q) <= size p.
Proof.
Admitted.

Lemma leq_gcdpr p q : q != 0 -> size (gcdp p q) <= size q.
Proof.
Admitted.

Lemma dvdp_gcd p m n : (p %| gcdp m n) = (p %| m) && (p %| n).
Proof.
Admitted.

Lemma gcdpC p q : gcdp p q %= gcdp q p.
Proof.
Admitted.

Lemma gcd1p p : gcdp 1 p %= 1.
Proof.
Admitted.

Lemma gcdp1 p : gcdp p 1 %= 1.
Proof.
Admitted.

Lemma gcdp_addl_mul p q r: gcdp r (p * r + q) %= gcdp r q.
Proof.
Admitted.

Lemma gcdp_addl m n : gcdp m (m + n) %= gcdp m n.
Proof.
Admitted.

Lemma gcdp_addr m n : gcdp m (n + m) %= gcdp m n.
Proof.
Admitted.

Lemma gcdp_mull m n : gcdp n (m * n) %= n.
Proof.
Admitted.

Lemma gcdp_mulr m n : gcdp n (n * m) %= n.
Proof.
Admitted.

Lemma gcdp_scalel c m n : c != 0 -> gcdp (c *: m) n %= gcdp m n.
Proof.
Admitted.

Lemma gcdp_scaler c m n : c != 0 -> gcdp m (c *: n) %= gcdp m n.
Proof.
Admitted.

Lemma dvdp_gcd_idl m n : m %| n -> gcdp m n %= m.
Proof.
Admitted.

Lemma dvdp_gcd_idr m n : n %| m -> gcdp m n %= n.
Proof.
Admitted.

Lemma gcdp_exp p k l : gcdp (p ^+ k) (p ^+ l) %= p ^+ minn k l.
Proof.
Admitted.

Lemma gcdp_eq0 p q : (gcdp p q == 0) = (p == 0) && (q == 0).
Proof.
Admitted.

Lemma eqp_gcdr p q r : q %= r -> gcdp p q %= gcdp p r.
Proof.
Admitted.

Lemma eqp_gcdl r p q : p %= q -> gcdp p r %= gcdp q r.
Proof.
Admitted.

Lemma eqp_gcd p1 p2 q1 q2 : p1 %= p2 -> q1 %= q2 -> gcdp p1 q1 %= gcdp p2 q2.
Proof.
Admitted.

Lemma eqp_rgcd_gcd p q : rgcdp p q %= gcdp p q.
Proof.
Admitted.

Lemma gcdp_modl m n : gcdp (m %% n) n %= gcdp m n.
Proof.
Admitted.

Lemma gcdp_modr m n : gcdp m (n %% m) %= gcdp m n.
Proof.
Admitted.

Lemma gcdp_def d m n :
    d %| m -> d %| n -> (forall d', d' %| m -> d' %| n -> d' %| d) ->
  gcdp m n %= d.
Proof.
Admitted.

Definition coprimep p q := size (gcdp p q) == 1%N.

Lemma coprimep_size_gcd p q : coprimep p q -> size (gcdp p q) = 1.
Proof.
Admitted.

Lemma coprimep_def p q : coprimep p q = (size (gcdp p q) == 1).
Proof.
Admitted.

Lemma coprimepZl c m n : c != 0 -> coprimep (c *: m) n = coprimep m n.
Proof.
Admitted.

Lemma coprimepZr c m n: c != 0 -> coprimep m (c *: n) = coprimep m n.
Proof.
Admitted.

Lemma coprimepp p : coprimep p p = (size p == 1).
Proof.
Admitted.

Lemma gcdp_eqp1 p q : (gcdp p q %= 1) = coprimep p q.
Proof.
Admitted.

Lemma coprimep_sym p q : coprimep p q = coprimep q p.
Proof.
Admitted.

Lemma coprime1p p : coprimep 1 p.
Proof.
Admitted.

Lemma coprimep1 p : coprimep p 1.
Proof.
Admitted.

Lemma coprimep0 p : coprimep p 0 = (p %= 1).
Proof.
Admitted.

Lemma coprime0p p : coprimep 0 p = (p %= 1).
Proof.
Admitted.

(* This is different from coprimeP in div. shall we keep this? *)
Lemma coprimepP p q :
 reflect (forall d, d %| p -> d %| q -> d %= 1) (coprimep p q).
Proof.
Admitted.

Lemma coprimepPn p q : p != 0 ->
  reflect (exists d, (d %| gcdp p q) && ~~ (d %= 1)) (~~ coprimep p q).
Proof.
Admitted.

Lemma coprimep_dvdl q p r : r %| q -> coprimep p q -> coprimep p r.
Proof.
Admitted.

Lemma coprimep_dvdr p q r : r %| p -> coprimep p q -> coprimep r q.
Proof.
Admitted.

Lemma coprimep_modl p q : coprimep (p %% q) q = coprimep p q.
Proof.
Admitted.

Lemma coprimep_modr q p : coprimep q (p %% q) = coprimep q p.
Proof.
Admitted.

Lemma rcoprimep_coprimep q p : rcoprimep q p = coprimep q p.
Proof.
Admitted.

Lemma eqp_coprimepr p q r : q %= r -> coprimep p q = coprimep p r.
Proof.
Admitted.

Lemma eqp_coprimepl p q r : q %= r -> coprimep q p = coprimep r p.
Proof.
Admitted.

(* This should be implemented with an extended remainder sequence *)
Fixpoint egcdp_rec p q k {struct k} : {poly R} * {poly R} :=
  if k is k'.+1 then
    if q == 0 then (1, 0) else
    let: (u, v) := egcdp_rec q (p %% q) k' in
      (lead_coef q ^+ scalp p q *: v, (u - v * (p %/ q)))
  else (1, 0).

Definition egcdp p q :=
  if size q <= size p then egcdp_rec p q (size q)
    else let e := egcdp_rec q p (size p) in (e.2, e.1).

(* No provable egcd0p *)
Lemma egcdp0 p : egcdp p 0 = (1, 0).
Proof.
Admitted.

Lemma egcdp_recP : forall k p q, q != 0 -> size q <= k -> size q <= size p ->
  let e := (egcdp_rec p q k) in
    [/\ size e.
Proof.
Admitted.

Lemma egcdpP p q : p != 0 -> q != 0 -> forall (e := egcdp p q),
  [/\ size e.
Proof.
Admitted.

Lemma egcdpE p q (e := egcdp p q) : gcdp p q %= e.
Proof.
Admitted.

Lemma Bezoutp p q : exists u, u.
Proof.
Admitted.

Lemma Bezout_coprimepP p q :
  reflect (exists u, u.
Proof.
Admitted.

Lemma coprimep_root p q x : coprimep p q -> root p x -> q.
Proof.
Admitted.

Lemma Gauss_dvdpl p q d: coprimep d q -> (d %| p * q) = (d %| p).
Proof.
Admitted.

Lemma Gauss_dvdpr p q d: coprimep d q -> (d %| q * p) = (d %| p).
Proof.
Admitted.

(* This could be simplified with the introduction of lcmp *)
Lemma Gauss_dvdp m n p : coprimep m n -> (m * n %| p) = (m %| p) && (n %| p).
Proof.
Admitted.

Lemma Gauss_gcdpr p m n : coprimep p m -> gcdp p (m * n) %= gcdp p n.
Proof.
Admitted.

Lemma Gauss_gcdpl p m n : coprimep p n -> gcdp p (m * n) %= gcdp p m.
Proof.
Admitted.

Lemma coprimepMr p q r : coprimep p (q * r) = (coprimep p q && coprimep p r).
Proof.
Admitted.

Lemma coprimepMl p q r: coprimep (q * r) p = (coprimep q p && coprimep r p).
Proof.
Admitted.

Lemma modp_coprime k u n : k != 0 -> (k * u) %% n %= 1 -> coprimep k n.
Proof.
Admitted.

Lemma coprimep_pexpl k m n : 0 < k -> coprimep (m ^+ k) n = coprimep m n.
Proof.
Admitted.

Lemma coprimep_pexpr k m n : 0 < k -> coprimep m (n ^+ k) = coprimep m n.
Proof.
Admitted.

Lemma coprimep_expl k m n : coprimep m n -> coprimep (m ^+ k) n.
Proof.
Admitted.

Lemma coprimep_expr k m n : coprimep m n -> coprimep m (n ^+ k).
Proof.
Admitted.

Lemma gcdp_mul2l p q r : gcdp (p * q) (p * r) %= (p * gcdp q r).
Proof.
Admitted.

Lemma gcdp_mul2r q r p : gcdp (q * p) (r * p) %= gcdp q r * p.
Proof.
Admitted.

Lemma mulp_gcdr p q r : r * (gcdp p q) %= gcdp (r * p) (r * q).
Proof.
Admitted.

Lemma mulp_gcdl p q r : (gcdp p q) * r %= gcdp (p * r) (q * r).
Proof.
Admitted.

Lemma coprimep_div_gcd p q : (p != 0) || (q != 0) ->
  coprimep (p %/ (gcdp p q)) (q %/ gcdp p q).
Proof.
Admitted.

Lemma divp_eq0 p q : (p %/ q == 0) = [|| p == 0, q ==0 | size p < size q].
Proof.
Admitted.

Lemma dvdp_div_eq0 p q : q %| p -> (p %/ q == 0) = (p == 0).
Proof.
Admitted.

Lemma Bezout_coprimepPn p q : p != 0 -> q != 0 ->
  reflect (exists2 uv : {poly R} * {poly R},
    (0 < size uv.
Proof.
Admitted.

Lemma dvdp_pexp2r m n k : k > 0 -> (m ^+ k %| n ^+ k) = (m %| n).
Proof.
Admitted.

Lemma root_gcd p q x : root (gcdp p q) x = root p x && root q x.
Proof.
Admitted.

Lemma root_biggcd x (ps : seq {poly R}) :
  root (\big[gcdp/0]_(p <- ps) p) x = all (fun p => root p x) ps.
Proof.
Admitted.

(* "gdcop Q P" is the Greatest Divisor of P which is coprime to Q *)
(* if P null, we pose that gdcop returns 1 if Q null, 0 otherwise*)
Fixpoint gdcop_rec q p k :=
  if k is m.+1 then
      if coprimep p q then p
        else gdcop_rec q (divp p (gcdp p q)) m
    else (q == 0)%:R.

Definition gdcop q p := gdcop_rec q p (size p).

Variant gdcop_spec q p : {poly R} -> Type :=
  GdcopSpec r of (dvdp r p) & ((coprimep r q) || (p == 0))
  & (forall d, dvdp d p -> coprimep d q -> dvdp d r)
  : gdcop_spec q p r.

Lemma gdcop0 q : gdcop q 0 = (q == 0)%:R.
Proof.
Admitted.

Lemma gdcop_recP q p k : size p <= k -> gdcop_spec q p (gdcop_rec q p k).
Proof.
Admitted.

Lemma gdcopP q p : gdcop_spec q p (gdcop q p).
Proof.
Admitted.

Lemma coprimep_gdco p q : (q != 0)%B -> coprimep (gdcop p q) p.
Proof.
Admitted.

Lemma size2_dvdp_gdco p q d : p != 0 -> size d = 2 ->
  (d %| (gdcop q p)) = (d %| p) && ~~(d %| q).
Proof.
Admitted.

Lemma dvdp_gdco p q : (gdcop p q) %| q.
Proof.
Admitted.

Lemma root_gdco p q x : p != 0 -> root (gdcop q p) x = root p x && ~~(root q x).
Proof.
Admitted.

Lemma dvdp_comp_poly r p q : (p %| q) -> (p \Po r) %| (q \Po r).
Proof.
Admitted.

Lemma gcdp_comp_poly r p q : gcdp p q \Po r %= gcdp (p \Po r) (q \Po r).
Proof.
Admitted.

Lemma coprimep_comp_poly r p q : coprimep p q -> coprimep (p \Po r) (q \Po r).
Proof.
Admitted.

Lemma coprimep_addl_mul p q r : coprimep r (p * r + q) = coprimep r q.
Proof.
Admitted.

Definition irreducible_poly p :=
  (size p > 1) * (forall q, size q != 1 -> q %| p -> q %= p) : Prop.

Lemma irredp_neq0 p : irreducible_poly p -> p != 0.
Proof.
Admitted.

Definition apply_irredp p (irr_p : irreducible_poly p) := irr_p.2.
Coercion apply_irredp : irreducible_poly >-> Funclass.

Lemma modp_XsubC p c : p %% ('X - c%:P) = p.
Proof.
Admitted.

Lemma coprimep_XsubC p c : coprimep p ('X - c%:P) = ~~ root p c.
Proof.
Admitted.

Lemma coprimep_XsubC2 (a b : R) : b - a != 0 ->
  coprimep ('X - a%:P) ('X - b%:P).
Proof.
Admitted.

Lemma coprimepX p : coprimep p 'X = ~~ root p 0.
Proof.
Admitted.

Lemma eqp_monic : {in monic &, forall p q, (p %= q) = (p == q)}.
Proof.
Admitted.

Lemma dvdp_mul_XsubC p q c :
  (p %| ('X - c%:P) * q) = ((if root p c then p %/ ('X - c%:P) else p) %| q).
Proof.
Admitted.

Lemma dvdp_prod_XsubC (I : Type) (r : seq I) (F : I -> R) p :
    p %| \prod_(i <- r) ('X - (F i)%:P) ->
  {m | p %= \prod_(i <- mask m r) ('X - (F i)%:P)}.
Proof.
Admitted.

Lemma irredp_XsubC (x : R) : irreducible_poly ('X - x%:P).
Proof.
Admitted.

Lemma irredp_XaddC (x : R) : irreducible_poly ('X + x%:P).
Proof.
Admitted.

Lemma irredp_XsubCP d p :
  irreducible_poly p -> d %| p -> {d %= 1} + {d %= p}.
Proof.
Admitted.

Lemma dvdp_exp_XsubCP (p : {poly R}) (c : R) (n : nat) :
  reflect (exists2 k, (k <= n)%N & p %= ('X - c%:P) ^+ k)
          (p %| ('X - c%:P) ^+ n).
Proof.
Admitted.

End IDomainPseudoDivision.
Arguments gcdp : simpl never.

#[global] Hint Resolve eqpxx divp0 divp1 mod0p modp0 modp1 : core.
#[global] Hint Resolve dvdp_mull dvdp_mulr dvdpp dvdp0 : core.
Arguments dvdp_exp_XsubCP {R p c n}.

End CommonIdomain.

Module Idomain.

Include IdomainDefs.
Export IdomainDefs.
Include WeakIdomain.
Include CommonIdomain.

End Idomain.

Module IdomainMonic.

Import Ring ComRing UnitRing IdomainDefs Idomain.

Section IdomainMonic.

Variable R : idomainType.

Implicit Type p d r : {poly R}.

Section MonicDivisor.

Variable q : {poly R}.
Hypothesis monq : q \is monic.

Lemma divpE p : p %/ q = rdivp p q.
Proof.
Admitted.

Lemma modpE p : p %% q = rmodp p q.
Proof.
Admitted.

Lemma scalpE p : scalp p q = 0.
Proof.
Admitted.

Lemma divp_eq p : p = (p %/ q) * q + (p %% q).
Proof.
Admitted.

Lemma divpp p : q %/ q = 1.
Proof.
Admitted.

Lemma dvdp_eq p : (q %| p) = (p == (p %/ q) * q).
Proof.
Admitted.

Lemma dvdpP p : reflect (exists qq, p = qq * q) (q %| p).
Proof.
Admitted.

Lemma mulpK p : p * q %/ q = p.
Proof.
Admitted.

Lemma mulKp p : q * p %/ q = p.
Proof.
Admitted.

End MonicDivisor.

Lemma drop_poly_divp n p : drop_poly n p = p %/ 'X^n.
Proof.
Admitted.

Lemma take_poly_modp n p : take_poly n p = p %% 'X^n.
Proof.
Admitted.

End IdomainMonic.

End IdomainMonic.

Module IdomainUnit.

Import Ring ComRing UnitRing IdomainDefs Idomain.

Section UnitDivisor.

Variable R : idomainType.
Variable d : {poly R}.

Hypothesis ulcd : lead_coef d \in GRing.unit.

Implicit Type p q r : {poly R}.

Lemma divp_eq p : p = (p %/ d) * d + (p %% d).
Proof.
Admitted.

Lemma edivpP p q r : p = q * d + r -> size r < size d ->
  q = (p %/ d) /\ r = p %% d.
Proof.
Admitted.

Lemma divpP p q r : p = q * d + r -> size r < size d -> q = (p %/ d).
Proof.
Admitted.

Lemma modpP p q r : p = q * d + r -> size r < size d -> r = (p %% d).
Proof.
Admitted.

Lemma ulc_eqpP p q : lead_coef q \is a GRing.
Proof.
Admitted.

Lemma dvdp_eq p : (d %| p) = (p == p %/ d * d).
Proof.
Admitted.

Lemma ucl_eqp_eq p q : lead_coef q \is a GRing.
Proof.
Admitted.

Lemma modpZl c p : (c *: p) %% d = c *: (p %% d).
Proof.
Admitted.

Lemma divpZl c p : (c *: p) %/ d = c *: (p %/ d).
Proof.
Admitted.

Lemma eqp_modpl p q : p %= q -> (p %% d) %= (q %% d).
Proof.
Admitted.

Lemma eqp_divl p q : p %= q -> (p %/ d) %= (q %/ d).
Proof.
Admitted.

Lemma modpN p : (- p) %% d = - (p %% d).
Proof.
Admitted.

Lemma divpN p : (- p) %/ d = - (p %/ d).
Proof.
Admitted.

Lemma modpD p q : (p + q) %% d = p %% d + q %% d.
Proof.
Admitted.

Lemma divpD p q : (p + q) %/ d = p %/ d + q %/ d.
Proof.
Admitted.

Lemma mulpK q : (q * d) %/ d = q.
Proof.
Admitted.

Lemma mulKp q : (d * q) %/ d = q.
Proof.
Admitted.

Lemma divp_addl_mul_small q r : size r < size d -> (q * d + r) %/ d = q.
Proof.
Admitted.

Lemma modp_addl_mul_small q r : size r < size d -> (q * d + r) %% d = r.
Proof.
Admitted.

Lemma divp_addl_mul q r : (q * d + r) %/ d = q + r %/ d.
Proof.
Admitted.

Lemma divpp : d %/ d = 1.
Proof.
Admitted.

Lemma leq_divMp m : size (m %/ d * d) <= size m.
Proof.
Admitted.

Lemma dvdpP p : reflect (exists q, p = q * d) (d %| p).
Proof.
Admitted.

Lemma divpK p : d %| p -> p %/ d * d = p.
Proof.
Admitted.

Lemma divpKC p : d %| p -> d * (p %/ d) = p.
Proof.
Admitted.

Lemma dvdp_eq_div p q : d %| p -> (q == p %/ d) = (q * d == p).
Proof.
Admitted.

Lemma dvdp_eq_mul p q : d %| p -> (p == q * d) = (p %/ d == q).
Proof.
Admitted.

Lemma divp_mulA p q : d %| q -> p * (q %/ d) = p * q %/ d.
Proof.
Admitted.

Lemma divp_mulAC m n : d %| m -> m %/ d * n = m * n %/ d.
Proof.
Admitted.

Lemma divp_mulCA p q : d %| p -> d %| q -> p * (q %/ d) = q * (p %/ d).
Proof.
Admitted.

Lemma modp_mul p q : (p * (q %% d)) %% d = (p * q) %% d.
Proof.
Admitted.

End UnitDivisor.

#[deprecated(since="mathcomp 2.4.0", use=leq_divMp)]
Notation leq_trunc_divp := leq_divMp (only parsing).

Section MoreUnitDivisor.

Variable R : idomainType.
Variable d : {poly R}.
Hypothesis ulcd : lead_coef d \in GRing.unit.

Implicit Types p q : {poly R}.

Lemma expp_sub m n : n <= m -> (d ^+ (m - n))%N = d ^+ m %/ d ^+ n.
Proof.
Admitted.

Lemma divp_pmul2l p q : lead_coef q \in GRing.
Proof.
Admitted.

Lemma divp_pmul2r p q : lead_coef p \in GRing.
Proof.
Admitted.

Lemma divp_divl r p q :
    lead_coef r \in GRing.
Proof.
Admitted.

Lemma divpAC p q : lead_coef p \in GRing.
Proof.
Admitted.

Lemma modpZr c p : c \in GRing.
Proof.
Admitted.

Lemma divpZr c p : c \in GRing.
Proof.
Admitted.

End MoreUnitDivisor.

End IdomainUnit.

Module Field.

Import Ring ComRing UnitRing.
Include IdomainDefs.
Export IdomainDefs.
Include CommonIdomain.

Section FieldDivision.

Variable F : fieldType.

Implicit Type p q r d : {poly F}.

Lemma divp_eq p q : p = (p %/ q) * q + (p %% q).
Proof.
Admitted.

Lemma divp_modpP p q d r : p = q * d + r -> size r < size d ->
  q = (p %/ d) /\ r = p %% d.
Proof.
Admitted.

Lemma divpP p q d r : p = q * d + r -> size r < size d ->
  q = (p %/ d).
Proof.
Admitted.

Lemma modpP p q d r : p = q * d + r -> size r < size d -> r = (p %% d).
Proof.
Admitted.

Lemma eqpfP p q : p %= q -> p = (lead_coef p / lead_coef q) *: q.
Proof.
Admitted.

Lemma dvdp_eq q p : (q %| p) = (p == p %/ q * q).
Proof.
Admitted.

Lemma eqpf_eq p q : reflect (exists2 c, c != 0 & p = c *: q) (p %= q).
Proof.
Admitted.

Lemma modpZl c p q : (c *: p) %% q = c *: (p %% q).
Proof.
Admitted.

Lemma mulpK p q : q != 0 -> p * q %/ q = p.
Proof.
Admitted.

Lemma mulKp p q : q != 0 -> q * p %/ q = p.
Proof.
Admitted.

Lemma divpZl c p q : (c *: p) %/ q = c *: (p %/ q).
Proof.
Admitted.

Lemma modpZr c p d : c != 0 -> p %% (c *: d) = (p %% d).
Proof.
Admitted.

Lemma divpZr c p d : c != 0 -> p %/ (c *: d) = c^-1 *: (p %/ d).
Proof.
Admitted.

Lemma eqp_modpl d p q : p %= q -> (p %% d) %= (q %% d).
Proof.
Admitted.

Lemma eqp_divl d p q : p %= q -> (p %/ d) %= (q %/ d).
Proof.
Admitted.

Lemma eqp_modpr d p q : p %= q -> (d %% p) %= (d %% q).
Proof.
Admitted.

Lemma eqp_mod p1 p2 q1 q2 : p1 %= p2 -> q1 %= q2 -> p1 %% q1 %= p2 %% q2.
Proof.
Admitted.

Lemma eqp_divr (d m n : {poly F}) : m %= n -> (d %/ m) %= (d %/ n).
Proof.
Admitted.

Lemma eqp_div p1 p2 q1 q2 : p1 %= p2 -> q1 %= q2 -> p1 %/ q1 %= p2 %/ q2.
Proof.
Admitted.

Lemma eqp_gdcor p q r : q %= r -> gdcop p q %= gdcop p r.
Proof.
Admitted.

Lemma eqp_gdcol p q r : q %= r -> gdcop q p %= gdcop r p.
Proof.
Admitted.

Lemma eqp_rgdco_gdco q p : rgdcop q p %= gdcop q p.
Proof.
Admitted.

Lemma modpD d p q : (p + q) %% d = p %% d + q %% d.
Proof.
Admitted.

Lemma modpN p q : (- p) %% q = - (p %% q).
Proof.
Admitted.

Lemma modNp p q : (- p) %% q = - (p %% q).
Proof.
Admitted.

Lemma divpD d p q : (p + q) %/ d = p %/ d + q %/ d.
Proof.
Admitted.

Lemma divpN p q : (- p) %/ q = - (p %/ q).
Proof.
Admitted.

Lemma divp_addl_mul_small d q r : size r < size d -> (q * d + r) %/ d = q.
Proof.
Admitted.

Lemma modp_addl_mul_small d q r : size r < size d -> (q * d + r) %% d = r.
Proof.
Admitted.

Lemma divp_addl_mul d q r : d != 0 -> (q * d + r) %/ d = q + r %/ d.
Proof.
Admitted.

Lemma divpp d : d != 0 -> d %/ d = 1.
Proof.
Admitted.

Lemma leq_divMp d m : size (m %/ d * d) <= size m.
Proof.
Admitted.

Lemma divpK d p : d %| p -> p %/ d * d = p.
Proof.
Admitted.

Lemma divpKC d p : d %| p -> d * (p %/ d) = p.
Proof.
Admitted.

Lemma dvdp_eq_div d p q : d != 0 -> d %| p -> (q == p %/ d) = (q * d == p).
Proof.
Admitted.

Lemma dvdp_eq_mul d p q : d != 0 -> d %| p -> (p == q * d) = (p %/ d == q).
Proof.
Admitted.

Lemma divp_mulA d p q : d %| q -> p * (q %/ d) = p * q %/ d.
Proof.
Admitted.

Lemma divp_mulAC d m n : d %| m -> m %/ d * n = m * n %/ d.
Proof.
Admitted.

Lemma divp_mulCA d p q : d %| p -> d %| q -> p * (q %/ d) = q * (p %/ d).
Proof.
Admitted.

Lemma expp_sub d m n : d != 0 -> m >= n -> (d ^+ (m - n))%N = d ^+ m %/ d ^+ n.
Proof.
Admitted.

Lemma divp_pmul2l d q p : d != 0 -> q != 0 -> d * p %/ (d * q) = p %/ q.
Proof.
Admitted.

Lemma divp_pmul2r d p q : d != 0 -> p != 0 -> q * d %/ (p * d) = q %/ p.
Proof.
Admitted.

Lemma divp_divl r p q : q %/ p %/ r = q %/ (p * r).
Proof.
Admitted.

Lemma divpAC d p q : q %/ d %/ p = q %/ p %/ d.
Proof.
Admitted.

Lemma edivp_def p q : edivp p q = (0, p %/ q, p %% q).
Proof.
Admitted.

Lemma divpE p q : p %/ q = (lead_coef q)^-(rscalp p q) *: (rdivp p q).
Proof.
Admitted.

Lemma modpE p q : p %% q = (lead_coef q)^-(rscalp p q) *: (rmodp p q).
Proof.
Admitted.

Lemma scalpE p q : scalp p q = 0.
Proof.
Admitted.

(* Just to have it without importing the weak theory *)
Lemma dvdpE p q : (p %| q) = rdvdp p q.
Proof.
Admitted.

Variant edivp_spec m d : nat * {poly F} * {poly F} -> Type :=
  EdivpSpec n q r of
  m = q * d + r & (d != 0) ==> (size r < size d) : edivp_spec m d (n, q, r).

Lemma edivpP m d : edivp_spec m d (edivp m d).
Proof.
Admitted.

Lemma edivp_eq d q r : size r < size d -> edivp (q * d + r) d = (0, q, r).
Proof.
Admitted.

Lemma modp_mul p q m : (p * (q %% m)) %% m = (p * q) %% m.
Proof.
Admitted.

Lemma horner_mod p q x : root q x -> (p %% q).
Proof.
Admitted.

Lemma dvdpP p q : reflect (exists qq, p = qq * q) (q %| p).
Proof.
Admitted.

Lemma Bezout_eq1_coprimepP p q :
  reflect (exists u, u.
Proof.
Admitted.

Lemma dvdp_gdcor p q : q != 0 -> p %| (gdcop q p) * (q ^+ size p).
Proof.
Admitted.

Lemma reducible_cubic_root p q :
  size p <= 4 -> 1 < size q < size p -> q %| p -> {r | root p r}.
Proof.
Admitted.

Lemma cubic_irreducible p :
  1 < size p <= 4 -> (forall x, ~~ root p x) -> irreducible_poly p.
Proof.
Admitted.

Section Multiplicity.

Definition mup x q :=
  [arg max_(n > (ord0 : 'I_(size q).+1) | ('X - x%:P) ^+ n %| q) n] : nat.

Lemma mup_geq x q n : q != 0 -> (n <= mup x q)%N = (('X - x%:P) ^+ n %| q).
Proof.
Admitted.

Lemma mup_leq x q n : q != 0 ->
  (mup x q <= n)%N = ~~ (('X - x%:P) ^+ n.
Proof.
Admitted.

Lemma mup_ltn x q n : q != 0 -> (mup x q < n)%N = ~~ (('X - x%:P) ^+ n %| q).
Proof.
Admitted.

Lemma XsubC_dvd x q : q != 0 -> ('X - x%:P %| q) = (0 < mup x q)%N.
Proof.
Admitted.

Lemma mup_XsubCX n x y :
  mup x (('X - y%:P) ^+ n) = (if (y == x) then n else 0)%N.
Proof.
Admitted.

Lemma mupNroot x q : ~~ root q x -> mup x q = 0%N.
Proof.
Admitted.

Lemma mupMr x q1 q2 : ~~ root q1 x -> mup x (q1 * q2) = mup x q2.
Proof.
Admitted.

Lemma mupMl x q1 q2 : ~~ root q2 x -> mup x (q1 * q2) = mup x q1.
Proof.
Admitted.

Lemma mupM x q1 q2 : q1 != 0 -> q2 != 0 ->
  mup x (q1 * q2) = (mup x q1 + mup x q2)%N.
Proof.
Admitted.

Lemma mu_prod_XsubC x (s : seq F) :
  mup x (\prod_(y <- s) ('X - y%:P)) = count_mem x s.
Proof.
Admitted.

Lemma prod_XsubC_eq (s t : seq F) :
  \prod_(x <- s) ('X - x%:P) = \prod_(x <- t) ('X - x%:P) -> perm_eq s t.
Proof.
Admitted.

End Multiplicity.

Section FieldRingMap.

Variable rR : nzRingType.

Variable f : {rmorphism F -> rR}.
Local Notation "p ^f" := (map_poly f p) : ring_scope.

Implicit Type a b : {poly F}.

Lemma redivp_map a b :
  redivp a^f b^f = (rscalp a b, (rdivp a b)^f, (rmodp a b)^f).
Proof.
Admitted.

End FieldRingMap.

Section FieldMap.

Variable rR : idomainType.

Variable f : {rmorphism F -> rR}.
Local Notation "p ^f" := (map_poly f p) : ring_scope.

Implicit Type a b : {poly F}.

Lemma edivp_map a b :
  edivp a^f b^f = (0, (a %/ b)^f, (a %% b)^f).
Proof.
Admitted.

Lemma scalp_map p q : scalp p^f q^f = scalp p q.
Proof.
Admitted.

Lemma map_divp p q : (p %/ q)^f = p^f %/ q^f.
Proof.
Admitted.

Lemma map_modp p q : (p %% q)^f = p^f %% q^f.
Proof.
Admitted.

Lemma egcdp_map p q :
  egcdp (map_poly f p) (map_poly f q)
     = (map_poly f (egcdp p q).
Proof.
Admitted.

Lemma dvdp_map p q : (p^f %| q^f) = (p %| q).
Proof.
Admitted.

Lemma eqp_map p q : (p^f %= q^f) = (p %= q).
Proof.
Admitted.

Lemma gcdp_map p q : (gcdp p q)^f = gcdp p^f q^f.
Proof.
Admitted.

Lemma coprimep_map p q : coprimep p^f q^f = coprimep p q.
Proof.
Admitted.

Lemma gdcop_rec_map p q n : (gdcop_rec p q n)^f = gdcop_rec p^f q^f n.
Proof.
Admitted.

Lemma gdcop_map p q : (gdcop p q)^f = gdcop p^f q^f.
Proof.
Admitted.

End FieldMap.

End FieldDivision.

#[deprecated(since="mathcomp 2.4.0", use=leq_divMp)]
Notation leq_trunc_divp := leq_divMp (only parsing).

End Field.

Module ClosedField.

Import Field.

Section closed.

Variable F : closedFieldType.

Lemma root_coprimep (p q : {poly F}) :
  (forall x, root p x -> q.
Proof.
Admitted.

Lemma coprimepP (p q : {poly F}) :
  reflect (forall x, root p x -> q.
Proof.
Admitted.

End closed.

End ClosedField.

End Pdiv.

Export Pdiv.Field.
