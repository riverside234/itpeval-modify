(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

#[local] Set Warnings "-deprecated-library-file,-deprecated-reference,-deprecated-syntactic-definition".

From Stdlib Require Import ZArith_base.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import Zcomplements.
From Stdlib Require Import Zdiv.
From Stdlib Require Import Zdivisibility.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Lia Cring Ncring_tac.

(** For compatibility reasons, this Open Scope isn't local as it should *)

Open Scope Z_scope.

#[local] Ltac Tauto.intuition_solver ::= auto with zarith.

(** This file contains some notions of number theory upon Z numbers:
     - a divisibility predicate [Z.divide]
     - a gcd predicate [gcd]
     - Euclid algorithm [extgcd]
     - a relatively prime predicate [rel_prime]
     - a prime predicate [prime]
     - properties of the efficient [Z.gcd] function
*)

(** The former specialized inductive predicate [Z.divide] is now
    a generic existential predicate. *)

(** Its former constructor is now a pseudo-constructor. *)

#[deprecated(use=ex_intro, since="Stdlib 9.1")]
Definition Zdivide_intro a b q (H:b=q*a) : Z.divide a b := ex_intro _ q H.

(** Results concerning divisibility*)

#[deprecated(use=Z.divide_1_l, since="Stdlib 9.1")]
Notation Zone_divide := Z.divide_1_l (only parsing).
#[deprecated(use=Z.divide_0_r, since="Stdlib 9.1")]
Notation Zdivide_0 := Z.divide_0_r (only parsing).
#[deprecated(use=Z.mul_divide_mono_l, since="Stdlib 9.1")]
Notation Zmult_divide_compat_l := Z.mul_divide_mono_l (only parsing).
#[deprecated(use=Z.mul_divide_mono_r, since="Stdlib 9.1")]
Notation Zmult_divide_compat_r := Z.mul_divide_mono_r (only parsing).
#[deprecated(use=Z.divide_add_r, since="Stdlib 9.1")]
Notation Zdivide_plus_r := Z.divide_add_r (only parsing).
#[deprecated(use=Z.divide_sub_r, since="Stdlib 9.1")]
Notation Zdivide_minus_l := Z.divide_sub_r (only parsing).
#[deprecated(use=Z.divide_mul_l, since="Stdlib 9.1")]
Notation Zdivide_mult_l := Z.divide_mul_l (only parsing).
#[deprecated(use=Z.divide_mul_r, since="Stdlib 9.1")]
Notation Zdivide_mult_r := Z.divide_mul_r (only parsing).
#[deprecated(use=Z.divide_factor_l, since="Stdlib 9.1")]
Notation Zdivide_factor_r := Z.divide_factor_l (only parsing).
#[deprecated(use=Z.divide_factor_r, since="Stdlib 9.1")]
Notation Zdivide_factor_l := Z.divide_factor_r (only parsing).

#[deprecated(use=Z.divide_opp_r, since="Stdlib 9.1")]
Lemma Zdivide_opp_r a b : (a | b) -> (a | - b).
Proof.
Admitted.

#[deprecated(since="Stdlib 9.1")]
Definition prime_dec_aux:
 forall p m,
  { forall n, 1 < n < m -> rel_prime n p } +
  { exists n, 1 < n < m  /\ ~ rel_prime n p }.
Proof.
Admitted.


Definition prime_dec: forall p, { prime p }+{ ~ prime p }.
Proof.
Admitted.

Theorem not_prime_divide:
 forall p, 1 < p -> ~ prime p -> exists n, 1 < n < p  /\ (n | p).
Proof.
Admitted.
