(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop fingroup perm.
From mathcomp Require Import nmodule algebra divalg decfield matrix mxalgebra.
From mathcomp Require Import poly polydiv.

(******************************************************************************)
(*   This file provides basic support for formal computation with matrices,   *)
(* mainly results combining matrices and univariate polynomials, such as the  *)
(* Cayley-Hamilton theorem; it also contains an extension of the first order  *)
(* representation of algebra introduced in ssralg (GRing.term/formula).       *)
(*      rVpoly v == the little-endian decoding of the row vector v as a       *)
(*                  polynomial p = \sum_i (v 0 i)%:P * 'X^i.                  *)
(*     poly_rV p == the partial inverse to rVpoly, for polynomials of degree  *)
(*                  less than d to 'rV_d (d is inferred from the context).    *)
(* Sylvester_mx p q == the Sylvester matrix of p and q.                       *)
(* resultant p q == the resultant of p and q, i.e., \det (Sylvester_mx p q).  *)
(*   horner_mx A == the morphism from {poly R} to 'M_n (n of the form n'.+1)  *)
(*                  mapping a (scalar) polynomial p to the value of its       *)
(*                  scalar matrix interpretation at A (this is an instance of *)
(*                  the generic horner_morph construct defined in poly).      *)
(* powers_mx A d == the d x (n ^ 2) matrix whose rows are the mxvec encodings *)
(*                  of the first d powers of A (n of the form n'.+1). Thus,   *)
(*                  vec_mx (v *m powers_mx A d) = horner_mx A (rVpoly v).     *)
(*   char_poly A  == the characteristic polynomial of A.                      *)
(* char_poly_mx A == a matrix whose determinant is char_poly A.               *)
(*  companionmx p == a matrix whose char_poly is p                            *)
(*   mxminpoly A  == the minimal polynomial of A, i.e., the smallest monic    *)
(*                   polynomial that annihilates A (A must be nontrivial).    *)
(* degree_mxminpoly A == the (positive) degree of mxminpoly A.                *)
(* mx_inv_horner A == the inverse of horner_mx A for polynomials of degree    *)
(*                  smaller than degree_mxminpoly A.                          *)
(*    kermxpoly g p == the kernel of p(g)                                     *)
(*  geigenspace g a == the generalized eigenspace of g for eigenvalue a       *)
(*                  := kermxpoly g ('X ^ n - a%:P) where g : 'M_n             *)
(*  eigenpoly g p <=> p is an eigen polynomial for g, i.e. kermxpoly g p != 0 *)
(*  integralOver RtoK u <-> u is in the integral closure of the image of R    *)
(*                  under RtoK : R -> K, i.e. u is a root of the image of a   *)
(*                  monic polynomial in R.                                    *)
(*  algebraicOver FtoE u <-> u : E is algebraic over E; it is a root of the   *)
(*                  image of a nonzero polynomial under FtoE; as F must be a  *)
(*                  fieldType, this is equivalent to integralOver FtoE u.     *)
(*  integralRange RtoK <-> the integral closure of the image of R contains    *)
(*                  all of K (:= forall u, integralOver RtoK u).              *)
(* This toolkit for building formal matrix expressions is packaged in the     *)
(* MatrixFormula submodule, and comprises the following:                      *)
(*     eval_mx e == GRing.eval lifted to matrices (:= map_mx (GRing.eval e)). *)
(*     mx_term A == GRing.Const lifted to matrices.                           *)
(* mulmx_term A B == the formal product of two matrices of terms.             *)
(* mxrank_form m A == a GRing.formula asserting that the interpretation of    *)
(*                  the term matrix A has rank m.                             *)
(* submx_form A B == a GRing.formula asserting that the row space of the      *)
(*                  interpretation of the term matrix A is included in the    *)
(*                  row space of the interpretation of B.                     *)
(*   seq_of_rV v == the seq corresponding to a row vector.                    *)
(*     row_env e == the flattening of a tensored environment e : seq 'rV_d.   *)
(* row_var F d k == the term vector of width d such that for e : seq 'rV[F]_d *)
(*                  we have eval e 'X_k = eval_mx (row_env e) (row_var d k).  *)
(*    conjmx V f := V *m f *m pinvmx V                                        *)
(*               == the conjugation of f by V, i.e. "the" matrix of f         *)
(*                  in the basis of row vectors of V.                         *)
(*                  Although this makes sense only when f stabilizes V,       *)
(*                  the definition can be stated more generally.              *)
(*  restrictmx V := conjmx (row_base V)                                       *)
(* A ~_P {in S'} == where P is a base change matrix, A is a matrix, and S     *)
(*                  is a boolean predicate representing a set of matrices,    *)
(*                  this states that conjmx P A is in S,                      *)
(*                  which means A is similar to a matrix in S.                *)
(* From the latter, we derive several related notions:                        *)
(*       A ~_P B := A ~_P {in pred1 B}                                        *)
(*                  A is similar to B, with base change matrix P              *)
(*  A ~_{in S} B := exists P, P \in S /\ A ~_P B                              *)
(*               == A is similar to B,   with a base change matrix in S       *)
(*   A ~_{in S} {in S'} := exists P, P \in S /\ A ~_P {in S'}                 *)
(*                      == A is similar to a matrix in the class S',          *)
(*                         with a base change matrix in S                     *)
(* all_simmx_in S As S' == all the matrices in the sequence As are            *)
(*                         similar to some matrix in the predicate S',        *)
(*                         with a base change matrix in S.                    *)
(*                                                                            *)
(* We also specialize the class S' to diagonalizability:                      *)
(*    diagonalizable_for P A := A ~_P {in is_diag_mx}.                        *)
(*     diagonalizable_in S A := A ~_{in S} {in is_diag_mx}.                   *)
(*          diagonalizable A := diagonalizable_in unitmx A.                   *)
(*  codiagonalizable_in S As := all_simmx_in S As is_diag_mx.                 *)
(*       codiagonalizable As := codiagonalizable_in unitmx As.                *)
(*                                                                            *)
(* The main results in diagnonalization theory are:                           *)
(* - diagonalizablePeigen:                                                    *)
(*     a matrix is diagonalizable iff there is a sequence                     *)
(*     of scalars r, such that the sum of the associated                      *)
(*     eigenspaces is full.                                                   *)
(* - diagonalizableP:                                                         *)
(*     a matrix is diagonalizable iff its minimal polynomial                  *)
(*     divides a split polynomial with simple roots.                          *)
(* - codiagonalizableP:                                                       *)
(*     a sequence of matrices are diagonalizable in the same basis            *)
(*     iff they are all diagonalizable and commute pairwize.                  *)
(*                                                                            *)
(* Naming conventions:                                                        *)
(* - p, q are polynomials                                                     *)
(* - A, B, C are matrices                                                     *)
(* - f, g are matrices that are viewed as linear maps                         *)
(* - V, W are matrices that are viewed as subspaces                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Monoid.Theory.

Local Open Scope ring_scope.

Import Pdiv.Idomain.
(* Row vector <-> bounded degree polynomial bijection *)
Section RowPoly.

Variables (R : nzSemiRingType) (d : nat).
Implicit Types u v : 'rV[R]_d.
Implicit Types p q : {poly R}.

Definition rVpoly v := \poly_(k < d) (if insub k is Some i then v 0 i else 0).
Definition poly_rV p := \row_(i < d) p`_i.

Lemma coef_rVpoly v k : (rVpoly v)`_k = if insub k is Some i then v 0 i else 0.
Proof.
Admitted.

Let split_diagA :
  exists2 q, \prod_(x <- diagA) ('X - x%:P) + q = char_poly & size q <= n.-1.
Proof.
Admitted.

Lemma size_char_poly : size char_poly = n.
Proof.
Admitted.
Let intR_XsubC u :
  integralOver RtoK (- u) -> {in 'X - u%:P : seq K, integralRange RtoK}.
Proof.
Admitted.

Lemma integral_opp u : integralOver RtoK u -> integralOver RtoK (- u).
Proof.
Admitted.

Lemma codiagonalizable_on m n (V_ : 'I_n -> 'M[F]_m) (As : seq 'M[F]_m) :
    (\sum_i V_ i :=: 1%:M)%MS -> mxdirect (\sum_i V_ i) ->
    (forall i, all (fun A => stablemx (V_ i) A) As) ->
    (forall i, codiagonalizable (map (restrictmx (V_ i)) As)) ->
  codiagonalizable As.
Proof.
Admitted.

Lemma diagonalizable_diag {n} (d : 'rV[F]_n) : diagonalizable (diag_mx d).
Proof.
Admitted.
Hint Resolve diagonalizable_diag : core.

Lemma diagonalizable_scalar {n} (a : F) : diagonalizable (a%:M : 'M_n).
Proof.
Admitted.
Hint Resolve diagonalizable_scalar : core.

Lemma diagonalizable0 {n} : diagonalizable (0 : 'M[F]_n).
Proof.
Admitted.
Hint Resolve diagonalizable0 : core.

Lemma diagonalizablePeigen {n} {A : 'M[F]_n} :
  diagonalizable A <->
  exists2 rs, uniq rs & (\sum_(r <- rs) eigenspace A r :=: 1%:M)%MS.
Proof.
Admitted.

Lemma diagonalizableP n' (n := n'.
Proof.
Admitted.

Lemma diagonalizable_conj_diag m n (V : 'M[F]_(m, n)) (d : 'rV[F]_n) :
  stablemx V (diag_mx d) -> row_free V -> diagonalizable (conjmx V (diag_mx d)).
Proof.
Admitted.

Lemma codiagonalizableP n (As : seq 'M[F]_n) :
  {in As &, forall A B, comm_mx A B} /\ {in As, forall A, diagonalizable A}
  <-> codiagonalizable As.
Proof.
Admitted.

End Diag.
