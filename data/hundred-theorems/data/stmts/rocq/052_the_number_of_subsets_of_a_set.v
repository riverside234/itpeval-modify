(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop.

(******************************************************************************)
(* This file defines a type for sets over a finite Type, similar to the type  *)
(* of functions over a finite Type defined in finfun.v (indeed, based in it): *)
(* {set T} where T must have a finType structure.                             *)
(* We equip {set T} itself with a finType structure, hence Leibnitz and       *)
(* extensional equalities coincide on {set T}, and we can form {set {set T}}. *)
(*   If A, B : {set T} and P : {set {set T}}, we define:                      *)
(*           x \in A == x belongs to A (i.e., {set T} implements predType,    *)
(*                      by coercion to pred_sort)                             *)
(*             mem A == the predicate corresponding to A                      *)
(*          finset p == the set corresponding to a predicate p                *)
(*       [set x | P] == the set containing the x such that P is true (x may   *)
(*                      appear in P)                                          *)
(*   [set x | P & Q] := [set x | P && Q]                                      *)
(*      [set x in A] == the set containing the x in a collective predicate A  *)
(*  [set x in A | P] == the set containing the x in A such that P is true     *)
(* [set x in A | P & Q] := [set x in A | P && Q]                              *)
(*  All these have typed variants [set x : T | P], [set x : T in A], etc.     *)
(*              set0 == the empty set                                         *)
(*  [set: T] or setT == the full set (the A containing all x : T)             *)
(*           [set x] == the singleton {x}                                     *)
(*          [set~ x] == the complement of the singleton {x}                   *)
(*         [set:: s] == the set spanned by the sequence s                     *)
(* [set a1; a2;...; an] := a1 |: [set a2] :|: ... :|: [set an]                *)
(*           A :|: B == the union of A and B                                  *)
(*            x |: A == A with the element x added (:= [set x] :|: A)         *)
(*           A :&: B == the intersection of A and B                           *)
(*              ~: A == the complement of A                                   *)
(*           A :\: B == the difference A minus B                              *)
(*            A :\ x == A with the element x removed (:= A :\: [set x])       *)
(* \bigcup_<range> A == the union of all A, for i in <range> (i is bound in   *)
(*                      A, see bigop.v)                                       *)
(* \bigcap_<range> A == the intersection of all A, for i in <range>           *)
(*           cover P == the union of the set of sets P                        *)
(*        trivIset P <=> the elements of P are pairwise disjoint              *)
(*     partition P A <=> P is a partition of A                                *)
(*        pblock P x == a block of P containing x, or else set0               *)
(* equivalence_partition R D == the partition induced on D by the relation R  *)
(*                       (provided R is an equivalence relation in D)         *)
(* preim_partition f D == the partition induced on D by the equivalence       *)
(*                      [rel x y | f x == f y]                                *)
(* is_transversal X P D <=> X is a transversal of the partition P of D        *)
(*   transversal P D == a transversal of P, provided P is a partition of D    *)
(* transversal_repr x0 X B == a representative of B \in P selected by the     *)
(*                      transversal X of P, or else x0                        *)
(*        powerset A == the set of all subset of the set A                    *)
(*          P ::&: A == those sets in P that are subsets of the set A         *)
(*        setX A1 A2 == cartesian product of A1 and A2                        *)
(*                   := [set u | u.1 \in A1 & u.2 \in A2]                     *)
(*       setXn I f A == indexed cartesian product of                          *)
(*                      A : forall i : I, {set f i}                           *)
(*         f @^-1: A == the preimage of the collective predicate A under f    *)
(*            f @: A == the image set of the collective predicate A by f      *)
(*       f @2:(A, B) == the image set of A x B by the binary function f       *)
(*  [set E | x in A] == the set of all the values of the expression E, for x  *)
(*                      drawn from the collective predicate A                 *)
(* [set E | x in A & P] == the set of values of E for x drawn from A, such    *)
(*                      that P is true                                        *)
(* [set E | x in A, y in B] == the set of values of E for x drawn from A and  *)
(*                      and y drawn from B; B may depend on x                 *)
(* [set E | x in A, y in B & P] == the set of values of E for x drawn from A  *)
(*                      y drawn from B, such that P is true                   *)
(*   [set E | x : T] == the set of all values of E, with x in type T          *)
(* [set E | x : T & P] == the set of values of E for x : T s.t. P is true     *)
(* [set E | x : T, y : U in B], [set E | x : T, y : U in B & P],              *)
(* [set E | x : T in A, y : U], [set E | x : T in A, y : U & P],              *)
(* [set E | x : T, y : U], [set E | x : T, y : U & P]                         *)
(*                   == type-ranging versions of the binary comprehensions    *)
(* [set E | x : T in A], [set E | x in A, y], [set E | x, y & P], etc.        *)
(*                   == typed and untyped variants of the comprehensions above*)
(*                      The types may be required as type inference processes *)
(*                      E before considering A or B. Note that type casts in  *)
(*                      the binary comprehension must either be both present  *)
(*                      or absent and that there are no untyped variants for  *)
(*                      single-type comprehension as Coq parsing confuses     *)
(*                      [x | P] and [E | x].                                  *)
(*        minset p A == A is a minimal set satisfying p                       *)
(*        maxset p A == A is a maximal set satisfying p                       *)
(*          unset1 A == [pick x in A] if #|A| == 1, else None                 *)
(* fprod_pick I T_ p == pick a function of type (forall i : I, T_ i) provided *)
(*                      a proof p of 0 < #|fprod I T_| is given               *)
(* ftagged I T_ p f i == untag (fprod_pick I T_ p) i (fun x=>x) (f i), useful *)
(*   to lift f : {ffun I -> {i : I & T_ i}} (akin to FProd's building blocks) *)
(*   to a vanilla dependent function of type (forall i : I, T_ i).            *)
(* Provided a monotonous function F : {set T} -> {set T}, we get fixpoints    *)
(*      fixset F := iter #|T| F set0                                          *)
(*               == the least fixpoint of F                                   *)
(*               == the minimal set such that F X == X                        *)
(* fix_order F x == the minimum number of iterations so that                  *)
(*                  x is in iter (fix_order F x) F set0                       *)
(*     funsetC F := fun X => ~: F (~: X)                                      *)
(*    cofixset F == the greatest fixpoint of F                                *)
(*               == the maximal set such that F X == X                        *)
(*               := ~: fixset (funsetC F)                                     *)
(* We also provide notations A :=: B, A :<>: B, A :==: B, A :!=: B, A :=P: B  *)
(* that specialize A = B, A <> B, A == B, etc., to {set _}. This is useful    *)
(* for subtypes of {set T}, such as {group T}, that coerce to {set T}.        *)
(*   We give many lemmas on these operations, on card, and on set inclusion.  *)
(* In addition to the standard suffixes described in ssrbool.v, we associate  *)
(* the following suffixes to set operations:                                  *)
(*  0 -- the empty set, as in in_set0 : (x \in set0) = false                  *)
(*  T -- the full set, as in in_setT : x \in [set: T]                         *)
(*  1 -- a singleton set, as in in_set1 : (x \in [set a]) = (x == a)          *)
(*  2 -- an unordered pair, as in                                             *)
(*          in_set2 : (x \in [set a; b]) = (x == a) || (x == b)               *)
(*  C -- complement, as in setCK : ~: ~: A = A                                *)
(*  I -- intersection, as in setIid : A :&: A = A                             *)
(*  U -- union, as in setUid : A :|: A = A                                    *)
(*  D -- difference, as in setDv : A :\: A = set0                             *)
(*  S -- a subset argument, as in                                             *)
(*         setIS: B \subset C -> A :&: B \subset A :&: C                      *)
(* These suffixes are sometimes preceded with an `s' to distinguish them from *)
(* their basic ssrbool interpretation, e.g.,                                  *)
(*  card1 : #|pred1 x| = 1 and cards1 : #|[set x]| = 1                        *)
(* We also use a trailing `r' to distinguish a right-hand complement from     *)
(* commutativity, e.g.,                                                       *)
(*  setIC : A :&: B = B :&: A and setICr : A :&: ~: A = set0.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope set_scope.

Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Definition set_of := set_type.
Identity Coercion type_of_set_of : set_of >-> set_type.

Definition set_isSub := Eval hnf in [isNew for finfun_of_set].
HB.instance Definition _ := set_isSub.
HB.instance Definition _ := [Finite of set_type by <:].

End SetType.

Delimit Scope set_scope with SET.
Bind Scope set_scope with set_type.
Bind Scope set_scope with set_of.
Open Scope set_scope.
Arguments set_of T%_type.
Arguments finfun_of_set {T} A%_SET.

Notation "{ 'set' T }" := (set_of T) (format "{ 'set'  T }") : type_scope.

(* We later define several subtypes that coerce to set; for these it is       *)
(* preferable to state equalities at the {set _} level, even when comparing   *)
(* subtype values, because the primitive "injection" tactic tends to diverge  *)
(* on complex types (e.g., quotient groups). We provide some parse-only       *)
(* notation to make this technicality less obstructive.                       *)
Notation "A :=: B" := (A = B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :<>: B" := (A <> B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :==: B" := (A == B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :!=: B" := (A != B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :=P: B" := (A =P B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.


HB.lock
Definition finset (T : finType) (P : pred T) : {set T} := @FinSet T (finfun P).
Canonical finset_unlock := Unlockable finset.unlock.

(* The weird type of pred_of_set is imposed by the syntactic restrictions on  *)
(* coercion declarations; it is unfortunately not possible to use a functor   *)
(* to retype the declaration, because this triggers an ugly bug in the Coq    *)
(* coercion chaining code.                                                    *)
HB.lock
Definition pred_of_set T (A : set_type T) : fin_pred_sort (predPredType T)
:= val A.
Canonical pred_of_set_unlock := Unlockable pred_of_set.unlock.

Notation "[ 'set' x : T | P ]" := (finset (fun x : T => P%B))
  (x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (P at level 99, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A ]" := [set x | x \in A]
  (format "[ 'set'  x  'in'  A ]") : set_scope.
Notation "[ 'set' x : T 'in' A ]" := [set x : T | x \in A]
  (only parsing) : set_scope.
Notation "[ 'set' x : T | P & Q ]" := [set x : T | P && Q]
  (only parsing) : set_scope.
Notation "[ 'set' x | P & Q ]" := [set x | P && Q ]
  (P at level 99, format "[ 'set'  x  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P ]" := [set x : T | x \in A & P]
  (only parsing) : set_scope.
Notation "[ 'set' x 'in' A | P ]" := [set x | x \in A & P]
  (format "[ 'set'  x  'in'  A  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A | P & Q ]" := [set x in A | P && Q]
  (format "[ 'set'  x  'in'  A  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P & Q ]" := [set x : T in A | P && Q]
  (only parsing) : set_scope.

Notation "[ 'set' :: s ]" := (finset [in pred_of_seq s])
  (format "[ 'set' ::  s ]") : set_scope.

(* This lets us use set and subtypes of set, like group or coset_of, both as  *)
(* collective predicates and as arguments of the \pi(_) notation.             *)
Coercion pred_of_set: set_type >-> fin_pred_sort.

(* Declare pred_of_set as a canonical instance of topred, but use the         *)
(* coercion to resolve mem A to @mem (predPredType T) (pred_of_set A).        *)
Canonical set_predType T := @PredType _ (unkeyed (set_type T)) (@pred_of_set T).

Section BasicSetTheory.

Variable T : finType.
Implicit Types (x : T) (A B : {set T}) (pA : pred T).

HB.instance Definition _ := Finite.on {set T}.

Lemma in_set pA x : (x \in finset pA) = pA x.
Proof.
Admitted.
Let PPx x : x \in D -> Px x \in P := fun Dx => imset_f _ Dx.

Lemma equivalence_partitionP : partition P D.
Proof.
Admitted.

Let sXP : {subset X <= cover P}.
Proof.
Admitted.

Let trX : {in P, forall B, #|X :&: B| == 1}.
Proof.
Admitted.

Lemma setI_transversal_pblock x0 B :
  B \in P -> X :&: B = [set transversal_repr x0 X B].
Proof.
Admitted.

Definition ftagged (T_gt0 : 0 < #|fprod T_|)
  (f : {ffun I -> {i : I & T_ i}}) (i : I) :=
    @untag I T_ (T_ i) (fprod_pick T_gt0 i) i id (f i).

Lemma ftaggedE t T_gt0 i : ftagged T_gt0 (fprod_fun t) i = t i.
Proof.
Admitted.

End FProd.

Section BigTag.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Variables (I : finType) (T_ : I -> finType).

Lemma big_tag_cond  (Q_ : forall i, {pred T_ i})
      (P_ : forall i : I, T_ i -> R) (i : I) :
  \big[op/idx]_(j in Q_ i) P_ i j =
  \big[op/idx]_(j in tagged_with T_ i | untag true (Q_ i) j)
     untag idx (P_ i) j.
Proof.
Admitted.

Lemma big_tag (P_ : forall i : I, T_ i -> R) (i : I) :
  \big[op/idx]_(j : T_ i) P_ i j =
  \big[op/idx]_(j in tagged_with T_ i) untag idx (P_ i) j.
Proof.
Admitted.

End BigTag.

Arguments big_tag_cond [R idx op I T_] _ _ _.
Arguments big_tag [R idx op I T_] _ _.

Section BigFProd.
  Variables (R : Type) (zero one : R) (times : R -> R -> R).
  Variables (plus : Monoid.add_law zero times).
  Variables (I : finType) (T_ : I -> finType).
  Variables (P_ : forall i : I, {ffun T_ i -> R}).
  Let T := fprod T_.

  Lemma big_fprod_dep (Q : {pred {ffun I -> {i : I &  (T_ i)}}}) :
    \big[plus/zero]_(t : T | Q (fprod_fun t)) \big[times/one]_(i : I) P_ i (t i) =
    \big[plus/zero]_(g in family (tagged_with T_) | Q g)
     \big[times/one]_(i : I) (untag zero (P_ i) (g i)).
Proof.
Admitted.

  Lemma big_fprod :
    \big[plus/zero]_(t : T) \big[times/one]_(i in I) P_ i (t i) =
    \big[plus/zero]_(g in family (tagged_with T_))
     \big[times/one]_(i : I) (untag zero (P_ i) (g i)).
Proof.
Admitted.

End BigFProd.
