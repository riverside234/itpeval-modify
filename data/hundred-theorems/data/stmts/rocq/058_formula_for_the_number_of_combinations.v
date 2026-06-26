Require Import FSets MapFunction.
Require Import Arith EqNat Euclid ArithRing ZArith.
Set Implicit Arguments.
Unset Standard Proposition Elimination Names.
Proof.
Admitted.

Lemma binomial_rec : forall n k, k<=n -> 
 (binomial n k)*(fact k * fact (n-k)) = fact n.
Proof.
Admitted.

Lemma fact_pos : forall k, fact k > 0.
Proof.
Admitted.

Lemma binomial_den_pos : forall n k, fact k * fact (n-k) > 0.
Proof.
Admitted.

Definition binomial' n k := 
 let (q,_) := quotient (fact k * fact (n-k)) (binomial_den_pos n k) (fact n)
 in q.

Lemma binomial_alt : forall n k, k<=n -> 
 binomial n k = binomial' n k.
Proof.
Admitted.


Module PowerSet (M:S).

(* M is our base sets structure. *)
(* MM is a "sets of sets" structure: *)
Module MM := FSetList.Make M.
(* Adding a map function to MM... *)
Module MM' := MapFunction.MapFunction MM.
(* Properties functors *)
Module P := FSetProperties.Properties M.
Module P' := FSetProperties.OrdProperties M.
Module F := P.FM.
Module PEP := FSetEqProperties.EqProperties MM.
Module PP := PEP.MP.
Module FF := PP.FM.
Module ME := OrderedTypeFacts M.E.

Infix "[=]" := M.Equal (at level 70, no associativity).
Infix "[==]" := MM.Equal (at level 70, no associativity).

(** Computing the set of all subsets of a particular set [s] *)

Definition powerset s := 
  M.fold 
   (fun (x:M.elt)(ss:MM.t) => MM.union ss (MM'.map (M.add x) ss)) 
   s 
   (MM.singleton M.empty).

(** Proofs about powerset *)

Lemma map_add : forall s s' x, MM.
Proof.
Admitted.

Lemma compat_op_pow :
 compat_op M.
Proof.
Admitted.
Hint Resolve compat_op_pow : set.

Lemma singleton_empty : forall s, MM.
Proof.
Admitted.

Lemma powerset_base : forall s, M.
Proof.
Admitted.

Lemma powerset_step : forall s1 s2 x, P'.
Proof.
Admitted.

Lemma powerset_is_powerset: 
 forall s s', MM.
Proof.
Admitted.

Lemma powerset_cardinal: 
 forall s, MM.
Proof.
Admitted.

(** Computing the set of all subsets of cardinal k for a particular set [s] *)

Definition powerset_k s k := 
 MM.filter (fun s => beq_nat (M.cardinal s) k) (powerset s).


(** Proofs about powerset_k *)

Lemma powerset_k_is_powerset_k : forall k s s', 
 MM.
Proof.
Admitted.

Lemma powerset_k_cardinal : forall s k, 
 MM.
Proof.
Admitted.

(** A more "direct" definition *)

Definition powerset_k' s := 
  M.fold 
  (fun (x:M.elt)(ff:nat->MM.t)(k:nat) => match k with 
    | O => ff 0
    | S k' => MM.union (ff k) (MM'.map (M.add x) (ff k'))
   end) 
  s 
  (fun k => if k then MM.singleton M.empty else MM.empty).

Lemma powerset_k'_is_powerset_k : 
 forall s s' k, MM.
Proof.
Admitted.

Lemma powerset_k_alt : 
 forall s k, powerset_k' s k [==] powerset_k s k.
Proof.
Admitted.

End PowerSet.

(** An example: *)

Open Scope positive_scope.

Module P := FSetList.Make Positive_as_OT.
Module PS := PowerSet P.
Module PP := PS.MM.

(* The set containing numbers 1..n *)
Fixpoint interval (n:nat) {struct n} : P.t := match n with 
 | O => P.empty
 | S n => P.add (P_of_succ_nat n) (interval n)
 end.

Eval vm_compute in P.elements (interval 10).

Definition powerset_5 := PS.powerset (interval 5).

Eval vm_compute in map P.elements (PP.elements powerset_5).

Definition subsets_size2_in5 := PS.powerset_k' (interval 5) 2. 

Eval vm_compute in map P.elements (PP.elements subsets_size2_in5).





