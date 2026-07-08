(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype prime bigop finset fingroup morphism.
From mathcomp Require Import automorphism quotient action cyclic gproduct .
From mathcomp Require Import gfunctor commutator pgroup center nilpotent.

(******************************************************************************)
(*   The Sylow theorem and its consequences, including the Frattini argument, *)
(* the nilpotence of p-groups, and the Baer-Suzuki theorem.                   *)
(*   This file also defines:                                                  *)
(*      Zgroup G == G is a Z-group, i.e., has only cyclic Sylow p-subgroups.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope group_scope.

(* The mod p lemma for the action of p-groups. *)
Section ModP.

Variable (aT : finGroupType) (sT : finType) (D : {group aT}).
Variable to : action D sT.

Lemma pgroup_fix_mod (p : nat) (G : {group aT}) (S : {set sT}) :
  p.
Proof.
Admitted.

End ModP.

Section ModularGroupAction.

Variables (aT rT : finGroupType) (D : {group aT}) (R : {group rT}).
Variables (to : groupAction D R) (p : nat).
Implicit Types (G H : {group aT}) (M : {group rT}).

Lemma nontrivial_gacent_pgroup G M :
    p.
Proof.
Admitted.

Lemma pcore_sub_astab_irr G M :
    p.
Proof.
Admitted.

Lemma pcore_faithful_irr_act G M :
    p.
Proof.
Admitted.

End ModularGroupAction.

Section Sylow.

Variables (p : nat) (gT : finGroupType) (G : {group gT}).
Implicit Types P Q H K : {group gT}.

Theorem Sylow's_theorem :
  [/\ forall P, [max P | p.
Proof.
Admitted.

Lemma max_pgroup_Sylow P : [max P | p.
Proof.
Admitted.

Lemma Sylow_superset Q :
  Q \subset G -> p.
Proof.
Admitted.

Lemma Sylow_exists : {P : {group gT} | p.
Proof.
Admitted.

Lemma Syl_trans : [transitive G, on 'Syl_p(G) | 'JG].
Proof.
Admitted.

Lemma Sylow_trans P Q :
  p.
Proof.
Admitted.

Lemma Sylow_subJ P Q :
    p.
Proof.
Admitted.

Lemma Sylow_Jsub P Q :
    p.
Proof.
Admitted.

Lemma card_Syl P : p.
Proof.
Admitted.

Lemma card_Syl_dvd : #|'Syl_p(G)| %| #|G|.
Proof.
Admitted.

Lemma card_Syl_mod : prime p -> #|'Syl_p(G)| %% p = 1%N.
Proof.
Admitted.

Lemma Frattini_arg H P : G <| H -> p.
Proof.
Admitted.

End Sylow.

Section MoreSylow.

Variables (gT : finGroupType) (p : nat).
Implicit Types G H P : {group gT}.

Lemma Sylow_setI_normal G H P :
  G <| H -> p.
Proof.
Admitted.

Lemma normal_sylowP G :
  reflect (exists2 P : {group gT}, p.
Proof.
Admitted.

Lemma trivg_center_pgroup P : p.
Proof.
Admitted.

Lemma p2group_abelian P : p.
Proof.
Admitted.

Lemma card_p2group_abelian P : prime p -> #|P| = (p ^ 2)%N -> abelian P.
Proof.
Admitted.

Lemma Sylow_transversal_gen (T : {set {group gT}}) G :
    (forall P, P \in T -> P \subset G) ->
    (forall p, p \in \pi(G) -> exists2 P, P \in T & p.
Proof.
Admitted.

Lemma Sylow_gen G : <<\bigcup_(P : {group gT} | Sylow G P) P>> = G.
Proof.
Admitted.

End MoreSylow.

Section SomeHall.

Variable gT : finGroupType.
Implicit Types (p : nat) (pi : nat_pred) (G H K P R : {group gT}).

Lemma Hall_pJsub p pi G H P :
    pi.
Proof.
Admitted.

Lemma Hall_psubJ p pi G H P :
    pi.
Proof.
Admitted.

Lemma Hall_setI_normal pi G K H :
  K <| G -> pi.
Proof.
Admitted.

Lemma coprime_mulG_setI_norm H G K R :
    K * R = G -> G \subset 'N(H) -> coprime #|K| #|R| ->
  (K :&: H) * (R :&: H) = G :&: H.
Proof.
Admitted.

End SomeHall.

Section Nilpotent.

Variable gT : finGroupType.
Implicit Types (G H K P L : {group gT}) (p q : nat).

Lemma pgroup_nil p P : p.
Proof.
Admitted.

Lemma pgroup_sol p P : p.
Proof.
Admitted.

Lemma small_nil_class G : nil_class G <= 5 -> nilpotent G.
Proof.
Admitted.

Lemma nil_class2 G : (nil_class G <= 2) = (G^`(1) \subset 'Z(G)).
Proof.
Admitted.

Lemma nil_class3 G : (nil_class G <= 3) = ('L_3(G) \subset 'Z(G)).
Proof.
Admitted.

Lemma nilpotent_maxp_normal pi G H :
  nilpotent G -> [max H | pi.
Proof.
Admitted.

Lemma nilpotent_Hall_pcore pi G H :
  nilpotent G -> pi.
Proof.
Admitted.

Lemma nilpotent_pcore_Hall pi G : nilpotent G -> pi.
Proof.
Admitted.

Lemma nilpotent_pcoreC pi G : nilpotent G -> 'O_pi(G) \x 'O_pi^'(G) = G.
Proof.
Admitted.

Lemma sub_nilpotent_cent2 H K G :
    nilpotent G -> K \subset G -> H \subset G -> coprime #|K| #|H| ->
  H \subset 'C(K).
Proof.
Admitted.

Lemma pi_center_nilpotent G : nilpotent G -> \pi('Z(G)) = \pi(G).
Proof.
Admitted.

Lemma Sylow_subnorm p G P : p.
Proof.
Admitted.

End Nilpotent.

Lemma nil_class_pgroup (gT : finGroupType) (p : nat) (P : {group gT}) :
  p.
Proof.
Admitted.

Definition Zgroup (gT : finGroupType) (A : {set gT}) :=
  [forall (V : {group gT} | Sylow A V), cyclic V].

Section Zgroups.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Types G H K : {group gT}.

Lemma ZgroupS G H : H \subset G -> Zgroup G -> Zgroup H.
Proof.
Admitted.

Lemma morphim_Zgroup G : Zgroup G -> Zgroup (f @* G).
Proof.
Admitted.

Lemma nil_Zgroup_cyclic G : Zgroup G -> nilpotent G -> cyclic G.
Proof.
Admitted.

End Zgroups.

Arguments Zgroup {gT} A%_g.

Section NilPGroups.

Variables (p : nat) (gT : finGroupType).
Implicit Type G P N : {group gT}.

(* B & G 1.22 p.9 *)
Lemma normal_pgroup r P N :
    p.
Proof.
Admitted.

Theorem Baer_Suzuki x G :
    x \in G -> (forall y, y \in G -> p.
Proof.
Admitted.

End NilPGroups.
