Require Import QArith.
Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Export ConditionalExpectation.
Require Import RbarExpectation.

Require Import Event.
Require Import Almost DVector.
Require Import utils.Utils.
Require Import List.
Require Import PushNeg.
Require Import Reals.
Require Import Coquelicot.Rbar Coquelicot.Lim_seq.

Require Import Martingale.

Set Bullet Behavior "Strict Subproofs". 

Section stopped_process.

  Local Open Scope R.
  Local Existing Instance Rge_pre.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rle_pre.
  
  Context {Ts:Type}.

    Definition lift1_min (x:nat) (y : option nat)
      := match y with
         | None => x
         | Some b => min x b
         end.
    
  Lemma lift1_lift2_min (x:nat) (y : option nat) :
    lift2_min (Some x) y = Some (lift1_min x y).
Proof.
Admitted.

    Global Instance process_stopped_at_adapted 
           {adapt:IsAdapted borel_sa Y F} :
      IsAdapted borel_sa (process_stopped_at Y T) F.
    Proof.
Admitted.

    Global Instance process_stopped_at_isfe
           {rv:forall n, RandomVariable dom borel_sa (Y n)}
           {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      forall n, IsFiniteExpectation prts (process_stopped_at Y T n).
    Proof.
Admitted.

    Instance process_stopped_at_alt_rv
             {rv:forall n, RandomVariable dom borel_sa (Y n)} :
      forall n, RandomVariable dom borel_sa (process_stopped_at_alt Y T n).
    Proof.
Admitted.

    Instance process_stopped_at_alt_isfe
           {rv:forall n, RandomVariable dom borel_sa (Y n)}
           {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      forall n, IsFiniteExpectation prts (process_stopped_at_alt Y T n).
    Proof.
Admitted.

    Instance process_stopped_at_alt_adapted 
           {adapt:IsAdapted borel_sa Y F} :
      IsAdapted borel_sa (process_stopped_at_alt Y T) F.
    Proof.
Admitted.

    Lemma process_stopped_at_alt_diff1_eq n :
      rv_eq (rvminus
               (process_stopped_at_alt Y T (S n))
               (process_stopped_at_alt Y T n))
            (rvmult
               (rvminus
                  (Y (S n))
                  (Y n))
               (EventIndicator (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n%nat))))).
Proof.
Admitted.

    Instance process_stopped_at_alt_diff1_isfe n
             {rv:forall n, RandomVariable dom borel_sa (Y n)}
             {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      IsFiniteExpectation prts
            (rvmult (rvminus (Y (S n)) (Y n))
               (EventIndicator
                  (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n))))).
    Proof.
Admitted.

    Lemma process_stopped_at_sub_martingale
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
      IsMartingale prts Rle (process_stopped_at Y T) F.
Proof.
Admitted.

  End process_under_props.

  Section opt_stop_thm.

    Context (Y : nat -> Ts -> R) (F : nat -> SigmaAlgebra Ts)
            {filt:IsFiltration F}
            {sub:IsSubAlgebras dom F}
            (T:Ts -> option nat)
            {is_stop:IsStoppingTime T F}.

    Section variant_a.

      Context (N:nat)
              (Nbound:almost prts (fun ts => match T ts with
                                          | Some k => (k <= N)%nat
                                          | None => False
                                          end)).
      
    Instance optional_stopping_time_a_isfe
             {rv:forall n, RandomVariable dom borel_sa (Y n)}
             {isfe:forall n, IsFiniteExpectation prts (Y n)} :
      IsFiniteExpectation prts (process_under Y T).
    Proof.
Admitted.

    Lemma optional_stopping_time_a_stopped_eq :
      almostR2 prts eq (process_stopped_at Y T N) (process_under Y T).
Proof.
Admitted.

      (* this should replace the existing rvlim *)
      Global Instance rvlim_rv' (f: nat -> Ts -> R)
             {rv : forall n, RandomVariable dom borel_sa (f n)} :
        RandomVariable dom borel_sa (rvlim f).
      Proof.
Admitted.

      Instance optional_stopping_time_b_isfe'
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        Rbar_IsFiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
      Proof.
Admitted.
        
      Lemma optional_stopping_time_b_eq
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        FiniteExpectation prts (process_under Y T) =
          Rbar_FiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
Proof.
Admitted.

      Lemma optional_stopping_time_sub_c_Kbound_stopped_telescope :
        forall n : nat, rv_eq (process_stopped_at Y T n)
                          (rvplus
                             (Y 0%nat)
                             (fun ts => match lift1_min n (T ts) with
                              | 0%nat => 0%R
                              | S n =>
                                  rvsum (fun k => rvminus (Y (S k)) (Y k)) n ts
                              end)).
Proof.
Admitted.
    
      Instance optional_stopping_time_sub_c_Kbound_isfe
               {rv:forall n, RandomVariable dom borel_sa (Y n)}
               {isfe:forall n, IsFiniteExpectation prts (Y n)} :
        Rbar_IsFiniteExpectation prts optional_stopping_time_sub_c_Kbound.
      Proof.
Admitted.

      Lemma optional_stopping_time_sub_c_Kbound_stopped :
        forall n : nat, almostR2 prts Rbar_le (rvabs (process_stopped_at Y T n))
                          optional_stopping_time_sub_c_Kbound.
Proof.
Admitted.

      Instance optional_stopping_time_c_isfe'
               {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        Rbar_IsFiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
      Proof.
Admitted.
        
      Lemma optional_stopping_time_c_eq
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        FiniteExpectation prts (process_under Y T) =
          Rbar_FiniteExpectation prts (Rbar_rvlim (process_stopped_at Y T)).
Proof.
Admitted.

      Lemma optional_stopping_time_c_helper
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
      is_lim_seq
        (fun n : nat => Rbar_FiniteExpectation prts (fun x : Ts => process_stopped_at Y T n x) (isfe:= (IsFiniteExpectation_Rbar prts (fun x : Ts => process_stopped_at Y T n x)
                                                      (process_stopped_at_isfe Y F T n))))
        (Rbar_FiniteExpectation prts
                                (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x))).
Proof.
Admitted.

      Lemma optional_stopping_time_c_helper'
            {rv:forall n, RandomVariable dom borel_sa (Y n)}
            {isfe:forall n, IsFiniteExpectation prts (Y n)} 
            {adapt:IsAdapted borel_sa Y F} :
        Lim_seq 
        (fun n : nat => Rbar_FiniteExpectation prts (fun x : Ts => process_stopped_at Y T n x) (isfe:= (IsFiniteExpectation_Rbar prts (fun x : Ts => process_stopped_at Y T n x)
                                                      (process_stopped_at_isfe Y F T n)))) = 
        Finite (Rbar_FiniteExpectation prts
                                (Rbar_rvlim (fun (n : nat) (x : Ts) => process_stopped_at Y T n x))).
Proof.
Admitted.

      Lemma optional_stopping_time_c
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts eq Y F} :
         FiniteExpectation prts (process_under Y T) = FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.

      Lemma optional_stopping_time_sub_c
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rle Y F} :
        FiniteExpectation prts (process_under Y T) >= FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.

      Lemma optional_stopping_time_super_c
          {rv:forall n, RandomVariable dom borel_sa (Y n)}
          {isfe:forall n, IsFiniteExpectation prts (Y n)} 
          {adapt:IsAdapted borel_sa Y F}
          {mart:IsMartingale prts Rge Y F} :
        FiniteExpectation prts (process_under Y T) <= FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.
      
    End variant_c.
  End opt_stop_thm.

End stopped_process.


Local Existing Instance Rge_pre.
Local Existing Instance Rle_pre.

Section optional_stopping_time_thm.
  (** * Optional Stopping Theorem (Fair Games Theorem) *)
  (** This presents a statement and proof of the optional stopping time theorem, 
     also known as the fair games theorem, for discrete-time (sub/super)-martingales
     over general probability spaces.
Proof.
Admitted.

  Theorem optional_stopping_time
          {mart:IsMartingale prts eq Y F} (**r If the stochastic process is a martingale with respect to the filtration *)
    : (**r then the expectation of the stopped process is the same as when the process started  *)
    FiniteExpectation prts (process_under Y τ) = FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.
    
  Theorem optional_stopping_time_sub
          {mart:IsMartingale prts Rle Y F} (**r If the stochastic process is a sub-martingale with respect to the filtration *)
    : (**r then the expectation of the stopped process is greater than or equal to when the process started  *)
    FiniteExpectation prts (process_under Y τ) >= FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.
    
  Theorem optional_stopping_time_super
          {mart:IsMartingale prts Rge Y F} (**r If the stochastic process is a super-martingale with respect to the filtration *)
    : (**r then the expectation of the stopped process is less than or equal to when the process started  *)
    FiniteExpectation prts (process_under Y τ) <= FiniteExpectation prts (Y 0%nat).
Proof.
Admitted.

End optional_stopping_time_thm.
