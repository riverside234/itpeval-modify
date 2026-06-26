Require Import Lra Lia Reals RealAdd RandomVariableL2 Coquelicot.Coquelicot.
Require Import Morphisms FiniteType List ListAdd Permutation infprod Almost NumberIso.
Require Import Sums SimpleExpectation PushNeg.
Require Import EquivDec.
Require Import Classical.
Require Import ClassicalChoice.
Require Import IndefiniteDescription ClassicalDescription.
Require Import BorelSigmaAlgebra.
Require Import utils.Utils.
Require Import ConditionalExpectation.
Require Import Independence.
Require Import sumtest.
Require Import Dynkin.
Require Import Measures.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Proof.
Admitted.

Instance partition_measurable_event_equiv (f : Ts -> R)
   {frf : FiniteRangeFunction f}
   {rvf : RandomVariable dom borel_sa f} :
  Proper (Forall2 event_equiv ==> iff) (partition_measurable f).
Proof.
Admitted.  

Lemma part_meas_refine_commute
      (f : Ts -> R) 
      (l1 l2 : list dec_sa_event)
      {frf : FiniteRangeFunction f}
      {rvf : RandomVariable dom borel_sa f} :
  partition_measurable f (map dsa_event
                              (refine_dec_sa_partitions l1 l2)) <->
  partition_measurable f (map dsa_event
                              (refine_dec_sa_partitions l2 l1)).
Proof.
Admitted.

Existing Instance isfe_l2_prod.
Existing Instance isfe_sqr_seq.

Lemma expec_cross_zero_filter (X : nat -> Ts -> R)
      {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {frf2 : forall (k:nat), IsFiniteExpectation Prts (rvsqr (X k))} 
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                (const 0))  :
  forall (j k : nat), 
    (j < k)%nat ->
    FiniteExpectation Prts (rvmult (X j) (X k)) = 0.
Proof.
Admitted. 

Global Instance nnf_cutoff_eps_rv (n : nat) (eps : R) (X : nat -> Ts -> R) 
         {nnf: forall n, NonnegativeFunction (X n)} :
  NonnegativeFunction (cutoff_eps_rv n eps X).
Proof.
Admitted.

Lemma cutoff_eps_values (n : nat) (eps : R) (X : nat -> Ts -> R) :
  forall (x:Ts),
  exists (k : nat), 
    (k <= n)%nat /\
    cutoff_eps_rv n eps X x = X k x.
Proof.
Admitted.

Local Obligation Tactic := unfold complement, equiv; Tactics.program_simpl.

Lemma cutoff_eps_succ_minus eps (X : nat -> R) :
  forall n, cutoff_eps (S n) eps X - cutoff_eps n eps X =
       if (Rlt_dec (Rmax_list_map (seq 0 (S n)) (fun n => Rabs (X n))) eps) then
         (X (S n) - X n) else 0.
Proof.
Admitted.

Global Instance cutoff_ind_rv (j:nat) (eps:R) (X: nat -> Ts -> R) 
      {rv : forall n, (n<=j)%nat -> RandomVariable dom borel_sa (X n)} :
  RandomVariable dom borel_sa
                 (cutoff_indicator (S j) eps (rvsum X)).
Proof.
Admitted.

  Lemma partition_measurable_rvplus (rv_X1 rv_X2 : Ts -> R)
        {rv1 : RandomVariable dom borel_sa rv_X1}
        {rv2 : RandomVariable dom borel_sa rv_X2} 
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2}         
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable  rv_X1 l ->
    partition_measurable  rv_X2 l ->     
    partition_measurable  (rvplus rv_X1 rv_X2) l.
Proof.
Admitted.

  Lemma IsFiniteExpectation_rvmult_rvmaxlist1 F G k
        {rvF:forall n, RandomVariable dom borel_sa (F n)}
        {rvG:RandomVariable dom borel_sa G}
    :
    (forall a, (a <= k)%nat ->
            IsFiniteExpectation Prts (rvmult (F a) G)) ->
    IsFiniteExpectation Prts
                        (rvmult (rvmaxlist F k) G).
Proof.
Admitted.

  Instance isfe_Sum1_from_crossmult X m
        {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
        {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))} :
    let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
    forall a b, IsFiniteExpectation Prts (rvmult (X a) (Sum b)).
  Proof.
Admitted.

  Instance isfe_Sum_from_crossmult X m
           {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
           {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))} :
    let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
    forall a b, IsFiniteExpectation Prts (rvmult (Sum a) (Sum b)).
  Proof.
Admitted.

  Instance isfe_sqr_Sum X m
           {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
           {isfe2 : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k))} :
    forall a,
      IsFiniteExpectation Prts (rvsqr (rvsum (fun n => X (n + m)%nat) a)).
  Proof.
Admitted.

  Lemma ash_6_1_4_filter (X: nat -> Ts -> R) {F : nat -> SigmaAlgebra Ts}
      (isfilt : IsFiltration F)
      (filt_sub : forall n, sa_sub (F n) dom)
      {adapt : IsAdapted borel_sa X F}
      (eps:posreal) (m:nat)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      (isfesqr : forall k : nat, IsFiniteExpectation Prts (rvsqr (X k)))
      (HC : forall n, 
          almostR2 Prts eq
                   (ConditionalExpectation Prts (filt_sub n) (X (S n)))
                   (const 0))  :

  let Sum := fun j => (rvsum (fun n => X (n + m)%nat) j) in
  (* Note that this is derivable from isfemult *)
  forall (isfe2: forall n, IsFiniteExpectation _ ((rvsqr (Sum n)))), 
  forall (n:nat), ps_P (event_ge dom (rvmaxlist (fun k => rvabs(Sum k)) n) eps) <=
             FiniteExpectation _ (rvsqr (Sum n))/eps^2.
Proof.
Admitted.

Transparent rv_max_sum_shift.

  Lemma event_ge_pf_irrel {x}
        {rv_X : Ts -> R}
        {rv1 : RandomVariable dom borel_sa rv_X}
        {rv2 : RandomVariable dom borel_sa rv_X} :
    event_equiv (event_ge dom rv_X (rv:=rv1) x)
                (event_ge dom rv_X (rv:=rv2) x).
Proof.
Admitted.

  Lemma pre_event_inter_pre_list_inter_combine (l1 l2:list (pre_event Ts)) :
    length l1 = length l2 ->
    pre_event_equiv (pre_event_inter (pre_list_inter l1) (pre_list_inter l2))
                    (pre_list_inter (map (fun '(x, y) => pre_event_inter x y) (combine l1 l2))).
Proof.
Admitted.

  Global Instance list_union_sub_proper {A} {σ:SigmaAlgebra A} :
    Proper (Forall2 event_sub ==> event_sub) (@list_union A σ).
  Proof.
Admitted.

  Global Instance list_inter_proper {A} {σ:SigmaAlgebra A}  :
    Proper (Forall2 event_equiv ==> event_equiv) (@list_inter A σ).
  Proof.
Admitted.

   Global Instance list_union_proper {A} {σ:SigmaAlgebra A}  :
    Proper (Forall2 event_equiv ==> event_equiv) (@list_union A σ).
  Proof.
Admitted.

  Global Instance list_inter_incl_proper {A} {σ:SigmaAlgebra A}  :
    Proper (@incl _ --> event_sub) (@list_inter A σ).
  Proof.
Admitted.

  Global Instance list_inter_equivlist_proper {A} {σ:SigmaAlgebra A}  :
    Proper (@equivlist _ ==> event_equiv) (@list_inter A σ).
  Proof.
Admitted.
  
  Definition independent_eventcoll_collection {Idx} (doms:Idx -> pre_event Ts -> Prop)
    := forall (A:Idx -> event dom),
      (forall n, (doms n) (A n)) ->
      independent_event_collection Prts A.


  Instance measure_proper_fin {T} {σ : SigmaAlgebra T} (μ : event σ -> R) {μ_meas:is_measure μ}
    : Proper (event_equiv ==> eq) μ.
  Proof.
Admitted.    
  
  Lemma measure_complement {T} {σ : SigmaAlgebra T} (μ : event σ -> R) {μ_meas:is_measure μ} A :
    μ (event_complement A) = μ Ω - μ A.
Proof.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.

  (*  measure_all_one_ps in Measures *)
  
  Definition independent_eventcoll_collection_μ2 (l : list (event dom)) : event dom -> R
    := fun x => ps_P x * ps_P (list_inter l).

  Program Instance independent_eventcoll_collection_μ2_is_measure (l : list (event dom)) :
    is_measure (independent_eventcoll_collection_μ2 l).
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.

  Definition measure_sa_sub {T} {σ1 σ2 : SigmaAlgebra T} (sub:sa_sub σ2 σ1) (μ: event σ1 -> Rbar) : event σ2 -> Rbar
    := fun x => μ (event_sa_sub sub x).

  Global Instance measure_sa_sub_is_measure {T}
         {σ1 σ2 : SigmaAlgebra T} (sub:sa_sub σ2 σ1) (μ: event σ1 -> Rbar)
         {μ_meas:is_measure μ} : is_measure (measure_sa_sub sub μ).
  Proof.
Admitted.
  
  Definition measure_sa_sub_fin {T} {σ1 σ2 : SigmaAlgebra T} (sub:sa_sub σ2 σ1) (μ: event σ1 -> R) : event σ2 -> R
    := fun x => μ (event_sa_sub sub x).

  Global Instance measure_sa_sub_fin_is_measure {T}
         {σ1 σ2 : SigmaAlgebra T} (sub:sa_sub σ2 σ1) (μ: event σ1 -> R)
         {μ_meas:is_measure μ} : is_measure (measure_sa_sub_fin sub μ).
  Proof.
Admitted.

  Global Instance fold_right_Rmult1_perm_proper :
    Proper (@Permutation R ==> eq) (fold_right Rmult 1).
  Proof.
Admitted.

  Lemma NoDup_remove_val {A} (l : list A) (a : A) {eqdec : EqDec A eq} :
    NoDup l ->
    forall b,
      In b (remove_one a l) -> b <> a.
Proof.
Admitted.


  Lemma independent_sas_join1  (sas : nat -> SigmaAlgebra Ts) 
        {sub:IsSubAlgebras dom sas} :
    independent_sa_collection Prts sas ->
    let sas2 := fun (n:nat) => match n with
                              | 0%nat => union_sa (sas 0%nat) (sas 1%nat)
                              | S n' => sas (S n)
                              end    in
    independent_sa_collection Prts sas2.
Proof.
Admitted.

  Lemma independent_sas_join_n  (sas : nat -> SigmaAlgebra Ts)  (n:nat)
        {sub:IsSubAlgebras dom sas} :
    independent_sa_collection Prts sas ->
    let sas2 := fun (n0:nat) => match n0 with
                              | 0%nat => filtrate_sa sas n
                              | S n' => sas (n0 + n)%nat
                              end    in
    independent_sa_collection Prts sas2.
Proof.
Admitted.

   Lemma finexp_sqr_scale (X : Ts -> R) (c: R) 
         {isfe : IsFiniteExpectation Prts (rvsqr X)} :
     FiniteExpectation Prts (rvsqr (rvscale c X)) = 
     Rsqr c * FiniteExpectation Prts (rvsqr X).
Proof.
Admitted.
     

  Lemma event_lt_indicator_sum (X : Ts -> R) (n : nat) 
        {rv: RandomVariable dom borel_sa X} :
    rv_eq
      (EventIndicator (classic_dec (event_lt dom (rvabs X) (INR n + 1))))
      (rvsum (fun k => EventIndicator (classic_dec 
                                         (event_inter
                                            (event_lt dom (rvabs X) (INR k + 1))
                                            (event_ge dom (rvabs X) (INR k)))))
             n).
Proof.
Admitted.

  Lemma event_lt_indicator_sum_mult (X Y : Ts -> R) (n : nat) 
        {rv: RandomVariable dom borel_sa X} :
    rv_eq
      (rvmult Y (EventIndicator (classic_dec (event_lt dom (rvabs X) (INR n + 1)))))
      (rvsum (fun k => rvmult Y (EventIndicator (classic_dec 
                                         (event_inter
                                            (event_lt dom (rvabs X) (INR k + 1))
                                            (event_ge dom (rvabs X) (INR k))))))
             n).
Proof.
Admitted.

   Lemma ELim_seq_ind_le (f : nat -> R) (x : nat) :
     ELim_seq
       (sum_Rbar_n
          (fun n0 : nat =>
             (if Compare_dec.
Proof.
Admitted.

   Lemma Rbar_mult_le_nneg (f g : Rbar) :
     Rbar_le 0 f -> Rbar_le 0 g ->
     Rbar_le 0 (Rbar_mult f g).
Proof.
Admitted.

   Lemma scale_pos_sum_Rbar_n (f : nat -> Rbar) (c : R) :
     (0 < c) ->
     (forall n, Rbar_le 0 (f n)) ->
     forall n,
       Rbar_mult c (sum_Rbar_n f n) = sum_Rbar_n (fun k => Rbar_mult c (f k)) n.
Proof.
Admitted.

   Existing Instance Rbar_le_pre.

   Lemma indicator_lim_seq (X : Ts -> R)
         {rv : RandomVariable dom borel_sa (rvabs X)}
         {isfe : forall x, IsFiniteExpectation Prts
           (rvmult (rvabs X)
              (EventIndicator (classic_dec (event_lt dom (rvabs X) (INR x + 1)))))} 
         {isfe0 : IsFiniteExpectation Prts (rvabs X)} :
     Lim_seq
       (fun x : nat =>
          FiniteExpectation Prts
                            (rvmult (rvabs X)
                                    (EventIndicator
                                       (classic_dec (event_lt dom (rvabs X) (INR x + 1)))))) =
     FiniteExpectation Prts (rvabs X).
Proof.
Admitted.

   
 Lemma BC_exist_N_not_ge (Y : nat -> Ts -> R) (α : nat -> R)
       (rv: forall n k, RandomVariable dom borel_sa (rvabs (Y (n + k)%nat))) :
   ps_P
     (inter_of_collection
        (fun k : nat =>
           union_of_collection
             (fun n : nat => event_ge dom (rvabs (Y (n + k)%nat)) (α (n + k)%nat)))) =
   0 ->
  almost Prts
    (fun omega : Ts =>
     exists N : nat,
       forall n : nat, (N <= n)%nat -> rvabs (Y n) omega < (α n)).
Proof.
Admitted.

   Lemma lim_avg_tails0 (X : nat -> R) (N:nat):
     is_lim_seq (fun n : nat => sum_n_m X 0 N / INR (S (n + S N))) 0.
Proof.
Admitted.

  

   Lemma lim_avg_tails (X : nat -> R) (l:R) (N:nat):
     is_lim_seq (fun n => sum_n_m X 0 n / INR (S n)) l <->
     is_lim_seq (fun n => sum_n_m X N n / INR (S n)) l.
Proof.
Admitted.

  Lemma Ash_6_2_5_0 (X : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (X n)} 
        {isfe : forall n, IsFiniteExpectation Prts (X n)} :
    (forall n, FiniteExpectation Prts (X n) = 0) ->
    iid_rv_collection Prts borel_sa X ->
    almost Prts (fun omega => is_lim_seq (fun n => ((rvsum X n) omega)/(INR (S n))) 0).
Proof.
Admitted.


  Lemma Ash_6_2_5 (X : nat -> Ts -> R) (mu : R)
        {rv : forall n, RandomVariable dom borel_sa (X n)} 
        {isfe : forall n, IsFiniteExpectation Prts (X n)} :
    (forall n, FiniteExpectation Prts (X n) = mu) ->
    iid_rv_collection Prts borel_sa X ->
    almost Prts (fun omega => is_lim_seq (fun n => ((rvsum X n) omega)/(INR (S n))) mu).
Proof.
Admitted.
          
End slln_extra.
