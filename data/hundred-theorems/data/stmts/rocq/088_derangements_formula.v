Require Import Exp_prop Rbase Rdefinitions Rfunctions Reals Lia.

Lemma lt_onehalf_if: forall a b: R,
    (0 < a)%R -> (0 < b)%R ->
    (b > 2 * a)%R -> ((a / b) < / 2)%R.
Proof.
Admitted.

Lemma INR_lt_onehalf_if: forall a b,
    (b > 2 * a) -> (((INR a) / (INR b)) < / 2)%R.
Proof.
Admitted.

Definition drm_count_as_sum (n: nat) := ((INR (fact n)) * (E1 (-1) n))%R.

Fixpoint fact_n_k (n k: nat): nat :=
  match k with
  | 0 => 1
  | S k' => ((Nat.max 1 n) + k - 1) * (fact_n_k n k')
  end.

Lemma fact_1_k: forall k, (fact_n_k 1 k) = (fact k).
Proof.
Admitted.

Lemma INR_S_neq_0: forall n, ((INR (S n)) <> 0)%R.
Proof.
Admitted.

Lemma INR_fact_n_k_gt_0: forall n k, ((INR (fact_n_k n k)) > 0)%R.
Proof.
Admitted.

Corollary INR_fact_n_k_neq_0: forall n k, ((INR (fact_n_k n k)) <> 0)%R.
Proof.
Admitted.

Lemma Rinv_eq_compat: forall r1 r2: R, r1 <> 0%R -> r2 <> 0%R -> (r1 = r2 <-> / r1 = / r2)%R.
Proof.
Admitted.

Lemma eq_INR: forall n m, n = m -> INR n = INR m.
Proof.
Admitted.

Lemma neg_1_mult_neg_1: ((-1) * (-1) = 1)%R.
Proof.
Admitted.

Lemma neg_1_mult: forall a, (((-1) * a) = - a)%R.
Proof.
Admitted.

Definition inv_fact_n_k (n k: nat): R := (/ (INR (fact_n_k n k)))%R.

Lemma fact_fact_n_k: forall n k: nat, (((INR (fact n)) / (INR (fact (n + k)))) = (inv_fact_n_k (n + 1) k))%R.
Proof.
Admitted.

Lemma fact_n_k_gt_0: forall n k, (fact_n_k n k) > 0.
Proof.
Admitted.

Lemma fact_n_k_lt: forall n k k', k > k' -> n > 1 -> ((fact_n_k n k) > (fact_n_k n k')).
Proof.
Admitted.

Corollary INR_fact_n_k_lt: forall n k k', k > k' -> n > 1 -> (INR (fact_n_k n k) > INR (fact_n_k n k'))%R.
Proof.
Admitted.

Lemma even_exists: forall n: nat, (Nat.
Proof.
Admitted.

Lemma not_even_S_n: forall n: nat, (Nat.
Proof.
Admitted.

Definition rest_sum (n N: nat) :=
  sum_f_R0 (fun k => (inv_fact_n_k (n + 1) (k + 1)) * ((-1) ^ k))%R (N - n - 1).

Lemma drm_count_rest_sum: forall N n, N > n ->
  ( (((INR (fact n)) * (E1 (-1) N)) - (drm_count_as_sum n)))%R =
  ( (rest_sum n N) * (if Nat.
Proof.
Admitted.

Fact Rplus_mult_neg_1_r_gt_0: forall a b, (a + b * (-1) > 0)%R <-> (a > b)%R.
Proof.
Admitted.

Fact Rplus_mult_neg_1_r_lt_0: forall a b, (a * (-1) + b < 0)%R <-> (a > b)%R.
Proof.
Admitted.

Fact Rplus_neg_gt_0: forall a b, (a + - b > 0)%R <-> (a > b)%R.
Proof.
Admitted.

Lemma inv_fact_n_k_gt: forall n k k', k < k' -> n > 1 -> (inv_fact_n_k n k > inv_fact_n_k n k')%R.
Proof.
Admitted.

Lemma inv_fact_n_k_gt_0: forall n k, (inv_fact_n_k n k > 0)%R.
Proof.
Admitted.

Lemma rest_sum_gt_0_odd: forall n N,
    n > 0 -> N > n + 2 -> (Nat.
Proof.
Admitted.

Lemma rest_sum_gt_0_even: forall n N,
    n > 0 -> N > n + 3 -> (Nat.
Proof.
Admitted.

Lemma rest_sum_gt_0: forall n N,
    n > 0 -> N > n + 3 -> ((rest_sum n N) > 0)%R.
Proof.
Admitted.

Lemma rest_sum_even: forall n N,
    n > 0 -> N > n + 3 -> (Nat.
Proof.
Admitted.

Lemma rest_sum_odd: forall n N,
    n > 0 -> N > n + 4 -> (Nat.
Proof.
Admitted.

Lemma rest_sum_lt: forall n N,
    n > 0 -> N > n + 4 -> ((rest_sum n N) < (rest_sum n (n + 1)))%R.
Proof.
Admitted.

Lemma R_dist_lt_swap: forall a b c eps, (R_dist a b < eps)%R -> ((Rabs (a + c)) < (Rabs (b + c)) + eps)%R.
Proof.
Admitted.

Lemma inv_fact_n_k_le: forall n n' k, n >= n' -> n' > 0 -> (inv_fact_n_k n k <= inv_fact_n_k n' k)%R.
Proof.
Admitted.

Lemma Rinv_1_l: forall r, r <> 0%R -> (/ r * r = 1)%R.
Proof.
Admitted.

Corollary Rinv_1_r: forall r, r <> 0%R -> (r * / r = 1)%R.
Proof.
Admitted.

Lemma drm_count_as_sum_e_diff_N: forall n: nat,
    n > 0 -> exists eps: R,
      (eps > 0)%R /\ exists N0: nat, forall N: nat,
        N > N0 ->
        ((Rabs (((INR (fact n)) * (E1 (-1) N)) - (drm_count_as_sum n))) + eps < (/ INR 2))%R.
Proof.
Admitted.

Lemma drm_count_as_sum_e_diff: forall n: nat, n > 0 ->
    ((Rabs (((INR (fact n)) * (exp (-1))) - (drm_count_as_sum n))) < (/ INR 2))%R.
Proof.
Admitted.


Require Import drmcorrect drmnodup List SetoidList SetoidPermutation FMapWeakList OrderedTypeEx Compare_dec.
Import ListNotations.

Fixpoint drm_count (n: nat) :=
  match n with
  | 0 => 1
  | 1 => 0
  | S k => (n - 1) * ((drm_count k) + (drm_count (Nat.pred k)))
  end.


Lemma drm_construct_1_count: forall n m, length (drm_construct_1 n m) = (card m).
Proof.
Admitted.

Lemma concat_map_length: forall {A B: Type} (l: list A) (f: A -> list B) c,
    (forall x, In x l -> (length (f x) = c)) ->
    (length (concat (List.
Proof.
Admitted.

Lemma drm_construct_2_count: forall n m,
    drm m (Nat.
Proof.
Admitted.

Lemma drm_count_correct: forall n, (drm_count n) = length (drm_construct n).
Proof.
Admitted.

Lemma drm_count_closed_form: forall n,
    INR (drm_count n) = drm_count_as_sum n.
Proof.
Admitted.


Definition round (r: R) :=
  if (Rlt_dec (R_dist r (IZR (Int_part r))) (/ INR 2)) then
    Some (Int_part r)
  else if (Rlt_dec (R_dist (IZR (up r)) r) (/ INR 2)) then
         Some (up r)
       else
         None.

Lemma round_dist: forall r n,
    (Rabs (r - INR n) < / INR 2)%R -> (round r) = Some (Z.
Proof.
Admitted.

Theorem drm_formula: forall n,
    n > 0 ->
    round ((INR (fact n)) * (exp (-1))) = Some (Z.
Proof.
Admitted.
