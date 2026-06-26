Require Import ZArith.
Require Import Zhints.
Require Import Zpow_facts.
Require Import BinInt. Import Z.
Require Import Znat.
Require Import Zeuclid. Import ZEuclid.
Require Import Znumtheory.
Require Import Reciprocity.Reciprocity.Finite. Import FiniteTypes.
Require Import Reciprocity.Reciprocity.Accumulation. Import Accum.
Require Import Classical.
Require Import Lia.

Lemma Zpos_induction (P : Z -> Prop) :
  P 0 ->
  (forall n : Z, 0 <= n -> P n -> P (succ n)) ->
  (forall n : Z, 0 <= n -> P n).
Proof.
Admitted.
Let f' u := exist (fun k => 1 <= k <= p - 1) (f u) (f'_exists u).
Let f'_injective :
  injection f'.
Proof.
Admitted.
Let f'_surjective :
  surjection f'.
Proof.
Admitted.
Let card_U :
  cardinality {u : Z | 1 <= u <= p - 1} (Z.to_nat (p - 1)).
Proof.
Admitted.
Let U_finite :
  finite {u : Z | 1 <= u <= p - 1}.
Proof.
Admitted.

Let P' := product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => `x).
Let P'_not_0 :
  P' mod p <> 0.
Proof.
Admitted.
Let P'1 :
  product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (compose (proj1_sig (P := fun k => 1 <= k <= p - 1)) f') =
  (ZpZmult p) (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => `x))
              (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => a)).
Proof.
Admitted.
Let P'2 :
  product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (compose (proj1_sig (P := fun k => 1 <= k <= p - 1)) f') = P'.
Proof.
Admitted.
Let P'3 :
  (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => a)) mod p = (a ^ (p - 1)) mod p.
Proof.
Admitted.
Theorem FLT :
  (a ^ (p - 1)) mod p = 1.
Proof.
Admitted.
Let U_finite :
  finite {x : Z | 1 <= x <= p - 1}.
Proof.
Admitted.
Theorem Wilson :
  product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _ U_finite (fun x => `x)
    = -1 mod p.
Proof.
Admitted.
Let if_a_0 :
  a mod p = 0 -> 0 mod p = (a ^ ((p - 1) / 2)) mod p.
Proof.
Admitted.
Let if_a_square :
  a mod p <> 0 -> (exists y, (y ^ 2) mod p = a mod p) ->
    1 mod p = (a ^ ((p - 1) / 2)) mod p.
Proof.
Admitted.
Let if_a_not_square :
  a mod p <> 0 -> (forall y, (y * y) mod p <> a mod p) ->
    -1 mod p = (a ^ ((p - 1) / 2)) mod p.
Proof.
Admitted.
Theorem Eulers_criterion :
  (legendre p a) mod p = a ^ ((p - 1) / 2) mod p.
Proof.
Admitted.
Let p_positive_rev :
  p > 0.
Proof.
Admitted.
Let p_not_0 :
  p <> 0.
Proof.
Admitted.
Let eq_mod_2 :
  forall x y : Z, (x + y) mod 2 = 0 -> x mod 2 = y mod 2.
Proof.
Admitted.
Let div_mod_mod_2_even :
  forall a : Z, a mod 2 = 0 -> (a / p) mod 2 = (a mod p) mod 2.
Proof.
Admitted.
Let div_mod_mod_2_odd :
  forall a : Z, a mod 2 = 1 -> (a / p) mod 2 = (a mod p + 1) mod 2.
Proof.
Admitted.

Variable q : Z.
Hypothesis q_not_0 : q mod p <> 0.
Hypothesis q_postive : q >= 0.

Let r (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :=
    (q * `u) mod p.
Let r_positive :
  forall (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}), 0 <= r u.
Proof.
Admitted.
Let r' (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :=
    ((Zpower (-1) (r u)) * (r u)) mod p.
Let r''_ex (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :
  1 <= (r' u) <= p - 1 /\ (r' u) mod 2 = 0.
Proof.
Admitted.
Let r'' (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :=
   exist (fun k => 1 <= k <= p - 1 /\ k mod 2 = 0) (r' u) (r''_ex u).
Let r''_inj1 :
  forall u1 u2, r' u1 = r' u2 -> Even (r u1) -> Odd (r u2) -> r u1 = r u2.
Proof.
Admitted.
Let r''_injective :
  injection r''.
Proof.
Admitted.
Let r''_surjective :
  surjection r''.
Proof.
Admitted.

Let card_R :
  cardinality {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} (Z.to_nat ((p - 1) / 2)).
Proof.
Admitted.

Let R_finite :
  finite {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}.
Proof.
Admitted.

Let mlt := ZpZmult p.
Let mlt_comm := ZpZmult_comm p.
Let mlt_assoc := ZpZmult_assoc p.
Let one_id := one_idemp p p_prime.

Let P := product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun x => `x).
Let P_not_0 :
  P mod p <> 0.
Proof.
Admitted.
Let P1 :
  product Z mlt mlt_comm mlt_assoc 1 _ R_finite r =
    mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun x => q)) P.
Proof.
Admitted.
Let P2 :
  product Z mlt mlt_comm mlt_assoc 1 _ R_finite r' =
    mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))
        (product Z mlt mlt_comm mlt_assoc 1 _ R_finite r).
Proof.
Admitted.
Let P3 :
  product Z mlt mlt_comm mlt_assoc 1 _ R_finite r' = P.
Proof.
Admitted.
Let P4 :
  mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))
      (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))
    = 1.
Proof.
Admitted.
Let P5 :
  mlt P ((product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))) =
    mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite r) 1.
Proof.
Admitted.
Let P6 :
  mlt P (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u))) =
  mlt P (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => q)).
Proof.
Admitted.
Let P7 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u))) mod p =
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => q)) mod p.
Proof.
Admitted.
Let P8 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u))) =
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ ((q * `u) / p))).
Proof.
Admitted.
Let P9 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ ((q * `u) / p))) mod p =
  (m1_pow (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p))) mod p.
Proof.
Admitted.
Let P10 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => q)) mod p =
    (q ^ ((p - 1) / 2)) mod p.
Proof.
Admitted.
Let Eisensteins_lemma_mod_p :
  (legendre p q) mod p = (m1_pow (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p))) mod p.
Proof.
Admitted.
Let p_not_2 :
  p <> 2.
Proof.
Admitted.
Lemma Eisensteins_lemma1 :
  legendre p q = m1_pow (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p)).
Proof.
Admitted.
Hypothesis q_odd : q mod 2 = 1.
Hypothesis q_prime : prime q.
Let E1 :
  (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p)) mod 2 =
  (product Z Zplus Zplus_comm Zplus_assoc 0 _ U_finite (fun u => (q * `u) / p)) mod 2.
Proof.
Admitted.
Definition EL := (product Z Zplus Zplus_comm Zplus_assoc 0 _ U_finite (fun u => (q * `u) / p)).
Lemma EL1 :
  0 <= EL.
Proof.
Admitted.
Let q_ge_1 :
  q > 1.
Proof.
Admitted.
Let p_not_2 :
  p <> 2.
Proof.
Admitted.
Let q_not_2 :
  q <> 2.
Proof.
Admitted.
Let p2_pos :
  (p - 1) / 2 > 0.
Proof.
Admitted.
Let q2_pos :
  (q - 1) / 2 > 0.
Proof.
Admitted.
Let p_mod_q_not_0 :
  p mod q <> 0.
Proof.
Admitted.
Let q_mod_p_not_0 :
  q mod p <> 0.
Proof.
Admitted.
Let a := EL p p_prime p_odd q.
Let b := EL q q_prime q_odd p.
Let QR1 :
  cardinality {s : {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2} |
                                                     p * snd `s <= q * fst `s}
   (Z.to_nat a).
Proof.
Admitted.
Let QR2 :
  cardinality {s : {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2} |
                                                     ~ (p * snd `s <= q * fst `s)}
   (Z.to_nat b).
Proof.
Admitted.
Let QR3 :
  cardinality {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2}
  (Z.to_nat a + Z.to_nat b).
Proof.
Admitted.
Let QR4 :
  cardinality {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2}
  (Z.to_nat (((p - 1) / 2) * ((q - 1) / 2))).
Proof.
Admitted.
Let QR5 :
  (Z.to_nat a + Z.to_nat b)%nat = (Z.to_nat (((p - 1) / 2) * ((q - 1) / 2))).
Proof.
Admitted.
Let QR6 :
  a + b = ((p - 1) / 2) * ((q - 1) / 2).
Proof.
Admitted.
Theorem Quadratic_reciprocity :
  (legendre p q) * (legendre q p) = (-1) ^ (((p - 1) / 2) * ((q - 1) / 2)).
Proof.
Admitted.
End Quadratic_reciprocity.
