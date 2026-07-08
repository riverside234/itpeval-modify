(*College Thesis of Raül Espejo Boix for Universitat Autònoma de Barcelona*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma prime_decomp_ind (P: nat -> Prop) (P0: P 0) (P1: P 1)
      (Pprime: forall p k, prime p -> k > 0 -> P (p^k))
      (Pmul: forall a b, P a -> P b -> coprime a b -> (P (a*b))) c: P c.
Proof.
Admitted.

Proposition gcdnM a b c: (a > 0) -> (coprime a b) ->
    gcdn (a*b) c = (gcdn a c)*(gcdn b c).
Proof.
Admitted.

Lemma div_gcdnE a b c (apos: a > 0): (coprime a b) ->
    reflect (c = (gcdn a c)*(gcdn b c)) (c %| a*b).
Proof.
Admitted.

Definition div_pair a b d:= (gcdn a d, gcdn b d).
Definition div_prod (d: nat*nat):= d.1*d.2.

Lemma div2_to_div a b (apos: a > 0) (bpos: b > 0): coprime a b ->
    map div_prod (allpairs pair (divisors a) (divisors b)) =i
    divisors (a*b).
Proof.
Admitted.

Lemma cpr_divl a b c: c%|a -> (coprime a b) -> (coprime c b).
Proof.
Admitted.

Lemma cpr_divr a b c: c%|b -> (coprime a b) -> (coprime a c).
Proof.
Admitted.

Lemma cpr_mult_projl a b c d: (coprime a d) -> (coprime b c) ->
    a*b = c*d -> b = d.
Proof.
Admitted.

Lemma cpr_mult_projr a b c d: (coprime a d) -> (coprime b c) ->
    a*b = c*d -> a = c.
Proof.
Admitted.

Lemma div2_to_divPerm a b (apos: a > 0) (bpos: b > 0): coprime a b ->
    perm_eq
        (map div_prod (allpairs pair (divisors a) (divisors b)))
        (divisors (a*b)).
Proof.
Admitted.

Lemma prime_div p k (kgt0: k > 0): prime p ->
    prime_decomp (p^k) = [:: (p, k)].
Proof.
Admitted.

Lemma div_primeX p k: prime p ->
    divisors (p^k) = [seq p^i | i <- iota 0 k.
Proof.
Admitted.

Definition multiplicative f := forall a b, (coprime a b) ->
    f (a*b) = (f a)*(f b).
Definition dirichlet_conv (f g: nat -> nat) n :=
    if n > 0 then \sum_(d <- divisors n) (f d)*(g (n%/d)) else 0.
  (* Definit al 0 com 0 per a mantenir les propietats desitjades*)

Definition sigma := dirichlet_conv (fun n => n) (fun n => 1).
Definition perfect p := sigma p = 2 * p.
Definition mersenne p := (prime p)/\(exists k, p = 2^k - 1).

Theorem dirichletM f g (f_cdt : multiplicative f) (g_cdt : multiplicative g) :
    (multiplicative (dirichlet_conv f g)).
Proof.
Admitted.

Theorem geoSum p n m: (p > 1) ->
    \sum_(i <- (iota m n)) p^i = (p^(m+n) - p^m)%/(p-1).
Proof.
Admitted.

Corollary sigmaM: multiplicative sigma.
Proof.
Admitted.

Proposition sigmaX p n: prime p -> n > 0 ->
    sigma (p^n) = (p^n.
Proof.
Admitted.

Corollary sigmaX1 p: prime p -> sigma p = p+1.
Proof.
Admitted.

Lemma remK (T: eqType) (x y: T) s: y != x -> y \in s -> y \in rem x s.
Proof.
Admitted.

Proposition sigma_geqn N: N > 1 -> sigma N >= N+1.
Proof.
Admitted.

Proposition sigmapS p: sigma p = p+1 -> prime p.
Proof.
Admitted.

Proposition sigma_geqdvd2 p k l: p > 1 -> k!=1 -> p!=k ->
    (k)*(l) = p -> sigma p >= 1+k+p.
Proof.
Admitted.

Theorem EuclidT p: prime (2^p-1) -> perfect (2^(p-1)*(2^p-1)).
Proof.
Admitted.

(*Leonard Eugene Dickson, History of the theory of numbers. Vol I page 19*)
Theorem EulerT p: perfect p -> 2%|p -> p > 0 ->
                  exists n, (p = (2^n-1)*2^n.
Proof.
Admitted.