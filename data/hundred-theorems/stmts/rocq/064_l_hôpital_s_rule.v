Require Import Reals.
Require Import Lra.
Require Import Rfunction_classes_def.
Require Import Cauchy_lipschitz. (* TODO on importe des trucs qui parlent de Cn *)
Require Import Rextensionality.
Open Scope R_scope.

(*
TODO check, rename, indent, and comment
*)

(* 
This file contains a proof of the Hopital's rule.
Due to the huge number of different cases we provide the user with some lemmas corresponding to
the cases of the Hopital's rule

How to use this file ?
There are 4 parameters: 
- The limit can be when x -> a+(the lemmas has a suffix : _right) or when x -> a- (the lemmas have a suffix : _left)
(* TODO change the names accordingly *)
- The limit of g is either + infinity, -infinity or 0
- The limit L of (f' / g') is either finite, +infinity or -infinity

********Not supported*********
If you want to reason about limits like x -> + infinity or x -> - infinity, we suggest that you change the variable
x -> 1 / t and then use this file with limits: t -> 0+ or t -> 0- 
******************************


So, an example of a specification can be : 

"Theorem Hopital_g0_Lfin_right :

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
g_not_0: \forall x \in ]a; b[, g' x <> 0 /\ g x <> 0
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> a+} f / g = L"



Exhaustive lemmas usable:
- Hopital_g0_Lfin_right
- Hopital_g0_Lpinf_right
- Hopital_g0_Lninf_right
- Hopital_gpinf_Lfin_right
- Hopital_gpinf_Lpinf_right
- Hopital_gpinf_Lninf_right
- Hopital_gninf_Lfin_right
- Hopital_gninf_Lpinf_right
- Hopital_gninf_Lninf_right
- Hopital_g0_Lfin_left
- Hopital_g0_Lpinf_left
- Hopital_g0_Lninf_left
- Hopital_gpinf_Lfin_left
- Hopital_gpinf_Lpinf_left
- Hopital_gpinf_Lninf_left
- Hopital_gninf_Lfin_left
- Hopital_gninf_Lpinf_left
- Hopital_gninf_Lninf_left


*)



Definition derivable_on_interval a b (Hab : a < b) f :=
  forall x, open_interval a b x -> derivable_pt f x.
Proof.
Admitted.

Lemma limit_div_pos_inv : forall f a b, limit_div_neg (fun x => - f x) (open_interval a b) a ->
   limit_div_pos f (open_interval a b) a.
Proof.
Admitted.

Lemma limit_div_neg_inv : forall f a b, limit_div_pos (fun x => - f x) (open_interval a b) a ->
   limit_div_neg f (open_interval a b) a.
Proof.
Admitted.

Lemma limit_div_neg_ext : forall f g (I : R -> Prop) a, (forall x, I x -> f x = g x) ->
  limit_div_neg f I a -> limit_div_neg g I a.
Proof.
Admitted.

Lemma limit_div_pos_ext : forall f g (I : R -> Prop) a, (forall x, I x -> f x = g x) ->
  limit_div_pos f I a -> limit_div_pos g I a.
Proof.
Admitted.


Lemma limit_div_pos_open : forall a b b' f, 
  open_interval a b b' -> limit_div_pos f (open_interval a b') a -> limit_div_pos f (open_interval a b) a.
Proof.
Admitted.

Lemma limit_div_neg_open : forall a b b' f, 
  open_interval a b b' -> limit_div_neg f (open_interval a b') a -> limit_div_neg f (open_interval a b) a.
Proof.
Admitted.

Lemma limit_div_pos_opp : forall a b g, limit_div_pos g (open_interval a b) b -> 
  limit_div_pos (fun x : R => g (- x)) (open_interval (- b) (- a)) (- b).
Proof.
Admitted.

Lemma limit_div_neg_opp : forall a b g, limit_div_neg g (open_interval a b) b -> 
  limit_div_neg (fun x : R => g (- x)) (open_interval (- b) (- a)) (- b).
Proof.
Admitted.

Lemma limit_div_pos_imp :
forall (f : R -> R) (D D1 : R -> Prop) (l : R),
  (forall x0 : R, D1 x0 -> D x0) -> limit_div_pos f D l -> limit_div_pos f D1 l.
Proof.
Admitted.

Lemma limit_div_neg_imp :
forall (f : R -> R) (D D1 : R -> Prop) (l : R),
  (forall x0 : R, D1 x0 -> D x0) -> limit_div_neg f D l -> limit_div_neg f D1 l.
Proof.
Admitted.


Lemma limit_div_pos_comp_Ropp : 
  forall (g : R -> R) (a b : R),
    limit_div_pos g (open_interval (-a) (-b)) (-a) -> 
      limit_div_pos (comp g (fun x => -x)) (open_interval b a) a.
Proof.
Admitted.

Lemma limit_div_pos_comp_Ropp_l : 
  forall (g : R -> R) (a b : R),
    limit_div_pos g (open_interval (-a) (-b)) (-b) -> 
      limit_div_pos (comp g (fun x => -x)) (open_interval b a) b.
Proof.
Admitted.

Lemma limit_div_neg_comp_Ropp : 
  forall (g : R -> R) (a b : R),
    limit_div_neg g (open_interval (-a) (-b)) (-a) -> 
      limit_div_neg (comp g (fun x => -x)) (open_interval b a) a.
Proof.
Admitted.

Lemma limit_div_neg_comp_Ropp_l : 
  forall (g : R -> R) (a b : R),
    limit_div_neg g (open_interval (-a) (-b)) (-b) -> 
      limit_div_neg (comp g (fun x => -x)) (open_interval b a) b.
Proof.
Admitted.

End Definitions.

Lemma derive_pt_comp_Ropp : forall a b f x (Df : forall x, open_interval a b x -> derivable_pt f x) 
(Df' : forall x, open_interval (-b) (-a) x -> derivable_pt (fun x0 => f (- x0)) x) 
  (H1 : open_interval (-b) (-a) x) (H2 : open_interval a b (-x)), - derive_pt f (- x) (Df (- x) H2) =
   derive_pt (fun x0 : R => f (- x0)) x (Df' x H1).
Proof.
Admitted.

Section FirstGenHopital.

(*
Theorem Hopital_g0_Lfin_right :

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
g_not_0: \forall x \in ]a; b[, g' x <> 0 /\ g x <> 0
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> a+} f / g = L

*)

Variables f g : R -> R.
Proof.
Admitted.

Lemma f_a_zero : f a = 0.
Proof.
Admitted.

Lemma g_a_zero : g a = 0.
Proof.
Admitted.

Theorem Hopital_g0_Lfin_right : limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
Admitted.

End FirstGenHopital.

Section FirstGenHopital_left.

(*
Theorem Hopital_g0_Lfin_left :

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> b-} f = 0
Zg: lim_{x -> b-} g = 0
g_not_0: \forall x \in ]a; b[, g' x <> 0 /\ g x <> 0
Hlimder: lim_{x -> b-} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> b-} f / g = L

*)

Variables f g : R -> R.
Proof.
Admitted.

End FirstGenHopital_left.

Section SndGenHopital.

(*
Theoreme Hopital_gpinf_Lfin_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = +infinity
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = L


*)
Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).

Lemma open_lemma : forall a b c, a < b -> c > 0 -> open_interval a b (a + Rmin ((b - a) /2) c).
Proof.
Admitted.


Lemma g_not_zero : exists a', open_interval a b a' /\ forall x, open_interval a a' x -> g x <> 0.
Proof.
Admitted.

Lemma MVT_unusable : forall a', open_interval a b a' -> 
          forall x y : R,
          open_interval a a' x ->
          open_interval a a' y ->
          x < y ->
          exists c : R,
            exists Hopenc : open_interval a b c,
              (f y - f x) * derive_pt g c (Dg c Hopenc) =
              derive_pt f c (Df c Hopenc) * (g y - g x) /\ 
              x < c < y.
Proof.
Admitted.


Theorem Hopital_gpinf_Lfin_right : limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
Admitted.

End SndGenHopital.

Section SndGenHopital_left.

(*
Theoreme Hopital_gpinf_Lfin_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = +infinity
Hlimder: lim_{x -> b-} f' / g' = L    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = L


*)
Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).


Theorem Hopital_gpinf_Lfin_left : limit1_in (fun x => f x / g x) (open_interval a b) L b.
Proof.
Admitted.


End SndGenHopital_left.

Section SndGenHopitalposneg.

(*
Theoreme Hopital_gninf_Lfin_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> a+} f / g = L


*)


Lemma g_not_zero2 : forall g a b, b > a -> limit_div_neg g (open_interval a b) a -> 
  exists a', open_interval a b a' /\ forall x, open_interval a a' x -> g x <> 0.
Proof.
Admitted.

Lemma limit1_in_open : forall f L a b c, open_interval a b c -> 
  limit1_in f (open_interval a c) L a ->
    limit1_in f (open_interval a b) L a.
Proof.
Admitted.

Lemma limit_div_neg_open1 : forall f a b c, open_interval a b c -> 
  limit_div_neg f (open_interval a b) a ->
    limit_div_neg f (open_interval a c) a.
Proof.
Admitted.

Lemma Hopital_gninf_Lfin_right
     : forall (f g : R -> R) (a b L : R),
       a < b ->
       forall (Df : forall x : R, open_interval a b x -> derivable_pt f x)
         (Dg : forall x : R, open_interval a b x -> derivable_pt g x),
       (forall x : R, a <= x <= b -> continuity_pt f x) ->
       (forall x : R, a <= x <= b -> continuity_pt g x) ->
       limit_div_neg g (open_interval a b) a ->
       (forall (x : R) (Hopen : open_interval a b x),
        derive_pt g x (Dg x Hopen) <> 0) ->
       (forall eps : R,
        eps > 0 ->
        exists alp : R,
          alp > 0 /\
          (forall (x : R) (Hopen : open_interval a b x),
           R_dist x a < alp ->
           R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L <
           eps)) ->
       limit1_in (fun x : R => f x / g x) (open_interval a b) L a.
Proof.
Admitted.

End SndGenHopitalposneg.

Section SndGenHopitalposneg_left.


(*
Theoreme Hopital_gninf_Lfin_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = -infinity
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
Hlimder: lim_{x -> b-} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> b-} f / g = L


*)

Lemma Hopital_gninf_Lfin_left
     : forall (f g : R -> R) (a b L : R),
       a < b ->
       forall (Df : forall x : R, open_interval a b x -> derivable_pt f x)
         (Dg : forall x : R, open_interval a b x -> derivable_pt g x),
       (forall x : R, a <= x <= b -> continuity_pt f x) ->
       (forall x : R, a <= x <= b -> continuity_pt g x) ->
       limit_div_neg g (open_interval a b) b ->
       (forall (x : R) (Hopen : open_interval a b x),
        derive_pt g x (Dg x Hopen) <> 0) ->
       (forall eps : R,
        eps > 0 ->
        exists alp : R,
          alp > 0 /\
          (forall (x : R) (Hopen : open_interval a b x),
           R_dist x b < alp ->
           R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L <
           eps)) ->
       limit1_in (fun x : R => f x / g x) (open_interval a b) L b.
Proof.
Admitted.


End SndGenHopitalposneg_left.

Section InfiniteLimiteHopital_pos.

(*
Theorem Hopital_g0_Lpinf_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
Hlimder: lim_{x -> a+} f' / g' = +infinity
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Proof.
Admitted.


End InfiniteLimiteHopital_pos.

Section InfiniteLimiteHopital_pos_left.


(*
Theorem Hopital_g0_Lpinf_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> b-} f = 0
Zg: lim_{x -> b-} g = 0
Hlimder: lim_{x -> b-} f' / g' = +infinity
-----------------------------------------------------
lim_{x -> b-} f / g = +infinity

*)

Variables f g : R -> R.
Proof.
Admitted.


End InfiniteLimiteHopital_pos_left.

Section InfiniteLimiteHopital_neg.

(*
Theorem Hopital_g0_Lninf_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
Hlimder: lim_{x -> a+} f' / g' = -infinity
-----------------------------------------------------
lim_{x -> a+} f / g = -infinity

*)

Variables f g : R -> R.
Proof.
Admitted.


End InfiniteLimiteHopital_neg.


Section InfiniteLimiteHopital_neg_left.

(*
Theorem Hopital_g0_Lninf_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> b-} f = 0
Zg: lim_{x -> b-} g = 0
Hlimder: lim_{x -> b-} f' / g' = -infinity
-----------------------------------------------------
lim_{x -> b-} f / g = -infinity

*)

Variables f g : R -> R.
Proof.
Admitted.

End InfiniteLimiteHopital_neg_left.

Section Hopital_infinite_pos.

(*
Theoreme Hopital_gpinf_Lpinf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = +infinity
Hlimder: lim_{x -> a+} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Theorem Hopital_gpinf_Lpinf_right : limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

End Hopital_infinite_pos.

Section Hopital_infinite_pos_left.

(*
Theoreme Hopital_gpinf_Lpinf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = +infinity
Hlimder: lim_{x -> b-} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Theorem Hopital_gpinf_Lpinf_left : limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

End Hopital_infinite_pos_left.


Section Hopital_infinite_neg.

(*
Theoreme Hopital_gpinf_Lninf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = +infinity
Hlimder: lim_{x -> a+} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < -m))).

Theorem Hopital_gpinf_Lninf_right : limit_div_neg (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.
 
End Hopital_infinite_neg.

Section Hopital_infinite_neg_left.


(*
Theoreme Hopital_gpinf_Lninf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = +infinity
Hlimder: lim_{x -> b-} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < -m))).

Theorem Hopital_gpinf_Lninf_left : limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

End Hopital_infinite_neg_left.

Section Useless.

(*
Theoreme Hopital_infinite_pos : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
Hlimder: lim_{x -> a+} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
g_not_zero : \forall x \in ]a ; b[, g x <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x), g x <> 0).

Theorem Hopital_infinite_inf_neg_lpos_useless : limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

End Useless.

Section Hopital_infinite_neg_pos.

(*
Theoreme Hopital_gninf_Lpinf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
Hlimder: lim_{x -> a+} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Lemma new_bound : exists b', (forall x, open_interval a b' x -> g x <> 0) /\ open_interval a b b'.
Proof.
Admitted.

Theorem Hopital_gninf_Lpinf_right : limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.


End Hopital_infinite_neg_pos.

Section Hopital_infinite_neg_pos_left.
(*
Theoreme Hopital_gninf_Lpinf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = -infinity
Hlimder: lim_{x -> b-} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Theorem Hopital_gninf_Lpinf_left : limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

End Hopital_infinite_neg_pos_left.

Section Hopital_infinite_pos_g.

(*
Theoreme Hopital_gninf_Lninf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
Hlimder: lim_{x -> a+} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m < 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < m))).

Theorem Hopital_gninf_Lninf_right : limit_div_neg (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.


End Hopital_infinite_pos_g.

Section Hopital_infinite_pos_g_left.

(*
Theoreme Hopital_gninf_Lninf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = -infinity
Hlimder: lim_{x -> b-} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m < 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < m))).

Theorem Hopital_gninf_Lninf_left : limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.


End Hopital_infinite_pos_g_left.
