(* ========================================================================= *)
(* Convex sets, functions and related things.                                *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*                 (c) Copyright, Lars Schewe 2007                           *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(* ========================================================================= *)

needs "Multivariate/topology.ml";;

(* ------------------------------------------------------------------------- *)
(* Some miscelleneous things that are convenient to prove here.              *)
(* ------------------------------------------------------------------------- *)

let TRANSLATION_EQ_IMP = `!P:(real^N->bool)->bool.
        (!a s. P(IMAGE (\x. a + x) s) <=> P s) <=>
        (!a s. P s ==> P (IMAGE (\x. a + x) s))`;;

let DIM_HYPERPLANE = `!a:real^N. ~(a = vec 0) ==> dim {x | a dot x = &0} = dimindex(:N) - 1`;;

let DIM_EQ_HYPERPLANE = `!s. dim s = dimindex(:N) - 1 <=>
       ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}`;;

(* ------------------------------------------------------------------------- *)
(* Affine set and affine hull.                                               *)
(* ------------------------------------------------------------------------- *)

let affine = new_definition
  `affine s <=> !x y u v. x IN s /\ y IN s /\ (u + v = &1)
                          ==> (u % x + v % y) IN s`;;

let AFFINE_ALT = `affine s <=> !x y u. x IN s /\ y IN s ==> ((&1 - u) % x + u % y) IN s`;;

let AFFINE_SCALING = `!s c. affine s ==> affine (IMAGE (\x. c % x) s)`;;

let AFFINE_NEGATIONS = `!s. affine s ==> affine (IMAGE (--) s)`;;

let AFFINE_SUMS = `!s t. affine s /\ affine t ==> affine {x + y | x IN s /\ y IN t}`;;

let AFFINE_DIFFERENCES = `!s t. affine s /\ affine t ==> affine {x - y | x IN s /\ y IN t}`;;

let AFFINE_TRANSLATION_EQ = `!a:real^N s. affine (IMAGE (\x. a + x) s) <=> affine s`;;

add_translation_invariants [AFFINE_TRANSLATION_EQ];;

let AFFINE_TRANSLATION = `!s a:real^N. affine s ==> affine (IMAGE (\x. a + x) s)`;;

let AFFINE_LINEAR_IMAGE = `!f s. affine s /\ linear f ==> affine(IMAGE f s)`;;

let AFFINE_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (affine (IMAGE f s) <=> affine s)`;;

add_linear_invariants [AFFINE_LINEAR_IMAGE_EQ];;

let AFFINE_LINEAR_PREIMAGE = `!f:real^M->real^N s. linear f /\ affine s ==> affine {x | f(x) IN s}`;;

let AFFINE_EMPTY = `affine {}`;;

let AFFINE_SING = `!x. affine {x}`;;

let AFFINE_SCALING_EQ = `!s:real^N->bool c. affine (IMAGE (\x. c % x) s) <=> c = &0 \/ affine s`;;

let AFFINE_AFFINITY_EQ = `!s m c:real^N.
        affine (IMAGE (\x. m % x + c) s) <=> m = &0 \/ affine s`;;

let AFFINE_AFFINITY = `!s m c:real^N. affine s ==> affine (IMAGE (\x. m % x + c) s)`;;

let AFFINE_UNIV = `affine(UNIV:real^N->bool)`;;

let AFFINE_HYPERPLANE = `!a b. affine {x | a dot x = b}`;;

let AFFINE_STANDARD_HYPERPLANE = `!b k. affine {x:real^N | x$k = b}`;;

let AFFINE_INTERS = `(!s. s IN f ==> affine s) ==> affine(INTERS f)`;;

let AFFINE_INTER = `!s t. affine s /\ affine t ==> affine(s INTER t)`;;

let AFFINE_AFFINE_HULL = `!s. affine(affine hull s)`;;

let AFFINE_HULL_EQ = `!s. (affine hull s = s) <=> affine s`;;

let IS_AFFINE_HULL = `!s. affine s <=> ?t. s = affine hull t`;;

let AFFINE_HULL_UNIV = `affine hull (:real^N) = (:real^N)`;;

let AFFINE_HULLS_EQ = `!s t. s SUBSET affine hull t /\ t SUBSET affine hull s
         ==> affine hull s = affine hull t`;;

let AFFINE_HULL_TRANSLATION = `!a s. affine hull (IMAGE (\x. a + x) s) =
         IMAGE (\x. a + x) (affine hull s)`;;

add_translation_invariants [AFFINE_HULL_TRANSLATION];;

let AFFINE_HULL_LINEAR_IMAGE = `!f s. linear f
         ==> affine hull (IMAGE f s) = IMAGE f (affine hull s)`;;

add_linear_invariants [AFFINE_HULL_LINEAR_IMAGE];;

let IN_AFFINE_HULL_LINEAR_IMAGE = `!f:real^M->real^N s x.
        linear f /\ x IN affine hull s ==> (f x) IN affine hull (IMAGE f s)`;;

let SAME_DISTANCES_TO_AFFINE_HULL = `!s a b:real^N.
        (!x. x IN s ==> dist(x,a) = dist(x,b))
        ==> (!x. x IN affine hull s ==> dist(x,a) = dist(x,b))`;;

let BILINEAR_IN_AFFINE_HULL = `!(f:real^M->real^N->real^P) s t x y.
        bilinear f /\ x IN affine hull s /\ y IN affine hull t
        ==> f x y IN affine hull { f a b | a IN s /\ b IN t}`;;

(* ------------------------------------------------------------------------- *)
(* Some convenient lemmas about common affine combinations.                  *)
(* ------------------------------------------------------------------------- *)

let IN_AFFINE_ADD_MUL = `!s a x:real^N d. affine s /\ a IN s /\ (a + x) IN s ==> (a + d % x) IN s`;;

let IN_AFFINE_ADD_MUL_DIFF = `!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> (x + a % (y - z)) IN s`;;

let IN_AFFINE_MUL_DIFF_ADD = `!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> a % (x - y) + z IN s`;;

let IN_AFFINE_SUB_MUL_DIFF = `!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> x - a % (y - z) IN s`;;

let AFFINE_DIFFS_SUBSPACE = `!s:real^N->bool a.
        affine s /\ a IN s ==> subspace {x - a | x IN s}`;;

(* ------------------------------------------------------------------------- *)
(* Explicit formulations for affine combinations.                            *)
(* ------------------------------------------------------------------------- *)

let AFFINE_VSUM = `!s k u x:A->real^N.
        FINITE k /\ affine s /\ sum k u = &1 /\ (!i. i IN k ==> x i IN s)
        ==> vsum k (\i. u i % x i) IN s`;;

let AFFINE_VSUM_STRONG = `!s k u x:A->real^N.
        affine s /\
        sum k u = &1 /\
        (!i. i IN k ==> u i = &0 \/ x i IN s)
        ==> vsum k (\i. u i % x i) IN s`;;

let AFFINE_INDEXED = `!s:real^N->bool.
        affine s <=>
            !k u x. (!i:num. 1 <= i /\ i <= k ==> x(i) IN s) /\
                    (sum (1..k) u = &1)
                    ==> vsum (1..k) (\i. u(i) % x(i)) IN s`;;

let AFFINE_HULL_INDEXED = `!s. affine hull s =
        {y:real^N | ?k u x. (!i. 1 <= i /\ i <= k ==> x i IN s) /\
                            (sum (1..k) u = &1) /\
                            (vsum (1..k) (\i. u i % x i) = y)}`;;

let AFFINE = `!V:real^N->bool.
     affine V <=>
         !(s:real^N->bool) (u:real^N->real).
             FINITE s /\ ~(s = {}) /\ s SUBSET V /\ sum s u = &1
             ==> vsum s (\x. u x % x) IN V`;;

let AFFINE_EXPLICIT = `!s:real^N->bool.
        affine s <=>
            !t u. FINITE t /\ t SUBSET s /\ sum t u = &1
                  ==> vsum t (\x. u(x) % x) IN s`;;

let AFFINE_HULL_EXPLICIT = `!(p:real^N -> bool).
        affine hull p =
         {y | ?s u. FINITE s /\ ~(s = {}) /\ s SUBSET p /\
                    sum s u = &1 /\ vsum s (\v. u v % v) = y}`;;

let AFFINE_HULL_EXPLICIT_ALT = `!(p:real^N -> bool).
        affine hull p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    sum s u = &1 /\ vsum s (\v. u v % v) = y}`;;

let AFFINE_HULL_FINITE = `!s:real^N->bool.
        affine hull s = {y | ?u. sum s u = &1 /\ vsum s (\v. u v % v) = y}`;;

let AFFINE_HULL_0_EXPLICIT = `!s:real^N->bool.
        vec 0 IN affine hull s <=>
        ?t u. FINITE t /\ ~(t = {}) /\ t SUBSET s /\
              ~(sum t u = &0) /\ vsum t (\x. u x % x) = vec 0`;;

(* ------------------------------------------------------------------------- *)
(* Stepping theorems and hence small special cases.                          *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_EMPTY = `affine hull {} = {}`;;

let AFFINE_HULL_EQ_EMPTY = `!s. (affine hull s = {}) <=> (s = {})`;;

let AFFINE_HULL_FINITE_STEP_GEN = `!P:real^N->real->bool.
        ((?u. (!x. x IN {} ==> P x (u x)) /\
              sum {} u = w /\ vsum {} (\x. u(x) % x) = y) <=>
         w = &0 /\ y = vec 0) /\
        (FINITE(s:real^N->bool) /\
         (!y. a IN s /\ P a y ==> P a (y / &2)) /\
         (!x y. a IN s /\ P a x /\ P a y ==> P a (x + y))
         ==> ((?u. (!x. x IN (a INSERT s) ==> P x (u x)) /\
                   sum (a INSERT s) u = w /\
                   vsum (a INSERT s) (\x. u(x) % x) = y) <=>
              ?v u. P a v /\ (!x. x IN s ==> P x (u x)) /\
                    sum s u = w - v /\
                    vsum s (\x. u(x) % x) = y - v % a))`;;

let AFFINE_HULL_FINITE_STEP = `((?u. sum {} u = w /\ vsum {} (\x. u(x) % x) = y) <=>
    w = &0 /\ y = vec 0) /\
   (FINITE(s:real^N->bool)
    ==> ((?u. sum (a INSERT s) u = w /\
              vsum (a INSERT s) (\x. u(x) % x) = y) <=>
         ?v u.  sum s u = w - v /\
                vsum s (\x. u(x) % x) = y - v % a))`;;

let AFFINE_HULL_2 = `!a b. affine hull {a,b} =
         {u % a + v % b | u + v = &1}`;;

let AFFINE_HULL_2_ALT = `!a b. affine hull {a,b} = {a + u % (b - a) | u IN (:real)}`;;

let AFFINE_HULL_3 = `affine hull {a,b,c} =
    { u % a + v % b + w % c | u + v + w = &1}`;;

let AFFINE_HULL_0_2_EXPLICIT = `!x y:real^N. vec 0 IN affine hull {x,y} <=>
                  ?a b. a % x + b % y = vec 0 /\ ~(a + b = &0)`;;

let AFFINE_HULL_0_3_EXPLICIT = `!x y z:real^N. vec 0 IN affine hull {x,y,z} <=>
                  ?a b c. a % x + b % y + c % z = vec 0 /\ ~(a + b + c = &0)`;;

(* ------------------------------------------------------------------------- *)
(* Some relations between affine hull and subspaces.                         *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_INSERT_SUBSET_SPAN = `!a:real^N s.
     affine hull (a INSERT s) SUBSET {a + v | v | v IN span {x - a | x IN s}}`;;

let AFFINE_HULL_INSERT_SPAN = `!a:real^N s.
        ~(a IN s)
        ==> affine hull (a INSERT s) =
            {a + v | v | v IN span {x - a | x IN s}}`;;

let AFFINE_HULL_SPAN = `!a:real^N s.
        a IN s
        ==> (affine hull s =
             {a + v | v | v IN span {x - a | x | x IN (s DELETE a)}})`;;

let DIFFS_AFFINE_HULL_SPAN = `!a:real^N s.
        a IN s ==> {x - a | x IN affine hull s} = span {x - a | x IN s}`;;

let AFFINE_HULL_SING = `!a. affine hull {a} = {a}`;;

let AFFINE_HULL_EQ_SING = `!s a:real^N. affine hull s = {a} <=> s = {a}`;;

let AFFINE_HULL_SCALING = `!s:real^N->bool c.
        affine hull (IMAGE (\x. c % x) s) =
        IMAGE (\x. c % x) (affine hull s)`;;

let AFFINE_HULL_AFFINITY = `!s a:real^N c.
        affine hull (IMAGE (\x. c % x + a) s) =
        IMAGE (\x. c % x + a) (affine hull s)`;;

(* ------------------------------------------------------------------------- *)
(* Convexity.                                                                *)
(* ------------------------------------------------------------------------- *)

let convex = new_definition
  `convex s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> (u % x + v % y) IN s`;;

let CONVEX_ALT = `convex s <=> !x y u. x IN s /\ y IN s /\ &0 <= u /\ u <= &1
                        ==> ((&1 - u) % x + u % y) IN s`;;

let IN_CONVEX_SET = `!s a b u.
        convex s /\ a IN s /\ b IN s /\ &0 <= u /\ u <= &1
        ==> ((&1 - u) % a + u % b) IN s`;;

let MIDPOINT_IN_CONVEX = `!s x y:real^N.
        convex s /\ x IN s /\ y IN s ==> midpoint(x,y) IN s`;;

let CONVEX_CONTAINS_SEGMENT = `!s. convex s <=> !a b. a IN s /\ b IN s ==> segment[a,b] SUBSET s`;;

let CONVEX_CONTAINS_OPEN_SEGMENT = `!s. convex s <=> !a b. a IN s /\ b IN s ==> segment(a,b) SUBSET s`;;

let CONVEX_CONTAINS_SEGMENT_EQ = `!s:real^N->bool.
        convex s <=> !a b. segment[a,b] SUBSET s <=> a IN s /\ b IN s`;;

let CONVEX_CONTAINS_SEGMENT_IMP = `!s a b. convex s ==> (segment[a,b] SUBSET s <=> a IN s /\ b IN s)`;;

let SEGMENT_SUBSET_CONVEX = `!s a b:real^N.
        convex s /\ a IN s /\ b IN s ==> segment[a,b] SUBSET s`;;

let CONVEX_CONTAINS = `!s a b x:real^N.
        convex s /\ a IN s /\ b IN s /\ x IN segment[a,b] ==> x IN s`;;

let CONVEX_EMPTY = `convex {}`;;

let CONVEX_SING = `!a. convex {a}`;;

let CONVEX_UNIV = `convex(UNIV:real^N->bool)`;;

let CONVEX_INTERS = `(!s. s IN f ==> convex s) ==> convex(INTERS f)`;;

let CONVEX_INTER = `!s t. convex s /\ convex t ==> convex(s INTER t)`;;

let CONVEX_HALFSPACE_LE = `!a b. convex {x | a dot x <= b}`;;

let CONVEX_HALFSPACE_COMPONENT_LE = `!a k. convex {x:real^N | x$k <= a}`;;

let CONVEX_HALFSPACE_GE = `!a b. convex {x:real^N | a dot x >= b}`;;

let CONVEX_HALFSPACE_COMPONENT_GE = `!a k. convex {x:real^N | x$k >= a}`;;

let CONVEX_HYPERPLANE = `!a b. convex {x:real^N | a dot x = b}`;;

let CONVEX_STANDARD_HYPERPLANE = `!k a. convex {x:real^N | x$k = a}`;;

let CONVEX_HALFSPACE_LT = `!a b. convex {x | a dot x < b}`;;

let CONVEX_HALFSPACE_COMPONENT_LT = `!a k. convex {x:real^N | x$k < a}`;;

let CONVEX_HALFSPACE_GT = `!a b. convex {x | a dot x > b}`;;

let CONVEX_HALFSPACE_COMPONENT_GT = `!a k. convex {x:real^N | x$k > a}`;;

let CONVEX_STRIP_COMPONENT_LE = `!a k. convex {x:real^N | abs(x$k) <= a}`;;

let CONVEX_STRIP_COMPONENT_LT = `!a k. convex {x:real^N | abs(x$k) < a}`;;

let CONVEX_HALFSPACE_SGN = `!a b. convex {x:real^N | real_sgn(a dot x) = b}`;;

let CONVEX_HALFSPACE_COMPONENT_SGN = `!a k. convex {x:real^N | real_sgn(x$k) = a}`;;

let CONVEX_POSITIVE_ORTHANT = `convex {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> &0 <= x$i}`;;

let LIMPT_OF_CONVEX = `!s x:real^N.
        convex s /\ x IN s ==> (x limit_point_of s <=> ~(s = {x}))`;;

let TRIVIAL_LIMIT_WITHIN_CONVEX = `!s x:real^N.
        convex s /\ x IN s ==> (trivial_limit(at x within s) <=> s = {x})`;;

(* ------------------------------------------------------------------------- *)
(* Some invariance theorems for convex sets.                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_TRANSLATION_EQ = `!a:real^N s. convex (IMAGE (\x. a + x) s) <=> convex s`;;

add_translation_invariants [CONVEX_TRANSLATION_EQ];;

let CONVEX_TRANSLATION = `!s a:real^N. convex s ==> convex (IMAGE (\x. a + x) s)`;;

let CONVEX_LINEAR_IMAGE = `!f s. convex s /\ linear f ==> convex(IMAGE f s)`;;

let CONVEX_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (convex (IMAGE f s) <=> convex s)`;;

add_linear_invariants [CONVEX_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Explicit expressions for convexity in terms of arbitrary sums.            *)
(* ------------------------------------------------------------------------- *)

let CONVEX_VSUM = `!s k u x:A->real^N.
        FINITE k /\ convex s /\ sum k u = &1 /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s)
        ==> vsum k (\i. u i % x i) IN s`;;

let CONVEX_VSUM_STRONG = `!s k u x:A->real^N.
        convex s /\
        sum k u = &1 /\
        (!i. i IN k ==> &0 <= u i /\ (u i = &0 \/ x i IN s))
        ==> vsum k (\i. u i % x i) IN s`;;

let CONVEX_INDEXED = `!s:real^N->bool.
        convex s <=>
            !k u x. (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                    (sum (1..k) u = &1)
                    ==> vsum (1..k) (\i. u(i) % x(i)) IN s`;;

let CONVEX_EXPLICIT = `!s:real^N->bool.
        convex s <=>
        !t u. FINITE t /\ t SUBSET s /\ (!x. x IN t ==> &0 <= u x) /\
              sum t u = &1
              ==> vsum t (\x. u(x) % x) IN s`;;

let CONVEX = `!V:real^N->bool.
     convex V <=>
         !(s:real^N->bool) (u:real^N->real).
             FINITE s /\ ~(s = {}) /\ s SUBSET V /\
             (!x. x IN s ==> &0 <= u x) /\ sum s u = &1
             ==> vsum s (\x. u x % x) IN V`;;

let CONVEX_FINITE = `!s:real^N->bool.
        FINITE s
        ==> (convex s <=>
                !u. (!x. x IN s ==> &0 <= u x) /\
                    sum s u = &1
                    ==> vsum s (\x. u(x) % x) IN s)`;;

let AFFINE_PCROSS = `!s:real^M->bool t:real^N->bool.
        affine s /\ affine t ==> affine(s PCROSS t)`;;

let AFFINE_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        affine(s PCROSS t) <=> s = {} \/ t = {} \/ affine s /\ affine t`;;

let CONVEX_PCROSS = `!s:real^M->bool t:real^N->bool.
        convex s /\ convex t ==> convex(s PCROSS t)`;;

let CONVEX_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        convex(s PCROSS t) <=> s = {} \/ t = {} \/ convex s /\ convex t`;;

(* ------------------------------------------------------------------------- *)
(* Conic sets and conic hull.                                                *)
(* ------------------------------------------------------------------------- *)

let conic = new_definition
  `conic s <=> !x c. x IN s /\ &0 <= c ==> (c % x) IN s`;;

let SUBSPACE_IMP_CONIC = `!s. subspace s ==> conic s`;;

let CONIC_EMPTY = `conic {}`;;

let CONIC_UNIV = `conic (UNIV:real^N->bool)`;;

let CONIC_INTERS = `(!s. s IN f ==> conic s) ==> conic(INTERS f)`;;

let CONIC_LINEAR_IMAGE = `!f s. conic s /\ linear f ==> conic(IMAGE f s)`;;

let CONIC_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (conic (IMAGE f s) <=> conic s)`;;

add_linear_invariants [CONIC_LINEAR_IMAGE_EQ];;

let CONIC_MUL = `!s c x:real^N. conic s /\ x IN s /\ &0 <= c ==> (c % x) IN s`;;

let CONIC_CONIC_HULL = `!s. conic(conic hull s)`;;

let CONIC_HULL_EQ = `!s. (conic hull s = s) <=> conic s`;;

let CONIC_HULL_UNIV = `conic hull (:real^N) = (:real^N)`;;

let CONIC_NEGATIONS = `!s. conic s ==> conic (IMAGE (--) s)`;;

let CONIC_SPAN = `!s. conic(span s)`;;

let CONIC_HULL_EXPLICIT = `!s:real^N->bool. conic hull s = {c % x | &0 <= c /\ x IN s}`;;

let CONIC_HULL_AS_IMAGE = `!s:real^N->bool.
        conic hull s = IMAGE (\z. drop(fstcart z) % sndcart z)
                             ({t | &0 <= drop t} PCROSS s)`;;

let CONIC_HULL_POINTLESS_AS_IMAGE = `!s:real^N->bool.
        conic hull s DELETE vec 0 =
        IMAGE (\z. drop(fstcart z) % sndcart z)
              ({t | &0 < drop t} PCROSS (s DELETE vec 0))`;;

let CONIC_HULL_LINEAR_IMAGE = `!f s. linear f ==> conic hull (IMAGE f s) = IMAGE f (conic hull s)`;;

add_linear_invariants [CONIC_HULL_LINEAR_IMAGE];;

let CONIC_HULL_IMAGE_SCALE = `!c s:real^N->bool.
        (!x. x IN s ==> &0 < c x)
        ==> conic hull (IMAGE (\x. c x % x) s) = conic hull s`;;

let CONVEX_CONIC_HULL = `!s:real^N->bool. convex s ==> convex (conic hull s)`;;

let CONIC_HALFSPACE_LE = `!a. conic {x | a dot x <= &0}`;;

let CONIC_HALFSPACE_GE = `!a. conic {x | a dot x >= &0}`;;

let CONIC_HULL_EMPTY = `conic hull {} = {}`;;

let CONIC_CONTAINS_0 = `!s:real^N->bool. conic s ==> (vec 0 IN s <=> ~(s = {}))`;;

let CONIC_HULL_EQ_EMPTY = `!s. (conic hull s = {}) <=> (s = {})`;;

let CONIC_SUMS = `!s t. conic s /\ conic t ==> conic {x + y:real^N | x IN s /\ y IN t}`;;

let CONIC_PCROSS = `!s:real^M->bool t:real^N->bool.
        conic s /\ conic t ==> conic(s PCROSS t)`;;

let CONIC_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        conic(s PCROSS t) <=> s = {} \/ t = {} \/ conic s /\ conic t`;;

let CONIC_POSITIVE_ORTHANT = `conic {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}`;;

let CONIC_HULL_0 = `conic hull {vec 0} = {vec 0}`;;

let CONIC_HULL_CONTAINS_0 = `!s:real^N->bool. vec 0 IN conic hull s <=> ~(s = {})`;;

let CONIC_HULL_EQ_SING = `!s x:real^N. conic hull s = {x} <=> s = {vec 0} /\ x = vec 0`;;

let CONIC_HULL_INTER_AFFINE_HULL = `!s f:real^N->bool.
        f SUBSET s /\ ~(vec 0 IN affine hull s)
        ==> (conic hull f) INTER (affine hull s) = f`;;

let SEPARATE_CLOSED_CONES = `!c d:real^N->bool.
        conic c /\ closed c /\ conic d /\ closed d /\ c INTER d SUBSET {vec 0}
        ==> ?e. &0 < e /\
                !x y. x IN c /\ y IN d
                      ==> dist(x,y) >= e * max (norm x) (norm y)`;;

let CONTINUOUS_ON_COMPACT_SURFACE_PROJECTION = `!s:real^N->bool v d:real^N->real.
        compact s /\ s SUBSET (v DELETE (vec 0)) /\ conic v /\
        (!x k. x IN v DELETE (vec 0) ==> (&0 < k /\ (k % x) IN s <=> d x = k))
        ==> (\x. d x % x) continuous_on (v DELETE (vec 0))`;;

(* ------------------------------------------------------------------------- *)
(* Affine dependence and consequential theorems (from Lars Schewe).          *)
(* ------------------------------------------------------------------------- *)

let affine_dependent = new_definition
 `affine_dependent (s:real^N -> bool) <=>
        ?x. x IN s /\ x IN (affine hull (s DELETE x))`;;

let AFFINE_DEPENDENT_EXPLICIT = `!p. affine_dependent (p:real^N -> bool) <=>
            (?s u. FINITE s /\ s SUBSET p /\
                   sum s u = &0 /\
                   (?v. v IN s /\ ~(u v = &0)) /\
                   vsum s (\v. u v % v) = (vec 0):real^N)`;;

let AFFINE_DEPENDENT_EXPLICIT_FINITE = `!s. FINITE(s:real^N -> bool)
       ==> (affine_dependent s <=>
            ?u. sum s u = &0 /\
                (?v. v IN s /\ ~(u v = &0)) /\
                vsum s (\v. u v % v) = vec 0)`;;

let AFFINE_DEPENDENT_TRANSLATION_EQ = `!a s. affine_dependent (IMAGE (\x. a + x) s) <=> affine_dependent s`;;

add_translation_invariants [AFFINE_DEPENDENT_TRANSLATION_EQ];;

let AFFINE_DEPENDENT_TRANSLATION = `!s a. affine_dependent s ==> affine_dependent (IMAGE (\x. a + x) s)`;;

let AFFINE_DEPENDENT_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (affine_dependent(IMAGE f s) <=> affine_dependent s)`;;

add_linear_invariants [AFFINE_DEPENDENT_LINEAR_IMAGE_EQ];;

let AFFINE_DEPENDENT_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        affine_dependent(s)
        ==> affine_dependent(IMAGE f s)`;;

let AFFINE_DEPENDENT_MONO = `!s t:real^N->bool. affine_dependent s /\ s SUBSET t ==> affine_dependent t`;;

let AFFINE_INDEPENDENT_EMPTY = `~(affine_dependent {})`;;

let AFFINE_INDEPENDENT_1 = `!a:real^N. ~(affine_dependent {a})`;;

let AFFINE_INDEPENDENT_2 = `!a b:real^N. ~(affine_dependent {a,b})`;;

let AFFINE_INDEPENDENT_SUBSET = `!s t. ~affine_dependent t /\ s SUBSET t ==> ~affine_dependent s`;;

let AFFINE_INDEPENDENT_DELETE = `!s a. ~affine_dependent s ==> ~affine_dependent(s DELETE a)`;;

(* ------------------------------------------------------------------------- *)
(* Coplanarity, and collinearity in terms of affine hull.                    *)
(* ------------------------------------------------------------------------- *)

let coplanar = new_definition
 `coplanar s <=> ?u v w. s SUBSET affine hull {u,v,w}`;;

let COLLINEAR_AFFINE_HULL = `!s:real^N->bool. collinear s <=> ?u v. s SUBSET affine hull {u,v}`;;

let COLLINEAR_IMP_COPLANAR = `!s. collinear s ==> coplanar s`;;

let COPLANAR_SMALL = `!s. FINITE s /\ CARD s <= 3 ==> coplanar s`;;

let COPLANAR_EMPTY = `coplanar {}`;;

let COPLANAR_SING = `!a. coplanar {a}`;;

let COPLANAR_2 = `!a b. coplanar {a,b}`;;

let COPLANAR_3 = `!a b c. coplanar {a,b,c}`;;

let COLLINEAR_AFFINE_HULL_COLLINEAR = `!s. collinear(affine hull s) <=> collinear s`;;

let COPLANAR_AFFINE_HULL_COPLANAR = `!s. coplanar(affine hull s) <=> coplanar s`;;

let COPLANAR_TRANSLATION_EQ = `!a:real^N s. coplanar(IMAGE (\x. a + x) s) <=> coplanar s`;;

let COPLANAR_TRANSLATION = `!a:real^N s. coplanar s ==> coplanar(IMAGE (\x. a + x) s)`;;

add_translation_invariants [COPLANAR_TRANSLATION_EQ];;

let COPLANAR_LINEAR_IMAGE = `!f:real^M->real^N s. coplanar s /\ linear f ==> coplanar(IMAGE f s)`;;

let COPLANAR_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (coplanar (IMAGE f s) <=> coplanar s)`;;

add_linear_invariants [COPLANAR_LINEAR_IMAGE_EQ];;

let COPLANAR_SUBSET = `!s t. coplanar t /\ s SUBSET t ==> coplanar s`;;

let AFFINE_HULL_3_IMP_COLLINEAR = `!a b c. c IN affine hull {a,b} ==> collinear {a,b,c}`;;

let COLLINEAR_3_AFFINE_HULL = `!a b c:real^N.
        ~(a = b) ==> (collinear {a,b,c} <=> c IN affine hull {a,b})`;;

let COLLINEAR_3_EQ_AFFINE_DEPENDENT = `!a b c:real^N.
        collinear{a,b,c} <=>
                a = b \/ a = c \/ b = c \/ affine_dependent {a,b,c}`;;

let AFFINE_DEPENDENT_IMP_COLLINEAR_3 = `!a b c:real^N. affine_dependent {a,b,c} ==> collinear{a,b,c}`;;

let COLLINEAR_3_IN_AFFINE_HULL = `!v0 v1 x:real^N.
        ~(v1 = v0)
        ==> (collinear {v0,v1,x} <=> x IN affine hull {v0,v1})`;;

let COLLINEAR_3_EXPLICIT = `!x y z:real^N.
        collinear {x,y,z} <=>
        ?a b c. a % x + b % y + c % z = vec 0 /\
                a + b + c = &0 /\ ~(a = &0 /\ b = &0 /\ c = &0)`;;

(* ------------------------------------------------------------------------- *)
(* A general lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CONNECTED = `!s:real^N->bool. convex s ==> connected s`;;

(* ------------------------------------------------------------------------- *)
(* Convex functions into the reals.                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("convex_on",(12,"right"));;

let convex_on = new_definition
  `f convex_on s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> f(u % x + v % y) <= u * f(x) + v * f(y)`;;

let CONVEX_ON_EMPTY = `!f:real^N->real. f convex_on {}`;;

let CONVEX_ON_SUBSET = `!f s t. f convex_on t /\ s SUBSET t ==> f convex_on s`;;

let CONVEX_ON_EQ = `!f g s. convex s /\ (!x. x IN s ==> f x = g x) /\ f convex_on s
           ==> g convex_on s`;;

let CONVEX_ON_CONST = `!s a. (\x. a) convex_on s`;;

let LINEAR_IMP_CONVEX_ON = `!f s:real^N->bool. linear (lift o f) ==> f convex_on s`;;

let CONVEX_ON_SING = `!f a:real^N. f convex_on {a}`;;

let CONVEX_ADD = `!s f g. f convex_on s /\ g convex_on s ==> (\x. f(x) + g(x)) convex_on s`;;

let CONVEX_ADD_EQ = `!a f s:real^N->bool. (\x. a + f x) convex_on s <=> f convex_on s`;;

let CONVEX_CMUL = `!s c f. &0 <= c /\ f convex_on s ==> (\x. c * f(x)) convex_on s`;;

let CONVEX_MAX = `!f g s. f convex_on s /\ g convex_on s
           ==> (\x. max (f x) (g x)) convex_on s`;;

let CONVEX_ON_SUM = `!t f:A->real^N->real s.
         FINITE s /\ (!a. a IN s ==> f a convex_on t)
         ==> (\x. sum s (\a. f a x)) convex_on t`;;

let CONVEX_ON_IMP_MIDPOINT_CONVEX = `!f s x y:real^N.
        f convex_on s /\ x IN s /\ y IN s
        ==> f(midpoint(x,y)) <= (f x + f y) / &2`;;

let CONVEX_LOWER = `!f s x y:real^N u v.
        f convex_on s /\
        x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
        ==> f(u % x + v % y) <= max (f(x)) (f(y))`;;

let CONVEX_LOWER_SEGMENT = `!f s a b x:real^N.
        f convex_on s /\ a IN s /\ b IN s /\ x IN segment[a,b]
        ==> f(x) <= max (f a) (f b)`;;

let CONVEX_LOWER_SEGMENT_LT = `!f s a b x:real^N.
        f convex_on s /\ a IN s /\ b IN s /\
        x IN segment[a,b] /\ ~(x = b) /\ f a < f b
        ==> f x < f b`;;

let CONVEX_LOCAL_GLOBAL_MINIMUM_SEGMENT = `!f s x:real^N.
        f convex_on s /\ x IN s /\
        (!z. z IN s /\ ~(z = x)
             ==> ?y. y IN segment[x,z] /\ y IN s /\ ~(y = x) /\ f(x) <= f(y))
        ==> !z. z IN s ==> f(x) <= f(z)`;;

let CONVEX_LOCAL_GLOBAL_MINIMUM_GEN = `!f s t x:real^N.
       f convex_on s /\ x IN t /\
       open_in (subtopology euclidean (affine hull s)) t /\
       t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`;;

let CONVEX_LOCAL_GLOBAL_MINIMUM = `!f s t x:real^N.
       f convex_on s /\ x IN t /\ open t /\ t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`;;

let CONVEX_DISTANCE = `!s a. (\x. dist(a,x)) convex_on s`;;

let CONVEX_NORM = `!s:real^N->bool. norm convex_on s`;;

let CONVEX_ON_COMPOSE_LINEAR = `!f g:real^M->real^N s.
        f convex_on (IMAGE g s) /\ linear g ==> (f o g) convex_on s`;;

let CONVEX_ON_TRANSLATION = `!f a:real^N.
        f convex_on (IMAGE (\x. a + x) s) <=> (\x. f(a + x)) convex_on s`;;

let LINEAR_CONVEX_ON_1 = `!f:real^N->real^1.
        linear f <=>
        f(vec 0) = vec 0 /\
        (drop o f) convex_on UNIV /\
        ((--) o drop o f) convex_on UNIV`;;

let CONVEX_CONCAVE_EQ_AFFINE = `!f:real^N->real.
        f convex_on UNIV /\ ((--) o f) convex_on UNIV <=>
        (?a b. f = \x. a dot x + b)`;;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls are convex and hence connected.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_BALL = `!x:real^N e. convex(ball(x,e))`;;

let CONNECTED_BALL = `!x:real^N e. connected(ball(x,e))`;;

let CONVEX_CBALL = `!x:real^N e. convex(cball(x,e))`;;

let CONNECTED_CBALL = `!x:real^N e. connected(cball(x,e))`;;

let CONVEX_INTERMEDIATE_BALL = `!a:real^N r t. ball(a,r) SUBSET t /\ t SUBSET cball(a,r) ==> convex t`;;

let FRONTIER_OF_CONNECTED_COMPONENT_SUBSET = `!s x:real^N. frontier(connected_component s x) SUBSET frontier s`;;

let FRONTIER_OF_COMPONENTS_SUBSET = `!s c:real^N->bool.
        c IN components s ==> frontier c SUBSET frontier s`;;

let FRONTIER_OF_COMPONENTS_CLOSED_COMPLEMENT = `!s c. closed s /\ c IN components ((:real^N) DIFF s)
         ==> frontier c SUBSET s`;;

let CONTAINS_COMPONENT_OF_COMPACT_FRONTIER = `!s:real^N->bool c.
        compact s /\ c IN components s
        ==> ?d. d IN components(frontier s) /\ d SUBSET c`;;

let CARD_LE_COMPONENTS_FRONTIER = `!s:real^N->bool. compact s ==> components s <=_c components(frontier s)`;;

let CONTAINS_COMPONENT_OF_CLOSURE_FRONTIER = `!s:real^N->bool c.
        bounded s /\ c IN components(closure s)
        ==> ?d. d IN components(frontier s) /\ d SUBSET c`;;

let CARD_LE_COMPONENTS_CLOSURE_FRONTIER = `!s:real^N->bool.
        bounded s ==> components(closure s) <=_c components(frontier s)`;;

(* ------------------------------------------------------------------------- *)
(* A couple of lemmas about components (see Newman IV, 3.3 and 3.4).         *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_UNION_CLOPEN_IN_COMPLEMENT = `!s t u:real^N->bool.
        connected s /\ connected u /\ s SUBSET u /\
        open_in (subtopology euclidean (u DIFF s)) t /\
        closed_in (subtopology euclidean (u DIFF s)) t
        ==> connected (s UNION t)`;;

let COMPONENT_COMPLEMENT_CONNECTED = `!s u c:real^N->bool.
        connected s /\ connected u /\ s SUBSET u /\ c IN components (u DIFF s)
        ==> connected(u DIFF c)`;;

(* ------------------------------------------------------------------------- *)
(* Condition for an open map's image to contain a ball.                      *)
(* ------------------------------------------------------------------------- *)

let BALL_SUBSET_OPEN_MAP_IMAGE = `!f:real^M->real^N s a r.
        bounded s /\ f continuous_on closure s /\ open(IMAGE f (interior s)) /\
        a IN s /\ &0 < r /\ (!z. z IN frontier s ==> r <= norm(f z - f a))
        ==> ball(f(a),r) SUBSET IMAGE f s`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on sets preserve convexity.                         *)
(* ------------------------------------------------------------------------- *)

let CONVEX_SCALING = `!s c. convex s ==> convex (IMAGE (\x. c % x) s)`;;

let CONVEX_SCALING_EQ = `!s:real^N->bool c. convex (IMAGE (\x. c % x) s) <=> c = &0 \/ convex s`;;

let CONVEX_NEGATIONS = `!s. convex s ==> convex (IMAGE (--) s)`;;

let CONVEX_SUMS = `!s t. convex s /\ convex t ==> convex {x + y | x IN s /\ y IN t}`;;

let CONVEX_DIFFERENCES = `!s t. convex s /\ convex t ==> convex {x - y | x IN s /\ y IN t}`;;

let CONVEX_AFFINITY_EQ = `!s m c:real^N.
        convex (IMAGE (\x. m % x + c) s) <=> m = &0 \/ convex s`;;

let CONVEX_AFFINITY = `!s m c:real^N. convex s ==> convex (IMAGE (\x. m % x + c) s)`;;

let CONVEX_LINEAR_PREIMAGE = `!f:real^M->real^N.
     linear f /\ convex s ==> convex {x | f(x) IN s}`;;

let CONVEX_SUMS_MULTIPLES = `!s:real^N->bool c d.
        convex s /\ &0 <= c /\ &0 <= d
        ==> {c % x + d % y | x IN s /\ y IN s} = IMAGE (\x. (c + d) % x) s`;;

let CONVEX_TRANSLATION_SUBSET_PREIMAGE = `!s t:real^N->bool.
        convex t ==> convex {a | IMAGE (\x. a + x) s SUBSET t}`;;

let CONVEX_TRANSLATION_SUPERSET_PREIMAGE = `!s t:real^N->bool.
        convex t ==> convex {a | s SUBSET IMAGE (\x. a + x) t}`;;

(* ------------------------------------------------------------------------- *)
(* Some interesting "cancellation" properties for sum-sets.                  *)
(* ------------------------------------------------------------------------- *)

let SUBSET_SUMS_LCANCEL = `!s t u:real^N->bool.
        ~(s = {}) /\ bounded s /\ closed u /\ convex u /\
        {x + y | x IN s /\ y IN t} SUBSET {x + z | x IN s /\ z IN u}
        ==> t SUBSET u`;;

let SUBSET_SUMS_RCANCEL = `!s t u:real^N->bool.
        closed t /\ convex t /\ bounded u /\ ~(u = {}) /\
        {x + z | x IN s /\ z IN u} SUBSET {y + z | y IN t /\ z IN u}
        ==> s SUBSET t`;;

let EQ_SUMS_LCANCEL = `!s t u.
        ~(s = {}) /\ bounded s /\
        closed t /\ convex t /\ closed u /\ convex u /\
        {x + y | x IN s /\ y IN t} = {x + z | x IN s /\ z IN u}
        ==> t = u`;;

let EQ_SUMS_RCANCEL = `!s t u.
        closed s /\ convex s /\ closed t /\ convex t /\
        bounded u /\ ~(u = {}) /\
        {x + z | x IN s /\ z IN u} = {y + z | y IN t /\ z IN u}
        ==> s = t`;;

(* ------------------------------------------------------------------------- *)
(* Convex hull.                                                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CONVEX_HULL = `!s. convex(convex hull s)`;;

let CONVEX_HULL_EQ = `!s. (convex hull s = s) <=> convex s`;;

let CONVEX_HULLS_EQ = `!s t. s SUBSET convex hull t /\ t SUBSET convex hull s
         ==> convex hull s = convex hull t`;;

let IS_CONVEX_HULL = `!s. convex s <=> ?t. s = convex hull t`;;

let CONVEX_HULL_CONTAINS = `!s a b x:real^N.
        a IN convex hull s /\ b IN convex hull s /\ x IN segment[a,b]
        ==> x IN convex hull s`;;

let MIDPOINTS_IN_CONVEX_HULL = `!x:real^N s. x IN convex hull s /\ y IN convex hull s
         ==> midpoint(x,y) IN convex hull s`;;

let CONVEX_HULL_UNIV = `convex hull (:real^N) = (:real^N)`;;

let BOUNDED_CONVEX_HULL = `!s:real^N->bool. bounded s ==> bounded(convex hull s)`;;

let BOUNDED_CONVEX_HULL_EQ = `!s. bounded(convex hull s) <=> bounded s`;;

let FINITE_IMP_BOUNDED_CONVEX_HULL = `!s. FINITE s ==> bounded(convex hull s)`;;

(* ------------------------------------------------------------------------- *)
(* Stepping theorems for convex hulls of finite sets.                        *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_EMPTY = `convex hull {} = {}`;;

let CONVEX_HULL_EQ_EMPTY = `!s. (convex hull s = {}) <=> (s = {})`;;

let CONVEX_HULL_SING = `!a. convex hull {a} = {a}`;;

let CONVEX_HULL_EQ_SING = `!s a:real^N. convex hull s = {a} <=> s = {a}`;;

let CONVEX_HULL_INSERT = `!s a. ~(s = {})
         ==> convex hull (a INSERT s) =
               {x:real^N | ?u v b. &0 <= u /\ &0 <= v /\ u + v = &1 /\
                                    b IN (convex hull s) /\
                                    x = u % a + v % b}`;;

let CONVEX_HULL_INSERT_ALT = `!s a:real^N.
      convex hull (a INSERT s) =
      if s = {} then {a}
      else {(&1 - u) % a + u % x | &0 <= u /\ u <= &1 /\ x IN convex hull s}`;;

let CONVEX_HULL_INSERT_SEGMENTS = `!s a:real^N.
        convex hull (a INSERT s) =
        if s = {} then {a} else  UNIONS {segment[a,x] | x IN convex hull s}`;;

(* ------------------------------------------------------------------------- *)
(* Explicit expressions for convex hull.                                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_INDEXED = `!s. convex hull s =
        {y:real^N | ?k u x. (!i. 1 <= i /\ i <= k ==> &0 <= u i /\ x i IN s) /\
                            (sum (1..k) u = &1) /\
                            (vsum (1..k) (\i. u i % x i) = y)}`;;

let CONVEX_HULL_FINITE_IMAGE_EXPLICIT = `!f:A->real^N k.
        FINITE k
        ==> convex hull (IMAGE f k) =
             {y | ?u. (!a. a IN k ==> &0 <= u a) /\
                      sum k u = &1 /\
                      vsum k (\a. u a % f a) = y}`;;

(* ------------------------------------------------------------------------- *)
(* Another formulation from Lars Schewe.                                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_EXPLICIT = `!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
             (!x. x IN s ==> &0 <= u x) /\
             sum s u = &1 /\ vsum s (\v. u v % v) = y}`;;

let CONVEX_HULL_FINITE = `!s:real^N->bool.
        convex hull s =
          {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                   sum s u = &1 /\
                   vsum s (\x. u x % x) = y}`;;

let CONVEX_HULL_IMAGE = `!f:A->real^N k.
        convex hull (IMAGE f k) =
             {y | ?c u. FINITE c /\ c SUBSET k /\
                        (!a. a IN c ==> &0 <= u a) /\
                        sum c u = &1 /\
                        vsum c (\a. u a % f a) = y}`;;

let CONVEX_HULL_IMAGE_LT = `!f:A->real^N k.
        convex hull (IMAGE f k) =
             {y | ?c u. FINITE c /\ c SUBSET k /\
                        (!a. a IN c ==> &0 < u a) /\
                        sum c u = &1 /\
                        vsum c (\a. u a % f a) = y}`;;

let CONVEX_HULL_UNION_EXPLICIT = `!s t:real^N->bool.
        convex s /\ convex t
        ==> convex hull (s UNION t) =
             s UNION t UNION
             {(&1 - u) % x + u % y | x IN s /\ y IN t /\ &0 <= u /\ u <= &1}`;;

let CONVEX_HULL_UNION_NONEMPTY_EXPLICIT = `!s t:real^N->bool.
        convex s /\ ~(s = {}) /\ convex t /\ ~(t = {})
        ==> convex hull (s UNION t) =
             {(&1 - u) % x + u % y | x IN s /\ y IN t /\ &0 <= u /\ u <= &1}`;;

let CONVEX_HULL_UNION_UNIONS = `!f s:real^N->bool.
        convex(UNIONS f) /\ ~(f = {})
        ==> convex hull (s UNION UNIONS f) =
            UNIONS {convex hull (s UNION t) | t IN f}`;;

(* ------------------------------------------------------------------------- *)
(* A stepping theorem for that expansion.                                    *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_FINITE_STEP = `((?u. (!x. x IN {} ==> &0 <= u x) /\
         sum {} u = w /\
         vsum {} (\x. u(x) % x) = y) <=> w = &0 /\ y = vec 0) /\
   (FINITE(s:real^N->bool)
    ==> ((?u. (!x. x IN (a INSERT s) ==> &0 <= u x) /\
              sum (a INSERT s) u = w /\
              vsum (a INSERT s) (\x. u(x) % x) = y) <=>
         ?v. &0 <= v /\
             ?u. (!x. x IN s ==> &0 <= u x) /\
              sum s u = w - v /\
              vsum s (\x. u(x) % x) = y - v % a))`;;

(* ------------------------------------------------------------------------- *)
(* Hence some special cases.                                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_2 = `!a b. convex hull {a,b} =
         {u % a + v % b | &0 <= u /\ &0 <= v /\ u + v = &1}`;;

let CONVEX_HULL_2_ALT = `!a b. convex hull {a,b} = {a + u % (b - a) | &0 <= u /\ u <= &1}`;;

let CONVEX_HULL_3 = `convex hull {a,b,c} =
    { u % a + v % b + w % c |
      &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1}`;;

let CONVEX_HULL_3_ALT = `!a b c. convex hull {a,b,c} =
                {a + u % (b - a) + v % (c - a) |
                   &0 <= u /\ &0 <= v /\ u + v <= &1}`;;

let CONVEX_HULL_SUMS = `!s t:real^N->bool.
        convex hull {x + y | x IN s /\ y IN t} =
        {x + y | x IN convex hull s /\ y IN convex hull t}`;;

let AFFINE_HULL_SUMS = `!s t:real^N->bool.
        affine hull {x + y | x IN s /\ y IN t} =
        {x + y | x IN affine hull s /\ y IN affine hull t}`;;

let AFFINE_HULL_PCROSS = `(!s:real^M->bool t:real^N->bool.
        affine hull (s PCROSS t) =
        (affine hull s) PCROSS (affine hull t))`
and CONVEX_HULL_PCROSS = `(!s:real^M->bool t:real^N->bool.
        convex hull (s PCROSS t) =
        (convex hull s) PCROSS (convex hull t))`;;

let BILINEAR_IN_CONVEX_HULL = `!(f:real^M->real^N->real^P) s t x y.
        bilinear f /\ x IN convex hull s /\ y IN convex hull t
        ==> f x y IN convex hull { f a b | a IN s /\ b IN t}`;;

(* ------------------------------------------------------------------------- *)
(* Relations among closure notions and corresponding hulls.                  *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_IMP_AFFINE = `!s. subspace s ==> affine s`;;

let AFFINE_IMP_CONVEX = `!s. affine s ==> convex s`;;

let SUBSPACE_IMP_CONVEX = `!s. subspace s ==> convex s`;;

let AFFINE_HULL_SUBSET_SPAN = `!s. (affine hull s) SUBSET (span s)`;;

let CONVEX_HULL_SUBSET_SPAN = `!s. (convex hull s) SUBSET (span s)`;;

let CONVEX_HULL_SUBSET_AFFINE_HULL = `!s. (convex hull s) SUBSET (affine hull s)`;;

let COLLINEAR_CONVEX_HULL_COLLINEAR = `!s:real^N->bool. collinear(convex hull s) <=> collinear s`;;

let AFFINE_SPAN = `!s. affine(span s)`;;

let CONVEX_SPAN = `!s. convex(span s)`;;

let SEGMENT_SUBSET_LINE = `(!a b:real^N. segment[a,b] SUBSET affine hull {a,b}) /\
   (!a b:real^N. segment(a,b) SUBSET affine hull {a,b})`;;

let SPAN_CONVEX_HULL = `!s:real^N->bool. span(convex hull s) = span s`;;

let DIM_CONVEX_HULL = `!s:real^N->bool. dim(convex hull s) = dim s`;;

let AFFINE_EQ_SUBSPACE = `!s:real^N->bool. vec 0 IN s ==> (affine s <=> subspace s)`;;

let AFFINE_IMP_SUBSPACE = `!s. affine s /\ vec 0 IN s ==> subspace s`;;

let SUBSPACE_EQ_AFFINE = `!s:real^N->bool. subspace s <=> affine s /\ vec 0 IN s`;;

let AFFINE_HULL_EQ_SPAN = `!s:real^N->bool. (vec 0) IN affine hull s ==> affine hull s = span s`;;

let SPAN_AFFINE_HULL_INSERT = `!s:real^N->bool. span s = affine hull (vec 0 INSERT s)`;;

let CLOSED_AFFINE = `!s:real^N->bool. affine s ==> closed s`;;

let CLOSED_AFFINE_HULL = `!s. closed(affine hull s)`;;

let CLOSURE_SUBSET_AFFINE_HULL = `!s. closure s SUBSET affine hull s`;;

let AFFINE_HULL_CLOSURE = `!s:real^N->bool. affine hull (closure s) = affine hull s`;;

let AFFINE_HULL_EQ_SPAN_EQ = `!s:real^N->bool. (affine hull s = span s) <=> (vec 0) IN affine hull s`;;

let AFFINE_DEPENDENT_IMP_DEPENDENT = `!s. affine_dependent s ==> dependent s`;;

let DEPENDENT_AFFINE_DEPENDENT_CASES = `!s:real^N->bool.
        dependent s <=> affine_dependent s \/ (vec 0) IN affine hull s`;;

let DEPENDENT_IMP_AFFINE_DEPENDENT = `!a:real^N s. dependent {x - a | x IN s} /\ ~(a IN s)
                ==> affine_dependent(a INSERT s)`;;

let AFFINE_DEPENDENT_BIGGERSET = `!s:real^N->bool.
        (FINITE s ==> CARD s >= dimindex(:N) + 2) ==> affine_dependent s`;;

let AFFINE_DEPENDENT_BIGGERSET_GENERAL = `!s:real^N->bool. (FINITE s ==> CARD s >= dim s + 2) ==> affine_dependent s`;;

let AFFINE_INDEPENDENT_IMP_FINITE = `!s:real^N->bool. ~(affine_dependent s) ==> FINITE s`;;

let AFFINE_INDEPENDENT_CARD_LE = `!s:real^N->bool. ~(affine_dependent s) ==> CARD s <= dimindex(:N) + 1`;;

let AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL = `!s t:real^N->bool.
        ~affine_dependent s /\ t SUBSET s
        ==> convex hull t = affine hull t INTER convex hull s`;;

let DISJOINT_AFFINE_HULL = `!s t u:real^N->bool.
        ~affine_dependent s /\ t SUBSET s /\ u SUBSET s /\ DISJOINT t u
        ==> DISJOINT (affine hull t) (affine hull u)`;;

let AFFINE_INDEPENDENT_SPAN_EQ = `!s. ~(affine_dependent s) /\ CARD s = dimindex(:N) + 1
       ==> affine hull s = (:real^N)`;;

let AFFINE_INDEPENDENT_SPAN_GT = `!s:real^N->bool.
        ~(affine_dependent s) /\ dimindex(:N) < CARD s
        ==> affine hull s = (:real^N)`;;

let EMPTY_INTERIOR_AFFINE_HULL = `!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N)
        ==> interior(affine hull s) = {}`;;

let EMPTY_INTERIOR_CONVEX_HULL = `!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N)
        ==> interior(convex hull s) = {}`;;

let AFFINE_DEPENDENT_CHOOSE = `!s a:real^N.
       ~(affine_dependent s)
       ==> (affine_dependent(a INSERT s) <=> ~(a IN s) /\ a IN affine hull s)`;;

let AFFINE_INDEPENDENT_INSERT = `!s a:real^N.
        ~(affine_dependent s) /\ ~(a IN affine hull s)
        ==> ~(affine_dependent(a INSERT s))`;;

let AFFINE_HULL_EXPLICIT_UNIQUE = `!s:real^N->bool u u'.
      ~(affine_dependent s) /\
      sum s u = &1 /\ sum s u' = &1 /\
      vsum s (\x. u x % x) = vsum s (\x. u' x % x)
      ==> !x. x IN s ==> u x = u' x`;;

let INDEPENDENT_IMP_AFFINE_DEPENDENT_0 = `!s. independent s ==> ~(affine_dependent(vec 0 INSERT s))`;;

let AFFINE_INDEPENDENT_STDBASIS = `~(affine_dependent
      ((vec 0:real^N) INSERT {basis i | 1 <= i /\ i <= dimindex (:N)}))`;;

let SPAN_CONIC_HULL = `!s:real^N->bool. span(conic hull s) = span s`;;

let CONIC_HULLS_EQ_IMP_SPANS_EQ = `!s t:real^N->bool.
        conic hull s = conic hull t ==> span s = span t`;;

let DIM_CONIC_HULL = `!s:real^N->bool. dim(conic hull s) = dim s`;;

let CONIC_HULL_SUBSET_SPAN = `!s:real^N->bool. conic hull s SUBSET span s`;;

let CONIC_IMAGE_MULTIPLE_EQ = `!s:real^N->bool. conic s <=> !a. &0 <= a ==> IMAGE (\x. a % x) s SUBSET s`;;

let CONIC_IMAGE_MULTIPLE = `!s:real^N->bool a. conic s /\ &0 < a ==> IMAGE (\x. a % x) s = s`;;

(* ------------------------------------------------------------------------- *)
(* Nonempty affine sets are translates of (unique) subspaces.                *)
(* ------------------------------------------------------------------------- *)

let AFFINE_TRANSLATION_SUBSPACE = `!t:real^N->bool.
        affine t /\ ~(t = {}) <=> ?a s. subspace s /\ t = IMAGE (\x. a + x) s`;;

let AFFINE_TRANSLATION_UNIQUE_SUBSPACE = `!t:real^N->bool.
        affine t /\ ~(t = {}) <=>
        ?!s. ?a. subspace s /\ t = IMAGE (\x. a + x) s`;;

let AFFINE_TRANSLATION_SUBSPACE_EXPLICIT = `!t:real^N->bool a.
        affine t /\ a IN t
        ==> subspace {x - a | x IN t} /\
            t = IMAGE (\x. a + x) {x - a | x IN t}`;;

(* ------------------------------------------------------------------------- *)
(* If we take a slice out of a set, we can do it perpendicularly,            *)
(* with the normal vector to the slice parallel to the affine hull.          *)
(* ------------------------------------------------------------------------- *)

let AFFINE_PARALLEL_SLICE = `!s a:real^N b.
       affine s
       ==> s INTER {x | a dot x <= b} = {} \/ s SUBSET {x | a dot x <= b} \/
           ?a' b'. ~(a' = vec 0) /\
                   s INTER {x | a' dot x <= b'} = s INTER {x | a dot x <= b} /\
                   s INTER {x | a' dot x = b'} = s INTER {x | a dot x = b} /\
                   !w. w IN s ==> (w + a') IN s`;;

(* ------------------------------------------------------------------------- *)
(* Affine dimension.                                                         *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_AFFINE_INDEPENDENT_SUBSET = `!s b:real^N->bool.
        b SUBSET s /\ ~(affine_dependent b) /\
        (!b'. b SUBSET b' /\ b' SUBSET s /\ ~(affine_dependent b') ==> b' = b)
        ==> s SUBSET (affine hull b)`;;

let MAXIMAL_AFFINE_INDEPENDENT_SUBSET_AFFINE = `!s b:real^N->bool.
        affine s /\ b SUBSET s /\ ~(affine_dependent b) /\
        (!b'. b SUBSET b' /\ b' SUBSET s /\ ~(affine_dependent b') ==> b' = b)
        ==> affine hull b = s`;;

let EXTEND_TO_AFFINE_BASIS = `!s u:real^N->bool.
        ~(affine_dependent s) /\ s SUBSET u
        ==> ?t. ~(affine_dependent t) /\ s SUBSET t /\ t SUBSET u /\
                affine hull t = affine hull u`;;

let AFFINE_BASIS_EXISTS = `!s:real^N->bool.
      ?b. ~(affine_dependent b) /\ b SUBSET s /\
          affine hull b = affine hull s`;;

let aff_dim = new_definition
  `aff_dim s =
        @d:int. ?b. affine hull b = affine hull s /\ ~(affine_dependent b) /\
                    &(CARD b) = d + &1`;;

let AFF_DIM = `!s. ?b. affine hull b = affine hull s /\
           ~(affine_dependent b) /\
           aff_dim s = &(CARD b) - &1`;;

let AFF_DIM_EMPTY = `aff_dim {} = -- &1`;;

let AFF_DIM_AFFINE_HULL = `!s. aff_dim(affine hull s) = aff_dim s`;;

let AFF_DIM_TRANSLATION_EQ = `!a:real^N s. aff_dim (IMAGE (\x. a + x) s) = aff_dim s`;;

add_translation_invariants [AFF_DIM_TRANSLATION_EQ];;

let AFFINE_HULL_CONIC_HULL = `!s:real^N->bool.
        affine hull (conic hull s) =
        if s = {} then {} else affine hull (vec 0 INSERT s)`;;

let AFFINE_INDEPENDENT_CARD_DIM_DIFFS = `!s a:real^N.
        ~affine_dependent s /\ a IN s
        ==> CARD s = dim {x - a | x IN s} + 1`;;

let AFF_DIM_DIM_0 = `!s:real^N->bool. vec 0 IN affine hull s ==> aff_dim s = &(dim s)`;;

let AFF_DIM_DIM_SUBSPACE = `!s:real^N->bool. subspace s ==> aff_dim s = &(dim s)`;;

let AFF_DIM_DIM_AFFINE_DIFFS_STRONG = `!a:real^N s. a IN affine hull s ==> aff_dim s = &(dim {x - a | x IN s})`;;

let AFF_DIM_DIM_AFFINE_DIFFS = `!a:real^N s. a IN s ==> aff_dim s = &(dim {x - a | x IN s})`;;

let AFF_DIM_LINEAR_IMAGE_LE = `!f:real^M->real^N s. linear f ==> aff_dim(IMAGE f s) <= aff_dim s`;;

let AFF_DIM_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> aff_dim(IMAGE f s) = aff_dim s`;;

add_linear_invariants [AFF_DIM_INJECTIVE_LINEAR_IMAGE];;

let AFF_DIM_AFFINE_INDEPENDENT = `!b:real^N->bool.
        ~(affine_dependent b) ==> aff_dim b = &(CARD b) - &1`;;

let AFF_DIM_UNIQUE = `!s b:real^N->bool.
        affine hull b = affine hull s /\ ~(affine_dependent b)
        ==> aff_dim s = &(CARD b) - &1`;;

let AFF_DIM_SING = `!a:real^N. aff_dim {a} = &0`;;

let AFF_DIM_LE_CARD = `!s:real^N->bool. FINITE s ==> aff_dim s <= &(CARD s) - &1`;;

let AFF_DIM_GE = `!s:real^N->bool. -- &1 <= aff_dim s`;;

let AFF_DIM_SUBSET = `!s t:real^N->bool. s SUBSET t ==> aff_dim s <= aff_dim t`;;

let AFF_DIM_LE_DIM = `!s:real^N->bool. aff_dim s <= &(dim s)`;;

let AFF_DIM_CONVEX_HULL = `!s:real^N->bool. aff_dim(convex hull s) = aff_dim s`;;

let AFF_DIM_CLOSURE = `!s:real^N->bool. aff_dim(closure s) = aff_dim s`;;

let AFF_DIM_2 = `!a b:real^N. aff_dim {a,b} = if a = b then &0 else &1`;;

let AFF_DIM_EQ_MINUS1 = `!s:real^N->bool. aff_dim s = -- &1 <=> s = {}`;;

let AFF_DIM_POS_LE = `!s:real^N->bool. &0 <= aff_dim s <=> ~(s = {})`;;

let AFF_DIM_EQ_0 = `!s:real^N->bool. aff_dim s = &0 <=> ?a. s = {a}`;;

let CONNECTED_IMP_PERFECT_AFF_DIM = `!s x:real^N.
        connected s /\ ~(aff_dim s = &0) /\ x IN s ==> x limit_point_of s`;;

let AFF_DIM_UNIV = `aff_dim(:real^N) = &(dimindex(:N))`;;

let AFF_DIM_EQ_AFFINE_HULL = `!s t:real^N->bool.
        s SUBSET t /\ aff_dim t <= aff_dim s
        ==> affine hull s = affine hull t`;;

let AFF_DIM_SUMS_INTER = `!s t:real^N->bool.
        affine s /\ affine t /\ ~(s INTER t = {})
        ==> aff_dim {x + y | x IN s /\ y IN t} =
                (aff_dim s + aff_dim t) - aff_dim(s INTER t)`;;

let AFF_DIM_PSUBSET = `!s t. (affine hull s) PSUBSET (affine hull t) ==> aff_dim s < aff_dim t`;;

let AFF_DIM_EQ_FULL_GEN = `!s t:real^N->bool.
        s SUBSET t
        ==> (aff_dim s = aff_dim t <=> affine hull s = affine hull t)`;;

let AFF_DIM_EQ_FULL = `!s. aff_dim s = &(dimindex(:N)) <=> affine hull s = (:real^N)`;;

let AFF_DIM_LE_UNIV = `!s:real^N->bool. aff_dim s <= &(dimindex(:N))`;;

let AFFINE_INDEPENDENT_IFF_CARD = `!s:real^N->bool.
        ~affine_dependent s <=> FINITE s /\ aff_dim s = &(CARD s) - &1`;;

let AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR = `!s t:real^N->bool.
        convex s /\ ~(s INTER interior t = {})
        ==> affine hull (s INTER t) = affine hull s`;;

let AFFINE_HULL_CONVEX_INTER_OPEN = `!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = affine hull s`;;

let AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR = `!s t:real^N->bool.
        affine s /\ ~(s INTER interior t = {})
        ==> affine hull (s INTER t) = s`;;

let AFFINE_HULL_AFFINE_INTER_OPEN = `!s t:real^N->bool.
        affine s /\ open t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = s`;;

let CONVEX_AND_AFFINE_INTER_OPEN = `!s t u:real^N->bool.
        convex s /\ affine t /\ open u /\
        s INTER u = t INTER u /\ ~(s INTER u = {})
        ==> affine hull s = t`;;

let AFFINE_HULL_CONVEX_INTER_OPEN_IN = `!s t:real^N->bool.
        convex s /\ open_in (subtopology euclidean (affine hull s)) t /\
        ~(s INTER t = {})
        ==> affine hull (s INTER t) = affine hull s`;;

let AFFINE_HULL_AFFINE_INTER_OPEN_IN = `!s t:real^N->bool.
        affine s /\ open_in (subtopology euclidean s) t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = s`;;

let AFFINE_HULL_OPEN_IN_CONVEX = `!s t:real^N->bool.
        convex s /\ open_in (subtopology euclidean s) t /\ ~(t = {})
        ==> affine hull t = affine hull s`;;

let AFFINE_HULL_OPEN_IN = `!s t:real^N->bool.
        open_in (subtopology euclidean (affine hull t)) s /\ ~(s = {})
        ==> affine hull s = affine hull t`;;

let AFFINE_HULL_OPEN_IN_AFFINE = `!u s:real^N->bool.
        affine u /\ open_in (subtopology euclidean u) s /\ ~(s = {})
        ==> affine hull s = u`;;

let AFFINE_HULL_OPEN = `!s. open s /\ ~(s = {}) ==> affine hull s = (:real^N)`;;

let AFFINE_HULL_NONEMPTY_INTERIOR = `!s. ~(interior s = {}) ==> affine hull s = (:real^N)`;;

let AFF_DIM_OPEN = `!s:real^N->bool. open s /\ ~(s = {}) ==> aff_dim s = &(dimindex(:N))`;;

let AFF_DIM_NONEMPTY_INTERIOR = `!s:real^N->bool. ~(interior s = {}) ==> aff_dim s = &(dimindex(:N))`;;

let EMPTY_INTERIOR_AFF_DIM = `!s:real^N->bool. aff_dim s < &(dimindex(:N)) ==> interior s = {}`;;

let SPAN_OPEN = `!s. open s /\ ~(s = {}) ==> span s = (:real^N)`;;

let DIM_OPEN = `!s:real^N->bool. open s /\ ~(s = {}) ==> dim s = dimindex(:N)`;;

let AFF_DIM_INSERT = `!a:real^N s.
        aff_dim (a INSERT s) =
        if a IN affine hull s then aff_dim s else aff_dim s + &1`;;

let AFF_DIM_DIM = `!s:real^N->bool.
        aff_dim s = if vec 0 IN affine hull s then &(dim s)
                    else &(dim s) - &1`;;

let AFF_DIM_CONIC_HULL_DIM = `!s:real^N->bool.
        aff_dim (conic hull s) = if s = {} then -- &1 else &(dim s)`;;

let AFFINE_BOUNDED_EQ_TRIVIAL = `!s:real^N->bool.
        affine s ==> (bounded s <=> s = {} \/ ?a. s = {a})`;;

let AFFINE_BOUNDED_EQ_LOWDIM = `!s:real^N->bool.
        affine s ==> (bounded s <=> aff_dim s <= &0)`;;

let COLLINEAR_AFF_DIM = `!s:real^N->bool. collinear s <=> aff_dim s <= &1`;;

let COPLANAR_AFF_DIM = `!s:real^N->bool. coplanar s <=> aff_dim s <= &2`;;

let HOMEOMORPHIC_AFFINE_SETS = `!s:real^M->bool t:real^N->bool.
        affine s /\ affine t /\ aff_dim s = aff_dim t ==> s homeomorphic t`;;

let AFF_DIM_OPEN_IN = `!s t:real^N->bool.
        ~(s = {}) /\ open_in (subtopology euclidean t) s /\ affine t
        ==> aff_dim s = aff_dim t`;;

let DIM_OPEN_IN = `!s t:real^N->bool.
        ~(s = {}) /\ open_in (subtopology euclidean t) s /\ subspace t
        ==> dim s = dim t`;;

let AFF_DIM_CONVEX_INTER_NONEMPTY_INTERIOR = `!s t:real^N->bool.
        convex s /\ ~(s INTER interior t = {})
        ==> aff_dim(s INTER t) = aff_dim s`;;

let AFF_DIM_CONVEX_INTER_OPEN = `!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> aff_dim(s INTER t) = aff_dim s`;;

let AFF_DIM_NONEMPTY_INTERIOR_OF = `!u s:real^N->bool.
        s SUBSET u /\ affine u /\
        ~((subtopology euclidean u) interior_of s = {})
        ==> aff_dim s = aff_dim u`;;

let EMPTY_INTERIOR_OF_AFF_DIM = `!u s:real^N->bool.
        affine u /\ aff_dim s < aff_dim u
        ==> (subtopology euclidean u) interior_of s = {}`;;

let AFFINE_HULL_HALFSPACE_LT = `!a b. affine hull {x | a dot x < b} =
         if a = vec 0 /\ b <= &0 then {} else (:real^N)`;;

let AFFINE_HULL_HALFSPACE_LE = `!a b. affine hull {x | a dot x <= b} =
         if a = vec 0 /\ b < &0 then {} else (:real^N)`;;

let AFFINE_HULL_HALFSPACE_GT = `!a b. affine hull {x | a dot x > b} =
         if a = vec 0 /\ b >= &0 then {} else (:real^N)`;;

let AFFINE_HULL_HALFSPACE_GE = `!a b. affine hull {x | a dot x >= b} =
         if a = vec 0 /\ b > &0 then {} else (:real^N)`;;

let AFF_DIM_HALFSPACE_LT = `!a:real^N b.
        aff_dim {x | a dot x < b} =
        if a = vec 0 /\ b <= &0 then --(&1) else &(dimindex(:N))`;;

let AFF_DIM_HALFSPACE_LE = `!a:real^N b.
        aff_dim {x | a dot x <= b} =
        if a = vec 0 /\ b < &0 then --(&1) else &(dimindex(:N))`;;

let AFF_DIM_HALFSPACE_GT = `!a:real^N b.
        aff_dim {x | a dot x > b} =
        if a = vec 0 /\ b >= &0 then --(&1) else &(dimindex(:N))`;;

let AFF_DIM_HALFSPACE_GE = `!a:real^N b.
        aff_dim {x | a dot x >= b} =
        if a = vec 0 /\ b > &0 then --(&1) else &(dimindex(:N))`;;

let CHOOSE_AFFINE_SUBSET = `!s:real^N->bool d.
        affine s /\ --(&1) <= d /\ d <= aff_dim s
        ==> ?t. affine t /\ t SUBSET s /\ aff_dim t = d`;;

let NONEMPTY_AFFINE_EXISTS = `!n a:real^N.
        &0 <= n /\ n <= &(dimindex(:N))
        ==> ?s. affine s /\ a IN s /\ aff_dim s = n`;;

let AFFINE_EXISTS = `!n. -- &1 <= n /\ n <= &(dimindex(:N))
       ==> ?s:real^N->bool. affine s /\ aff_dim s = n`;;

let AFF_DIM_CONIC_HULL = `!s:real^N->bool.
        aff_dim(conic hull s) =
        if s = {} \/ vec 0 IN affine hull s
        then aff_dim s else aff_dim s + &1`;;

let AFF_DIM_PCROSS = `!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {})
        ==> aff_dim(s PCROSS t) = aff_dim s + aff_dim t`;;

let AFF_DIM_UNION = `!s t:real^N->bool.
        affine s /\ affine t /\ ~(s INTER t = {})
        ==> aff_dim(s UNION t) =
            (aff_dim s + aff_dim t) - aff_dim(s INTER t)`;;

let COPLANAR_INTERSECTING_LINES = `!a b c d z:real^N.
        collinear {a,z,b} /\ collinear {c,z,d} ==> coplanar {z,a,b,c,d}`;;

let ISOMETRIC_HOMEOMORPHISM_AFFINE = `!s:real^M->bool t:real^N->bool.
        affine s /\ affine t /\ aff_dim s = aff_dim t
        ==> ?f g. homeomorphism (s,t) (f,g) /\
                  (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y)) /\
                  (!x y. x IN t /\ y IN t ==> dist(g x,g y) = dist(x,y))`;;

(* ------------------------------------------------------------------------- *)
(* Existence of a rigid transform between congruent sets.                    *)
(* ------------------------------------------------------------------------- *)

let RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS = `!x:A->real^N y:A->real^N s.
        (!i j. i IN s /\ j IN s ==> dist(x i,x j) = dist(y i,y j))
        ==> ?a f. orthogonal_transformation f /\
                  !i. i IN s ==> y i = a + f(x i)`;;

let RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS_STRONG = `!x:A->real^N y:A->real^N s t.
        t SUBSET s /\ affine hull (IMAGE y t) = affine hull (IMAGE y s) /\
        (!i j. i IN s /\ j IN t ==> dist(x i,x j) = dist(y i,y j))
        ==> ?a f. orthogonal_transformation f /\
                  !i. i IN s ==> y i = a + f(x i)`;;

let RIGID_TRANSFORMATION_BETWEEN_3 = `!a b c a' b' c':real^N.
        dist(a,b) = dist(a',b') /\
        dist(b,c) = dist(b',c') /\
        dist(c,a) = dist(c',a')
        ==> ?k f. orthogonal_transformation f /\
                  a' = k + f a /\ b' = k + f b /\ c' = k + f c`;;

let RIGID_TRANSFORMATION_BETWEEN_2 = `!a b a' b':real^N.
        dist(a,b) = dist(a',b')
        ==> ?k f. orthogonal_transformation f /\
                  a' = k + f a /\ b' = k + f b`;;

(* ------------------------------------------------------------------------- *)
(* Caratheodory's theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_CARATHEODORY_AFF_DIM = `!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
                          &(CARD s) <= aff_dim p + &1 /\
                          (!x. x IN s ==> &0 <= u x) /\
                          sum s u = &1 /\ vsum s (\v. u v % v) = y}`;;

let CARATHEODORY_AFF_DIM = `!p. convex hull p =
        {x:real^N | ?s. FINITE s /\ s SUBSET p /\
                         &(CARD s) <= aff_dim p + &1 /\
                        x IN convex hull s}`;;

let CONVEX_HULL_CARATHEODORY = `!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
                          CARD(s) <= dimindex(:N) + 1 /\
                          (!x. x IN s ==> &0 <= u x) /\
                          sum s u = &1 /\ vsum s (\v. u v % v) = y}`;;

let CARATHEODORY = `!p. convex hull p =
        {x:real^N | ?s. FINITE s /\ s SUBSET p /\
                        CARD(s) <= dimindex(:N) + 1 /\
                        x IN convex hull s}`;;

(* ------------------------------------------------------------------------- *)
(* Some results on decomposing convex hulls, e.g. simplicial subdivision.    *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_INTER = `(!s t:real^N->bool.
        ~(affine_dependent(s UNION t))
        ==> affine hull s INTER affine hull t = affine hull (s INTER t))`
and CONVEX_HULL_INTER = `(!s t:real^N->bool.
        ~(affine_dependent (s UNION t))
        ==> convex hull s INTER convex hull t = convex hull (s INTER t))`;;

let AFFINE_HULL_INTERS = `!s:(real^N->bool)->bool.
        ~(affine_dependent(UNIONS s))
        ==> affine hull (INTERS s) = INTERS {affine hull t | t IN s}`;;

let CONVEX_HULL_INTERS = `!s:(real^N->bool)->bool.
        ~(affine_dependent(UNIONS s))
        ==> convex hull (INTERS s) = INTERS {convex hull t | t IN s}`;;

let IN_CONVEX_HULL_EXCHANGE = `!s a x:real^N.
        a IN convex hull s /\ x IN convex hull s
        ==> ?b. b IN s /\ x IN convex hull (a INSERT (s DELETE b))`;;

let IN_CONVEX_HULL_EXCHANGE_UNIQUE = `!s t t' a x:real^N.
        ~(affine_dependent s) /\
        a IN convex hull s /\
        t SUBSET s /\ t' SUBSET s /\
        x IN convex hull (a INSERT t) /\
        x IN convex hull (a INSERT t')
        ==> x IN convex hull (a INSERT (t INTER t'))`;;

let CONVEX_HULL_EXCHANGE_UNION = `!s a:real^N.
        a IN convex hull s
        ==> convex hull s =
            UNIONS {convex hull (a INSERT (s DELETE b)) |b| b IN s}`;;

let CONVEX_HULL_EXCHANGE_INTER = `!s a:real^N t t'.
         ~affine_dependent s /\
         a IN convex hull s /\
         t SUBSET s /\
         t' SUBSET s
         ==> (convex hull (a INSERT t)) INTER (convex hull (a INSERT t')) =
             convex hull (a INSERT (t INTER t'))`;;

(* ------------------------------------------------------------------------- *)
(* Representing affine hull as hyperplane or finite intersection of them.    *)
(* ------------------------------------------------------------------------- *)

let AFF_DIM_EQ_INTER_HYPERPLANE = `!s t:real^N->bool.
        affine s /\ affine t /\ t SUBSET s /\ aff_dim t + &1 = aff_dim s
        ==> ?a b. ~(a = vec 0) /\ {x | a dot x = b} INTER s = t`;;

let AFF_DIM_EQ_HYPERPLANE = `!s. aff_dim s = &(dimindex(:N)) - &1 <=>
       ?a b. ~(a = vec 0) /\ affine hull s = {x:real^N | a dot x = b}`;;

let AFF_DIM_HYPERPLANE = `!a b. ~(a = vec 0)
         ==> aff_dim {x:real^N | a dot x = b} = &(dimindex(:N)) - &1`;;

let BOUNDED_HYPERPLANE_EQ_TRIVIAL = `!a b. bounded {x:real^N | a dot x = b} <=>
         if a = vec 0 then ~(b = &0) else dimindex(:N) = 1`;;

let AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES = `!s:real^N->bool.
        ?f. FINITE f /\
            &(CARD f) + aff_dim s = &(dimindex(:N)) /\
            affine hull s = INTERS f /\
            (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x = b})`;;

let AFFINE_HYPERPLANE_SUMS_EQ_UNIV = `!a b s.
        affine s /\
        ~(s INTER {v | a dot v = b} = {}) /\
        ~(s DIFF {v | a dot v = b} = {})
        ==> {x + y | x IN s /\ y IN {v | a dot v = b}} = (:real^N)`;;

let AFF_DIM_AFFINE_INTER_HYPERPLANE = `!a b s:real^N->bool.
        affine s
        ==> aff_dim(s INTER {x | a dot x = b}) =
                if s INTER {v | a dot v = b} = {} then -- &1
                else if s SUBSET {v | a dot v = b} then aff_dim s
                else aff_dim s - &1`;;

let AFF_DIM_LT_FULL = `!s. aff_dim s < &(dimindex(:N)) <=> ~(affine hull s = (:real^N))`;;

let AFF_LOWDIM_SUBSET_HYPERPLANE = `!s:real^N->bool.
        aff_dim s < &(dimindex(:N))
        ==> ?a b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`;;

let COLLINEAR_HYPERPLANE_2 = `!a:real^N b.
     dimindex(:N) <= 2 /\ ~(a = vec 0) ==> collinear {x | a dot x = b}`;;

let COLLINEAR_STANDARD_HYPERPLANE_2 = `!k b. dimindex(:N) <= 2 ==> collinear {x:real^N | x$k = b}`;;

(* ------------------------------------------------------------------------- *)
(* Existence of rotation into general position w.r.t the axes.               *)
(* ------------------------------------------------------------------------- *)

let ROTATION_TO_GENERAL_POSITION_EXISTS_GEN = `!n s:real^N->bool.
      n <= dimindex(:N) /\ COUNTABLE s /\
      s SUBSET span(IMAGE basis (1..n))
      ==> ?f. orthogonal_transformation f /\
              det(matrix f) = &1 /\
              (!x. (!i. 1 <= i /\ i <= n ==> x$i = &0) ==> f x = x) /\
              IMAGE f (span(IMAGE basis (1..n))) = span(IMAGE basis (1..n)) /\
              pairwise (\x y. !i. 1 <= i /\ i <= n ==> ~(f x$i = f y$i)) s`;;

let ROTATION_TO_GENERAL_POSITION_EXISTS = `!s:real^N->bool.
        COUNTABLE s
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\
                pairwise (\x y. !i. 1 <= i /\ i <= dimindex(:N)
                                    ==> ~(f x$i = f y$i)) s`;;

(* ------------------------------------------------------------------------- *)
(* Openness and compactness are preserved by convex hull operation.          *)
(* ------------------------------------------------------------------------- *)

let OPEN_CONVEX_HULL = `!s:real^N->bool. open s ==> open(convex hull s)`;;

let COMPACT_CONVEX_COMBINATIONS = `!s t. compact s /\ compact t
         ==> compact { (&1 - u) % x + u % y :real^N |
                      &0 <= u /\ u <= &1 /\ x IN s /\ y IN t}`;;

let COMPACT_CONVEX_HULL = `!s:real^N->bool. compact s ==> compact(convex hull s)`;;

let FINITE_IMP_COMPACT_CONVEX_HULL = `!s:real^N->bool. FINITE s ==> compact(convex hull s)`;;

let CONVEX_HULL_INTERIOR_SUBSET = `!s:real^N->bool. convex hull (interior s) SUBSET interior (convex hull s)`;;

(* ------------------------------------------------------------------------- *)
(* Extremal points of a simplex are some vertices.                           *)
(* ------------------------------------------------------------------------- *)

let SIMPLEX_FURTHEST_LT = `!a:real^N s x.
        x IN (convex hull s) /\ ~(x IN s)
        ==> ?y. y IN (convex hull s) /\ norm(x - a) < norm(y - a)`;;

let SIMPLEX_FURTHEST_LT_EXISTS = `!a:real^N s x.
        x IN convex hull s /\ ~(x IN s)
        ==> ?y. y IN s /\ norm(x - a) < norm(y - a)`;;

let SIMPLEX_FURTHEST_LE_EXISTS = `!a:real^N s x.
        x IN convex hull s
        ==> ?y. y IN s /\ norm(x - a) <= norm(y - a)`;;

let SIMPLEX_FURTHEST_LE = `!a:real^N s.
        FINITE s /\ ~(s = {})
        ==> ?y. y IN s /\
                !x. x IN (convex hull s) ==> norm(x - a) <= norm(y - a)`;;

let SIMPLEX_EXTREMAL_LE = `!s:real^N->bool.
        FINITE s /\ ~(s = {})
         ==> ?u v. u IN s /\ v IN s /\
                   !x y. x IN convex hull s /\ y IN convex hull s
                         ==> norm(x - y) <= norm(u - v)`;;

let SIMPLEX_EXTREMAL_LE_EXISTS = `!s:real^N->bool x y. FINITE s /\ x IN convex hull s /\ y IN convex hull s
                        ==> ?u v. u IN s /\ v IN s /\
                                  norm(x - y) <= norm(u - v)`;;

(* ------------------------------------------------------------------------- *)
(* Closest point of a convex set is unique, with a continuous projection.    *)
(* ------------------------------------------------------------------------- *)

let CLOSER_POINTS_LEMMA = `!y:real^N z.
        y dot z > &0
        ==> ?u. &0 < u /\
                !v. &0 < v /\ v <= u ==> norm(v % z - y) < norm y`;;

let CLOSER_POINT_LEMMA = `!x y z. (y - x) dot (z - x) > &0
           ==> ?u. &0 < u /\ u <= &1 /\ dist(x + u % (z - x),y) < dist(x,y)`;;

let ANY_CLOSEST_POINT_DOT = `!s a x y:real^N.
        convex s /\ closed s /\ x IN s /\ y IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z))
        ==> (a - x) dot (y - x) <= &0`;;

let ANY_CLOSEST_POINT_UNIQUE = `!s a x y:real^N.
        convex s /\ closed s /\ x IN s /\ y IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z)) /\
        (!z. z IN s ==> dist(a,y) <= dist(a,z))
        ==> x = y`;;

let CLOSEST_POINT_UNIQUE = `!s a x:real^N.
        convex s /\ closed s /\ x IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z))
        ==> x = closest_point s a`;;

let CLOSEST_POINT_DOT = `!s a x:real^N.
        convex s /\ closed s /\ x IN s
        ==> (a - closest_point s a) dot (x - closest_point s a) <= &0`;;

let CLOSEST_POINT_LT = `!s a x. convex s /\ closed s /\ x IN s /\ ~(x = closest_point s a)
           ==> dist(a,closest_point s a) < dist(a,x)`;;

let CLOSEST_POINT_LIPSCHITZ = `!s x y:real^N.
        convex s /\ closed s /\ ~(s = {})
        ==> dist(closest_point s x,closest_point s y) <= dist(x,y)`;;

let CONTINUOUS_AT_CLOSEST_POINT = `!s x. convex s /\ closed s /\ ~(s = {})
         ==> (closest_point s) continuous (at x)`;;

let CONTINUOUS_ON_CLOSEST_POINT = `!s t. convex s /\ closed s /\ ~(s = {})
         ==> (closest_point s) continuous_on t`;;

let CLOSEST_POINT_TRANSLATION = `!s a:real^N.
     convex s /\ closed s /\ ~(s = {})
     ==> closest_point (IMAGE (\x. a + x) s) (a + x) =
         a + closest_point s x`;;

(* ------------------------------------------------------------------------- *)
(* Relating closest points and orthogonality.                                *)
(* ------------------------------------------------------------------------- *)

let ANY_CLOSEST_POINT_AFFINE_ORTHOGONAL = `!s a b:real^N.
        affine s /\ b IN s /\ (!x. x IN s ==> dist(a,b) <= dist(a,x))
        ==> (!x. x IN s ==> orthogonal (x - b) (a - b))`;;

let ORTHOGONAL_ANY_CLOSEST_POINT = `!s a b:real^N.
        b IN s /\ (!x. x IN s ==> orthogonal (x - b) (a - b))
        ==> (!x. x IN s ==> dist(a,b) <= dist(a,x))`;;

let CLOSEST_POINT_AFFINE_ORTHOGONAL = `!s a:real^N x.
        affine s /\ ~(s = {}) /\ x IN s
        ==> orthogonal (x - closest_point s a) (a - closest_point s a)`;;

let CLOSEST_POINT_AFFINE_ORTHOGONAL_EQ = `!s a b:real^N.
        affine s /\ b IN s
        ==> (closest_point s a = b <=>
             !x. x IN s ==> orthogonal (x - b) (a - b))`;;

(* ------------------------------------------------------------------------- *)
(* Using "closest_point" to give orthogonal projection onto a subspace       *)
(* ------------------------------------------------------------------------- *)

let CLOSEST_POINT_SUBSPACE_ORTHOGONAL_EQ = `!s a b:real^N.
         subspace s
         ==> (closest_point s a = b <=>
              b IN s /\ (!x. x IN s ==> orthogonal (a - b) x))`;;

let CLOSEST_POINT_SUBSPACE_ORTHOGONAL = `!s a b:real^N.
        subspace s /\ b IN s ==> orthogonal (a - closest_point s a) b`;;

let LINEAR_CLOSEST_POINT = `!s:real^N->bool. subspace s ==> linear(closest_point s)`;;

let SELF_ADJOINT_CLOSEST_POINT = `!s:real^N->bool.
        subspace s ==> adjoint(closest_point s) = closest_point s`;;

let CLOSEST_POINT_IDEMPOTENT = `!s:real^N->bool.
        closed s ==> closest_point s o closest_point s = closest_point s`;;

let MATRIX_INV_PROJECTION_IMAGE = `(!A:real^M^N. A ** matrix_inv A =
                 matrix(closest_point (IMAGE (\x. A ** x) UNIV)))`
and MATRIX_INV_PROJECTION_IMAGE_ALT = `(!A:real^M^N x. (A ** matrix_inv A) ** x =
                  closest_point (IMAGE (\x. A ** x) UNIV) x)`;;

(* ------------------------------------------------------------------------- *)
(* Stronger separating hyperplane results for affine sets / affine hulls.    *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_AFFINE_AFFINE = `!s t:real^N->bool.
        affine s /\ affine t /\ ~(s = {}) /\ ~(t = {}) /\ DISJOINT s t
        ==> ?a b c. ~(a = vec 0) /\ b < c /\
                    (!x. x IN s ==> a dot x = b) /\
                    (!x. x IN t ==> a dot x = c)`;;

let SEPARATING_HYPERPLANE_AFFINE_HULLS = `!s t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ DISJOINT (affine hull s) (affine hull t)
        ==> ?a b c. ~(a = vec 0) /\ b < c /\
                    (!x. x IN s ==> a dot x = b) /\
                    (!x. x IN t ==> a dot x = c)`;;

(* ------------------------------------------------------------------------- *)
(* Various point-to-set separating/supporting hyperplane theorems.           *)
(* ------------------------------------------------------------------------- *)

let SUPPORTING_HYPERPLANE_COMPACT_POINT_SUP = `!a c s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?b y. y IN s /\ a dot (y - c) = b /\
                  (!x. x IN s ==> a dot (x - c) <= b)`;;

let SUPPORTING_HYPERPLANE_COMPACT_POINT_INF = `!a c s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?b y. y IN s /\ a dot (y - c) = b /\
                  (!x. x IN s ==> a dot (x - c) >= b)`;;

let SUPPORTING_HYPERPLANE_CLOSED_POINT = `!s z:real^N. convex s /\ closed s /\ ~(s = {}) /\ ~(z IN s)
                ==> ?a b y. a dot z < b /\ y IN s /\ (a dot y = b) /\
                            (!x. x IN s ==> a dot x >= b)`;;

let SEPARATING_HYPERPLANE_CLOSED_POINT_INSET = `!s z:real^N. convex s /\ closed s /\ ~(s = {}) /\ ~(z IN s)
                ==> ?a b. a IN s /\
                          (a - z) dot z < b /\
                          (!x. x IN s ==> (a - z) dot x > b)`;;

let SEPARATING_HYPERPLANE_CLOSED_0_INSET = `!s:real^N->bool.
        convex s /\ closed s /\ ~(s = {}) /\ ~(vec 0 IN s)
        ==> ?a b. a IN s /\ ~(a = vec 0) /\ &0 < b /\
                  (!x. x IN s ==> a dot x > b)`;;

let SEPARATING_HYPERPLANE_CLOSED_POINT = `!s z:real^N. convex s /\ closed s /\ ~(z IN s)
                ==> ?a b. a dot z < b /\ (!x. x IN s ==> a dot x > b)`;;

let SEPARATING_HYPERPLANE_CLOSED_0 = `!s:real^N->bool.
        convex s /\ closed s /\ ~(vec 0 IN s)
        ==> ?a b. ~(a = vec 0) /\ &0 < b /\ (!x. x IN s ==> a dot x > b)`;;

(* ------------------------------------------------------------------------- *)
(* Now set-to-set for closed/compact sets.                                   *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_CLOSED_COMPACT = `!s t. convex s /\ closed s /\
         convex t /\ compact t /\ ~(t = {}) /\ DISJOINT s t
         ==> ?a:real^N b. (!x. x IN s ==> a dot x < b) /\
                          (!x. x IN t ==> a dot x > b)`;;

let SEPARATING_HYPERPLANE_COMPACT_CLOSED = `!s t. convex s /\ compact s /\ ~(s = {}) /\
         convex t /\ closed t /\ DISJOINT s t
         ==> ?a:real^N b. (!x. x IN s ==> a dot x < b) /\
                          (!x. x IN t ==> a dot x > b)`;;

let SEPARATING_HYPERPLANE_COMPACT_CLOSED_NONZERO = `!s t:real^N->bool.
           convex s /\ compact s /\ ~(s = {}) /\
           convex t /\ closed t /\ DISJOINT s t
           ==> ?a b. ~(a = vec 0) /\
                     (!x. x IN s ==> a dot x < b) /\
                     (!x. x IN t ==> a dot x > b)`;;

let SEPARATING_HYPERPLANE_COMPACT_COMPACT = `!s t:real^N->bool.
           convex s /\ compact s /\ convex t /\ compact t /\ DISJOINT s t
           ==> ?a b. ~(a = vec 0) /\
                     (!x. x IN s ==> a dot x < b) /\
                     (!x. x IN t ==> a dot x > b)`;;

(* ------------------------------------------------------------------------- *)
(* General case without assuming closure and getting non-strict separation.  *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_SET_0_INSPAN = `!s:real^N->bool.
        convex s /\ ~(s = {}) /\ ~(vec 0 IN s)
        ==> ?a b. a IN span s /\ ~(a = vec 0) /\
                  !x. x IN s ==> &0 <= a dot x`;;

let SEPARATING_HYPERPLANE_SET_POINT_INAFF = `!s z:real^N.
        convex s /\ ~(s = {}) /\ ~(z IN s)
        ==> ?a b. (z + a) IN affine hull (z INSERT s) /\ ~(a = vec 0) /\
                  a dot z <= b /\ (!x. x IN s ==> a dot x >= b)`;;

let SEPARATING_HYPERPLANE_SET_0 = `!s:real^N->bool.
        convex s /\ ~(vec 0 IN s)
        ==> ?a. ~(a = vec 0) /\ !x. x IN s ==> &0 <= a dot x`;;

let SEPARATING_HYPERPLANE_SETS = `!s t. convex s /\ convex t /\ ~(s = {}) /\ ~(t = {}) /\ DISJOINT s t
         ==> ?a:real^N b. ~(a = vec 0) /\
                          (!x. x IN s ==> a dot x <= b) /\
                          (!x. x IN t ==> a dot x >= b)`;;

(* ------------------------------------------------------------------------- *)
(* More convexity generalities.                                              *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_COMPLEMENT_COMPONENT_CONVEX = `!s c:real^N->bool.
        convex s /\ c IN components((:real^N) DIFF s) ==> ~bounded c`;;

let UNBOUNDED_COMPLEMENT_CONVEX = `!c. convex c /\ ~(c = (:real^N)) ==> ~bounded((:real^N) DIFF c)`;;

let COMPONENTS_CONVEX_COMPLEMENT_CONTAINS_HALFSPACE = `!s c. convex s /\ c IN components((:real^N) DIFF s)
         ==> ?a b. ~(a = vec 0) /\ {x | a dot x <= b} SUBSET c`;;

let CARD_COMPONENTS_COMPLEMENT_CONVEX = `(!s. convex s ==> CARD(components((:real^N) DIFF s)) <= 2)`
and FINITE_COMPONENTS_COMPLEMENT_CONVEX = `(!s. convex s ==> FINITE(components((:real^N) DIFF s)))`;;

let CONVEX_CLOSURE = `!s:real^N->bool. convex s ==> convex(closure s)`;;

let CONVEX_INTERIOR = `!s:real^N->bool. convex s ==> convex(interior s)`;;

let CONVEX_HULL_CLOSURE_SUBSET = `!s:real^N->bool. convex hull (closure s) SUBSET closure(convex hull s)`;;

let CONVEX_HULL_CLOSURE = `!s. bounded s ==> convex hull (closure s) = closure(convex hull s)`;;

let SUPPORTING_HYPERPLANE_POINT = `!s z:real^N.
        convex s /\ ~(s = {}) /\ ~(z IN s)
        ==> ?a b y. ~(a = vec 0) /\
                    a dot z <= b /\
                    y IN closure s /\
                    a dot y = b /\
                    !x. x IN closure s ==> a dot x >= b`;;

let CONVEX_ON_SETDIST = `!s t:real^N->bool. convex t ==> (\x. setdist ({x},t)) convex_on s`;;

(* ------------------------------------------------------------------------- *)
(* Moving and scaling convex hulls.                                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_TRANSLATION = `!a:real^N s.
       convex hull (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (convex hull s)`;;

add_translation_invariants [CONVEX_HULL_TRANSLATION];;

let CONVEX_HULL_SCALING = `!s:real^N->bool c.
       convex hull (IMAGE (\x. c % x) s) = IMAGE (\x. c % x) (convex hull s)`;;

let CONVEX_HULL_AFFINITY = `!s a:real^N c.
        convex hull (IMAGE (\x. c % x + a) s) =
        IMAGE (\x. c % x + a) (convex hull s)`;;

(* ------------------------------------------------------------------------- *)
(* Convex set as intersection of halfspaces.                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HALFSPACE_INTERSECTION = `!s. closed(s:real^N->bool) /\ convex s
       ==> s = INTERS {h | s SUBSET h /\ ?a b. h = {x | a dot x <= b}}`;;

(* ------------------------------------------------------------------------- *)
(* Polar dual of a set.                                                      *)
(* ------------------------------------------------------------------------- *)

let polar_dual = new_definition
 `polar_dual s = {x:real^N | !u. u IN s ==> u dot x >= -- &1}`;;

let POLAR_DUAL = `!s:real^N->bool.
        polar_dual s = INTERS {{x | u dot x >= -- &1} | u IN s}`;;

let CLOSED_POLAR_DUAL = `!s:real^N->bool. closed(polar_dual s)`;;

let CONVEX_POLAR_DUAL = `!s:real^N->bool. convex(polar_dual s)`;;

let POLAR_DUAL_0 = `!s:real^N->bool. vec 0 IN polar_dual s`;;

let POLAR_DUAL_EMPTY = `polar_dual {} = (:real^N)`;;

let POLAR_DUAL_SING = `polar_dual {vec 0} = (:real^N)`;;

let POLAR_DUAL_UNIV = `polar_dual (:real^N) = {vec 0}`;;

let POLAR_DUAL_ANTIMONO = `!s t:real^N->bool.
        s SUBSET t ==> polar_dual t SUBSET polar_dual s`;;

let POLAR_DUAL_UNION = `!s t:real^N->bool. polar_dual(s UNION t) = polar_dual s INTER polar_dual t`;;

let POLAR_DUAL_SCALING = `!a s:real^N->bool.
        ~(a = &0)
        ==> polar_dual {a % x | x IN s} = {inv a % x | x IN polar_dual s}`;;

let POLAR_DUAL_UNIT_CBALL = `polar_dual(cball(vec 0:real^N,&1)) = cball(vec 0,&1)`;;

let POLAR_DUAL_CBALL = `!r. &0 < r ==> polar_dual(cball(vec 0:real^N,r)) = cball(vec 0,inv r)`;;

let POLAR_DUAL_POLAR_DUAL_GEN = `!s:real^N->bool.
        polar_dual(polar_dual s) = closure(convex hull (vec 0 INSERT s))`;;

let POLAR_DUAL_POLAR_DUAL_EQ = `!s:real^N->bool.
        polar_dual(polar_dual s) = s <=>
        closed s /\ convex s /\ vec 0 IN s`;;

let POLAR_DUAL_POLAR_DUAL = `!s:real^N->bool.
        closed s /\ convex s /\ vec 0 IN s
        ==> polar_dual(polar_dual s) = s`;;

(* ------------------------------------------------------------------------- *)
(* Radon's theorem (from Lars Schewe).                                       *)
(* ------------------------------------------------------------------------- *)

let RADON_EX_LEMMA = `!(c:real^N->bool).
        FINITE c /\ affine_dependent c
        ==> (?u. sum c u = &0 /\ (?v. v IN c /\ ~(u v = &0)) /\
                                      vsum c (\v. u v % v) = (vec 0):real^N)`;;

let RADON_S_LEMMA = `!(s:A->bool) f.
        FINITE s /\ sum s f = &0
        ==> sum {x | x IN s /\ &0 < f x} f =
            -- sum {x | x IN s /\ f x < &0} f`;;

let RADON_V_LEMMA = `!(s:A->bool) f g.
        FINITE s /\ vsum s f = vec 0 /\ (!x. g x = &0 ==> f x = vec 0)
        ==> (vsum {x | x IN s /\ &0 < g x} f) :real^N =
             -- vsum {x | x IN s /\ g x < &0} f`;;

let RADON_PARTITION = `!(c:real^N->bool).
        FINITE c /\ affine_dependent c
        ==> ?(m:real^N->bool) (p:real^N->bool).
                (DISJOINT m p) /\
                (m UNION p = c) /\
                ~(DISJOINT (convex hull m) (convex hull p))`;;

let RADON = `!(c:real^N->bool).
        affine_dependent c
        ==> ?(m:real^N->bool) (p:real^N->bool).
                m SUBSET c /\
                p SUBSET c /\
                DISJOINT m p /\
                ~(DISJOINT (convex hull m) (convex hull p))`;;

(* ------------------------------------------------------------------------- *)
(* Helly's theorem.                                                          *)
(* ------------------------------------------------------------------------- *)

let HELLY_INDUCT = `!n f. f HAS_SIZE n /\ n >= dimindex(:N) + 1 /\
         (!s:real^N->bool. s IN f ==> convex s) /\
         (!t. t SUBSET f /\ CARD(t) = dimindex(:N) + 1
              ==> ~(INTERS t = {}))
         ==> ~(INTERS f = {})`;;

let HELLY = `!f:(real^N->bool)->bool.
        FINITE f /\ CARD(f) >= dimindex(:N) + 1 /\
        (!s. s IN f ==> convex s) /\
        (!t. t SUBSET f /\ CARD(t) = dimindex(:N) + 1 ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`;;

let HELLY_ALT = `!f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> convex s) /\
        (!t. t SUBSET f /\ CARD(t) <= dimindex(:N) + 1 ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`;;

let HELLY_CLOSED_ALT = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ closed s) /\ (?s. s IN f /\ bounded s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) <= dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`;;

let HELLY_COMPACT_ALT = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ compact s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) <= dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`;;

let HELLY_CLOSED = `!f:(real^N->bool)->bool.
        (FINITE f ==> CARD f >= dimindex (:N) + 1) /\
        (!s. s IN f ==> convex s /\ closed s) /\ (?s. s IN f /\ bounded s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) = dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`;;

let HELLY_COMPACT = `!f:(real^N->bool)->bool.
        (FINITE f ==> CARD f >= dimindex (:N) + 1) /\
        (!s. s IN f ==> convex s /\ compact s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) = dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`;;

(* ------------------------------------------------------------------------- *)
(* Kirchberger's theorem                                                     *)
(* ------------------------------------------------------------------------- *)

let KIRCHBERGER = `!s t:real^N->bool.
        compact s /\ compact t /\
        (!s' t'. s' SUBSET s /\ t' SUBSET t /\ FINITE s' /\ FINITE t' /\
                 CARD(s') + CARD(t') <= dimindex(:N) + 2
                 ==> ?a b. (!x. x IN s' ==> a dot x < b) /\
                           (!x. x IN t' ==> a dot x > b))
        ==> ?a b. ~(a = vec 0) /\
                  (!x. x IN s ==> a dot x < b) /\
                  (!x. x IN t ==> a dot x > b)`;;

(* ------------------------------------------------------------------------- *)
(* Convex hull is "preserved" by a linear function.                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_LINEAR_IMAGE = `!f s. linear f ==> convex hull (IMAGE f s) = IMAGE f (convex hull s)`;;

add_linear_invariants [CONVEX_HULL_LINEAR_IMAGE];;

let IN_CONVEX_HULL_LINEAR_IMAGE = `!f:real^M->real^N s x.
        linear f /\ x IN convex hull s ==> (f x) IN convex hull (IMAGE f s)`;;

let CONIC_CONVEX_HULL = `!s:real^N->bool. conic s ==> conic(convex hull s)`;;

let CONIC_HULL_CONVEX_HULL = `!s:real^N->bool. conic hull (convex hull s) = convex hull (conic hull s)`;;

(* ------------------------------------------------------------------------- *)
(* Convexity of general and special intervals.                               *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_CONVEX = `!s:real^N->bool. is_interval s ==> convex s`;;

let IS_INTERVAL_CONNECTED = `!s:real^N->bool. is_interval s ==> connected s`;;

let IS_INTERVAL_CONNECTED_1 = `!s:real^1->bool. is_interval s <=> connected s`;;

let CONVEX_INTERVAL = `!a b:real^N. convex(interval [a,b]) /\ convex(interval (a,b))`;;

let CONNECTED_INTERVAL = `(!a b:real^N. connected(interval[a,b])) /\
   (!a b:real^N. connected(interval(a,b)))`;;

let LIMIT_POINT_OF_INTERVAL = `(!a b x:real^N.
        x limit_point_of interval[a,b] <=>
        ~(a = b) /\ x IN interval[a,b]) /\
   (!a b x:real^N.
        x limit_point_of interval(a,b) <=>
        ~(interval(a,b) = {}) /\ x IN interval[a,b])`;;

let CONVEX_CONNECTED_COLLINEAR = `!s:real^N->bool. collinear s ==> (convex s <=> connected s)`;;

let CONVEX_EQ_CONVEX_LINE_INTERSECTION = `!s:real^N->bool. convex s <=> !a b. convex(s INTER affine hull {a,b})`;;

let CONVEX_EQ_CONNECTED_LINE_INTERSECTION = `!s:real^N->bool. convex s <=> !a b. connected(s INTER affine hull {a,b})`;;

(* ------------------------------------------------------------------------- *)
(* On real^1, is_interval, convex and connected are all equivalent.          *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_CONVEX_1 = `!s:real^1->bool. is_interval s <=> convex s`;;

let CONVEX_CONNECTED_1 = `!s:real^1->bool. convex s <=> connected s`;;

let CONNECTED_CONVEX_1 = `!s:real^1->bool. connected s <=> convex s`;;

let CONNECTED_COMPACT_INTERVAL_1 = `!s:real^1->bool. connected s /\ compact s <=> ?a b. s = interval[a,b]`;;

let CONVEX_CONNECTED_1_GEN = `!s:real^N->bool.
        dimindex(:N) = 1 ==> (convex s <=> connected s)`;;

let CONNECTED_CONVEX_1_GEN = `!s:real^N->bool.
        dimindex(:N) = 1 ==> (connected s <=> convex s)`;;

let COMPACT_CONVEX_COLLINEAR_SEGMENT_ALT = `!s:real^N->bool.
        ~(s = {}) /\ compact s /\ connected s /\ collinear s
        ==> ?a b. s = segment[a,b]`;;

let COMPACT_CONVEX_COLLINEAR_SEGMENT = `!s:real^N->bool.
        ~(s = {}) /\ compact s /\ convex s /\ collinear s
        ==> ?a b. s = segment[a,b]`;;

let IN_CONVEX_HULL_SEGMENT_1 = `(!s:real^1->bool x.
        x IN convex hull s <=>
        ?a b. a IN s /\ b IN s /\ x IN segment[a,b])`
and IN_CONVEX_HULL_INTERVAL_1 = `(!s:real^1->bool x.
        x IN convex hull s <=>
        ?a b. a IN s /\ b IN s /\ x IN interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Jung's theorem.                                                           *)
(* Proof taken from http://cstheory.wordpress.com/2010/08/07/jungs-theorem/  *)
(* ------------------------------------------------------------------------- *)

let JUNG = `!s:real^N->bool r.
        bounded s /\
        sqrt(&(dimindex(:N)) / &(2 * dimindex(:N) + 2)) * diameter s <= r
        ==> ?a. s SUBSET cball(a,r)`;;

(* ------------------------------------------------------------------------- *)
(* Kirszbraun's theorem (proof from Federer's "Geometric Measure Theory")    *)
(* ------------------------------------------------------------------------- *)

let KIRSZBRAUN = `!f:real^M->real^N s B.
        &0 <= B /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> ?g. (!x y. norm(g x - g y) <= B * norm(x - y)) /\
                (!x. x IN s ==> g x = f x)`;;

let LIPSCHITZ_EXTENSION_EXISTS = `!f:real^M->real^N s.
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> ?g. (?B. !x y. norm(g x - g y) <= B * norm(x - y)) /\
                (!x. x IN s ==> g x = f x)`;;

(* ------------------------------------------------------------------------- *)
(* The Dugundji extension theorem, and Tietze variants as corollaries.       *)
(* ------------------------------------------------------------------------- *)

let DUGUNDJI = `!f:real^M->real^N c u s.
        convex c /\ ~(c = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\ IMAGE f s SUBSET c
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                !x. x IN s ==> g x = f x`;;

let TIETZE = `!f:real^M->real^N u s B.
        &0 <= B /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> norm(f x) <= B)
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> norm(g x) <= B)`;;

let TIETZE_CLOSED_INTERVAL = `!f:real^M->real^N u s a b.
        ~(interval[a,b] = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval[a,b])`;;

let TIETZE_CLOSED_INTERVAL_1 = `!f:real^N->real^1 u s a b.
        drop a <= drop b /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval[a,b])`;;

let TIETZE_OPEN_INTERVAL = `!f:real^M->real^N u s a b.
        ~(interval(a,b) = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval(a,b))`;;

let TIETZE_OPEN_INTERVAL_1 = `!f:real^N->real^1 u s a b.
        drop a < drop b /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval(a,b))`;;

let TIETZE_UNBOUNDED = `!f:real^M->real^N u s.
        closed_in (subtopology euclidean u) s /\ f continuous_on s
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x)`;;

(* ------------------------------------------------------------------------- *)
(* Convex cones and corresponding hulls.                                     *)
(* ------------------------------------------------------------------------- *)

let convex_cone = new_definition
 `convex_cone s <=> ~(s = {}) /\ convex s /\ conic s`;;

let CONVEX_CONE = `!s:real^N->bool.
     convex_cone s <=>
        vec 0 IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!x c. x IN s /\ &0 <= c ==> (c % x) IN s)`;;

let CONVEX_CONE_ADD = `!s x y. convex_cone s /\ x IN s /\ y IN s ==> (x + y) IN s`;;

let CONVEX_CONE_MUL = `!s c x. convex_cone s /\ &0 <= c /\ x IN s ==> (c % x) IN s`;;

let CONVEX_CONE_NONEMPTY = `!s. convex_cone s ==> ~(s = {})`;;

let CONVEX_CONE_LINEAR_IMAGE = `!f:real^M->real^N s.
        convex_cone s /\ linear f ==> convex_cone(IMAGE f s)`;;

let CONVEX_CONE_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (convex_cone(IMAGE f s) <=> convex_cone s)`;;

add_linear_invariants [CONVEX_CONE_LINEAR_IMAGE_EQ];;

let CONVEX_CONE_HALFSPACE_GE = `!a. convex_cone {x | a dot x >= &0}`;;

let CONVEX_CONE_HALFSPACE_LE = `!a. convex_cone {x | a dot x <= &0}`;;

let CONVEX_CONE_CONTAINS_0 = `!s:real^N->bool. convex_cone s ==> vec 0 IN s`;;

let CONVEX_CONE_INTERS = `!f. (!s:real^N->bool. s IN f ==> convex_cone s) ==> convex_cone(INTERS f)`;;

let CONVEX_CONE_CONVEX_CONE_HULL = `!s. convex_cone(convex_cone hull s)`;;

let CONVEX_CONVEX_CONE_HULL = `!s. convex(convex_cone hull s)`;;

let CONIC_CONVEX_CONE_HULL = `!s. conic(convex_cone hull s)`;;

let CONVEX_CONE_HULL_NONEMPTY = `!s. ~(convex_cone hull s = {})`;;

let CONVEX_CONE_HULL_CONTAINS_0 = `!s. vec 0 IN convex_cone hull s`;;

let CONVEX_CONE_HULL_ADD = `!s x y:real^N.
        x IN convex_cone hull s /\ y IN convex_cone hull s
        ==> x + y IN convex_cone hull s`;;

let CONVEX_CONE_HULL_MUL = `!s c x:real^N.
        &0 <= c /\ x IN convex_cone hull s
        ==> (c % x) IN convex_cone hull s`;;

let CONVEX_CONE_SUMS = `!s t. convex_cone s /\ convex_cone t
         ==> convex_cone {x + y:real^N | x IN s /\ y IN t}`;;

let CONVEX_CONE_PCROSS = `!s:real^M->bool t:real^N->bool.
        convex_cone s /\ convex_cone t ==> convex_cone(s PCROSS t)`;;

let CONVEX_CONE_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        convex_cone(s PCROSS t) <=> convex_cone s /\ convex_cone t`;;

let CONVEX_CONE_HULL_UNION = `!s t. convex_cone hull(s UNION t) =
         {x + y:real^N | x IN convex_cone hull s /\ y IN convex_cone hull t}`;;

let CONVEX_CONE_SING = `convex_cone {vec 0}`;;

let CONVEX_HULL_SUBSET_CONVEX_CONE_HULL = `!s. convex hull s SUBSET convex_cone hull s`;;

let CONIC_HULL_SUBSET_CONVEX_CONE_HULL = `!s. conic hull s SUBSET convex_cone hull s`;;

let CONVEX_CONE_HULL_SEPARATE_NONEMPTY = `!s:real^N->bool.
    ~(s = {})
    ==> convex_cone hull s = conic hull (convex hull s)`;;

let CONVEX_CONE_HULL_EMPTY = `convex_cone hull {} = {vec 0}`;;

let CONVEX_CONE_HULL_SEPARATE = `!s:real^N->bool.
    convex_cone hull s = vec 0 INSERT conic hull (convex hull s)`;;

let CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY = `!s:real^N->bool.
        ~(s = {})
        ==> convex_cone hull s = {c % x | &0 <= c /\ x IN convex hull s}`;;

let CONVEX_CONE_HULL_CONVEX_HULL = `!s:real^N->bool.
        convex_cone hull s =
        vec 0 INSERT {c % x | &0 <= c /\ x IN convex hull s}`;;

let CONVEX_CONE_HULL_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f
        ==> convex_cone hull (IMAGE f s) = IMAGE f (convex_cone hull s)`;;

add_linear_invariants [CONVEX_CONE_HULL_LINEAR_IMAGE];;

let SUBSPACE_IMP_CONVEX_CONE = `!s. subspace s ==> convex_cone s`;;

let CONVEX_CONE_SPAN = `!s. convex_cone(span s)`;;

let CONVEX_CONE_NEGATIONS = `!s. convex_cone s ==> convex_cone (IMAGE (--) s)`;;

let SUBSPACE_CONVEX_CONE_SYMMETRIC = `!s:real^N->bool.
        subspace s <=> convex_cone s /\ (!x. x IN s ==> --x IN s)`;;

let SPAN_CONVEX_CONE_ALLSIGNS = `!s:real^N->bool. span s = convex_cone hull (s UNION IMAGE (--) s)`;;

(* ------------------------------------------------------------------------- *)
(* Epigraphs of convex functions.                                            *)
(* ------------------------------------------------------------------------- *)

let epigraph = new_definition
  `epigraph s (f:real^N->real) =
       {xy:real^((N,1)finite_sum) |
             fstcart xy IN s /\ f(fstcart xy) <= drop(sndcart xy)}`;;

let IN_EPIGRAPH = `!x y. (pastecart x (lift y)) IN epigraph s f <=> x IN s /\ f(x) <= y`;;

let CONVEX_EPIGRAPH = `!f s. f convex_on s /\ convex s <=> convex(epigraph s f)`;;

let CONVEX_EPIGRAPH_CONVEX = `!f s. convex s ==> (f convex_on s <=> convex(epigraph s f))`;;

let CONVEX_ON_EPIGRAPH_SLICE_LE = `!f:real^N->real s a.
        f convex_on s /\ convex s ==> convex {x | x IN s /\ f(x) <= a}`;;

let CONVEX_ON_EPIGRAPH_SLICE_LT = `!f:real^N->real s a.
        f convex_on s /\ convex s ==> convex {x | x IN s /\ f(x) < a}`;;

let CONVEX_ON_SUP = `!t:A->bool s:real^N->bool.
        convex s /\
        (!i. i IN t ==> f i convex_on s) /\
        (!x. x IN s ==> ?B. !i. i IN t ==> f i x <= B)
        ==> (\x. sup {f i x | i IN t}) convex_on s`;;

(* ------------------------------------------------------------------------- *)
(* Use this to derive general bound property of convex function.             *)
(* ------------------------------------------------------------------------- *)

let FORALL_OF_PASTECART = `(!p. P (fstcart o p) (sndcart o p)) <=> (!x:A->B^M y:A->B^N. P x y)`;;

let FORALL_OF_DROP = `(!v. P (drop o v)) <=> (!x:A->real. P x)`;;

let CONVEX_ON_JENSEN = `!f:real^N->real s.
        convex s
        ==> (f convex_on s <=>
                !k u x.
                   (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                   (sum (1..k) u = &1)
                   ==> f(vsum (1..k) (\i. u(i) % x(i)))
                           <= sum (1..k) (\i. u(i) * f(x(i))))`;;

let CONVEX_ON_IMP_JENSEN = `!f:real^N->real s k:A->bool u x.
        f convex_on s /\ convex s /\ FINITE k /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s) /\ sum k u = &1
        ==> f(vsum k (\i. u i % x i)) <= sum k (\i. u i * f(x i))`;;

(* ------------------------------------------------------------------------- *)
(* Another intermediate value theorem formulation.                           *)
(* ------------------------------------------------------------------------- *)

let IVT_INCREASING_COMPONENT_ON_1 = `!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        f continuous_on interval[a,b] /\
        f(a)$k <= y /\ y <= f(b)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`;;

let IVT_INCREASING_COMPONENT_1 = `!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f continuous at x) /\
        f(a)$k <= y /\ y <= f(b)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`;;

let IVT_DECREASING_COMPONENT_ON_1 = `!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        f continuous_on interval[a,b] /\
        f(b)$k <= y /\ y <= f(a)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`;;

let IVT_DECREASING_COMPONENT_1 = `!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f continuous at x) /\
        f(b)$k <= y /\ y <= f(a)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`;;

(* ------------------------------------------------------------------------- *)
(* A bound within a convex hull, and so an interval.                         *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_CONVEX_HULL_BOUND = `!f s b. f convex_on (convex hull s) /\
           (!x:real^N. x IN s ==> f(x) <= b)
           ==> !x. x IN convex hull s ==> f(x) <= b`;;

let CONVEX_ON_CONVEX_HULL_BOUND_EQ = `!f s:real^N->bool b.
       f convex_on convex hull s
       ==> ((!x. x IN convex hull s ==> f x <= b) <=>
            (!x. x IN s ==> f x <= b))`;;

let DIST_CONVEX_HULL_BOUND_EQ = `!s a:real^N d.
        (!x. x IN convex hull s ==> dist(a,x) <= d) <=>
        (!x. x IN s ==> dist(a,x) <= d)`;;

let DIST_CONVEX_HULL_BOUND_2 = `!s:real^N->bool d.
        (!x y. x IN convex hull s /\ y IN convex hull s ==> dist(x,y) <= d) <=>
        (!x y. x IN s /\ y IN s ==> dist(x,y) <= d)`;;

let DIAMETER_CONVEX_HULL = `!s:real^N->bool. diameter(convex hull s) = diameter s`;;

let DIAMETER_SIMPLEX = `!s:real^N->bool.
        ~(s = {})
        ==> diameter(convex hull s) = sup { dist(x,y) | x IN s /\ y IN s}`;;

let UNIT_INTERVAL_CONVEX_HULL = `interval [vec 0,vec 1:real^N] =
     convex hull
       {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                           ==> ((x$i = &0) \/ (x$i = &1))}`;;

(* ------------------------------------------------------------------------- *)
(* Representation of any interval as a finite convex hull.                   *)
(* ------------------------------------------------------------------------- *)

let CLOSED_INTERVAL_AS_CONVEX_HULL = `!a b:real^N. ?s. FINITE s /\ interval[a,b] = convex hull s`;;

(* ------------------------------------------------------------------------- *)
(* Characterizations of convex functions in terms of secants.                *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_LEFT_SECANT_MUL = `(!f s:real^N->bool.
        f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment[a,b]
                ==> (f x - f a) * norm(b - a) <= (f b - f a) * norm(x - a))`
and CONVEX_ON_RIGHT_SECANT_MUL = `(!f s:real^N->bool.
        f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment[a,b]
                ==> (f b - f a) * norm(b - x) <= (f b - f x) * norm(b - a))`
and CONVEX_ON_MID_SECANT_MUL = `(!f s:real^N->bool.
        f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment[a,b]
                ==> (f x - f a) * norm (b - x) <= (f b - f x) * norm(x - a))`;;

let CONVEX_ON_LEFT_SECANT = `(!f s:real^N->bool.
      f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment(a,b)
                ==> (f x - f a) / norm(x - a) <= (f b - f a) / norm(b - a))`
and CONVEX_ON_RIGHT_SECANT = `(!f s:real^N->bool.
      f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment(a,b)
                ==> (f b - f a) / norm(b - a) <= (f b - f x) / norm(b - x))`
and CONVEX_ON_MID_SECANT = `(!f s:real^N->bool.
      f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment(a,b)
                ==> (f x - f a) / norm (x - a) <= (f b - f x) / norm(b - x))`;;

let CONVEX_ON_SECANTS_1_IMP = `!f s a b c d.
        f convex_on s /\
        a IN s /\ b IN s /\ c IN s /\ d IN s /\
        drop a < drop b /\ drop b <= drop c /\ drop c < drop d
        ==> (f b - f a) / (drop b - drop a)
            <= (f d - f c) / (drop d - drop c)`;;

let CONVEX_ON_SECANTS_1 = `!f s. is_interval s
         ==> (f convex_on s <=>
              !a b c d. a IN s /\ b IN s /\ c IN s /\ d IN s /\
                         drop a < drop b /\ drop b <= drop c /\ drop c < drop d
                         ==> (f b - f a) / (drop b - drop a)
                             <= (f d - f c) / (drop d - drop c))`;;

(* ------------------------------------------------------------------------- *)
(* Starlike sets and more stuff about line segments.                         *)
(* ------------------------------------------------------------------------- *)

let starlike = new_definition
 `starlike s <=> ?a. a IN s /\ !x. x IN s ==> segment[a,x] SUBSET s`;;

let CONVEX_IMP_STARLIKE = `!s. convex s /\ ~(s = {}) ==> starlike s`;;

let CONIC_IMP_STARLIKE = `!s:real^N->bool. conic s /\ ~(s = {}) ==> starlike s`;;

let SEGMENT_CONVEX_HULL = `!a b. segment[a,b] = convex hull {a,b}`;;

let CONTINUOUS_INCREASING_IMAGE_INTERVAL_1 = `!f:real^1->real^1 a b.
        ~(interval[a,b] = {}) /\ f continuous_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> IMAGE f (interval[a,b]) = interval[f a,f b]`;;

let CONTINUOUS_DECREASING_IMAGE_INTERVAL_1 = `!f:real^1->real^1 a b.
        ~(interval[a,b] = {}) /\ f continuous_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
        ==> IMAGE f (interval[a,b]) = interval[f b,f a]`;;

let SEGMENT_FURTHEST_LE = `!a b x y:real^N.
        x IN segment[a,b] ==> norm(y - x) <= norm(y - a) \/
                              norm(y - x) <= norm(y - b)`;;

let SEGMENT_BOUND = `!a b x:real^N.
        x IN segment[a,b] ==> norm(x - a) <= norm(b - a) /\
                              norm(x - b) <= norm(b - a)`;;

let BETWEEN_IN_CONVEX_HULL = `!x a b:real^N. between x (a,b) <=> x IN convex hull {a,b}`;;

let STARLIKE_LINEAR_IMAGE = `!f s. starlike s /\ linear f ==> starlike(IMAGE f s)`;;

let STARLIKE_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (starlike (IMAGE f s) <=> starlike s)`;;

add_linear_invariants [STARLIKE_LINEAR_IMAGE_EQ];;

let STARLIKE_TRANSLATION_EQ = `!a s. starlike (IMAGE (\x. a + x) s) <=> starlike s`;;

add_translation_invariants [STARLIKE_TRANSLATION_EQ];;

let BETWEEN_LINEAR_IMAGE_EQ = `!f x y z. linear f /\ (!x y. f x = f y ==> x = y)
             ==> (between (f x) (f y,f z) <=> between x (y,z))`;;

add_linear_invariants [BETWEEN_LINEAR_IMAGE_EQ];;

let STARLIKE_CLOSURE = `!s:real^N->bool. starlike s ==> starlike(closure s)`;;

let STARLIKE_UNIV = `starlike(:real^N)`;;

let STARLIKE_PCROSS = `!s:real^M->bool t:real^N->bool.
        starlike s /\ starlike t ==> starlike(s PCROSS t)`;;

let STARLIKE_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        starlike(s PCROSS t) <=> starlike s /\ starlike t`;;

let BETWEEN_DIST_LT = `!r a b c:real^N.
        dist(c,a) < r /\ dist(c,b) < r /\ between x (a,b) ==> dist(c,x) < r`;;

let BETWEEN_DIST_LE = `!r a b c:real^N.
      dist(c,a) <= r /\ dist(c,b) <= r /\ between x (a,b) ==> dist(c,x) <= r`;;

let BETWEEN_NORM_LT = `!r a b x:real^N.
        norm a < r /\ norm b < r /\ between x (a,b) ==> norm x < r`;;

let BETWEEN_NORM_LE = `!r a b x:real^N.
        norm a <= r /\ norm b <= r /\ between x (a,b) ==> norm x <= r`;;

let UNION_SEGMENT = `!a b c:real^N.
        b IN segment[a,c]
        ==> segment[a,b] UNION segment[b,c] = segment[a,c]`;;

let CONVEX_STARCENTRES = `!s:real^N->bool.
        convex {a | a IN s /\ !x. x IN s ==> segment[a,x] SUBSET s}`;;

(* ------------------------------------------------------------------------- *)
(* It might occasionally be handy to use midpoint convexity only.            *)
(* ------------------------------------------------------------------------- *)

let MIDPOINT_CONVEX_SET = `!s:real^N->bool.
        open s \/ closed s
        ==> (convex s <=> !a b. a IN s /\ b IN s ==> midpoint(a,b) IN s)`;;

(* ------------------------------------------------------------------------- *)
(* Eliminate scalings when 0 is not in the affine hull.                      *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_DESCALE = `!a b c x y z:real^N.
        ~(a = &0) /\ ~(c = &0) /\
        collinear {a % x,b % y,c % z} /\
        ~(vec 0 IN affine hull {x,y,z})
        ==> collinear {x,y,z}`;;

let CLOSED_SEGMENT_DESCALE = `!a b c x y z:real^N.
        &0 < a /\ &0 <= b /\ &0 < c /\
        (b % y) IN segment[a % x,c % z] /\
        ~(vec 0 IN affine hull {x,y,z})
        ==> y IN segment[x,z]`;;

let OPEN_SEGMENT_DESCALE = `!a b c x y z:real^N.
        &0 < a /\ &0 <= b /\ &0 < c /\
        (b % y) IN segment(a % x,c % z) /\
        ~(vec 0 IN affine hull {x,y,z}) /\
        ~(x = y /\ z = y)
        ==> y IN segment(x,z)`;;

(* ------------------------------------------------------------------------- *)
(* Shrinking towards the interior of a convex set.                           *)
(* ------------------------------------------------------------------------- *)

let IN_INTERIOR_CONVEX_SHRINK = `!s e x c:real^N.
     convex s /\ c IN interior s /\
     x IN s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN interior s`;;

let IN_INTERIOR_CLOSURE_CONVEX_SHRINK = `!s e x c:real^N.
     convex s /\ c IN interior s /\
     x IN closure s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN interior s`;;

let IN_INTERIOR_CLOSURE_CONVEX_SEGMENT = `!s a b:real^N.
        convex s /\ a IN interior s /\ b IN closure s
        ==> segment(a,b) SUBSET interior s`;;

(* ------------------------------------------------------------------------- *)
(* Relative interior of a set.                                               *)
(* ------------------------------------------------------------------------- *)

let relative_interior = new_definition
 `relative_interior s =
   {x | ?t. open_in (subtopology euclidean (affine hull s)) t /\
            x IN t /\ t SUBSET s}`;;

let relative_frontier = new_definition
 `relative_frontier s = closure s DIFF relative_interior s`;;

let RELATIVE_INTERIOR_INTERIOR_OF = `!s:real^N->bool.
        relative_interior s =
        subtopology euclidean (affine hull s) interior_of s`;;

let RELATIVE_FRONTIER_FRONTIER_OF = `!s:real^N->bool.
        relative_frontier s =
        subtopology euclidean (affine hull s) frontier_of s`;;

let RELATIVE_INTERIOR = `!s. relative_interior s =
          {x | x IN s /\
               ?t. open t /\ x IN t /\ t INTER (affine hull s) SUBSET s}`;;

let RELATIVE_INTERIOR_EQ = `!s. relative_interior s = s <=>
       open_in(subtopology euclidean (affine hull s)) s`;;

let RELATIVE_INTERIOR_OPEN_IN = `!s. open_in(subtopology euclidean (affine hull s)) s
       ==> relative_interior s = s`;;

let RELATIVE_INTERIOR_EMPTY = `relative_interior {} = {}`;;

let RELATIVE_FRONTIER_EMPTY = `relative_frontier {} = {}`;;

let RELATIVE_INTERIOR_AFFINE = `!s:real^N->bool. affine s ==> relative_interior s = s`;;

let RELATIVE_INTERIOR_UNIV = `!s. relative_interior(affine hull s) = affine hull s`;;

let OPEN_IN_RELATIVE_INTERIOR = `!s. open_in (subtopology euclidean (affine hull s))
               (relative_interior s)`;;

let RELATIVE_INTERIOR_SUBSET = `!s. (relative_interior s) SUBSET s`;;

let RELATIVE_FRONTIER_SUBSET = `!s:real^N->bool. closed s ==> relative_frontier s SUBSET s`;;

let RELATIVE_FRONTIER_SUBSET_EQ = `!s:real^N->bool. relative_frontier s SUBSET s <=> closed s`;;

let BOUNDED_RELATIVE_INTERIOR = `!s:real^N->bool. bounded s ==> bounded(relative_interior s)`;;

let OPEN_IN_SET_RELATIVE_INTERIOR = `!s:real^N->bool. open_in (subtopology euclidean s) (relative_interior s)`;;

let SUBSET_RELATIVE_INTERIOR = `!s t. s SUBSET t /\ affine hull s = affine hull t
         ==> (relative_interior s) SUBSET (relative_interior t)`;;

let RELATIVE_INTERIOR_CLOSURE_SUBSET = `!s. relative_interior s SUBSET relative_interior(closure s)`;;

let RELATIVE_INTERIOR_MAXIMAL = `!s t. t SUBSET s /\
         open_in(subtopology euclidean (affine hull s)) t
         ==> t SUBSET (relative_interior s)`;;

let RELATIVE_INTERIOR_UNIQUE = `!s t. t SUBSET s /\
         open_in(subtopology euclidean (affine hull s)) t /\
         (!t'. t' SUBSET s /\
               open_in(subtopology euclidean (affine hull s)) t'
               ==> t' SUBSET t)
         ==> (relative_interior s = t)`;;

let IN_RELATIVE_INTERIOR = `!x:real^N s.
        x IN relative_interior s <=>
        x IN s /\ ?e. &0 < e /\ (ball(x,e) INTER (affine hull s)) SUBSET s`;;

let IN_RELATIVE_INTERIOR_CBALL = `!x:real^N s.
        x IN relative_interior s <=>
        x IN s /\ ?e. &0 < e /\ (cball(x,e) INTER affine hull s) SUBSET s`;;

let RELATIVE_INTERIOR_CONVEX_INTER_OPEN = `!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> relative_interior(s INTER t) = relative_interior s INTER t`;;

let CONIC_HULL_EQ_SPAN = `(!s:real^N->bool.
        vec 0 IN relative_interior s ==> conic hull s = span s)`
and CONIC_HULL_EQ_AFFINE_HULL = `(!s:real^N->bool.
        vec 0 IN relative_interior s ==> conic hull s = affine hull s)`;;

let CONIC_HULL_EQ_SPAN_EQ = `!s:real^N->bool.
        vec 0 IN relative_interior(conic hull s) <=> conic hull s = span s`;;

let OPEN_IN_SUBSET_RELATIVE_INTERIOR = `!s t. open_in(subtopology euclidean (affine hull t)) s
         ==> (s SUBSET relative_interior t <=> s SUBSET t)`;;

let RELATIVE_INTERIOR_TRANSLATION = `!a:real^N s.
        relative_interior (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (relative_interior s)`;;

add_translation_invariants [RELATIVE_INTERIOR_TRANSLATION];;

let RELATIVE_FRONTIER_TRANSLATION = `!a:real^N s.
        relative_frontier (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (relative_frontier s)`;;

add_translation_invariants [RELATIVE_FRONTIER_TRANSLATION];;

let RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> relative_interior(IMAGE f s) = IMAGE f (relative_interior s)`;;

add_linear_invariants [RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE];;

let RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> relative_frontier(IMAGE f s) = IMAGE f (relative_frontier s)`;;

add_linear_invariants [RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE];;

let RELATIVE_INTERIOR_RELATIVE_INTERIOR = `!s:real^N->bool.
        relative_interior(relative_interior s) = relative_interior s`;;

let RELATIVE_INTERIOR_EQ_EMPTY = `!s:real^N->bool.
        convex s ==> (relative_interior s = {} <=> s = {})`;;

let AFF_DIM_NONEMPTY_INTERIOR_OF_EQ = `!u s:real^N->bool.
        convex s /\ affine u /\ s SUBSET u
        ==> (aff_dim s = aff_dim u <=>
             s = {} /\ u = {} \/
             ~((subtopology euclidean u) interior_of s = {}))`;;

let RELATIVE_INTERIOR_INTERIOR = `!s. affine hull s = (:real^N)
       ==> relative_interior s = interior s`;;

let RELATIVE_INTERIOR_OPEN = `!s:real^N->bool. open s ==> relative_interior s = s`;;

let RELATIVE_INTERIOR_NONEMPTY_INTERIOR = `!s. ~(interior s = {}) ==> relative_interior s = interior s`;;

let RELATIVE_FRONTIER_NONEMPTY_INTERIOR = `!s. ~(interior s = {}) ==> relative_frontier s = frontier s`;;

let RELATIVE_FRONTIER_FRONTIER = `!s. affine hull s = (:real^N) ==> relative_frontier s = frontier s`;;

let RELATIVE_FRONTIER_OPEN = `!s:real^N->bool. open s ==> relative_frontier s = frontier s`;;

let AFFINE_HULL_CONVEX_HULL = `!s. affine hull (convex hull s) = affine hull s`;;

let INTERIOR_SIMPLEX_NONEMPTY = `!s:real^N->bool.
        independent s /\ s HAS_SIZE (dimindex(:N))
        ==> ?a. a IN interior(convex hull (vec 0 INSERT s))`;;

let INTERIOR_SUBSET_RELATIVE_INTERIOR = `!s. interior s SUBSET relative_interior s`;;

let RELATIVE_FRONTIER_SUBSET_FRONTIER = `!s:real^N->bool. relative_frontier s SUBSET frontier s`;;

let CONVEX_RELATIVE_INTERIOR = `!s:real^N->bool. convex s ==> convex(relative_interior s)`;;

let IN_RELATIVE_INTERIOR_CONVEX_SHRINK = `!s e x c:real^N.
     convex s /\ c IN relative_interior s /\
     x IN s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN relative_interior s`;;

let IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK = `!s e x c:real^N.
     convex s /\ c IN relative_interior s /\
     x IN closure s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN relative_interior s`;;

let IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT = `!s a b:real^N.
        convex s /\ a IN relative_interior s /\ b IN closure s
        ==> segment(a,b) SUBSET relative_interior s`;;

let INTER_RELATIVE_FRONTIER_CONIC_HULL = `!s t:real^N->bool.
     convex s /\ vec 0 IN relative_interior s /\ t SUBSET relative_frontier s
     ==> t = relative_frontier s INTER conic hull t`;;

let INTER_CONVEX_HULL_INSERT_RELATIVE_EXTERIOR = `!c t s z:real^N.
        convex c /\ t SUBSET c /\ z IN relative_interior c /\
        DISJOINT s (relative_interior c)
        ==> s INTER (convex hull (z INSERT t)) =
            s INTER (convex hull t)`;;

let CONVEX_OPEN_SEGMENT_CASES = `!s a b:real^N.
        convex s /\ a IN closure s /\ b IN closure s
        ==> segment(a,b) SUBSET relative_frontier s \/
            segment(a,b) SUBSET relative_interior s`;;

let CONVEX_OPEN_SEGMENT_CASES_ALT = `!s a b:real^N.
         convex s /\ a IN closure s /\ b IN closure s
         ==> segment (a,b) SUBSET frontier s \/
             segment (a,b) SUBSET interior s`;;

let EXTEND_CONVEX_RELATIVE_FRONTIER_SEGMENT = `!s a b x:real^N.
        convex s /\ a IN closure s /\ b IN closure s /\
        x IN segment(a,b) /\ x IN relative_frontier s
        ==> segment[a,b] SUBSET relative_frontier s`;;

let SEGMENT_SUBSET_RELATIVE_FRONTIER_CONVEX = `!s a b c:real^N.
        convex s /\ c IN segment(a,b) /\ {a,b,c} SUBSET relative_frontier s
        ==> segment[a,b] SUBSET relative_frontier s`;;

let EXTEND_CONVEX_FRONTIER_SEGMENT = `!s a b x:real^N.
        convex s /\ a IN closure s /\ b IN closure s /\
        x IN segment(a,b) /\ x IN frontier s
        ==> segment[a,b] SUBSET frontier s`;;

let RELATIVE_INTERIOR_SING = `!a. relative_interior {a} = {a}`;;

let RELATIVE_FRONTIER_SING = `!a:real^N. relative_frontier {a} = {}`;;

let RELATIVE_INTERIOR_CBALL = `!a r. relative_interior(cball(a,r)) = if r = &0 then {a} else ball(a,r)`;;

let RELATIVE_INTERIOR_BALL = `!a r. relative_interior(ball(a,r)) = ball(a,r)`;;

let RELATIVE_FRONTIER_CBALL = `!a:real^N r. relative_frontier(cball(a,r)) =
                if r = &0 then {} else sphere(a,r)`;;

let RELATIVE_FRONTIER_BALL = `!a:real^N r. relative_frontier(ball(a,r)) =
                if r = &0 then {} else sphere(a,r)`;;

let DIFFERENT_NORM_3_COLLINEAR_POINTS = `!a b x:real^N.
     ~(x IN segment(a,b) /\ norm(a) = norm(b) /\ norm(x) = norm(b))`;;

let OPEN_SEGMENT_SUBSET_BALL = `!a r u v:real^N.
      u IN cball(a,r) /\ v IN cball(a,r) ==> segment(u,v) SUBSET ball(a,r)`;;

let STARLIKE_CONVEX_TWEAK_BOUNDARY_POINTS = `!s t:real^N->bool.
        convex s /\ ~(s = {}) /\
        relative_interior s SUBSET t /\ t SUBSET closure s
        ==> starlike t`;;

let RELATIVE_INTERIOR_PROLONG = `!s x y:real^N.
        x IN relative_interior s /\ y IN s
        ==> ?t. &1 < t /\ (y + t % (x - y)) IN s`;;

let RELATIVE_INTERIOR_CONVEX_PROLONG = `!s. convex s
       ==> relative_interior s =
           {x:real^N | x IN s /\
                       !y. y IN s ==> ?t. &1 < t /\ (y + t % (x - y)) IN s}`;;

let RELATIVE_INTERIOR_EQ_CLOSURE = `!s:real^N->bool.
        relative_interior s = closure s <=> affine s`;;

let RAY_TO_RELATIVE_FRONTIER = `!s a l:real^N.
        bounded s /\ a IN relative_interior s /\
        (a + l) IN affine hull s /\ ~(l = vec 0)
        ==> ?d. &0 < d /\
                (a + d % l) IN relative_frontier s /\
                !e. &0 <= e /\ e < d ==> (a + e % l) IN relative_interior s`;;

let RAY_TO_FRONTIER = `!s a l:real^N.
        bounded s /\ a IN interior s /\ ~(l = vec 0)
        ==> ?d. &0 < d /\ (a + d % l) IN frontier s /\
                !e. &0 <= e /\ e < d ==> (a + e % l) IN interior s`;;

let SEGMENT_TO_RELATIVE_FRONTIER = `!s x y:real^N.
        convex s /\ bounded s /\ x IN relative_interior s /\ y IN s /\
        ~(x = y /\ s = {x})
        ==> ?z. z IN relative_frontier s /\ y IN segment[x,z] /\
                segment(x,z) SUBSET relative_interior s`;;

let SEGMENT_TO_RELATIVE_FRONTIER_SIMPLE = `!s x:real^N.
        bounded s /\ x IN s /\ ~(s = {x})
        ==> ?a b. a IN relative_frontier s /\
                  b IN relative_frontier s /\
                  x IN segment[a,b]`;;

let SEGMENT_TO_FRONTIER_SIMPLE = `!s x:real^N.
        bounded s /\ x IN s
        ==> ?a b. a IN frontier s /\
                  b IN frontier s /\
                  x IN segment[a,b]`;;

let SEGMENT_OUT_TO_FRONTIER = `!s a b:real^N.
        bounded s /\ b IN closure s /\ ~(b = a)
        ==> ?c. ~(c = a) /\ c IN frontier s /\ b IN segment[a,c]`;;

let SUBSET_CONVEX_HULL_RELATIVE_FRONTIER = `!s:real^N->bool.
        bounded s /\ ~(?a. s = {a})
        ==> s SUBSET convex hull (relative_frontier s)`;;

let SUBSET_CONVEX_HULL_FRONTIER = `!s:real^N->bool.
        bounded s ==> s SUBSET convex hull (frontier s)`;;

let AFFINE_HULL_RELATIVE_FRONTIER_BOUNDED = `!s:real^N->bool.
        bounded s /\ ~(?a. s = {a})
        ==> affine hull (relative_frontier s) = affine hull s`;;

let KREIN_MILMAN_RELATIVE_FRONTIER = `!s:real^N->bool.
        convex s /\ compact s /\ ~(?a. s = {a})
        ==> s = convex hull (relative_frontier s)`;;

let KREIN_MILMAN_RELATIVE_BOUNDARY = `!s:real^N->bool.
        convex s /\ compact s /\ ~(?a. s = {a})
        ==> s = convex hull (s DIFF relative_interior s)`;;

let KREIN_MILMAN_FRONTIER = `!s:real^N->bool.
        convex s /\ compact s ==> s = convex hull (frontier s)`;;

let RELATIVE_FRONTIER_NOT_SING = `!s a:real^N. bounded s ==> ~(relative_frontier s = {a})`;;

let RELATIVE_INTERIOR_PCROSS = `!s:real^M->bool t:real^N->bool.
        relative_interior(s PCROSS t) =
        relative_interior s PCROSS relative_interior t`;;

let RELATIVE_FRONTIER_EQ_EMPTY = `!s:real^N->bool. relative_frontier s = {} <=> affine s`;;

let DIAMETER_BOUNDED_BOUND_LT = `!s x y:real^N.
        bounded s /\ x IN relative_interior s /\ y IN closure s /\
        ~(diameter s = &0)
        ==> norm(x - y) < diameter s`;;

let DIAMETER_ATTAINED_RELATIVE_FRONTIER = `!s:real^N->bool.
        bounded s /\ ~(diameter s = &0)
        ==> ?x y. x IN relative_frontier s /\
                  y IN relative_frontier s /\
                  norm(x - y) = diameter s`;;

let DIAMETER_RELATIVE_FRONTIER = `!s:real^N->bool.
        bounded s /\ ~(?a. s = {a})
        ==> diameter(relative_frontier s) = diameter s`;;

let DIAMETER_ATTAINED_FRONTIER = `!s:real^N->bool.
        bounded s /\ ~(diameter s = &0)
        ==> ?x y. x IN frontier s /\ y IN frontier s /\
                  norm(x - y) = diameter s`;;

let DIAMETER_FRONTIER = `!s:real^N->bool. bounded s ==> diameter(frontier s) = diameter s`;;

let CLOSEST_POINT_IN_RELATIVE_INTERIOR = `!s x:real^N.
        closed s /\ ~(s = {}) /\ x IN affine hull s
        ==> ((closest_point s x) IN relative_interior s <=>
             x IN relative_interior s)`;;

let CLOSEST_POINT_IN_RELATIVE_FRONTIER = `!s x:real^N.
        closed s /\ ~(s = {}) /\ x IN affine hull s DIFF relative_interior s
        ==> closest_point s x IN relative_frontier s`;;

let IN_RELATIVE_INTERIOR_IN_OPEN_SEGMENT = `!s x a:real^N.
        convex s /\ x IN relative_interior s /\ a IN affine hull s /\ ~(x = a)
        ==> ?b. b IN s /\ x IN segment(a,b)`;;

let IN_RELATIVE_INTERIOR_IN_OPEN_SEGMENT_STRONG = `!s x a:real^N.
        convex s /\ x IN relative_interior s /\ a IN affine hull s /\ ~(x = a)
        ==> ?b. b IN relative_interior s /\ x IN segment(a,b)`;;

let IN_RELATIVE_INTERIOR_IN_OPEN_SEGMENT_EQ = `!s x:real^N.
        convex s
        ==> (x IN relative_interior s <=>
             ~(s = {}) /\
             !a. a IN s /\ ~(a = x) ==> ?b. b IN s /\ x IN segment(a,b))`;;

let INTER_RELATIVE_INTERIOR_SUBSET = `!s t:real^N->bool.
        convex s /\ convex t
        ==> relative_interior s INTER relative_interior t SUBSET
            relative_interior(s INTER t)`;;

let RELATIVE_INTERIOR_INTER = `!s t:real^N->bool.
        convex s /\ convex t /\
        ~(relative_interior s INTER relative_interior t = {})
        ==> relative_interior(s INTER t) =
            relative_interior s INTER relative_interior t`;;

let SUBSET_RELATIVE_INTERIOR_INTERSECTING_CONVEX = `!s t:real^N->bool.
        convex s /\ convex t /\
        s SUBSET t /\ ~(s INTER relative_interior t = {})
        ==> relative_interior s SUBSET relative_interior t`;;

let CONVEX_HULL_SPHERE = `!a:real^N r. convex hull (sphere(a,r)) = cball(a,r)`;;

let SPHERE_SUBSET_CONVEX = `!s a:real^N r. convex s ==> (sphere(a,r) SUBSET s <=> cball(a,r) SUBSET s)`;;

let DIAMETER_SPHERE = `!a:real^N r. diameter(sphere(a,r)) = if r < &0 then &0 else &2 * r`;;

(* ------------------------------------------------------------------------- *)
(* Small move from (relative frontier of) convex set.                        *)
(* ------------------------------------------------------------------------- *)

let CONVEX_NEARBY_IN_SCALING = `!s:real^N->bool r.
        convex s /\ vec 0 IN relative_interior s /\ &1 < r
        ==> ?d. &0 < d /\
                !x y. x IN s /\ y IN affine hull s /\ dist(x,y) <= d
                      ==> y IN IMAGE (\x. r % x) s`;;

let CONVEX_NEARBY_IN_SCALING_RELATIVE_INTERIOR = `!s:real^N->bool r.
        convex s /\ vec 0 IN relative_interior s /\ &1 < r
        ==> ?d. &0 < d /\
                !x y. x IN s /\ y IN affine hull s /\ dist(x,y) <= d
                      ==> y IN IMAGE (\x. r % x) (relative_interior s)`;;

let CONVEX_NEARBY_NOT_IN_SCALING = `!s:real^N->bool r.
        convex s /\ vec 0 IN relative_interior s /\ &0 < r /\ r < &1
        ==> ?d. &0 < d /\
                !x y. x IN relative_frontier s /\ dist(x,y) <= d
                      ==> ~(y IN IMAGE (\x. r % x) s)`;;

(* ------------------------------------------------------------------------- *)
(* Basic closure properties for "is_interval".                               *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_RELATIVE_INTERIOR = `!s:real^N->bool. is_interval s ==> is_interval(relative_interior s)`;;

let IS_INTERVAL_INTERIOR = `!s:real^N->bool. is_interval s ==> is_interval(interior s)`;;

let IS_INTERVAL_CLOSURE = `!s:real^N->bool. is_interval s ==> is_interval(closure s)`;;

(* ------------------------------------------------------------------------- *)
(* Shrinking space to a ball while preserving convexity.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_PREIMAGE_CONCAVE_SCALING = `!f s t:real^N->bool.
        convex s /\ convex t /\ vec 0 IN s /\
        (\x. --f x) convex_on t /\ (!x. x IN t ==> &0 < f x)
        ==> convex {x | x IN t /\ (inv(f x) % x) IN s}`;;

let CONVEXITY_PRESERVING_SHRINK_0 = `?f g. homeomorphism ((:real^N),ball(vec 0:real^N,&1)) (f,g) /\
         (!s. conic hull (IMAGE f s) = conic hull s) /\
         (!s. vec 0 IN s ==> vec 0 IN IMAGE f s) /\
         (!s. convex s /\ vec 0 IN s ==> convex(IMAGE f s)) /\
         (!s. vec 0 IN relative_interior s
              ==> vec 0 IN relative_interior(IMAGE f s))`;;

(* ------------------------------------------------------------------------- *)
(* Some convexity-related properties of Hausdorff distance                   *)
(* ------------------------------------------------------------------------- *)

let HAUSDIST_CONVEX_HULLS = `!s t:real^N->bool.
        bounded s /\ bounded t
        ==> hausdist(convex hull s,convex hull t) <= hausdist(s,t)`;;

let HAUSDIST_SUMS = `!s t:real^N->bool u.
        bounded s /\ bounded t /\ convex s /\ convex t /\ bounded u /\
        ~(s = {}) /\ ~(t = {}) /\ ~(u = {})
        ==> hausdist({x + e | x IN s /\ e IN u},
                     {y + e | y IN t /\ e IN u}) =
            hausdist(s,t)`;;

let HAUSDIST_COMPLEMENTS_CONVEX_EXPLICIT = `!s t d x:real^N.
        convex s /\ bounded s /\ ~(s = {}) /\
        bounded t /\ ~(x IN s) /\ hausdist(s,t) < d
        ==> ?y. ~(y IN t) /\ dist(x,y) < d`;;

let HAUSDIST_COMPLEMENTS_CONVEX_LE = `!s t:real^N->bool.
      convex s /\ bounded s /\ convex t /\ bounded t /\ ~(s = {}) /\ ~(t = {})
      ==> hausdist((:real^N) DIFF s,(:real^N) DIFF t) <= hausdist(s,t)`;;

(* ------------------------------------------------------------------------- *)
(* The Blaschke selection principle and related results.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HAUSDIST_LIMIT = `!s:(num->real^N->bool) t.
    eventually (\n. bounded(s n) /\ convex(s n) /\ ~(s n = {})) sequentially /\
    compact t /\ ((\n. lift(hausdist(s n,t))) --> vec 0) sequentially
    ==> convex t`;;

let COMPLETE_HAUSDIST_CONVEX = `!f:num->(real^N->bool) c.
        closed c /\
        (!n. bounded(f n) /\ convex(f n) /\ ~(f n = {}) /\ f n SUBSET c) /\
        (!e. &0 < e
             ==> ?N. !m n. m >= N /\ n >= N ==> hausdist(f m,f n) < e)
        ==> ?s. compact s /\ convex s /\ ~(s = {}) /\ s SUBSET c /\
                ((\n. lift(hausdist(f n,s))) --> vec 0) sequentially`;;

let COMPLETE_HAUSDIST_CONVEX_UNIV = `!f:num->(real^N->bool).
        (!n. bounded(f n) /\ convex(f n) /\ ~(f n = {})) /\
        (!e. &0 < e
             ==> ?N. !m n. m >= N /\ n >= N ==> hausdist(f m,f n) < e)
        ==> ?s. compact s /\ convex s /\ ~(s = {}) /\
                ((\n. lift(hausdist(f n,s))) --> vec 0) sequentially`;;

let BLASCHKE = `!f:num->(real^N->bool) c.
        compact c /\ (!n. convex(f n) /\ ~(f n = {}) /\ f n SUBSET c)
        ==> ?r s. (!m n. m < n ==> r m < r n) /\
                  compact s /\ convex s /\ ~(s = {}) /\ s SUBSET c /\
                  ((\n. lift(hausdist(f(r n),s))) --> vec 0) sequentially`;;

let BLASCHKE_UNIV = `!f:num->(real^N->bool) c.
        bounded c /\ (!n. convex(f n) /\ ~(f n = {}) /\ f n SUBSET c)
        ==> ?r s. (!m n. m < n ==> r m < r n) /\
                  compact s /\ convex s /\ ~(s = {}) /\
                  ((\n. lift(hausdist(f(r n),s))) --> vec 0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Interior, relative interior and closure interrelations.                   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CLOSURE_INTERIOR = `!s:real^N->bool.
        convex s /\ ~(interior s = {})
        ==> closure(interior s) = closure s`;;

let EMPTY_INTERIOR_SUBSET_HYPERPLANE = `!s. convex s /\ interior s = {}
       ==> ?a:real^N b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`;;

let CONVEX_INTERIOR_CLOSURE = `!s:real^N->bool. convex s ==> interior(closure s) = interior s`;;

let FRONTIER_CLOSURE_CONVEX = `!s:real^N->bool. convex s ==> frontier(closure s) = frontier s`;;

let CONVEX_CLOSURE_RELATIVE_INTERIOR = `!s:real^N->bool.
        convex s ==> closure(relative_interior s) = closure s`;;

let OPEN_IN_CONVEX_MEETS_RELATIVE_INTERIOR = `!u s:real^N->bool.
        convex u /\ open_in (subtopology euclidean u) s /\ ~(s = {})
        ==> ~(s INTER relative_interior u = {})`;;

let OPEN_SUBSET_CLOSURE_CONVEX = `!u s:real^N->bool.
        open u /\ convex s ==> (u SUBSET closure s <=> u SUBSET interior s)`;;

let SETDIST_RELATIVE_INTERIOR = `(!s t. convex s ==> setdist(relative_interior s,t) = setdist(s,t)) /\
   (!s t. convex t ==> setdist(s,relative_interior t) = setdist(s,t))`;;

let HAUSDIST_RELATIVE_INTERIOR = `(!s t. convex s ==> hausdist(relative_interior s,t) = hausdist(s,t)) /\
   (!s t. convex t ==> hausdist(s,relative_interior t) = hausdist(s,t))`;;

let AFFINE_HULL_RELATIVE_INTERIOR = `!s. convex s
       ==> affine hull (relative_interior s) = affine hull s`;;

let AFF_DIM_RELATIVE_INTERIOR = `!s:real^N->bool. convex s ==> aff_dim(relative_interior s) = aff_dim s`;;

let CONVEX_RELATIVE_INTERIOR_CLOSURE = `!s:real^N->bool.
        convex s ==> relative_interior(closure s) = relative_interior s`;;

let RELATIVE_FRONTIER_CLOSURE = `!s. convex s ==> relative_frontier(closure s) = relative_frontier s`;;

let RELATIVE_FRONTIER_RELATIVE_INTERIOR = `!s:real^N->bool.
        convex s
        ==> relative_frontier(relative_interior s) = relative_frontier s`;;

let CONNECTED_INTER_RELATIVE_FRONTIER = `!s t:real^N->bool.
        connected s /\ s SUBSET affine hull t /\
        ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER relative_frontier t = {})`;;

let CLOSED_RELATIVE_FRONTIER = `!s:real^N->bool. closed(relative_frontier s)`;;

let CLOSED_RELATIVE_BOUNDARY = `!s. closed s ==> closed(s DIFF relative_interior s)`;;

let COMPACT_RELATIVE_BOUNDARY = `!s. compact s ==> compact(s DIFF relative_interior s)`;;

let BOUNDED_RELATIVE_FRONTIER = `!s:real^N->bool. bounded s ==> bounded(relative_frontier s)`;;

let COMPACT_RELATIVE_FRONTIER_BOUNDED = `!s:real^N->bool. bounded s ==> compact(relative_frontier s)`;;

let COMPACT_RELATIVE_FRONTIER = `!s:real^N->bool. compact s ==> compact(relative_frontier s)`;;

let CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE = `!s t. convex s /\ convex t
         ==> (relative_interior s = relative_interior t <=>
              closure s = closure t)`;;

let CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE_STRADDLE = `!s t. convex s /\ convex t
         ==> (relative_interior s = relative_interior t <=>
              relative_interior s SUBSET t /\ t SUBSET closure s)`;;

let RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX = `!f:real^M->real^N s.
        linear f /\ convex s
        ==> relative_interior(IMAGE f s) = IMAGE f (relative_interior s)`;;

let RELATIVE_INTERIOR_LINEAR_PREIMAGE_CONVEX = `!f:real^M->real^N s.
        linear f /\ convex s /\ ~({x | f(x) IN relative_interior s} = {})
        ==> relative_interior {x | f(x) IN s} =
            {x | f(x) IN relative_interior s}`;;

let RELATIVE_INTERIOR_SUMS = `!s t:real^N->bool.
        convex s /\ convex t
        ==> relative_interior {x + y | x IN s /\ y IN t} =
            {x + y | x IN relative_interior s /\ y IN relative_interior t}`;;

let CLOSURE_INTERS_CONVEX = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s) /\
        ~(INTERS(IMAGE relative_interior f) = {})
        ==> closure(INTERS f) = INTERS(IMAGE closure f)`;;

let CLOSURE_INTERS_CONVEX_OPEN = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ open s)
        ==> closure(INTERS f) =
                if INTERS f = {} then {}
                else INTERS(IMAGE closure f)`;;

let CLOSURE_INTER_CONVEX = `!s t:real^N->bool.
        convex s /\ convex t /\
        ~(relative_interior s INTER relative_interior t = {})
        ==> closure(s INTER t) = closure(s) INTER closure(t)`;;

let CLOSURE_INTER_CONVEX_OPEN = `!s t. convex s /\ open s /\ convex t /\ open t
         ==> closure(s INTER t) =
                if s INTER t = {} then {} else closure(s) INTER closure(t)`;;

let CLOSURE_CONVEX_INTER_SUPERSET = `!s t:real^N->bool.
        convex s /\ ~(interior s = {}) /\ interior s SUBSET closure t
        ==> closure(s INTER t) = closure s`;;

let CLOSURE_DYADIC_RATIONALS_IN_CONVEX_SET = `!s:real^N->bool.
        convex s /\ ~(interior s = {})
        ==> closure(s INTER
                    { inv(&2 pow n) % x | n,x |
                      !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }) =
            closure s`;;

let CLOSURE_RATIONALS_IN_CONVEX_SET = `!s:real^N->bool.
      convex s /\ ~(interior s = {})
      ==> closure(s INTER
                  { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }) =
          closure s`;;

let RELATIVE_INTERIOR_CONVEX_INTER_AFFINE = `!s t:real^N->bool.
        convex s /\ affine t /\ ~(interior s INTER t = {})
        ==> relative_interior(s INTER t) = interior s INTER t`;;

let CONNECTED_WITH_RELATIVE_INTERIOR_OPEN_IN_CONVEX = `!c s:real^N->bool.
        convex c /\ connected s /\ open_in (subtopology euclidean c) s
        ==> connected(relative_interior c INTER s)`;;

let RELATIVE_INTERIOR_CBALL_INTER_AFFINE = `!s a:real^N r.
        affine s /\ a IN s /\ ~(r = &0)
        ==> relative_interior(cball(a,r) INTER s) = ball(a,r) INTER s`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about extending nondecreasing functions.                           *)
(* ------------------------------------------------------------------------- *)

let NONDECREASING_EXTENDS_TO_CONVEX_HULL = `!f s. (!x y. x IN s /\ y IN s /\ drop x <= drop y
                ==> drop(f x) <= drop(f y))
         ==> ?g. (!x y. x IN convex hull s /\ y IN convex hull s /\
                        drop x <= drop y
                        ==> drop(g x) <= drop(g y)) /\
                 (!x. x IN s ==> g x = f x)`;;

let NONDECREASING_EXTENDS_FROM_DENSE = `!f s. closure s = (:real^1) /\ closure(IMAGE f s) = (:real^1) /\
         (!x y. x IN s /\ y IN s /\ drop x <= drop y
                ==> drop(f x) <= drop(f y))
         ==> ?g. (!x y. drop x <= drop y ==> drop(g x) <= drop(g y)) /\
                 (!x. x IN s ==> g x = f x) /\
                 g continuous_on (:real^1) /\
                 IMAGE g (:real^1) = (:real^1)`;;

let INCREASING_EXTENDS_FROM_DENSE = `!f s. closure s = (:real^1) /\ closure(IMAGE f s) = (:real^1) /\
         (!x y. x IN s /\ y IN s /\ drop x < drop y
                ==> drop(f x) < drop(f y))
         ==> ?g. (!x y. drop(g x) < drop(g y) <=> drop x < drop y) /\
                 (!x. x IN s ==> g x = f x) /\
                 g continuous_on (:real^1) /\
                 IMAGE g (:real^1) = (:real^1)`;;

(* ------------------------------------------------------------------------- *)
(* More basics about segments.                                               *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_SEGMENT = `(!a b:real^N. bounded(segment[a,b])) /\
   (!a b:real^N. bounded(segment(a,b)))`;;

let SEGMENT_IMAGE_INTERVAL = `(!a b. segment[a,b] =
          IMAGE (\u. (&1 - drop u) % a + drop u % b)
                (interval[vec 0,vec 1])) /\
   (!a b. ~(a = b)
          ==> segment(a,b) =
                IMAGE (\u. (&1 - drop u) % a + drop u % b)
                (interval(vec 0,vec 1)))`;;

let CLOSURE_SEGMENT = `(!a b:real^N. closure(segment[a,b]) = segment[a,b]) /\
   (!a b:real^N. closure(segment(a,b)) = if a = b then {} else segment[a,b])`;;

let CLOSED_SEGMENT = `(!a b:real^N. closed(segment[a,b])) /\
   (!a b:real^N. closed(segment(a,b)) <=> a = b)`;;

let COMPACT_SEGMENT = `(!a b:real^N. compact(segment[a,b])) /\
   (!a b:real^N. compact(segment(a,b)) <=> a = b)`;;

let AFFINE_HULL_SEGMENT = `(!a b:real^N. affine hull (segment [a,b]) = affine hull {a,b}) /\
   (!a b:real^N. affine hull (segment(a,b)) =
                 if a = b then {} else affine hull {a,b})`;;

let SEGMENT_AS_BALL = `(!a b. segment[a:real^N,b] =
         affine hull {a,b} INTER cball(inv(&2) % (a + b),norm(b - a) / &2)) /\
   (!a b. segment(a:real^N,b) =
         affine hull {a,b} INTER ball(inv(&2) % (a + b),norm(b - a) / &2))`;;

let CONVEX_SEGMENT = `(!a b. convex(segment[a,b])) /\ (!a b. convex(segment(a,b)))`;;

let RELATIVE_INTERIOR_SEGMENT = `(!a b:real^N.
      relative_interior(segment[a,b]) = if a = b then {a} else segment(a,b)) /\
   (!a b:real^N. relative_interior(segment(a,b)) = segment(a,b))`;;

let OPEN_IN_SEGMENT = `!s a b:real^N.
        segment(a,b) SUBSET s /\ s SUBSET affine hull (segment(a,b))
        ==> open_in (subtopology euclidean s) (segment(a,b))`;;

let AFF_DIM_SEGMENT = `(!a b:real^N. aff_dim(segment[a,b]) = if a = b then &0 else &1) /\
   (!a b:real^N. aff_dim(segment(a,b)) = if a = b then -- &1 else &1)`;;

let CONVEX_SEMIOPEN_SEGMENT = `(!a b:real^N. convex(segment[a,b] DELETE a)) /\
   (!a b:real^N. convex(segment[a,b] DELETE b))`;;

let CONNECTED_SEMIOPEN_SEGMENT = `(!a b:real^N. connected(segment[a,b] DELETE a)) /\
   (!a b:real^N. connected(segment[a,b] DELETE b))`;;

let SEGMENT_EQ_EMPTY = `(!a b:real^N. ~(segment[a,b] = {})) /\
   (!a b:real^N. segment(a,b) = {} <=> a = b)`;;

let FINITE_SEGMENT = `(!a b:real^N. FINITE(segment[a,b]) <=> a = b) /\
   (!a b:real^N. FINITE(segment(a,b)) <=> a = b)`;;

let SEGMENT_EQ_SING = `(!a b c:real^N. segment[a,b] = {c} <=> a = c /\ b = c) /\
   (!a b c:real^N. ~(segment(a,b) = {c}))`;;

let SEGMENT_SUBSET_RELATIVE_FRONTIER_CONVEX_GEN = `!s a b c:real^N.
        convex s /\ collinear{a,b,c} /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        {a,b,c} SUBSET relative_frontier s
        ==> convex hull {a,b,c} SUBSET relative_frontier s`;;

let SUBSET_SEGMENT_OPEN_CLOSED = `!a b c d:real^N.
        segment(a,b) SUBSET segment(c,d) <=>
        a = b \/ segment[a,b] SUBSET segment[c,d]`;;

let SUBSET_SEGMENT = `(!a b c d:real^N.
        segment[a,b] SUBSET segment[c,d] <=>
        a IN segment[c,d] /\ b IN segment[c,d]) /\
   (!a b c d:real^N.
        segment[a,b] SUBSET segment(c,d) <=>
        a IN segment(c,d) /\ b IN segment(c,d)) /\
   (!a b c d:real^N.
        segment(a,b) SUBSET segment[c,d] <=>
        a = b \/ a IN segment[c,d] /\ b IN segment[c,d]) /\
   (!a b c d:real^N.
        segment(a,b) SUBSET segment(c,d) <=>
        a = b \/ a IN segment[c,d] /\ b IN segment[c,d])`;;

let INTERIOR_SEGMENT = `(!a b:real^N. interior(segment[a,b]) =
                 if 2 <= dimindex(:N) then {} else segment(a,b)) /\
   (!a b:real^N. interior(segment(a,b)) =
                 if 2 <= dimindex(:N) then {} else segment(a,b))`;;

let FRONTIER_SEGMENT = `(!a b:real^N.
        frontier(segment[a,b]) =
        if 2 <= dimindex(:N) then segment[a,b] else {a,b}) /\
   (!a b:real^N.
        frontier(segment(a,b)) =
        if a = b then {}
        else if 2 <= dimindex(:N) then segment[a,b] else {a,b})`;;

let SEGMENT_EQ = `(!a b c d:real^N.
        segment[a,b] = segment[c,d] <=> {a,b} = {c,d}) /\
   (!a b c d:real^N.
        ~(segment[a,b] = segment(c,d))) /\
   (!a b c d:real^N.
        ~(segment(a,b) = segment[c,d])) /\
   (!a b c d:real^N.
        segment(a,b) = segment(c,d) <=> a = b /\ c = d \/ {a,b} = {c,d})`;;

let COLLINEAR_SEGMENT = `(!a b:real^N. collinear(segment[a,b])) /\
   (!a b:real^N. collinear(segment(a,b)))`;;

let INTER_SEGMENT = `!a b c:real^N.
        b IN segment[a,c] \/ ~collinear{a,b,c}
        ==> segment[a,b] INTER segment[b,c] = {b}`;;

let CONVEX_LINE_INTERSECTION_UNIQUE_CLOSED = `!s a b:real^N.
        convex s /\ closed s /\
        a IN relative_frontier s /\ b IN relative_frontier s /\
        ~(segment(a,b) INTER relative_interior s = {})
        ==> s INTER (affine hull {a,b}) = segment[a,b]`;;

let CONVEX_LINE_INTERSECTION_UNIQUE_OPEN_IN = `!s a b:real^N.
        convex s /\
        open_in (subtopology euclidean (affine hull s)) s /\
        a IN relative_frontier s /\ b IN relative_frontier s /\
        ~(segment(a,b) INTER s = {})
        ==> s INTER (affine hull {a,b}) = segment(a,b)`;;

let CONVEX_LINE_INTERSECTION_UNIQUE_OPEN = `!s a b:real^N.
        convex s /\ open s /\
        a IN relative_frontier s /\ b IN relative_frontier s /\
        ~(segment(a,b) INTER s = {})
        ==> s INTER (affine hull {a,b}) = segment(a,b)`;;

let CONVEX_LINE_INTERSECTIONS = `!s a b:real^N.
        convex s /\ a IN relative_frontier s /\ b IN relative_frontier s /\
        ~(segment(a,b) INTER relative_interior s = {})
        ==> ~(a = b) /\
            closure s INTER affine hull {a,b} = segment[a,b] /\
            relative_interior s INTER affine hull {a,b} = segment(a,b) /\
            relative_frontier s INTER affine hull {a,b} = {a,b}`;;

let CONVEX_LINE_INTERSECTIONS_ALT = `!s a b:real^N.
        convex s /\ a IN relative_frontier s /\ b IN relative_frontier s /\
        ~(segment(a,b) SUBSET relative_frontier s)
        ==> ~(a = b) /\
            closure s INTER affine hull {a,b} = segment[a,b] /\
            relative_interior s INTER affine hull {a,b} = segment(a,b) /\
            relative_frontier s INTER affine hull {a,b} = {a,b}`;;

(* ------------------------------------------------------------------------- *)
(* Theorems about strips between bounds on a component.                      *)
(* ------------------------------------------------------------------------- *)

let CLOSED_STRIP_COMPONENT_LE = `!a k. closed {x:real^N | abs(x$k) <= a}`;;

let OPEN_STRIP_COMPONENT_LT = `!a k. open {x:real^N | abs(x$k) < a}`;;

let INTERIOR_STRIP_COMPONENT_LE = `!a k. interior {x:real^N | abs(x$k) <= a} = {x | abs(x$k) < a}`;;

let CLOSURE_STRIP_COMPONENT_LT = `!a k. closure {x:real^N | abs(x$k) < a} =
         if a = &0 then {} else {x | abs(x$k) <= a}`;;

let FRONTIER_STRIP_COMPONENT_LE = `!a k. frontier {x:real^N | abs(x$k) <= a} = {x | abs(x$k) = a}`;;

let FRONTIER_STRIP_COMPONENT_LT = `!a k. frontier {x:real^N | abs(x$k) < a} =
         if a = &0 then {} else {x | abs(x$k) = a}`;;

(* ------------------------------------------------------------------------- *)
(* Lower-dimensional affine subsets are nowhere dense.                       *)
(* ------------------------------------------------------------------------- *)

let DENSE_COMPLEMENT_SUBSPACE = `!s t:real^N->bool.
        dim t < dim s /\ subspace s ==> closure(s DIFF t) = s`;;

let DENSE_COMPLEMENT_AFFINE = `!s t:real^N->bool.
        aff_dim t < aff_dim s /\ affine s ==> closure(s DIFF t) = s`;;

let DENSE_COMPLEMENT_OPEN_IN_AFFINE_HULL = `!s t:real^N->bool.
        aff_dim t < aff_dim s /\
        open_in (subtopology euclidean (affine hull s)) s
        ==> closure(s DIFF t) = closure s`;;

let DENSE_COMPLEMENT_CONVEX = `!s t:real^N->bool.
        aff_dim t < aff_dim s /\ convex s ==> closure(s DIFF t) = closure s`;;

let DENSE_COMPLEMENT_CONVEX_CLOSED = `!s t:real^N->bool.
        aff_dim t < aff_dim s /\ convex s /\ closed s
        ==> closure(s DIFF t) = s`;;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of all convex compact sets with same affine dimension, and  *)
(* in particular all those with nonempty interior.                           *)
(* ------------------------------------------------------------------------- *)

let COMPACT_FRONTIER_LINE_LEMMA = `!s x. compact s /\ (vec 0 IN s) /\ ~(x = vec 0 :real^N)
         ==> ?u. &0 <= u /\ (u % x) IN frontier s /\
                 !v. u < v ==> ~((v % x) IN s)`;;

let STARLIKE_COMPACT_PROJECTIVE = `!s:real^N->bool a.
       compact s /\ a IN relative_interior s /\
       (!x. x IN s ==> segment(a,x) SUBSET relative_interior s)
       ==> s DIFF relative_interior s homeomorphic
           sphere(a,&1) INTER affine hull s /\
           s homeomorphic cball(a,&1) INTER affine hull s /\
           relative_interior s homeomorphic (ball(a,&1)) INTER affine hull s`;;

let HOMEOMORPHIC_CONVEX_COMPACT_SETS = `(!s:real^M->bool t:real^N->bool.
        convex s /\ compact s /\ convex t /\ compact t /\ aff_dim s = aff_dim t
        ==> s homeomorphic t)`
and HOMEOMORPHIC_RELATIVE_INTERIORS_CONVEX_COMPACT_SETS = `(!s:real^M->bool t:real^N->bool.
        convex s /\ compact s /\ convex t /\ compact t /\ aff_dim s = aff_dim t
        ==> relative_interior s homeomorphic relative_interior t)`
and HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS = `(!s:real^M->bool t:real^N->bool.
        convex s /\ bounded s /\ convex t /\ bounded t /\ aff_dim s = aff_dim t
        ==> relative_frontier s homeomorphic relative_frontier t)`;;

let HOMEOMORPHIC_CONVEX_COMPACT = `!s:real^N->bool t:real^N->bool.
        convex s /\ compact s /\ ~(interior s = {}) /\
        convex t /\ compact t /\ ~(interior t = {})
        ==> s homeomorphic t`;;

let HOMEOMORPHIC_CONVEX_COMPACT_CBALL = `!s:real^N->bool b:real^N e.
        convex s /\ compact s /\ ~(interior s = {}) /\ &0 < e
        ==> s homeomorphic cball(b,e)`;;

let HOMEOMORPHIC_CLOSED_INTERVALS = `!a b:real^N c d:real^N.
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {})
        ==> interval[a,b] homeomorphic interval[c,d]`;;

(* ------------------------------------------------------------------------- *)
(* Hence homeomorphism of convex open sets of same affine dimension.         *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_RELATIVELY_OPEN_CONVEX_SETS = `!s:real^M->bool t:real^N->bool.
        convex s /\ open_in (subtopology euclidean (affine hull s)) s /\
        convex t /\ open_in (subtopology euclidean (affine hull t)) t /\
        aff_dim s = aff_dim t
        ==> s homeomorphic t`;;

let HOMEOMORPHIC_CONVEX_OPEN_SETS = `!s:real^N->bool t:real^N->bool.
        convex s /\ open s /\ convex t /\ open t /\ (s = {} <=> t = {})
        ==> s homeomorphic t`;;

(* ------------------------------------------------------------------------- *)
(* More refined Lipschitz homeomorphisms between relative frontiers.         *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_CONVEX_SPHERICAL_PROJECTION_EXPLICIT = `!r s x y:real^N.
      convex s /\ &0 < r /\ vec 0 IN s /\
      ball(vec 0,r) INTER affine hull s SUBSET relative_interior s /\
      x IN relative_frontier s /\ y IN relative_frontier s
      ==> dist(inv(norm x) % x,inv(norm y) % y) <= inv r * dist(x,y)`;;

let LIPSCHITZ_CONVEX_SPHERICAL_PROJECTION = `!s:real^N->bool.
     convex s /\ vec 0 IN relative_interior s
     ==> ?B. !x y. x IN relative_frontier s /\ y IN relative_frontier s
                   ==> dist(inv(norm x) % x,inv(norm y) % y) <= B * dist(x,y)`;;

let INVERSE_LIPSCHITZ_CONVEX_SPHERICAL_PROJECTION_EXPLICIT = `!r R s x y:real^N.
      convex s /\ &0 < r /\ vec 0 IN s /\
      ball(vec 0,r) INTER affine hull s SUBSET relative_interior s /\
      s SUBSET cball(vec 0,R) /\
      x IN relative_frontier s /\ y IN relative_frontier s
      ==> dist(inv(norm x) % x,inv(norm y) % y) >= r / R pow 2 * dist(x,y)`;;

let INVERSE_LIPSCHITZ_CONVEX_SPHERICAL_PROJECTION = `!s:real^N->bool.
    convex s /\ bounded s /\ vec 0 IN relative_interior s
    ==>  ?B. &0 < B /\
             !x y. x IN relative_frontier s /\ y IN relative_frontier s
                   ==> dist(inv(norm x) % x,inv(norm y) % y) >= B * dist(x,y)`;;

let BILIPSCHITZ_HOMEOMORPHISM_SPHERICAL_PROJECTION = `!s:real^N->bool.
        convex s /\ bounded s /\ vec 0 IN relative_interior s
        ==> ?g. homeomorphism
                  (relative_frontier s,sphere(vec 0,&1) INTER affine hull s)
                  ((\x. inv(norm x) % x),g) /\
                (?B. !x y. x IN relative_frontier s /\ y IN relative_frontier s
                           ==> norm(inv(norm x) % x - inv(norm y) % y)
                               <= B * norm(x - y)) /\
                (?B. !x y. x IN sphere(vec 0,&1) INTER affine hull s /\
                           y IN sphere(vec 0,&1) INTER affine hull s
                           ==> norm(g x - g y) <= B * norm(x - y))`;;

let BILIPSCHITZ_HOMEOMORPHISM_RELATIVE_FRONTIERS = `!s:real^M->bool t:real^N->bool.
     convex s /\ bounded s /\ convex t /\ bounded t /\ aff_dim s = aff_dim t
     ==> ?f g. homeomorphism (relative_frontier s,relative_frontier t) (f,g) /\
               (?B. !x y. x IN relative_frontier s /\
                          y IN relative_frontier s
                          ==> norm(f x - f y) <= B * norm(x - y)) /\
               (?B. !x y. x IN relative_frontier t /\
                          y IN relative_frontier t
                          ==> norm(g x - g y) <= B * norm(x - y))`;;

(* ------------------------------------------------------------------------- *)
(* More about affine dimension of special sets.                              *)
(* ------------------------------------------------------------------------- *)

let AFF_DIM_NONEMPTY_INTERIOR_EQ = `!s:real^N->bool.
        convex s ==> (aff_dim s = &(dimindex (:N)) <=> ~(interior s = {}))`;;

let AFF_DIM_BALL = `!a:real^N r.
        aff_dim(ball(a,r)) = if &0 < r then &(dimindex(:N)) else --(&1)`;;

let AFF_DIM_CBALL = `!a:real^N r.
        aff_dim(cball(a,r)) =
            if &0 < r then &(dimindex(:N))
            else if r = &0 then &0 else --(&1)`;;

let AFF_DIM_INTERVAL = `(!a b:real^N.
        aff_dim(interval[a,b]) =
                if interval[a,b] = {} then --(&1)
                else &(CARD {i | 1 <= i /\ i <= dimindex(:N) /\ a$i < b$i})) /\
   (!a b:real^N.
         aff_dim(interval(a,b)) =
                if interval(a,b) = {} then --(&1)
                else &(dimindex(:N)))`;;

(* ------------------------------------------------------------------------- *)
(* A complete graph of |R|-many vertices can be embedded in R^3 with the     *)
(* edges as straight-line segments that intersect only at common endpoints.  *)
(* Basically, you just scatter the points onto the twisted cubic.            *)
(* ------------------------------------------------------------------------- *)

let GRAPH_EMBEDS_IN_R3 = `!s:A->bool.
        s <=_c (:real)
        ==> ?v:A->real^3.
                (!a b. a IN s /\ b IN s ==> (v a = v b <=> a = b)) /\
                (!a b c d. ~({v a,v b} = {v c,v d})
                           ==> segment[v a,v b] INTER segment[v c,v d]
                               SUBSET {v a,v b} INTER {v c,v d})`;;

(* ------------------------------------------------------------------------- *)
(* Deducing convexity from midpoint convexity in common cases.               *)
(* ------------------------------------------------------------------------- *)

let MIDPOINT_CONVEX_DYADIC_RATIONALS = `!f:real^N->real s.
        (!x y. x IN s /\ y IN s
               ==> midpoint(x,y) IN s /\
                   f(midpoint(x,y)) <= (f(x) + f(y)) / &2)
        ==> !n m p x y.
                x IN s /\ y IN s /\ m + p = 2 EXP n
                ==> (&m / &2 pow n % x + &p / &2 pow n % y) IN s /\
                    f(&m / &2 pow n % x + &p / &2 pow n % y)
                    <= &m / &2 pow n * f x + &p / &2 pow n * f y`;;

let CONTINUOUS_MIDPOINT_CONVEX = `!f:real^N->real s.
        (lift o f) continuous_on s /\ convex s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint(x,y)) <= (f(x) + f(y)) / &2)
         ==> f convex_on s`;;

(* ------------------------------------------------------------------------- *)
(* Slightly shaper separating/supporting hyperplane results.                 *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_RELATIVE_INTERIORS = `!s t. convex s /\ convex t /\
         ~(s = {} /\ t = (:real^N) \/ s = (:real^N) /\ t = {}) /\
         DISJOINT (relative_interior s) (relative_interior t)
         ==> ?a b. ~(a = vec 0) /\
                   (!x. x IN s ==> a dot x <= b) /\
                   (!x. x IN t ==> a dot x >= b)`;;

let SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY = `!s x:real^N.
        convex s /\ x IN s /\ ~(x IN relative_interior s)
        ==> ?a. ~(a = vec 0) /\
                (!y. y IN s ==> a dot x <= a dot y) /\
                (!y. y IN relative_interior s ==> a dot x < a dot y)`;;

let SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER = `!s x:real^N.
        convex s /\ x IN relative_frontier s
        ==> ?a. ~(a = vec 0) /\
                (!y. y IN closure s ==> a dot x <= a dot y) /\
                (!y. y IN relative_interior s ==> a dot x < a dot y)`;;

let SUPPORTING_HYPERPLANE_FRONTIER = `!s x:real^N.
        convex s /\ x IN frontier s
        ==> ?a. ~(a = vec 0) /\
                !y. y IN closure s ==> a dot x <= a dot y`;;

(* ------------------------------------------------------------------------- *)
(* Containment of rays in unbounded convex sets.                             *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY = `!s a:real^N.
        convex s /\ ~bounded s /\ closed s /\ a IN s
        ==> ?l. ~(l = vec 0) /\ !t. &0 <= t ==> (a + t % l) IN s`;;

let CONVEX_CLOSED_CONTAINS_SAME_RAY = `!s a b l:real^N.
        convex s /\ closed s /\ b IN s /\ (!t. &0 <= t ==> (a + t % l) IN s)
        ==> !t. &0 <= t ==> (b + t % l) IN s`;;

let UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAYS = `!s:real^N->bool.
        convex s /\ ~bounded s /\ closed s
        ==> ?l. ~(l = vec 0) /\ !a t. a IN s /\ &0 <= t ==> (a + t % l) IN s`;;

let RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAY = `!s a:real^N.
        convex s /\ ~bounded s /\ a IN relative_interior s
        ==> ?l. ~(l = vec 0) /\
                !t. &0 <= t ==> (a + t % l) IN relative_interior s`;;

let RELATIVE_INTERIOR_CONVEX_CONTAINS_SAME_RAY = `!s a b l:real^N.
        convex s /\ b IN relative_interior s /\
        (!t. &0 <= t ==> (a + t % l) IN relative_interior s)
        ==> !t. &0 <= t ==> (b + t % l) IN relative_interior s`;;

let RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAYS = `!s:real^N->bool.
        convex s /\ ~bounded s
        ==> ?l. ~(l = vec 0) /\
                !a t. a IN relative_interior s /\ &0 <= t
                      ==> (a + t % l) IN relative_interior s`;;

let CONVEX_TRIPLE_RELATIVE_FRONTIER = `!s a b c d e.
        convex s /\
        {a,b,c} SUBSET relative_frontier s /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        d dot a = e /\ d dot b = e /\ d dot c = e
        ==> s SUBSET {x:real^2 | d dot x <= e} \/
            s SUBSET {x:real^2 | d dot x >= e}`;;

(* ------------------------------------------------------------------------- *)
(* Explicit formulas for interior and relative interior of convex hull.      *)
(* ------------------------------------------------------------------------- *)

let EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL = `!s. FINITE s
       ==> {y:real^N | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                           sum s u = &1 /\
                           vsum s (\x. u x % x) = y}
       SUBSET relative_interior(convex hull s)`;;

let EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL = `!s. FINITE s
       ==> {y:real^N | ?u. (!x. x IN s ==> &0 < u x) /\
                           sum s u = &1 /\
                           vsum s (\x. u x % x) = y}
       SUBSET relative_interior(convex hull s)`;;

let RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT = `!s. ~(affine_dependent s)
       ==> relative_interior(convex hull s) =
             {y:real^N | ?u. (!x. x IN s ==> &0 < u x) /\
                             sum s u = &1 /\
                             vsum s (\x. u x % x) = y}`;;

let EXPLICIT_SUBSET_INTERIOR_CONVEX_HULL = `!s. FINITE s /\ affine hull s = (:real^N)
       ==> {y | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                    sum s u = &1 /\
                    vsum s (\x. u x % x) = y}
           SUBSET interior(convex hull s)`;;

let EXPLICIT_SUBSET_INTERIOR_CONVEX_HULL_MINIMAL = `!s. FINITE s /\ affine hull s = (:real^N)
       ==> {y | ?u. (!x. x IN s ==> &0 < u x) /\
                    sum s u = &1 /\
                    vsum s (\x. u x % x) = y}
           SUBSET interior(convex hull s)`;;

let INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL = `!s:real^N->bool.
        ~(affine_dependent s)
        ==> interior(convex hull s) =
             if CARD(s) <= dimindex(:N) then {}
              else {y | ?u. (!x. x IN s ==> &0 < u x) /\
                            sum s u = &1 /\
                            vsum s (\x. u x % x) = y}`;;

let INTERIOR_CONVEX_HULL_EXPLICIT = `!s:real^N->bool.
        ~(affine_dependent s)
        ==> interior(convex hull s) =
             if CARD(s) <= dimindex(:N) then {}
              else {y | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                            sum s u = &1 /\
                            vsum s (\x. u x % x) = y}`;;

let DISJOINT_RELATIVE_INTERIOR_CONVEX_HULL = `!s:real^N->bool.
        ~affine_dependent s /\ ~(?a. s = {a})
        ==> relative_interior(convex hull s) INTER s = {}`;;

let INTERIOR_CONVEX_HULL_3_MINIMAL = `!a b c:real^2.
        ~collinear{a,b,c}
        ==> interior(convex hull {a,b,c}) =
                {v | ?x y z. &0 < x /\
                             &0 < y /\
                             &0 < z /\
                             x + y + z = &1 /\
                             x % a + y % b + z % c = v}`;;

let INTERIOR_CONVEX_HULL_3 = `!a b c:real^2.
        ~collinear{a,b,c}
        ==> interior(convex hull {a,b,c}) =
                {v | ?x y z. &0 < x /\ x < &1 /\
                             &0 < y /\ y < &1 /\
                             &0 < z /\ z < &1 /\
                             x + y + z = &1 /\
                             x % a + y % b + z % c = v}`;;

(* ------------------------------------------------------------------------- *)
(* Similar results for closure and (relative or absolute) frontier.          *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_CONVEX_HULL = `!s. compact s ==> closure(convex hull s) = convex hull s`;;

let RELATIVE_FRONTIER_CONVEX_HULL_EXPLICIT = `!s:real^N->bool.
        ~(affine_dependent s)
        ==> relative_frontier(convex hull s) =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         (?x. x IN s /\ u x = &0) /\
                         sum s u = &1 /\
                         vsum s (\x. u x % x) = y}`;;

let FRONTIER_CONVEX_HULL_EXPLICIT = `!s:real^N->bool.
        ~(affine_dependent s)
        ==> frontier(convex hull s) =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         (dimindex(:N) < CARD s ==> ?x. x IN s /\ u x = &0) /\
                         sum s u = &1 /\
                         vsum s (\x. u x % x) = y}`;;

let RELATIVE_FRONTIER_OF_CONVEX_HULL = `!s:real^N->bool.
        ~(affine_dependent s)
        ==> relative_frontier(convex hull s) =
                UNIONS { convex hull (s DELETE a) |a| a IN s }`;;

let FRONTIER_CONVEX_HULL_CASES = `!s:real^N->bool.
        ~(affine_dependent s)
        ==> frontier(convex hull s) =
                if CARD(s) <= dimindex(:N) then convex hull s
                else UNIONS { convex hull (s DELETE a) |a| a IN s }`;;

let IN_FRONTIER_CONVEX_HULL = `!s x:real^N.
        FINITE s /\ CARD s <= dimindex(:N) + 1 /\ x IN s
        ==> x IN frontier(convex hull s)`;;

let NOT_IN_INTERIOR_CONVEX_HULL = `!s x:real^N.
        FINITE s /\ CARD s <= dimindex(:N) + 1 /\ x IN s
        ==> ~(x IN interior(convex hull s))`;;

let INTERIOR_CONVEX_HULL_EQ_EMPTY = `!s:real^N->bool.
        s HAS_SIZE (dimindex(:N) + 1)
        ==> (interior(convex hull s) = {} <=> affine_dependent s)`;;

(* ------------------------------------------------------------------------- *)
(* Similar things in special case (could use above as lemmas here instead).  *)
(* ------------------------------------------------------------------------- *)

let SIMPLEX_EXPLICIT = `!s:real^N->bool.
        FINITE s /\ ~(vec 0 IN s)
        ==> convex hull (vec 0 INSERT s) =
            { y | ?u. (!x. x IN s ==> &0 <= u x) /\
                      sum s u <= &1 /\
                      vsum s (\x. u x % x) = y}`;;

let STD_SIMPLEX = `convex hull (vec 0 INSERT { basis i | 1 <= i /\ i <= dimindex(:N)}) =
        {x:real^N | (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i) /\
                    sum (1..dimindex(:N)) (\i. x$i) <= &1 }`;;

let INTERIOR_STD_SIMPLEX = `interior
    (convex hull (vec 0 INSERT { basis i | 1 <= i /\ i <= dimindex(:N)})) =
        {x:real^N | (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < x$i) /\
                    sum (1..dimindex(:N)) (\i. x$i) < &1 }`;;

(* ------------------------------------------------------------------------- *)
(* Barycentres.                                                              *)
(* ------------------------------------------------------------------------- *)

let barycentre = new_definition
  `barycentre s =
     if FINITE s then vsum s (\x. inv(&(CARD s)) % x) else vec 0`;;

let BARYCENTRE_0 = `barycentre {} = vec 0`;;

let BARYCENTRE_1 = `!a:real^N. barycentre {a} = a`;;

let BARYCENTRE_2 = `!a b:real^N. barycentre {a,b} = midpoint(a,b)`;;

let BARYCENTRE_IN_RELATIVE_INTERIOR = `!s:real^N->bool.
        FINITE s /\ ~(s = {})
        ==> (barycentre s) IN relative_interior(convex hull s)`;;

let BARYCENTRE_IN_CONVEX_HULL = `!s:real^N->bool.
        FINITE s /\ ~(s = {}) ==> (barycentre s) IN (convex hull s)`;;

let BARYCENTRE_IN_AFFINE_HULL = `!s:real^N->bool.
        FINITE s /\ ~(s = {}) ==> (barycentre s) IN (affine hull s)`;;

let BARYCENTRE_TRANSLATION = `!a:real^N s.
        barycentre (IMAGE (\x. a + x) s) =
        (if FINITE s /\ ~(s = {}) then a else vec 0) + barycentre s`;;

add_translation_invariants [BARYCENTRE_TRANSLATION];;

let BARYCENTRE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> barycentre (IMAGE f s) = f(barycentre s)`;;

add_linear_invariants [BARYCENTRE_LINEAR_IMAGE];;

let BARYCENTRE_NOT_IN_SET = `!s:real^N->bool.
        ~affine_dependent s /\ ~(?a. s = {a}) ==> ~(barycentre s IN s)`;;

(* ------------------------------------------------------------------------- *)
(* Construction of regular polyhedra with given parameters.                  *)
(* ------------------------------------------------------------------------- *)

let REGULAR_POLYTOPE_DIST_BARYCENTRE = `!s:real^N->bool n r.
        s HAS_SIZE n /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> dist(x,y) = r)
        ==> !x. x IN s
                ==> dist(barycentre s,x) = sqrt((&n - &1) / (&2 * &n)) * r`;;

let REGULAR_POLYTOPE_EXISTS = `!r s:real^N->bool n.
       &n <= aff_dim s + &1 /\ &0 < r
       ==> ?k. k HAS_SIZE n /\ ~affine_dependent k /\ k SUBSET affine hull s /\
               (!x y. x IN k /\ y IN k /\ ~(x = y) ==> dist(x,y) = r)`;;

let REGULAR_POLYTOPE_WITH_BARYCENTRE_EXISTS_ALT = `!r s:real^N->bool a n.
      &n <= aff_dim s + &1 /\ &0 < r /\ a IN affine hull s /\ ~(n = 0)
      ==> ?k. k HAS_SIZE n /\ ~affine_dependent k /\ k SUBSET affine hull s /\
              barycentre k = a /\
              (!x y. x IN k /\ y IN k /\ ~(x = y) ==> dist(x,y) = r) /\
              (!x. x IN k ==> dist(a,x) = sqrt((&n - &1) / (&2 * &n)) * r)`;;

let REGULAR_POLYTOPE_WITH_BARYCENTRE_EXISTS = `!r s:real^N->bool a n.
      &n <= aff_dim s + &1 /\ &0 < r /\ a IN affine hull s /\ 1 < n
      ==> ?k. k HAS_SIZE n /\ ~affine_dependent k /\ k SUBSET affine hull s /\
              barycentre k = a /\
              (!x. x IN k ==> dist(a,x) = r) /\
              (!x y. x IN k /\ y IN k /\ ~(x = y)
                     ==> dist(x,y) = sqrt((&2 * &n) / (&n - &1)) * r)`;;

(* ------------------------------------------------------------------------- *)
(* Continuity of convex functions and related results.                       *)
(* ------------------------------------------------------------------------- *)

let CONVEX_IMP_LOCALLY_BOUNDED = `!f s a:real^N.
        f convex_on s /\ a IN relative_interior s
        ==> ?e B. &0 < e /\ &0 < B /\
                  cball(a,e) INTER affine hull s SUBSET s /\
                  !x. x IN cball(a,e) INTER affine hull s ==> abs(f x) <= B`;;

let CONVEX_IMP_LOCALLY_LIPSCHITZ = `!f s a:real^N.
        f convex_on s /\ a IN relative_interior s
        ==> ?e B. &0 < e /\ &0 < B /\
                  cball(a,e) INTER affine hull s SUBSET s /\
                  !x y. x IN cball(a,e) INTER affine hull s /\
                        y IN cball(a,e) INTER affine hull s
                        ==> abs(f x - f y) <= B * norm(x - y)`;;

let CONVEX_ON_CONTINUOUS_ON_RELATIVE_INTERIOR = `!f s:real^N->bool.
        f convex_on s ==> lift o f continuous_on relative_interior s`;;

let CONVEX_ON_CONTINUOUS = `!f s:real^N->bool. open s /\ f convex_on s ==> lift o f continuous_on s`;;

let CONVEX_IMP_LIPSCHITZ = `!f:real^N->real s t.
        f convex_on t /\ compact s /\ s SUBSET relative_interior t
        ==> ?B. &0 < B /\
                !x y. x IN s /\ y IN s ==> abs(f x - f y) <= B * norm(x - y)`;;

let CONVEX_BOUNDS_LEMMA = `!f x:real^N e.
        f convex_on cball(x,e) /\
        (!y. y IN cball(x,e) ==> f(y) <= b)
        ==> !y. y IN cball(x,e) ==> abs(f(y)) <= b + &2 * abs(f(x))`;;

let CONVEX_IMP_BOUNDED_ON_INTERVAL = `!f:real^1->real a b.
        f convex_on interval[a,b]
        ==> ?B. &0 < B /\ !x. x IN interval[a,b] ==> abs(f x) <= B`;;

(* ------------------------------------------------------------------------- *)
(* A convex function on R^1 is "piecewise monotone" in this precise sense.   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_IMP_PIECEWISE_MONOTONE = `!f s. f convex_on s /\ is_interval s
         ==> (!x y. x IN interior s /\ y IN interior s /\ drop x <= drop y
                    ==> f x <= f y) \/
             (!x y. x IN interior s /\ y IN interior s /\ drop x <= drop y
                    ==> f y <= f x) \/
             ?a. a IN interior s /\
                 (!x y. x IN s /\ y IN s /\
                        drop x <= drop y /\ drop y <= drop a
                        ==> f y <= f x) /\
                 (!x y. x IN s /\ y IN s /\
                        drop a <= drop x /\ drop x <= drop y
                        ==> f x <= f y)`;;
