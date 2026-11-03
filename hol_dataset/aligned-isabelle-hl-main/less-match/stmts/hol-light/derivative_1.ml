(* ========================================================================= *)
(* Complex analysis.                                                         *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* (c) Copyright, Marco Maggesi, Graziano Gentili and Gianni Ciolli, 2008.   *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Library/floor.ml";;
needs "Library/iter.ml";;
needs "Multivariate/integration.ml";;
needs "Multivariate/complexes.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Some toplogical facts formulated for the complex numbers.                 *)
(* ------------------------------------------------------------------------- *)

let CLOSED_HALFSPACE_RE_GE = `!b. closed {z | Re(z) >= b}`;;

let CLOSED_HALFSPACE_RE_LE = `!b. closed {z | Re(z) <= b}`;;

let CLOSED_HALFSPACE_RE_EQ = `!b. closed {z | Re(z) = b}`;;

let OPEN_HALFSPACE_RE_GT = `!b. open {z | Re(z) > b}`;;

let OPEN_HALFSPACE_RE_LT = `!b. open {z | Re(z) < b}`;;

let CLOSED_HALFSPACE_IM_GE = `!b. closed {z | Im(z) >= b}`;;

let CLOSED_HALFSPACE_IM_LE = `!b. closed {z | Im(z) <= b}`;;

let CLOSED_HALFSPACE_IM_EQ = `!b. closed {z | Im(z) = b}`;;

let OPEN_HALFSPACE_IM_GT = `!b. open {z | Im(z) > b}`;;

let OPEN_HALFSPACE_IM_LT = `!b. open {z | Im(z) < b}`;;

let CONVEX_HALFSPACE_RE_GE = `!b. convex {z | Re(z) >= b}`;;

let CONVEX_HALFSPACE_RE_GT = `!b. convex {z | Re(z) > b}`;;

let CONVEX_HALFSPACE_RE_LE = `!b. convex {z | Re(z) <= b}`;;

let CONVEX_HALFSPACE_RE_LT = `!b. convex {z | Re(z) < b}`;;

let CONVEX_HALFSPACE_IM_GE = `!b. convex {z | Im(z) >= b}`;;

let CONVEX_HALFSPACE_IM_GT = `!b. convex {z | Im(z) > b}`;;

let CONVEX_HALFSPACE_IM_LE = `!b. convex {z | Im(z) <= b}`;;

let CONVEX_HALFSPACE_IM_LT = `!b. convex {z | Im(z) < b}`;;

let CONVEX_HALFSPACE_RE_SGN = `!b. convex {z | real_sgn(Re z) = b}`;;

let CONVEX_HALFSPACE_IM_SGN = `!b. convex {z | real_sgn(Im z) = b}`;;

let COMPLEX_IN_BALL_0 = `!v r. v IN ball(Cx(&0),r) <=> norm v < r`;;

let COMPLEX_IN_CBALL_0 = `!v r. v IN cball(Cx(&0),r) <=> norm v <= r`;;

let COMPLEX_IN_SPHERE_0 = `!v r. v IN sphere(Cx(&0),r) <=> norm v = r`;;

let IN_BALL_RE = `!x z e. x IN ball(z,e) ==> abs(Re(x) - Re(z)) < e`;;

let IN_BALL_IM = `!x z e. x IN ball(z,e) ==> abs(Im(x) - Im(z)) < e`;;

let IN_CBALL_RE = `!x z e. x IN cball(z,e) ==> abs(Re(x) - Re(z)) <= e`;;

let IN_CBALL_IM = `!x z e. x IN cball(z,e) ==> abs(Im(x) - Im(z)) <= e`;;

let CLOSED_REAL_SET = `closed {z | real z}`;;

let CLOSED_REAL = `closed real`;;

let UNBOUNDED_REAL = `~(bounded real)`;;

let CONNECTED_REAL = `connected real`;;

let PATH_CONNECTED_REAL = `path_connected real`;;

let TRIVIAL_LIMIT_WITHIN_REAL = `!z. trivial_limit (at z within real) <=> ~(real z)`;;

(* ------------------------------------------------------------------------- *)
(* Complex-specific uniform limit composition theorems.                      *)
(* ------------------------------------------------------------------------- *)

let UNIFORM_LIM_COMPLEX_MUL = `!net:(A)net P f g l m b1 b2.
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        eventually (\x. !n. P n ==> norm(m n) <= b2) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(f n x * g n x - l n * m n) < e)
                     net`;;

let UNIFORM_LIM_COMPLEX_INV = `!net:(A)net P f l b.
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        &0 < b /\ eventually (\x. !n. P n ==> b <= norm(l n)) net
        ==> !e. &0 < e
                ==> eventually
                    (\x. !n. P n ==> norm(inv(f n x) - inv(l n)) < e) net`;;

let UNIFORM_LIM_COMPLEX_DIV = `!net:(A)net P f g l m b1 b2.
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        &0 < b2 /\ eventually (\x. !n. P n ==> b2 <= norm(m n)) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(f n x / g n x - l n / m n) < e)
                     net`;;

(* ------------------------------------------------------------------------- *)
(* The usual non-uniform versions.                                           *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPLEX_MUL = `!net:(A)net f g l m.
         (f --> l) net /\ (g --> m) net ==> ((\x. f x * g x) --> l * m) net`;;

let LIM_COMPLEX_INV = `!net:(A)net f g l m.
         (f --> l) net /\ ~(l = Cx(&0)) ==> ((\x. inv(f x)) --> inv(l)) net`;;

let LIM_COMPLEX_DIV = `!net:(A)net f g l m.
         (f --> l) net /\ (g --> m) net /\ ~(m = Cx(&0))
         ==> ((\x. f x / g x) --> l / m) net`;;

let LIM_COMPLEX_POW = `!net:(A)net f l n.
         (f --> l) net ==> ((\x. f(x) pow n) --> l pow n) net`;;

let LIM_COMPLEX_LMUL = `!f l c. (f --> l) net ==> ((\x. c * f x) --> c * l) net`;;

let LIM_COMPLEX_RMUL = `!f l c. (f --> l) net ==> ((\x. f x * c) --> l * c) net`;;

(* ------------------------------------------------------------------------- *)
(* Mapping real limits between C and R^1.                                    *)
(* ------------------------------------------------------------------------- *)

let LIM_CX_LIFT = `!net f l.
     ((\x. Cx(f x)) --> Cx l) net <=> ((\x. lift(f x)) --> lift l) net`;;

let SERIES_CX_LIFT = `!f s x.
     ((\x. Cx(f x)) sums (Cx x)) s <=> ((\x. lift(f x)) sums (lift x)) s`;;

let LIM_INFINITY_POSINFINITY_CX = `!f l:real^N. (f --> l) at_infinity ==> ((f o Cx) --> l) at_posinfinity`;;

(* ------------------------------------------------------------------------- *)
(* Special cases of null limits.                                             *)
(* ------------------------------------------------------------------------- *)

let LIM_NULL_COMPLEX = `!net f. (f --> l) net <=> ((\x. f x - l) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_NORM = `!net f. (f --> Cx(&0)) net <=> ((\x. Cx(norm(f x))) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_NEG = `!net f. (f --> Cx(&0)) net ==> ((\x. --(f x)) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_ADD = `!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x + g x) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_SUB = `!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x - g x) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_MUL = `!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x * g x) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_LMUL = `!net f c. (f --> Cx(&0)) net ==> ((\x. c * f x) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_RMUL = `!net f c. (f --> Cx(&0)) net ==> ((\x. f x * c) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_POW = `!net f n. (f --> Cx(&0)) net /\ ~(n = 0)
             ==> ((\x. (f x) pow n) --> Cx(&0)) net`;;

let SUMS_COMPLEX_0 = `!f s. (!n. n IN s ==> f n = Cx(&0)) ==> (f sums Cx(&0)) s`;;

let LIM_NULL_COMPLEX_RMUL_BOUNDED = `!net f g B.
        (f --> Cx(&0)) net /\
        eventually (\a. f a = Cx(&0) \/ norm(g a) <= B) net
        ==> ((\z. f(z) * g(z)) --> Cx(&0)) net`;;

let LIM_NULL_COMPLEX_LMUL_BOUNDED = `!net f g B.
        eventually (\a. norm(f a) <= B \/ g a = Cx(&0)) net /\
        (g --> Cx(&0)) net
        ==> ((\z. f(z) * g(z)) --> Cx(&0)) net`;;

(* ------------------------------------------------------------------------- *)
(* Bound results for real and imaginary components of limits.                *)
(* ------------------------------------------------------------------------- *)

let LIM_RE_UBOUND = `!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. Re(f x) <= b) net
        ==> Re(l) <= b`;;

let LIM_RE_LBOUND = `!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= Re(f x)) net
        ==> b <= Re(l)`;;

let LIM_IM_UBOUND = `!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. Im(f x) <= b) net
        ==> Im(l) <= b`;;

let LIM_IM_LBOUND = `!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= Im(f x)) net
        ==> b <= Im(l)`;;

(* ------------------------------------------------------------------------- *)
(* Case analysis for limit of reciprocal of a function. This can be true     *)
(* degenerately, and it's a bit tiresome to show otherwise that it means     *)
(* what you expect.                                                          *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPLEX_INV_NONDEGENERATE = `!f:real^N->complex s a l.
        2 <= dimindex(:N) /\
        a IN s /\ open s /\
        f continuous_on (s DELETE a) /\
        ((inv o f) --> l) (at a)
        ==> ?t. open t /\ t SUBSET s /\
                ((!x. x IN t DELETE a ==> f x = Cx(&0)) /\ l = Cx(&0) \/
                 (!x. x IN t DELETE a ==> ~(f x = Cx(&0))))`;;

(* ------------------------------------------------------------------------- *)
(* Multiplication of complex series.                                         *)
(* ------------------------------------------------------------------------- *)

let SERIES_COMPLEX_LMUL = `!f l c s. (f sums l) s ==> ((\x. c * f x) sums c * l) s`;;

let SERIES_COMPLEX_RMUL = `!f l c s. (f sums l) s ==> ((\x. f x * c) sums l * c) s`;;

let SERIES_COMPLEX_DIV = `!f l c s. (f sums l) s ==> ((\x. f x / c) sums (l / c)) s`;;

let SUMMABLE_COMPLEX_LMUL = `!f c s. summable s f ==> summable s (\x. c * f x)`;;

let SUMMABLE_COMPLEX_RMUL = `!f c s. summable s f ==> summable s (\x. f x * c)`;;

let SUMMABLE_COMPLEX_DIV = `!f c s. summable s f ==> summable s (\x. f x / c)`;;

let SERIES_COMPLEX_MUL = `!x y a b.
        (x sums a) (from 0) /\ (y sums b) (from 0) /\
        (summable (from 0) (\n. lift(norm(x n))) \/
         summable (from 0) (\n. lift(norm(y n))))
        ==> ((\n. vsum(0..n) (\i. x i * y(n - i))) sums (a * b))
            (from 0)`;;

let SERIES_COMPLEX_MUL_UNIQUE = `!x y a b c.
        (x sums a) (from 0) /\ (y sums b) (from 0) /\
        ((\n. vsum (0..n) (\i. x i * y(n - i))) sums c) (from 0)
        ==> a * b = c`;;

let SUMMABLE_COMPLEX_MUL_LEFT = `!x y m n p.
        summable (from m) (\n. lift(norm(x n))) /\ summable (from n) y
        ==> summable (from p) (\n. vsum(0..n) (\i. x i * y(n - i)))`;;

let SUMMABLE_COMPLEX_MUL_RIGHT = `!x y m n p.
        summable (from m) x /\ summable (from n) (\n. lift(norm(y n)))
        ==> summable (from p) (\n. vsum(0..n) (\i. x i * y(n - i)))`;;

(* ------------------------------------------------------------------------- *)
(* Complex-specific continuity closures.                                     *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_COMPLEX_MUL = `!net f g.
    f continuous net /\ g continuous net ==> (\x. f(x) * g(x)) continuous net`;;

let CONTINUOUS_COMPLEX_LMUL = `!c f net. f continuous net ==> (\x. c * f x) continuous net`;;

let CONTINUOUS_COMPLEX_RMUL = `!c f net. f continuous net ==> (\x. f x * c) continuous net`;;

let CONTINUOUS_COMPLEX_INV = `!net f.
    f continuous net /\ ~(f(netlimit net) = Cx(&0))
    ==> (\x. inv(f x)) continuous net`;;

let CONTINUOUS_COMPLEX_DIV = `!net f g.
    f continuous net /\ g continuous net /\ ~(g(netlimit net) = Cx(&0))
    ==> (\x. f(x) / g(x)) continuous net`;;

let CONTINUOUS_COMPLEX_POW = `!net f n. f continuous net ==> (\x. f(x) pow n) continuous net`;;

let CONTINUOUS_CPRODUCT = `!(net:(real^N)net) f k:A->bool.
        FINITE k /\
        (!i. i IN k ==> f i continuous net)
        ==> (\z. cproduct k (\i. f i z)) continuous net`;;

(* ------------------------------------------------------------------------- *)
(* Write away the netlimit, which is otherwise a bit tedious.                *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_COMPLEX_INV_WITHIN = `!f s a.
    f continuous (at a within s) /\ ~(f a = Cx(&0))
    ==> (\x. inv(f x)) continuous (at a within s)`;;

let CONTINUOUS_COMPLEX_INV_AT = `!f a.
    f continuous (at a) /\ ~(f a = Cx(&0))
    ==> (\x. inv(f x)) continuous (at a)`;;

let CONTINUOUS_COMPLEX_DIV_WITHIN = `!f g s a.
    f continuous (at a within s) /\ g continuous (at a within s) /\
    ~(g a = Cx(&0))
    ==> (\x. f x / g x) continuous (at a within s)`;;

let CONTINUOUS_COMPLEX_DIV_AT = `!f g a.
    f continuous at a /\ g continuous at a /\ ~(g a = Cx(&0))
    ==> (\x. f x / g x) continuous at a`;;

(* ------------------------------------------------------------------------- *)
(* Also prove "on" variants as needed.                                       *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_COMPLEX_MUL = `!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) * g(x)) continuous_on s`;;

let CONTINUOUS_ON_COMPLEX_LMUL = `!f:real^N->complex s. f continuous_on s ==> (\x. c * f(x)) continuous_on s`;;

let CONTINUOUS_ON_COMPLEX_RMUL = `!f:real^N->complex s. f continuous_on s ==> (\x. f(x) * c) continuous_on s`;;

let CONTINUOUS_ON_COMPLEX_INV = `!f:real^N->complex.
        f continuous_on s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> (\x. inv(f x)) continuous_on s`;;

let CONTINUOUS_ON_COMPLEX_DIV = `!f g s. f continuous_on s /\ g continuous_on s /\
           (!x. x IN s ==> ~(g x = Cx(&0)))
           ==> (\x. f(x) / g(x)) continuous_on s`;;

let CONTINUOUS_ON_COMPLEX_POW = `!f n s. f continuous_on s ==> (\x. f(x) pow n) continuous_on s`;;

let CONTINUOUS_ON_CPRODUCT = `!f k:A->bool s.
        FINITE k /\
        (!i. i IN k ==> f i continuous_on s)
        ==> (\z. cproduct k (\i. f i z)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* And also uniform versions.                                                *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_ON_COMPLEX_MUL = `!f g s:real^N->bool.
        f uniformly_continuous_on s /\ g uniformly_continuous_on s /\
        bounded(IMAGE f s) /\ bounded(IMAGE g s)
        ==> (\x. f(x) * g(x)) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_COMPLEX_LMUL = `!f c s:real^N->bool.
      f uniformly_continuous_on s ==> (\x. c * f x) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_COMPLEX_RMUL = `!f c s:real^N->bool.
      f uniformly_continuous_on s ==> (\x. f x * c) uniformly_continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Continuity prover (not just for complex numbers but with more for them).  *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_TAC =
  let ETA_THM = `f continuous net <=> (\x. f x) continuous net` in
  let ETA_TWEAK =
    GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] o SPEC_ALL in
  let tac_base =
    MATCH_ACCEPT_TAC CONTINUOUS_CONST ORELSE
    MATCH_ACCEPT_TAC CONTINUOUS_AT_ID ORELSE
    MATCH_ACCEPT_TAC CONTINUOUS_WITHIN_ID
  and tac_1 =
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_CMUL) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_NEG) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_COMPLEX_POW)
  and tac_2 =
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_ADD) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_SUB) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_COMPLEX_MUL)
  and tac_1' = MATCH_MP_TAC (ETA_TWEAK CONTINUOUS_COMPLEX_INV)
  and tac_2' = MATCH_MP_TAC (ETA_TWEAK CONTINUOUS_COMPLEX_DIV) in
  let rec CONTINUOUS_TAC gl =
   (tac_base ORELSE
    (tac_1 THEN CONTINUOUS_TAC) ORELSE
    (tac_2 THEN CONJ_TAC THEN CONTINUOUS_TAC) ORELSE
    (tac_1' THEN CONJ_TAC THENL
     [CONTINUOUS_TAC; REWRITE_TAC[NETLIMIT_AT; NETLIMIT_WITHIN]]) ORELSE
    (tac_2' THEN REPEAT CONJ_TAC THENL
     [CONTINUOUS_TAC; CONTINUOUS_TAC;
      REWRITE_TAC[NETLIMIT_AT; NETLIMIT_WITHIN]]) ORELSE
    ALL_TAC) gl in
  CONTINUOUS_TAC;;

(* ------------------------------------------------------------------------- *)
(* Hence a limit calculator                                                  *)
(* ------------------------------------------------------------------------- *)

let LIM_TAC =
  MATCH_MP_TAC LIM_CONTINUOUS THEN CONJ_TAC THENL
   [CONTINUOUS_TAC; REWRITE_TAC[NETLIMIT_AT; NETLIMIT_WITHIN]];;

(* ------------------------------------------------------------------------- *)
(* Continuity of the norm.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_CX_NORM = `!z:real^N. (\z. Cx(norm z)) continuous at z`;;

let CONTINUOUS_WITHIN_CX_NORM = `!z:real^N s. (\z. Cx(norm z)) continuous (at z within s)`;;

let CONTINUOUS_ON_CX_NORM = `!s. (\z. Cx(norm z)) continuous_on s`;;

let CONTINUOUS_AT_CX_DOT = `!c z:real^N. (\z. Cx(c dot z)) continuous at z`;;

let CONTINUOUS_WITHIN_CX_DOT = `!c z:real^N s. (\z. Cx(c dot z)) continuous (at z within s)`;;

let CONTINUOUS_ON_CX_DOT = `!s c:real^N. (\z. Cx(c dot z)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Continuity switching range between complex and real^1                     *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CX_DROP = `!net f. f continuous net ==> (\x. Cx(drop(f x))) continuous net`;;

let CONTINUOUS_ON_CX_DROP = `!f s. f continuous_on s ==> (\x. Cx(drop(f x))) continuous_on s`;;

let CONTINUOUS_CX_LIFT = `!f. (\x. Cx(f x)) continuous net <=> (\x. lift(f x)) continuous net`;;

let CONTINUOUS_ON_CX_LIFT = `!f s. (\x. Cx(f x)) continuous_on s <=> (\x. lift(f x)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Linearity and continuity of the components.                               *)
(* ------------------------------------------------------------------------- *)

let LINEAR_CX_RE = `linear(Cx o Re)`;;

let CONTINUOUS_AT_CX_RE = `!z. (Cx o Re) continuous at z`;;

let CONTINUOUS_ON_CX_RE = `!s. (Cx o Re) continuous_on s`;;

let LINEAR_CX_IM = `linear(Cx o Im)`;;

let CONTINUOUS_AT_CX_IM = `!z. (Cx o Im) continuous at z`;;

let CONTINUOUS_ON_CX_IM = `!s. (Cx o Im) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Complex differentiability.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_complex_derivative",(12,"right"));;
parse_as_infix ("complex_differentiable",(12,"right"));;
parse_as_infix ("holomorphic_on",(12,"right"));;

let has_complex_derivative = new_definition
 `(f has_complex_derivative f') net <=> (f has_derivative (\x. f' * x)) net`;;

let complex_differentiable = new_definition
 `f complex_differentiable net <=> ?f'. (f has_complex_derivative f') net`;;

let complex_derivative = new_definition
 `complex_derivative f x = @f'. (f has_complex_derivative f') (at x)`;;

let higher_complex_derivative = define
 `higher_complex_derivative 0 f = f /\
  (!n. higher_complex_derivative (SUC n) f =
                complex_derivative (higher_complex_derivative n f))`;;

let holomorphic_on = new_definition
 `f holomorphic_on s <=>
     !x. x IN s ==> ?f'. (f has_complex_derivative f') (at x within s)`;;

let HOLOMORPHIC_ON_EMPTY = `!f. f holomorphic_on {}`;;

let HOLOMORPHIC_ON_DIFFERENTIABLE = `!f s. f holomorphic_on s <=>
         !x. x IN s ==> f complex_differentiable (at x within s)`;;

let HOLOMORPHIC_ON_OPEN = `!f s. open s
         ==> (f holomorphic_on s <=>
              !x. x IN s ==> ?f'. (f has_complex_derivative f') (at x))`;;

let HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_WITHIN = `!f s x. f holomorphic_on s /\ x IN s
           ==> f complex_differentiable (at x within s)`;;

let HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT = `!f s x. f holomorphic_on s /\ open s /\ x IN s
           ==> f complex_differentiable (at x)`;;

let HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT = `!f f' x. (f has_complex_derivative f') (at x) ==> f continuous at x`;;

let HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN = `!f f' x s. (f has_complex_derivative f') (at x within s)
              ==> f continuous (at x within s)`;;

let COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE = `!net f. f complex_differentiable net ==> f differentiable net`;;

let COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT = `!f x. f complex_differentiable at x ==> f continuous at x`;;

let COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN = `!f x s. f complex_differentiable (at x within s)
           ==> f continuous (at x within s)`;;

let HOLOMORPHIC_ON_IMP_CONTINUOUS_ON = `!f s. f holomorphic_on s ==> f continuous_on s`;;

let HOLOMORPHIC_ON_SUBSET = `!f s t. f holomorphic_on s /\ t SUBSET s ==> f holomorphic_on t`;;

let HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET = `!f s t x. (f has_complex_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_complex_derivative f') (at x within t)`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_SUBSET = `!f s t. f complex_differentiable (at x within s) /\ t SUBSET s
           ==> f complex_differentiable (at x within t)`;;

let HAS_COMPLEX_DERIVATIVE_AT_WITHIN = `!f f' x s. (f has_complex_derivative f') (at x)
              ==> (f has_complex_derivative f') (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN = `!f f' a s.
         a IN s /\ open s
         ==> ((f has_complex_derivative f') (at a within s) <=>
              (f has_complex_derivative f') (at a))`;;

let COMPLEX_DIFFERENTIABLE_AT_WITHIN = `!f s z. f complex_differentiable (at z)
           ==> f complex_differentiable (at z within s)`;;

let HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN = `!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       (f has_complex_derivative f') (at x within s)
       ==> (g has_complex_derivative f') (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN = `!f g f' s z. open s /\ z IN s /\ (!w. w IN s ==> f w = g w) /\
                 (f has_complex_derivative f') (at z)
                 ==> (g has_complex_derivative f') (at z)`;;

let HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT = `!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> f x' = g x') /\
       (f has_complex_derivative f') (at x)
       ==> (g has_complex_derivative f') (at x)`;;

let HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT = `!f s.
        convex s /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x within s))
        ==> ?c. !x. x IN s ==> f(x) = c`;;

let HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE = `!f s c a.
        convex s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x within s))
        ==> !x. x IN s ==> f(x) = c`;;

let HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT = `!f s.
        open s /\ connected s /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x))
        ==> ?c. !x. x IN s ==> f(x) = c`;;

let HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_UNIQUE = `!f s c a.
        open s /\ connected s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x))
        ==> !x. x IN s ==> f(x) = c`;;

let COMPLEX_DIFF_CHAIN_WITHIN = `!f g f' g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at (f x) within (IMAGE f s))
        ==> ((g o f) has_complex_derivative (g' * f'))(at x within s)`;;

let COMPLEX_DIFF_CHAIN_AT = `!f g f' g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at (f x))
        ==> ((g o f) has_complex_derivative (g' * f')) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_CHAIN = `!P f g.
        (!x. P x ==> (g has_complex_derivative g'(x)) (at x))
        ==> (!x s. (f has_complex_derivative f') (at x within s) /\ P(f x)
                   ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                       (at x within s)) /\
            (!x. (f has_complex_derivative f') (at x) /\ P(f x)
                 ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                     (at x))`;;

let HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV = `!f g. (!x. (g has_complex_derivative g'(x)) (at x))
         ==> (!x s. (f has_complex_derivative f') (at x within s)
                    ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                        (at x within s)) /\
             (!x. (f has_complex_derivative f') (at x)
                  ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                      (at x))`;;

let COMPLEX_DERIVATIVE_UNIQUE_AT = `!f z f' f''.
        (f has_complex_derivative f') (at z) /\
        (f has_complex_derivative f'') (at z)
        ==> f' = f''`;;

let HIGHER_COMPLEX_DERIVATIVE_1 = `!f z. higher_complex_derivative 1 f z = complex_derivative f z`;;

(* ------------------------------------------------------------------------- *)
(* A more direct characterization.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_WITHIN = `!f s a. (f has_complex_derivative f') (at a within s) <=>
           ((\x. (f(x) - f(a)) / (x - a)) --> f') (at a within s)`;;

let HAS_COMPLEX_DERIVATIVE_AT = `!f a. (f has_complex_derivative f') (at a) <=>
         ((\x. (f(x) - f(a)) / (x - a)) --> f') (at a)`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetical combining theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_COMPLEX_CMUL = `!net c. ((\x. c * x) has_derivative (\x. c * x)) net`;;

let HAS_COMPLEX_DERIVATIVE_LINEAR = `!net c. ((\x. c * x) has_complex_derivative c) net`;;

let HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN = `!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. c * f(x)) has_complex_derivative (c * f')) (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_LMUL_AT = `!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. c * f(x)) has_complex_derivative (c * f')) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN = `!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. f(x) * c) has_complex_derivative (f' * c)) (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_RMUL_AT = `!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. f(x) * c) has_complex_derivative (f' * c)) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN = `!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. f(x) / c) has_complex_derivative (f' / c)) (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_CDIV_AT = `!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. f(x) / c) has_complex_derivative (f' / c)) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_ID = `!net. ((\x. x) has_complex_derivative Cx(&1)) net`;;

let HAS_COMPLEX_DERIVATIVE_CONST = `!c net. ((\x. c) has_complex_derivative Cx(&0)) net`;;

let HAS_COMPLEX_DERIVATIVE_NEG = `!f f' net. (f has_complex_derivative f') net
            ==> ((\x. --(f(x))) has_complex_derivative (--f')) net`;;

let HAS_COMPLEX_DERIVATIVE_ADD = `!f f' g g' net.
        (f has_complex_derivative f') net /\ (g has_complex_derivative g') net
        ==> ((\x. f(x) + g(x)) has_complex_derivative (f' + g')) net`;;

let HAS_COMPLEX_DERIVATIVE_SUB = `!f f' g g' net.
        (f has_complex_derivative f') net /\ (g has_complex_derivative g') net
        ==> ((\x. f(x) - g(x)) has_complex_derivative (f' - g')) net`;;

let HAS_COMPLEX_DERIVATIVE_MUL_WITHIN = `!f f' g g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at x within s)
        ==> ((\x. f(x) * g(x)) has_complex_derivative
             (f(x) * g' + f' * g(x))) (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_MUL_AT = `!f f' g g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at x)
        ==> ((\x. f(x) * g(x)) has_complex_derivative
             (f(x) * g' + f' * g(x))) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_POW_WITHIN = `!f f' x s n. (f has_complex_derivative f') (at x within s)
                ==> ((\x. f(x) pow n) has_complex_derivative
                     (Cx(&n) * f(x) pow (n - 1) * f')) (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_POW_AT = `!f f' x n. (f has_complex_derivative f') (at x)
              ==> ((\x. f(x) pow n) has_complex_derivative
                   (Cx(&n) * f(x) pow (n - 1) * f')) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_INV_BASIC = `!x. ~(x = Cx(&0))
         ==> ((inv) has_complex_derivative (--inv(x pow 2))) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_INV_WITHIN = `!f f' x s. (f has_complex_derivative f') (at x within s) /\
              ~(f x = Cx(&0))
              ==> ((\x. inv(f(x))) has_complex_derivative (--f' / f(x) pow 2))
                  (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_INV_AT = `!f f' x. (f has_complex_derivative f') (at x) /\
            ~(f x = Cx(&0))
            ==> ((\x. inv(f(x))) has_complex_derivative (--f' / f(x) pow 2))
                (at x)`;;

let HAS_COMPLEX_DERIVATIVE_DIV_WITHIN = `!f f' g g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at x within s) /\
        ~(g(x) = Cx(&0))
        ==> ((\x. f(x) / g(x)) has_complex_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_DIV_AT = `!f f' g g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at x) /\
        ~(g(x) = Cx(&0))
        ==> ((\x. f(x) / g(x)) has_complex_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (at x)`;;

let HAS_COMPLEX_DERIVATIVE_VSUM = `!f net s.
         FINITE s /\ (!a. a IN s ==> (f a has_complex_derivative f' a) net)
         ==> ((\x. vsum s (\a. f a x)) has_complex_derivative (vsum s f'))
             net`;;

(* ------------------------------------------------------------------------- *)
(* Same thing just for complex differentiability.                            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DIFFERENTIABLE_LINEAR = `(\z. c * z) complex_differentiable p`;;

let COMPLEX_DIFFERENTIABLE_CONST = `!c net. (\z. c) complex_differentiable net`;;

let COMPLEX_DIFFERENTIABLE_ID = `!net. (\z. z) complex_differentiable net`;;

let COMPLEX_DIFFERENTIABLE_NEG = `!f net.
        f complex_differentiable net
        ==> (\z. --(f z)) complex_differentiable net`;;

let COMPLEX_DIFFERENTIABLE_ADD = `!f g net.
        f complex_differentiable net /\
        g complex_differentiable net
        ==> (\z. f z + g z) complex_differentiable net`;;

let COMPLEX_DIFFERENTIABLE_SUB = `!f g net.
        f complex_differentiable net /\
        g complex_differentiable net
        ==> (\z. f z - g z) complex_differentiable net`;;

let COMPLEX_DIFFERENTIABLE_INV_WITHIN = `!f z s.
        f complex_differentiable (at z within s) /\ ~(f z = Cx(&0))
        ==> (\z. inv(f z)) complex_differentiable (at z within s)`;;

let COMPLEX_DIFFERENTIABLE_MUL_WITHIN = `!f g z s.
        f complex_differentiable (at z within s) /\
        g complex_differentiable (at z within s)
        ==> (\z. f z * g z) complex_differentiable (at z within s)`;;

let COMPLEX_DIFFERENTIABLE_DIV_WITHIN = `!f g z s.
        f complex_differentiable (at z within s) /\
        g complex_differentiable (at z within s) /\
        ~(g z = Cx(&0))
        ==> (\z. f z / g z) complex_differentiable (at z within s)`;;

let COMPLEX_DIFFERENTIABLE_POW_WITHIN = `!f n z s.
        f complex_differentiable (at z within s)
        ==> (\z. f z pow n) complex_differentiable (at z within s)`;;

let COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN = `!f k:A->bool z s.
        FINITE k /\
        (!i. i IN k ==> f i complex_differentiable (at z within s))
        ==> (\z. cproduct k (\i. f i z)) complex_differentiable
            (at z within s)`;;

let COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN = `!f g x s d.
        &0 < d /\
        x IN s /\
        (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
        f complex_differentiable (at x within s)
        ==> g complex_differentiable (at x within s)`;;

let HOLOMORPHIC_TRANSFORM = `!f g s. (!x. x IN s ==> f x = g x) /\ f holomorphic_on s
           ==> g holomorphic_on s`;;

let HOLOMORPHIC_EQ = `!f g s. (!x. x IN s ==> f x = g x)
           ==> (f holomorphic_on s <=> g holomorphic_on s)`;;

let COMPLEX_DIFFERENTIABLE_INV_AT = `!f z.
        f complex_differentiable at z /\ ~(f z = Cx(&0))
        ==> (\z. inv(f z)) complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_MUL_AT = `!f g z.
        f complex_differentiable at z /\
        g complex_differentiable at z
        ==> (\z. f z * g z) complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_DIV_AT = `!f g z.
        f complex_differentiable at z /\
        g complex_differentiable at z /\
        ~(g z = Cx(&0))
        ==> (\z. f z / g z) complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_POW_AT = `!f n z.
        f complex_differentiable at z
        ==> (\z. f z pow n) complex_differentiable at z`;;

let COMPLEX_DIFFERENTIABLE_CPRODUCT_AT = `!f k:A->bool z.
        FINITE k /\
        (!i. i IN k ==> f i complex_differentiable (at z))
        ==> (\z. cproduct k (\i. f i z)) complex_differentiable (at z)`;;

let COMPLEX_DIFFERENTIABLE_TRANSFORM_AT = `!f g x d.
        &0 < d /\
        (!x'. dist (x',x) < d ==> f x' = g x') /\
        f complex_differentiable at x
        ==> g complex_differentiable at x`;;

let COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN = `!f g x s.
         f complex_differentiable (at x within s) /\
         g complex_differentiable (at (f x) within IMAGE f s)
         ==> (g o f) complex_differentiable (at x within s)`;;

let COMPLEX_DIFFERENTIABLE_COMPOSE_AT = `!f g x.
         f complex_differentiable (at x) /\
         g complex_differentiable (at (f x))
         ==> (g o f) complex_differentiable (at x)`;;

let COMPLEX_DIFFERENTIABLE_WITHIN_OPEN = `!f a s.
        a IN s /\ open s
        ==> (f complex_differentiable at a within s <=>
             f complex_differentiable at a)`;;

(* ------------------------------------------------------------------------- *)
(* Same again for being holomorphic on a set.                                *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_LINEAR = `!s c. (\w. c * w) holomorphic_on s`;;

let HOLOMORPHIC_ON_CONST = `!c s. (\z. c) holomorphic_on s`;;

let HOLOMORPHIC_ON_ID = `!s. (\z. z) holomorphic_on s`;;

let HOLOMORPHIC_ON_COMPOSE = `!f g s. f holomorphic_on s /\ g holomorphic_on (IMAGE f s)
           ==> (g o f) holomorphic_on s`;;

let HOLOMORPHIC_ON_NEG = `!f s. f holomorphic_on s ==> (\z. --(f z)) holomorphic_on s`;;

let HOLOMORPHIC_ON_ADD = `!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z + g z) holomorphic_on s`;;

let HOLOMORPHIC_ON_SUB = `!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z - g z) holomorphic_on s`;;

let HOLOMORPHIC_ON_MUL = `!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z * g z) holomorphic_on s`;;

let HOLOMORPHIC_ON_LMUL = `!f c s. f holomorphic_on s ==> (\x. c * f x) holomorphic_on s`;;

let HOLOMORPHIC_ON_RMUL = `!f c s. f holomorphic_on s ==> (\x. f x * c) holomorphic_on s`;;

let HOLOMORPHIC_ON_INV = `!f s. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
         ==> (\z. inv(f z)) holomorphic_on s`;;

let HOLOMORPHIC_ON_DIV = `!f g s.
        f holomorphic_on s /\ g holomorphic_on s /\
        (!z. z IN s ==> ~(g z = Cx(&0)))
        ==> (\z. f z / g z) holomorphic_on s`;;

let HOLOMORPHIC_ON_POW = `!f s n. f holomorphic_on s ==> (\z. (f z) pow n) holomorphic_on s`;;

let HOLOMORPHIC_ON_VSUM = `!f s k. FINITE k /\ (!a. a IN k ==> (f a) holomorphic_on s)
           ==> (\x. vsum k (\a. f a x)) holomorphic_on s`;;

let HOLOMORPHIC_ON_CPRODUCT = `!f k:A->bool s.
        FINITE k /\
        (!i. i IN k ==> f i holomorphic_on s)
        ==> (\z. cproduct k (\i. f i z)) holomorphic_on s`;;

let HOLOMORPHIC_ON_COMPOSE_GEN = `!f g s t. f holomorphic_on s /\ g holomorphic_on t /\
             (!z. z IN s ==> f z IN t)
             ==>  g o f holomorphic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Same again for the actual derivative function.                            *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_DERIVATIVE = `!f f' x. (f has_complex_derivative f') (at x)
                ==> complex_derivative f x = f'`;;

let HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE = `!f x. (f has_complex_derivative (complex_derivative f x)) (at x) <=>
         f complex_differentiable at x`;;

let COMPLEX_DERIVATIVE_CHAIN = `!f g z. f complex_differentiable at z /\ g complex_differentiable at (f z)
           ==> complex_derivative (g o f) z =
               complex_derivative g (f z) * complex_derivative f z`;;

let COMPLEX_DERIVATIVE_LINEAR = `!c. complex_derivative (\w. c * w) = \z. c`;;

let COMPLEX_DERIVATIVE_ID = `complex_derivative (\w.w) = \z. Cx(&1)`;;

let COMPLEX_DERIVATIVE_CONST = `!c. complex_derivative (\w.c) = \z. Cx(&0)`;;

let COMPLEX_DERIVATIVE_ADD = `!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w + g w) z =
               complex_derivative f z + complex_derivative g z`;;

let COMPLEX_DERIVATIVE_SUB = `!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w - g w) z =
               complex_derivative f z - complex_derivative g z`;;

let COMPLEX_DERIVATIVE_MUL = `!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w * g w) z =
               f z * complex_derivative g z + complex_derivative f z * g z`;;

let COMPLEX_DERIVATIVE_LMUL = `!f c z. f complex_differentiable at z
             ==> complex_derivative (\w. c * f w) z =
                 c * complex_derivative f z`;;

let COMPLEX_DERIVATIVE_RMUL = `!f c z. f complex_differentiable at z
           ==> complex_derivative (\w. f w * c) z =
               complex_derivative f z * c`;;

let COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN = `!f g s z. open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s /\
             (!w. w IN s ==> f w = g w)
             ==> complex_derivative f z = complex_derivative g z`;;

let COMPLEX_DERIVATIVE_COMPOSE_LINEAR = `!f c z. f complex_differentiable at (c * z)
           ==> complex_derivative (\w. f (c * w)) z =
               c * complex_derivative f (c * z)`;;

(* ------------------------------------------------------------------------- *)
(* Caratheodory characterization.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CARATHEODORY_AT = `!f f' z.
        (f has_complex_derivative f') (at z) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g continuous at z /\ g(z) = f'`;;

let HAS_COMPLEX_DERIVATIVE_CARATHEODORY_WITHIN = `!f f' z s.
        (f has_complex_derivative f') (at z within s) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g continuous (at z within s) /\ g(z) = f'`;;

let COMPLEX_DIFFERENTIABLE_CARATHEODORY_AT = `!f z. f complex_differentiable at z <=>
         ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\ g continuous at z`;;

let COMPLEX_DIFFERENTIABLE_CARATHEODORY_WITHIN = `!f z s.
      f complex_differentiable (at z within s) <=>
      ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\ g continuous (at z within s)`;;

(* ------------------------------------------------------------------------- *)
(* A slightly stronger, more traditional notion of analyticity on a set.     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("analytic_on",(12,"right"));;

let analytic_on = new_definition
 `f analytic_on s <=>
      !x. x IN s ==> ?e. &0 < e /\ f holomorphic_on ball(x,e)`;;

let ANALYTIC_IMP_HOLOMORPHIC = `!f s. f analytic_on s ==> f holomorphic_on s`;;

let ANALYTIC_ON_OPEN = `!f s. open s ==> (f analytic_on s <=> f holomorphic_on s)`;;

let ANALYTIC_ON_IMP_DIFFERENTIABLE_AT = `!f s x. f analytic_on s /\ x IN s ==> f complex_differentiable (at x)`;;

let ANALYTIC_ON_SUBSET = `!f s t. f analytic_on s /\ t SUBSET s ==> f analytic_on t`;;

let ANALYTIC_ON_UNION = `!f s t. f analytic_on (s UNION t) <=> f analytic_on s /\ f analytic_on t`;;

let ANALYTIC_ON_UNIONS = `!f s. f analytic_on (UNIONS s) <=> (!t. t IN s ==> f analytic_on t)`;;

let ANALYTIC_ON_HOLOMORPHIC = `!f s. f analytic_on s <=> ?t. open t /\ s SUBSET t /\ f holomorphic_on t`;;

let ANALYTIC_ON_LINEAR = `!s c. (\w. c * w) analytic_on s`;;

let ANALYTIC_ON_CONST = `!c s. (\z. c) analytic_on s`;;

let ANALYTIC_ON_ID = `!s. (\z. z) analytic_on s`;;

let ANALYTIC_ON_COMPOSE = `!f g s. f analytic_on s /\ g analytic_on (IMAGE f s)
           ==> (g o f) analytic_on s`;;

let ANALYTIC_ON_COMPOSE_GEN = `!f g s t. f analytic_on s /\ g analytic_on t /\ (!z. z IN s ==> f z IN t)
             ==> g o f analytic_on s`;;

let ANALYTIC_ON_NEG = `!f s. f analytic_on s ==> (\z. --(f z)) analytic_on s`;;

let ANALYTIC_ON_ADD = `!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z + g z) analytic_on s`;;

let ANALYTIC_ON_SUB = `!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z - g z) analytic_on s`;;

let ANALYTIC_ON_MUL = `!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z * g z) analytic_on s`;;

let ANALYTIC_ON_INV = `!f s. f analytic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
         ==> (\z. inv(f z)) analytic_on s`;;

let ANALYTIC_ON_DIV = `!f g s.
        f analytic_on s /\ g analytic_on s /\
        (!z. z IN s ==> ~(g z = Cx(&0)))
        ==> (\z. f z / g z) analytic_on s`;;

let ANALYTIC_ON_POW = `!f s n. f analytic_on s ==> (\z. (f z) pow n) analytic_on s`;;

let ANALYTIC_ON_VSUM = `!f s k. FINITE k /\ (!a. a IN k ==> (f a) analytic_on s)
           ==> (\x. vsum k (\a. f a x)) analytic_on s`;;

(* ------------------------------------------------------------------------- *)
(* The case of analyticity at a point.                                       *)
(* ------------------------------------------------------------------------- *)

let ANALYTIC_AT_BALL = `!f z. f analytic_on {z} <=> ?e. &0<e /\ f holomorphic_on ball (z,e)`;;

let ANALYTIC_AT = `!f z. f analytic_on {z} <=> ?s. open s /\ z IN s /\ f holomorphic_on s`;;

let ANALYTIC_ON_ANALYTIC_AT = `!f s. f analytic_on s <=> !z. z IN s ==> f analytic_on {z}`;;

let ANALYTIC_AT_TWO = `!f g z. f analytic_on {z} /\ g analytic_on {z} <=>
    ?s. open s /\ z IN s /\ f holomorphic_on s /\ g holomorphic_on s`;;

let ANALYTIC_AT_ADD = `!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> (\w. f w + g w) analytic_on {z}`;;

let ANALYTIC_AT_SUB = `!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> (\w. f w - g w) analytic_on {z}`;;

let ANALYTIC_AT_MUL = `!f g z. f analytic_on {z} /\ g analytic_on {z}

     ==> (\w. f w * g w) analytic_on {z}`;;

let ANALYTIC_AT_POW = `!f n z. f analytic_on {z}
     ==> (\w. f w pow n) analytic_on {z}`;;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for derivative with analytic_at {z} hypotheses.        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DERIVATIVE_ADD_AT = `!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w + g w) z =
           complex_derivative f z + complex_derivative g z`;;

let COMPLEX_DERIVATIVE_SUB_AT = `!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w - g w) z =
           complex_derivative f z - complex_derivative g z`;;

let COMPLEX_DERIVATIVE_MUL_AT = `!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w * g w) z =
           f z * complex_derivative g z + complex_derivative f z * g z`;;

let COMPLEX_DERIVATIVE_LMUL_AT = `!f c z. f analytic_on {z}
    ==> complex_derivative (\w. c * f w) z = c * complex_derivative f z`;;

let COMPLEX_DERIVATIVE_RMUL_AT = `!f c z. f analytic_on {z}
    ==> complex_derivative (\w. f w * c) z = complex_derivative f z * c`;;

(* ------------------------------------------------------------------------- *)
(* A composition lemma for functions of mixed type.                          *)
(* ------------------------------------------------------------------------- *)

let HAS_VECTOR_DERIVATIVE_REAL_COMPLEX = `(f has_complex_derivative f') (at(Cx(drop a)))
   ==> ((\x. f(Cx(drop x))) has_vector_derivative f') (at a)`;;

let DIFFERENTIABLE_REAL_COMPLEX = `!f a. f complex_differentiable at (Cx(drop a))
         ==> (\x. f(Cx(drop x))) differentiable at a`;;

(* ------------------------------------------------------------------------- *)
(* Complex differentiation of sequences and series.                          *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_SEQUENCE = `!s f f' g'.
         convex s /\
         (!n x. x IN s
                ==> (f n has_complex_derivative f' n x) (at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s ==> norm (f' n x - g' x) <= e) /\
         (?x l. x IN s /\ ((\n. f n x) --> l) sequentially)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) --> g x) sequentially /\
                         (g has_complex_derivative g' x) (at x within s)`;;

let HAS_COMPLEX_DERIVATIVE_SERIES = `!s f f' g' k.
         convex s /\
         (!n x. x IN s
                ==> (f n has_complex_derivative f' n x) (at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s
                            ==> norm(vsum (k INTER (0..n)) (\i. f' i x) - g' x)
                                    <= e) /\
         (?x l. x IN s /\ ((\n. f n x) sums l) k)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) sums g x) k /\
                         (g has_complex_derivative g' x) (at x within s)`;;

(* ------------------------------------------------------------------------- *)
(* Bound theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DIFFERENTIABLE_BOUND = `!f f' s B.
        convex s /\
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s) /\
                        norm(f' x) <= B)
        ==> !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)`;;

(* ------------------------------------------------------------------------- *)
(* Inverse function theorem for complex derivatives.                         *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC = `!f g f' t y.
        (f has_complex_derivative f') (at (g y)) /\
        ~(f' = Cx(&0)) /\
        g continuous at y /\
        open t /\
        y IN t /\
        (!z. z IN t ==> f (g z) = z)
        ==> (g has_complex_derivative inv(f')) (at y)`;;

let HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG = `!f g f' s x.
         open s /\
         x IN s /\
         f continuous_on s /\
         (!x. x IN s ==> g (f x) = x) /\
         (f has_complex_derivative f') (at x) /\
         ~(f' = Cx(&0))
         ==> (g has_complex_derivative inv(f')) (at (f x))`;;

let HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X = `!f g f' s y.
        open s /\ (g y) IN s /\ f continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_complex_derivative f') (at (g y)) /\ ~(f' = Cx(&0)) /\
        f(g y) = y
        ==> (g has_complex_derivative inv(f')) (at y)`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy-Riemann condition and relation to conformal.                       *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_RIEMANN = `!f z. f complex_differentiable at z <=>
         f differentiable at z  /\
         (jacobian f (at z))$1$1 = (jacobian f (at z))$2$2 /\
         (jacobian f (at z))$1$2 = --((jacobian f (at z))$2$1)`;;

let COMPLEX_DERIVATIVE_JACOBIAN = `!f z.
        f complex_differentiable (at z)
        ==> complex_derivative f z =
            complex(jacobian f (at z)$1$1,jacobian f (at z)$2$1)`;;

let JACOBIAN_COMPLEX_DERIVATIVE = `!f f' z.
        (f has_complex_derivative f') (at z)
        ==> det(jacobian f (at z)) = norm(f') pow 2`;;

let COMPLEX_DIFFERENTIABLE_EQ_CONFORMAL = `!f z.
      f complex_differentiable at z /\ ~(complex_derivative f z = Cx(&0)) <=>
      f differentiable at z  /\
      ?a. ~(a = &0) /\ rotation_matrix (a %% jacobian f (at z))`;;

let HOLOMORPHIC_CONSTANT_RE = `!f s. open s /\ connected s /\
         f holomorphic_on s /\
         (?c. !z. z IN s ==> Re(f z) = c)
         ==> (?a. !z. z IN s ==> f z = a)`;;

let HOLOMORPHIC_CONSTANT_IM = `!f s. open s /\ connected s /\
         f holomorphic_on s /\
         (?c. !z. z IN s ==> Im(f z) = c)
         ==> (?a. !z. z IN s ==> f z = a)`;;

(* ------------------------------------------------------------------------- *)
(* Differentiation conversion.                                               *)
(* ------------------------------------------------------------------------- *)

let complex_differentiation_theorems = ref [];;

let add_complex_differentiation_theorems =
  let ETA_THM = 
   `(f has_complex_derivative f') net <=>
     ((\x. f x) has_complex_derivative f') net` in
  let ETA_TWEAK =
    PURE_REWRITE_RULE [IMP_CONJ] o
    GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] o
    SPEC_ALL in
  fun l -> complex_differentiation_theorems :=
              !complex_differentiation_theorems @ map ETA_TWEAK l;;

add_complex_differentiation_theorems
 [HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN; HAS_COMPLEX_DERIVATIVE_LMUL_AT;
  HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN; HAS_COMPLEX_DERIVATIVE_RMUL_AT;
  HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN; HAS_COMPLEX_DERIVATIVE_CDIV_AT;
  HAS_COMPLEX_DERIVATIVE_ID;
  HAS_COMPLEX_DERIVATIVE_CONST;
  HAS_COMPLEX_DERIVATIVE_NEG;
  HAS_COMPLEX_DERIVATIVE_ADD;
  HAS_COMPLEX_DERIVATIVE_SUB;
  HAS_COMPLEX_DERIVATIVE_MUL_WITHIN; HAS_COMPLEX_DERIVATIVE_MUL_AT;
  HAS_COMPLEX_DERIVATIVE_DIV_WITHIN; HAS_COMPLEX_DERIVATIVE_DIV_AT;
  HAS_COMPLEX_DERIVATIVE_POW_WITHIN; HAS_COMPLEX_DERIVATIVE_POW_AT;
  HAS_COMPLEX_DERIVATIVE_INV_WITHIN; HAS_COMPLEX_DERIVATIVE_INV_AT];;

let GEN_COMPLEX_DIFF_CONV ths =
  let partfn tm = let l,r = dest_comb tm in mk_pair(lhand l,r)
  and is_deriv = can (term_match [] `(f has_complex_derivative f') net`)
  and ths' =
   unions(mapfilter (CONJUNCTS o REWRITE_RULE[FORALL_AND_THM] o
                     MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV) ths) in
  let rec COMPLEX_DIFF_CONV tm =
    try tryfind (fun th -> PART_MATCH partfn th (partfn tm))
                (!complex_differentiation_theorems @ ths')
    with Failure _ ->
        let ith = tryfind (fun th ->
         PART_MATCH (partfn o repeat (snd o dest_imp)) th (partfn tm))
                    (!complex_differentiation_theorems @ ths') in
        COMPLEX_DIFF_ELIM ith
  and COMPLEX_DIFF_ELIM th =
    let tm = concl th in
    if not(is_imp tm) then th else
    let t = lhand tm in
    if not(is_deriv t) then UNDISCH th
    else COMPLEX_DIFF_ELIM (MATCH_MP th (COMPLEX_DIFF_CONV t)) in
  COMPLEX_DIFF_CONV;;

let COMPLEX_DIFF_CONV = GEN_COMPLEX_DIFF_CONV [];;

(* ------------------------------------------------------------------------- *)
(* Hence a tactic.                                                           *)
(* ------------------------------------------------------------------------- *)

let GEN_COMPLEX_DIFF_TAC ths =
  let pth = MESON[]
   `(f has_complex_derivative f') net
    ==> f' = g'
        ==> (f has_complex_derivative g') net` in
  W(fun (asl,w) -> let th = MATCH_MP pth (GEN_COMPLEX_DIFF_CONV ths w) in
       MATCH_MP_TAC(repeat (GEN_REWRITE_RULE I [IMP_IMP]) (DISCH_ALL th)));;

let COMPLEX_DIFF_TAC = GEN_COMPLEX_DIFF_TAC [];;

let COMPLEX_DIFFERENTIABLE_TAC =
  let DISCH_FIRST th = DISCH (hd(hyp th)) th in
  GEN_REWRITE_TAC I [complex_differentiable] THEN
  W(fun (asl,w) ->
        let th = COMPLEX_DIFF_CONV(snd(dest_exists w)) in
        let f' = rand(rator(concl th)) in
        EXISTS_TAC f' THEN
        (if hyp th = [] then MATCH_ACCEPT_TAC th else
         let th' = repeat (GEN_REWRITE_RULE I [IMP_IMP] o DISCH_FIRST)
                          (DISCH_FIRST th) in
         MATCH_MP_TAC th'));;

(* ------------------------------------------------------------------------- *)
(* A kind of complex Taylor theorem.                                         *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_TAYLOR = `!f n s B.
    convex s /\
    (!i x. x IN s /\ i <= n
           ==> ((f i) has_complex_derivative f (i + 1) x) (at x within s)) /\
    (!x. x IN s ==> norm(f (n + 1) x) <= B)
    ==> !w z. w IN s /\ z IN s
              ==> norm(f 0 z -
                       vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))))
                  <= B * norm(z - w) pow (n + 1) / &(FACT n)`;;

(* ------------------------------------------------------------------------- *)
(* The simplest special case.                                                *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_MVT = `!f f' s B.
        convex s /\
        (!z. z IN s ==> (f has_complex_derivative f' z) (at z within s)) /\
        (!z. z IN s ==> norm (f' z) <= B)
        ==> !w z. w IN s /\ z IN s ==> norm (f z - f w) <= B * norm (z - w)`;;

(* ------------------------------------------------------------------------- *)
(* Something more like the traditional MVT for real components.              *)
(* Could, perhaps should, sharpen this to derivatives inside the segment.    *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_MVT_LINE = `!f f' w z.
        (!u. u IN segment[w,z]
             ==> (f has_complex_derivative f'(u)) (at u))
        ==> ?u. u IN segment[w,z] /\ Re(f z) - Re(f w) = Re(f'(u) * (z - w))`;;

let COMPLEX_TAYLOR_MVT = `!f w z n.
    (!i x. x IN segment[w,z] /\ i <= n
           ==> ((f i) has_complex_derivative f (i + 1) x) (at x))
    ==> ?u. u IN segment[w,z] /\
            Re(f 0 z) =
            Re(vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))) +
               (f (n + 1) u * (z - u) pow n / Cx (&(FACT n))) * (z - w))`;;

(* ------------------------------------------------------------------------- *)
(* Further useful properties of complex conjugation.                         *)
(* ------------------------------------------------------------------------- *)

let LIM_CNJ = `!net f l. ((\x. cnj(f x)) --> cnj l) net <=> (f --> l) net`;;

let SUMS_CNJ = `!net f l. ((\x. cnj(f x)) sums cnj l) net <=> (f sums l) net`;;

let CONTINUOUS_WITHIN_CNJ = `!s z. cnj continuous (at z within s)`;;

let CONTINUOUS_AT_CNJ = `!z. cnj continuous (at z)`;;

let CONTINUOUS_ON_CNJ = `!s. cnj continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Some limit theorems about real part of real series etc.                   *)
(* ------------------------------------------------------------------------- *)

let REAL_LIM = `!net:(A)net f l.
        (f --> l) net /\ ~(trivial_limit net) /\
        eventually (\a. real(f a)) net
        ==> real l`;;

let REAL_LIM_SEQUENTIALLY = `!f l. (f --> l) sequentially /\ (?N. !n. n >= N ==> real(f n))
         ==> real l`;;

let REAL_SERIES = `!f l s. (f sums l) s /\ (!n. real(f n)) ==> real l`;;

(* ------------------------------------------------------------------------- *)
(* Often convenient to use comparison with real limit of complex type.       *)
(* ------------------------------------------------------------------------- *)

let LIM_NULL_COMPARISON_COMPLEX = `!net:(A)net f g.
        eventually (\x. norm(f x) <= norm(g x)) net /\
        (g --> Cx(&0)) net
        ==> (f --> Cx(&0)) net`;;

let LIM_NULL_COMPARISON_COMPLEX_RE = `!net:(A)net f g.
        eventually (\x. norm(f x) <= Re(g x)) net /\
        (g --> Cx(&0)) net
        ==> (f --> Cx(&0)) net`;;

let SERIES_COMPARISON_COMPLEX = `!f:num->real^N g s.
        summable s g /\
        (!n. n IN s ==> real(g n) /\ &0 <= Re(g n)) /\
        (?N. !n. n >= N /\ n IN s ==> norm(f n) <= norm(g n))
        ==> summable s f`;;

let SERIES_COMPARISON_UNIFORM_COMPLEX = `!f:A->num->real^N g P s.
        summable s g /\
        (!n. n IN s ==> real(g n) /\ &0 <= Re(g n)) /\
        (?N. !n x. N <= n /\ n IN s /\ P x ==> norm(f x n) <= norm(g n))
        ==> ?l. !e. &0 < e
                    ==> ?N. !n x. N <= n /\ P x
                                  ==> dist(vsum(s INTER (0..n)) (f x),l x) <
                                       e`;;

let SUMMABLE_SUBSET_COMPLEX = `!x s t. (!n. n IN s ==> real(x n) /\ &0 <= Re(x n)) /\
           summable s x /\ t SUBSET s
           ==> summable t x`;;

let SERIES_ABSCONV_IMP_CONV = `!x:num->real^N k. summable k (\n. Cx(norm(x n))) ==> summable k x`;;

(* ------------------------------------------------------------------------- *)
(* Complex-valued geometric series.                                          *)
(* ------------------------------------------------------------------------- *)

let SUMS_GP = `!n z. norm(z) < &1
         ==> ((\k. z pow k) sums (z pow n / (Cx(&1) - z))) (from n)`;;

let SUMMABLE_GP = `!z k. norm(z) < &1 ==> summable k (\n. z pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Complex version (the usual one) of Dirichlet convergence test.            *)
(* ------------------------------------------------------------------------- *)

let SERIES_DIRICHLET_COMPLEX_GEN = `!f g k m p l.
        bounded {vsum (m..n) f | n IN (:num)} /\
        summable (from p) (\n. Cx(norm(g(n + 1) - g(n)))) /\
        ((\n. vsum(1..n) f * g(n + 1)) --> l) sequentially
        ==> summable (from k) (\n. f(n) * g(n))`;;

let SERIES_DIRICHLET_COMPLEX = `!f g N k m.
        bounded {vsum (m..n) f | n IN (:num)} /\
        (!n. real(g n)) /\
        (!n. N <= n ==> Re(g(n + 1)) <= Re(g n)) /\
        (g --> Cx(&0)) sequentially
        ==> summable (from k) (\n. f(n) * g(n))`;;

(* ------------------------------------------------------------------------- *)
(* Versions with explicit bounds are sometimes useful.                       *)
(* ------------------------------------------------------------------------- *)

let SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT = `!f g B p.
        &0 < B /\ 1 <= p /\
        (!m n. p <= m ==> norm(vsum(m..n) f) <= B) /\
        (!n. p <= n ==> real(g n) /\ &0 <= Re(g n)) /\
        (!n. p <= n ==> Re(g(n + 1)) <= Re(g n))
        ==> !m n. p <= m
                  ==> norm(vsum(m..n) (\k. f k * g k)) <= &2 * B * norm(g m)`;;

let SERIES_DIRICHLET_COMPLEX_EXPLICIT = `!f g p q.
           1 <= p /\
           bounded {vsum (q..n) f | n IN (:num)} /\
           (!n. p <= n ==> real(g n) /\ &0 <= Re(g n)) /\
           (!n. p <= n ==> Re(g(n + 1)) <= Re(g n))
           ==> ?B. &0 < B /\
                   !m n. p <= m
                         ==> norm(vsum(m..n) (\k. f k * g k))
                                 <= B * norm(g m)`;;

(* ------------------------------------------------------------------------- *)
(* Integrals and complex multiplication.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPLEX_LMUL = `!f y i c. (f has_integral y) i ==> ((\x. c * f(x)) has_integral (c * y)) i`;;

let HAS_INTEGRAL_COMPLEX_RMUL = `!f y i c. (f has_integral y) i ==> ((\x. f(x) * c) has_integral (y * c)) i`;;

let HAS_INTEGRAL_COMPLEX_0 = `!s. ((\x. Cx(&0)) has_integral Cx(&0)) s`;;

let INTEGRABLE_COMPLEX_LMUL = `!f:real^N->complex s c.
        f integrable_on s ==> (\x. c * f x) integrable_on s`;;

let INTEGRABLE_COMPLEX_RMUL = `!f:real^N->complex s c.
        f integrable_on s ==> (\x. f x * c) integrable_on s`;;

let INTEGRABLE_COMPLEX_0 = `!s. (\x. Cx(&0)) integrable_on s`;;

let INTEGRABLE_COMPLEX_LMUL_EQ = `!f:real^N->complex s c.
        (\x. c * f x) integrable_on s <=> c = Cx(&0) \/ f integrable_on s`;;

let INTEGRABLE_COMPLEX_RMUL_EQ = `!f:real^N->complex s c.
        (\x. f x * c) integrable_on s <=> c = Cx(&0) \/ f integrable_on s`;;

let INTEGRAL_COMPLEX_LMUL = `!f:real^N->complex s c.
        f integrable_on s ==> integral s (\x. c * f x) = c * integral s f`;;

let INTEGRAL_COMPLEX_RMUL = `!f:real^N->complex s c.
        f integrable_on s ==> integral s (\x. f x * c) = integral s f * c`;;

let ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL = `!f s c. f absolutely_integrable_on s
           ==> (\x. c * f x) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_COMPLEX_RMUL = `!f s c. f absolutely_integrable_on s
           ==> (\x. f x * c) absolutely_integrable_on s`;;

let REAL_COMPLEX_INTEGRAL = `!f:real^N->complex s.
     f integrable_on s /\ (!x. x IN s ==> real(f x)) ==> real(integral s f)`;;

let INTEGRABLE_BOUNDED_VARIATION_COMPLEX_LMUL = `!f g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. g x * f x) integrable_on interval[a,b]`;;

let INTEGRABLE_BOUNDED_VARIATION_COMPLEX_RMUL = `!f g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. f x * g x) integrable_on interval[a,b]`;;

let HAS_BOUNDED_VARIATION_ON_COMPLEX_MUL = `!f g:real^1->complex s.
        f has_bounded_variation_on s /\
        g has_bounded_variation_on s /\
        is_interval s
        ==> (\x. f x * g x) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_COMPLEX_INV = `!f s e. f has_bounded_variation_on s /\
             &0 < e /\ (!x. x IN s ==> e <= norm(f x))
           ==> (\x. inv(f x)) has_bounded_variation_on s`;;

(* ------------------------------------------------------------------------- *)
(* Relations among convergence and absolute convergence for power series.    *)
(* ------------------------------------------------------------------------- *)

let ABEL_LEMMA = `!a M r r0.
        &0 <= r /\ r < r0 /\
        (!n. n IN k ==> norm(a n) * r0 pow n <= M)
        ==> summable k (\n. Cx(norm(a(n)) * r pow n))`;;

let POWER_SERIES_CONV_IMP_ABSCONV = `!a k w z.
        summable k (\n. a(n) * z pow n) /\ norm(w) < norm(z)
        ==> summable k (\n. Cx(norm(a(n) * w pow n)))`;;

let POWER_SERIES_CONV_IMP_ABSCONV_WEAK = `!a k w z.
        summable k (\n. a(n) * z pow n) /\ norm(w) < norm(z)
        ==> summable k (\n. Cx(norm(a(n))) * w pow n)`;;

let POWER_SERIES_RADIUS_OF_CONVERGENCE = `!a k w z.
           summable k (\n. a n * z pow n) /\ norm w < norm z
           ==> summable k (\n. a n * w pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Comparing sums and "integrals" via complex antiderivatives.               *)
(* ------------------------------------------------------------------------- *)

let SUM_INTEGRAL_UBOUND_INCREASING = `!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> Re(f(Cx x)) <= Re(f(Cx y)))
      ==> sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n + &1)) - g(Cx(&m)))`;;

let SUM_INTEGRAL_UBOUND_DECREASING = `!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n)) - g(Cx(&m - &1)))`;;

let SUM_INTEGRAL_LBOUND_INCREASING = `!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> Re(f(Cx x)) <= Re(f(Cx y)))
      ==> Re(g(Cx(&n)) - g(Cx(&m - &1))) <= sum(m..n) (\k. Re(f(Cx(&k))))`;;

let SUM_INTEGRAL_LBOUND_DECREASING = `!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> Re(g(Cx(&n + &1)) - g(Cx(&m))) <= sum(m..n) (\k. Re(f(Cx(&k))))`;;

let SUM_INTEGRAL_BOUNDS_INCREASING = `!f g m n.
         m <= n /\
         (!x. x IN segment[Cx(&m - &1),Cx (&n + &1)]
              ==> (g has_complex_derivative f x) (at x)) /\
         (!x y.
              &m - &1 <= x /\ x <= y /\ y <= &n + &1
              ==> Re(f(Cx x)) <= Re(f(Cx y)))
         ==> Re(g(Cx(&n)) - g(Cx(&m - &1))) <= sum(m..n) (\k. Re(f(Cx(&k)))) /\
             sum (m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n + &1)) - g(Cx(&m)))`;;

let SUM_INTEGRAL_BOUNDS_DECREASING = `!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n + &1
             ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> Re(g(Cx(&n + &1)) - g(Cx(&m))) <= sum(m..n) (\k. Re(f(Cx(&k)))) /\
          sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n)) - g(Cx(&m - &1)))`;;

(* ------------------------------------------------------------------------- *)
(* Relating different kinds of complex limits.                               *)
(* ------------------------------------------------------------------------- *)

let LIM_INFINITY_SEQUENTIALLY_COMPLEX = `!f l. (f --> l) at_infinity ==> ((\n. f(Cx(&n))) --> l) sequentially`;;

let LIM_AT_INFINITY_COMPLEX_0 = `!f l:real^N.
        (f --> l) at_infinity <=> ((f o inv) --> l) (at(Cx(&0)))`;;

let LIM_ZERO_INFINITY_COMPLEX = `!f l:real^N.
     ((\x. f(Cx(&1) / x)) --> l) (at (Cx(&0))) ==> (f --> l) at_infinity`;;

(* ------------------------------------------------------------------------- *)
(* Transforming complex limits to real ones.                                 *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPLEX_REAL = `!f g l m.
         eventually (\n. Re(g n) = f n) sequentially /\
         Re m = l /\
         (g --> m) sequentially
         ==> !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n - l) < e`;;

let LIM_COMPLEX_REAL_0 = `!f g. eventually (\n. Re(g n) = f n) sequentially /\
         (g --> Cx(&0)) sequentially
         ==> !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n) < e`;;

(* ------------------------------------------------------------------------- *)
(* Uniform convergence of power series in a "Stolz angle".                   *)
(* ------------------------------------------------------------------------- *)

let POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1 = `!M a s e.
        summable s a /\ &0 < M /\ &0 < e
        ==> eventually
             (\n. !z. norm(Cx(&1) - z) <= M * (&1 - norm z)
                      ==> norm(vsum (s INTER (0..n)) (\i. a i * z pow i) -
                               infsum s (\i. a i * z pow i)) < e)
             sequentially`;;

let POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ = `!M a w s e.
        summable s (\i. a i * w pow i) /\ &0 < M /\ &0 < e
        ==> eventually
             (\n. !z. norm(w - z) <= M * (norm w - norm z)
                      ==> norm(vsum (s INTER (0..n)) (\i. a i * z pow i) -
                               infsum s (\i. a i * z pow i)) < e)
             sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Hence continuity and the Abel limit theorem.                              *)
(* ------------------------------------------------------------------------- *)

let ABEL_POWER_SERIES_CONTINUOUS = `!M s a w.
        summable s (\i. a i * w pow i) /\ &0 < M
        ==> (\z. infsum s (\i. a i * z pow i)) continuous_on
            {z | norm(w - z) <= M * (norm w - norm z)}`;;

let ABEL_POWER_SERIES_CONTINUOUS_1 = `!M s a.
        summable s a /\ &0 < M
        ==> (\z. infsum s (\i. a i * z pow i)) continuous_on
            {z | norm(Cx(&1) - z) <= M * (&1 - norm z)}`;;

let ABEL_LIMIT_THEOREM = `!M s a w.
        summable s (\i. a i * w pow i) /\ &0 < M
        ==> (!z. norm(z) < norm(w) ==> summable s (\i. a i * z pow i)) /\
            ((\z. infsum s (\i. a i * z pow i)) -->
             infsum s  (\i. a i * w pow i))
            (at w within {z | norm(w - z) <= M * (norm w - norm z)})`;;

let ABEL_LIMIT_THEOREM_1 = `!M s a.
        summable s a /\ &0 < M
        ==> (!z. norm(z) < &1 ==> summable s (\i. a i * z pow i)) /\
            ((\z. infsum s (\i. a i * z pow i)) --> infsum s a)
            (at (Cx(&1)) within {z | norm(Cx(&1) - z) <= M * (&1 - norm z)})`;;

(* ------------------------------------------------------------------------- *)
(* Continuity and uniqueness of power series. These would drop easily out    *)
(* of later developments, but it seems nice to prove them without all the    *)
(* machinery of Cauchy's theorem etc.                                        *)
(* ------------------------------------------------------------------------- *)

let POWER_SERIES_CONTINUOUS = `!a k f z r.
        (!w. w IN ball(z,r) ==> ((\n. a n * (w - z) pow n) sums f w) k)
        ==> f continuous_on ball(z,r)`;;

let POWER_SERIES_LIMIT_POINT_OF_ZEROS = `!f c z k r s.
        &0 < r /\
        (!w. dist(w,z) < r ==> ((\i. c i * (w - z) pow i) sums f(w)) k) /\
        (!w. w IN s ==> f(w) = Cx(&0)) /\ z limit_point_of s
        ==> !i. i IN k ==> c(i) = Cx(&0)`;;

let POWER_SERIES_UNIQUE = `!f g c d k r s t z.
        &0 < r /\ &0 < s /\
        (!w. w IN ball(z,r) ==> ((\i. c i * (w - z) pow i) sums f w) k) /\
        (!w. w IN ball(z,s) ==> ((\i. d i * (w - z) pow i) sums g w) k) /\
        (!w. w IN t ==> f w = g w) /\
        z limit_point_of t
        ==> (!i. i IN k ==> c i = d i)`;;

(* ------------------------------------------------------------------------- *)
(* The only endomorphisms of C that are measurable or map R into R are the   *)
(* obvious ones. Hence such an automorphism is the identity or conjugation.  *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_COMPLEX_ENDOMORPHISM = `!f:complex->complex.
        f measurable_on (:complex) /\
        (!x y. f(x + y) = f x + f y) /\
        (!x y. f(x * y) = f x * f y) <=>
        f = (\x. Cx(&0)) \/ f = I \/ f = cnj`;;

let REAL_COMPLEX_ENDOMORPHISM = `!f:complex->complex.
        IMAGE f real SUBSET real /\
        (!x y. f(x + y) = f x + f y) /\
        (!x y. f(x * y) = f x * f y) <=>
        f = (\x. Cx(&0)) \/ f = I \/ f = cnj`;;
