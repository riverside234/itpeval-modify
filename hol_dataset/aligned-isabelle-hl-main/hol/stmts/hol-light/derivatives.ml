(* ========================================================================= *)
(* Multivariate calculus in Euclidean space.                                 *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(* ========================================================================= *)

needs "Multivariate/degree.ml";;

(* ------------------------------------------------------------------------- *)
(* Derivatives. The definition is slightly tricky since we make it work over *)
(* nets of a particular form. This lets us prove theorems generally and use  *)
(* "at a" or "at a within s" for restriction to a set (1-sided on R etc.)    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_derivative",(12,"right"));;

let has_derivative = new_definition
  `(f has_derivative f') net <=>
        linear f' /\
        ((\y. inv(norm(y - netlimit net)) %
              (f(y) -
               (f(netlimit net) + f'(y - netlimit net)))) --> vec 0) net`;;

(* ------------------------------------------------------------------------- *)
(* These are the only cases we'll care about, probably.                      *)
(* ------------------------------------------------------------------------- *)

let has_derivative_within = `!f:real^M->real^N f' x s.
    (f has_derivative f') (at x within s) <=>
         linear f' /\
         ((\y. inv(norm(y - x)) % (f(y) - (f(x) + f'(y - x)))) --> vec 0)
         (at x within s)`;;

let has_derivative_at = `!f:real^M->real^N f' x.
    (f has_derivative f') (at x) <=>
         linear f' /\
         ((\y. inv(norm(y - x)) % (f(y) - (f(x) + f'(y - x)))) --> vec 0)
         (at x)`;;

(* ------------------------------------------------------------------------- *)
(* More explicit epsilon-delta forms.                                        *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_WITHIN = `(f has_derivative f')(at x within s) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\
                         &0 < norm(x' - x) /\ norm(x' - x) < d
                         ==> norm(f(x') - f(x) - f'(x' - x)) /
                             norm(x' - x) < e`;;

let HAS_DERIVATIVE_AT = `(f has_derivative f')(at x) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. &0 < norm(x' - x) /\ norm(x' - x) < d
                         ==> norm(f(x') - f(x) - f'(x' - x)) /
                             norm(x' - x) < e`;;

let HAS_DERIVATIVE_AT_WITHIN = `!f x s. (f has_derivative f') (at x)
           ==> (f has_derivative f') (at x within s)`;;

let HAS_DERIVATIVE_WITHIN_OPEN = `!f f' a s.
         a IN s /\ open s
         ==> ((f has_derivative f') (at a within s) <=>
              (f has_derivative f') (at a))`;;

let HAS_DERIVATIVE_WITHIN_OPEN_IN = `!f:real^M->real^N f' a s u.
        a IN s /\ open_in (subtopology euclidean u) s
        ==> ((f has_derivative f') (at a within s) <=>
             (f has_derivative f') (at a within u))`;;

(* ------------------------------------------------------------------------- *)
(* Combining theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_LINEAR = `!f net. linear f ==> (f has_derivative f) net`;;

let HAS_DERIVATIVE_ID = `!net. ((\x. x) has_derivative (\h. h)) net`;;

let HAS_DERIVATIVE_CONST = `!c net. ((\x. c) has_derivative (\h. vec 0)) net`;;

let HAS_DERIVATIVE_LIFT_COMPONENT = `!net:(real^N)net. ((\x. lift(x$i)) has_derivative (\x. lift(x$i))) net`;;

let HAS_DERIVATIVE_CMUL = `!f f' net c. (f has_derivative f') net
                ==> ((\x. c % f(x)) has_derivative (\h. c % f'(h))) net`;;

let HAS_DERIVATIVE_CMUL_EQ = `!f f' net c.
       ~(c = &0)
       ==> (((\x. c % f(x)) has_derivative (\h. c % f'(h))) net <=>
            (f has_derivative f') net)`;;

let HAS_DERIVATIVE_NEG = `!f f' net. (f has_derivative f') net
            ==> ((\x. --(f(x))) has_derivative (\h. --(f'(h)))) net`;;

let HAS_DERIVATIVE_NEG_EQ = `!f f' net. ((\x. --(f(x))) has_derivative (\h. --(f'(h)))) net <=>
              (f has_derivative f') net`;;

let HAS_DERIVATIVE_ADD = `!f f' g g' net.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. f(x) + g(x)) has_derivative (\h. f'(h) + g'(h))) net`;;

let HAS_DERIVATIVE_SUB = `!f f' g g' net.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. f(x) - g(x)) has_derivative (\h. f'(h) - g'(h))) net`;;

let HAS_DERIVATIVE_VSUM = `!f net s.
     FINITE s /\
     (!a. a IN s ==> ((f a) has_derivative (f' a)) net)
     ==> ((\x. vsum s (\a. f a x)) has_derivative (\h. vsum s (\a. f' a h)))
          net`;;

let HAS_DERIVATIVE_VSUM_NUMSEG = `!f net m n.
     (!i. m <= i /\ i <= n ==> ((f i) has_derivative (f' i)) net)
     ==> ((\x. vsum (m..n) (\i. f i x)) has_derivative
          (\h. vsum (m..n) (\i. f' i h))) net`;;

let HAS_DERIVATIVE_COMPONENTWISE_WITHIN = `!f:real^M->real^N f' a s.
        (f has_derivative f') (at a within s) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift(f(x)$i)) has_derivative (\x. lift(f'(x)$i)))
                (at a within s)`;;

let HAS_DERIVATIVE_COMPONENTWISE_AT = `!f:real^M->real^N f' a.
        (f has_derivative f') (at a) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift(f(x)$i)) has_derivative (\x. lift(f'(x)$i))) (at a)`;;

let HAS_DERIVATIVE_PASTECART_EQ = `!net f:real^M->real^N g:real^M->real^P f' g'.
        ((\x. pastecart (f x) (g x)) has_derivative
        (\x. pastecart (f' x) (g' x))) net <=>
        (f has_derivative f') net /\ (g has_derivative g') net`;;

let HAS_DERIVATIVE_PASTECART = `!net f:real^M->real^N g:real^M->real^P f' g'.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. pastecart (f x) (g x)) has_derivative
             (\x. pastecart (f' x) (g' x))) net`;;

(* ------------------------------------------------------------------------- *)
(* Somewhat different results for derivative of scalar multiplier.           *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_VMUL_COMPONENT = `!c:real^M->real^N c' k v:real^P.
        1 <= k /\ k <= dimindex(:N) /\ (c has_derivative c') net
        ==> ((\x. c(x)$k % v) has_derivative (\x. c'(x)$k % v)) net`;;

let HAS_DERIVATIVE_VMUL_DROP = `!c c' v. (c has_derivative c') net
            ==> ((\x. drop(c(x)) % v) has_derivative (\x. drop(c'(x)) % v)) net`;;

let HAS_DERIVATIVE_LIFT_DOT = `!f:real^M->real^N f'.
     (f has_derivative f') net
     ==> ((\x. lift(v dot f(x))) has_derivative (\t. lift(v dot (f' t)))) net`;;

(* ------------------------------------------------------------------------- *)
(* Limit transformation for derivatives.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_TRANSFORM_WITHIN = `!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       (f has_derivative f') (at x within s)
       ==> (g has_derivative f') (at x within s)`;;

let HAS_DERIVATIVE_TRANSFORM_AT = `!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> f x' = g x') /\
       (f has_derivative f') (at x)
       ==> (g has_derivative f') (at x)`;;

let HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN = `!f g:real^M->real^N s x.
        open s /\ x IN s /\
        (!y. y IN s ==> f y = g y) /\
        (f has_derivative f') (at x)
        ==> (g has_derivative f') (at x)`;;

(* ------------------------------------------------------------------------- *)
(* Differentiability.                                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("differentiable",(12,"right"));;
parse_as_infix ("differentiable_on",(12,"right"));;

let differentiable = new_definition
  `f differentiable net <=> ?f'. (f has_derivative f') net`;;

let differentiable_on = new_definition
  `f differentiable_on s <=> !x. x IN s ==> f differentiable (at x within s)`;;

let HAS_DERIVATIVE_IMP_DIFFERENTIABLE = `!f f' net. (f has_derivative f') net ==> f differentiable net`;;

let DIFFERENTIABLE_AT_WITHIN = `!f s x. f differentiable (at x)
           ==> f differentiable (at x within s)`;;

let DIFFERENTIABLE_WITHIN_OPEN = `!f a s.
         a IN s /\ open s
         ==> (f differentiable (at a within s) <=> (f differentiable (at a)))`;;

let DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON = `!f s. (!x. x IN s ==> f differentiable at x) ==> f differentiable_on s`;;

let DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT = `!f s. open s ==> (f differentiable_on s <=>
                     !x. x IN s ==> f differentiable at x)`;;

let DIFFERENTIABLE_TRANSFORM_WITHIN = `!f g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       f differentiable (at x within s)
       ==> g differentiable (at x within s)`;;

let DIFFERENTIABLE_TRANSFORM_AT = `!f g x d.
       &0 < d /\
       (!x'. dist (x',x) < d ==> f x' = g x') /\
       f differentiable at x
       ==> g differentiable at x`;;

let DIFFERENTIABLE_ON_EQ = `!f g:real^M->real^N s.
        (!x. x IN s ==> f x = g x) /\ f differentiable_on s
        ==> g differentiable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Frechet derivative and Jacobian matrix.                                   *)
(* ------------------------------------------------------------------------- *)

let frechet_derivative = new_definition
  `frechet_derivative f net = @f'. (f has_derivative f') net`;;

let FRECHET_DERIVATIVE_WORKS = `!f net. f differentiable net <=>
           (f has_derivative (frechet_derivative f net)) net`;;

let LINEAR_FRECHET_DERIVATIVE = `!f net. f differentiable net ==> linear(frechet_derivative f net)`;;

let jacobian = new_definition
  `jacobian f net = matrix(frechet_derivative f net)`;;

let JACOBIAN_WORKS = `!f net. f differentiable net <=>
           (f has_derivative (\h. jacobian f net ** h)) net`;;

(* ------------------------------------------------------------------------- *)
(* Differentiability implies continuity.                                     *)
(* ------------------------------------------------------------------------- *)

let LIM_MUL_NORM_WITHIN = `!f a s. (f --> vec 0) (at a within s)
           ==> ((\x. norm(x - a) % f(x)) --> vec 0) (at a within s)`;;

let DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN = `!f:real^M->real^N s.
        f differentiable (at x within s) ==> f continuous (at x within s)`;;

let DIFFERENTIABLE_IMP_CONTINUOUS_AT = `!f:real^M->real^N x. f differentiable (at x) ==> f continuous (at x)`;;

let DIFFERENTIABLE_IMP_CONTINUOUS_ON = `!f:real^M->real^N s. f differentiable_on s ==> f continuous_on s`;;

let HAS_DERIVATIVE_WITHIN_SUBSET = `!f s t x. (f has_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_derivative f') (at x within t)`;;

let DIFFERENTIABLE_WITHIN_SUBSET = `!f:real^M->real^N s t.
      f differentiable (at x within t) /\ s SUBSET t
      ==> f differentiable (at x within s)`;;

let DIFFERENTIABLE_ON_SUBSET = `!f:real^M->real^N s t.
      f differentiable_on t /\ s SUBSET t ==> f differentiable_on s`;;

let DIFFERENTIABLE_ON_EMPTY = `!f. f differentiable_on {}`;;

(* ------------------------------------------------------------------------- *)
(* Several results are easier using a "multiplied-out" variant.              *)
(* (I got this idea from Dieudonne's proof of the chain rule).               *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_WITHIN_ALT = `!f:real^M->real^N f' s x.
     (f has_derivative f') (at x within s) <=>
            linear f' /\
            !e. &0 < e
                ==> ?d. &0 < d /\
                        !y. y IN s /\ norm(y - x) < d
                            ==> norm(f(y) - f(x) - f'(y - x)) <=
                                e * norm(y - x)`;;

let HAS_DERIVATIVE_AT_ALT = `!f:real^M->real^N f' x.
     (f has_derivative f') (at x) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !y. norm(y - x) < d
                        ==> norm(f(y) - f(x) - f'(y - x)) <= e * norm(y - x)`;;

(* ------------------------------------------------------------------------- *)
(* The chain rule.                                                           *)
(* ------------------------------------------------------------------------- *)

let DIFF_CHAIN_WITHIN = `!f:real^M->real^N g:real^N->real^P f' g' x s.
        (f has_derivative f') (at x within s) /\
        (g has_derivative g') (at (f x) within (IMAGE f s))
        ==> ((g o f) has_derivative (g' o f'))(at x within s)`;;

let DIFF_CHAIN_AT = `!f:real^M->real^N g:real^N->real^P f' g' x.
        (f has_derivative f') (at x) /\
        (g has_derivative g') (at (f x))
        ==> ((g o f) has_derivative (g' o f')) (at x)`;;

let HAS_DERIVATIVE_WITHIN_REFLECT = `!f:real^M->real^N f' s a.
        ((\x. f(--x)) has_derivative (\x. f'(--x)))
        (at (--a) within (IMAGE (--) s)) <=>
        (f has_derivative f') (at a within s)`;;

let HAS_DERIVATIVE_AT_REFLECT = `!f:real^M->real^N f' a.
        ((\x. f(--x)) has_derivative (\x. f'(--x))) (at (--a)) <=>
        (f has_derivative f') (at a)`;;

let DIFFERENTIABLE_ON_REFLECT = `!f:real^M->real^N s.
        (\x. f(--x)) differentiable_on (IMAGE (--) s) <=>
        f differentiable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Composition rules stated just for differentiability.                      *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_LINEAR = `!net f:real^M->real^N. linear f ==> f differentiable net`;;

let DIFFERENTIABLE_CONST = `!c net. (\z. c) differentiable net`;;

let DIFFERENTIABLE_ID = `!net. (\z. z) differentiable net`;;

let DIFFERENTIABLE_LIFT_COMPONENT = `!net:(real^N)net. (\x. lift(x$i)) differentiable net`;;

let DIFFERENTIABLE_CMUL = `!net f c. f differentiable net ==> (\x. c % f(x)) differentiable net`;;

let DIFFERENTIABLE_NEG = `!f net. f differentiable net ==> (\z. --(f z)) differentiable net`;;

let DIFFERENTIABLE_ADD = `!f g net.
        f differentiable net /\
        g differentiable net
        ==> (\z. f z + g z) differentiable net`;;

let DIFFERENTIABLE_SUB = `!f g net.
        f differentiable net /\
        g differentiable net
        ==> (\z. f z - g z) differentiable net`;;

let DIFFERENTIABLE_VSUM = `!f net s.
     FINITE s /\
     (!a. a IN s ==> (f a) differentiable net)
     ==> (\x. vsum s (\a. f a x)) differentiable net`;;

let DIFFERENTIABLE_VSUM_NUMSEG = `!f net m n.
     FINITE s /\
     (!i. m <= i /\ i <= n ==> (f i) differentiable net)
     ==> (\x. vsum (m..n) (\a. f a x)) differentiable net`;;

let DIFFERENTIABLE_CHAIN_AT = `!f g x.
    f differentiable (at x) /\
    g differentiable (at(f x))
    ==> (g o f) differentiable (at x)`;;

let DIFFERENTIABLE_CHAIN_WITHIN = `!f g x s.
    f differentiable (at x within s) /\
    g differentiable (at(f x) within IMAGE f s)
    ==> (g o f) differentiable (at x within s)`;;

let DIFFERENTIABLE_COMPONENTWISE_WITHIN = `!f:real^M->real^N a s.
        f differentiable (at a within s) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f(x)$i)) differentiable (at a within s)`;;

let DIFFERENTIABLE_COMPONENTWISE_AT = `!f:real^M->real^N a.
        f differentiable (at a) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f(x)$i)) differentiable (at a)`;;

(* ------------------------------------------------------------------------- *)
(* Similarly for "differentiable_on".                                        *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_ON_LINEAR = `!f:real^M->real^N s. linear f ==> f differentiable_on s`;;

let DIFFERENTIABLE_ON_CONST = `!s c. (\z. c) differentiable_on s`;;

let DIFFERENTIABLE_ON_ID = `!s. (\z. z) differentiable_on s`;;

let DIFFERENTIABLE_ON_COMPOSE = `!f g s. f differentiable_on s /\ g differentiable_on (IMAGE f s)
           ==> (g o f) differentiable_on s`;;

let DIFFERENTIABLE_ON_NEG = `!f s. f differentiable_on s ==> (\z. --(f z)) differentiable_on s`;;

let DIFFERENTIABLE_ON_ADD = `!f g s.
        f differentiable_on s /\ g differentiable_on s
        ==> (\z. f z + g z) differentiable_on s`;;

let DIFFERENTIABLE_ON_SUB = `!f g s.
        f differentiable_on s /\ g differentiable_on s
        ==> (\z. f z - g z) differentiable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of derivative.                                                 *)
(*                                                                           *)
(* The general result is a bit messy because we need approachability of the  *)
(* limit point from any direction. But OK for nontrivial intervals etc.      *)
(* ------------------------------------------------------------------------- *)

let FRECHET_DERIVATIVE_UNIQUE_WITHIN = `!f:real^M->real^N f' f'' x s.
     (f has_derivative f') (at x within s) /\
     (f has_derivative f'') (at x within s) /\
     (!i e. 1 <= i /\ i <= dimindex(:M) /\ &0 < e
            ==> ?d. &0 < abs(d) /\ abs(d) < e /\ (x + d % basis i) IN s)
     ==> f' = f''`;;

let FRECHET_DERIVATIVE_UNIQUE_AT = `!f:real^M->real^N f' f'' x.
     (f has_derivative f') (at x) /\ (f has_derivative f'') (at x)
     ==> f' = f''`;;

let HAS_FRECHET_DERIVATIVE_UNIQUE_AT = `!f:real^M->real^N f' x.
        (f has_derivative f') (at x)
        ==> frechet_derivative f (at x) = f'`;;

let FRECHET_DERIVATIVE_CONST_AT = `!c:real^N a:real^M. frechet_derivative (\x. c) (at a) = \h. vec 0`;;

let FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL = `!f:real^M->real^N f' f'' x a b.
     (!i. 1 <= i /\ i <= dimindex(:M) ==> a$i < b$i) /\
     x IN interval[a,b] /\
     (f has_derivative f') (at x within interval[a,b]) /\
     (f has_derivative f'') (at x within interval[a,b])
     ==> f' = f''`;;

let FRECHET_DERIVATIVE_UNIQUE_WITHIN_OPEN_INTERVAL = `!f:real^M->real^N f' f'' x a b.
     x IN interval(a,b) /\
     (f has_derivative f') (at x within interval(a,b)) /\
     (f has_derivative f'') (at x within interval(a,b))
     ==> f' = f''`;;

let FRECHET_DERIVATIVE_AT = `!f:real^M->real^N f' x.
     (f has_derivative f') (at x) ==> (f' = frechet_derivative f (at x))`;;

let FRECHET_DERIVATIVE_WITHIN_CLOSED_INTERVAL = `!f:real^M->real^N f' x a b.
     (!i. 1 <= i /\ i <= dimindex(:M) ==> a$i < b$i) /\
     x IN interval[a,b] /\
     (f has_derivative f') (at x within interval[a,b])
     ==> frechet_derivative f (at x within interval[a,b]) = f'`;;

(* ------------------------------------------------------------------------- *)
(* Component of the differential must be zero if it exists at a local        *)
(* maximum or minimum for that corresponding component. Start with slightly  *)
(* sharper forms that fix the sign of the derivative on the boundary.        *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM = `!f:real^M->real^N f' x s k e.
        1 <= k /\ k <= dimindex(:N) /\
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> (f x)$k <= (f w)$k)
        ==> !y. y IN s ==> &0 <= (f'(y - x))$k`;;

let DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM = `!f:real^M->real^N f' x s k e.
        1 <= k /\ k <= dimindex(:N) /\
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> (f w)$k <= (f x)$k)
        ==> !y. y IN s ==> (f'(y - x))$k <= &0`;;

let DROP_DIFFERENTIAL_POS_AT_MINIMUM = `!f:real^N->real^1 f' x s e.
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> drop(f x) <= drop(f w))
        ==> !y. y IN s ==> &0 <= drop(f'(y - x))`;;

let DROP_DIFFERENTIAL_NEG_AT_MAXIMUM = `!f:real^N->real^1 f' x s e.
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> drop(f w) <= drop(f x))
        ==> !y. y IN s ==> drop(f'(y - x)) <= &0`;;

let DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN = `!f:real^M->real^N f' x s k.
        1 <= k /\ k <= dimindex(:N) /\
        x IN s /\ open s /\ (f has_derivative f') (at x) /\
        ((!w. w IN s ==> (f w)$k <= (f x)$k) \/
         (!w. w IN s ==> (f x)$k <= (f w)$k))
        ==> !h. (f' h)$k = &0`;;

let DIFFERENTIAL_ZERO_MAXMIN_COMPONENT = `!f:real^M->real^N x e k.
        1 <= k /\ k <= dimindex(:N) /\ &0 < e /\
        ((!y. y IN ball(x,e) ==> (f y)$k <= (f x)$k) \/
         (!y. y IN ball(x,e) ==> (f x)$k <= (f y)$k)) /\
        f differentiable (at x)
        ==> (jacobian f (at x) $ k = vec 0)`;;

let DIFFERENTIAL_ZERO_MAXMIN = `!f:real^N->real^1 f' x s.
        x IN s /\ open s /\ (f has_derivative f') (at x) /\
        ((!y. y IN s ==> drop(f y) <= drop(f x)) \/
         (!y. y IN s ==> drop(f x) <= drop(f y)))
        ==> (f' = \v. vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* The traditional Rolle theorem in one dimension.                           *)
(* ------------------------------------------------------------------------- *)

let ROLLE = `!f:real^1->real^1 f' a b.
        drop a < drop b /\ (f a = f b) /\
        f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\ (f'(x) = \v. vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* One-dimensional mean value theorem.                                       *)
(* ------------------------------------------------------------------------- *)

let MVT = `!f:real^1->real^1 f' a b.
        drop a < drop b /\
        f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\ (f(b) - f(a) = f'(x) (b - a))`;;

let MVT_SIMPLE = `!f:real^1->real^1 f' a b.
        drop a < drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_derivative f'(x)) (at x within interval[a,b]))
        ==> ?x. x IN interval(a,b) /\ (f(b) - f(a) = f'(x) (b - a))`;;

let MVT_VERY_SIMPLE = `!f:real^1->real^1 f' a b.
        drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_derivative f'(x)) (at x within interval[a,b]))
        ==> ?x. x IN interval[a,b] /\ (f(b) - f(a) = f'(x) (b - a))`;;

let MVT_SEGMENT = `!f:real^N->real^1 f' a b.
        ~(a = b) /\
        f continuous_on segment[a,b] /\
        (!x. x IN segment(a,b)

             ==> (f has_derivative f' x) (at x within segment(a,b)))
        ==> ?c. c IN segment(a,b) /\ f(b) - f(a) = f'(c) (b - a)`;;

let MVT_SEGMENT_SIMPLE = `!f:real^N->real^1 f' a b.
        ~(a = b) /\
        (!x. x IN segment[a,b]
             ==> (f has_derivative f' x) (at x within segment(a,b)))
        ==> ?c. c IN segment(a,b) /\ f(b) - f(a) = f'(c) (b - a)`;;

(* ------------------------------------------------------------------------- *)
(* A nice generalization (see Havin's proof of 5.19 from Rudin's book).      *)
(* ------------------------------------------------------------------------- *)

let MVT_GENERAL = `!f:real^1->real^N f' a b.
        drop a < drop b /\
        f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\
                norm(f(b) - f(a)) <= norm(f'(x) (b - a))`;;

(* ------------------------------------------------------------------------- *)
(* Still more general bound theorem.                                         *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_BOUND = `!f:real^M->real^N f' s B.
        convex s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        (!x. x IN s ==> onorm(f'(x)) <= B)
        ==> !x y. x IN s /\ y IN s ==> norm(f(x) - f(y)) <= B * norm(x - y)`;;

(* ------------------------------------------------------------------------- *)
(* A sort of converse bounding the derivatives.                              *)
(* ------------------------------------------------------------------------- *)

let ONORM_DERIVATIVES_LE = `!f:real^M->real^N g:real^M->real^P f' g' x.
        (f has_derivative f') (at x) /\
        (g has_derivative g') (at x) /\
        eventually (\y. norm(f y - f x) <= norm(g y - g x)) (at x)
        ==> onorm f' <= onorm g'`;;

(* ------------------------------------------------------------------------- *)
(* In particular.                                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_CONSTANT = `!f:real^M->real^N s.
        convex s /\
        (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x within s))
        ==> ?c. !x. x IN s ==> f(x) = c`;;

let HAS_DERIVATIVE_ZERO_UNIQUE = `!f s a c. convex s /\ a IN s /\ f a = c /\
             (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x within s))
             ==> !x. x IN s ==> f x = c`;;

let HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT = `!f:real^M->real^N s.
        open s /\ connected s /\
        (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x))
        ==> ?c. !x. x IN s ==> f(x) = c`;;

let HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE = `!f s a c. open s /\ connected s /\ a IN s /\ f a = c /\
             (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x))
             ==> !x. x IN s ==> f x = c`;;

(* ------------------------------------------------------------------------- *)
(* Discreteness of point preimage sets for differentiable function.          *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_DISCRETE_PREIMAGES = `!f f' s y:real^N.
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> {l | l IN s /\ l limit_point_of {x | x IN s /\ f x = y}} = {}`;;

let DIFFERENTIABLE_DISCRETE_PREIMAGES_CLOSED = `!f f' s y:real^N.
        closed s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> {l | l limit_point_of {x | x IN s /\ f x = y}} = {}`;;

let DIFFERENTIABLE_COUNTABLE_PREIMAGES = `!f f' s y:real^N.
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> COUNTABLE {x | x IN s /\ f(x) = y}`;;

let DIFFERENTIABLE_FINITE_PREIMAGES = `!f f' s y:real^N.
        compact s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> FINITE {x | x IN s /\ f(x) = y}`;;

let DIFFERENTIABLE_FINITE_PREIMAGES_GEN = `!f:real^N->real^N f' s y.
         compact {x | x IN s /\ f x = y} /\
         (!x. x IN s /\ f x = y ==> (f has_derivative f' x) (at x within s)) /\
         (!x. x IN s /\ f x = y ==> ~(det (matrix (f' x)) = &0))
         ==> FINITE {x | x IN s /\ f x = y}`;;

(* ------------------------------------------------------------------------- *)
(* Differentiability of inverse function (most basic form).                  *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_INVERSE_WITHIN = `!f:real^M->real^N f' g g' s a.
        a IN s /\
        (!x. x IN s ==> g(f x) = x) /\
        (f has_derivative f') (at a within s) /\
        linear g' /\ g' o f' = I /\
        g continuous (at (f a) within IMAGE f s)
        ==> (g has_derivative g') (at (f a) within IMAGE f s)`;;

let HAS_DERIVATIVE_INVERSE_BASIC = `!f:real^M->real^N g f' g' t y.
        (f has_derivative f') (at (g y)) /\ linear g' /\ (g' o f' = I) /\
        g continuous (at y) /\
        open t /\ y IN t /\ (!z. z IN t ==> (f(g(z)) = z))
        ==> (g has_derivative g') (at y)`;;

(* ------------------------------------------------------------------------- *)
(* Simply rewrite that based on the domain point x.                          *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_INVERSE_BASIC_X = `!f:real^M->real^N g f' g' t x.
        (f has_derivative f') (at x) /\ linear g' /\ (g' o f' = I) /\
        g continuous (at (f(x))) /\ (g(f(x)) = x) /\
        open t /\ f(x) IN t /\ (!y. y IN t ==> (f(g(y)) = y))
        ==> (g has_derivative g') (at (f(x)))`;;

(* ------------------------------------------------------------------------- *)
(* This is the version in Dieudonne', assuming continuity of f and g.        *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_INVERSE_DIEUDONNE = `!f:real^M->real^N g s.
        open s /\ open (IMAGE f s) /\
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> (g(f(x)) = x))
        ==> !f' g' x. x IN s /\ (f has_derivative f') (at x) /\
                      linear g' /\ (g' o f' = I)
                      ==> (g has_derivative g') (at (f(x)))`;;

(* ------------------------------------------------------------------------- *)
(* Here's the simplest way of not assuming much about g.                     *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_INVERSE = `!f:real^M->real^N g f' g' s x.
        compact s /\ x IN s /\ f(x) IN interior(IMAGE f s) /\
        f continuous_on s /\ (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_derivative f') (at x) /\ linear g' /\ (g' o f' = I)
        ==> (g has_derivative g') (at (f(x)))`;;

(* ------------------------------------------------------------------------- *)
(* Proving surjectivity via Brouwer fixpoint theorem.                        *)
(* ------------------------------------------------------------------------- *)

let BROUWER_SURJECTIVE = `!f:real^N->real^N s t.
        compact t /\ convex t /\ ~(t = {}) /\ f continuous_on t /\
        (!x y. x IN s /\ y IN t ==> x + (y - f(y)) IN t)
        ==> !x. x IN s ==> ?y. y IN t /\ (f(y) = x)`;;

let BROUWER_SURJECTIVE_CBALL = `!f:real^N->real^N s a e.
        &0 < e /\
        f continuous_on cball(a,e) /\
        (!x y. x IN s /\ y IN cball(a,e) ==> x + (y - f(y)) IN cball(a,e))
        ==> !x. x IN s ==> ?y. y IN cball(a,e) /\ (f(y) = x)`;;

(* ------------------------------------------------------------------------- *)
(* See Sussmann: "Multidifferential calculus", Theorem 2.1.1                 *)
(* ------------------------------------------------------------------------- *)

let SUSSMANN_OPEN_MAPPING = `!f:real^M->real^N f' g' s x.
        open s /\ f continuous_on s /\
        x IN s /\ (f has_derivative f') (at x) /\ linear g' /\ (f' o g' = I)
        ==> !t. t SUBSET s /\ x IN interior(t)
                ==> f(x) IN interior(IMAGE f t)`;;

let DIFFERENTIABLE_IMP_OPEN_MAP_GEN = `!f:real^M->real^N f' g' s.
        open s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\
                 linear(g' x) /\ f' x o g' x = I)
        ==> open(IMAGE f s)`;;

let DIFFERENTIABLE_IMP_OPEN_MAP = `!f:real^N->real^N f' s.
        open s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix(f' x)) = &0))
        ==> open(IMAGE f s)`;;

let DIFFERENTIABLE_IMP_OPEN_MAP_ALT = `!f:real^N->real^N f' s t.
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within s) /\
                 ~(det(matrix(f' x)) = &0)) /\
        open t /\ t SUBSET s
        ==> open(IMAGE f t)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the following eccentric variant of the inverse function theorem.    *)
(* This has no continuity assumptions, but we do need the inverse function.  *)
(* We could put f' o g = I but this happens to fit with the minimal linear   *)
(* algebra theory I've set up so far.                                        *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_INVERSE_STRONG = `!f:real^N->real^N g f' g' s x.
        open s /\ x IN s /\ f continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_derivative f') (at x) /\ (f' o g' = I)
        ==> (g has_derivative g') (at (f(x)))`;;

(* ------------------------------------------------------------------------- *)
(* A rewrite based on the other domain.                                      *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_INVERSE_STRONG_X = `!f:real^N->real^N g f' g' s y.
        open s /\ (g y) IN s /\ f continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_derivative f') (at (g y)) /\ (f' o g' = I) /\
        f(g y) = y
        ==> (g has_derivative g') (at y)`;;

(* ------------------------------------------------------------------------- *)
(* On a region.                                                              *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_INVERSE_ON = `!f:real^N->real^N s.
        open s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x) /\ (g(f(x)) = x) /\
                        (f'(x) o g'(x) = I))
        ==> !x. x IN s ==> (g has_derivative g'(x)) (at (f(x)))`;;

(* ------------------------------------------------------------------------- *)
(* Uniformly convergent sequence of derivatives.                             *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ = `!s f:num->real^M->real^N f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(f' n x h - g' x h) <= e * norm(h))
        ==> !e. &0 < e
                ==> ?N. !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s
                                  ==> norm((f m x - f n x) - (f m y - f n y))
                                      <= e * norm(x - y)`;;

let HAS_DERIVATIVE_SEQUENCE = `!s f:num->real^M->real^N f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(f' n x h - g' x h) <= e * norm(h)) /\
        (?x l. x IN s /\ ((\n. f n x) --> l) sequentially)
        ==> ?g. !x. x IN s
                    ==> ((\n. f n x) --> g x) sequentially /\
                        (g has_derivative g'(x)) (at x within s)`;;

(* ------------------------------------------------------------------------- *)
(* Can choose to line up antiderivatives if we want.                         *)
(* ------------------------------------------------------------------------- *)

let HAS_ANTIDERIVATIVE_SEQUENCE = `!s f:num->real^M->real^N f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(f' n x h - g' x h) <= e * norm(h))
        ==> ?g. !x. x IN s ==> (g has_derivative g'(x)) (at x within s)`;;

let HAS_ANTIDERIVATIVE_LIMIT = `!s g':real^M->real^M->real^N.
        convex s /\
        (!e. &0 < e
             ==> ?f f'. !x. x IN s
                            ==> (f has_derivative (f' x)) (at x within s) /\
                                (!h. norm(f' x h - g' x h) <= e * norm(h)))
        ==> ?g. !x. x IN s ==> (g has_derivative g'(x)) (at x within s)`;;

(* ------------------------------------------------------------------------- *)
(* Differentiation of a series.                                              *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_SERIES = `!s f:num->real^M->real^N f' g' k.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(vsum(k INTER (0..n)) (\i. f' i x h) -
                                      g' x h) <= e * norm(h)) /\
        (?x l. x IN s /\ ((\n. f n x) sums l) k)
        ==> ?g. !x. x IN s ==> ((\n. f n x) sums (g x)) k /\
                               (g has_derivative g'(x)) (at x within s)`;;

(* ------------------------------------------------------------------------- *)
(* Derivative with composed bilinear function.                               *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_BILINEAR_WITHIN = `!h:real^M->real^N->real^P f g f' g' x:real^Q s.
        (f has_derivative f') (at x within s) /\
        (g has_derivative g') (at x within s) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (at x within s)`;;

let HAS_DERIVATIVE_BILINEAR_AT = `!h:real^M->real^N->real^P f g f' g' x:real^Q.
        (f has_derivative f') (at x) /\
        (g has_derivative g') (at x) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (at x)`;;

let BILINEAR_DIFFERENTIABLE_AT_COMPOSE = `!f:real^M->real^N g:real^M->real^P h:real^N->real^P->real^Q a.
        f differentiable at a /\ g differentiable at a /\ bilinear h
        ==> (\x. h (f x) (g x)) differentiable at a`;;

let BILINEAR_DIFFERENTIABLE_WITHIN_COMPOSE = `!f:real^M->real^N g:real^M->real^P h:real^N->real^P->real^Q x s.
        f differentiable at x within s /\ g differentiable at x within s /\
        bilinear h
        ==> (\x. h (f x) (g x)) differentiable at x within s`;;

let BILINEAR_DIFFERENTIABLE_ON_COMPOSE = `!f:real^M->real^N g:real^M->real^P h:real^N->real^P->real^Q s.
        f differentiable_on s /\ g differentiable_on s /\ bilinear h
        ==> (\x. h (f x) (g x)) differentiable_on s`;;

let DIFFERENTIABLE_AT_LIFT_DOT2 = `!f:real^M->real^N g x.
        f differentiable at x /\ g differentiable at x
        ==> (\x. lift(f x dot g x)) differentiable at x`;;

let DIFFERENTIABLE_WITHIN_LIFT_DOT2 = `!f:real^M->real^N g x s.
        f differentiable (at x within s) /\ g differentiable (at x within s)
        ==> (\x. lift(f x dot g x)) differentiable (at x within s)`;;

let DIFFERENTIABLE_ON_LIFT_DOT2 = `!f:real^M->real^N g s.
        f differentiable_on s /\ g differentiable_on s
        ==> (\x. lift(f x dot g x)) differentiable_on s`;;

let HAS_DERIVATIVE_MUL_WITHIN = `!f f' g:real^M->real^N g' a s.
        ((lift o f) has_derivative (lift o f')) (at a within s) /\
        (g has_derivative g') (at a within s)
        ==> ((\x. f x % g x) has_derivative
             (\h. f a % g' h + f' h % g a)) (at a within s)`;;

let HAS_DERIVATIVE_MUL_AT = `!f f' g:real^M->real^N g' a.
        ((lift o f) has_derivative (lift o f')) (at a) /\
        (g has_derivative g') (at a)
        ==> ((\x. f x % g x) has_derivative
             (\h. f a % g' h + f' h % g a)) (at a)`;;

let HAS_DERIVATIVE_SQNORM_AT = `!a:real^N.
    ((\x. lift(norm x pow 2)) has_derivative (\x. &2 % lift(a dot x))) (at a)`;;

let DIFFERENTIABLE_MUL_WITHIN = `!f g:real^M->real^N a s.
        (lift o f) differentiable (at a within s) /\
        g differentiable (at a within s)
        ==> (\x. f x % g x) differentiable (at a within s)`;;

let DIFFERENTIABLE_MUL_AT = `!f g:real^M->real^N a.
        (lift o f) differentiable (at a) /\ g differentiable (at a)
        ==> (\x. f x % g x) differentiable (at a)`;;

let DIFFERENTIABLE_SQNORM_AT = `!a:real^N. (\x. lift(norm x pow 2)) differentiable (at a)`;;

let DIFFERENTIABLE_ON_MUL = `!f g:real^M->real^N s.
        (lift o f) differentiable_on s /\ g differentiable_on s
        ==> (\x. f x % g x) differentiable_on s`;;

let DIFFERENTIABLE_ON_SQNORM = `!s:real^N->bool. (\x. lift(norm x pow 2)) differentiable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Partial derivatives and jacobians are Baire functions.                    *)
(* ------------------------------------------------------------------------- *)

let BAIRE1_PARTIAL_DERIVATIVES = `!f:real^M->real^N f' s i j.
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\
        open s /\
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:M)
        ==> baire 1 s (\x. lift(matrix(f' x)$i$j))`;;

let BAIRE1_DET_JACOBIAN = `!f:real^N->real^N f' s.
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\ open s
        ==> baire 1 s (\x. lift(det(matrix(f' x))))`;;

(* ------------------------------------------------------------------------- *)
(* A Frechet derivative is also a Gateaux derivative, and if the function    *)
(* is Lipschitz then the converse also holds.                                *)
(* ------------------------------------------------------------------------- *)

let GATEAUX_DERIVATIVE_WITHIN = `!f:real^M->real^N f' s x y.
        (f has_derivative f') (at x within s)
        ==> ((\t. inv(drop t) % (f(x + drop t % y) - f(x))) --> f' y)
            (at (vec 0) within {t | (x + drop t % y) IN s})`;;

let GATEAUX_DERIVATIVE = `!f:real^M->real^N f' x y.
        (f has_derivative f') (at x)
        ==> ((\t. inv(drop t) % (f(x + drop t % y) - f(x))) --> f' y)
            (at (vec 0))`;;

let GATEAUX_DERIVATIVE_LIPSCHITZ = `!f:real^M->real^N f' x s.
        x IN s /\ open s /\
        (?B. !u v. u IN s /\ v IN s ==> norm(f u - f v) <= B * norm(u - v)) /\
        linear f' /\
        (!y. ((\t. inv(drop t) % (f(x + drop t % y) - f(x))) --> f' y)
             (at (vec 0)))
        ==> (f has_derivative f') (at x)`;;

(* ------------------------------------------------------------------------- *)
(* Strong form of the inverse function theorem not assuming continuity of    *)
(* the derivative. This proof closely follows Jean Saint Raymond's paper     *)
(* "Local Inversion for Differentiable Functions and the Darboux Property".  *)
(* ------------------------------------------------------------------------- *)

let INVERSE_FUNCTION_THEOREM = `!f:real^N->real^N f' a s.
        open s /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0))
        ==> ?t u g g'. open t /\ a IN t /\ t SUBSET s /\ open u /\ f a IN u /\
                       homeomorphism (t,u) (f,g) /\
                       (!x. x IN t
                            ==> (f has_derivative f' x) (at x) /\
                                f'(x) o g'(f x) = I /\ g'(f x) o f'(x) = I) /\
                       (!y. y IN u
                            ==> (g has_derivative g' y) (at y) /\
                                f'(g y) o g' y = I /\ g' y o f'(g y) = I)`;;

(* ------------------------------------------------------------------------- *)
(* Sign invariance of nonvanishing Jacobian (also from Saint Raymond).       *)
(* ------------------------------------------------------------------------- *)

let JACOBIAN_SIGN_INVARIANCE = `!f:real^N->real^N f' s.
        open s /\ connected s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0))
        ==> (!x. x IN s ==> &0 < det(matrix(f' x))) \/
            (!x. x IN s ==> det(matrix(f' x)) < &0)`;;

(* ------------------------------------------------------------------------- *)
(* Invertible derivative continous at a point implies local injectivity.     *)
(* It's only for this we need continuity of the derivative, except of course *)
(* if we want the fact that the inverse derivative is also continuous. So if *)
(* we know for some other reason that the inverse function exists, it's OK.  *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_LOCALLY_INJECTIVE = `!f:real^M->real^N f' g' s a.
        a IN s /\ open s /\ linear g' /\ (g' o f'(a) = I) /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !x. dist(a,x) < d ==> onorm(\v. f'(x) v - f'(a) v) < e)
        ==> ?t. a IN t /\ open t /\
                !x x'. x IN t /\ x' IN t /\ (f x' = f x) ==> (x' = x)`;;

(* ------------------------------------------------------------------------- *)
(* More conventional "C1" version of inverse function theorem.               *)
(* ------------------------------------------------------------------------- *)

let INVERSE_FUNCTION_THEOREM_C1_POINTWISE = `!f:real^N->real^N f' s a.
        open s /\ a IN s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\
        ~(det(matrix(f' a)) = &0) /\ (!h. (\x. f' x h) continuous at a)
        ==> ?t u g g'.
                open t /\ a IN t /\ t SUBSET s /\ open u /\ f a IN u /\
                homeomorphism (t,u) (f,g) /\
                (!x. x IN t
                     ==> (f has_derivative f' x) (at x) /\
                         f'(x) o g'(f x) = I /\ g'(f x) o f'(x) = I) /\
                (!y. y IN u
                     ==> (g has_derivative g' y) (at y) /\
                         f'(g y) o g' y = I /\ g' y o f'(g y) = I) /\
                (!x. x IN t /\ (!h. (\y. f' y h) continuous at x)
                       ==> (!h. (\z. g' z h) continuous at (f x)))`;;

let INVERSE_FUNCTION_C1 = `!f:real^N->real^N f' s a.
        open s /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f'(x)) (at x) /\
                 ((!h. (\y. f' y h) continuous at x))) /\
        ~(det(matrix(f' a)) = &0)
        ==> ?t u g g'.
                open t /\ a IN t /\ t SUBSET s /\ open u /\ f a IN u /\
                homeomorphism (t,u) (f,g) /\
                (!x. x IN t
                     ==> (f has_derivative f' x) (at x) /\
                         f'(x) o g'(f x) = I /\ g'(f x) o f'(x) = I) /\
                (!y. y IN u
                     ==> (g has_derivative g' y) (at y) /\
                         f'(g y) o g' y = I /\ g' y o f'(g y) = I) /\
                (!x. x IN t ==> (!h. (\z. g' z h) continuous at (f x)))`;;

(* ------------------------------------------------------------------------- *)
(* A Hadamard-style global inverse function theorem when the function is     *)
(* a closed (or equivalently proper) map into a simply connected set.        *)
(* ------------------------------------------------------------------------- *)

let INVERSE_FUNCTION_THEOREM_GLOBAL = `!f:real^N->real^N f' s t.
      open s /\ connected s /\ simply_connected t /\ (s = {} ==> t = {}) /\
      (!c. closed_in (subtopology euclidean s) c
           ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
      (!x. x IN s
           ==> (f has_derivative f' x) (at x) /\ ~(det(matrix(f' x)) = &0))
      ==> ?g g'. homeomorphism (s,t) (f,g) /\
                 (!y. y IN t
                      ==> (g has_derivative g' y) (at y) /\
                          f' (g y) o g' y = I /\ g' y o f' (g y) = I) /\
                 (!x. x IN s ==> f' x o g' (f x) = I /\ g' (f x) o f' x = I)`;;

(* ------------------------------------------------------------------------- *)
(* Some slightly more refined localized variants.                            *)
(* ------------------------------------------------------------------------- *)

let INVERSE_FUNCTION_THEOREM_SUBSPACE = `!f:real^N->real^N f' s p a.
        subspace p /\ open_in (subtopology euclidean p) s /\
        IMAGE f s SUBSET p /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within p) /\ IMAGE (f' x) p = p)
        ==> ?t u g g'. open_in (subtopology euclidean p) t /\ a IN t /\
                       t SUBSET s /\
                       open_in (subtopology euclidean p) u /\ f(a) IN u /\
                       homeomorphism (t,u) (f,g) /\
                       (!x. x IN t
                            ==> (f has_derivative f' x) (at x within p) /\
                                (!h. h IN p
                                     ==> f' x (g' (f x) h) = h /\
                                         g' (f x) (f' x h) = h)) /\
                       (!y. y IN u
                            ==> (g has_derivative g' y) (at y within p) /\
                                (!h. h IN p
                                     ==> f' (g y) (g' y h) = h /\
                                         g' y (f' (g y) h) = h))`;;

let INVERSE_FUNCTION_THEOREM_AFFINE = `!f:real^N->real^N f' s p a.
        affine p /\ open_in (subtopology euclidean p) s /\
        IMAGE f s SUBSET p /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within p) /\
                 ~(det (matrix (f' x)) = &0))
        ==> ?t u g g'. open_in (subtopology euclidean p) t /\ a IN t /\
                       t SUBSET s /\
                       open_in (subtopology euclidean p) u /\ f(a) IN u /\
                       homeomorphism (t,u) (f,g) /\
                       (!x. x IN t
                            ==> (f has_derivative f' x) (at x within p) /\
                                f' x o g' (f x) = I /\
                                g' (f x) o f' x = I) /\
                       (!y. y IN u
                            ==> (g has_derivative g' y) (at y within p) /\
                                f' (g y) o g' y = I /\
                                g' y o f' (g y) = I)`;;

(* ------------------------------------------------------------------------- *)
(* Considering derivative R(^1)->R^n as a vector.                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_vector_derivative",(12,"right"));;

let has_vector_derivative = new_definition
 `(f has_vector_derivative f') net <=>
        (f has_derivative (\x. drop(x) % f')) net`;;

let vector_derivative = new_definition
 `vector_derivative (f:real^1->real^N) net =
        @f'. (f has_vector_derivative f') net`;;

let VECTOR_DERIVATIVE_WORKS = `!net f:real^1->real^N.
        f differentiable net <=>
        (f has_vector_derivative (vector_derivative f net)) net`;;

let VECTOR_DIFFERENTIABLE = `!f net. f differentiable net <=> (?f'. (f has_vector_derivative f') net)`;;

let HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE = `!f f' net. (f has_vector_derivative f') net ==> f differentiable net`;;

let VECTOR_DERIVATIVE_UNIQUE_AT = `!f:real^1->real^N x f' f''.
     (f has_vector_derivative f') (at x) /\
     (f has_vector_derivative f'') (at x)
     ==> f' = f''`;;

let VECTOR_DERIVATIVE_AT = `!f:real^1->real^N f' x.
        (f has_vector_derivative f') (at x)
        ==> vector_derivative f (at x) = f'`;;

let HAS_VECTOR_DERIVATIVE_COMPONENTWISE_WITHIN = `!(f:real^1->real^N) f' a s.
         (f has_vector_derivative f') (at a within s) <=>
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i))
                 (at a within s)`;;

let HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT = `!(f:real^1->real^N) f' a.
         (f has_vector_derivative f') (at a) <=>
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i)) (at a)`;;

let HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_WITHIN = `!(f:real^1->real^N) f' a s i.
        (f has_vector_derivative f') (at a within s) /\
        1 <= i /\ i <= dimindex(:N)
        ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i))
             (at a within s)`;;

let HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT = `!(f:real^1->real^N) f' a i.
        (f has_vector_derivative f') (at a) /\
        1 <= i /\ i <= dimindex(:N)
        ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i)) (at a)`;;

let HAS_VECTOR_DERIVATIVE_WITHIN_1D = `!f:real^1->real^N s x.
      (f has_vector_derivative f') (at x within s) <=>
      ((\y. inv(drop(y - x)) % (f y - f x)) --> f') (at x within s)`;;

let HAS_VECTOR_DERIVATIVE_AT_1D = `!f:real^1->real^N x.
      (f has_vector_derivative f') (at x) <=>
      ((\y. inv(drop(y - x)) % (f y - f x)) --> f') (at x)`;;

let VECTOR_DERIVATIVE_UNIQUE_WITHIN = `!(f:real^1->real^N) x s f' f''.
        ~trivial_limit (at x within s) /\
        (f has_vector_derivative f') (at x within s) /\
        (f has_vector_derivative f'') (at x within s)
        ==> f' = f''`;;

let VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL = `!f:real^1->real^N a b x f' f''.
        drop a < drop b /\
        x IN interval [a,b] /\
        (f has_vector_derivative f') (at x within interval [a,b]) /\
        (f has_vector_derivative f'') (at x within interval [a,b])
        ==> f' = f''`;;

let VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL = `!f:real^1->real^N f' x a b.
         drop a < drop b /\ x IN interval[a,b] /\
         (f has_vector_derivative f') (at x within interval [a,b])
         ==> vector_derivative f (at x within interval [a,b]) = f'`;;

let HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET = `!f s t x. (f has_vector_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_vector_derivative f') (at x within t)`;;

let HAS_VECTOR_DERIVATIVE_CONST = `!c net. ((\x. c) has_vector_derivative vec 0) net`;;

let VECTOR_DERIVATIVE_CONST_AT = `!c:real^N a. vector_derivative (\x. c) (at a) = vec 0`;;

let HAS_VECTOR_DERIVATIVE_ID = `!net. ((\x. x) has_vector_derivative (vec 1)) net`;;

let HAS_VECTOR_DERIVATIVE_CMUL = `!f f' net c. (f has_vector_derivative f') net
                ==> ((\x. c % f(x)) has_vector_derivative (c % f')) net`;;

let HAS_VECTOR_DERIVATIVE_CMUL_EQ = `!f f' net c.
       ~(c = &0)
       ==> (((\x. c % f(x)) has_vector_derivative (c % f')) net <=>
            (f has_vector_derivative f') net)`;;

let HAS_VECTOR_DERIVATIVE_NEG = `!f f' net. (f has_vector_derivative f') net
            ==> ((\x. --(f(x))) has_vector_derivative (--f')) net`;;

let HAS_VECTOR_DERIVATIVE_NEG_EQ = `!f f' net. ((\x. --(f(x))) has_vector_derivative --f') net <=>
              (f has_vector_derivative f') net`;;

let HAS_VECTOR_DERIVATIVE_ADD = `!f f' g g' net.
        (f has_vector_derivative f') net /\ (g has_vector_derivative g') net
        ==> ((\x. f(x) + g(x)) has_vector_derivative (f' + g')) net`;;

let HAS_VECTOR_DERIVATIVE_SUB = `!f f' g g' net.
        (f has_vector_derivative f') net /\ (g has_vector_derivative g') net
        ==> ((\x. f(x) - g(x)) has_vector_derivative (f' - g')) net`;;

let HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN = `!h:real^M->real^N->real^P f g f' g' x s.
        (f has_vector_derivative f') (at x within s) /\
        (g has_vector_derivative g') (at x within s) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_vector_derivative
             (h (f x) g' + h f' (g x))) (at x within s)`;;

let HAS_VECTOR_DERIVATIVE_BILINEAR_AT = `!h:real^M->real^N->real^P f g f' g' x.
        (f has_vector_derivative f') (at x) /\
        (g has_vector_derivative g') (at x) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_vector_derivative
             (h (f x) g' + h f' (g x))) (at x)`;;

let HAS_VECTOR_DERIVATIVE_AT_WITHIN = `!f x s. (f has_vector_derivative f') (at x)
           ==> (f has_vector_derivative f') (at x within s)`;;

let HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN = `!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       (f has_vector_derivative f') (at x within s)
       ==> (g has_vector_derivative f') (at x within s)`;;

let HAS_VECTOR_DERIVATIVE_TRANSFORM_AT = `!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> f x' = g x') /\
       (f has_vector_derivative f') (at x)
       ==> (g has_vector_derivative f') (at x)`;;

let HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN = `!f g s x.
        open s /\ x IN s /\
        (!y. y IN s ==> f y = g y) /\
        (f has_vector_derivative f') (at x)
        ==> (g has_vector_derivative f') (at x)`;;

let VECTOR_DIFF_CHAIN_AT = `!f g f' g' x.
         (f has_vector_derivative f') (at x) /\
         (g has_vector_derivative g') (at (f x))
         ==> ((g o f) has_vector_derivative (drop f' % g')) (at x)`;;

let VECTOR_DIFF_CHAIN_WITHIN = `!f g f' g' s x.
         (f has_vector_derivative f') (at x within s) /\
         (g has_vector_derivative g') (at (f x) within IMAGE f s)
         ==> ((g o f) has_vector_derivative (drop f' % g')) (at x within s)`;;

let VECTOR_DIFFERENTIABLE_BOUND = `!f f':real^1->real^N s B.
     convex s /\
     (!x. x IN s ==> (f has_vector_derivative f' x) (at x within s)) /\
     (!x. x IN s ==> norm (f' x) <= B)
     ==> (!x y. x IN s /\ y IN s ==> norm (f x - f y) <= B * norm (x - y))`;;

let HAS_BOUNDED_VECTOR_DERIVATIVE_IMP_LIPSCHITZ = `!f:real^1->real^N f' s.
      (!x. x IN s ==> (f has_vector_derivative f'(x)) (at x within s)) /\
      convex s /\ bounded(IMAGE f' s)
      ==> ?B. &0 < B /\
              !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm (x - y)`;;

let RESTRICTION_HAS_DERIVATIVE = `!f:real^1->real^N f' s x.
     x IN s
     ==> ((RESTRICTION s f has_vector_derivative f') (at x within s) <=>
          (f has_vector_derivative f') (at x within s))`;;

let BAIRE1_VECTOR_DERIVATIVE = `!f:real^1->real^N f' s.
        (!x. x IN s ==> (f has_vector_derivative f'(x)) (at x)) /\ open s
        ==> baire 1 s f'`;;

(* ------------------------------------------------------------------------- *)
(* Bounds on derivatives from function properties.                           *)
(* ------------------------------------------------------------------------- *)

let VECTOR_DERIVATIVE_INCREASING_WITHIN = `!f f' s a.
        (!x y. x IN s /\ y IN s /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        a IN s /\ a limit_point_of s /\
        (f has_vector_derivative f') (at a within s)
        ==> &0 <= drop f'`;;

let NORM_VECTOR_DERIVATIVES_LE_WITHIN = `!f:real^1->real^M g:real^1->real^N f' g' x s.
        x limit_point_of s /\
        (f has_vector_derivative f') (at x within s) /\
        (g has_vector_derivative g') (at x within s) /\
        eventually (\y. norm(f y - f x) <= norm(g y - g x)) (at x within s)
        ==> norm f' <= norm g'`;;

let NORM_VECTOR_DERIVATIVES_LE_AT = `!f:real^1->real^M g:real^1->real^N f' g' x.
        (f has_vector_derivative f') (at x) /\
        (g has_vector_derivative g') (at x) /\
        eventually (\y. norm(f y - f x) <= norm(g y - g x)) (at x)
        ==> norm f' <= norm g'`;;

(* ------------------------------------------------------------------------- *)
(* Various versions of Kachurovskii's theorem.                               *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_DERIVATIVE_SECANT_IMP = `!f f' s x y:real^N.
        f convex_on s /\ segment[x,y] SUBSET s /\
        ((lift o f) has_derivative (lift o f')) (at x within s)
        ==> f'(y - x) <= f y - f x`;;

let CONVEX_ON_SECANT_DERIVATIVE_IMP = `!f f' s x y:real^N.
        f convex_on s /\ segment[x,y] SUBSET s /\
        ((lift o f) has_derivative (lift o f')) (at y within s)
        ==> f y - f x <= f'(y - x)`;;

let CONVEX_ON_DERIVATIVES_IMP = `!f f'x f'y s x y:real^N.
        f convex_on s /\ segment[x,y] SUBSET s /\
        ((lift o f) has_derivative (lift o f'x)) (at x within s) /\
        ((lift o f) has_derivative (lift o f'y)) (at y within s)
        ==> f'x(y - x) <= f'y(y - x)`;;

let CONVEX_ON_DERIVATIVE_SECANT = `(!f f' s:real^N->bool.
        convex s /\
        (!x. x IN s ==> ((lift o f) has_derivative (lift o f'(x)))
                        (at x within s))
        ==> (f convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x)(y - x) <= f y - f x))`
and CONVEX_ON_DERIVATIVES = `(!f f' s:real^N->bool.
        convex s /\
        (!x. x IN s ==> ((lift o f) has_derivative (lift o f'(x)))
                        (at x within s))
        ==> (f convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x)(y - x) <= f'(y)(y - x)))`;;

let CONVEX_ON_SECANT_DERIVATIVE = `!f f' s:real^N->bool.
        convex s /\
        (!x. x IN s ==> ((lift o f) has_derivative (lift o f'(x)))
                        (at x within s))
        ==> (f convex_on s <=>
             !x y. x IN s /\ y IN s ==> f y - f x <= f'(y)(y - x))`;;
