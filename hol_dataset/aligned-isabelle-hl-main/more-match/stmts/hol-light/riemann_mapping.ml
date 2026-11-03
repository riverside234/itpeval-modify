(* ========================================================================= *)
(* Complex path integrals and Cauchy's theorem.                              *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* (c) Copyright, Gianni Ciolli, Graziano Gentili, Marco Maggesi 2008-2009.  *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Library/iter.ml";;
needs "Multivariate/moretop.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Piecewise differentiability on a 1-D interval. The definition doesn't     *)
(* tie it to real^1 but it's not obviously that useful elsewhere.            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("piecewise_differentiable_on",(12,"right"));;

let piecewise_differentiable_on = new_definition
 `f piecewise_differentiable_on i <=>
        f continuous_on i /\
        (?s. FINITE s /\ !x. x IN (i DIFF s) ==> f differentiable at x)`;;

let PIECEWISE_DIFFERENTIABLE_ON_IMP_CONTINUOUS_ON = `!f s. f piecewise_differentiable_on s ==> f continuous_on s`;;

let PIECEWISE_DIFFERENTIABLE_ON_SUBSET = `!f s t.
        f piecewise_differentiable_on s /\ t SUBSET s
        ==> f piecewise_differentiable_on t`;;

let DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE = `!f:real^1->real^N a b.
        f differentiable_on interval[a,b]
        ==> f piecewise_differentiable_on interval[a,b]`;;

let DIFFERENTIABLE_IMP_PIECEWISE_DIFFERENTIABLE = `!f s. (!x. x IN s ==> f differentiable (at x))
         ==> f piecewise_differentiable_on s`;;

let PIECEWISE_DIFFERENTIABLE_COMPOSE = `!f:real^M->real^N g:real^N->real^P s.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on (IMAGE f s) /\
        (!b. FINITE {x | x IN s /\ f(x) = b})
        ==> (g o f) piecewise_differentiable_on s`;;

let DIFFERENTIABLE_PIECEWISE_DIFFERENTIABLE_COMPOSE = `!f:real^M->real^N g:real^N->real^P s.
        f piecewise_differentiable_on s /\
        g differentiable_on (:real^N)
        ==> (g o f) piecewise_differentiable_on s`;;

let PIECEWISE_DIFFERENTIABLE_AFFINE = `!f:real^M->real^N s m c.
        f piecewise_differentiable_on (IMAGE (\x. m % x + c) s)
        ==> (f o (\x. m % x + c)) piecewise_differentiable_on s`;;

let PIECEWISE_DIFFERENTIABLE_CASES = `!f g:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b /\ f c = g c /\
        f piecewise_differentiable_on interval[a,c] /\
        g piecewise_differentiable_on interval[c,b]
        ==> (\x. if drop x <= drop c then f(x) else g(x))
            piecewise_differentiable_on interval[a,b]`;;

let PIECEWISE_DIFFERENTIABLE_NEG = `!f:real^M->real^N s.
        f piecewise_differentiable_on s
        ==> (\x. --(f x)) piecewise_differentiable_on s`;;

let PIECEWISE_DIFFERENTIABLE_ADD = `!f g:real^M->real^N s.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on s
        ==> (\x. f x + g x) piecewise_differentiable_on s`;;

let PIECEWISE_DIFFERENTIABLE_SUB = `!f g:real^M->real^N s.
        f piecewise_differentiable_on s /\
        g piecewise_differentiable_on s
        ==> (\x. f x - g x) piecewise_differentiable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Valid paths, and their start and finish.                                  *)
(* ------------------------------------------------------------------------- *)

let valid_path = new_definition
 `valid_path (f:real^1->complex) <=>
     f piecewise_differentiable_on interval[vec 0,vec 1]`;;

let closed_path = new_definition
 `closed_path g <=> pathstart g = pathfinish g`;;

let VALID_PATH_EQ = `!p q. (!t. t IN interval[vec 0,vec 1] ==> p t = q t) /\ valid_path p
         ==> valid_path q`;;

let VALID_PATH_COMPOSE = `!f g. valid_path g /\ f differentiable_on (path_image g)
         ==> valid_path (f o g)`;;

let VALID_PATH_TRANSLATION_EQ = `!a g. valid_path((\x. a + x) o g) <=> valid_path g`;;

add_translation_invariants [VALID_PATH_TRANSLATION_EQ];;

let VALID_PATH_LINEAR_IMAGE_EQ = `!f g. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (valid_path(f o g) <=> valid_path g)`;;

add_linear_invariants [VALID_PATH_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* In particular, all results for paths apply.                               *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_IMP_PATH = `!g. valid_path g ==> path g`;;

let CONNECTED_VALID_PATH_IMAGE = `!g. valid_path g ==> connected(path_image g)`;;

let COMPACT_VALID_PATH_IMAGE = `!g. valid_path g ==> compact(path_image g)`;;

let BOUNDED_VALID_PATH_IMAGE = `!g. valid_path g ==> bounded(path_image g)`;;

let CLOSED_VALID_PATH_IMAGE = `!g. valid_path g ==> closed(path_image g)`;;

(* ------------------------------------------------------------------------- *)
(* Theorems about rectifiable valid paths.                                   *)
(* ------------------------------------------------------------------------- *)

let RECTIFIABLE_VALID_PATH = `!g. valid_path g
       ==> (rectifiable_path g <=>
              (\t. vector_derivative g (at t)) absolutely_integrable_on
              interval [vec 0,vec 1])`;;

let PATH_LENGTH_VALID_PATH = `!g. valid_path g /\ rectifiable_path g
       ==> path_length g =
                 drop(integral (interval[vec 0,vec 1])
                               (\t. lift(norm(vector_derivative g (at t)))))`;;

let ABSOLUTELY_CONTINUOUS_RECTIFIABLE_VALID_PATH = `!g:real^1->complex.
        valid_path g /\ rectifiable_path g
        ==> g absolutely_continuous_on interval[vec 0,vec 1]`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility of valid_path image                                         *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_VALID_PATH_IMAGE = `!g. valid_path g ==> negligible(path_image g)`;;

(* ------------------------------------------------------------------------- *)
(* Integrals along a path (= piecewise differentiable function on [0,1]).    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_path_integral",(12,"right"));;
parse_as_infix("path_integrable_on",(12,"right"));;

let has_path_integral = define
  `(f has_path_integral i) (g) <=>
       ((\x. f(g(x)) * vector_derivative g (at x within interval[vec 0,vec 1]))
        has_integral i)
       (interval[vec 0,vec 1])`;;

let path_integral = new_definition
 `path_integral g f = @i. (f has_path_integral i) (g)`;;

let path_integrable_on = new_definition
 `f path_integrable_on g <=> ?i. (f has_path_integral i) g`;;

let PATH_INTEGRAL_UNIQUE = `!f g i. (f has_path_integral i) (g) ==> path_integral(g) f = i`;;

let HAS_PATH_INTEGRAL_INTEGRAL = `!f i. f path_integrable_on i
         ==> (f has_path_integral (path_integral i f)) i`;;

let HAS_PATH_INTEGRAL_UNIQUE = `!f i j g. (f has_path_integral i) g /\
             (f has_path_integral j) g
             ==> i = j`;;

let HAS_PATH_INTEGRAL_INTEGRABLE = `!f g i. (f has_path_integral i) g ==> f path_integrable_on g`;;

let HAS_PATH_INTEGRAL_INTEGRABLE_INTEGRAL = `!f y g. (f has_path_integral y) g <=>
           f path_integrable_on g /\ path_integral g f = y`;;

(* ------------------------------------------------------------------------- *)
(* Show that we can forget about the localized derivative.                   *)
(* ------------------------------------------------------------------------- *)

let VECTOR_DERIVATIVE_WITHIN_INTERIOR = `!a b x.
        x IN interior(interval[a,b])
        ==> vector_derivative f (at x within interval[a,b]) =
            vector_derivative f (at x)`;;

let HAS_INTEGRAL_LOCALIZED_VECTOR_DERIVATIVE = `((\x. f' (g x) * vector_derivative g (at x within interval [a,b]))
    has_integral i) (interval [a,b]) <=>
    ((\x. f' (g x) * vector_derivative g (at x))
     has_integral i) (interval [a,b])`;;

let HAS_PATH_INTEGRAL = `(f has_path_integral i) g <=>
        ((\x. f (g x) * vector_derivative g (at x)) has_integral i)
        (interval[vec 0,vec 1])`;;

let PATH_INTEGRABLE_ON = `f path_integrable_on g <=>
        (\t. f(g t) * vector_derivative g (at t))
            integrable_on interval[vec 0,vec 1]`;;

(* ------------------------------------------------------------------------- *)
(* Reversing a path.                                                         *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_REVERSEPATH = `!g. valid_path(reversepath g) <=> valid_path g`;;

let HAS_PATH_INTEGRAL_REVERSEPATH = `!f g i. valid_path g /\ (f has_path_integral i) g
           ==> (f has_path_integral (--i)) (reversepath g)`;;

let PATH_INTEGRABLE_REVERSEPATH = `!f g. valid_path g /\ f path_integrable_on g
         ==> f path_integrable_on (reversepath g)`;;

let PATH_INTEGRABLE_REVERSEPATH_EQ = `!f g. valid_path g
         ==> (f path_integrable_on (reversepath g) <=>
              f path_integrable_on g)`;;

let PATH_INTEGRAL_REVERSEPATH = `!f g. valid_path g /\ f path_integrable_on g
         ==> path_integral (reversepath g) f = --(path_integral g f)`;;

(* ------------------------------------------------------------------------- *)
(* Joining two paths together.                                               *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_JOIN_EQ = `!g1 g2.
        pathfinish g1 = pathstart g2
        ==> (valid_path(g1 ++ g2) <=> valid_path g1 /\ valid_path g2)`;;

let VALID_PATH_JOIN = `!g1 g2.
        valid_path g1 /\ valid_path g2 /\ pathfinish g1 = pathstart g2
        ==> valid_path(g1 ++ g2)`;;

let VALID_PATH_SYM = `!p q:real^1->complex.
        pathfinish p = pathstart q /\ pathfinish q = pathstart p
        ==> (valid_path(p ++ q) <=> valid_path(q ++ p))`;;

let HAS_PATH_INTEGRAL_JOIN = `!f g1 g2 i1 i2.
        (f has_path_integral i1) g1 /\
        (f has_path_integral i2) g2 /\
        valid_path g1 /\ valid_path g2
        ==> (f has_path_integral (i1 + i2)) (g1 ++ g2)`;;

let PATH_INTEGRABLE_JOIN = `!f g1 g2.
        valid_path g1 /\ valid_path g2
        ==> (f path_integrable_on (g1 ++ g2) <=>
             f path_integrable_on g1 /\ f path_integrable_on g2)`;;

let PATH_INTEGRAL_JOIN = `!f g1 g2:real^1->complex.
        valid_path g1 /\ valid_path g2 /\
        f path_integrable_on g1 /\ f path_integrable_on g2
        ==> path_integral (g1 ++ g2) f =
            path_integral g1 f + path_integral g2 f`;;

(* ------------------------------------------------------------------------- *)
(* Reparametrizing to shift the starting point of a (closed) path.           *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_SHIFTPATH = `!g a. valid_path g /\ pathfinish g = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> valid_path(shiftpath a g)`;;

let HAS_PATH_INTEGRAL_SHIFTPATH = `!f g i a.
        (f has_path_integral i) g /\ valid_path g /\
        a IN interval[vec 0,vec 1]
        ==> (f has_path_integral i) (shiftpath a g)`;;

let HAS_PATH_INTEGRAL_SHIFTPATH_EQ = `!f g i a.
        valid_path g /\ pathfinish g = pathstart g /\
        a IN interval[vec 0,vec 1]
        ==> ((f has_path_integral i) (shiftpath a g) <=>
             (f has_path_integral i) g)`;;

let PATH_INTEGRAL_SHIFTPATH = `!f g a. valid_path g /\ pathfinish g = pathstart g /\
           a IN interval[vec 0,vec 1]
           ==> path_integral (shiftpath a g) f = path_integral g f`;;

(* ------------------------------------------------------------------------- *)
(* More about straight-line paths.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_VECTOR_DERIVATIVE_LINEPATH_WITHIN = `!a b:complex x s.
    (linepath(a,b) has_vector_derivative (b - a)) (at x within s)`;;

let HAS_VECTOR_DERIVATIVE_LINEPATH_AT = `!a b:complex x.
    (linepath(a,b) has_vector_derivative (b - a)) (at x)`;;

let VALID_PATH_LINEPATH = `!a b. valid_path(linepath(a,b))`;;

let VECTOR_DERIVATIVE_LINEPATH_WITHIN = `!a b x. x IN interval[vec 0,vec 1]
           ==> vector_derivative (linepath(a,b))
                (at x within interval[vec 0,vec 1]) = b - a`;;

let VECTOR_DERIVATIVE_LINEPATH_AT = `!a b x. vector_derivative (linepath(a,b)) (at x) = b - a`;;

let HAS_PATH_INTEGRAL_LINEPATH = `!f i a b. (f has_path_integral i) (linepath(a,b)) <=>
             ((\x. f(linepath(a,b) x) * (b - a)) has_integral i)
             (interval[vec 0,vec 1])`;;

let LINEPATH_IN_PATH = `!x. x IN interval[vec 0,vec 1] ==> linepath(a,b) x IN segment[a,b]`;;

let RE_LINEPATH_CX = `!a b x. Re(linepath(Cx a,Cx b) x) = (&1 - drop x) * a + drop x * b`;;

let IM_LINEPATH_CX = `!a b x. Im(linepath(Cx a,Cx b) x) = &0`;;

let LINEPATH_CX = `!a b x. linepath(Cx a,Cx b) x = Cx((&1 - drop x) * a + drop x * b)`;;

let HAS_PATH_INTEGRAL_TRIVIAL = `!f a. (f has_path_integral (Cx(&0))) (linepath(a,a))`;;

let PATH_INTEGRAL_TRIVIAL = `!f a. path_integral (linepath(a,a)) f = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* Relation to subpath construction.                                         *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_SUBPATH = `!g u v. valid_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
           ==> valid_path(subpath u v g)`;;

let HAS_PATH_INTEGRAL_SUBPATH_REFL = `!f g u. (f has_path_integral (Cx(&0))) (subpath u u g)`;;

let PATH_INTEGRABLE_SUBPATH_REFL = `!f g u. f path_integrable_on (subpath u u g)`;;

let PATH_INTEGRAL_SUBPATH_REFL = `!f g u. path_integral (subpath u u g) f = Cx(&0)`;;

let HAS_PATH_INTEGRAL_SUBPATH = `!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
        drop u <= drop v
        ==> (f has_path_integral
             integral (interval[u,v])
                      (\x. f(g x) * vector_derivative g (at x)))
            (subpath u v g)`;;

let PATH_INTEGRABLE_SUBPATH = `!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> f path_integrable_on (subpath u v g)`;;

let HAS_INTEGRAL_PATH_INTEGRAL_SUBPATH = `!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
        drop u <= drop v
        ==> (((\x. f(g x) * vector_derivative g (at x))) has_integral
             path_integral (subpath u v g) f)
            (interval[u,v])`;;

let PATH_INTEGRAL_SUBPATH_INTEGRAL = `!f g u v.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
        drop u <= drop v
        ==> path_integral (subpath u v g) f =
            integral (interval[u,v])
                     (\x. f(g x) * vector_derivative g (at x))`;;

let PATH_INTEGRAL_SUBPATH_COMBINE = `!f g u v w.
        valid_path g /\ f path_integrable_on g /\
        u IN interval[vec 0,vec 1] /\
        v IN interval[vec 0,vec 1] /\
        w IN interval[vec 0,vec 1]
        ==> path_integral (subpath u v g) f + path_integral (subpath v w g) f =
            path_integral (subpath u w g) f`;;

let PATH_INTEGRAL_INTEGRAL = `!f g. path_integral g f =
         integral (interval [vec 0,vec 1])
                  (\x. f (g x) * vector_derivative g (at x))`;;

(* ------------------------------------------------------------------------- *)
(* Easier to reason about segments via convex hulls.                         *)
(* ------------------------------------------------------------------------- *)

let SEGMENTS_SUBSET_CONVEX_HULL = `!a b c. segment[a,b] SUBSET (convex hull {a,b,c}) /\
           segment[a,c] SUBSET (convex hull {a,b,c}) /\
           segment[b,c] SUBSET (convex hull {a,b,c}) /\
           segment[b,a] SUBSET (convex hull {a,b,c}) /\
           segment[c,a] SUBSET (convex hull {a,b,c}) /\
           segment[c,b] SUBSET (convex hull {a,b,c})`;;

let POINTS_IN_CONVEX_HULL = `!x s. x IN s ==> x IN convex hull s`;;

let CONVEX_HULL_SUBSET = `(!x. x IN s ==> x IN convex hull t)
   ==> (convex hull s) SUBSET (convex hull t)`;;

let NOT_IN_INTERIOR_CONVEX_HULL_3 = `!a b c:complex. ~(a IN interior(convex hull {a,b,c})) /\
                   ~(b IN interior(convex hull {a,b,c})) /\
                   ~(c IN interior(convex hull {a,b,c}))`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy's theorem where there's a primitive.                               *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_PRIMITIVE_LEMMA = `!f f' g a b s.
        ~(interval[a,b] = {}) /\
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s)) /\
        g piecewise_differentiable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> g(x) IN s)
        ==> ((\x. f'(g x) * vector_derivative g (at x within interval[a,b]))
             has_integral (f(g b) - f(g a))) (interval[a,b])`;;

let PATH_INTEGRAL_PRIMITIVE = `!f f' g s.
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s)) /\
        valid_path g /\ (path_image g) SUBSET s
        ==> (f' has_path_integral (f(pathfinish g) - f(pathstart g))) (g)`;;

let CAUCHY_THEOREM_PRIMITIVE = `!f f' g s.
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s)) /\
        valid_path g /\ (path_image g) SUBSET s /\
        pathfinish g = pathstart g
        ==> (f' has_path_integral Cx(&0)) (g)`;;

(* ------------------------------------------------------------------------- *)
(* Existence of path integral for continuous function.                       *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRABLE_CONTINUOUS_LINEPATH = `!f a b. f continuous_on segment[a,b]
           ==> f path_integrable_on (linepath(a,b))`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetical combining theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_CONST_LINEPATH = `!a b c. ((\x. c) has_path_integral (c * (b - a))) (linepath(a,b))`;;

let HAS_PATH_INTEGRAL_NEG = `!f i g. (f has_path_integral i) g
           ==> ((\x. --(f x)) has_path_integral (--i)) g`;;

let HAS_PATH_INTEGRAL_ADD = `!f1 i1 f2 i2 g.
        (f1 has_path_integral i1) g /\ (f2 has_path_integral i2) g
        ==> ((\x. f1(x) + f2(x)) has_path_integral (i1 + i2)) g`;;

let HAS_PATH_INTEGRAL_SUB = `!f1 i1 f2 i2 g.
        (f1 has_path_integral i1) g /\ (f2 has_path_integral i2) g
         ==> ((\x. f1(x) - f2(x)) has_path_integral (i1 - i2)) g`;;

let HAS_PATH_INTEGRAL_COMPLEX_LMUL = `!f g i c. (f has_path_integral i) g
             ==> ((\x. c * f x) has_path_integral (c * i)) g`;;

let HAS_PATH_INTEGRAL_COMPLEX_RMUL = `!f g i c. (f has_path_integral i) g
             ==> ((\x. f x * c) has_path_integral (i * c)) g`;;

let HAS_PATH_INTEGRAL_COMPLEX_DIV = `!f g i c. (f has_path_integral i) g
             ==> ((\x. f x / c) has_path_integral (i / c)) g`;;

let HAS_PATH_INTEGRAL_EQ = `!f g p y.
        (!x. x IN path_image p ==> f x = g x) /\
        (f has_path_integral y) p
        ==> (g has_path_integral y) p`;;

let HAS_PATH_INTEGRAL_BOUND_LINEPATH = `!f i a b B.
        (f has_path_integral i) (linepath(a,b)) /\
        &0 <= B /\ (!x. x IN segment[a,b] ==> norm(f x) <= B)
        ==> norm(i) <= B * norm(b - a)`;;

let HAS_PATH_INTEGRAL_BOUND_LINEPATH_STRONG = `!f i a b B k.
        FINITE k /\
        (f has_path_integral i) (linepath(a,b)) /\
        &0 <= B /\ (!x. x IN segment[a,b] DIFF k ==> norm(f x) <= B)
        ==> norm(i) <= B * norm(b - a)`;;

let HAS_PATH_INTEGRAL_0 = `!g. ((\x. Cx(&0)) has_path_integral Cx(&0)) g`;;

let HAS_PATH_INTEGRAL_IS_0 = `!f g. (!z. z IN path_image g ==> f(z) = Cx(&0))
         ==> (f has_path_integral Cx(&0)) g`;;

let HAS_PATH_INTEGRAL_VSUM = `!f p s. FINITE s /\ (!a. a IN s ==> (f a has_path_integral i a) p)
           ==> ((\x. vsum s (\a. f a x)) has_path_integral vsum s i) p`;;

(* ------------------------------------------------------------------------- *)
(* Same thing non-relationally.                                              *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_CONST_LINEPATH = `!a b c. path_integral (linepath(a,b)) (\x. c) = c * (b - a)`;;

let PATH_INTEGRAL_NEG = `!f g. f path_integrable_on g
         ==> path_integral g (\x. --(f x)) = --(path_integral g f)`;;

let PATH_INTEGRAL_ADD = `!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> path_integral g (\x. f1(x) + f2(x)) =
                path_integral g f1 + path_integral g f2`;;

let PATH_INTEGRAL_SUB = `!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> path_integral g (\x. f1(x) - f2(x)) =
                path_integral g f1 - path_integral g f2`;;

let PATH_INTEGRAL_COMPLEX_LMUL = `!f g c.  f path_integrable_on g
           ==> path_integral g (\x. c * f x) = c * path_integral g f`;;

let PATH_INTEGRAL_COMPLEX_RMUL = `!f g c.  f path_integrable_on g
           ==> path_integral g (\x. f x * c) = path_integral g f * c`;;

let PATH_INTEGRAL_COMPLEX_DIV = `!f g c.  f path_integrable_on g
           ==> path_integral g (\x. f x / c) = path_integral g f / c`;;

let PATH_INTEGRAL_EQ = `!f g p.
        (!x. x IN path_image p ==> f x = g x)
        ==> path_integral p f = path_integral p g`;;

let PATH_INTEGRAL_EQ_0 = `!f g. (!z. z IN path_image g ==> f(z) = Cx(&0))
         ==> path_integral g f = Cx(&0)`;;

let PATH_INTEGRAL_BOUND_LINEPATH = `!f a b.
        f path_integrable_on (linepath(a,b)) /\
        &0 <= B /\ (!x. x IN segment[a,b] ==> norm(f x) <= B)
        ==> norm(path_integral (linepath(a,b)) f) <= B * norm(b - a)`;;

let PATH_INTEGRAL_0 = `!g. path_integral g (\x. Cx(&0)) = Cx(&0)`;;

let PATH_INTEGRAL_VSUM = `!f p s. FINITE s /\ (!a. a IN s ==> (f a) path_integrable_on p)
           ==> path_integral p (\x. vsum s (\a. f a x)) =
                vsum s (\a. path_integral p (f a))`;;

let PATH_INTEGRABLE_EQ = `!f g p. (!x. x IN path_image p ==> f x = g x) /\ f path_integrable_on p
           ==> g path_integrable_on p`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic theorems for path integrability.                               *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRABLE_NEG = `!f g. f path_integrable_on g
           ==> (\x. --(f x)) path_integrable_on g`;;

let PATH_INTEGRABLE_ADD = `!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> (\x. f1(x) + f2(x)) path_integrable_on g`;;

let PATH_INTEGRABLE_SUB = `!f1 f2 g.
        f1 path_integrable_on g /\ f2 path_integrable_on g
        ==> (\x. f1(x) - f2(x)) path_integrable_on g`;;

let PATH_INTEGRABLE_COMPLEX_LMUL = `!f g c. f path_integrable_on g
             ==> (\x. c * f x) path_integrable_on g`;;

let PATH_INTEGRABLE_COMPLEX_RMUL = `!f g c. f path_integrable_on g
             ==> (\x. f x * c) path_integrable_on g`;;

let PATH_INTEGRABLE_COMPLEX_DIV = `!f g c. f path_integrable_on g
             ==> (\x. f x / c) path_integrable_on g`;;

let PATH_INTEGRABLE_VSUM = `!f g s. FINITE s /\ (!a. a IN s ==> f a path_integrable_on g)
           ==> (\x. vsum s (\a. f a x)) path_integrable_on g`;;

(* ------------------------------------------------------------------------- *)
(* Considering a path integral "backwards".                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_REVERSE_LINEPATH = `!f a b i.
        (f has_path_integral i) (linepath(a,b))
        ==> (f has_path_integral (--i)) (linepath(b,a))`;;

let PATH_INTEGRAL_REVERSE_LINEPATH = `!f a b.
        f continuous_on (segment[a,b])
        ==> path_integral(linepath(a,b)) f =
            --(path_integral(linepath(b,a)) f)`;;

(* ------------------------------------------------------------------------- *)
(* Splitting a path integral in a flat way.                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_SPLIT = `!f a b c i j k.
        &0 <= k /\ k <= &1 /\ c - a = k % (b - a) /\
        (f has_path_integral i) (linepath(a,c)) /\
        (f has_path_integral j) (linepath(c,b))
        ==> (f has_path_integral (i + j)) (linepath(a,b))`;;

let PATH_INTEGRAL_SPLIT = `!f a b c k.
        &0 <= k /\ k <= &1 /\ c - a = k % (b - a) /\
        f continuous_on (segment[a,b])
        ==> path_integral(linepath(a,b)) f =
            path_integral(linepath(a,c)) f +
            path_integral(linepath(c,b)) f`;;

let PATH_INTEGRAL_SPLIT_LINEPATH = `!f a b c.
        f continuous_on segment[a,b] /\ c IN segment[a,b]
        ==> path_integral(linepath (a,b)) f =
            path_integral(linepath (a,c)) f +
            path_integral(linepath (c,b)) f`;;

(* ------------------------------------------------------------------------- *)
(* The special case of midpoints used in the main quadrisection.             *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_MIDPOINT = `!f a b i j.
        (f has_path_integral i) (linepath(a,midpoint(a,b))) /\
        (f has_path_integral j) (linepath(midpoint(a,b),b))
        ==> (f has_path_integral (i + j)) (linepath(a,b))`;;

let PATH_INTEGRAL_MIDPOINT = `!f a b.
        f continuous_on (segment[a,b])
        ==> path_integral(linepath(a,b)) f =
            path_integral(linepath(a,midpoint(a,b))) f +
            path_integral(linepath(midpoint(a,b),b)) f`;;

(* ------------------------------------------------------------------------- *)
(* A couple of special case lemmas that are useful below.                    *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_LINEAR_HAS_CHAIN_INTEGRAL = `!a b c m d. ((\x. m * x + d) has_path_integral Cx(&0))
         (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a))`;;

let HAS_CHAIN_INTEGRAL_CHAIN_INTEGRAL = `!f i a b c d.
        (f has_path_integral i)
        (linepath(a,b) ++ linepath(b,c) ++ linepath(c,d))
        ==> path_integral (linepath(a,b)) f +
            path_integral (linepath(b,c)) f +
            path_integral (linepath(c,d)) f = i`;;

(* ------------------------------------------------------------------------- *)
(* Reversing the order in a double path integral. The condition is           *)
(* stronger than needed but it's often true in typical situations.           *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_SWAP = `!f g h.
    (\y. f (fstcart y) (sndcart y)) continuous_on
    (path_image g PCROSS path_image h) /\
    valid_path g /\ valid_path h /\
    (\t. vector_derivative g (at t)) continuous_on interval[vec 0,vec 1] /\
    (\t. vector_derivative h (at t)) continuous_on interval[vec 0,vec 1]
    ==> path_integral g (\w. path_integral h (f w)) =
        path_integral h (\z. path_integral g (\w. f w z))`;;

(* ------------------------------------------------------------------------- *)
(* The key quadrisection step.                                               *)
(* ------------------------------------------------------------------------- *)

let NORM_SUM_LEMMA = `norm(a + b + c + d:complex) >= e
   ==> norm(a) >= e / &4 \/
       norm(b) >= e / &4 \/
       norm(c) >= e / &4 \/
       norm(d) >= e / &4`;;

let CAUCHY_THEOREM_QUADRISECTION = `!f a b c e K.
        f continuous_on (convex hull {a,b,c}) /\
        dist (a,b) <= K /\
        dist (b,c) <= K /\
        dist (c,a) <= K /\
        norm(path_integral(linepath(a,b)) f +
             path_integral(linepath(b,c)) f +
             path_integral(linepath(c,a)) f) >= e * K pow 2
        ==> ?a' b' c'. a' IN convex hull {a,b,c} /\
                       b' IN convex hull {a,b,c} /\
                       c' IN convex hull {a,b,c} /\
                       dist(a',b') <= K / &2 /\
                       dist(b',c') <= K / &2 /\
                       dist(c',a') <= K / &2 /\
                       norm(path_integral(linepath(a',b')) f +
                            path_integral(linepath(b',c')) f +
                            path_integral(linepath(c',a')) f)
                        >= e * (K / &2) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Yet at small enough scales this cannot be the case.                       *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_POINTS_CLOSER = `!a b c x y:real^N.
        x IN convex hull {a,b,c} /\
        y IN convex hull {a,b,c}
        ==> norm(x - y) <= norm(a - b) \/
            norm(x - y) <= norm(b - c) \/
            norm(x - y) <= norm(c - a)`;;

let HOLOMORPHIC_POINT_SMALL_TRIANGLE = `!f s x e.
        x IN s /\ f continuous_on s /\
        f complex_differentiable (at x within s) /\
        &0 < e
        ==> ?k. &0 < k /\
                !a b c. dist(a,b) <= k /\ dist(b,c) <= k /\ dist(c,a) <= k /\
                        x IN convex hull {a,b,c} /\ convex hull {a,b,c} SUBSET s
                        ==> norm(path_integral(linepath(a,b)) f +
                                 path_integral(linepath(b,c)) f +
                                 path_integral(linepath(c,a)) f)
                            <= e * (dist(a,b) + dist(b,c) + dist(c,a)) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Hence the most basic theorem for a triangle.                              *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_TRIANGLE = `!f a b c.
        f holomorphic_on (convex hull {a,b,c})
        ==> (f has_path_integral Cx(&0))
            (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a))`;;

(* ------------------------------------------------------------------------- *)
(* Version needing function holomorphic in interior only.                    *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_FLAT_LEMMA = `!f a b c k.
        f continuous_on convex hull {a,b,c} /\ c - a = k % (b - a) /\ &0 <= k
        ==> path_integral (linepath(a,b)) f +
            path_integral (linepath(b,c)) f +
            path_integral (linepath(c,a)) f = Cx(&0)`;;

let CAUCHY_THEOREM_FLAT = `!f a b c k.
        f continuous_on convex hull {a,b,c} /\ c - a = k % (b - a)
        ==> path_integral (linepath(a,b)) f +
            path_integral (linepath(b,c)) f +
            path_integral (linepath(c,a)) f = Cx(&0)`;;

let CAUCHY_THEOREM_TRIANGLE_INTERIOR = `!f a b c.
        f continuous_on (convex hull {a,b,c}) /\
        f holomorphic_on interior (convex hull {a,b,c})
        ==> (f has_path_integral Cx(&0))
            (linepath(a,b) ++ linepath(b,c) ++ linepath(c,a))`;;

(* ------------------------------------------------------------------------- *)
(* Version allowing finite number of exceptional points.                     *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_TRIANGLE_COFINITE = `!f s a b c.
        f continuous_on (convex hull {a,b,c}) /\
        FINITE s /\
        (!x. x IN interior(convex hull {a,b,c}) DIFF s
             ==> f complex_differentiable (at x))
        ==> (f has_path_integral Cx(&0))
            (linepath (a,b) ++ linepath(b,c) ++ linepath(c,a))`;;

(* ------------------------------------------------------------------------- *)
(* Existence of a primitive.                                                 *)
(* ------------------------------------------------------------------------- *)

let STARLIKE_CONVEX_SUBSET = `!s a b c:real^N.
        a IN s /\ segment[b,c] SUBSET s /\
        (!x. x IN s ==> segment[a,x] SUBSET s)
        ==> convex hull {a,b,c} SUBSET s`;;

let TRIANGLE_PATH_INTEGRALS_STARLIKE_PRIMITIVE = `!f s a.
      a IN s /\ open s /\ f continuous_on s /\
      (!z. z IN s ==> segment[a,z] SUBSET s) /\
      (!b c. segment[b,c] SUBSET s
             ==> path_integral (linepath(a,b)) f +
                 path_integral (linepath(b,c)) f +
                 path_integral (linepath(c,a)) f = Cx(&0))
      ==> ?g. !z. z IN s ==> (g has_complex_derivative f(z)) (at z)`;;

let HOLOMORPHIC_STARLIKE_PRIMITIVE = `!f s k. open s /\ starlike s /\ FINITE k /\ f continuous_on s /\
           (!x. x IN s DIFF k ==> f complex_differentiable at x)
           ==> ?g. !x. x IN s ==> (g has_complex_derivative f(x)) (at x)`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy's theorem for an open starlike set.                                *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_STARLIKE = `!f s k g. open s /\ starlike s /\ FINITE k /\ f continuous_on s /\
             (!x. x IN s DIFF k ==> f complex_differentiable at x) /\
             valid_path g /\ (path_image g) SUBSET s /\
             pathfinish g = pathstart g
             ==> (f has_path_integral Cx(&0)) (g)`;;

let CAUCHY_THEOREM_STARLIKE_SIMPLE = `!f s g. open s /\ starlike s /\ f holomorphic_on s /\
           valid_path g /\ (path_image g) SUBSET s /\
           pathfinish g = pathstart g
           ==> (f has_path_integral Cx(&0)) (g)`;;

(* ------------------------------------------------------------------------- *)
(* For a convex set we can avoid assuming openness and boundary analyticity. *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_PATH_INTEGRALS_CONVEX_PRIMITIVE = `!f s a.
      a IN s /\ convex s /\ f continuous_on s /\
      (!b c. b IN s /\ c IN s
             ==> path_integral (linepath(a,b)) f +
                 path_integral (linepath(b,c)) f +
                 path_integral (linepath(c,a)) f = Cx(&0))
      ==> ?g. !z. z IN s ==> (g has_complex_derivative f(z)) (at z within s)`;;

let PATHINTEGRAL_CONVEX_PRIMITIVE = `!f s. convex s /\ f continuous_on s /\
         (!a b c. a IN s /\ b IN s /\ c IN s
                  ==>  (f has_path_integral Cx(&0))
                       (linepath (a,b) ++ linepath(b,c) ++ linepath(c,a)))
         ==> ?g. !x. x IN s
                     ==> (g has_complex_derivative f(x)) (at x within s)`;;

let HOLOMORPHIC_CONVEX_PRIMITIVE = `!f s k. convex s /\ FINITE k /\ f continuous_on s /\
           (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x)
           ==> ?g. !x. x IN s
                       ==> (g has_complex_derivative f(x)) (at x within s)`;;

let CAUCHY_THEOREM_CONVEX = `!f s k g. convex s /\ FINITE k /\ f continuous_on s /\
             (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x) /\
             valid_path g /\ (path_image g) SUBSET s /\
             pathfinish g = pathstart g
             ==> (f has_path_integral Cx(&0)) (g)`;;

let CAUCHY_THEOREM_CONVEX_SIMPLE = `!f s g. convex s /\ f holomorphic_on s /\
           valid_path g /\ (path_image g) SUBSET s /\
           pathfinish g = pathstart g
           ==> (f has_path_integral Cx(&0)) (g)`;;

(* ------------------------------------------------------------------------- *)
(* In particular for a disc.                                                 *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_DISC = `!f g k a e.
        FINITE k /\ f continuous_on cball(a,e) /\
        (!x. x IN ball(a,e) DIFF k ==> f complex_differentiable at x) /\
        valid_path g /\ (path_image g) SUBSET cball(a,e) /\
        pathfinish g = pathstart g
        ==> (f has_path_integral Cx(&0)) (g)`;;

let CAUCHY_THEOREM_DISC_SIMPLE = `!f g a e.
        f holomorphic_on ball(a,e) /\
        valid_path g /\ (path_image g) SUBSET ball(a,e) /\
        pathfinish g = pathstart g
        ==> (f has_path_integral Cx(&0)) (g)`;;

(* ------------------------------------------------------------------------- *)
(* Generalize integrability to local primitives.                             *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_LOCAL_PRIMITIVE_LEMMA = `!f f' g s a b.
        (!x. x IN s ==> (f has_complex_derivative f' x) (at x within s)) /\
        g piecewise_differentiable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> g(x) IN s)
        ==> (\x. f' (g x) * vector_derivative g (at x within interval[a,b]))
            integrable_on interval[a,b]`;;

let PATH_INTEGRAL_LOCAL_PRIMITIVE_ANY = `!f g s a b.
    (!x. x IN s
         ==> ?d h. &0 < d /\
                   !y. norm(y - x) < d
                       ==> (h has_complex_derivative f(y)) (at y within s)) /\
    g piecewise_differentiable_on interval[a,b] /\
    (!x. x IN interval[a,b] ==> g(x) IN s)
    ==> (\x. f(g x) * vector_derivative g (at x)) integrable_on interval[a,b]`;;

let PATH_INTEGRAL_LOCAL_PRIMITIVE = `!f g s.
        (!x. x IN s
         ==> ?d h. &0 < d /\
                   !y. norm(y - x) < d
                       ==> (h has_complex_derivative f(y)) (at y within s)) /\
        valid_path g /\ (path_image g) SUBSET s
        ==> f path_integrable_on g`;;

(* ------------------------------------------------------------------------- *)
(* In particular if a function is holomorphic.                               *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRABLE_HOLOMORPHIC = `!f g s k.
        open s /\ FINITE k /\
        f continuous_on s /\
        (!x. x IN s DIFF k ==> f complex_differentiable at x) /\
        valid_path g /\ path_image g SUBSET s
        ==> f path_integrable_on g`;;

let PATH_INTEGRABLE_HOLOMORPHIC_SIMPLE = `!f g s. open s /\ f holomorphic_on s /\ valid_path g /\ path_image g SUBSET s
           ==> f path_integrable_on g`;;

(* ------------------------------------------------------------------------- *)
(* Key fact that path integral is the same for a "nearby" path. This is the  *)
(* main lemma for the homotopy form of Cauchy's theorem and is also useful   *)
(* if we want "without loss of generality" to assume some niceness of our    *)
(* path (e.g. smoothness). It can also be used to define the integrals of    *)
(* analytic functions over arbitrary continuous paths. This is just done for *)
(* winding numbers now; I'm not sure if it's worth going further with that.  *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_NEARBY_ENDS = `(!s p.
      open s /\ path p /\ path_image p SUBSET s
      ==> ?d. &0 < d /\
              !g h. valid_path g /\ valid_path h /\
                    (!t. t IN interval[vec 0,vec 1]
                         ==> norm(g t - p t) < d /\ norm(h t - p t) < d) /\
                    pathstart h = pathstart g /\ pathfinish h = pathfinish g
                    ==> path_image g SUBSET s /\
                        path_image h SUBSET s /\
                        !f. f holomorphic_on s
                            ==> path_integral h f = path_integral g f)`
and PATH_INTEGRAL_NEARBY_LOOP = `(!s p.
      open s /\ path p /\ path_image p SUBSET s
      ==> ?d. &0 < d /\
              !g h. valid_path g /\ valid_path h /\
                    (!t. t IN interval[vec 0,vec 1]
                         ==> norm(g t - p t) < d /\ norm(h t - p t) < d) /\
                    pathfinish g = pathstart g /\ pathfinish h = pathstart h
                    ==> path_image g SUBSET s /\
                        path_image h SUBSET s /\
                        !f. f holomorphic_on s
                            ==> path_integral h f = path_integral g f)`;;

(* ------------------------------------------------------------------------- *)
(* Hence we can treat even non-rectifiable paths as having a "length"        *)
(* for bounds on analytic functions in open sets.                            *)
(* ------------------------------------------------------------------------- *)

let VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION = `!p:real^1->complex.
     vector_polynomial_function p ==> valid_path p`;;

let PATH_INTEGRAL_BOUND_EXISTS = `!s g. open s /\ valid_path g /\ path_image g SUBSET s
         ==> ?L. &0 < L /\
                 !f B. f holomorphic_on s /\ (!z. z IN s ==> norm(f z) <= B)
                       ==> norm(path_integral g f) <= L * B`;;

(* ------------------------------------------------------------------------- *)
(* Winding number.                                                           *)
(* ------------------------------------------------------------------------- *)

let winding_number = new_definition
 `winding_number(g,z) =
    @n. !e. &0 < e
            ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                    pathstart p = pathstart g /\
                    pathfinish p = pathfinish g /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(g t - p t) < e) /\
                    path_integral p (\w. Cx(&1) / (w - z)) =
                    Cx(&2) * Cx(pi) * ii * n`;;

let CX_2PII_NZ = `~(Cx(&2) * Cx(pi) * ii = Cx(&0))`;;

let PATH_INTEGRABLE_INVERSEDIFF = `!g z. valid_path g /\ ~(z IN path_image g)
         ==> (\w. Cx(&1) / (w - z)) path_integrable_on g`;;

let WINDING_NUMBER = `!g z e.
        path g /\ ~(z IN path_image g) /\ &0 < e
         ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                 pathstart p = pathstart g /\
                 pathfinish p = pathfinish g /\
                 (!t. t IN interval[vec 0,vec 1] ==> norm(g t - p t) < e) /\
                 path_integral p (\w. Cx(&1) / (w - z)) =
                 Cx(&2) * Cx(pi) * ii * winding_number(g,z)`;;

let WINDING_NUMBER_UNIQUE = `!g z n.
        path g /\ ~(z IN path_image g) /\
        (!e. &0 < e
             ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                     pathstart p = pathstart g /\
                     pathfinish p = pathfinish g /\
                     (!t. t IN interval[vec 0,vec 1]
                          ==> norm(g t - p t) < e) /\
                     path_integral p (\w. Cx(&1) / (w - z)) =
                     Cx(&2) * Cx(pi) * ii * n)
        ==> winding_number(g,z) = n`;;

let WINDING_NUMBER_UNIQUE_LOOP = `!g z e n.
        path g /\ ~(z IN path_image g) /\ pathfinish g = pathstart g /\
        (!e. &0 < e
             ==> ?p. valid_path p /\ ~(z IN path_image p) /\
                     pathfinish p = pathstart p /\
                     (!t. t IN interval[vec 0,vec 1]
                          ==> norm(g t - p t) < e) /\
                     path_integral p (\w. Cx(&1) / (w - z)) =
                     Cx(&2) * Cx(pi) * ii * n)
        ==> winding_number(g,z) = n`;;

let WINDING_NUMBER_VALID_PATH = `!g z. valid_path g /\ ~(z IN path_image g)
         ==> winding_number(g,z) =
             Cx(&1) / (Cx(&2) * Cx(pi) * ii) *
             path_integral g (\w. Cx(&1) / (w - z))`;;

let HAS_PATH_INTEGRAL_WINDING_NUMBER = `!g z. valid_path g /\ ~(z IN path_image g)
         ==> ((\w. Cx(&1) / (w - z)) has_path_integral
              (Cx(&2) * Cx(pi) * ii * winding_number(g,z))) g`;;

let WINDING_NUMBER_TRIVIAL = `!a z. ~(z = a) ==> winding_number(linepath(a,a),z) = Cx(&0)`;;

let WINDING_NUMBER_JOIN = `!g1 g2 z.
        path g1 /\ path g2 /\ pathfinish g1 = pathstart g2 /\
        ~(z IN path_image g1) /\ ~(z IN path_image g2)
        ==> winding_number(g1 ++ g2,z) =
            winding_number(g1,z) + winding_number(g2,z)`;;

let WINDING_NUMBER_REVERSEPATH = `!g z. path g /\ ~(z IN path_image g)
         ==> winding_number(reversepath g,z) = --(winding_number(g,z))`;;

let WINDING_NUMBER_SHIFTPATH = `!g a z. path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g) /\
           a IN interval[vec 0,vec 1]
           ==> winding_number(shiftpath a g,z) = winding_number(g,z)`;;

let WINDING_NUMBER_SPLIT_LINEPATH = `!a b c z.
    c IN segment[a,b] /\ ~(z IN segment[a,b])
    ==> winding_number(linepath(a,b),z) =
        winding_number(linepath(a,c),z) +
        winding_number(linepath(c,b),z)`;;

let WINDING_NUMBER_EQUAL = `!p q z. (!t. t IN interval[vec 0,vec 1] ==> p t = q t)
           ==> winding_number(p,z) = winding_number(q,z)`;;

let WINDING_NUMBER_OFFSET = `!p z. winding_number(p,z) = winding_number((\w. p w - z),Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* A combined theorem deducing several things piecewise.                     *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_JOIN_POS_COMBINED = `!g1 g2 z.
       (valid_path g1 /\
        ~(z IN path_image g1) /\
        &0 < Re(winding_number(g1,z))) /\
       (valid_path g2 /\
        ~(z IN path_image g2) /\
        &0 < Re(winding_number(g2,z))) /\
       pathfinish g1 = pathstart g2
       ==> valid_path(g1 ++ g2) /\
           ~(z IN path_image(g1 ++ g2)) /\
           &0 < Re(winding_number(g1 ++ g2,z))`;;

(* ------------------------------------------------------------------------- *)
(* Useful sufficient conditions for the winding number to be positive etc.   *)
(* ------------------------------------------------------------------------- *)

let RE_WINDING_NUMBER = `!g z. valid_path g /\ ~(z IN path_image g)
         ==> Re(winding_number(g,z)) =
             Im(path_integral g (\w. Cx(&1) / (w - z))) / (&2 * pi)`;;

let WINDING_NUMBER_POS_LE = `!g z. valid_path g /\ ~(z IN path_image g) /\
         (!x. x IN interval(vec 0,vec 1)
              ==> &0 <= Im(vector_derivative g (at x) * cnj(g x - z)))
         ==> &0 <= Re(winding_number(g,z))`;;

let WINDING_NUMBER_POS_LT_LEMMA = `!g z e. valid_path g /\ ~(z IN path_image g) /\ &0 < e /\
           (!x. x IN interval(vec 0,vec 1)
                ==> e <= Im(vector_derivative g (at x) / (g x - z)))
           ==> &0 < Re(winding_number(g,z))`;;

let WINDING_NUMBER_POS_LT = `!g z e. valid_path g /\ ~(z IN path_image g) /\ &0 < e /\
           (!x. x IN interval(vec 0,vec 1)
                ==> e <= Im(vector_derivative g (at x) * cnj(g x - z)))
           ==> &0 < Re(winding_number(g,z))`;;

(* ------------------------------------------------------------------------- *)
(* The winding number is an integer (proof from Ahlfors's book).             *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_AHLFORS_LEMMA = `!g a b.
        g piecewise_differentiable_on interval [a,b] /\
        drop a <= drop b /\ (!x. x IN interval [a,b] ==> ~(g x = z))
        ==> (\x. vector_derivative g (at x within interval[a,b]) / (g(x) - z))
            integrable_on interval[a,b] /\
            cexp(--(integral (interval[a,b])
                        (\x. vector_derivative g (at x within interval[a,b]) /
                               (g(x) - z)))) *
            (g(b) - z) = g(a) - z`;;

let WINDING_NUMBER_AHLFORS = `!g z a b.
        g piecewise_differentiable_on interval [a,b] /\
        drop a <= drop b /\ (!x. x IN interval [a,b] ==> ~(g x = z))
        ==> (\x. vector_derivative g (at x) / (g(x) - z))
            integrable_on interval[a,b] /\
            cexp(--(integral (interval[a,b])
                             (\x. vector_derivative g (at x) / (g(x) - z)))) *
            (g(b) - z) = g(a) - z`;;

let WINDING_NUMBER_AHLFORS_FULL = `!p z. path p /\ ~(z IN path_image p)
         ==> pathfinish p - z =
             cexp(Cx(&2) * Cx pi * ii * winding_number(p,z)) *
             (pathstart p - z)`;;

(* ------------------------------------------------------------------------- *)
(* State in terms of complex integers. Note the useful equality version.     *)
(* ------------------------------------------------------------------------- *)

let complex_integer = new_definition
 `complex_integer z <=> integer(Re z) /\ Im z = &0`;;

let COMPLEX_INTEGER = `complex_integer z <=> ?n. integer n /\ z = Cx n`;;

let INTEGER_WINDING_NUMBER_EQ = `!g z. path g /\ ~(z IN path_image g)
         ==> (complex_integer(winding_number(g,z)) <=>
              pathfinish g = pathstart g)`;;

let INTEGER_WINDING_NUMBER = `!g z. path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g)
         ==> complex_integer(winding_number(g,z))`;;

(* ------------------------------------------------------------------------- *)
(* For |WN| >= 1 the path must contain points in every direction.            *)
(* We can thus bound the WN of a path that doesn't meet some "cut".          *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_POS_MEETS = `!g z. valid_path g /\ ~(z IN path_image g) /\
         Re(winding_number(g,z)) >= &1
         ==> !w. ~(w = z)
                 ==> ?a. &0 < a /\ z + (Cx a * (w - z)) IN path_image g`;;

let WINDING_NUMBER_BIG_MEETS = `!g z. valid_path g /\ ~(z IN path_image g) /\
         abs(Re(winding_number(g,z))) >= &1
         ==> !w. ~(w = z)
                 ==> ?a. &0 < a /\ z + (Cx a * (w - z)) IN path_image g`;;

let WINDING_NUMBER_LT_1 = `!g w z. valid_path g /\ ~(z IN path_image g) /\ ~(w = z) /\
           (!a. &0 < a ==> ~(z + (Cx a * (w - z)) IN path_image g))
           ==> Re(winding_number(g,z)) < &1`;;

(* ------------------------------------------------------------------------- *)
(* One way of proving that WN=1 for a loop.                                  *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_EQ_1 = `!g z. valid_path g /\ ~(z IN path_image g) /\ pathfinish g = pathstart g /\
         &0 < Re(winding_number(g,z)) /\ Re(winding_number(g,z)) < &2
         ==> winding_number(g,z) = Cx(&1)`;;

(* ------------------------------------------------------------------------- *)
(* Continuity of winding number and invariance on connected sets.            *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_WINDING_NUMBER = `!g z. path g /\ ~(z IN path_image g)
         ==> (\w. winding_number(g,w)) continuous (at z)`;;

let CONTINUOUS_ON_WINDING_NUMBER = `!g. path g
       ==> (\w. winding_number(g,w)) continuous_on
           ((:complex) DIFF path_image g)`;;

let WINDING_NUMBER_CONSTANT = `!s g. path g /\ pathfinish g = pathstart g /\
         connected s /\ s INTER path_image g = {}
         ==> ?k. !z. z IN s ==> winding_number(g,z) = k`;;

let WINDING_NUMBER_EQ = `!g s w z.
        path g /\ pathfinish g = pathstart g /\
        w IN s /\ z IN s /\ connected s /\ s INTER path_image g = {}
        ==> winding_number(g,w) = winding_number(g,z)`;;

let OPEN_WINDING_NUMBER_LEVELSETS = `!g k. path g /\ pathfinish g = pathstart g
         ==> open {z | ~(z IN path_image g) /\ winding_number(g,z) = k}`;;

(* ------------------------------------------------------------------------- *)
(* Winding number is zero "outside" a curve, in various senses.              *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_ZERO_IN_OUTSIDE = `!g z. path g /\ pathfinish g = pathstart g /\ z IN outside(path_image g)
         ==> winding_number(g,z) = Cx(&0)`;;

let WINDING_NUMBER_ZERO_OUTSIDE = `!g s z. path g /\ convex s /\ pathfinish g = pathstart g /\
           ~(z IN s) /\ path_image g SUBSET s
           ==> winding_number(g,z) = Cx(&0)`;;

let WINDING_NUMBER_ZERO_ATINFINITY = `!g. path g /\ pathfinish g = pathstart g
       ==> ?B. !z. B <= norm(z) ==> winding_number(g,z) = Cx(&0)`;;

let WINDING_NUMBER_ZERO_POINT = `!g s. path g /\ pathfinish g = pathstart g /\
         open s /\ path_image g SUBSET s
         ==> ?z. z IN s /\ winding_number(g,z) = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* If a path winds round a set, it winds rounds its inside.                  *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_AROUND_INSIDE = `!g s z.
        path g /\ pathfinish g = pathstart g /\
        closed s /\ connected s /\ s INTER path_image g = {} /\
        z IN s /\ ~(winding_number(g,z) = Cx(&0))
        ==> !w. w IN s UNION inside(s)
                ==> winding_number(g,w) = winding_number(g,z)`;;

(* ------------------------------------------------------------------------- *)
(* Bounding a WN by 1/2 for a path and point in opposite halfspaces.         *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_SUBPATH_CONTINUOUS = `!g z. valid_path g /\ ~(z IN path_image g)
         ==> (\a. winding_number(subpath (vec 0) a g,z)) continuous_on
             interval[vec 0,vec 1]`;;

let WINDING_NUMBER_IVT_POS = `!g z w.
        valid_path g /\ ~(z IN path_image g) /\
        &0 <= w /\ w <= Re(winding_number(g,z))
        ==> ?t. t IN interval[vec 0,vec 1] /\
                Re(winding_number(subpath (vec 0) t g,z)) = w`;;

let WINDING_NUMBER_IVT_NEG = `!g z w.
        valid_path g /\ ~(z IN path_image g) /\
        Re(winding_number(g,z)) <= w /\ w <= &0
        ==> ?t. t IN interval[vec 0,vec 1] /\
                Re(winding_number(subpath (vec 0) t g,z)) = w`;;

let WINDING_NUMBER_IVT_ABS = `!g z w.
        valid_path g /\ ~(z IN path_image g) /\
        &0 <= w /\ w <= abs(Re(winding_number(g,z)))
        ==> ?t. t IN interval[vec 0,vec 1] /\
                abs(Re(winding_number(subpath (vec 0) t g,z))) = w`;;

let WINDING_NUMBER_LT_HALF = `!g z a b.
        valid_path g /\ a dot z <= b /\ path_image g SUBSET {w | a dot w > b}
        ==> abs(Re(winding_number(g,z))) < &1 / &2`;;

let WINDING_NUMBER_LE_HALF = `!g z a b.
        valid_path g /\ ~(z IN path_image g) /\
        ~(a = vec 0) /\ a dot z <= b /\ path_image g SUBSET {w | a dot w >= b}
        ==> abs(Re(winding_number(g,z))) <= &1 / &2`;;

let WINDING_NUMBER_LT_HALF_LINEPATH = `!a b z.
        ~(z IN segment[a,b])
        ==> abs(Re(winding_number(linepath(a,b),z))) < &1 / &2`;;

(* ------------------------------------------------------------------------- *)
(* Positivity of WN for a linepath.                                          *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_LINEPATH_POS_LT = `!a b z. &0 < Im((b - a) * cnj(b - z))
           ==> &0 < Re(winding_number(linepath(a,b),z))`;;

(* ------------------------------------------------------------------------- *)
(* Winding number for a triangle.                                            *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_TRIANGLE = `!a b c z.
        z IN interior(convex hull {a,b,c})
        ==> winding_number(linepath(a,b) ++ linepath(b,c) ++ linepath(c,a),z) =
            if &0 < Im((b - a) * cnj (b - z)) then Cx(&1) else --Cx(&1)`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy's integral formula, again for a convex enclosing set.              *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INTEGRAL_FORMULA_WEAK = `!f s k g z.
        convex s /\ FINITE k /\ f continuous_on s /\
        (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x) /\
        z IN interior(s) DIFF k /\
        valid_path g /\ (path_image g) SUBSET (s DELETE z) /\
        pathfinish g = pathstart g
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`;;

let CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE = `!f s g z.
        convex s /\ f holomorphic_on s /\
        z IN interior(s) /\
        valid_path g /\ (path_image g) SUBSET (s DELETE z) /\
        pathfinish g = pathstart g
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy forms of Cauchy's theorem. The first two proofs are almost the   *)
(* same and could potentially be unified with a little more work.            *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_THEOREM_HOMOTOPIC_PATHS = `!f g h s.
        open s /\ f holomorphic_on s /\
        valid_path g /\ valid_path h /\ homotopic_paths s g h
        ==> path_integral g f = path_integral h f`;;

let CAUCHY_THEOREM_HOMOTOPIC_LOOPS = `!f g h s.
        open s /\ f holomorphic_on s /\
        valid_path g /\ valid_path h /\ homotopic_loops s g h
        ==> path_integral g f = path_integral h f`;;

let CAUCHY_THEOREM_NULL_HOMOTOPIC = `!f g s a.
        open s /\ f holomorphic_on s /\ a IN s /\ valid_path g /\
        homotopic_loops s g (linepath(a,a))
        ==> (f has_path_integral Cx(&0)) g`;;

let CAUCHY_THEOREM_SIMPLY_CONNECTED = `!f g s. open s /\ simply_connected s /\ f holomorphic_on s /\
           valid_path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g
           ==> (f has_path_integral Cx(&0)) g`;;

(* ------------------------------------------------------------------------- *)
(* More winding number properties, including the fact that it's +-1 inside   *)
(* a simple closed curve.                                                    *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_HOMOTOPIC_PATHS = `!g h z. homotopic_paths ((:complex) DELETE z) g h
           ==> winding_number(g,z) = winding_number(h,z)`;;

let WINDING_NUMBER_HOMOTOPIC_LOOPS = `!g h z. homotopic_loops ((:complex) DELETE z) g h
           ==> winding_number(g,z) = winding_number(h,z)`;;

let WINDING_NUMBER_PATHS_LINEAR_EQ = `!g h z.
        path g /\ path h /\
        pathstart h = pathstart g /\
        pathfinish h = pathfinish g /\
        (!t. t IN interval[vec 0,vec 1] ==> ~(z IN segment[g t,h t]))
        ==> winding_number(h,z) = winding_number(g,z)`;;

let WINDING_NUMBER_LOOPS_LINEAR_EQ = `!g h z.
        path g /\ path h /\
        pathfinish g = pathstart g /\
        pathfinish h = pathstart h /\
        (!t. t IN interval[vec 0,vec 1] ==> ~(z IN segment[g t,h t]))
        ==> winding_number(h,z) = winding_number(g,z)`;;

let WINDING_NUMBER_NEARBY_PATHS_EQ = `!g h z.
        path g /\ path h /\
        pathstart h = pathstart g /\
        pathfinish h = pathfinish g /\
        (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < norm(g t - z))
        ==> winding_number(h,z) = winding_number(g,z)`;;

let WINDING_NUMBER_NEARBY_LOOPS_EQ = `!g h z.
        path g /\ path h /\
        pathfinish g = pathstart g /\
        pathfinish h = pathstart h /\
        (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < norm(g t - z))
        ==> winding_number(h,z) = winding_number(g,z)`;;

let WINDING_NUMBER_SUBPATH_COMBINE = `!g u v w z.
        path g /\ ~(z IN path_image g) /\
        u IN interval [vec 0,vec 1] /\
        v IN interval [vec 0,vec 1] /\
        w IN interval [vec 0,vec 1]
        ==> winding_number(subpath u v g,z) +
            winding_number(subpath v w g,z) =
            winding_number(subpath u w g,z)`;;

let WINDING_NUMBER_STRONG = `!g z e.
        path g /\ ~(z IN path_image g) /\ &0 < e
         ==> ?p. vector_polynomial_function p /\ valid_path p /\
                 ~(z IN path_image p) /\
                 pathstart p = pathstart g /\
                 pathfinish p = pathfinish g /\
                 (!t. t IN interval[vec 0,vec 1] ==> norm(g t - p t) < e) /\
                 path_integral p (\w. Cx(&1) / (w - z)) =
                 Cx(&2) * Cx(pi) * ii * winding_number(g,z)`;;

let WINDING_NUMBER_FROM_INNERPATH = `!c1 c2 c a b z:complex d.
        ~(a = b) /\
        simple_path c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        simple_path c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        simple_path c /\ pathstart c = a /\ pathfinish c = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c1 INTER path_image c = {a,b} /\
        path_image c2 INTER path_image c = {a,b} /\
        ~(path_image c INTER inside(path_image c1 UNION path_image c2) = {}) /\
        z IN inside(path_image c1 UNION path_image c) /\
        winding_number(c1 ++ reversepath c,z) = d /\ ~(d = Cx(&0))
        ==> z IN inside(path_image c1 UNION path_image c2) /\
            winding_number(c1 ++ reversepath c2,z) = d`;;

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE = `!g. simple_path g
       ==> (!z. z IN inside(path_image g) ==> winding_number(g,z) = Cx(&1)) \/
           (!z. z IN inside(path_image g) ==> winding_number(g,z) = --Cx(&1))`;;

let SIMPLE_CLOSED_PATH_ABS_WINDING_NUMBER_INSIDE = `!g z. simple_path g /\ z IN inside(path_image g)
         ==> abs(Re(winding_number(g,z))) = &1`;;

let SIMPLE_CLOSED_PATH_NORM_WINDING_NUMBER_INSIDE = `!g z. simple_path g /\ z IN inside(path_image g)
         ==> norm(winding_number(g,z)) = &1`;;

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_CASES = `!g z. simple_path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g)
         ==> winding_number(g,z) IN {--Cx(&1),Cx(&0),Cx(&1)}`;;

let SIMPLE_CLOSED_PATH_WINDING_NUMBER_POS = `!g z. simple_path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g) /\
         &0 < Re(winding_number(g,z))
         ==> winding_number(g,z) = Cx(&1)`;;

let SIMPLY_CONNECTED_IMP_WINDING_NUMBER_ZERO = `!s g z. simply_connected s /\
           path g /\ path_image g SUBSET s /\
           pathfinish g = pathstart g /\ ~(z IN s)
           ==> winding_number(g,z) = Cx(&0)`;;

let NO_BOUNDED_CONNECTED_COMPONENT_IMP_WINDING_NUMBER_ZERO = `!s. ~(?z. ~(z IN s) /\ bounded(connected_component ((:complex) DIFF s) z))
       ==> !g z. path g /\ path_image g SUBSET s /\
                 pathfinish g = pathstart g /\ ~(z IN s)
                 ==> winding_number(g,z) = Cx(&0)`;;

let NO_BOUNDED_PATH_COMPONENT_IMP_WINDING_NUMBER_ZERO = `!s. ~(?z. ~(z IN s) /\ bounded(path_component ((:complex) DIFF s) z))
       ==> !g z. path g /\ path_image g SUBSET s /\
                 pathfinish g = pathstart g /\ ~(z IN s)
                 ==> winding_number(g,z) = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* Partial circle path.                                                      *)
(* ------------------------------------------------------------------------- *)

let partcirclepath = new_definition
 `partcirclepath(z,r,s,t) =
    \x. z + Cx(r) * cexp(ii * linepath(Cx(s),Cx(t)) x)`;;

let PATHSTART_PARTCIRCLEPATH = `!r z s t. pathstart(partcirclepath(z,r,s,t)) =
                z + Cx(r) * cexp(ii * Cx(s))`;;

let PATHFINISH_PARTCIRCLEPATH = `!r z s t. pathfinish(partcirclepath(z,r,s,t)) =
                z + Cx(r) * cexp(ii * Cx(t))`;;

let HAS_VECTOR_DERIVATIVE_PARTCIRCLEPATH = `!z r s t x.
        ((partcirclepath(z,r,s,t)) has_vector_derivative
         (ii * Cx(r) * (Cx t - Cx s) * cexp(ii * linepath(Cx(s),Cx(t)) x)))
        (at x)`;;

let VECTOR_DERIVATIVE_PARTCIRCLEPATH = `!z r s t x.
        vector_derivative (partcirclepath(z,r,s,t)) (at x) =
        ii * Cx(r) * (Cx t - Cx s) * cexp(ii * linepath(Cx(s),Cx(t)) x)`;;

let VALID_PATH_PARTCIRCLEPATH = `!z r s t. valid_path(partcirclepath(z,r,s,t))`;;

let PATH_PARTCIRCLEPATH = `!z r s t. path(partcirclepath(z,r,s,t))`;;

let PATH_IMAGE_PARTCIRCLEPATH = `!z r s t.
        &0 <= r /\ s <= t
        ==> path_image(partcirclepath(z,r,s,t)) =
                {z + Cx(r) * cexp(ii * Cx x) | s <= x /\ x <= t}`;;

let PATH_IMAGE_PARTCIRCLEPATH_SUBSET_ABS = `!z r s t. path_image(partcirclepath(z,r,s,t)) SUBSET sphere(z,abs r)`;;

let PATH_IMAGE_PARTCIRCLEPATH_SUBSET = `!z r s t.
        &0 <= r
        ==> path_image(partcirclepath(z,r,s,t)) SUBSET sphere(z,r)`;;

let IN_PATH_IMAGE_PARTCIRCLEPATH = `!z r s t w.
        &0 <= r /\ w IN path_image(partcirclepath(z,r,s,t))
        ==> norm(w - z) = r`;;

let RECTIFIABLE_PATH_PARTCIRCLEPATH,PATH_LENGTH_PARTCIRCLEPATH =
  let lemma = `(partcirclepath (z,r,s,t) has_vector_derivative
      ii * Cx(t - s) * partcirclepath (Cx(&0),r,s,t) u) (at u)` in
  let RECTIFIABLE_PATH_PARTCIRCLEPATH = `!z r s t. rectifiable_path(partcirclepath(z,r,s,t))` in
  let PATH_LENGTH_PARTCIRCLEPATH = `!z r s t. path_length(partcirclepath(z,r,s,t)) = abs(r * (t - s))` in
  RECTIFIABLE_PATH_PARTCIRCLEPATH,PATH_LENGTH_PARTCIRCLEPATH;;

let HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH_STRONG = `!f i z r s t B k.
        FINITE k /\
        (f has_path_integral i) (partcirclepath(z,r,s,t)) /\
        &0 <= B /\ &0 < r /\ s <= t /\
        (!x. x IN path_image(partcirclepath(z,r,s,t)) DIFF k
             ==> norm(f x) <= B)
        ==> norm(i) <= B * r * (t - s)`;;

let HAS_PATH_INTEGRAL_BOUND_PARTCIRCLEPATH = `!f i z r s t B.
        (f has_path_integral i) (partcirclepath(z,r,s,t)) /\
        &0 <= B /\ &0 < r /\ s <= t /\
        (!x. x IN path_image(partcirclepath(z,r,s,t))
             ==> norm(f x) <= B)
        ==> norm(i) <= B * r * (t - s)`;;

let PATH_INTEGRABLE_CONTINUOUS_PARTCIRCLEPATH = `!f z r s t. f continuous_on path_image(partcirclepath(z,r,s,t))
               ==> f path_integrable_on (partcirclepath(z,r,s,t))`;;

let WINDING_NUMBER_PARTCIRCLEPATH_POS_LT = `!r z s t w.
        s < t /\ norm(w - z) < r
        ==> &0 < Re(winding_number(partcirclepath(z,r,s,t),w))`;;

let SIMPLE_PATH_PARTCIRCLEPATH = `!z r s t. simple_path(partcirclepath(z,r,s,t)) <=>
                ~(r = &0) /\ ~(s = t) /\ abs(s - t) <= &2 * pi`;;

let ARC_PARTCIRCLEPATH = `!z r s t. ~(r = &0) /\ ~(s = t) /\ abs(s - t) < &2 * pi
             ==> arc(partcirclepath(z,r,s,t))`;;

let WINDING_NUMBER_PARTCIRCLEPATH = `!z r s t.
        ~(r = &0)
        ==> winding_number (partcirclepath(z,r,s,t),z) =
            Cx((t - s) / (&2 * pi))`;;

(* ------------------------------------------------------------------------- *)
(* Special case of one complete circle.                                      *)
(* ------------------------------------------------------------------------- *)

let circlepath = new_definition
 `circlepath(z,r) = partcirclepath(z,r,&0,&2 * pi)`;;

let CIRCLEPATH = `circlepath(z,r) = \x. z + Cx(r) * cexp(Cx(&2) * Cx pi * ii * Cx(drop x))`;;

let PATH_CIRCLEPATH = `!z r. path(circlepath(z,r))`;;

let PATHSTART_CIRCLEPATH = `!r z. pathstart(circlepath(z,r)) = z + Cx(r)`;;

let PATHFINISH_CIRCLEPATH = `!r z. pathfinish(circlepath(z,r)) = z + Cx(r)`;;

let HAS_VECTOR_DERIVATIVE_CIRCLEPATH = `((circlepath (z,r)) has_vector_derivative
    (Cx(&2) * Cx(pi) * ii * Cx(r) * cexp(Cx(&2) * Cx pi * ii * Cx(drop x))))
   (at x)`;;

let VECTOR_DERIVATIVE_CIRCLEPATH = `vector_derivative (circlepath (z,r)) (at x) =
        Cx(&2) * Cx(pi) * ii * Cx(r) * cexp(Cx(&2) * Cx pi * ii * Cx(drop x))`;;

let VALID_PATH_CIRCLEPATH = `!z r. valid_path (circlepath(z,r))`;;

let RECTIFIABLE_PATH_CIRCLEPATH = `!z r. rectifiable_path(circlepath(z,r))`;;

let PATH_LENGTH_CIRCLEPATH = `!z r. path_length(circlepath(z,r)) = &2 * pi * abs r`;;

let SHIFTPATH_CIRCLEPATH = `!a z r.
        shiftpath a (circlepath(z,r)) =
        partcirclepath(z,r,&2 * pi * drop a,&2 * pi * (drop a + &1))`;;

let PATH_IMAGE_CIRCLEPATH = `!z r. &0 <= r ==> path_image (circlepath(z,r)) = sphere(z,r)`;;

let HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH_STRONG = `!f i z r B k.
        FINITE k /\
        (f has_path_integral i) (circlepath(z,r)) /\
        &0 <= B /\ &0 < r /\
        (!x. norm(x - z) = r /\ ~(x IN k) ==> norm(f x) <= B)
        ==> norm(i) <= B * (&2 * pi * r)`;;

let HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH = `!f i z r B.
        (f has_path_integral i) (circlepath(z,r)) /\
        &0 <= B /\ &0 < r /\ (!x. norm(x - z) = r ==> norm(f x) <= B)
        ==> norm(i) <= B * (&2 * pi * r)`;;

let PATH_INTEGRABLE_CONTINUOUS_CIRCLEPATH = `!f z r. f continuous_on path_image(circlepath(z,r))
           ==> f path_integrable_on (circlepath(z,r))`;;

let SIMPLE_PATH_CIRCLEPATH = `!z r. simple_path(circlepath(z,r)) <=> ~(r = &0)`;;

let WINDING_NUMBER_CIRCLEPATH = `!z r w. norm(w - z) < r ==> winding_number(circlepath(z,r),w) = Cx(&1)`;;

(* ------------------------------------------------------------------------- *)
(* We can also deduce this; it's pushed to this late point in the build      *)
(* just for the convenience of using "circlepath".                           *)
(* ------------------------------------------------------------------------- *)

let RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX = `!s:real^N->bool.
        bounded s /\ convex s /\ aff_dim s = &2
        ==> ?g. simple_path g /\
                rectifiable_path g /\
                pathfinish g = pathstart g /\
                path_image g = relative_frontier s`;;

let RECTIFIABLE_LOOP_FRONTIER_CONVEX = `!s:real^2->bool.
        bounded s /\ convex s /\ ~(interior s = {})
        ==> ?g. simple_path g /\
                rectifiable_path g /\
                pathfinish g = pathstart g /\
                path_image g = frontier s`;;

let RECTIFIABLE_PATH_FRONTIER_CONVEX = `!s:real^2->bool.
        bounded s /\ convex s /\ ~(s = {})
        ==> ?g. rectifiable_path g /\
                pathfinish g = pathstart g /\
                path_image g = frontier s`;;

(* ------------------------------------------------------------------------- *)
(* Hence the Cauchy formula for points inside a circle.                      *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INTEGRAL_CIRCLEPATH = `!f z r w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> ((\u. f(u) / (u - w)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * f(w))) (circlepath(z,r))`;;

let CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE = `!f z r w.
        f holomorphic_on cball(z,r) /\ w IN ball(z,r)
        ==> ((\u. f(u) / (u - w)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * f(w))) (circlepath(z,r))`;;

(* ------------------------------------------------------------------------- *)
(* Uniform convergence of path integral when the derivative of the path is   *)
(* bounded, and in particular for the special case of a circle.              *)
(* ------------------------------------------------------------------------- *)

let PATH_INTEGRAL_UNIFORM_LIMIT = `!net f B g l.
     ~(trivial_limit net) /\ valid_path g /\
     (!t. t IN interval[vec 0,vec 1]
          ==> norm(vector_derivative g (at t)) <= B) /\
     eventually (\n:A. (f n) path_integrable_on g) net /\
     (!e. &0 < e
          ==> eventually (\n. !x. x IN path_image g
                                  ==> norm(f n x - l x) < e) net)
     ==> l path_integrable_on g /\
         ((\n. path_integral g (f n)) --> path_integral g l) net`;;

let PATH_INTEGRAL_UNIFORM_LIMIT_CIRCLEPATH = `!net f l z r.
     &0 < r /\ ~(trivial_limit net) /\
     eventually (\n:A. (f n) path_integrable_on circlepath(z,r)) net /\
     (!e. &0 < e
          ==> eventually (\n. !x. x IN path_image (circlepath(z,r))
                                  ==> norm(f n x - l x) < e) net)
     ==> l path_integrable_on circlepath(z,r) /\
         ((\n. path_integral (circlepath(z,r)) (f n))
          --> path_integral (circlepath(z,r)) l) net`;;

(* ------------------------------------------------------------------------- *)
(* General stepping result for derivative formulas.                          *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_NEXT_DERIVATIVE = `!f' f g s k B.
     ~(k = 0) /\
     open s /\ valid_path g /\
     (!t. t IN interval[vec 0,vec 1]
          ==> norm(vector_derivative g (at t)) <= B) /\
     f' continuous_on path_image g /\
     (!w. w IN s DIFF path_image g
          ==> ((\u. f'(u) / (u - w) pow k) has_path_integral f w) g)
     ==> !w. w IN s DIFF path_image g
             ==> (\u. f'(u) / (u - w) pow (k + 1)) path_integrable_on g /\
                 (f has_complex_derivative
                  (Cx(&k) * path_integral g (\u. f'(u) / (u - w) pow (k + 1))))
                  (at w)`;;

let CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH = `!f g z r k.
        ~(k = 0) /\
        (f continuous_on path_image(circlepath(z,r))) /\
        (!w. w IN ball(z,r)
             ==> ((\u. f(u) / (u - w) pow k) has_path_integral g w)
                 (circlepath(z,r)))
        ==> !w. w IN ball(z,r)
                ==> (\u. f(u) / (u - w) pow (k + 1)) path_integrable_on
                            (circlepath(z,r)) /\
                    (g has_complex_derivative
                     (Cx(&k) * path_integral(circlepath(z,r))
                                 (\u. f(u) / (u - w) pow (k + 1))))
                    (at w)`;;

(* ------------------------------------------------------------------------- *)
(* In particular, the first derivative formula.                              *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_DERIVATIVE_INTEGRAL_CIRCLEPATH = `!f z r w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> (\u. f(u) / (u - w) pow 2) path_integrable_on circlepath(z,r) /\
            (f has_complex_derivative
                (Cx(&1) / (Cx(&2) * Cx(pi) * ii) *
                 path_integral(circlepath(z,r)) (\u. f(u) / (u - w) pow 2)))
            (at w)`;;

(* ------------------------------------------------------------------------- *)
(* Existence of all higher derivatives.                                      *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_DERIVATIVE = `!f f' s. open s /\ (!z. z IN s ==> (f has_complex_derivative f'(z)) (at z))
            ==> f' holomorphic_on s`;;

let HOLOMORPHIC_COMPLEX_DERIVATIVE = `!f s. open s /\ f holomorphic_on s
         ==> (complex_derivative f) holomorphic_on s`;;

let ANALYTIC_COMPLEX_DERIVATIVE = `!f s. f analytic_on s ==> (complex_derivative f) analytic_on s`;;

let HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE = `!f s n. open s /\ f holomorphic_on s
           ==> (higher_complex_derivative n f) holomorphic_on s`;;

let ANALYTIC_HIGHER_COMPLEX_DERIVATIVE = `!f s n. f analytic_on s ==> (higher_complex_derivative n f) analytic_on s`;;

let HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE = `!f s x n. open s /\ f holomorphic_on s /\ x IN s
             ==> ((higher_complex_derivative n f) has_complex_derivative
                          (higher_complex_derivative (SUC n) f x)) (at x)`;;

(* ------------------------------------------------------------------------- *)
(* Morera's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let MORERA_LOCAL_TRIANGLE_GEN = `!f s.
     (!z. z IN s
          ==> ?e a. &0 < e /\ z IN ball(a,e) /\ f continuous_on ball(a,e) /\
                    !b c. segment[b,c] SUBSET ball(a,e)
                           ==> path_integral (linepath(a,b)) f +
                               path_integral (linepath(b,c)) f +
                               path_integral (linepath(c,a)) f = Cx(&0))
     ==> f analytic_on s`;;

let MORERA_LOCAL_TRIANGLE = `!f s. (!z. z IN s
              ==> ?t. open t /\ z IN t /\ f continuous_on t /\
                      !a b c. convex hull {a,b,c} SUBSET t
                              ==> path_integral (linepath(a,b)) f +
                                  path_integral (linepath(b,c)) f +
                                  path_integral (linepath(c,a)) f = Cx(&0))
         ==> f analytic_on s`;;

let MORERA_TRIANGLE = `!f s. open s /\ f continuous_on s /\
         (!a b c. convex hull {a,b,c} SUBSET s
                  ==> path_integral (linepath(a,b)) f +
                      path_integral (linepath(b,c)) f +
                      path_integral (linepath(c,a)) f = Cx(&0))
         ==> f analytic_on s`;;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for higher derivatives including Leibniz rule.         *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_EQ_ITER = `!n. higher_complex_derivative n = ITER n complex_derivative`;;

let HIGHER_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE = `!f m n. higher_complex_derivative m (higher_complex_derivative n f) =
           higher_complex_derivative (m + n) f`;;

let higher_complex_derivative_alt = `(!f. higher_complex_derivative 0 f = f) /\
   (!f n. higher_complex_derivative (SUC n) f =
          higher_complex_derivative n (complex_derivative f))`;;

let HIGHER_COMPLEX_DERIVATIVE_LINEAR = `!c n. higher_complex_derivative n (\w. c * w) =
    \z. if n = 0 then c * z else if n = 1 then c else (Cx(&0))`;;

let HIGHER_COMPLEX_DERIVATIVE_CONST = `!i c. higher_complex_derivative i (\w.c) = \w. if i=0 then c else Cx(&0)`;;

let HIGHER_COMPLEX_DERIVATIVE_ID = `!z i. higher_complex_derivative i (\w.w) z =
            if i = 0 then z else if i = 1 then Cx(&1) else Cx(&0)`;;

let HAS_COMPLEX_DERIVATIVE_ITER_1 = `!f n z. f z = z /\ (f has_complex_derivative Cx(&1)) (at z)
           ==> (ITER n f has_complex_derivative Cx(&1)) (at z)`;;

let HIGHER_COMPLEX_DERIVATIVE_NEG = `!f s n z.
     open s /\ f holomorphic_on s /\ z IN s
     ==> higher_complex_derivative n (\w. --(f w)) z =
                --(higher_complex_derivative n f z)`;;

let HIGHER_COMPLEX_DERIVATIVE_ADD = `!f g s n z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s ==>
     higher_complex_derivative n (\w. f w + g w) z  =
     higher_complex_derivative n f z + higher_complex_derivative n g z`;;

let HIGHER_COMPLEX_DERIVATIVE_SUB = `!f g s n z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s ==>
     higher_complex_derivative n (\w. f w - g w) z  =
     higher_complex_derivative n f z - higher_complex_derivative n g z`;;

let HIGHER_COMPLEX_DERIVATIVE_MUL = `!f g s n z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s
     ==> higher_complex_derivative n (\w. f w * g w) z =
         vsum (0..n) (\i. Cx(&(binom(n,i))) *
                          higher_complex_derivative i f z *
                          higher_complex_derivative (n-i) g z)`;;

let HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN = `!f g s i z.
     open s /\ f holomorphic_on s /\ g holomorphic_on s /\
     (!w. w IN s ==> f w = g w) /\ z IN s
     ==> higher_complex_derivative i f z = higher_complex_derivative i g z`;;

let HIGHER_COMPLEX_DERIVATIVE_COMPOSE_LINEAR = `!f u s t n z.
     f holomorphic_on t /\ open s /\ open t /\
     (!w. w IN s ==> u * w IN t) /\ z IN s
     ==> higher_complex_derivative n (\w. f (u * w)) z =
         u pow n * higher_complex_derivative n f (u * z)`;;

let HIGHER_COMPLEX_DERIVATIVE_ADD_AT = `!f g n z.
     f analytic_on {z} /\ g analytic_on {z}
     ==> higher_complex_derivative n (\w. f w + g w) z =
         higher_complex_derivative n f z +
         higher_complex_derivative n g z`;;

let HIGHER_COMPLEX_DERIVATIVE_SUB_AT = `!f g n z.
     f analytic_on {z} /\ g analytic_on {z}
     ==> higher_complex_derivative n (\w. f w - g w) z =
         higher_complex_derivative n f z -
         higher_complex_derivative n g z`;;

let HIGHER_COMPLEX_DERIVATIVE_NEG_AT = `!f n z.
     f analytic_on {z}
     ==> higher_complex_derivative n (\w. --(f w)) z =
         --(higher_complex_derivative n f z)`;;

let HIGHER_COMPLEX_DERIVATIVE_MUL_AT = `!f g n z.
     f analytic_on {z} /\ g analytic_on {z}
     ==> higher_complex_derivative n (\w. f w * g w) z =
         vsum (0..n) (\i. Cx(&(binom(n,i))) *
                          higher_complex_derivative i f z *
                          higher_complex_derivative (n-i) g z)`;;

(* ------------------------------------------------------------------------- *)
(* Nonexistence of isolated singularities and a stronger integral formula.   *)
(* ------------------------------------------------------------------------- *)

let NO_ISOLATED_SINGULARITY = `!f s k. open s /\ FINITE k /\
           f continuous_on s /\ f holomorphic_on (s DIFF k)
           ==> f holomorphic_on s`;;

let CAUCHY_INTEGRAL_FORMULA_CONVEX = `!f s k g z.
        convex s /\ FINITE k /\ f continuous_on s /\
        (!x. x IN interior(s) DIFF k ==> f complex_differentiable at x) /\
        z IN interior(s) /\
        valid_path g /\ (path_image g) SUBSET (s DELETE z) /\
        pathfinish g = pathstart g
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`;;

(* ------------------------------------------------------------------------- *)
(* Formula for higher derivatives.                                           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_HAS_PATH_INTEGRAL_HIGHER_DERIVATIVE_CIRCLEPATH = `!f z r k w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> ((\u. f(u) / (u - w) pow (k + 1))
             has_path_integral
             ((Cx(&2) * Cx(pi) * ii) / Cx(&(FACT k)) *
              higher_complex_derivative k f w))
            (circlepath(z,r))`;;

let CAUCHY_HIGHER_DERIVATIVE_INTEGRAL_CIRCLEPATH = `!f z r k w.
        f continuous_on cball(z,r) /\
        f holomorphic_on ball(z,r) /\
        w IN ball(z,r)
        ==> (\u. f(u) / (u - w) pow (k + 1))
                path_integrable_on circlepath(z,r) /\
            higher_complex_derivative k f w =
              Cx(&(FACT k)) / (Cx(&2) * Cx(pi) * ii) *
              path_integral(circlepath(z,r)) (\u. f(u) / (u - w) pow (k + 1))`;;

(* ------------------------------------------------------------------------- *)
(* A holomorphic function is analytic, i.e. has local power series.          *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_POWER_SERIES = `!f z w r.
     f holomorphic_on ball(z,r) /\ w IN ball(z,r)
     ==> ((\n. higher_complex_derivative n f z / Cx(&(FACT n)) * (w - z) pow n)
          sums f(w)) (from 0)`;;

(* ------------------------------------------------------------------------- *)
(* These weak Liouville versions don't even need the derivative formula.     *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_WEAK = `!f l. f holomorphic_on (:complex) /\ (f --> l) at_infinity
         ==> !z. f(z) = l`;;

let LIOUVILLE_WEAK_INVERSE = `!f. f holomorphic_on (:complex) /\
       (!B. eventually (\x. norm(f x) >= B) at_infinity)
       ==> ?z. f(z) = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* In particular we get the Fundamental Theorem of Algebra.                  *)
(* ------------------------------------------------------------------------- *)

let FTA = `!a n. a(0) = Cx(&0) \/ ~(!k. k IN 1..n ==> a(k) = Cx(&0))
         ==> ?z. vsum(0..n) (\i. a(i) * z pow i) = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* Weierstrass convergence theorem.                                          *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_UNIFORM_LIMIT = `!net:(A net) f g z r.
        ~(trivial_limit net) /\
        eventually
           (\n. (f n) continuous_on cball(z,r) /\
                (f n) holomorphic_on ball(z,r))
           net /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN cball(z,r) ==> norm(f n x - g x) < e)
                            net)
        ==> g continuous_on cball(z,r) /\ g holomorphic_on ball(z,r)`;;

(* ------------------------------------------------------------------------- *)
(* Version showing that the limit is the limit of the derivatives.           *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_UNIFORM_LIMIT = `!net:(A net) f f' g z r.
        &0 < r /\ ~(trivial_limit net) /\
        eventually
          (\n. (f n) continuous_on cball(z,r) /\
               (!w. w IN ball(z,r)
                    ==> ((f n) has_complex_derivative (f' n w)) (at w)))
          net /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN cball(z,r) ==> norm(f n x - g x) < e)
                            net)
        ==> g continuous_on cball(z,r) /\
            ?g'. !w. w IN ball(z,r)
                     ==> (g has_complex_derivative (g' w)) (at w) /\
                         ((\n. f' n w) --> g' w) net`;;

(* ------------------------------------------------------------------------- *)
(* Some more simple/convenient versions for applications.                    *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_UNIFORM_SEQUENCE = `!f g s.
        open s /\
        (!n. (f n) holomorphic_on s) /\
        (!x. x IN s
             ==> ?d. &0 < d /\ cball(x,d) SUBSET s /\
                     !e. &0 < e
                         ==> eventually (\n. !y. y IN cball(x,d)
                                                 ==> norm(f n y - g y) < e)
                                        sequentially)
        ==> g holomorphic_on s`;;

let HAS_COMPLEX_DERIVATIVE_UNIFORM_SEQUENCE = `!f f' g s.
        open s /\
        (!n x. x IN s ==> ((f n) has_complex_derivative f' n x) (at x)) /\
        (!x. x IN s
             ==> ?d. &0 < d /\ cball(x,d) SUBSET s /\
                     !e. &0 < e
                         ==> eventually (\n. !y. y IN cball(x,d)
                                                 ==> norm(f n y - g y) < e)
                                        sequentially)
        ==> ?g'. !x. x IN s ==> (g has_complex_derivative g'(x)) (at x) /\
                                ((\n. f' n x) --> g'(x)) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* A one-stop shop for an analytic function defined by a series.             *)
(* ------------------------------------------------------------------------- *)

let SERIES_AND_DERIVATIVE_COMPARISON = `!f f' s k h.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n has_complex_derivative f' n x) (at x)) /\
     (?l. (lift o h sums l) k) /\
     (?N. !n x. N <= n /\ n IN k /\ x IN s ==> norm(f n x) <= h n)
          ==> ?g g'. !x. x IN s
                         ==> ((\n. f n x) sums g x) k /\
                             ((\n. f' n x) sums g' x) k /\
                             (g has_complex_derivative g' x) (at x)`;;

(* ------------------------------------------------------------------------- *)
(* A version where we only have local uniform/comparative convergence.       *)
(* ------------------------------------------------------------------------- *)

let SERIES_AND_DERIVATIVE_COMPARISON_LOCAL = `!f f' s k.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n has_complex_derivative f' n x) (at x)) /\
     (!x. x IN s
          ==> ?d h N. &0 < d /\ (?l. (lift o h sums l) k) /\
                      !n y. N <= n /\ n IN k /\ y IN ball(x,d)
                               ==> norm(f n y) <= h n)
     ==> ?g g'. !x. x IN s
                    ==> ((\n. f n x) sums g x) k /\
                        ((\n. f' n x) sums g' x) k /\
                        (g has_complex_derivative g' x) (at x)`;;

(* ------------------------------------------------------------------------- *)
(* Sometimes convenient to compare with a complex series of +ve reals.       *)
(* ------------------------------------------------------------------------- *)

let SERIES_AND_DERIVATIVE_COMPARISON_COMPLEX = `!f f' s k.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n has_complex_derivative f' n x) (at x)) /\
     (!x. x IN s
          ==> ?d h N. &0 < d /\ summable k h /\
                      (!n. n IN k ==> real(h n) /\ &0 <= Re(h n)) /\
                      (!n y. N <= n /\ n IN k /\ y IN ball(x,d)
                             ==> norm(f n y) <= norm(h n)))
     ==> ?g g'. !x. x IN s
                    ==> ((\n. f n x) sums g x) k /\
                        ((\n. f' n x) sums g' x) k /\
                        (g has_complex_derivative g' x) (at x)`;;

let SERIES_DIFFERENTIABLE_COMPARISON_COMPLEX = `!f s k.
     open s /\
     (!n x. n IN k /\ x IN s ==> (f n) complex_differentiable (at x)) /\
     (!x. x IN s
          ==> ?d h N. &0 < d /\ summable k h /\
                      (!n. n IN k ==> real(h n) /\ &0 <= Re(h n)) /\
                      (!n y. N <= n /\ n IN k /\ y IN ball(x,d)
                             ==> norm(f n y) <= norm(h n)))
     ==> ?g. !x. x IN s
                 ==> ((\n. f n x) sums g x) k /\
                      g complex_differentiable (at x)`;;

(* ------------------------------------------------------------------------- *)
(* In particular, a power series is analytic inside circle of convergence.   *)
(* ------------------------------------------------------------------------- *)

let POWER_SERIES_AND_DERIVATIVE_0 = `!k a r. summable k (\n. a(n) * Cx(r) pow n)
           ==> ?g g'.
                  !z. norm(z) < r
                      ==> ((\n. a(n) * z pow n) sums g(z)) k /\
                          ((\n. Cx(&n) * a(n) * z pow (n - 1)) sums g'(z)) k /\
                          (g has_complex_derivative g' z) (at z)`;;

let POWER_SERIES_AND_DERIVATIVE = `!k a r w.
        summable k (\n. a(n) * Cx(r) pow n)
        ==> ?g g'.
             !z. z IN ball(w,r)
                 ==> ((\n. a(n) * (z - w) pow n) sums g(z)) k /\
                     ((\n. Cx(&n) * a(n) * (z - w) pow (n - 1)) sums g'(z)) k /\
                     (g has_complex_derivative g' z) (at z)`;;

let POWER_SERIES_HOLOMORPHIC = `!a k f z r. (!w. w IN ball(z,r) ==> ((\n. a(n) * (w - z) pow n) sums f w) k)
               ==> f holomorphic_on ball(z,r)`;;

let HOLOMORPHIC_IFF_POWER_SERIES = `!f z r. f holomorphic_on ball(z,r) <=>
             !w. w IN ball(z,r)
                 ==> ((\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
                       (w - z) pow n) sums
                      f w)
                     (from 0)`;;

let POWER_SERIES_ANALYTIC = `!a k f z r. (!w. w IN ball(z,r) ==> ((\n. a(n) * (w - z) pow n) sums f w) k)
               ==> f analytic_on ball(z,r)`;;

let ANALYTIC_IFF_POWER_SERIES = `!f z r. f analytic_on ball(z,r) <=>
             !w. w IN ball(z,r)
                 ==> ((\n. higher_complex_derivative n f z / Cx(&(FACT n)) *
                       (w - z) pow n) sums
                      f w)
                     (from 0)`;;

let HIGHER_COMPLEX_DERIVATIVE_POWER_SERIES = `!f c r n.
        &0 < r /\ n IN k /\
        (!w. dist(w,z) < r ==> ((\i. c i * (w - z) pow i) sums f(w)) k)
        ==> higher_complex_derivative n f z / Cx(&(FACT n)) = c n`;;

(* ------------------------------------------------------------------------- *)
(* Taylor series for log. It's this late because we can more easily get      *)
(* a good error bound given the convergence of the series.                   *)
(* ------------------------------------------------------------------------- *)

let CLOG_CONVERGES = `!z. norm(z) < &1
       ==> ((\n. --Cx(&1) pow (n + 1) * z pow n / Cx(&n)) sums clog(Cx(&1) + z))
           (from 1)`;;

let CLOG_CONVERGES_STRONG = `!z. norm(z) <= &1 /\ ~(z = --Cx(&1))
       ==> ((\n. --Cx(&1) pow (n + 1) * z pow n / Cx(&n)) sums
            clog(Cx(&1) + z)) (from 1)`;;

let TAYLOR_CLOG = `!n z. norm(z) < &1
         ==> norm(clog(Cx(&1) + z) -
                  vsum(1..n) (\k. --Cx(&1) pow (k + 1) * z pow k / Cx(&k)))
             <= norm z pow (n + 1) / (&1 - norm z)`;;

let TAYLOR_CLOG_NEG = `!n z. norm(z) < &1
         ==> norm(clog(Cx(&1) - z) + vsum(1..n) (\k. z pow k / Cx(&k)))
              <= norm z pow (n + 1) / (&1 - norm z)`;;

let LOG2_APPROX_32 = `abs(log(&2) - &2977044471 / &4294967296) <= inv(&2 pow 32)`;;

(* ------------------------------------------------------------------------- *)
(* Taylor series for arctan.                                                 *)
(* ------------------------------------------------------------------------- *)

let CATN_CONVERGES_STRONG = `!z. norm z <= &1 /\ ~(z = ii) /\ ~(z = --ii)
       ==> ((\n. --Cx(&1) pow n / Cx(&(2 * n + 1)) * z pow (2 * n + 1))
            sums catn z) (from 0)`;;

let CATN_CONVERGES = `!z. norm(z) < &1
       ==> ((\n. --(Cx(&1)) pow n / Cx(&(2 * n + 1)) * z pow (2 * n + 1))
            sums catn(z)) (from 0)`;;

let TAYLOR_CATN = `!n z. norm(z) < &1
          ==> norm(catn z -
                   vsum(0..n) (\k. --(Cx(&1)) pow k / Cx(&(2 * k + 1)) *
                                   z pow (2 * k + 1)))
              <= norm(z) pow (2 * n + 3) /
                 ((&2 * &n + &3) * (&1 - norm z pow 2))`;;

(* ------------------------------------------------------------------------- *)
(* The classical limit for e and other useful limits.                        *)
(* ------------------------------------------------------------------------- *)

let CEXP_LIMIT = `!z. ((\n. (Cx(&1) + z / Cx(&n)) pow n) --> cexp(z)) sequentially`;;

let EXP_LIMIT = `!x. ((\n. (&1 + x / &n) pow n) ---> exp(x)) sequentially`;;

let LIM_LOGPLUS1_OVER_X = `((\x. clog(Cx(&1) + x) / x) --> Cx(&1)) (at(Cx(&0)))`;;

let LIM_N_MUL_SUB_CLOG = `!w z. ((\n. Cx(&n) * (clog(Cx(&n) + w) - clog(Cx(&n) + z))) --> w - z)
         sequentially`;;

let LIM_SUB_CLOG = `!w z. ((\n. clog(Cx(&n) + w) - clog(Cx(&n) + z)) --> Cx(&0)) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Equality between holomorphic functions, on open ball then connected set.  *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_FUN_EQ_ON_BALL = `!f g z r w.
     f holomorphic_on ball(z,r) /\ g holomorphic_on ball(z,r) /\
     w IN ball(z,r) /\
     (!n. higher_complex_derivative n f z = higher_complex_derivative n g z)
     ==> f w = g w`;;

let HOLOMORPHIC_FUN_EQ_0_ON_BALL = `!f z r w.
     w IN ball(z,r) /\ f holomorphic_on ball(z,r) /\
     (!n. higher_complex_derivative n f z = Cx(&0))
     ==> f w = Cx(&0)`;;

let HOLOMORPHIC_FUN_EQ_0_ON_CONNECTED = `!f s z.
        open s /\ connected s /\ f holomorphic_on s /\
        z IN s /\ (!n. higher_complex_derivative n f z = Cx(&0))
        ==> !w. w IN s ==> f w = Cx(&0)`;;

let HOLOMORPHIC_FUN_EQ_ON_CONNECTED = `!f g z s w.
     open s /\ connected s /\ f holomorphic_on s /\ g holomorphic_on s /\
     w IN s /\ z IN s /\
     (!n. higher_complex_derivative n f z = higher_complex_derivative n g z)
     ==> f w = g w`;;

let HOLOMORPHIC_FUN_EQ_CONST_ON_CONNECTED = `!f s z.
        open s /\
        connected s /\
        f holomorphic_on s /\
        z IN s /\
        (!n. 0 < n ==> higher_complex_derivative n f z = Cx(&0))
        ==> !w. w IN s ==> f w = f z`;;

(* ------------------------------------------------------------------------- *)
(* Some basic lemmas about poles/singularities.                              *)
(* ------------------------------------------------------------------------- *)

let POLE_LEMMA = `!f s a.
        f holomorphic_on s /\ a IN interior(s)
        ==> (\z. if z = a then complex_derivative f a
                 else (f(z) - f(a)) / (z - a)) holomorphic_on s`;;

let POLE_LEMMA_OPEN = `!f s a.
        open s /\ f holomorphic_on s
        ==> (\z. if z = a
                 then complex_derivative f a
                 else (f z - f a) / (z - a)) holomorphic_on s`;;

let POLE_THEOREM = `!f g s a.
        g holomorphic_on s /\ a IN interior(s) /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) holomorphic_on s`;;

let POLE_THEOREM_OPEN = `!f g s a.
        open s /\ g holomorphic_on s /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) holomorphic_on s`;;

let POLE_THEOREM_0 = `!f g s a.
        g holomorphic_on s /\ a IN interior(s) /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f holomorphic_on s`;;

let POLE_THEOREM_OPEN_0 = `!f g s a.
        open s /\ g holomorphic_on s /\
        (!z. z IN s /\ ~(z = a) ==> g(z) = (z - a) * f(z)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f holomorphic_on s`;;

let POLE_THEOREM_ANALYTIC = `!f g s a.
        g analytic_on s /\
        (!z. z IN s
             ==> ?d. &0 < d /\
                     !w. w IN ball(z,d) /\ ~(w = a) ==> g(w) = (w - a) * f(w))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) analytic_on s`;;

let POLE_THEOREM_ANALYTIC_0 = `!f g s a.
        g analytic_on s /\
        (!z. z IN s
             ==> ?d. &0 < d /\
                     !w. w IN ball(z,d) /\ ~(w = a)
                         ==> g(w) = (w - a) * f(w)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f analytic_on s`;;

let POLE_THEOREM_ANALYTIC_OPEN_SUPERSET = `!f g s a t.
        s SUBSET t /\ open t /\ g analytic_on s /\
        (!z. z IN t /\ ~(z = a) ==> g(z) = (z - a) * f(z))
        ==> (\z. if z = a then complex_derivative g a
                 else f(z) - g(a) / (z - a)) analytic_on s`;;

let POLE_THEOREM_ANALYTIC_OPEN_SUPERSET_0 = `!f g s a t.
        s SUBSET t /\ open t /\ g analytic_on s /\
        (!z. z IN t /\ ~(z = a) ==> g(z) = (z - a) * f(z)) /\
        f a = complex_derivative g a /\ g(a) = Cx(&0)
        ==> f analytic_on s`;;

let HOLOMORPHIC_ON_EXTEND_LIM = `(!f a s.
      f holomorphic_on (s DELETE a) /\ a IN interior s
      ==> ((?g. g holomorphic_on s /\ (!z. z IN s DELETE a ==> g z = f z)) <=>
           ((\z. (z - a) * f(z)) --> Cx(&0)) (at a)))`
and HOLOMORPHIC_ON_EXTEND_BOUNDED = `(!f a s.
      f holomorphic_on (s DELETE a) /\ a IN interior s
      ==> ((?g. g holomorphic_on s /\ (!z. z IN s DELETE a ==> g z = f z)) <=>
           (?B. eventually (\z. norm(f z) <= B) (at a))))`;;

(* ------------------------------------------------------------------------- *)
(* Power series for z / (e^z - 1), hence cotangent and tangent.              *)
(* ------------------------------------------------------------------------- *)

let ZBYEXPM1_CONVERGES = `!z. norm z < &2 * pi
       ==> ((\n. Cx(bernoulli n (&0)) / Cx(&(FACT n)) * z pow n) sums
            (if z = Cx(&0) then Cx(&1) else z / (cexp z - Cx(&1)))) (from 0)`;;

let ZBYEXPM1_CONVERGES_ALT = `!z. norm z < &2 * pi
       ==> ((\n. Cx(bernoulli (2 * n) (&0)) / Cx(&(FACT(2 * n))) *
                 z pow (2 * n)) sums
            (if z = Cx(&0) then Cx(&0)
             else z / (cexp z - Cx (&1)) + z / Cx(&2) - Cx(&1))) (from 1)`;;

let CCOT_CONVERGES = `!z. norm(z) < pi
       ==> ((\n. (--Cx(&4) pow n / Cx(&(FACT(2 * n))) *
                  Cx(bernoulli (2 * n) (&0))) * z pow (2 * n - 1))
            sums (Cx(&1) / ctan z - inv(z))) (from 1)`;;

let CTAN_CONVERGES = `!z. norm(z) < pi / &2
       ==> ((\n. ((Cx(&1) - Cx(&4) pow n) *
                  --Cx(&4) pow n / Cx(&(FACT(2 * n))) *
                  Cx(bernoulli (2 * n) (&0))) * z pow (2 * n - 1))
            sums ctan z) (from 1)`;;

(* ------------------------------------------------------------------------- *)
(* General, homology form of Cauchy's theorem. Proof is based on Dixon's,    *)
(* as presented in Lang's "Complex Analysis" book.                           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INTEGRAL_FORMULA_GLOBAL = `!f s g z.
        open s /\ f holomorphic_on s /\ z IN s /\
        valid_path g /\ pathfinish g = pathstart g /\
        path_image g SUBSET s DELETE z /\
        (!w. ~(w IN s) ==> winding_number(g,w) = Cx(&0))
        ==> ((\w. f(w) / (w - z)) has_path_integral
             (Cx(&2) * Cx(pi) * ii * winding_number(g,z) * f(z))) g`;;

let CAUCHY_THEOREM_GLOBAL = `!f s g.
        open s /\ f holomorphic_on s /\
        valid_path g /\ pathfinish g = pathstart g /\ path_image g SUBSET s /\
        (!z. ~(z IN s) ==> winding_number(g,z) = Cx(&0))
        ==> (f has_path_integral Cx(&0)) g`;;

let CAUCHY_THEOREM_GLOBAL_OUTSIDE = `!f s g.
        open s /\ f holomorphic_on s /\
        valid_path g /\ pathfinish g = pathstart g /\
        (!z. ~(z IN s) ==> z IN outside(path_image g))
        ==> (f has_path_integral Cx(&0)) g`;;

(* ------------------------------------------------------------------------- *)
(* Basic residue integrals.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_RESIDUE_INTEGRAL = `!g z n. valid_path g /\ ~(z IN path_image g) /\ pathfinish g = pathstart g
           ==> ((\w. inv(w - z) pow n) has_path_integral
                (if n = 1 then Cx(&2) * Cx pi * ii * winding_number(g,z)
                 else Cx(&0))) g`;;

let HAS_RESIDUE_INTEGRAL_INTEGER = `!g z n. valid_path g /\ ~(z IN path_image g) /\
           pathfinish g = pathstart g /\ complex_integer n
           ==> ((\w. (w - z) cpow n) has_path_integral
                (if n = --Cx(&1) then Cx(&2) * Cx pi * ii * winding_number(g,z)
                 else Cx(&0))) g`;;

(* ------------------------------------------------------------------------- *)
(* First Cartan Theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_COMP_LEMMA = `!f g z s t n i.
     open s /\ f holomorphic_on s /\ z IN s /\
     open t /\ g holomorphic_on t /\ (!w. w IN s ==> f w IN t) /\
     complex_derivative f z = Cx(&1) /\
     (!i. 1 < i /\ i <= n ==> higher_complex_derivative i f z = Cx(&0)) /\
     i <= n
     ==> higher_complex_derivative i (g o f) z =
         higher_complex_derivative i g (f z)`;;

let HIGHER_COMPLEX_DERIVATIVE_COMP_ITER_LEMMA = `!f s z n m i.
     open s /\ f holomorphic_on s /\ (!w. w IN s ==> f w IN s) /\
     z IN s /\ f z = z /\ complex_derivative f z = Cx(&1) /\
     (!i. 1 < i /\ i <= n ==> higher_complex_derivative i f z = Cx(&0)) /\
     i <= n
     ==> higher_complex_derivative i (ITER m f) z =
         higher_complex_derivative i f z`;;

let HIGHER_COMPLEX_DERIVATIVE_ITER_TOP_LEMMA = `!f s z n m.
     open s /\ f holomorphic_on s /\ (!w. w IN s ==> f w IN s) /\
     z IN s /\ f z = z /\ complex_derivative f z = Cx(&1) /\
     (!i. 1 < i /\ i < n ==> higher_complex_derivative i f z = Cx(&0)) /\
     1 < n
     ==> higher_complex_derivative n (ITER m f) z =
         Cx(&m) * higher_complex_derivative n f z`;;

let CAUCHY_HIGHER_COMPLEX_DERIVATIVE_BOUND = `!f z y r B0 n.
     &0 < r /\ 0 < n /\
     f holomorphic_on ball(z,r) /\
     f continuous_on cball(z,r) /\
     (!w. w IN ball(z,r) ==> f w IN ball(y,B0))
     ==> norm (higher_complex_derivative n f z) <= &(FACT n) * B0 / r pow n`;;

let FIRST_CARTAN_THM_DIM_1 = `!f s z w.
      open s /\ connected s /\ bounded s /\
      (!w. w IN s ==> f w IN s) /\ f holomorphic_on s /\
      z IN s /\ f z = z /\
      complex_derivative f z = Cx(&1) /\ w IN s
      ==> f w = w`;;

(* ------------------------------------------------------------------------- *)
(* Second Cartan Theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let SECOND_CARTAN_THM_DIM_1 = `!g f r.
     &0 < r /\
     g holomorphic_on ball(Cx(&0),r) /\
     (!z. z IN ball(Cx(&0),r) ==> g z IN ball(Cx(&0),r)) /\
     g(Cx(&0)) = Cx(&0) /\
     f holomorphic_on ball(Cx(&0),r) /\
     (!z. z IN ball(Cx(&0),r) ==> f z IN ball(Cx(&0),r)) /\
     f (Cx(&0)) = Cx(&0) /\
     (!z. z IN ball(Cx(&0),r) ==> g (f z) = z) /\
     (!z. z IN ball(Cx(&0),r) ==> f (g z) = z)
     ==> ?t. !z. z IN ball(Cx(&0),r) ==> g z = cexp(ii * Cx t) * z`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy's inequality and more versions of Liouville.                       *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INEQUALITY = `!f z r (B:real) n.
     f continuous_on cball(z,r) /\
     f holomorphic_on ball(z,r) /\ &0 < r /\
     (!x:complex. norm(z-x) = r ==> norm(f x) <= B)
     ==> norm (higher_complex_derivative n f z) <= &(FACT n) * B / r pow n`;;

let LIOUVILLE_POLYNOMIAL = `!f A B n.
        f holomorphic_on (:complex) /\
        (!z. A <= norm(z) ==> norm(f z) <= B * norm(z) pow n)
        ==> !z. f(z) = vsum (0..n)
                            (\k. higher_complex_derivative k f (Cx(&0)) /
                                 Cx(&(FACT k)) * z pow k)`;;

let LIOUVILLE_THEOREM = `!f. f holomorphic_on (:complex) /\ bounded (IMAGE f (:complex))
       ==> ?c. !z. f(z) = c`;;

(* ------------------------------------------------------------------------- *)
(* A holomorphic function f has only isolated zeros unless f is 0.           *)
(* ------------------------------------------------------------------------- *)

let ISOLATED_ZEROS = `!f a z w.
     open a /\ connected a /\ f holomorphic_on a /\ z IN a /\ f z = Cx(&0) /\
     w IN a /\ ~(f w = Cx(&0))
     ==> (?r. &0 < r /\ ball(z,r) SUBSET a /\
              (!w. w IN ball(z,r) /\ ~(w=z) ==> ~(f w = Cx(&0))))`;;

(* ------------------------------------------------------------------------- *)
(* Analytic continuation.                                                    *)
(* ------------------------------------------------------------------------- *)

let ANALYTIC_CONTINUATION = `!f a u z.
     open a /\ connected a /\ f holomorphic_on a /\ u SUBSET a /\ z IN a /\
     z limit_point_of u /\ (!w. w IN u ==> f w = Cx(&0))
     ==> (!w. w IN a ==> f w = Cx(&0))`;;

let HOLOMORPHIC_FUNCTION_ENTIRE = `!f g s.
        open s /\ connected s /\
        f continuous_on s /\ g holomorphic_on s /\
        (!z. z IN s ==> f z * g z = Cx(&0))
        ==> (!z. z IN s ==> f z = Cx(&0)) \/
            (!z. z IN s ==> g z = Cx(&0))`;;

let HOLOMORPHIC_FUNCTION_ENTIRE_PRODUCT = `!f s k:A->bool.
        open s /\ connected s /\ FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> f i holomorphic_on s) /\
        (!z. z IN s ==> cproduct k (\i. f i z) = Cx(&0))
        ==> ?i. i IN k /\ !z. z IN s ==> f i z = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* Open mapping theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let OPEN_MAPPING_THM = `!a f.
     open a /\ connected a /\ f holomorphic_on a /\
     ~(?c:complex. !z:complex. z IN a ==> f z = c)
     ==> (!u. open u /\ u SUBSET a ==> open(IMAGE f u))`;;

(* ------------------------------------------------------------------------- *)
(* Maximum modulus principle.                                                *)
(* ------------------------------------------------------------------------- *)

let MAXIMUM_MODULUS_PRINCIPLE = `!f a u w.
      open a /\ connected a /\ f holomorphic_on a /\
      open u /\ u SUBSET a /\ w IN u /\
      (!z. z IN u ==> norm(f z) <= norm(f w))
      ==> (?c. !z. z IN a ==> f z = c)`;;

let MAXIMUM_MODULUS_FRONTIER = `!f s B.
        bounded s /\
        f holomorphic_on (interior s) /\
        f continuous_on (closure s) /\
        (!z. z IN frontier s ==> norm(f z) <= B)
        ==> !z. z IN s ==> norm(f z) <= B`;;

let MAXIMUM_REAL_FRONTIER = `!f s B.
        bounded s /\
        f holomorphic_on (interior s) /\
        f continuous_on (closure s) /\
        (!z. z IN frontier s ==> Re(f z) <= B)
        ==> !z. z IN s ==> Re(f z) <= B`;;

let HOLOMORPHIC_CONSTANT_ON_FRONTIER = `!f s c.
        bounded s /\
        f holomorphic_on interior s /\
        f continuous_on closure s /\
        (!z. z IN frontier s ==> f z = c)
        ==> !z. z IN s ==> f z = c`;;

let HOLOMORPHIC_CONSTANT_NORM = `!f s. open s /\ connected s /\
         f holomorphic_on s /\
         (?c. !z. z IN s ==> norm(f z) = c)
         ==> ?a. !z. z IN s ==> f z = a`;;

let HOLOMORPHIC_NONZERO_CONSTANT_NORM_ON_FRONTIER = `!f s.
        bounded s /\ open s /\ connected s /\
        f holomorphic_on s /\ f continuous_on closure s /\
        (!z. z IN s ==> ~(f z = Cx(&0))) /\
        (?c. !z. z IN frontier s ==> norm(f z) = c)
        ==> ?a. !z. z IN s ==> f z = a`;;

let MAXIMUM_MODULUS_LIMIT_ATINFINITY = `!f s B.
        &0 <= B /\
        f holomorphic_on interior s /\
        f continuous_on closure s /\
        (!z. z IN frontier s ==> norm(f z) <= B) /\
        (f --> Cx(&0)) (at_infinity within s)
        ==> !z. z IN s ==> norm(f z) <= B`;;

let MAXIMUM_MODULUS_BOUNDED_FUNCTION = `!f s B.
        f holomorphic_on interior s /\
        f continuous_on closure s /\
        (!z. z IN frontier s ==> norm(f z) <= B) /\
        ~(s = (:complex)) /\ bounded(IMAGE f s)
        ==> !z. z IN s ==> norm(f z) <= B`;;

let HOLOMORPHIC_CONSTANT_ON_SPHERE_SEGMENT = `!f a r s c.
        f holomorphic_on ball(a,r) /\
        f continuous_on cball(a,r) /\
        open_in (subtopology euclidean (sphere(a,r))) s /\ ~(s = {}) /\
        (!z. z IN s ==> f z = c)
        ==> !z. z IN cball(a,r) ==> f z = c`;;

(* ------------------------------------------------------------------------- *)
(* A proper holomorphic function maps frontier onto frontier.                *)
(* ------------------------------------------------------------------------- *)

let FRONTIER_PROPER_HOLOMORPHIC_IMAGE = `!f s. open s /\ connected s /\ bounded s /\
         f holomorphic_on s /\ f continuous_on closure s /\
         (!k. compact k /\ k SUBSET IMAGE f s
              ==> compact {x | x IN s /\ f x IN k})
         ==> frontier(IMAGE f s) = IMAGE f (frontier s)`;;

(* ------------------------------------------------------------------------- *)
(* Various forms of Hadamard's three-line theorem.                           *)
(* ------------------------------------------------------------------------- *)

let HADAMARD_THREE_LINE_EXPLICIT_RE = `!f:complex->complex a b u v ma mb.
        a <= b /\
        f holomorphic_on {z | a < Re z /\ Re z < b} /\
        f continuous_on {z | a <= Re z /\ Re z <= b} /\
        bounded (IMAGE f {z | a < Re z /\ Re z < b}) /\
        (!z. Re z = a ==> norm(f z) <= ma) /\
        (!z. Re z = b ==> norm(f z) <= mb) /\
        &0 <= u /\ &0 <= v /\ u + v = &1
        ==> !z. Re z = u * a + v * b ==> norm(f z) <= ma rpow u * mb rpow v`;;

let HADAMARD_THREE_LINE_EXPLICIT_IM = `!f:complex->complex a b u v.
        a <= b /\
        f holomorphic_on {z | a < Im z /\ Im z < b} /\
        f continuous_on {z | a <= Im z /\ Im z <= b} /\
        bounded (IMAGE f {z | a < Im z /\ Im z < b}) /\
        (!z. Im z = a ==> norm(f z) <= ma) /\
        (!z. Im z = b ==> norm(f z) <= mb) /\
        &0 <= u /\ &0 <= v /\ u + v = &1
        ==> !z. Im z = u * a + v * b ==> norm(f z) <= ma rpow u * mb rpow v`;;

let HADAMARD_THREE_LINE_RE = `!f:complex->complex a b.
        f holomorphic_on {z | a < Re z /\ Re z < b} /\
        f continuous_on {z | a <= Re z /\ Re z <= b} /\
        bounded (IMAGE f {z | a <= Re z /\ Re z <= b})
        ==> (\y. sup {norm(f z) | Re z = y}) real_log_convex_on
            real_interval[a,b]`;;

let HADAMARD_THREE_LINE_IM = `!f:complex->complex a b.
        f holomorphic_on {z | a < Im z /\ Im z < b} /\
        f continuous_on {z | a <= Im z /\ Im z <= b} /\
        bounded (IMAGE f {z | a <= Im z /\ Im z <= b})
        ==> (\y. sup {norm(f z) | Im z = y}) real_log_convex_on
            real_interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Likewise the three-circle theorem.                                        *)
(* ------------------------------------------------------------------------- *)

let HADAMARD_THREE_CIRCLE_EXPLICIT = `!f a b u v ma mb.
        &0 < a /\ a <= b /\
        f holomorphic_on {z | a < norm z /\ norm z < b} /\
        f continuous_on {z | a <= norm z /\ norm z <= b} /\
        (!z. norm z = a ==> norm (f z) <= ma) /\
        (!z. norm z = b ==> norm (f z) <= mb) /\
        &0 <= u /\
        &0 <= v /\
        u + v = &1
        ==> !z. norm z = a rpow u * b rpow v
                ==> norm(f z) <= ma rpow u * mb rpow v`;;

let HADAMARD_THREE_CIRCLE = `!f a b.
        &0 < a /\ a <= b /\
        f holomorphic_on {z | exp a < norm z /\ norm z < exp b} /\
        f continuous_on {z | exp a <= norm z /\ norm z <= exp b}
        ==> (\y. sup {norm (f z) | norm z = exp y}) real_log_convex_on
            real_interval [a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Factoring out a zero according to its order.                              *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_FACTOR_ORDER_OF_ZERO = `!f s n.
      open s /\ z IN s /\ f holomorphic_on s /\
      0 < n /\ ~(higher_complex_derivative n f z = Cx(&0)) /\
      (!m. 0 < m /\ m < n ==> higher_complex_derivative m f z = Cx(&0))
      ==> ?g r. &0 < r /\
                g holomorphic_on ball(z,r) /\
                (!w. w IN ball(z,r) ==> f(w) - f(z) = (w - z) pow n * g(w)) /\
                (!w. w IN ball(z,r) ==> ~(g w = Cx(&0)))`;;

let HOLOMORPHIC_FACTOR_ORDER_OF_ZERO_STRONG = `!f s n z.
      open s /\ z IN s /\ f holomorphic_on s /\
      0 < n /\ ~(higher_complex_derivative n f z = Cx(&0)) /\
      (!m. 0 < m /\ m < n ==> higher_complex_derivative m f z = Cx(&0))
      ==> ?g r. &0 < r /\
                g holomorphic_on ball(z,r) /\
                (!w. w IN ball(z,r)
                     ==> f(w) - f(z) = ((w - z) * g w) pow n) /\
                (!w. w IN ball(z,r) ==> ~(g w = Cx(&0)))`;;

let HOLOMORPHIC_FACTOR_ZERO_NONCONSTANT = `!f s z.
        open s /\ connected s /\ z IN s /\
        f holomorphic_on s /\ f(z) = Cx(&0) /\ ~(?c. !w. w IN s ==> f w = c)
        ==> ?g r n.
                0 < n /\ &0 < r /\ ball(z,r) SUBSET s /\
                g holomorphic_on ball(z,r) /\
                (!w. w IN ball(z,r) ==> f w = (w - z) pow n * g w) /\
                (!w. w IN ball(z,r) ==> ~(g w = Cx(&0)))`;;

let HOLOMORPHIC_LOWER_BOUND_DIFFERENCE = `!f s z.
        open s /\ connected s /\ z IN s /\ f holomorphic_on s /\
        ~(!w. w IN s ==> f w = f z)
        ==> ?k n r. &0 < k /\ &0 < r /\ ball(z,r) SUBSET s /\
                    !w. w IN ball(z,r)
                        ==> k * norm(w - z) pow n <= norm(f w - f z)`;;

let POLE_AT_INFINITY = `!f l. f holomorphic_on (:complex) /\ ((inv o f) --> l) at_infinity
         ==> ?a n. !z. f(z) = vsum(0..n) (\i. a i * z pow i)`;;

(* ------------------------------------------------------------------------- *)
(* Entire proper functions C->C are precisely the non-trivial polynomials.   *)
(* ------------------------------------------------------------------------- *)

let PROPER_MAP_COMPLEX_POLYFUN = `!s k c n. closed s /\ compact k /\ (?i. i IN 1..n /\ ~(c i = Cx(&0)))
             ==> compact {z | z IN s /\ vsum(0..n) (\i. c i * z pow i) IN k}`;;

let PROPER_MAP_COMPLEX_POLYFUN_UNIV = `!k c n. compact k /\ (?i. i IN 1..n /\ ~(c i = Cx(&0)))
           ==> compact {z | vsum(0..n) (\i. c i * z pow i) IN k}`;;

let PROPER_MAP_COMPLEX_POLYFUN_EQ = `!f. f holomorphic_on (:complex)
       ==> ((!k. compact k ==> compact {z | f z IN k}) <=>
            ?c n. 0 < n /\ ~(c n = Cx(&0)) /\
                  f = \z. vsum(0..n) (\i. c i * z pow i))`;;

(* ------------------------------------------------------------------------- *)
(* Power and squaring functions as covering maps.                            *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_POW_PUNCTURED_PLANE = `!n. 0 < n
       ==> covering_space ((:complex) DIFF {Cx(&0)},(\z. z pow n))
                          ((:complex) DIFF {Cx (&0)})`;;

let COVERING_SPACE_SQUARE_PUNCTURED_PLANE = `covering_space ((:complex) DIFF {Cx(&0)},(\z. z pow 2))
                  ((:complex) DIFF {Cx (&0)})`;;

(* ------------------------------------------------------------------------- *)
(* Relating invertibility and nonvanishing of derivative.                    *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_LOCALLY_INJECTIVE = `!f s z.
        f holomorphic_on s /\ open s /\ z IN s /\
        ~(complex_derivative f z = Cx(&0))
        ==> ?t. z IN t /\
                open t /\
                (!x x'. x IN t /\ x' IN t /\ f x' = f x ==> x' = x)`;;

let HAS_COMPLEX_DERIVATIVE_LOCALLY_INVERTIBLE = `!f s z.
        f holomorphic_on s /\ open s /\ z IN s /\
        ~(complex_derivative f z = Cx(&0))
        ==> ?t g. z IN t /\ open t /\ open(IMAGE f t) /\ t SUBSET s /\
                  (!w. w IN t ==> g(f w) = w) /\
                  (!y. y IN (IMAGE f t) ==> f(g y) = y)`;;

let HOLOMORPHIC_INJECTIVE_IMP_REGULAR = `!f s.
        f holomorphic_on s /\ open s /\
        (!w z. w IN s /\ z IN s /\ f w = f z ==> w = z)
        ==> !z. z IN s ==> ~(complex_derivative f z = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* Hence a nice clean inverse function theorem.                              *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_INVERSE = `!f s. f holomorphic_on s /\ open s /\
         (!w z. w IN s /\ z IN s /\ f w = f z ==> w = z)
         ==> open(IMAGE f s) /\
             ?g. g holomorphic_on (IMAGE f s) /\
                 (!z. z IN s
                      ==> complex_derivative f z * complex_derivative g (f z) =
                          Cx(&1)) /\
                 (!z. z IN s ==> g(f z) = z) /\
                 (!y. y IN (IMAGE f s) ==> f(g y) = y)`;;

(* ------------------------------------------------------------------------- *)
(* Holomorphism of covering maps and lifts.                                  *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_LIFT_IS_HOLOMORPHIC = `!p c s f g u.
        covering_space (c,p) s /\ open c /\ p holomorphic_on c /\
        f holomorphic_on u /\ IMAGE f u SUBSET s /\ IMAGE g u SUBSET c /\
        g continuous_on u /\ (!x. x IN u ==> p(g x) = f x)
        ==> g holomorphic_on u`;;

let COVERING_SPACE_LIFT_HOLOMORPHIC = `!p c s f u.
        covering_space (c,p) s /\ p holomorphic_on c /\ open c /\
        simply_connected u /\ locally path_connected u /\
        f holomorphic_on u /\ IMAGE f u SUBSET s
        ==> ?g. g holomorphic_on u /\ IMAGE g u SUBSET c /\
                !y. y IN u ==> p(g y) = f y`;;

(* ------------------------------------------------------------------------- *)
(* The Schwarz lemma.                                                        *)
(* ------------------------------------------------------------------------- *)

let SCHWARZ_LEMMA = `!f. f holomorphic_on ball(Cx(&0),&1) /\
       (!z:complex. norm z < &1 ==> norm (f z) < &1) /\
       f(Cx(&0)) = Cx(&0)
       ==> (!z. norm z < &1 ==> norm(f z) <= norm z) /\
           norm(complex_derivative f(Cx(&0))) <= &1 /\
           ((?z. norm z < &1 /\ ~(z= Cx(&0)) /\ norm(f z) = norm z) \/
            norm(complex_derivative f (Cx(&0))) = &1
            ==> ?c. (!z. norm z < &1 ==> f z = c*z) /\ norm c = &1)`;;

let HOLOMORPHIC_SUBORDINATION = `!f g a r s.
        r <= s /\ f a = g a /\
        f holomorphic_on ball(a,s) /\ g holomorphic_on ball(a,s) /\
        (!w z. w IN ball(a,s) /\ z IN ball(a,s) /\ g w = g z ==> w = z) /\
        IMAGE f (ball(a,s)) SUBSET IMAGE g (ball(a,s))
        ==> IMAGE f (ball(a,r)) SUBSET IMAGE g (ball(a,r))`;;

(* ------------------------------------------------------------------------- *)
(* The Schwarz reflection principle.                                         *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_PASTE_ACROSS_LINE = `!f s a k.
        open s /\ ~(a = vec 0) /\
        f holomorphic_on {z | z IN s /\ k < a dot z} /\
        f holomorphic_on {z | z IN s /\ a dot z < k} /\
        f continuous_on s
        ==> f holomorphic_on s`;;

let SCHWARZ_REFLECTION = `!f s. open s /\ (!z. z IN s ==> cnj z IN s) /\
         f holomorphic_on {z | z IN s /\ &0 < Im z} /\
         f continuous_on {z | z IN s /\ &0 <= Im z} /\
         (!z. z IN s /\ real z ==> real(f z))
         ==> (\z. if &0 <= Im z then f(z) else cnj(f(cnj z)))
             holomorphic_on s`;;

let SCHWARZ_REFLECTION_UNIQUE = `!f s. open s /\ connected s /\ (!z. z IN s ==> cnj z IN s) /\
         f holomorphic_on s /\ (!z. z IN s /\ real z ==> real(f z))
         ==> (!z. z IN s ==> f(cnj z) = cnj(f z))`;;

(* ------------------------------------------------------------------------- *)
(* Bloch's theorem.                                                          *)
(* ------------------------------------------------------------------------- *)

let BLOCH_LEMMA = `!f a r.
    &0 < r /\ f holomorphic_on cball(a,r) /\
    (!z. z IN ball(a,r)
         ==> norm(complex_derivative f z) <= &2 * norm(complex_derivative f a))
    ==> ball(f(a),(&3 - &2 * sqrt(&2)) * r * norm(complex_derivative f a))
        SUBSET IMAGE f (ball(a,r))`;;

let BLOCH_UNIT = `!f a. f holomorphic_on ball(a,&1) /\
       complex_derivative f a = Cx(&1)
       ==> ?b r. &1 / &12 < r /\ ball(b,r) SUBSET IMAGE f (ball(a,&1))`;;

let BLOCH = `!f a r r'.
      &0 < r /\ f holomorphic_on ball(a,r) /\
      r' <= r * norm(complex_derivative f a) / &12
      ==> ?b. ball(b,r') SUBSET IMAGE f (ball(a,r))`;;

let BLOCH_COROLLARY = `!f s a t r.
      f holomorphic_on s /\ a IN s /\
      (!z. z IN frontier s ==> t <= dist(a,z)) /\
      r <= t * norm(complex_derivative f a) / &12
      ==> ?b. ball(b,r) SUBSET IMAGE f s`;;

(* ------------------------------------------------------------------------- *)
(* Schottky's theorem.                                                       *)
(* ------------------------------------------------------------------------- *)

let SCHOTTKY = `!f r. f holomorphic_on cball(Cx(&0),&1) /\ norm(f(Cx(&0))) <= r /\
         (!z. z IN cball(Cx(&0),&1) ==> ~(f z = Cx(&0) \/ f z = Cx(&1)))
         ==> !t z. &0 < t /\ t < &1 /\ norm(z) <= t
                   ==> norm(f z)
                       <= exp(pi * exp(pi *
                                       (&2 + &2 * r + &12 * t / (&1 - t))))`;;

(* ------------------------------------------------------------------------- *)
(* The Little Picard Theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let LANDAU_PICARD = `?R. (!z. &0 < R z) /\
       !f. f holomorphic_on cball(Cx(&0),R(f(Cx(&0)))) /\
           (!z. z IN cball(Cx(&0),R(f(Cx(&0))))
                ==> ~(f(z) = Cx(&0)) /\ ~(f(z) = Cx(&1)))
           ==> norm(complex_derivative f (Cx(&0))) < &1`;;

let LITTLE_PICARD = `!f a b.
      f holomorphic_on (:complex) /\
      ~(a = b) /\ IMAGE f (:complex) INTER {a,b} = {}
      ==> ?c. f = \x. c`;;

(* ------------------------------------------------------------------------- *)
(* A couple of little applications of Little Picard.                         *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_PERIODIC_FIXPOINT = `!f p. f holomorphic_on (:complex) /\ ~(p = Cx(&0)) /\ (!z. f(z + p) = f(z))
         ==> ?x. f(x) = x`;;

let HOLOMORPHIC_INVOLUTION_POINT = `!f. f holomorphic_on (:complex) /\ ~(?a. f = \x. a + x) ==> ?x. f(f x) = x`;;

(* ------------------------------------------------------------------------- *)
(* Montel's theorem: a sequence of holomorphic functions uniformly bounded   *)
(* on compact subsets of an open set S has a subsequence that converges to a *)
(* holomorphic function, and converges *uniformly* on compact subsets of S.  *)
(* ------------------------------------------------------------------------- *)

let MONTEL = `!(f:num->complex->complex) p s.
    open s /\ (!h. h IN p ==> h holomorphic_on s) /\
    (!k. compact k /\ k SUBSET s
         ==> ?b. !h z. h IN p /\ z IN k ==> norm(h z) <= b) /\
    (!n. (f n) IN p)
    ==> ?g r. g holomorphic_on s /\
              (!m n:num. m < n ==> r m < r n) /\
              (!x. x IN s ==> ((\n. f (r n) x) --> g(x)) sequentially) /\
              (!k e. compact k /\ k SUBSET s /\ &0 < e
                     ==> ?N. !n x. n >= N /\ x IN k
                                   ==> norm(f (r n) x - g x) < e)`;;

(* ------------------------------------------------------------------------- *)
(* Moebius functions are biholomorphisms of the unit disc.                   *)
(* ------------------------------------------------------------------------- *)

let moebius_function = new_definition
  `!t w z. moebius_function t w z =
           cexp(ii * Cx t) * (z - w) / (Cx(&1) - cnj w * z)`;;

let MOEBIUS_FUNCTION_SIMPLE = `!w z. moebius_function (&0) w z = (z - w) / (Cx(&1) - cnj w * z)`;;

let MOEBIUS_FUNCTION_EQ_ZERO = `!t w. moebius_function t w w = Cx(&0)`;;

let MOEBIUS_FUNCTION_OF_ZERO = `!t w. moebius_function t w (Cx(&0)) = -- cexp(ii * Cx t) * w`;;

let MOEBIUS_FUNCTION_NORM_LT_1 = `!t w z. norm w < &1 /\ norm z < &1
            ==> norm (moebius_function t w z) < &1`;;

let MOEBIUS_FUNCTION_HOLOMORPHIC = `!t w. norm w < &1 ==> moebius_function t w holomorphic_on ball(Cx(&0),&1)`;;

let MOEBIUS_FUNCTION_COMPOSE = `!w1 w2 z.
     -- w1 = w2  /\ norm w1 < &1 /\ norm z < &1
     ==> moebius_function (&0) w1 (moebius_function (&0) w2 z) = z`;;

let BALL_BIHOLOMORPHISM_EXISTS = `!a. a IN ball(Cx(&0),&1)
       ==> ?f g. f(a) = Cx(&0) /\
                 f holomorphic_on ball (Cx(&0),&1) /\
                 (!z. z IN ball (Cx(&0),&1) ==> f z IN ball (Cx(&0),&1)) /\
                 g holomorphic_on ball (Cx(&0),&1) /\
                 (!z. z IN ball (Cx(&0),&1) ==> g z IN ball (Cx(&0),&1)) /\
                 (!z. z IN ball (Cx(&0),&1) ==> f (g z) = z) /\
                 (!z. z IN ball (Cx(&0),&1) ==> g (f z) = z)`;;

let BALL_BIHOLOMORPHISM_MOEBIUS_FUNCTION = `!f g.
      f holomorphic_on ball (Cx(&0),&1) /\
      (!z. z IN ball (Cx(&0),&1) ==> f z IN ball (Cx(&0),&1)) /\
      g holomorphic_on ball (Cx(&0),&1) /\
      (!z. z IN ball (Cx(&0),&1) ==> g z IN ball (Cx(&0),&1)) /\
      (!z. z IN ball (Cx(&0),&1) ==> f (g z) = z) /\
      (!z. z IN ball (Cx(&0),&1) ==> g (f z) = z)
      ==> ?t w. w IN ball (Cx(&0),&1) /\
                (!z. z IN ball (Cx(&0),&1) ==> f z = moebius_function t w z)`;;

(* ------------------------------------------------------------------------- *)
(* Some simple but useful cases of Hurwitz's theorem.                        *)
(* ------------------------------------------------------------------------- *)

let HURWITZ_NO_ZEROS = `!f:num->complex->complex g s.
        open s /\ connected s /\
        (!n. (f n) holomorphic_on s) /\ g holomorphic_on s /\
        (!k e. compact k /\ k SUBSET s /\ &0 < e
               ==> ?N. !n x. n >= N /\ x IN k ==> norm(f n x - g x) < e) /\
        ~(?c. !z. z IN s ==> g z = c) /\
        (!n z. z IN s ==> ~(f n z = Cx(&0)))
        ==> (!z. z IN s ==> ~(g z = Cx(&0)))`;;

let HURWITZ_INJECTIVE = `!f:num->complex->complex g s.
    open s /\ connected s /\
    (!n. (f n) holomorphic_on s) /\ g holomorphic_on s /\
    (!k e. compact k /\ k SUBSET s /\ &0 < e
           ==> ?N. !n x. n >= N /\ x IN k ==> norm(f n x - g x) < e) /\
    ~(?c. !z. z IN s ==> g z = c) /\
    (!n w z. w IN s /\ z IN s /\ f n w = f n z ==> w = z)
    ==> (!w z. w IN s /\ z IN s /\ g w = g z ==> w = z)`;;

(* ------------------------------------------------------------------------- *)
(* The Great Picard theorem, and a thematic Montel variant.                  *)
(* ------------------------------------------------------------------------- *)

let GREAT_PICARD = `(!f n a b z.
        open n /\ z IN n /\ ~(a = b) /\ f holomorphic_on (n DELETE z) /\
        (!w. w IN n DELETE z ==> ~(f w = a) /\ ~(f w = b))
        ==> ?l. (f --> l) (at z) \/ ((inv o f) --> l) (at z))`
and MONTEL_OMITTING = `(!f:num->complex->complex p s a b.
     open s /\ connected s /\ ~(a = b) /\
     (!h. h IN p
          ==> h holomorphic_on s /\ !z. z IN s ==> ~(h z = a) /\ ~(h z = b)) /\
     (!n. f n IN p)
     ==> ?r. (!m n. m < n ==> r m < r n) /\
             ((!x. x IN s
                   ==> ((\n. inv(f (r n) x)) --> Cx(&0)) sequentially) /\
              (!k c. compact k /\ k SUBSET s
                     ==> ?N. !n x. n >= N /\ x IN k
                                   ==> c < norm(f (r n) x)) \/
              ?g. g holomorphic_on s /\
                  (!x. x IN s ==> ((\n. f (r n) x) --> g x) sequentially) /\
                  (!k e. compact k /\ k SUBSET s /\ &0 < e
                         ==> ?N. !n x. n >= N /\ x IN k
                                       ==> norm(f (r n) x - g x) < e)))`;;

let GREAT_PICARD_ALT = `!f n z.
        open n /\ z IN n /\ f holomorphic_on (n DELETE z) /\
        ~(?l. (f --> l) (at z) \/ ((inv o f) --> l) (at z))
        ==> ?a. (:complex) DELETE a SUBSET IMAGE f (n DELETE z)`;;

let GREAT_PICARD_INFINITE = `!f n z.
        open n /\ z IN n /\ f holomorphic_on (n DELETE z) /\
        ~(?l. (f --> l) (at z) \/ ((inv o f) --> l) (at z))
        ==> ?a. !w. ~(w = a) ==> INFINITE {x | x IN n DELETE z /\ f x = w}`;;

let CASORATI_WEIERSTRASS = `!f n z.
        open n /\ z IN n /\ f holomorphic_on (n DELETE z) /\
        ~(?l. (f --> l) (at z) \/ ((inv o f) --> l) (at z))
        ==> closure(IMAGE f (n DELETE z)) = (:complex)`;;

(* ------------------------------------------------------------------------- *)
(* A big chain of equivalents of simple connectedness for an open set.       *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_EQ_WINDING_NUMBER_ZERO = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !g z. path g /\ path_image g SUBSET s /\
                   pathfinish g = pathstart g /\ ~(z IN s)
                   ==> winding_number(g,z) = Cx(&0)))`
and SIMPLY_CONNECTED_EQ_PATH_INTEGRAL_ZERO = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !g f. valid_path g /\ path_image g SUBSET s /\
                   pathfinish g = pathstart g /\ f holomorphic_on s
                 ==> (f has_path_integral Cx(&0)) g))`
and SIMPLY_CONNECTED_EQ_GLOBAL_PRIMITIVE = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s
                 ==> ?h. !z. z IN s
                             ==> (h has_complex_derivative f(z)) (at z)))`
and SIMPLY_CONNECTED_EQ_HOLOMORPHIC_LOG = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g holomorphic_on s /\
                         !z. z IN s ==> f z = cexp(g z)))`
and SIMPLY_CONNECTED_EQ_HOLOMORPHIC_SQRT = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g holomorphic_on s /\
                         !z. z IN s ==> f z = g z pow 2))`
and SIMPLY_CONNECTED_EQ_INJECTIVE_HOLOMORPHIC_SQRT = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0))) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
                 ==> ?g. g holomorphic_on s /\
                         !z. z IN s ==> f z = g z pow 2))`
and SIMPLY_CONNECTED_EQ_BIHOLOMORPHIC_TO_DISC = `(!s. open s
        ==> (simply_connected s <=>
             s = {} \/ s = (:complex) \/
             ?f g. f holomorphic_on s /\ g holomorphic_on ball(Cx(&0),&1) /\
                   (!z. z IN s ==> f(z) IN ball(Cx(&0),&1) /\ g(f z) = z) /\
                   (!z. z IN ball(Cx(&0),&1) ==> g(z) IN s /\ f(g z) = z)))`
and SIMPLY_CONNECTED_EQ_HOMEOMORPHIC_TO_DISC = `(!s. open s
        ==> (simply_connected(s:complex->bool) <=>
             s = {} \/ s homeomorphic ball(Cx(&0),&1)))`;;

let CONTRACTIBLE_EQ_SIMPLY_CONNECTED_2D = `!s:real^2->bool. open s ==> (contractible s <=> simply_connected s)`;;

(* ------------------------------------------------------------------------- *)
(* A further chain of equivalents about components of the complement of a    *)
(* simply connected set (following 1.35 in Burckel's book).                  *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_EQ_FRONTIER_PROPERTIES = `(!s:complex->bool.
        open s
        ==> (simply_connected s <=>
             connected s /\
             if bounded s then connected(frontier s)
             else !c. c IN components(frontier s) ==> ~bounded c))`
and SIMPLY_CONNECTED_EQ_UNBOUNDED_COMPLEMENT_COMPONENTS = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !c. c IN components ((:complex) DIFF s) ==> ~bounded c))`
and SIMPLY_CONNECTED_EQ_EMPTY_INSIDE = `(!s:complex->bool.
        open s ==> (simply_connected s <=> connected s /\ inside s = {}))`;;

let SIMPLY_CONNECTED_IFF_SIMPLE = `!s:real^2->bool.
        open s /\ bounded s
        ==> (simply_connected s <=>
             connected s /\ connected((:real^2) DIFF s))`;;

let CONNECTED_COMPLEMENT_IFF_SIMPLY_CONNECTED_COMPONENTS = `!s:real^2->bool.
        open s /\ bounded s
        ==> (connected((:real^2) DIFF s) <=>
             !c. c IN components s ==> simply_connected c)`;;

let SIMPLY_CONNECTED_COMPONENT_PATH_COMPLEMENT = `!g c. path g /\ c IN components((:real^2) DIFF path_image g) /\ bounded c
         ==> simply_connected c`;;

(* ------------------------------------------------------------------------- *)
(* Yet another set of equivalences based on *continuous* logs and sqrts.     *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_EQ_CONTINUOUS_LOG = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f continuous_on s /\ (!z:complex. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g continuous_on s /\
                         !z. z IN s ==> f z = cexp(g z)))`
and SIMPLY_CONNECTED_EQ_CONTINUOUS_SQRT = `(!s. open s
        ==> (simply_connected s <=>
             connected s /\
             !f. f continuous_on s /\ (!z:complex. z IN s ==> ~(f z = Cx(&0)))
                 ==> ?g. g continuous_on s /\
                         !z. z IN s ==> f z = g z pow 2))`;;

(* ------------------------------------------------------------------------- *)
(* Relations to the borsukian property.                                      *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_EQ_BORSUKIAN = `!s:real^2->bool.
        open s ==> (simply_connected s <=> connected s /\ borsukian s)`;;

let BORSUKIAN_EQ_SIMPLY_CONNECTED = `!s:real^2->bool.
        open s
        ==> (borsukian s <=> !c. c IN components s ==> simply_connected c)`;;

let BORSUKIAN_SEPARATION_OPEN_CLOSED = `!s:real^2->bool.
        (open s \/ closed s) /\ bounded s
        ==> (borsukian s <=> connected((:real^2) DIFF s))`;;

(* ------------------------------------------------------------------------- *)
(* A per-function version for continuous logs, a kind of monodromy.          *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_COMPOSE_CEXP = `!p. path p
       ==> winding_number(cexp o p,Cx(&0)) =
           Cx(&1) / (Cx(&2) * Cx pi * ii) * (pathfinish p - pathstart p)`;;

let MONODROMY_CONTINUOUS_LOG = `!f:complex->complex s.
        open s /\ f continuous_on s /\
        (!z. z IN s ==> ~(f z = Cx(&0)))
        ==> ((!p. path p /\ path_image p SUBSET s /\
                  pathfinish p = pathstart p
                  ==> winding_number(f o p,Cx(&0)) = Cx(&0)) <=>
             (?g. g continuous_on s /\ !z. z IN s ==> f(z) = cexp(g z)))`;;

(* ------------------------------------------------------------------------- *)
(* The winding number defines a continuous logarithm for the path itself.    *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM = `!p z.
      path p /\ ~(z IN path_image p)
      ==> ?q. path q /\
              pathfinish q - pathstart q =
              Cx(&2) * Cx pi * ii * winding_number(p,z) /\
              !t. t IN interval[vec 0,vec 1] ==> p(t) = z + cexp(q t)`;;

(* ------------------------------------------------------------------------- *)
(* Winding number integral for absolutely continuous closed curves.          *)
(* Incomparable with HAS_PATH_INTEGRAL_WINDING_NUMBER (which uses            *)
(* valid_path = piecewise differentiable): valid_path allows unbounded       *)
(* derivatives so need not be AC/rectifiable; AC paths are differentiable    *)
(* a.e. but the exceptional null set need not be finite.                     *)
(* Proof: construct indefinite integral ef of 1/(g-z)*gd, show               *)
(* G(t) = cexp(-ef(t))*(g(t)-z) has zero a.e. derivative via product rule,   *)
(* hence G is constant by AC FTC. Then cexp(q-ef) is constant, and           *)
(* q-ef = q(0) by discrete range argument (CEXP_EQ). Finally ef(1) = 2pi*wn. *)
(* ------------------------------------------------------------------------- *)

let HAS_PATH_INTEGRAL_WINDING_NUMBER_AC = `!g:real^1->complex z.
    g absolutely_continuous_on interval[vec 0,vec 1] /\
    pathfinish g = pathstart g /\
    ~(z IN path_image g)
    ==> ((\w. Cx(&1) / (w - z)) has_path_integral
         (Cx(&2) * Cx(pi) * ii * winding_number(g,z))) g`;;

(* ------------------------------------------------------------------------- *)
(* Winding number equality is the same as path/loop homotopy in C - {0}.     *)
(* ------------------------------------------------------------------------- *)

let WINDING_NUMBER_HOMOTOPIC_LOOPS_NULL_EQ = `!p z. path p /\ ~(z IN path_image p)
         ==> (winding_number(p,z) = Cx(&0) <=>
              ?a. homotopic_loops ((:complex) DELETE z) p (\t. a))`;;

let WINDING_NUMBER_HOMOTOPIC_PATHS_NULL_EXPLICIT_EQ = `!p z. path p /\ ~(z IN path_image p)
         ==> (winding_number(p,z) = Cx(&0) <=>
              homotopic_paths ((:complex) DELETE z)
                              p (linepath(pathstart p,pathstart p)))`;;

let WINDING_NUMBER_HOMOTOPIC_PATHS_NULL_EQ = `!p z. path p /\ ~(z IN path_image p)
         ==> (winding_number(p,z) = Cx(&0) <=>
              ?a. homotopic_paths ((:complex) DELETE z) p (\t. a))`;;

let WINDING_NUMBER_HOMOTOPIC_PATHS_EQ = `!p q z.
        path p /\ ~(z IN path_image p) /\
        path q /\ ~(z IN path_image q) /\
        pathstart q = pathstart p /\ pathfinish q = pathfinish p
        ==> (winding_number(p,z) = winding_number(q,z) <=>
             homotopic_paths ((:complex) DELETE z) p q)`;;

let WINDING_NUMBER_HOMOTOPIC_LOOPS_EQ = `!p q z.
        path p /\ pathfinish p = pathstart p /\ ~(z IN path_image p) /\
        path q /\ pathfinish q = pathstart q /\ ~(z IN path_image q)
        ==> (winding_number(p,z) = winding_number(q,z) <=>
             homotopic_loops ((:complex) DELETE z) p q)`;;

let HOMOTOPIC_LOOPS_PARTCIRCLEPATH = `!g z r n.
        path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g) /\
        &0 < r /\ winding_number(g,z) = Cx(n)
        ==> homotopic_loops ((:complex) DELETE z)
                            g (partcirclepath(z,r,&0,&2 * n * pi))`;;

(* ------------------------------------------------------------------------- *)
(* A few simple corollaries from the various equivalences.                   *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_INSIDE_SIMPLE_PATH = `!p:real^1->real^2.
     simple_path p ==> simply_connected(inside(path_image p))`;;

let HOMEOMORPHIC_INSIDE_SIMPLE_PATH_BALL = `!p:real^1->real^2 a:real^2 r.
        simple_path p /\ pathfinish p = pathstart p /\ &0 < r
        ==> inside(path_image p) homeomorphic ball(a,r)`;;

let SIMPLY_CONNECTED_INTER = `!s t:real^2->bool.
        open s /\ open t /\ simply_connected s /\ simply_connected t /\
        connected (s INTER t)
        ==> simply_connected (s INTER t)`;;

(* ------------------------------------------------------------------------- *)
(* More sufficient conditions for Borsukian-ness.                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_ORDER_FUNDAMENTAL_GROUP_IMP_BORSUKIAN = `!s a:real^N.
        path_connected s /\ locally path_connected s /\ a IN s /\
        (!p. path p /\ path_image p SUBSET s /\
             pathstart p = a /\ pathfinish p = a
             ==> ?n. homotopic_paths s (ITER n ((++) p) p) (linepath(a,a)))
         ==> borsukian s`;;

let FINITE_FUNDAMENTAL_GROUP_IMP_BORSUKIAN = `!s:real^N->bool a.
        path_connected s /\ locally path_connected s /\
        a IN s /\ FINITE (fundamental_group(s,a))
         ==> borsukian s`;;

(* ------------------------------------------------------------------------- *)
(* Pick out the Riemann Mapping Theorem from the earlier chain.              *)
(* ------------------------------------------------------------------------- *)

let RIEMANN_MAPPING_THEOREM = `!s. open s /\ simply_connected s <=>
       s = {} \/
       s = (:real^2) \/
       ?f g. f holomorphic_on s /\
             g holomorphic_on ball(Cx(&0),&1) /\
             (!z. z IN s ==> f z IN ball(Cx(&0),&1) /\ g(f z) = z) /\
             (!z. z IN ball(Cx(&0),&1) ==> g z IN s /\ f(g z) = z)`;;

(* ------------------------------------------------------------------------- *)
(* Extension of conformal maps to the frontier of the unit disc.             *)
(* ------------------------------------------------------------------------- *)

let TORHORST_CONFORMAL_EXTENSION_THEOREM = `!f s. f holomorphic_on ball(Cx(&0),&1) /\ IMAGE f (ball(Cx(&0),&1)) = s /\
         (!w z. w IN ball(Cx(&0),&1) /\ z IN ball(Cx(&0),&1) /\ f w = f z
                ==> w = z)
         ==> ((?g. g continuous_on cball(Cx(&0),&1) /\
                   !z. z IN ball(Cx(&0),&1) ==> g z = f z) <=>
              bounded s /\ locally connected (frontier s))`;;

let CARATHEODORY_CONFORMAL_EXTENSION_LEMMA = `!f s a.
        f holomorphic_on ball(Cx(&0),&1) /\
        f continuous_on cball(Cx(&0),&1) /\
        IMAGE f (ball(Cx(&0),&1)) = s /\
        (!w z. w IN ball(Cx(&0),&1) /\ z IN ball(Cx(&0),&1) /\ f w = f z
               ==> w = z) /\
        a IN closure s
        ==> ({x | x IN cball(Cx(&0),&1) /\ f x = a} HAS_SIZE 1 <=>
             connected (frontier(s) DELETE a))`;;

(* ------------------------------------------------------------------------- *)
(* Full Caratheodory and Jordan-Schoenflies theorems.                        *)
(* ------------------------------------------------------------------------- *)

let CARATHEODORY_CONFORMAL_EXTENSION_THEOREM,JORDAN_SCHOENFLIES_CIRCLE =
  let carat_cball = `!f s p.
          f holomorphic_on ball(Cx(&0),&1) /\ IMAGE f (ball(Cx(&0),&1)) = s /\
          (!w z. w IN ball(Cx(&0),&1) /\ z IN ball(Cx(&0),&1) /\ f w = f z
                 ==> w = z) /\
          simple_path p /\ path_image p = frontier s
          ==> ?g h. homeomorphism (cball(Cx(&0),&1),closure s) (g,h) /\
                    IMAGE g (ball(Cx(&0),&1)) = s /\
                    IMAGE g (sphere(Cx(&0),&1)) = frontier s /\
                    !x. x IN ball(Cx(&0),&1) ==> g x = f x` in
  let js_cball = `!g:real^2->real^2 h s z:real^2.
       homeomorphism (sphere(vec 0,&1),s) (g,h) /\ z IN inside s
       ==> ?g' h'. homeomorphism (cball(vec 0,&1),closure(inside s)) (g',h') /\
                   (!x. x IN sphere(vec 0,&1) ==> g' x = g x) /\
                   (!y. y IN s ==> h' y = h y) /\
                   IMAGE g' (sphere(vec 0,&1)) = s /\
                   IMAGE g' (ball(vec 0,&1)) = inside s /\
                   g'(vec 0) = z` in
  let inv_lemma = `!g. simple_path g /\ pathfinish g = pathstart g /\
         Cx(&0) IN inside(path_image g)
          ==> homeomorphism(outside(path_image g),
                            inside(path_image(inv o g)) DELETE Cx(&0))
                           (inv,inv)` in
  let js_noball_0 = `!g:real^2->real^2 h s.
        homeomorphism (sphere(vec 0,&1),s) (g,h) /\ vec 0 IN inside s
        ==> ?g' h'. homeomorphism ((:complex) DIFF ball(Cx(&0),&1),
                                   closure(outside s))
                                  (g',h') /\
                    (!x. x IN sphere(vec 0,&1) ==> g' x = g x) /\
                    (!y. y IN s ==> h' y = h y) /\
                    IMAGE g' (sphere(vec 0,&1)) = s /\
                    IMAGE g' ((:complex) DIFF cball(vec 0,&1)) = outside s` in
  let js_noball = `!g:real^2->real^2 h s.
        homeomorphism (sphere(vec 0,&1),s) (g,h)
        ==> ?g' h'. homeomorphism ((:complex) DIFF ball(Cx(&0),&1),
                                   closure(outside s))
                                  (g',h') /\
                    (!x. x IN sphere(vec 0,&1) ==> g' x = g x) /\
                    (!y. y IN s ==> h' y = h y) /\
                    IMAGE g' (sphere(vec 0,&1)) = s /\
                    IMAGE g' ((:complex) DIFF cball(vec 0,&1)) = outside s` in
  let CARATHEODORY_CONFORMAL_EXTENSION_THEOREM = `!f s p.
          f holomorphic_on ball(Cx(&0),&1) /\ IMAGE f (ball(Cx(&0),&1)) = s /\
          (!w z. w IN ball(Cx(&0),&1) /\ z IN ball(Cx(&0),&1) /\ f w = f z
                 ==> w = z) /\
          simple_path p /\ path_image p = frontier s
          ==> ?g h. homeomorphism ((:complex),(:complex)) (g,h) /\
                    IMAGE g (ball(Cx(&0),&1)) = s /\
                    IMAGE g (cball(Cx(&0),&1)) = closure s /\
                    IMAGE g (sphere(Cx(&0),&1)) = frontier s /\
                    IMAGE g ((:complex) DIFF cball(Cx(&0),&1)) =
                    (:complex) DIFF closure s /\
                    !x. x IN ball(Cx(&0),&1) ==> g x = f x` in
  let JORDAN_SCHOENFLIES_CIRCLE = `!g:real^2->real^2 h s.
        homeomorphism (sphere(vec 0,&1),s) (g,h)
        ==> ?g' h'. homeomorphism ((:real^2),(:real^2)) (g',h') /\
                    (!x. x IN sphere(vec 0,&1) ==> g' x = g x) /\
                    (!y. y IN s ==> h' y = h y) /\
                    IMAGE g' (ball(vec 0,&1)) = inside s /\
                    IMAGE g' (sphere(vec 0,&1)) = s /\
                    IMAGE g' ((:real^2) DIFF cball(vec 0,&1)) = outside s` in
  CARATHEODORY_CONFORMAL_EXTENSION_THEOREM,JORDAN_SCHOENFLIES_CIRCLE;;

let JORDAN_SCHOENFLIES = `!g h f f'.
        simple_path g /\ simple_path h /\
        homeomorphism (path_image g,path_image h) (f,f')
        ==> ?k k'. homeomorphism ((:real^2),(:real^2)) (k,k') /\
                   (!x. x IN path_image g ==> k x = f x) /\
                   (!y. y IN path_image h ==> k' y = f' y) /\
                   IMAGE k (path_image g) = path_image h /\
                   IMAGE k (inside(path_image g)) = inside(path_image h) /\
                   IMAGE k (outside(path_image g)) = outside(path_image h)`;;

let JORDAN_SCHOENFLIES_S2 = `!g h f f' z:real^3 r.
        simple_path g /\ simple_path h /\
        path_image g SUBSET sphere(z,r) /\
        path_image h SUBSET sphere(z,r) /\
        homeomorphism (path_image g,path_image h) (f,f')
        ==> ?k k'. homeomorphism (sphere(z,r),sphere(z,r)) (k,k') /\
                   (!x. x IN path_image g ==> k x = f x) /\
                   (!y. y IN path_image h ==> k' y = f' y)`;;
