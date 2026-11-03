(* ========================================================================= *)
(* Faces, extreme points, polytopes, polyhedra etc.                          *)
(* ========================================================================= *)

needs "Multivariate/paths.ml";;

(* ------------------------------------------------------------------------- *)
(* Faces of a (usually convex) set.                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("face_of",(12,"right"));;

let face_of = new_definition
 `t face_of s <=>
        t SUBSET s /\ convex t /\
        !a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b)
                ==> a IN t /\ b IN t`;;

let FACE_OF_TRANSLATION_EQ = `!a f s:real^N->bool.
        (IMAGE (\x. a + x) f) face_of (IMAGE (\x. a + x) s) <=> f face_of s`;;

add_translation_invariants [FACE_OF_TRANSLATION_EQ];;

let FACE_OF_LINEAR_IMAGE = `!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) face_of (IMAGE f s) <=> c face_of s)`;;

add_linear_invariants [FACE_OF_LINEAR_IMAGE];;

let FACE_OF_REFL = `!s. convex s ==> s face_of s`;;

let FACE_OF_REFL_EQ = `!s. s face_of s <=> convex s`;;

let EMPTY_FACE_OF = `!s. {} face_of s`;;

let FACE_OF_EMPTY = `!s. s face_of {} <=> s = {}`;;

let FACE_OF_TRANS = `!s t u. s face_of t /\ t face_of u
           ==> s face_of u`;;

let FACE_OF_FACE = `!f s t.
        t face_of s
        ==> (f face_of t <=> f face_of s /\ f SUBSET t)`;;

let FACE_OF_SUBSET = `!f s t. f face_of s /\ f SUBSET t /\ t SUBSET s ==> f face_of t`;;

let FACE_OF_SLICE = `!f s t.
        f face_of s /\ convex t
        ==> (f INTER t) face_of (s INTER t)`;;

let FACE_OF_INTER = `!s t1 t2. t1 face_of s /\ t2 face_of s
             ==> (t1 INTER t2) face_of s`;;

let FACE_OF_INTERS = `!P s. ~(P = {}) /\ (!t. t IN P ==> t face_of s)
         ==> (INTERS P) face_of s`;;

let FACE_OF_INTER_INTER = `!f t f' t'.
     f face_of t /\ f' face_of t' ==> (f INTER f') face_of (t INTER t')`;;

let FACE_OF_STILLCONVEX = `!s t:real^N->bool.
        convex s
        ==> (t face_of s <=>
             t SUBSET s /\
             convex(s DIFF t) /\
             t = (affine hull t) INTER s)`;;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG = `!s a:real^N b.
        convex(s INTER {x | a dot x = b}) /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) face_of s`;;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG = `!s a:real^N b.
        convex(s INTER {x | a dot x = b}) /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) face_of s`;;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE = `!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) face_of s`;;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE = `!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) face_of s`;;

let FACE_OF_IMP_SUBSET = `!s t. t face_of s ==> t SUBSET s`;;

let FACE_OF_IMP_CONVEX = `!s t. t face_of s ==> convex t`;;

let FACE_OF_IMP_CLOSED = `!s t. convex s /\ closed s /\ t face_of s ==> closed t`;;

let FACE_OF_IMP_COMPACT = `!s t. convex s /\ compact s /\ t face_of s ==> compact t`;;

let FACE_OF_INTER_SUBFACE = `!c1 c2 d1 d2:real^N->bool.
        (c1 INTER c2) face_of c1 /\ (c1 INTER c2) face_of c2 /\
        d1 face_of c1 /\ d2 face_of c2
        ==> (d1 INTER d2) face_of d1 /\ (d1 INTER d2) face_of d2`;;

let SUBSET_OF_FACE_OF = `!s t u:real^N->bool.
      t face_of s /\ u SUBSET s /\
      ~(DISJOINT t (relative_interior u))
      ==> u SUBSET t`;;

let FACE_OF_EQ = `!s t u:real^N->bool.
        t face_of s /\ u face_of s /\
        ~(DISJOINT (relative_interior t) (relative_interior u))
        ==> t = u`;;

let FACE_OF_DISJOINT_RELATIVE_INTERIOR = `!f s:real^N->bool.
        f face_of s /\ ~(f = s) ==> f INTER relative_interior s = {}`;;

let FACE_OF_DISJOINT_INTERIOR = `!f s:real^N->bool.
        f face_of s /\ ~(f = s) ==> f INTER interior s = {}`;;

let SUBSET_OF_FACE_OF_AFFINE_HULL = `!s t u:real^N->bool.
        t face_of s /\ convex s /\ u SUBSET s /\
        ~DISJOINT (affine hull t) (relative_interior u)
        ==> u SUBSET t`;;

let AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR = `!s f:real^N->bool.
        convex s /\ f face_of s /\ ~(f = s)
        ==> affine hull f INTER relative_interior s = {}`;;

let FACE_OF_SUBSET_RELATIVE_BOUNDARY = `!s f:real^N->bool.
        f face_of s /\ ~(f = s) ==> f SUBSET (s DIFF relative_interior s)`;;

let FACE_OF_SUBSET_RELATIVE_FRONTIER = `!s f:real^N->bool.
        f face_of s /\ ~(f = s) ==> f SUBSET relative_frontier s`;;

let FACE_OF_SUBSET_RELATIVE_FRONTIER_AFF_DIM = `!f s:real^N->bool.
        f face_of s /\ aff_dim f < aff_dim s
        ==> f SUBSET relative_frontier s`;;

let FACE_OF_SUBSET_FRONTIER_AFF_DIM = `!f s:real^N->bool.
        f face_of s /\ aff_dim f < &(dimindex(:N))
        ==> f SUBSET frontier s`;;

let FACE_OF_AFF_DIM_LT = `!f s:real^N->bool.
        convex s /\ f face_of s /\ ~(f = s) ==> aff_dim f < aff_dim s`;;

let FACE_OF_CONVEX_HULLS = `!f s:real^N->bool.
        FINITE s /\ f SUBSET s /\
        DISJOINT (affine hull f) (convex hull (s DIFF f))
        ==> (convex hull f) face_of (convex hull s)`;;

let FACE_OF_CONVEX_HULL_INSERT = `!f s a:real^N.
        FINITE s /\ ~(a IN affine hull s) /\ f face_of (convex hull s)
        ==> f face_of (convex hull (a INSERT s))`;;

let FACE_OF_AFFINE_TRIVIAL = `!s f:real^N->bool.
        affine s /\ f face_of s ==> f = {} \/ f = s`;;

let FACE_OF_AFFINE_EQ = `!s:real^N->bool f. affine s ==> (f face_of s <=> f = {} \/ f = s)`;;

let INTERS_FACES_FINITE_BOUND = `!s f:(real^N->bool)->bool.
        convex s /\ (!c. c IN f ==> c face_of s)
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 1 /\
                 INTERS f' = INTERS f`;;

let INTERS_FACES_FINITE_ALTBOUND = `!s f:(real^N->bool)->bool.
        (!c. c IN f ==> c face_of s)
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 2 /\
                 INTERS f' = INTERS f`;;

let FACES_OF_TRANSLATION = `!s a:real^N.
        {f | f face_of IMAGE (\x. a + x) s} =
        IMAGE (IMAGE (\x. a + x)) {f | f face_of s}`;;

let FACES_OF_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> {t | t face_of (IMAGE f s)} = IMAGE (IMAGE f) {t | t face_of s}`;;

let FACE_OF_CONIC = `!s f:real^N->bool. conic s /\ f face_of s ==> conic f`;;

let FACE_OF_PCROSS = `!f s:real^M->bool f' s':real^N->bool.
        f face_of s /\ f' face_of s' ==> (f PCROSS f') face_of (s PCROSS s')`;;

let FACE_OF_PCROSS_DECOMP = `!s:real^M->bool s':real^N->bool c.
        c face_of (s PCROSS s') <=>
        ?f f'. f face_of s /\ f' face_of s' /\ c = f PCROSS f'`;;

let FACE_OF_PCROSS_EQ = `!f s:real^M->bool f' s':real^N->bool.
        (f PCROSS f') face_of (s PCROSS s') <=>
        f = {} \/ f' = {} \/ f face_of s /\ f' face_of s'`;;

let HYPERPLANE_FACE_OF_HALFSPACE_LE = `!a:real^N b. {x | a dot x = b} face_of {x | a dot x <= b}`;;

let HYPERPLANE_FACE_OF_HALFSPACE_GE = `!a:real^N b. {x | a dot x = b} face_of {x | a dot x >= b}`;;

let FACE_OF_HALFSPACE_LE = `!f a:real^N b.
         f face_of {x | a dot x <= b} <=>
         f = {} \/ f = {x | a dot x = b} \/ f = {x | a dot x <= b}`;;

let FACE_OF_HALFSPACE_GE = `!f a:real^N b.
         f face_of {x | a dot x >= b} <=>
         f = {} \/ f = {x | a dot x = b} \/ f = {x | a dot x >= b}`;;

let RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE = `!s x:real^N.
        convex s /\ x IN s /\ ~(x IN relative_interior s)
        ==> ?f. f face_of s /\ ~(f = s) /\ x IN f`;;

let RELATIVE_FRONTIER_OF_CONVEX_CLOSED = `!s:real^N->bool.
        convex s /\ closed s
        ==> relative_frontier s = UNIONS {f | f face_of s /\ ~(f = s)}`;;

let IN_RELATIVE_INTERIOR_OF_FACE = `!s:real^N->bool x.
        convex s /\ x IN s ==> ?f. f face_of s /\ x IN relative_interior f`;;

let CONVEX_FACIAL_PARTITION = `!s:real^N->bool.
        convex s ==> UNIONS {relative_interior f | f face_of s} = s`;;

let IN_RELATIVE_INTERIOR_OF_UNIQUE_FACE = `!s:real^N->bool x.
        convex s /\ x IN s ==> ?!f. f face_of s /\ x IN relative_interior f`;;

let RELATIVE_INTERIOR_SUBSET_OF_PROPER_FACE = `!s t:real^N->bool.
        convex s /\ t SUBSET s /\
        ~(relative_interior t DIFF relative_interior s = {})
        ==> ?f. f face_of s /\ ~(f = s) /\ t SUBSET f`;;

let CONVEX_RELATIVE_BOUNDARY_SUBSET_OF_PROPER_FACE = `!s t:real^N->bool.
        convex s /\ ~(s = {}) /\
        convex t /\ t SUBSET s DIFF relative_interior s
        ==> ?f. f face_of s /\ ~(f = s) /\ t SUBSET f`;;

let RELATIVE_FRONTIER_FACIAL_PARTITION_ALT = `!s:real^N->bool.
        convex s /\ closed s
        ==> UNIONS { relative_interior f | f face_of s /\ ~(f = s)} =
            relative_frontier s`;;

let RELATIVE_FRONTIER_FACIAL_PARTITION = `!s:real^N->bool.
        convex s /\ closed s
        ==> UNIONS { relative_interior f |
                     f face_of s /\ aff_dim f < aff_dim s} =
            relative_frontier s`;;

let FRONTIER_OF_CONVEX_CLOSED = `!s:real^N->bool.
        convex s /\ closed s
        ==> frontier s =
            UNIONS {f | f face_of s /\ aff_dim f < &(dimindex(:N))}`;;

let FACE_OF_INTER_AS_INTER_OF_FACE = `!s t f:real^N->bool.
        convex s /\ convex t /\ f face_of (s INTER t)
        ==> ?k l. k face_of s /\ l face_of t /\ k INTER l = f`;;

(* ------------------------------------------------------------------------- *)
(* Exposed faces (faces that are intersection with supporting hyperplane).   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("exposed_face_of",(12,"right"));;

let exposed_face_of = new_definition
 `t exposed_face_of s <=>
    t face_of s /\
    ?a b. s SUBSET {x | a dot x <= b} /\ t = s INTER {x | a dot x = b}`;;

let EXPOSED_FACE_OF_IMP_FACE_OF = `!s t:real^N->bool. t exposed_face_of s ==> t face_of s`;;

let EMPTY_EXPOSED_FACE_OF = `!s:real^N->bool. {} exposed_face_of s`;;

let EXPOSED_FACE_OF_REFL_EQ = `!s:real^N->bool. s exposed_face_of s <=> convex s`;;

let EXPOSED_FACE_OF_REFL = `!s:real^N->bool. convex s ==> s exposed_face_of s`;;

let EXPOSED_FACE_OF = `!s t. t exposed_face_of s <=>
             t face_of s /\
             (t = {} \/ t = s \/
              ?a b. ~(a = vec 0) /\
                    s SUBSET {x:real^N | a dot x <= b} /\
                    t = s INTER {x | a dot x = b})`;;

let EXPOSED_FACE_OF_TRANSLATION_EQ = `!a f s:real^N->bool.
        (IMAGE (\x. a + x) f) exposed_face_of (IMAGE (\x. a + x) s) <=>
        f exposed_face_of s`;;

add_translation_invariants [EXPOSED_FACE_OF_TRANSLATION_EQ];;

let EXPOSED_FACE_OF_LINEAR_IMAGE = `!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
      ==> ((IMAGE f c) exposed_face_of (IMAGE f s) <=> c exposed_face_of s)`;;

let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE = `!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s`;;

let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE = `!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s`;;

let EXPOSED_FACE_OF_INTER = `!s t u:real^N->bool.
        t exposed_face_of s /\ u exposed_face_of s
        ==> (t INTER u) exposed_face_of s`;;

let EXPOSED_FACE_OF_INTERS = `!P s:real^N->bool.
        ~(P = {}) /\ (!t. t IN P ==> t exposed_face_of s)
        ==> INTERS P exposed_face_of s`;;

let EXPOSED_FACE_OF_SUMS = `!s t f:real^N->bool.
        convex s /\ convex t /\
        f exposed_face_of {x + y | x IN s /\ y IN t}
        ==> ?k l. k exposed_face_of s /\ l exposed_face_of t /\
                  f = {x + y | x IN k /\ y IN l}`;;

let EXPOSED_FACE_OF_PARALLEL = `!t s. t exposed_face_of s <=>
         t face_of s /\
          ?a b. s SUBSET {x:real^N | a dot x <= b} /\
                t = s INTER {x | a dot x = b} /\
                (~(t = {}) /\ ~(t = s) ==> ~(a = vec 0)) /\
                (!w. w IN affine hull s /\ ~(t = s)
                     ==> (w + a) IN affine hull s)`;;

let RELATIVE_BOUNDARY_POINT_IN_EXPOSED_FACE = `!s x:real^N.
           convex s /\ x IN s /\ ~(x IN relative_interior s)
           ==> ?f. f exposed_face_of s /\ ~(f = s) /\ x IN f`;;

(* ------------------------------------------------------------------------- *)
(* Extreme points of a set, which are its singleton faces.                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("extreme_point_of",(12,"right"));;

let extreme_point_of = new_definition
 `x extreme_point_of s <=>
    x IN s /\ !a b. a IN s /\ b IN s ==> ~(x IN segment(a,b))`;;

let EXTREME_POINT_RELATIVE_FRONTIER = `!s x:real^N.
       convex s /\ x IN s DIFF relative_interior s /\
       (!a b. {a,b} SUBSET s DIFF relative_interior s ==> ~(x IN segment(a,b)))
       ==> x extreme_point_of s`;;

let EXTREME_POINT_OF_STILLCONVEX_IMP = `!s x:real^N. x IN s /\ convex(s DELETE x) ==> x extreme_point_of s`;;

let EXTREME_POINTS_OF_STILLCONVEX = `!s t:real^N->bool.
        convex s /\ t SUBSET {x | x extreme_point_of s} ==> convex(s DIFF t)`;;

let EXTREME_POINT_OF_STILLCONVEX = `!s x:real^N.
        convex s ==> (x extreme_point_of s <=> x IN s /\ convex(s DELETE x))`;;

let FACE_OF_SING = `!x s. {x} face_of s <=> x extreme_point_of s`;;

let FACE_OF_AFF_DIM_0 = `!s f:real^N->bool.
        f face_of s /\ aff_dim f = &0 <=> ?a. a extreme_point_of s /\ f = {a}`;;

let EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR = `!s x:real^N.
        x extreme_point_of s /\ ~(s = {x})
        ==> ~(x IN relative_interior s)`;;

let EXTREME_POINT_NOT_IN_INTERIOR = `!s x:real^N. x extreme_point_of s ==> ~(x IN interior s)`;;

let EXTREME_POINT_IN_RELATIVE_FRONTIER = `!s x:real^N.
        x extreme_point_of s /\ ~(s = {x}) ==> x IN relative_frontier s`;;

let EXTREME_POINT_IN_FRONTIER = `!s x:real^N. x extreme_point_of s ==> x IN frontier s`;;

let EXTREME_POINT_OF_FACE = `!f s v. f face_of s
           ==> (v extreme_point_of f <=> v extreme_point_of s /\ v IN f)`;;

let EXTREME_POINT_OF_MIDPOINT = `!s x:real^N.
        convex s
        ==> (x extreme_point_of s <=>
             x IN s /\
             !a b. a IN s /\ b IN s /\ x = midpoint(a,b) ==> x = a /\ x = b)`;;

let EXTREME_POINT_OF_CONVEX_HULL = `!x:real^N s. x extreme_point_of (convex hull s) ==> x IN s`;;

let EXTREME_POINTS_OF_CONVEX_HULL = `!s. {x | x extreme_point_of (convex hull s)} SUBSET s`;;

let EXTREME_POINT_OF_EMPTY = `!x. ~(x extreme_point_of {})`;;

let EXTREME_POINT_OF_SING = `!a x. x extreme_point_of {a} <=> x = a`;;

let EXTREME_POINT_OF_TRANSLATION_EQ = `!a:real^N x s.
           (a + x) extreme_point_of (IMAGE (\x. a + x) s) <=>
           x extreme_point_of s`;;

add_translation_invariants [EXTREME_POINT_OF_TRANSLATION_EQ];;

let EXTREME_POINT_OF_LINEAR_IMAGE = `!f:real^M->real^N.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((f x) extreme_point_of (IMAGE f s) <=> x extreme_point_of s)`;;

add_linear_invariants [EXTREME_POINT_OF_LINEAR_IMAGE];;

let EXTREME_POINTS_OF_TRANSLATION = `!a s. {x:real^N | x extreme_point_of (IMAGE (\x. a + x) s)} =
         IMAGE (\x. a + x) {x | x extreme_point_of s}`;;

let EXTREME_POINT_OF_INTER = `!x s t. x extreme_point_of s /\ x extreme_point_of t
           ==> x extreme_point_of (s INTER t)`;;

let EXTREME_POINT_OF_INTER_GEN = `!x s t. (x extreme_point_of s \/ x extreme_point_of t) /\ x IN s INTER t
           ==> x extreme_point_of (s INTER t)`;;

let EXTREME_POINTS_OF_LINEAR_IMAGE = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> {y | y extreme_point_of (IMAGE f s)} =
            IMAGE f {x | x extreme_point_of s}`;;

let EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE = `!s a b c. (!x. x IN s ==> a dot x <= b) /\
             s INTER {x | a dot x = b} = {c}
             ==> c extreme_point_of s`;;

let EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE = `!s a b c. (!x. x IN s ==> a dot x >= b) /\
             s INTER {x | a dot x = b} = {c}
             ==> c extreme_point_of s`;;

let EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE = `!s a b c:real^N.
        (!x. x IN s ==> a dot x <= b) /\
        s INTER {x | a dot x = b} = {c}
        ==> {c} exposed_face_of s`;;

let EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE = `!s a b c:real^N.
        (!x. x IN s ==> a dot x >= b) /\
        s INTER {x | a dot x = b} = {c}
        ==> {c} exposed_face_of s`;;

let EXPOSED_POINT_OF_FURTHEST_POINT = `!s a b:real^N.
        b IN s /\ (!x. x IN s ==> dist(a,x) <= dist(a,b))
        ==> {b} exposed_face_of s`;;

let COLLINEAR_EXTREME_POINTS = `!s. collinear s
       ==> FINITE {x:real^N | x extreme_point_of s} /\
           CARD {x | x extreme_point_of s} <= 2`;;

let EXTREME_POINT_OF_CONIC = `!s x:real^N.
        conic s /\ x extreme_point_of s ==> x = vec 0`;;

let EXTREME_POINT_OF_CONVEX_HULL_INSERT = `!s a:real^N.
        FINITE s /\ ~(a IN convex hull s)
        ==> a extreme_point_of (convex hull (a INSERT s))`;;

let FACE_OF_CONIC_HULL = `!f s:real^N->bool.
      f face_of s /\ ~(vec 0 IN affine hull s)
      ==> (conic hull f) face_of (conic hull s)`;;

let FACE_OF_CONIC_HULL_REV = `!s f:real^N->bool.
        f face_of (conic hull s) /\ ~(vec 0 IN affine hull s)
        ==> f = {vec 0} \/ ?f'. f' face_of s /\ conic hull f' = f`;;

let EXTREME_POINT_OF_CONIC_HULL = `!s x:real^N.
        ~(vec 0 IN affine hull s)
        ==> (x extreme_point_of conic hull s <=> x = vec 0 /\ ~(s = {}))`;;

let FACE_OF_CONIC_HULL_EQ = `!s f:real^N->bool.
     ~(vec 0 IN affine hull s)
     ==> (f face_of (conic hull s) <=>
          f = {vec 0} /\ ~(s = {}) \/ ?f'. f' face_of s /\ conic hull f' = f)`;;

let EXTREME_POINT_OF_CBALL = `!a r x:real^N.
        x extreme_point_of cball(a,r) <=> x IN sphere(a,r)`;;

(* ------------------------------------------------------------------------- *)
(* Closure and (relative) openness of conic hulls etc.                       *)
(* ------------------------------------------------------------------------- *)

let CLOSED_IN_CONIC_HULL = `!s t:real^N->bool.
        compact t /\ ~(vec 0 IN t) /\ t SUBSET s
        ==> closed_in (subtopology euclidean (conic hull s))
                      (conic hull t)`;;

let CLOSED_CONIC_HULL = `!s:real^N->bool.
     vec 0 IN relative_interior s \/ compact s /\ ~(vec 0 IN s)
     ==> closed(conic hull s)`;;

let CONIC_CLOSURE = `!s:real^N->bool. conic s ==> conic(closure s)`;;

let CLOSURE_CONIC_HULL = `!s:real^N->bool.
        vec 0 IN relative_interior s \/ bounded s /\ ~(vec 0 IN closure s)
        ==> closure(conic hull s) = conic hull (closure s)`;;

let OPEN_IN_SAME_CONIC_HULL = `!u s:real^N->bool.
        conic u /\ open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean u) (conic hull s DELETE vec 0)`;;

let OPEN_CONIC_HULL = `!s:real^N->bool. open s ==> open(conic hull s DELETE vec 0)`;;

let OPEN_IN_CONIC_HULL = `!u s:real^N->bool.
        open_in (subtopology euclidean (affine hull u)) s
        ==> open_in (subtopology euclidean (affine hull (conic hull u)))
                    (conic hull s DELETE vec 0)`;;

let CONIC_INTERIOR_INSERT = `!s:real^N->bool. conic s ==> conic(vec 0 INSERT interior s)`;;

let CONIC_INTERIOR = `!s:real^N->bool. conic s /\ vec 0 IN interior s ==> conic(interior s)`;;

let CONIC_RELATIVE_INTERIOR_INSERT = `!s:real^N->bool. conic s ==> conic(vec 0 INSERT relative_interior s)`;;

let CONIC_RELATIVE_INTERIOR = `!s:real^N->bool.
        conic s /\ vec 0 IN relative_interior s
        ==> conic(relative_interior s)`;;

let CONIC_HULL_RELATIVE_INTERIOR_SUBSET = `!s:real^N->bool.
        conic hull (relative_interior s) DELETE (vec 0) SUBSET
        relative_interior(conic hull s)`;;

let CONIC_SUBSET_AS_CONIC_HULL = `!s c:real^N->bool.
        conic c /\ ~(c = {vec 0}) /\ c SUBSET conic hull s
        ==> conic hull (s INTER c) = c`;;

let RELATIVE_INTERIOR_CONIC_HULL = `!s:real^N->bool.
        ~(vec 0 IN affine hull s)
        ==> relative_interior(conic hull s) =
            conic hull (relative_interior s) DELETE (vec 0)`;;

let CONIC_HULL_RELATIVE_INTERIOR = `!s:real^N->bool.
        ~(vec 0 IN affine hull s)
        ==> conic hull (relative_interior s) =
            if relative_interior s = {} then {}
            else (vec 0) INSERT relative_interior(conic hull s)`;;

let CONIC_HULL_DIFF = `!s t:real^N->bool.
        ~(vec 0 IN affine hull s) /\ t SUBSET s
        ==> conic hull (s DIFF t) =
            if t = s then {}
            else conic hull s DIFF (conic hull t DELETE vec 0)`;;

let CONIC_HULL_INTER = `!s t:real^N->bool.
        ~(vec 0 IN affine hull (s UNION t))
        ==> conic hull (s INTER t) =
            if s INTER t = {} then {}
            else conic hull s INTER conic hull t`;;

let INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER = `!s t u:real^N->bool.
        convex u /\ vec 0 IN relative_interior u /\
        s UNION t SUBSET relative_frontier u
        ==> conic hull s INTER conic hull t =
            if s = {} \/ t = {} then {}
            else if s INTER t = {} then {vec 0}
            else conic hull (s INTER t)`;;

let RELATIVE_FRONTIER_CONIC_HULL = `!s:real^N->bool.
        bounded s /\ ~(vec 0 IN affine hull s)
        ==> relative_frontier(conic hull s) =
            if ?a. s = {a} then {vec 0}
            else conic hull (relative_frontier s)`;;

let CONIC_HULL_RELATIVE_FRONTIER = `!s:real^N->bool.
        bounded s /\ ~(vec 0 IN affine hull s)
        ==> conic hull (relative_frontier s) =
            if ?a. s = {a} then {}
            else relative_frontier(conic hull s)`;;

let INTER_CONIC_HULL = `!s t:real^N->bool.
        ~(vec 0 IN affine hull (s UNION t))
        ==> conic hull s INTER conic hull t =
            if s = {} \/ t = {} then {}
            else if s INTER t = {} then {vec 0}
            else conic hull (s INTER t)`;;

let RELATIVE_INTERIOR_CONIC_HULL_0 = `!s:real^N->bool.
        convex s
        ==> (vec 0 IN relative_interior(conic hull s) <=>
             vec 0 IN relative_interior s)`;;

(* ------------------------------------------------------------------------- *)
(* Facets.                                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("facet_of",(12, "right"));;

let facet_of = new_definition
 `f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1`;;

let FACET_OF_EMPTY = `!s. ~(s facet_of {})`;;

let FACET_OF_REFL = `!s. ~(s facet_of s)`;;

let FACET_OF_IMP_FACE_OF = `!f s. f facet_of s ==> f face_of s`;;

let FACET_OF_IMP_SUBSET = `!f s. f facet_of s ==> f SUBSET s`;;

let FACET_OF_IMP_PROPER = `!f s. f facet_of s ==> ~(f = {}) /\ ~(f = s)`;;

let FACET_OF_TRANSLATION_EQ = `!a:real^N f s.
        (IMAGE (\x. a + x) f) facet_of (IMAGE (\x. a + x) s) <=> f facet_of s`;;

add_translation_invariants [FACET_OF_TRANSLATION_EQ];;

let FACET_OF_LINEAR_IMAGE = `!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) facet_of (IMAGE f s) <=> c facet_of s)`;;

add_linear_invariants [FACET_OF_LINEAR_IMAGE];;

let HYPERPLANE_FACET_OF_HALFSPACE_LE = `!a:real^N b.
        ~(a = vec 0) ==> {x | a dot x = b} facet_of {x | a dot x <= b}`;;

let HYPERPLANE_FACET_OF_HALFSPACE_GE = `!a:real^N b.
        ~(a = vec 0) ==> {x | a dot x = b} facet_of {x | a dot x >= b}`;;

let FACET_OF_HALFSPACE_LE = `!f a:real^N b.
        f facet_of {x | a dot x <= b} <=>
        ~(a = vec 0) /\ f = {x | a dot x = b}`;;

let FACET_OF_HALFSPACE_GE = `!f a:real^N b.
        f facet_of {x | a dot x >= b} <=>
        ~(a = vec 0) /\ f = {x | a dot x = b}`;;

let EXPOSED_FACET_OF = `!s t:real^N->bool. convex s /\ t facet_of s ==> t exposed_face_of s`;;

let OPEN_IN_RELATIVE_FRONTIER_INTERIOR_FACET = `!s f:real^N->bool.
        convex s /\ f facet_of s
        ==> open_in (subtopology euclidean (relative_frontier s))
                    (relative_interior f)`;;

(* ------------------------------------------------------------------------- *)
(* Extreme points of convex closed set with aff_dim <= 2 are closed.         *)
(* ------------------------------------------------------------------------- *)

let CLOSED_EXTREME_POINTS_2D = `!s:real^N->bool.
        closed s /\ convex s /\ aff_dim s <= &2
        ==> closed {x | x extreme_point_of s}`;;

(* ------------------------------------------------------------------------- *)
(* Edges, i.e. faces of affine dimension 1.                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("edge_of",(12, "right"));;

let edge_of = new_definition
 `e edge_of s <=> e face_of s /\ aff_dim e = &1`;;

let EDGE_OF_TRANSLATION_EQ = `!a:real^N f s.
        (IMAGE (\x. a + x) f) edge_of (IMAGE (\x. a + x) s) <=> f edge_of s`;;

add_translation_invariants [EDGE_OF_TRANSLATION_EQ];;

let EDGE_OF_LINEAR_IMAGE = `!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) edge_of (IMAGE f s) <=> c edge_of s)`;;

add_linear_invariants [EDGE_OF_LINEAR_IMAGE];;

let EDGE_OF_IMP_SUBSET = `!s t. s edge_of t ==> s SUBSET t`;;

(* ------------------------------------------------------------------------- *)
(* Existence of extreme points.                                              *)
(* ------------------------------------------------------------------------- *)

let EXTREME_POINT_EXISTS_CONVEX = `!s:real^N->bool.
        compact s /\ convex s /\ ~(s = {}) ==> ?x. x extreme_point_of s`;;

(* ------------------------------------------------------------------------- *)
(* Krein-Milman, the weaker form as in more general spaces first.            *)
(* ------------------------------------------------------------------------- *)

let KREIN_MILMAN = `!s:real^N->bool.
        convex s /\ compact s
        ==> s = closure(convex hull {x | x extreme_point_of s})`;;

(* ------------------------------------------------------------------------- *)
(* Now the sharper form.                                                     *)
(* ------------------------------------------------------------------------- *)

let KREIN_MILMAN_MINKOWSKI = `!s:real^N->bool.
        convex s /\ compact s
        ==> s = convex hull {x | x extreme_point_of s}`;;

let KREIN_MILMAN_EQ = `!s e:real^N->bool.
        compact s /\ convex s
        ==> (convex hull e = s <=>
             e SUBSET s /\ {x | x extreme_point_of s} SUBSET e)`;;

(* ------------------------------------------------------------------------- *)
(* Applying it to convex hulls of explicitly indicated finite sets.          *)
(* ------------------------------------------------------------------------- *)

let KREIN_MILMAN_POLYTOPE = `!s. FINITE s
       ==> convex hull s =
           convex hull {x | x extreme_point_of (convex hull s)}`;;

let EXTREME_POINTS_OF_CONVEX_HULL_EQ = `!s:real^N->bool.
        compact s /\
        (!t. t PSUBSET s ==> ~(convex hull t = convex hull s))
        ==> {x | x extreme_point_of (convex hull s)} = s`;;

let EXTREME_POINT_OF_CONVEX_HULL_EQ = `!s x:real^N.
        compact s /\
        (!t. t PSUBSET s ==> ~(convex hull t = convex hull s))
        ==> (x extreme_point_of (convex hull s) <=> x IN s)`;;

let EXTREME_POINT_OF_CONVEX_HULL_CONVEX_INDEPENDENT = `!s x:real^N.
        compact s /\
        (!a. a IN s ==> ~(a IN convex hull (s DELETE a)))
        ==> (x extreme_point_of (convex hull s) <=> x IN s)`;;

let EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT = `!s x. ~affine_dependent s
         ==> (x extreme_point_of (convex hull s) <=> x IN s)`;;

let EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT = `!s:real^N->bool.
        ~affine_dependent s ==> {x | x extreme_point_of convex hull s} = s`;;

let SIMPLEX_VERTICES_UNIQUE = `!s t:real^N->bool.
        ~affine_dependent s /\ ~affine_dependent t /\
        convex hull s = convex hull t
        ==> s = t`;;

let EXTREME_POINT_OF_CONVEX_HULL_2 = `!a b x. x extreme_point_of (convex hull {a,b}) <=> x = a \/ x = b`;;

let EXTREME_POINT_OF_SEGMENT = `!a b x:real^N. x extreme_point_of segment[a,b] <=> x = a \/ x = b`;;

let FACE_OF_CONVEX_HULL_SUBSET = `!s t:real^N->bool.
        compact s /\ t face_of (convex hull s)
        ==> ?s'. s' SUBSET s /\ t = convex hull s'`;;

let FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT = `!s t:real^N->bool.
        ~affine_dependent s
        ==> (t face_of (convex hull s) <=>
             ?c. c SUBSET s /\ t = convex hull c)`;;

let FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT = `!s t:real^N->bool.
        ~affine_dependent s
        ==> (t facet_of (convex hull s) <=>
             ~(t = {}) /\ ?u. u IN s /\ t = convex hull (s DELETE u))`;;

let FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT = `!s t:real^N->bool.
        ~affine_dependent s
        ==> (t facet_of (convex hull s) <=>
             2 <= CARD s /\ ?u. u IN s /\ t = convex hull (s DELETE u))`;;

let SEGMENT_FACE_OF = `!s a b:real^N.
    segment[a,b] face_of s ==> a extreme_point_of s /\ b extreme_point_of s`;;

let SEGMENT_EDGE_OF = `!s a b:real^N.
        segment[a,b] edge_of s
        ==> ~(a = b) /\ a extreme_point_of s /\ b extreme_point_of s`;;

let EXTREME_POINT_OF_CONVEX_HULL_INSERT_EQ = `!s a x:real^N.
        FINITE s /\ ~(a IN affine hull s)
        ==> (x extreme_point_of (convex hull (a INSERT s)) <=>
             x = a \/ x extreme_point_of (convex hull s))`;;

let FACE_OF_CONVEX_HULL_INSERT_EQ = `!f s a:real^N.
        FINITE s /\ ~(a IN affine hull s)
        ==> (f face_of (convex hull (a INSERT s)) <=>
             f face_of (convex hull s) \/
             ?f'. f' face_of (convex hull s) /\
                  f = convex hull (a INSERT f'))`;;

let CONVEX_HULL_REDUNDANT_SUBSET_GEN = `!s t:real^N->bool.
        compact s /\ t SUBSET s /\
        DISJOINT (s DIFF t) {x | x extreme_point_of convex hull s}
        ==> convex hull s = convex hull t`;;

let CONVEX_HULL_REDUNDANT_SUBSET = `!s t:real^N->bool.
        compact s /\ t SUBSET s /\
        s DIFF t SUBSET interior(convex hull s)
        ==> convex hull s = convex hull t`;;

let CONVEX_HULL_REDUNDANT_SUBSET_REV = `!s t:real^N->bool.
        convex hull s = convex hull t
        ==> DISJOINT (s DIFF t) {x | x extreme_point_of (convex hull s)}`;;

let CONVEX_HULL_INSERT_REDUNDANT_POINT = `!s a b c:real^N.
        a IN convex hull (c INSERT s) /\
        b IN convex hull (c INSERT s) /\
        c IN segment(a,b)
        ==> convex hull (c INSERT s) = convex hull s`;;

let CONVEX_HULL_REDUNDANT_POINT = `!s a:real^N. convex hull (s DELETE a) = convex hull s <=>
                ~(a extreme_point_of convex hull s)`;;

let HAUSDIST_FRONTIERS_CONVEX = `!s t:real^N->bool.
        convex s /\ convex t /\ bounded s /\ bounded t
        ==> hausdist(frontier s,frontier t) = hausdist(s,t)`;;

(* ------------------------------------------------------------------------- *)
(* If we perturb a set little enough, a point stays inside or outside it.    *)
(* The "inside" needs convexity in general or we could just remove a         *)
(* thin path to the point without changing the Hausdorff distance at all.    *)
(* ------------------------------------------------------------------------- *)

let HAUSDIST_STILL_OUTSIDE = `!s t x:real^N.

        bounded s /\ bounded t /\ hausdist(s,t) < setdist({x},s)
        ==> ~(x IN t)`;;

let HAUSDIST_STILL_INSIDE = `!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\ ~(t = {}) /\
        hausdist(s,t) < setdist({x},(:real^N) DIFF s)
        ==> x IN t`;;

let HAUSDIST_STILL_INSIDE_INTERIOR = `!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\ ~(t = {}) /\
        hausdist(s,t) < setdist({x},(:real^N) DIFF s)
        ==> x IN interior t`;;

let HAUSDIST_STILL_NONEMPTY_INTERIOR = `!s:real^N->bool.
      bounded s /\ convex s /\ ~(interior s = {})
      ==> ?e. &0 < e /\
              !s'. bounded s' /\ convex s' /\ ~(s' = {}) /\ hausdist(s,s') < e
                   ==> ~(interior s' = {})`;;

let HAUSDIST_STILL_SAME_PLACE_STRONG = `!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\
        ~(t = {}) /\ hausdist(s,t) < setdist({x},frontier s)
        ==> ~(x IN frontier s) /\ ~(x IN frontier t) /\ (x IN t <=> x IN s)`;;

let HAUSDIST_STILL_SAME_PLACE = `!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\
        ~(t = {}) /\ hausdist(s,t) < setdist({x},frontier s)
        ==> (x IN t <=> x IN s)`;;

let HAUSDIST_STILL_SAME_PLACE_CONIC_HULL_STRONG = `!s x:real^N.
       convex s /\ bounded s /\ ~(s = {}) /\ ~(vec 0 IN closure s) /\
       ~(x = vec 0) /\ ~(x IN frontier(conic hull s))
       ==> ?e. &0 < e /\
               !s'. convex s' /\ bounded s' /\ ~(s' = {}) /\ hausdist(s,s') < e
                    ==> ~(x IN frontier(conic hull s')) /\
                        (x IN conic hull s' <=> x IN conic hull s)`;;

let HAUSDIST_STILL_SAME_PLACE_CONIC_HULL = `!s x:real^N.
       convex s /\ bounded s /\ ~(s = {}) /\ ~(vec 0 IN closure s) /\
       ~(x IN frontier(conic hull s))
       ==> ?e. &0 < e /\
               !s'. convex s' /\ bounded s' /\ ~(s' = {}) /\ hausdist(s,s') < e
                    ==> (x IN conic hull s' <=> x IN conic hull s)`;;

let CONVEX_SYMDIFF_CLOSE_TO_FRONTIER = `!s t:real^N->bool e.
        bounded s /\ convex s /\ ~(s = {}) /\
        bounded t /\ convex t /\ ~(t = {}) /\
        hausdist(s,t) < e
        ==> (s DIFF t) UNION (t DIFF s) SUBSET
            {u + v:real^N | u IN frontier s /\ v IN ball(vec 0,e)}`;;

(* ------------------------------------------------------------------------- *)
(* Polytopes.                                                                *)
(* ------------------------------------------------------------------------- *)

let polytope = new_definition
 `polytope s <=> ?v. FINITE v /\ s = convex hull v`;;

let POLYTOPE_TRANSLATION_EQ = `!a s. polytope (IMAGE (\x:real^N. a + x) s) <=> polytope s`;;

add_translation_invariants [POLYTOPE_TRANSLATION_EQ];;

let POLYTOPE_LINEAR_IMAGE = `!f:real^M->real^N p.
        linear f /\ polytope p ==> polytope(IMAGE f p)`;;

let POLYTOPE_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (polytope (IMAGE f s) <=> polytope s)`;;

let POLYTOPE_EMPTY = `polytope {}`;;

let POLYTOPE_NEGATIONS = `!s:real^N->bool. polytope s ==> polytope(IMAGE (--) s)`;;

let POLYTOPE_CONVEX_HULL = `!s. FINITE s ==> polytope(convex hull s)`;;

let POLYTOPE_SEGMENT = `!a b:real^N. polytope(segment[a,b])`;;

let POLYTOPE_PCROSS = `!s:real^M->bool t:real^N->bool.
        polytope s /\ polytope t ==> polytope(s PCROSS t)`;;

let POLYTOPE_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        polytope(s PCROSS t) <=>
        s = {} \/ t = {} \/ polytope s /\ polytope t`;;

let FACE_OF_POLYTOPE_POLYTOPE = `!f s:real^N->bool. polytope s /\ f face_of s ==> polytope f`;;

let FINITE_POLYTOPE_FACES = `!s:real^N->bool. polytope s ==> FINITE {f | f face_of s}`;;

let FINITE_POLYTOPE_FACETS = `!s:real^N->bool. polytope s ==> FINITE {f | f facet_of s}`;;

let POLYTOPE_INTERVAL = `!a b. polytope(interval[a,b])`;;

let POLYTOPE_SING = `!a. polytope {a}`;;

let POLYTOPE_SCALING = `!c s:real^N->bool. polytope s ==> polytope (IMAGE (\x. c % x) s)`;;

let POLYTOPE_SCALING_EQ = `!s:real^N->bool c.
        polytope (IMAGE (\x. c % x) s) <=> c = &0 \/ polytope s`;;

let POLYTOPE_AFFINITY_EQ = `!s m c:real^N.
        polytope (IMAGE (\x. m % x + c) s) <=> m = &0 \/ polytope s`;;

let POLYTOPE_AFFINITY = `!s m c:real^N. polytope s ==> polytope (IMAGE (\x. m % x + c) s)`;;

let POLYTOPE_SUMS = `!s t:real^N->bool.
        polytope s /\ polytope t ==> polytope {x + y | x IN s /\ y IN t}`;;

let POLYTOPE_IMP_COMPACT = `!s. polytope s ==> compact s`;;

let POLYTOPE_IMP_CONVEX = `!s. polytope s ==> convex s`;;

let POLYTOPE_IMP_CLOSED = `!s. polytope s ==> closed s`;;

let POLYTOPE_IMP_BOUNDED = `!s. polytope s ==> bounded s`;;

let POLYTOPE_1 = `!s:real^1->bool. polytope s <=> ?a b. s = interval[a,b]`;;

let POLYTOPE_AFF_DIM_1 = `!p:real^N->bool.
        polytope p /\ aff_dim p = &1 <=> ?a b. ~(a = b) /\ p = segment[a,b]`;;

let FACE_OF_POLYTOPE_INSERT_EQ = `!f s a:real^N.
         polytope s /\ ~(a IN affine hull s)
         ==> (f face_of convex hull (a INSERT s) <=>
              f face_of s \/
              (?f'. f' face_of s /\ f = convex hull (a INSERT f')))`;;

(* ------------------------------------------------------------------------- *)
(* Approximation of bounded convex sets by polytopes.                        *)
(* ------------------------------------------------------------------------- *)

let CONVEX_INNER_APPROXIMATION = `!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?k. FINITE k /\ convex hull k SUBSET s /\
                hausdist(convex hull k,s) < e /\
                (k = {} ==> s = {})`;;

let CONVEX_OUTER_APPROXIMATION = `!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?k. FINITE k /\ s SUBSET convex hull k /\
                hausdist(convex hull k,s) < e`;;

let CONVEX_INNER_POLYTOPE = `!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?p. polytope p /\ p SUBSET s /\ hausdist(p,s) < e /\
                (p = {} ==> s = {})`;;

let CONVEX_OUTER_POLYTOPE = `!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?p. polytope p /\ s SUBSET p /\ hausdist(p,s) < e`;;

(* ------------------------------------------------------------------------- *)
(* Polyhedra.                                                                *)
(* ------------------------------------------------------------------------- *)

let polyhedron = new_definition
 `polyhedron s <=>
        ?f. FINITE f /\
            s = INTERS f /\
            (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})`;;

let POLYHEDRON_INTER = `!s t:real^N->bool.
        polyhedron s /\ polyhedron t ==> polyhedron (s INTER t)`;;

let POLYHEDRON_UNIV = `polyhedron(:real^N)`;;

let POLYHEDRON_POSITIVE_ORTHANT = `polyhedron {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}`;;

let POLYHEDRON_INTERS = `!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> polyhedron s) ==> polyhedron(INTERS f)`;;

let POLYHEDRON_EMPTY = `polyhedron({}:real^N->bool)`;;

let POLYHEDRON_HALFSPACE_LE = `!a b. polyhedron {x:real^N | a dot x <= b}`;;

let POLYHEDRON_HALFSPACE_GE = `!a b. polyhedron {x:real^N | a dot x >= b}`;;

let POLYHEDRON_HYPERPLANE = `!a b. polyhedron {x:real^N | a dot x = b}`;;

let AFFINE_IMP_POLYHEDRON = `!s:real^N->bool. affine s ==> polyhedron s`;;

let POLYHEDRON_IMP_CLOSED = `!s:real^N->bool. polyhedron s ==> closed s`;;

let POLYHEDRON_IMP_CONVEX = `!s:real^N->bool. polyhedron s ==> convex s`;;

let POLYHEDRON_AFFINE_HULL = `!s. polyhedron(affine hull s)`;;

(* ------------------------------------------------------------------------- *)
(* Canonical polyedron representation making facial structure explicit.      *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_INTER_AFFINE = `!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b})`;;

let POLYHEDRON_INTER_AFFINE_PARALLEL = `!s:real^N->bool.
        polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b} /\
                           (!x. x IN affine hull s
                                ==> (x + a) IN affine hull s))`;;

let POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL = `!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b} /\
                           (!x. x IN affine hull s
                                ==> (x + a) IN affine hull s)) /\
            !f'. f' PSUBSET f ==> s PSUBSET (affine hull s) INTER (INTERS f')`;;

let POLYHEDRON_INTER_AFFINE_MINIMAL = `!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b}) /\
            !f'. f' PSUBSET f ==> s PSUBSET (affine hull s) INTER (INTERS f')`;;

let RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT = `!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> relative_interior s =
                {x | x IN s /\ !h. h IN f ==> a h dot x < b h}`;;

let FACET_OF_POLYHEDRON_EXPLICIT = `!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c facet_of s <=>
                ?h. h IN f /\ c = s INTER {x | a h dot x = b h}`;;

let FACE_OF_POLYHEDRON_SUBSET_EXPLICIT = `!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c face_of s /\ ~(c = {}) /\ ~(c = s)
                ==> ?h. h IN f /\ c SUBSET (s INTER {x | a h dot x = b h})`;;

let FACE_OF_POLYHEDRON_EXPLICIT = `!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c face_of s /\ ~(c = {}) /\ ~(c = s)
                ==> c = INTERS {s INTER {x | a h dot x = b h} |h|
                                h IN f /\
                                c SUBSET (s INTER {x | a h dot x = b h})}`;;

(* ------------------------------------------------------------------------- *)
(* More general corollaries from the explicit representation.                *)
(* ------------------------------------------------------------------------- *)

let FACET_OF_POLYHEDRON = `!s:real^N->bool c.
        polyhedron s /\ c facet_of s
        ==> ?a b. ~(a = vec 0) /\
                  s SUBSET {x | a dot x <= b} /\
                  c = s INTER {x | a dot x = b}`;;

let FACE_OF_POLYHEDRON = `!s:real^N->bool c.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> c = INTERS {f | f facet_of s /\ c SUBSET f}`;;

let FACE_OF_POLYHEDRON_SUBSET_FACET = `!s:real^N->bool c.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> ?f. f facet_of s /\ c SUBSET f`;;

let FACE_OF_POLYHEDRON_FACE_OF_FACET = `!s c:real^N->bool.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> ?f. c face_of f /\ f facet_of s`;;

let EXPOSED_FACE_OF_POLYHEDRON = `!s f:real^N->bool. polyhedron s ==> (f exposed_face_of s <=> f face_of s)`;;

let FACE_OF_POLYHEDRON_POLYHEDRON = `!s:real^N->bool c. polyhedron s /\ c face_of s ==> polyhedron c`;;

let FINITE_POLYHEDRON_FACES = `!s:real^N->bool. polyhedron s ==> FINITE {f | f face_of s}`;;

let FINITE_POLYHEDRON_EXPOSED_FACES = `!s:real^N->bool. polyhedron s ==> FINITE {f | f exposed_face_of s}`;;

let FINITE_POLYHEDRON_EXTREME_POINTS = `!s:real^N->bool. polyhedron s ==> FINITE {v | v extreme_point_of s}`;;

let FINITE_POLYHEDRON_FACETS = `!s:real^N->bool. polyhedron s ==> FINITE {f | f facet_of s}`;;

let RELATIVE_INTERIOR_OF_POLYHEDRON = `!s:real^N->bool.
        polyhedron s
        ==> relative_interior s = s DIFF UNIONS {f | f facet_of s}`;;

let RELATIVE_BOUNDARY_OF_POLYHEDRON = `!s:real^N->bool.
        polyhedron s
        ==> s DIFF relative_interior s = UNIONS {f | f facet_of s}`;;

let RELATIVE_FRONTIER_OF_POLYHEDRON = `!s:real^N->bool.
        polyhedron s ==> relative_frontier s = UNIONS {f | f facet_of s}`;;

let RELATIVE_FRONTIER_OF_POLYHEDRON_ALT = `!s:real^N->bool.
        polyhedron s
        ==> relative_frontier s = UNIONS {f | f face_of s /\ ~(f = s)}`;;

let FACETS_OF_POLYHEDRON_EXPLICIT_DISTINCT = `!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !h1 h2. h1 IN f /\ h2 IN f /\
                    s INTER {x | a h1 dot x = b h1} =
                    s INTER {x | a h2 dot x = b h2}
                    ==> h1 = h2`;;

let POLYHEDRON_MINIMAL_LEMMA = `!f s:real^N->bool.
        FINITE f /\
        affine hull s INTER INTERS f = s
        ==> ?f'. FINITE f' /\ f' SUBSET f /\
                 affine hull s INTER INTERS f' = s /\
                 (!f''. f'' PSUBSET f'
                        ==> s PSUBSET affine hull s INTER INTERS f'')`;;

let POLYHEDRON = `!s. polyhedron s <=>
        ?f. FINITE f /\
            affine hull s INTER INTERS f = s /\
            (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f') /\
            (!h. h IN f
                 ==> (?a:real^N b. ~(a = vec 0) /\ h = {x | a dot x <= b}))`;;

(* ------------------------------------------------------------------------- *)
(* A characterization of polyhedra as having finitely many faces.            *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_EQ_FINITE_EXPOSED_FACES = `!s:real^N->bool.
    polyhedron s <=> closed s /\ convex s /\ FINITE {f | f exposed_face_of s}`;;

let POLYHEDRON_EQ_FINITE_FACES = `!s:real^N->bool.
        polyhedron s <=>
        closed s /\ convex s /\ FINITE {f | f face_of s}`;;

let POLYHEDRON_TRANSLATION_EQ = `!a s. polyhedron (IMAGE (\x:real^N. a + x) s) <=> polyhedron s`;;

add_translation_invariants [POLYHEDRON_TRANSLATION_EQ];;

let POLYHEDRON_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (polyhedron (IMAGE f s) <=> polyhedron s)`;;

add_linear_invariants [POLYHEDRON_LINEAR_IMAGE_EQ];;

let POLYHEDRON_NEGATIONS = `!s:real^N->bool. polyhedron s ==> polyhedron(IMAGE (--) s)`;;

let POLYHEDRON_LINEAR_PREIMAGE = `!f:real^M->real^N s.
        linear f /\ polyhedron s ==> polyhedron {x | f x IN s}`;;

(* ------------------------------------------------------------------------- *)
(* Relation between polytopes and polyhedra.                                 *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_EQ_BOUNDED_POLYHEDRON = `!s:real^N->bool. polytope s <=> polyhedron s /\ bounded s`;;

let POLYTOPE_INTER = `!s t. polytope s /\ polytope t ==> polytope(s INTER t)`;;

let POLYTOPE_INTER_POLYHEDRON = `!s t:real^N->bool. polytope s /\ polyhedron t ==> polytope(s INTER t)`;;

let POLYHEDRON_INTER_POLYTOPE = `!s t:real^N->bool. polyhedron s /\ polytope t ==> polytope(s INTER t)`;;

let POLYTOPE_IMP_POLYHEDRON = `!p. polytope p ==> polyhedron p`;;

let POLYTOPE_FACET_EXISTS = `!p:real^N->bool. polytope p /\ &0 < aff_dim p ==> ?f. f facet_of p`;;

let POLYHEDRON_INTERVAL = `!a b. polyhedron(interval[a,b])`;;

let POLYHEDRON_CONVEX_HULL = `!s. FINITE s ==> polyhedron(convex hull s)`;;

(* ------------------------------------------------------------------------- *)
(* Polytope is union of convex hulls of facets plus any point inside.        *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_UNION_CONVEX_HULL_FACETS = `!s p:real^N->bool.
        polytope p /\ &0 < aff_dim p /\ ~(s = {}) /\ s SUBSET p
        ==> p = UNIONS { convex hull (s UNION f) | f facet_of p}`;;

(* ------------------------------------------------------------------------- *)
(* Finitely generated cone is polyhedral, and hence closed.                  *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_CONVEX_CONE_HULL = `!s:real^N->bool. FINITE s ==> polyhedron(convex_cone hull s)`;;

let CLOSED_CONVEX_CONE_HULL = `!s:real^N->bool. FINITE s ==> closed(convex_cone hull s)`;;

let POLYHEDRON_CONVEX_CONE_HULL_POLYTOPE = `!s:real^N->bool. polytope s ==> polyhedron(convex_cone hull s)`;;

let POLYHEDRON_CONIC_HULL_POLYTOPE = `!s:real^N->bool. polytope s ==> polyhedron(conic hull s)`;;

let CLOSED_CONIC_HULL_STRONG = `!s:real^N->bool.
    vec 0 IN relative_interior s \/ polytope s \/ compact s /\ ~(vec 0 IN s)
    ==> closed(conic hull s)`;;

let CLOSED_CONVEX_CONE_HULL_STRONG = `!s:real^N->bool.
        FINITE s \/
        polytope s \/
        vec 0 IN relative_interior (convex hull s) \/
        compact s /\ ~(vec 0 IN convex hull s)
        ==> closed(convex_cone hull s)`;;

(* ------------------------------------------------------------------------- *)
(* And conversely, a polyhedral cone is finitely generated.                  *)
(* ------------------------------------------------------------------------- *)

let FINITELY_GENERATED_CONIC_POLYHEDRON = `!s:real^N->bool.
        polyhedron s /\ conic s /\ ~(s = {})
        ==> ?c. FINITE c /\ s = convex_cone hull c`;;

(* ------------------------------------------------------------------------- *)
(* Decomposition of polyhedron into cone plus polytope and more corollaries. *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_POLYTOPE_SUMS = `!s t:real^N->bool.
    polyhedron s /\ polytope t ==> polyhedron {x + y | x IN s /\ y IN t}`;;

let POLYHEDRON_AS_CONE_PLUS_CONV = `!s:real^N->bool.
        polyhedron s <=> ?t u. FINITE t /\ FINITE u /\
                               s = {x + y | x IN convex_cone hull t /\
                                            y IN convex hull u}`;;

let POLYHEDRON_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ polyhedron s ==> polyhedron(IMAGE f s)`;;

let POLYHEDRON_SUMS = `!s t:real^N->bool.
    polyhedron s /\ polyhedron t ==> polyhedron {x + y | x IN s /\ y IN t}`;;

let POLYHEDRAL_CONVEX_CONE = `!s:real^N->bool.
        polyhedron s /\ convex_cone s <=>
        ?k. FINITE k /\ s = convex_cone hull k`;;

(* ------------------------------------------------------------------------- *)
(* Farkas's lemma (2 variants) and stronger separation for polyhedra.        *)
(* ------------------------------------------------------------------------- *)

let FARKAS_LEMMA = `!A:real^N^M b.
        (?x:real^N.
            A ** x = b /\
            (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i)) <=>
        ~(?y:real^M.
            b dot y < &0 /\
            (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= (transp A ** y)$i))`;;

let FARKAS_LEMMA_ALT = `!A:real^N^M b.
        (?x:real^N.
            (!i. 1 <= i /\ i <= dimindex(:M) ==> (A ** x)$i <= b$i)) <=>
        ~(?y:real^M.
            (!i. 1 <= i /\ i <= dimindex(:M) ==> &0 <= y$i) /\
            y ** A = vec 0 /\ b dot y < &0)`;;

let SEPARATING_HYPERPLANE_POLYHEDRA = `!s t:real^N->bool.
        polyhedron s /\ polyhedron t /\ ~(s = {}) /\ ~(t = {}) /\ DISJOINT s t
        ==> ?a b. ~(a = vec 0) /\
                  (!x. x IN s ==> a dot x < b) /\
                  (!x. x IN t ==> a dot x > b)`;;

(* ------------------------------------------------------------------------- *)
(* Relative and absolute frontier of a polytope.                             *)
(* ------------------------------------------------------------------------- *)

let RELATIVE_BOUNDARY_OF_CONVEX_HULL = `!s:real^N->bool.
        ~affine_dependent s
        ==> (convex hull s) DIFF relative_interior(convex hull s) =
            UNIONS { convex hull (s DELETE a) | a | a IN s}`;;

let FRONTIER_OF_CONVEX_HULL = `!s:real^N->bool.
        s HAS_SIZE (dimindex(:N) + 1)
        ==> frontier(convex hull s) =
               UNIONS { convex hull (s DELETE a) | a | a IN s}`;;

(* ------------------------------------------------------------------------- *)
(* Special case of a triangle.                                               *)
(* ------------------------------------------------------------------------- *)

let RELATIVE_BOUNDARY_OF_TRIANGLE = `!a b c:real^N.
        ~collinear {a,b,c}
        ==> convex hull {a,b,c} DIFF relative_interior(convex hull {a,b,c}) =
            segment[a,b] UNION segment[b,c] UNION segment[c,a]`;;

let RELATIVE_FRONTIER_OF_TRIANGLE = `!a b c:real^N.
        ~collinear {a,b,c}
        ==> relative_frontier(convex hull {a,b,c}) =
            segment[a,b] UNION segment[b,c] UNION segment[c,a]`;;

let FRONTIER_OF_TRIANGLE = `!a b c:real^2.
        frontier(convex hull {a,b,c}) =
            segment[a,b] UNION segment[b,c] UNION segment[c,a]`;;

let INSIDE_OF_TRIANGLE = `!a b c:real^2.
        inside(segment[a,b] UNION segment[b,c] UNION segment[c,a]) =
                interior(convex hull {a,b,c})`;;

let INTERIOR_OF_TRIANGLE = `!a b c:real^2.
        interior(convex hull {a,b,c}) =
        (convex hull {a,b,c}) DIFF
        (segment[a,b] UNION segment[b,c] UNION segment[c,a])`;;

(* ------------------------------------------------------------------------- *)
(* A ridge is the intersection of precisely two facets.                      *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_RIDGE_TWO_FACETS = `!p:real^N->bool r.
    polyhedron p /\ r face_of p /\ ~(r = {}) /\ aff_dim r = aff_dim p - &2
    ==> ?f1 f2. f1 face_of p /\ aff_dim f1 = aff_dim p - &1 /\
                f2 face_of p /\ aff_dim f2 = aff_dim p - &1 /\
                 ~(f1 = f2) /\ r SUBSET f1 /\ r SUBSET f2 /\ f1 INTER f2 = r /\
                !f. f face_of p /\ aff_dim f = aff_dim p - &1 /\ r SUBSET f
                    ==> f = f1 \/ f = f2`;;

(* ------------------------------------------------------------------------- *)
(* Lower bounds on then number of 0 and n-1 dimensional faces.               *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_VERTEX_LOWER_BOUND = `!p:real^N->bool.
        polytope p ==> aff_dim p + &1 <= &(CARD {v | v extreme_point_of p})`;;

let POLYTOPE_FACET_LOWER_BOUND = `!p:real^N->bool.
        polytope p /\ ~(aff_dim p = &0)
        ==> aff_dim p + &1 <= &(CARD {f | f facet_of p})`;;

(* ------------------------------------------------------------------------- *)
(* The notion of n-simplex where n is an integer >= -1.                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("simplex",(12,"right"));;

let simplex = new_definition
 `n simplex s <=> ?c. ~(affine_dependent c) /\
                      &(CARD c):int = n + &1 /\
                      s = convex hull c`;;

let SIMPLEX_TRANSLATION_EQ = `!a:real^N s n. n simplex (IMAGE (\x. a + x) s) <=> n simplex s`;;

add_translation_invariants [SIMPLEX_TRANSLATION_EQ];;

let SIMPLEX_LINEAR_IMAGE_EQ = `!f:real^M->real^N s n.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (n simplex (IMAGE f s) <=> n simplex s)`;;

add_linear_invariants [SIMPLEX_LINEAR_IMAGE_EQ];;

let SIMPLEX = `n simplex s <=> ?c. FINITE c /\
                       ~(affine_dependent c) /\
                       &(CARD c):int = n + &1 /\
                       s = convex hull c`;;

let SIMPLEX_CONVEX_HULL = `!c:real^N->bool n.
    ~affine_dependent c /\ &(CARD c) = n + &1 ==> n simplex (convex hull c)`;;

let SIMPLEX_IMP_POLYTOPE = `!n s. n simplex s ==> polytope s`;;

let SIMPLEX_IMP_POLYHEDRON = `!s n. n simplex s ==> polyhedron s`;;

let SIMPLEX_IMP_CONVEX = `!s:real^N->bool n. n simplex s ==> convex s`;;

let SIMPLEX_IMP_COMPACT = `!s:real^N->bool n. n simplex s ==> compact s`;;

let SIMPLEX_IMP_CLOSED = `!s:real^N->bool n. n simplex s ==> closed s`;;

let SIMPLEX_DIM_GE = `!n s. n simplex s ==> -- &1 <= n`;;

let SIMPLEX_EMPTY = `!n. n simplex {} <=> n = -- &1`;;

let SIMPLEX_MINUS_1 = `!s. (-- &1) simplex s <=> s = {}`;;

let AFF_DIM_SIMPLEX = `!s n. n simplex s ==> aff_dim s = n`;;

let SIMPLEX_EXTREME_POINTS = `!n s:real^N->bool.
       n simplex s
       ==> FINITE {v | v extreme_point_of s} /\
           ~(affine_dependent {v | v extreme_point_of s}) /\
           &(CARD {v | v extreme_point_of s}) = n + &1 /\
           s = convex hull {v | v extreme_point_of s}`;;

let SIMPLEX_FACE_OF_SIMPLEX = `!n s f:real^N->bool.
        n simplex s /\ f face_of s ==> ?m. m <= n /\ m simplex f`;;

let FACE_OF_SIMPLEX_SUBSET = `!n s f:real^N->bool.
        n simplex s /\ f face_of s
        ==> ?c. c SUBSET {x | x extreme_point_of s} /\ f = convex hull c`;;

let SUBSET_FACE_OF_SIMPLEX = `!s n c:real^N->bool.
      n simplex s /\ c SUBSET {x | x extreme_point_of s}
      ==> (convex hull c) face_of s`;;

let FACES_OF_SIMPLEX = `!n s. n simplex s
         ==> {f | f face_of s} =
             {convex hull c | c SUBSET {v | v extreme_point_of s}}`;;

let HAS_SIZE_FACES_OF_SIMPLEX = `!n s:real^N->bool.
        n simplex s
        ==> {f | f face_of s} HAS_SIZE 2 EXP (num_of_int(n + &1))`;;

let FINITE_FACES_OF_SIMPLEX = `!n s. n simplex s ==> FINITE {f | f face_of s}`;;

let CARD_FACES_OF_SIMPLEX = `!n s. n simplex s ==> CARD {f | f face_of s} = 2 EXP (num_of_int(n + &1))`;;

let CHOOSE_SIMPLEX = `!n. --(&1) <= n /\ n <= &(dimindex(:N)) ==> ?s:real^N->bool. n simplex s`;;

let CHOOSE_SURROUNDING_SIMPLEX = `!a:real^N n.
        &0 <= n /\ n <= &(dimindex (:N))
        ==>  ?s. n simplex s /\ a IN relative_interior s`;;

let CHOOSE_SURROUNDING_SIMPLEX_FULL = `!a:real^N. ?s. &(dimindex(:N)) simplex s /\ a IN interior s`;;

let CHOOSE_POLYTOPE = `!n. --(&1) <= n /\ n <= &(dimindex(:N))
       ==> ?s:real^N->bool. polytope s /\ aff_dim s = n`;;

let SIMPLEX_SING = `!n a:real^N. n simplex {a} <=> n = &0`;;

let SIMPLEX_ZERO = `!s:real^N->bool. &0 simplex s <=> ?a. s = {a}`;;

let SIMPLEX_SEGMENT_CASES = `!a b:real^N. (if a = b then &0 else &1) simplex segment[a,b]`;;

let SIMPLEX_SEGMENT = `!a b. ?n. n simplex segment[a,b]`;;

let POLYTOPE_LOWDIM_IMP_SIMPLEX = `!p:real^N->bool. polytope p /\ aff_dim p <= &1 ==> ?n. n simplex p`;;

let SIMPLEX_INSERT_DIMPLUS1 = `!n s a:real^N.
        n simplex s /\ ~(a IN affine hull s)
        ==> (n + &1) simplex (convex hull (a INSERT s))`;;

let SIMPLEX_INSERT = `!s a:real^N.
        (?n. n simplex s) /\ ~(a IN affine hull s)
        ==> ?n. n simplex (convex hull (a INSERT s))`;;

let SIMPLEX_ALT = `!s:real^N->bool i.
        i simplex s <=>
          convex s /\ compact s /\
          FINITE {v | v extreme_point_of s} /\
          &(CARD {v | v extreme_point_of s}) = i + &1 /\
          ~affine_dependent {v | v extreme_point_of s}`;;

let SIMPLEX_ALT1 = `!s:real^N->bool.
        (&n - &1) simplex s <=>
          convex s /\ compact s /\
          {v | v extreme_point_of s} HAS_SIZE n /\
          ~affine_dependent {v | v extreme_point_of s}`;;

let SIMPLEX_0_NOT_IN_AFFINE_HULL = `!s:real^N->bool.
        (&n - &1) simplex s /\ ~(vec 0 IN affine hull s) <=>
        convex s /\ compact s /\
        {v | v extreme_point_of s} HAS_SIZE n /\
        independent {v | v extreme_point_of s}`;;

let SIMPLEX_EXTREME_POINTS_NONEMPTY = `!c. &(dimindex (:N)) - &1 simplex c ==> ~({v | v extreme_point_of c} = {})`;;

(* ------------------------------------------------------------------------- *)
(* Simplicial complexes and triangulations.                                  *)
(* ------------------------------------------------------------------------- *)

let simplicial_complex = new_definition
 `simplicial_complex c <=>
        FINITE c /\
        (!s. s IN c ==> ?n. n simplex s) /\
        (!f s. s IN c /\ f face_of s ==> f IN c) /\
        (!s s'. s IN c /\ s' IN c
                ==> (s INTER s') face_of s /\ (s INTER s') face_of s')`;;

let triangulation = new_definition
 `triangulation(tr:(real^N->bool)->bool) <=>
        FINITE tr /\
        (!t. t IN tr ==> ?n. n simplex t) /\
        (!t t'. t IN tr /\ t' IN tr
                ==> (t INTER t') face_of t /\ (t INTER t') face_of t')`;;

let SIMPLICIAL_COMPLEX_TRANSLATION = `!a:real^N tr.
   simplicial_complex(IMAGE (IMAGE (\x. a + x)) tr) <=> simplicial_complex tr`;;

add_translation_invariants [SIMPLICIAL_COMPLEX_TRANSLATION];;

let SIMPLICIAL_COMPLEX_LINEAR_IMAGE = `!f:real^M->real^N tr.
       linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
       ==> (simplicial_complex(IMAGE (IMAGE f) tr) <=> simplicial_complex tr)`;;

add_linear_invariants [SIMPLICIAL_COMPLEX_LINEAR_IMAGE];;

let TRIANGULATION_TRANSLATION = `!a:real^N tr.
        triangulation(IMAGE (IMAGE (\x. a + x)) tr) <=> triangulation tr`;;

add_translation_invariants [TRIANGULATION_TRANSLATION];;

let TRIANGULATION_LINEAR_IMAGE = `!f:real^M->real^N tr.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (triangulation(IMAGE (IMAGE f) tr) <=> triangulation tr)`;;

add_linear_invariants [TRIANGULATION_LINEAR_IMAGE];;

let SIMPLICIAL_COMPLEX_IMP_TRIANGULATION = `!tr. simplicial_complex tr ==> triangulation tr`;;

let TRIANGULATION_SUBSET = `!tr:(real^N->bool)->bool tr'.
        triangulation tr /\ tr' SUBSET tr ==> triangulation tr'`;;

let TRIANGULATION_UNION = `!tr1 tr2.
        triangulation(tr1 UNION tr2) <=>
        triangulation tr1 /\ triangulation tr2 /\
        (!s t. s IN tr1 /\ t IN tr2
               ==> s INTER t face_of s /\ s INTER t face_of t)`;;

let TRIANGULATION_INTER_SIMPLEX = `!tr t t':real^N->bool.
        triangulation tr /\ t IN tr /\ t' IN tr
        ==> t INTER t' = convex hull ({x | x extreme_point_of t} INTER
                                      {x | x extreme_point_of t'})`;;

let TRIANGULATION_SIMPLICIAL_COMPLEX = `!tr. triangulation tr
        ==> simplicial_complex {f:real^N->bool | ?t. t IN tr /\ f face_of t}`;;

let TRIANGULATION_SIMPLEX_FACES = `!s:real^N->bool n d.
        n simplex s ==> triangulation {c | c face_of s /\ aff_dim c = d}`;;

let TRIANGULATION_SIMPLEX_FACETS = `!s:real^N->bool n. n simplex s ==> triangulation {c | c facet_of s}`;;

let CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS = `!c d:real^N->bool.
        c INTER d face_of c /\ c INTER d face_of d /\ ~(c = d)
        ==> relative_interior c INTER relative_interior d = {}`;;

let TRIANGULATION_DISJOINT_RELATIVE_INTERIORS = `!t c d:real^N->bool.
        triangulation t /\ c IN t /\ d IN t /\ ~(c = d)
        ==> relative_interior c INTER relative_interior d = {}`;;

let SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS = `!t c d:real^N->bool.
        simplicial_complex t /\ c IN t /\ d IN t /\ ~(c = d)
        ==> relative_interior c INTER relative_interior d = {}`;;

let NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION = `!t u z. convex u /\ bounded u /\ z IN interior u /\
           triangulation t /\ UNIONS t SUBSET frontier u
           ==> !c:real^N->bool. c IN t ==> ~(z IN affine hull c)`;;

let TRIANGULATION_SUBFACES = `!tr:(real^N->bool)->bool tr'.
        triangulation tr /\ (!c'. c' IN tr' ==> ?c. c IN tr /\ c' face_of c)
        ==> triangulation tr'`;;

(* ------------------------------------------------------------------------- *)
(* Subdividing a cell complex (not necessarily simplicial).                  *)
(* ------------------------------------------------------------------------- *)

let CELL_COMPLEX_SUBDIVISION_EXISTS = `!m:(real^N->bool)->bool d e.
     &0 < e /\
     FINITE m /\
     (!c. c IN m ==> polytope c) /\
     (!c. c IN m ==> aff_dim c <= d) /\
     (!c1 c2. c1 IN m /\ c2 IN m
              ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
     ==> ?m'. (!c. c IN m' ==> diameter c < e) /\
              UNIONS m' = UNIONS m /\
              FINITE m' /\
              (!c. c IN m' ==> ?d. d IN m /\ c SUBSET d) /\
              (!c x. c IN m /\ x IN c
                     ==> ?d. d IN m' /\ x IN d /\ d SUBSET c) /\
              (!c. c IN m' ==> polytope c) /\
              (!c. c IN m' ==> aff_dim c <= d) /\
              (!c1 c2. c1 IN m' /\ c2 IN m'
                       ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)`;;

(* ------------------------------------------------------------------------- *)
(* Refining a cell complex to a simplicial complex.                          *)
(* ------------------------------------------------------------------------- *)

let SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX_LOWDIM = `!m:(real^N->bool)->bool d.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c <= d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. simplicial_complex t /\
                (!k. k IN t ==> aff_dim k <= d) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)`;;

let SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX = `!m:(real^N->bool)->bool.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. simplicial_complex t /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)`;;

let FINE_SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX = `!m:(real^N->bool)->bool e.
        &0 < e /\ FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. simplicial_complex t /\
                (!k. k IN t ==> diameter k < e) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)`;;

(* ------------------------------------------------------------------------- *)
(* Some results on cell division with full-dimensional cells only.           *)
(* ------------------------------------------------------------------------- *)

let REGULAR_CLOSED_UNIONS_FAT_CELLS_UNIV = `!s u:real^N->bool.
        closure(interior u) = u /\
        FINITE s /\ (!c. c IN s ==> closed c /\ convex c) /\ UNIONS s = u
        ==> UNIONS {c | c IN s /\ ~(interior c = {})} = u`;;

let CONVEX_UNIONS_FULLDIM_CELLS = `!s u:real^N->bool.
        FINITE s /\ (!c. c IN s ==> closed c /\ convex c) /\
        UNIONS s = u /\ convex u
        ==> UNIONS {c | c IN s /\ aff_dim c = aff_dim u} = u`;;

let TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX = `!m:(real^N->bool)->bool d.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c = d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. triangulation t /\
                (!k. k IN t ==> aff_dim k = d) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)`;;

let FINE_TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX = `!m:(real^N->bool)->bool d e.
        &0 < e /\ FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c = d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. triangulation t /\
                (!k. k IN t ==> diameter k < e) /\
                (!k. k IN t ==> aff_dim k = d) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)`;;
