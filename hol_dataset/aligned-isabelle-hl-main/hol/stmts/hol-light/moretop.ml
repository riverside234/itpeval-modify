(* ========================================================================= *)
(* Additional topology theory.                                               *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2013                       *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Injective map into R is also an open map w.r.t. the universe, and this    *)
(* is actually an implication in both directions for an interval. Compare    *)
(* the local form in INJECTIVE_INTO_1D_IMP_OPEN_MAP (not a bi-implication).  *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_EQ_1D_OPEN_MAP_UNIV = `!f:real^1->real^1 s.
        f continuous_on s /\ is_interval s
        ==>  ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!t. open t /\ t SUBSET s ==> open(IMAGE f t)))`;;

(* ------------------------------------------------------------------------- *)
(* Nonsurjectivity of differentiable map from lower-dimensional sphere.      *)
(* ------------------------------------------------------------------------- *)

let NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM = `!f:real^N->real^N s t.
      subspace s /\ subspace t /\ dim s < dim t /\ s SUBSET t /\
      f differentiable_on sphere(vec 0,&1) INTER s
      ==> ~(IMAGE f (sphere(vec 0,&1) INTER s) = sphere(vec 0,&1) INTER t)`;;

(* ------------------------------------------------------------------------- *)
(* Map f:S^m->S^n for m < n is nullhomotopic.                                *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_SPHEREMAP_LOWDIM_GEN = `!f:real^M->real^N s t.
     convex s /\ bounded s /\ convex t /\ bounded t /\ aff_dim s < aff_dim t /\
     f continuous_on relative_frontier s /\
     IMAGE f (relative_frontier s) SUBSET (relative_frontier t)
     ==> ?c. homotopic_with (\z. T)
                (subtopology euclidean (relative_frontier s),
                 subtopology euclidean (relative_frontier t)) f (\x. c)`;;

let INESSENTIAL_SPHEREMAP_LOWDIM = `!f:real^M->real^N a r b s.
        dimindex(:M) < dimindex(:N) /\
        f continuous_on sphere(a,r) /\
        IMAGE f (sphere(a,r)) SUBSET (sphere(b,s))
        ==> ?c. homotopic_with (\z. T)
                 (subtopology euclidean (sphere(a,r)),
                  subtopology euclidean (sphere(b,s))) f (\x. c)`;;

let HOMEOMORPHIC_SPHERES_EQ = `(!a:real^M b:real^N r s.
        sphere(a,r) homeomorphic sphere(b,s) <=>
        r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N))`
and HOMOTOPY_EQUIVALENT_SPHERES_EQ = `(!a:real^M b:real^N r s.
        sphere(a,r) homotopy_equivalent sphere(b,s) <=>
        r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N))`;;

let SIMPLY_CONNECTED_SPHERE_GEN = `!s. convex s /\ bounded s /\ &3 <= aff_dim s
       ==> simply_connected(relative_frontier s)`;;

let SIMPLY_CONNECTED_SPHERE = `!a:real^N r. 3 <= dimindex(:N) ==> simply_connected(sphere(a,r))`;;

let SIMPLY_CONNECTED_PUNCTURED_CONVEX = `!s a:real^N.
        convex s /\ &3 <= aff_dim s ==> simply_connected(s DELETE a)`;;

let SIMPLY_CONNECTED_PUNCTURED_UNIVERSE = `!a. 3 <= dimindex(:N) ==> simply_connected((:real^N) DELETE a)`;;

let SIMPLY_CONNECTED_CONVEX_DIFF_FINITE = `!s t:real^N->bool.
        convex s /\ &3 <= aff_dim s /\ FINITE t
        ==> simply_connected(s DIFF t)`;;

(* ------------------------------------------------------------------------- *)
(* Borsuk's odd mapping degree theorem.                                      *)
(* ------------------------------------------------------------------------- *)

let ODD_MAP_HOMOTOPY_LEMMA = `!f:real^N->real^N s t.
        subspace s /\ subspace t /\ dim s + 1 = dim t /\ s SUBSET t /\
        f continuous_on (sphere(vec 0,&1) INTER t) /\
        IMAGE f (sphere(vec 0,&1) INTER t) SUBSET (sphere(vec 0,&1) INTER t) /\
        (!x. x IN (sphere(vec 0,&1) INTER t) ==> f(--x) = --(f x))
        ==> ?g. g continuous_on (sphere(vec 0,&1) INTER t) /\
                IMAGE g (sphere(vec 0,&1) INTER t) SUBSET
                sphere(vec 0,&1) INTER t /\
                IMAGE g (sphere(vec 0,&1) INTER s) SUBSET
                sphere(vec 0,&1) INTER s /\
                (!x. x IN (sphere(vec 0,&1) INTER t) ==> g(--x) = --(g x)) /\
                homotopic_with (\z. T)
                 (subtopology euclidean (sphere(vec 0,&1) INTER t),
                  subtopology euclidean (sphere(vec 0,&1) INTER t))
                 f g`;;

let BORSUK_ODD_MAPPING_GEN = `!n (f:real^N->real^N).
        f continuous_on (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) /\
        IMAGE f (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) SUBSET
        sphere(vec 0,&1) INTER span(IMAGE basis (1..n)) /\
        (!x. x IN sphere(vec 0,&1) INTER span(IMAGE basis (1..n))
             ==> f(--x) = --(f x))
        ==> (brouwer_degree1 n f == &1) (mod &2)`;;

let BORSUK_ODD_MAPPING = `!f:real^N->real^N.
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> (brouwer_degree f == &1) (mod &2)`;;

(* ------------------------------------------------------------------------- *)
(* Various forms and corollaries of the Borsuk-Ulam theorem.                 *)
(* ------------------------------------------------------------------------- *)

let BORSUK_ULAM_NOT_NULLHOMOTOPIC_GEN = `!(f:real^N->real^N) s a.
        subspace s /\ 1 <= dim s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER s /\
        (!x. x IN sphere(vec 0,&1) INTER s ==> f(--x) = --(f x))
        ==> ~(homotopic_with (\x. T)
               (subtopology euclidean (sphere(vec 0,&1) INTER s),
                subtopology euclidean (sphere(vec 0,&1) INTER s))
               f (\x. a))`;;

let BORSUK_ULAM_NOT_NULLHOMOTOPIC = `!(f:real^N->real^N) a.
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> ~(homotopic_with (\x. T)
                (subtopology euclidean (sphere(vec 0,&1)),
                 subtopology euclidean (sphere(vec 0,&1)))
                f (\x. a))`;;

let BORSUK_ULAM_SURJECTIVE_GEN = `!(f:real^N->real^N) s.
        subspace s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER s /\
        (!x. x IN sphere(vec 0,&1) INTER s ==> f(--x) = --(f x))
        ==> IMAGE f (sphere(vec 0,&1) INTER s) = sphere(vec 0,&1) INTER s`;;

let BORSUK_ULAM_SURJECTIVE = `!(f:real^N->real^N).
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> IMAGE f (sphere(vec 0,&1)) = sphere(vec 0,&1)`;;

let BORSUK_ULAM_ZERO_GEN = `!(f:real^M->real^N) s t.
        subspace s /\ dim t + 1 <= dim s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET t /\
        (!x. x IN (sphere(vec 0,&1) INTER s) ==> f(--x) = --(f x))
        ==> ?x. x IN (sphere(vec 0,&1) INTER s) /\ f x = vec 0`;;

let BORSUK_ULAM_ZERO = `!(f:real^M->real^N) s.
        dim s < dimindex(:M) /\
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET s /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> ?x. x IN sphere(vec 0,&1) /\ f x = vec 0`;;

let BORSUK_ULAM_ANTIPODAL_SUBSPACE = `!(f:real^M->real^N) s t.
        subspace s /\ dim t + 1 <= dim s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET t
        ==> ?x. x IN (sphere(vec 0,&1) INTER s) /\ f(--x) = f(x)`;;

let BORSUK_ULAM_ANTIPODAL_GEN = `!(f:real^M->real^N) s t.
        subspace s /\ max (&1) (aff_dim t + &1) <= &(dim s) /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET t
        ==> ?x. x IN (sphere(vec 0,&1) INTER s) /\ f(--x) = f(x)`;;

let BORSUK_ULAM_ANTIPODAL = `!(f:real^M->real^N) s.
        aff_dim s < &(dimindex(:M)) /\
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET s
        ==> ?x. x IN sphere(vec 0,&1) /\ f(--x) = f(x)`;;

let BORSUK_ULAM_FRONTIER_MAP_GEN = `!f s:real^N->bool.
      ~(subspace s /\ 1 <= dim s /\
        f continuous_on (cball(vec 0,&1) INTER s) /\
        IMAGE f (cball(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER s /\
        !x. x IN (sphere(vec 0,&1) INTER s) ==> f(--x) = --(f x))`;;

let BORSUK_ULAM_FRONTIER_MAP = `!f:real^N->real^N.
      ~(f continuous_on cball(vec 0,&1) /\
        IMAGE f (cball(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        !x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))`;;

let LUSTERNIK_SCHNIRELMANN = `!u:(real^N->bool)->bool.
        FINITE u /\ CARD(u) <= dimindex(:N) /\ (!c. c IN u ==> closed c) /\
        sphere(vec 0,&1) SUBSET UNIONS u
        ==> ?c x. c IN u /\ x IN sphere(vec 0,&1) /\ x IN c /\ --x IN c`;;

let HAM_SANDWICH_THEOREM = `!u:(real^N->bool)->bool.
      FINITE u /\ CARD(u) <= dimindex(:N) /\ (!s. s IN u ==> measurable s)
      ==> ?a b. !s. s IN u
                    ==> measure {x | x IN s /\ a dot x <= b} = measure s / &2`;;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas about extending maps from cell complexes.           *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAP_CELL_COMPLEX_TO_SPHERE = `(!f:real^M->real^N m s t.
        FINITE m /\ (!c. c IN m ==> polytope c /\ aff_dim c < aff_dim t) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2) /\
        s SUBSET UNIONS m /\ closed s /\ convex t /\ bounded t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier t
        ==> ?g. g continuous_on UNIONS m /\
                IMAGE g (UNIONS m) SUBSET relative_frontier t /\
                !x. x IN s ==> g x = f x)`
and EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE = `(!f:real^M->real^N m s t.
        FINITE m /\ (!c. c IN m ==> polytope c /\ aff_dim c <= aff_dim t) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2) /\
        s SUBSET UNIONS m /\ closed s /\ convex t /\ bounded t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier t
        ==> ?k g. FINITE k /\ DISJOINT k s /\
                  g continuous_on (UNIONS m DIFF k) /\
                  IMAGE g (UNIONS m DIFF k) SUBSET relative_frontier t /\
                  !x. x IN s ==> g x = f x)`;;

(* ------------------------------------------------------------------------- *)
(* Special cases and corollaries involving spheres.                          *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE = `!f:real^M->real^N s t u.
        compact s /\ convex u /\ bounded u /\ aff_dim t <= aff_dim u /\
        s SUBSET t /\ f continuous_on s /\ IMAGE f s SUBSET relative_frontier u
        ==> ?k g. FINITE k /\ k SUBSET t /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                  !x. x IN s ==> g x = f x`;;

let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN = `!f:real^M->real^N s t u p.
        compact s /\ convex u /\ bounded u /\
        affine t /\ aff_dim t <= aff_dim u /\ s SUBSET t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
        (!c. c IN components(t DIFF s) /\ bounded c ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                  !x. x IN s ==> g x = f x`;;

let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE = `!f:real^M->real^N s t a r p.
        compact s /\ affine t /\ aff_dim t <= &(dimindex(:N)) /\ s SUBSET t /\
        &0 <= r /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
        (!c. c IN components(t DIFF s) /\ bounded c ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET sphere(a,r) /\
                  !x. x IN s ==> g x = f x`;;

let EXTEND_MAP_UNIV_TO_SPHERE_COFINITE = `!f:real^M->real^N s a r p.
     dimindex(:M) <= dimindex(:N) /\ &0 <= r /\
     compact s /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
     (!c. c IN components((:real^M) DIFF s) /\ bounded c
          ==> ~(c INTER p = {}))
     ==> ?k g. FINITE k /\ k SUBSET p /\ DISJOINT k s /\
               g continuous_on ((:real^M) DIFF k) /\
               IMAGE g ((:real^M) DIFF k) SUBSET sphere(a,r) /\
               !x. x IN s ==> g x = f x`;;

let EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT = `!f:real^M->real^N s a r.
     dimindex(:M) <= dimindex(:N) /\ &0 <= r /\
     compact s /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
     (!c. c IN components((:real^M) DIFF s) ==> ~bounded c)
     ==> ?g. g continuous_on (:real^M) /\
             IMAGE g (:real^M) SUBSET sphere(a,r) /\
             !x. x IN s ==> g x = f x`;;

let EXTEND_MAP_SPHERE_TO_SPHERE_GEN = `!f:real^M->real^N c s t.
        closed c /\ c SUBSET relative_frontier s /\ convex s /\ bounded s /\
        convex t /\ bounded t /\ aff_dim s <= aff_dim t /\
        f continuous_on c /\ IMAGE f c SUBSET relative_frontier t
         ==> ?g. g continuous_on (relative_frontier s) /\
                 IMAGE g (relative_frontier s) SUBSET relative_frontier t /\
                 !x. x IN c ==> g x = f x`;;

let EXTEND_MAP_SPHERE_TO_SPHERE = `!f:real^M->real^N c a r b s.
        dimindex(:M) <= dimindex(:N) /\ closed c /\ c SUBSET sphere(a,r) /\
        f continuous_on c /\ IMAGE f c SUBSET sphere(b,s) /\
        (&0 <= r /\ c = {} ==> &0 <= s)
        ==> ?g. g continuous_on sphere(a,r) /\
                IMAGE g (sphere(a,r)) SUBSET sphere(b,s) /\
                !x. x IN c ==> g x = f x`;;

let EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN = `!f:real^M->real^N s t u p.
        convex t /\ bounded t /\ convex u /\ bounded u /\
        aff_dim t <= aff_dim u + &1 /\
        closed s /\ s SUBSET relative_frontier t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
        (!c. c IN components(relative_frontier t DIFF s) ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\
                  k SUBSET relative_frontier t /\ DISJOINT k s /\
                  g continuous_on (relative_frontier t DIFF k) /\
                  IMAGE g (relative_frontier t DIFF k) SUBSET
                  relative_frontier u /\
                  !x. x IN s ==> g x = f x`;;

let EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE = `!f:real^M->real^N s a d b e p.
        dimindex(:M) <= dimindex(:N) + 1 /\
        (&0 < d /\ s = {} ==> &0 <= e) /\
        closed s /\ s SUBSET sphere(a,d) /\
        f continuous_on s /\ IMAGE f s SUBSET sphere(b,e) /\
        (!c. c IN components(sphere(a,d) DIFF s) ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\
                  k SUBSET sphere(a,d) /\ DISJOINT k s /\
                  g continuous_on (sphere(a,d) DIFF k) /\
                  IMAGE g (sphere(a,d) DIFF k) SUBSET sphere(b,e) /\
                  !x. x IN s ==> g x = f x`;;

(* ------------------------------------------------------------------------- *)
(* Borsuk-style characterization of separation.                              *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_BORSUK_MAP = `!s a:real^N.
        ~(a IN s) ==> (\x. inv(norm (x - a)) % (x - a)) continuous_on s`;;

let BORSUK_MAP_INTO_SPHERE = `!s a:real^N.
        IMAGE (\x. inv(norm (x - a)) % (x - a)) s SUBSET sphere(vec 0,&1) <=>
        ~(a IN s)`;;

let BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT = `!s a b. path_component ((:real^N) DIFF s) a b
           ==> homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean (sphere(vec 0,&1)))
                   (\x. inv(norm(x - a)) % (x - a))
                   (\x. inv(norm(x - b)) % (x - b))`;;

let NON_EXTENSIBLE_BORSUK_MAP = `!s c a:real^N.
        compact s /\ c IN components((:real^N) DIFF s) /\ bounded c /\ a IN c
        ==> ~(?g. g continuous_on (s UNION c) /\
                  IMAGE g (s UNION c) SUBSET sphere (vec 0,&1) /\
                  (!x. x IN s ==> g x = inv(norm(x - a)) % (x - a)))`;;

let BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT = `!s a. compact s /\ ~(a IN s)
         ==> (bounded(connected_component ((:real^N) DIFF s) a) <=>
              ~(?c. homotopic_with (\x. T)
                      (subtopology euclidean s,
                       subtopology euclidean (sphere(vec 0:real^N,&1)))
                      (\x. inv(norm(x - a)) % (x - a)) (\x. c)))`;;

let HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT = `!s a b.
        compact s /\ ~(a IN s) /\ ~(b IN s) /\
        bounded (connected_component ((:real^N) DIFF s) a) /\
        homotopic_with (\x. T)
          (subtopology euclidean s,
           subtopology euclidean (sphere(vec 0,&1)))
          (\x. inv(norm(x - a)) % (x - a))
          (\x. inv(norm(x - b)) % (x - b))
        ==> connected_component ((:real^N) DIFF s) a b`;;

let BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ = `!s a b. 2 <= dimindex(:N) /\ compact s /\ ~(a IN s) /\ ~(b IN s)
           ==> (homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean (sphere(vec 0,&1)))
                   (\x. inv(norm(x - a)) % (x - a))
                   (\x. inv(norm(x - b)) % (x - b)) <=>
                connected_component ((:real^N) DIFF s) a b)`;;

let BORSUK_SEPARATION_THEOREM_GEN = `!s:real^N->bool.
    compact s
    ==> ((!c. c IN components((:real^N) DIFF s) ==> ~bounded c) <=>
         (!f. f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0:real^N,&1)
              ==> ?c. homotopic_with (\x. T)
                       (subtopology euclidean s,
                        subtopology euclidean (sphere(vec 0,&1))) f (\x. c)))`;;

let BORSUK_SEPARATION_THEOREM = `!s:real^N->bool.
      2 <= dimindex(:N) /\ compact s
      ==> (connected((:real^N) DIFF s) <=>
           !f. f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0:real^N,&1)
               ==> ?c. homotopic_with (\x. T)
                        (subtopology euclidean s,
                         subtopology euclidean (sphere(vec 0,&1))) f (\x. c))`;;

let HOMOTOPY_EQUIVALENT_SEPARATION = `!s t. compact s /\ compact t /\ s homotopy_equivalent t
         ==> (connected((:real^N) DIFF s) <=> connected((:real^N) DIFF t))`;;

let JORDAN_BROUWER_NONSEPARATION_STRONG = `!s t a:real^N r.
        2 <= dimindex(:N) /\ s homeomorphic sphere(a,r) /\ t PSUBSET s
        ==> path_connected((:real^N) DIFF t)`;;

let JORDAN_BROUWER_ACCESSIBILITY = `!s c a:real^N r x y.
        2 <= dimindex(:N) /\
        s homeomorphic sphere(a,r) /\
        c IN components((:real^N) DIFF s) /\ x IN c /\ y IN s
        ==> ?g. arc g /\  pathstart g = x /\ pathfinish g = y /\
                IMAGE g (interval[vec 0,vec 1] DELETE (vec 1)) SUBSET c`;;

let HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE = `!s t:real^N->bool a r.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\
      compact s /\ compact t /\ s homotopy_equivalent t
      ==> (connected (sphere(a,r) DIFF s) <=> connected(sphere(a,r) DIFF t))`;;

let CONNECTED_COMPLEMENT_CONTRACTIBLE = `!s. 2 <= dimindex(:N) /\ compact s /\ contractible s
       ==> connected((:real^N) DIFF s)`;;

let CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE = `!g. 3 <= dimindex(:N) /\ simple_path g
       ==> connected((:real^N) DIFF path_image g)`;;

let PATH_CONNECTED_PSUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE = `!g s:real^N->bool.
        2 <= dimindex(:N) /\ simple_path g /\
        (:real^N) DIFF path_image g PSUBSET s
        ==> path_connected s`;;

(* ------------------------------------------------------------------------- *)
(* A few additional invariance of domain/dimension corollaries.              *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_ON_INVERSE = `!f g s. f real_continuous_on s /\
           (is_realinterval s \/ real_compact s \/ real_open s) /\
           (!x. x IN s ==> g(f x) = x)
           ==> g real_continuous_on (IMAGE f s)`;;

let REAL_CONTINUOUS_ON_INVERSE_ALT = `!f g s t. f real_continuous_on s /\
             (is_realinterval s \/ real_compact s \/ real_open s) /\
             IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x)
           ==> g real_continuous_on t`;;

let SIMPLY_CONNECTED_SPHERE_EQ = `!a:real^N r.
        simply_connected(sphere(a,r)) <=> 3 <= dimindex(:N) \/ r <= &0`;;

let SIMPLY_CONNECTED_PUNCTURED_UNIVERSE_EQ = `!a. simply_connected((:real^N) DELETE a) <=> 3 <= dimindex(:N)`;;

let NOT_SIMPLY_CONNECTED_CIRCLE = `!a:real^2 r. &0 < r ==> ~simply_connected(sphere(a,r))`;;

(* ------------------------------------------------------------------------- *)
(* The exponential function as a covering map.                               *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_CEXP_PUNCTURED_PLANE = `covering_space((:complex),cexp) ((:complex) DIFF {Cx(&0)})`;;

(* ------------------------------------------------------------------------- *)
(* Hence the Borsukian results about mappings into circle.                   *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_EQ_CONTINUOUS_LOGARITHM = `!f:real^N->complex s.
      (?a. homotopic_with (\h. T)
             (subtopology euclidean s,
              subtopology euclidean ((:complex) DIFF {Cx(&0)})) f (\t. a)) <=>
      (?g. g continuous_on s /\ (!x. x IN s ==> f x = cexp(g x)))`;;

let INESSENTIAL_IMP_CONTINUOUS_LOGARITHM_CIRCLE = `!f:real^N->complex s.
        (?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1))) f (\t. a))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)`;;

let INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE = `!f:real^N->complex s.
        (?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1))) f (\t. a)) <=>
        (?g. (Cx o g) continuous_on s /\
             !x. x IN s ==> f x = cexp(ii * Cx(g x)))`;;

let HOMOTOPIC_CIRCLEMAPS_DIV = `(!f g:real^N->real^2 s.
    homotopic_with (\x. T)
     (subtopology euclidean s,
      subtopology euclidean (sphere(vec 0,&1))) f g <=>
    f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,&1) /\
    g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,&1) /\
    ?c. homotopic_with (\x. T)
         (subtopology euclidean s,
          subtopology euclidean (sphere(vec 0,&1)))
         (\x. f x / g x) (\x. c))`
and HOMOTOPIC_CIRCLEMAPS_DIV_1 = `(!f g:real^N->real^2 s.
    homotopic_with (\x. T)
     (subtopology euclidean s,
      subtopology euclidean (sphere(vec 0,&1))) f g <=>
    f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,&1) /\
    g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,&1) /\
    homotopic_with (\x. T)
     (subtopology euclidean s,
      subtopology euclidean (sphere(vec 0,&1)))
     (\x. f x / g x) (\x. Cx(&1)))`;;

(* ------------------------------------------------------------------------- *)
(* In particular, complex logs exist on various "well-behaved" sets.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE = `!f:real^N->complex s.
        f continuous_on s /\ contractible s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)`;;

let CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED = `!f:real^N->complex s.
        f continuous_on s /\ simply_connected s /\ locally path_connected s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)`;;

let CONTINUOUS_LOGARITHM_ON_CBALL = `!f:real^N->complex a r.
        f continuous_on cball(a,r) /\
        (!z. z IN cball(a,r) ==> ~(f z = Cx(&0)))
        ==> ?h. h continuous_on cball(a,r) /\
                !z. z IN cball(a,r) ==> f z = cexp(h z)`;;

let CONTINUOUS_LOGARITHM_ON_BALL = `!f:real^N->complex a r.
        f continuous_on ball(a,r) /\
        (!x. x IN ball(a,r) ==> ~(f x = Cx(&0)))
        ==> ?h. h continuous_on ball(a,r) /\
                !x. x IN ball(a,r) ==> f x = cexp(h x)`;;

let CONTINUOUS_SQRT_ON_CONTRACTIBLE = `!f:real^N->complex s.
        f continuous_on s /\ contractible s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = (g x) pow 2`;;

let CONTINUOUS_SQRT_ON_SIMPLY_CONNECTED = `!f:real^N->complex s.
        f continuous_on s /\ simply_connected s /\ locally path_connected s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = (g x) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Analogously, holomorphic logarithms and square roots.                     *)
(* ------------------------------------------------------------------------- *)

let CONTRACTIBLE_IMP_HOLOMORPHIC_LOG = `(!s:complex->bool.
      contractible s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = cexp(g z))`
and SIMPLY_CONNECTED_IMP_HOLOMORPHIC_LOG = `(!s:complex->bool.
      simply_connected s /\ locally path_connected s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = cexp(g z))`;;

let CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT = `(!s:complex->bool.
      contractible s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\  !z. z IN s ==> f z = g z pow 2)`
and SIMPLY_CONNECTED_IMP_HOLOMORPHIC_SQRT = `(!s:complex->bool.
      simply_connected s /\ locally path_connected s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\  !z. z IN s ==> f z = g z pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Related theorems about holomorphic inverse cosines.                       *)
(* ------------------------------------------------------------------------- *)

let CONTRACTIBLE_IMP_HOLOMORPHIC_ACS = `!f s. f holomorphic_on s /\ contractible s /\
         (!z. z IN s ==> ~(f z = Cx(&1)) /\ ~(f z = --Cx(&1)))
         ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = ccos(g z)`;;

let CONTRACTIBLE_IMP_HOLOMORPHIC_ACS_BOUNDED = `!f s a.
        f holomorphic_on s /\ contractible s /\ a IN s /\
        (!z. z IN s ==> ~(f z = Cx(&1)) /\ ~(f z = --Cx(&1)))
        ==> ?g. g holomorphic_on s /\ norm(g a) <= pi + norm(f a) /\
                !z. z IN s ==> f z = ccos(g z)`;;

(* ------------------------------------------------------------------------- *)
(* Extension property for inessential maps. This almost follows from         *)
(* INESSENTIAL_NEIGHBOURHOOD_EXTENSION except that here we don't need to     *)
(* assume that t is closed in s.                                             *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_NEIGHBOURHOOD_EXTENSION_LOGARITHM = `!f:real^N->complex s t.
        f continuous_on s /\ t SUBSET s /\
        (?g. g continuous_on t /\ !x. x IN t ==> f x = cexp(g x))
        ==> ?u. t SUBSET u /\ open_in (subtopology euclidean s) u /\
                (?g. g continuous_on u /\ !x. x IN u ==> f x = cexp(g x))`;;

(* ------------------------------------------------------------------------- *)
(* The "borsukian" property of sets. This doesn't seem to have a standard    *)
(* name. Kuratowski uses "contractible with respect to [S^1]" while          *)
(* Whyburn uses "property b". It's closely related to unicoherence.          *)
(* ------------------------------------------------------------------------- *)

let borsukian = new_definition
 `borsukian(s:real^N->bool) <=>
        !f. f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)})
            ==> ?a. homotopic_with (\h. T)
                     (subtopology euclidean s,
                      subtopology euclidean ((:real^2) DIFF {Cx(&0)}))
                                   f (\x. a)`;;

let BORSUKIAN_RETRACTION_GEN = `!s:real^M->bool t:real^N->bool h k.
        h continuous_on s /\ IMAGE h s = t /\
        k continuous_on t /\ IMAGE k t SUBSET s /\
        (!y. y IN t ==> h(k y) = y) /\
        borsukian s
        ==> borsukian t`;;

let RETRACT_OF_BORSUKIAN = `!s t:real^N->bool. borsukian t /\ s retract_of t ==> borsukian s`;;

let HOMEOMORPHIC_BORSUKIAN = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ borsukian s ==> borsukian t`;;

let HOMEOMORPHIC_BORSUKIAN_EQ = `!s:real^M->bool t:real^N->bool.
     s homeomorphic t ==> (borsukian s <=> borsukian t)`;;

let BORSUKIAN_TRANSLATION = `!a:real^N s. borsukian (IMAGE (\x. a + x) s) <=> borsukian s`;;

add_translation_invariants [BORSUKIAN_TRANSLATION];;

let BORSUKIAN_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (borsukian(IMAGE f s) <=> borsukian s)`;;

add_linear_invariants [BORSUKIAN_INJECTIVE_LINEAR_IMAGE];;

let HOMEOMORPHISM_BORSUKIANNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (borsukian(IMAGE f k) <=> borsukian k)`;;

let HOMOTOPY_EQUIVALENT_BORSUKIANNESS = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t
        ==> (borsukian s <=> borsukian t)`;;

let BORSUKIAN_ALT = `!s:real^N->bool.
        borsukian s <=>
        !f g:real^N->real^2.
           f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)}) /\
           g continuous_on s /\ IMAGE g s SUBSET ((:real^2) DIFF {Cx(&0)})
           ==> homotopic_with (\h. T)
                (subtopology euclidean s,
                 subtopology euclidean ((:real^2) DIFF {Cx (&0)})) f g`;;

let BORSUKIAN_CONTINUOUS_LOGARITHM = `!s:real^N->bool.
        borsukian s <=>
        !f. f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)})
            ==> ?g. g continuous_on s /\ (!x. x IN s ==> f(x) = cexp(g x))`;;

let BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE = `!s:real^N->bool.
        borsukian s <=>
           !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
               ==> ?g. g continuous_on s /\ (!x. x IN s ==> f(x) = cexp(g x))`;;

let BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX = `!s:real^N->bool.
        borsukian s <=>
            !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
            ==> ?g. (Cx o g) continuous_on s /\
                    (!x. x IN s ==> f x = cexp(ii * Cx(g x)))`;;

let BORSUKIAN_CIRCLE = `!s:real^N->bool.
        borsukian s <=>
            !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
                ==> ?a. homotopic_with (\h. T)
                         (subtopology euclidean s,
                          subtopology euclidean (sphere(Cx(&0),&1)))
                         f (\x. a)`;;

let BORSUKIAN_CIRCLE_ALT = `!s:real^N->bool.
        borsukian s <=>
        !f g:real^N->real^2.
           f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1) /\
           g continuous_on s /\ IMAGE g s SUBSET sphere(Cx(&0),&1)
           ==> homotopic_with (\h. T)
                (subtopology euclidean s,
                 subtopology euclidean (sphere(Cx(&0),&1))) f g`;;

let CONTRACTIBLE_IMP_BORSUKIAN = `!s:real^N->bool. contractible s ==> borsukian s`;;

let CONIC_IMP_BORSUKIAN = `!s:real^N->bool. conic s ==> borsukian s`;;

let SIMPLY_CONNECTED_IMP_BORSUKIAN = `!s:real^N->bool.
        simply_connected s /\ locally path_connected s ==> borsukian s`;;

let STARLIKE_IMP_BORSUKIAN = `!s:real^N->bool. starlike s ==> borsukian s`;;

let BORSUKIAN_EMPTY = `borsukian({}:real^N->bool)`;;

let BORSUKIAN_UNIV = `borsukian(:real^N)`;;

let CONVEX_IMP_BORSUKIAN = `!s:real^N->bool. convex s ==> borsukian s`;;

let BORSUKIAN_1_GEN = `!s:real^N->bool.
        (dimindex(:N) = 1 \/ ?r:real^1->bool. s homeomorphic r)
        ==> borsukian s`;;

let BORSUKIAN_1 = `!s:real^1->bool. borsukian s`;;

let BORSUKIAN_SPHERE = `!a:real^N r. borsukian(sphere(a,r)) <=> r <= &0 \/ ~(dimindex(:N) = 2)`;;

let BORSUKIAN_OPEN_UNION = `!s t:real^N->bool.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        borsukian s /\ borsukian t /\ connected(s INTER t)
        ==> borsukian(s UNION t)`;;

let BORSUKIAN_CLOSED_UNION = `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        borsukian s /\ borsukian t /\ connected(s INTER t)
        ==> borsukian(s UNION t)`;;

let BORSUKIAN_SEPARATION_COMPACT = `!s:real^2->bool.
        compact s ==> (borsukian s <=> connected((:real^2) DIFF s))`;;

let BORSUKIAN_COMPONENTWISE_EQ = `!s:real^N->bool.
        locally connected s \/ compact s
        ==> (borsukian s <=> !c. c IN components s ==> borsukian c)`;;

let BORSUKIAN_COMPONENTWISE = `!s:real^N->bool.
        (locally connected s \/ compact s) /\
        (!c. c IN components s ==> borsukian c)
        ==> borsukian s`;;

let BORSUKIAN_MONOTONE_IMAGE_COMPACT = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
        borsukian s
        ==> borsukian t`;;

let BORSUKIAN_OPEN_MAP_IMAGE_COMPACT = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        borsukian s
        ==> borsukian t`;;

(* ------------------------------------------------------------------------- *)
(* Unicoherence (closed).                                                    *)
(* ------------------------------------------------------------------------- *)

let unicoherent = new_definition
 `unicoherent(u:real^N->bool) <=>
  !s t. connected s /\ connected t /\ s UNION t = u /\
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t
        ==> connected (s INTER t)`;;

let HOMEOMORPHIC_UNICOHERENT = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ unicoherent s ==> unicoherent t`;;

let HOMEOMORPHIC_UNICOHERENT_EQ = `!s:real^M->bool t:real^N->bool.
     s homeomorphic t ==> (unicoherent s <=> unicoherent t)`;;

let UNICOHERENT_TRANSLATION = `!a:real^N s. unicoherent (IMAGE (\x. a + x) s) <=> unicoherent s`;;

add_translation_invariants [UNICOHERENT_TRANSLATION];;

let UNICOHERENT_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (unicoherent(IMAGE f s) <=> unicoherent s)`;;

add_linear_invariants [UNICOHERENT_INJECTIVE_LINEAR_IMAGE];;

let HOMEOMORPHISM_UNICOHERENCE = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (unicoherent(IMAGE f k) <=> unicoherent k)`;;

let BORSUKIAN_IMP_UNICOHERENT = `!u:real^N->bool. borsukian u ==> unicoherent u`;;

let CONTRACTIBLE_IMP_UNICOHERENT = `!u:real^N->bool. contractible u ==> unicoherent u`;;

let CONVEX_IMP_UNICOHERENT = `!u:real^N->bool. convex u ==> unicoherent u`;;

let UNICOHERENT_UNIV = `unicoherent(:real^N)`;;

let UNICOHERENT_MONOTONE_IMAGE_COMPACT = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
        unicoherent s
        ==> unicoherent t`;;

(* ------------------------------------------------------------------------- *)
(* Several common variants of unicoherence for R^n.                          *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_FRONTIER_SIMPLE = `!s. connected(s) /\ connected((:real^N) DIFF s) ==> connected(frontier s)`;;

let CONNECTED_FRONTIER_COMPONENT_COMPLEMENT = `!s c:real^N->bool.
        connected s /\ c IN components((:real^N) DIFF s)
        ==> connected(frontier c)`;;

let CONNECTED_FRONTIER_DISJOINT = `!s t:real^N->bool.
     connected s /\ connected t /\ DISJOINT s t /\ frontier s SUBSET frontier t
     ==> connected(frontier s)`;;

let SEPARATION_BY_COMPONENT_CLOSED_POINTWISE = `!s a b. closed s /\ ~connected_component ((:real^N) DIFF s) a b
           ==> ?c. c IN components s /\
                   ~connected_component((:real^N) DIFF c) a b`;;

let SEPARATION_BY_COMPONENT_CLOSED = `!s. closed s /\ ~connected((:real^N) DIFF s)
       ==> ?c. c IN components s /\ ~connected((:real^N) DIFF c)`;;

let SEPARATION_BY_UNION_CLOSED_POINTWISE = `!s t a b. closed s /\ closed t /\ DISJOINT s t /\
             connected_component ((:real^N) DIFF s) a b /\
             connected_component ((:real^N) DIFF t) a b
             ==> connected_component ((:real^N) DIFF (s UNION t)) a b`;;

let SEPARATION_BY_UNION_CLOSED = `!s t:real^N->bool.
        closed s /\ closed t /\ DISJOINT s t /\
        connected((:real^N) DIFF s) /\
        connected((:real^N) DIFF t)
        ==> connected((:real^N) DIFF (s UNION t))`;;

let OPEN_UNICOHERENT_UNIV = `!s t. open s /\ open t /\ connected s /\ connected t /\
         s UNION t = (:real^N)
         ==> connected(s INTER t)`;;

let SEPARATION_BY_COMPONENT_OPEN = `!s. open s /\ ~connected((:real^N) DIFF s)
       ==> ?c. c IN components s /\ ~connected((:real^N) DIFF c)`;;

let SEPARATION_BY_UNION_OPEN = `!s t:real^N->bool.
        open s /\ open t /\ DISJOINT s t /\
        connected((:real^N) DIFF s) /\
        connected((:real^N) DIFF t)
        ==> connected((:real^N) DIFF (s UNION t))`;;

let CONNECTED_INTER_DISJOINT_OPEN_FRONTIERS = `!s t:real^N->bool.
        open s /\ connected s /\ open t /\ connected t /\
        DISJOINT (frontier s) (frontier t)
        ==> connected(s INTER t)`;;

let NONSEPARATION_BY_COMPONENT_EQ = `!s. (open s \/ closed s)
       ==> ((!c. c IN components s ==> connected((:real^N) DIFF c)) <=>
            connected((:real^N) DIFF s))`;;

let CONNECTED_COMMON_FRONTIER_DOMAINS = `!s t c:real^N->bool.
        open s /\ connected s /\
        open t /\ connected t /\
        ~(s = t) /\ frontier s = c /\ frontier t = c
        ==> connected c`;;

(* ------------------------------------------------------------------------- *)
(* The frontier of an ANR is locally connected (this is only this late       *)
(* since it's handy to use basics about unicoherence).                       *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONNECTED_FRONTIER_ANR = `!s:real^N->bool.
        compact s /\ ANR s ==> locally connected (frontier s)`;;

(* ------------------------------------------------------------------------- *)
(* Another interesting equivalent of an inessential mapping into C-{0}       *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_EQ_EXTENSIBLE = `!f s.
   closed s
   ==> ((?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean ((:complex) DIFF {Cx(&0)}))
              f (\t. a)) <=>
        (?g. g continuous_on (:real^N) /\
             (!x. x IN s ==> g x = f x) /\ (!x. ~(g x = Cx(&0)))))`;;

(* ------------------------------------------------------------------------- *)
(* Another simple case where sphere maps are nullhomotopic.                  *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_SPHEREMAP_2 = `!f:real^M->real^N a r b s.
        2 < dimindex(:M) /\ dimindex(:N) = 2 /\
        f continuous_on sphere(a,r) /\
        IMAGE f (sphere(a,r)) SUBSET (sphere(b,s))
        ==> ?c. homotopic_with (\z. T)
                  (subtopology euclidean (sphere(a,r)),
                   subtopology euclidean (sphere(b,s))) f (\x. c)`;;

(* ------------------------------------------------------------------------- *)
(* Janiszewski's theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let JANISZEWSKI = `!s t a b:real^2.
        compact s /\ closed t /\ connected(s INTER t) /\
        connected_component ((:real^2) DIFF s) a b /\
        connected_component ((:real^2) DIFF t) a b
        ==> connected_component ((:real^2) DIFF (s UNION t)) a b`;;

let JANISZEWSKI_GEN = `!s t a b:real^N.
        dimindex(:N) <= 2 /\
        compact s /\ closed t /\ connected(s INTER t) /\
        connected_component ((:real^N) DIFF s) a b /\
        connected_component ((:real^N) DIFF t) a b
        ==> connected_component ((:real^N) DIFF (s UNION t)) a b`;;

let JANISZEWSKI_CONNECTED = `!s t:real^2->bool.
       compact s /\ closed t /\ connected(s INTER t) /\
       connected ((:real^2) DIFF s) /\ connected ((:real^2) DIFF t)
       ==> connected((:real^2) DIFF (s UNION t))`;;

let JANISZEWSKI_DUAL = `!s t:real^2->bool.
        compact s /\ compact t /\ connected s /\ connected t /\
        connected((:real^2) DIFF (s UNION t))
         ==> connected(s INTER t)`;;

(* ------------------------------------------------------------------------- *)
(* Triple-curve or "theta-curve" theorem. Proof that there is no fourth      *)
(* component taken from Kuratowski's Topology vol 2, para 61, II.            *)
(* ------------------------------------------------------------------------- *)

let THETA_CURVE_INSIDE_CASES = `!c1 c2 c3 a b:real^2.
        arc c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        arc c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        arc c3 /\ pathstart c3 = a /\ pathfinish c3 = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c2 INTER path_image c3 = {a,b} /\
        path_image c3 INTER path_image c1 = {a,b}
        ==> path_image c1 DIFF {a,b} SUBSET
            inside(path_image c2 UNION path_image c3) \/
            path_image c2 DIFF {a,b} SUBSET
            inside(path_image c3 UNION path_image c1) \/
            path_image c3 DIFF {a,b} SUBSET
            inside(path_image c1 UNION path_image c2)`;;

let SPLIT_INSIDE_SIMPLE_CLOSED_CURVE = `!c1 c2 c a b:real^2.
        ~(a = b) /\
        simple_path c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        simple_path c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        simple_path c /\ pathstart c = a /\ pathfinish c = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c1 INTER path_image c = {a,b} /\
        path_image c2 INTER path_image c = {a,b} /\
        ~(path_image c INTER inside(path_image c1 UNION path_image c2) = {})
        ==> inside(path_image c1 UNION path_image c) INTER
            inside(path_image c2 UNION path_image c) = {} /\
            inside(path_image c1 UNION path_image c) UNION
            inside(path_image c2 UNION path_image c) UNION
            (path_image c DIFF {a,b}) =
            inside(path_image c1 UNION path_image c2)`;;
