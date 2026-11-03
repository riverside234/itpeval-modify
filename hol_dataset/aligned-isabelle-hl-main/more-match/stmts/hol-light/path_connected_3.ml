(* ========================================================================= *)
(* Elementary topology in Euclidean space.                                   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2017                       *)
(*                (c) Copyright, Valentina Bruno 2010                        *)
(*               (c) Copyright, Marco Maggesi 2014-2017                      *)
(*             (c) Copyright, Andrea Gabrielli 2016-2017                     *)
(* ========================================================================= *)

needs "Library/card.ml";;
needs "Library/iter.ml";;
needs "Multivariate/metric.ml";;
needs "Multivariate/determinants.ml";;

(* ------------------------------------------------------------------------- *)
(* The universal Euclidean topology that we use most of the time.            *)
(* ------------------------------------------------------------------------- *)

let open_def = new_definition
  `open s <=> !x. x IN s ==> ?e. &0 < e /\ !x'. dist(x',x) < e ==> x' IN s`;;

let euclidean = new_definition
 `euclidean = topology open`;;

let euclidean_metric = new_definition
  `euclidean_metric = metric ((:real^N), dist)`;;

let EUCLIDEAN_METRIC = `mdist (euclidean_metric:(real^N)metric) = dist /\
   mspace euclidean_metric = (:real^N)`;;

let OPEN_IN_EUCLIDEAN_METRIC = `open_in (mtopology euclidean_metric) = open:(real^N->bool)->bool`;;

let OPEN_IN_EUCLIDEAN = `open_in euclidean = open`;;

let OPEN_IN = `!s:real^N->bool. open s <=> open_in euclidean s`;;

let MTOPOLOGY_EUCLIDEAN_METRIC = `mtopology euclidean_metric = euclidean:(real^N)topology`;;

let METRIZABLE_SPACE_EUCLIDEAN = `metrizable_space euclidean`;;

let HAUSDORFF_SPACE_EUCLIDEAN = `hausdorff_space euclidean`;;

let KC_SPACE_EUCLIDEAN = `kc_space(euclidean:(real^N)topology)`;;

let T1_SPACE_EUCLIDEAN = `t1_space euclidean`;;

let REGULAR_SPACE_EUCLIDEAN = `regular_space euclidean`;;

let K_SPACE_EUCLIDEAN = `k_space(euclidean:(real^N)topology)`;;

let OPEN_EMPTY = `open {}`;;

let OPEN_UNIV = `open(:real^N)`;;

let OPEN_INTER = `!s t. open s /\ open t ==> open (s INTER t)`;;

let OPEN_UNIONS = `(!s. s IN f ==> open s) ==> open(UNIONS f)`;;

let OPEN_EXISTS_IN = `!P Q:A->real^N->bool.
        (!a. P a ==> open {x | Q a x}) ==> open {x | ?a. P a /\ Q a x}`;;

let OPEN_EXISTS = `!Q:A->real^N->bool. (!a. open {x | Q a x}) ==> open {x | ?a. Q a x}`;;

let OPEN_RELATIVE_TO = `!s t:real^N->bool.
        (open relative_to s) t <=> open_in (subtopology euclidean s) t`;;

let TOPSPACE_EUCLIDEAN = `topspace euclidean = (:real^N)`;;

let TOPSPACE_EUCLIDEAN_SUBTOPOLOGY = `!s. topspace (subtopology euclidean s) = s`;;

let OPEN_IN_REFL = `!s:real^N->bool. open_in (subtopology euclidean s) s`;;

let SUBTOPOLOGY_EUCLIDEAN_EQ_DISCRETE_TOPOLOGY_FINITE = `!s:real^N->bool.
        FINITE s ==> subtopology euclidean s = discrete_topology s`;;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let closed = new_definition
  `closed(s:real^N->bool) <=> open(UNIV DIFF s)`;;

let CLOSED_IN = `!s:real^N->bool. closed s <=> closed_in euclidean s`;;

let CLOSED_IN_EUCLIDEAN = `closed_in euclidean = closed:(real^N->bool)->bool`;;

let CLOSED_IN_EUCLIDEAN_METRIC = `closed_in (mtopology euclidean_metric) = closed:(real^N->bool)->bool`;;

let CLOSED_IN_REFL = `!s:real^N->bool. closed_in (subtopology euclidean s) s`;;

let CLOSED_RELATIVE_TO = `!s t:real^N->bool.
        (closed relative_to s) t <=> closed_in (subtopology euclidean s) t`;;

let OPEN_UNION = `!s t. open s /\ open t ==> open(s UNION t)`;;

let OPEN_SUBOPEN = `!s. open s <=> !x. x IN s ==> ?t. open t /\ x IN t /\ t SUBSET s`;;

let CLOSED_EMPTY = `closed {}`;;

let CLOSED_UNIV = `closed(UNIV:real^N->bool)`;;

let CLOSED_UNION = `!s t. closed s /\ closed t ==> closed(s UNION t)`;;

let CLOSED_INTER = `!s t. closed s /\ closed t ==> closed(s INTER t)`;;

let CLOSED_INTERS = `!f. (!s:real^N->bool. s IN f ==> closed s) ==> closed(INTERS f)`;;

let CLOSED_FORALL_IN = `!P Q:A->real^N->bool.
        (!a. P a ==> closed {x | Q a x}) ==> closed {x | !a. P a ==> Q a x}`;;

let CLOSED_FORALL = `!Q:A->real^N->bool. (!a. closed {x | Q a x}) ==> closed {x | !a. Q a x}`;;

let OPEN_CLOSED = `!s:real^N->bool. open s <=> closed(UNIV DIFF s)`;;

let OPEN_DIFF = `!s t. open s /\ closed t ==> open(s DIFF t)`;;

let CLOSED_DIFF = `!s t. closed s /\ open t ==> closed(s DIFF t)`;;

let OPEN_INTERS = `!s. FINITE s /\ (!t. t IN s ==> open t) ==> open(INTERS s)`;;

let CLOSED_UNIONS = `!s. FINITE s /\ (!t. t IN s ==> closed t) ==> closed(UNIONS s)`;;

let CLOSED_LOCALLY_FINITE_UNIONS = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> closed s) /\ locally_finite_in euclidean f
        ==> closed(UNIONS f)`;;

(* ------------------------------------------------------------------------- *)
(* Componentwise, lifted and dropped limits and continuity.                  *)
(* ------------------------------------------------------------------------- *)

let LIMIT_EQ_LIFT = `!(net:A net) f l.
        limit euclideanreal f l net <=>
        limit euclidean (lift o f) (lift l) net`;;

let LIMIT_EQ_DROP = `!(net:A net) f l.
        limit euclidean f l net <=>
        limit euclideanreal (drop o f) (drop l) net`;;

let CONTINUOUS_MAP_EQ_LIFT = `!top f:A->real.
        continuous_map(top,euclideanreal) f <=>
        continuous_map(top,euclidean) (lift o f)`;;

let CONTINUOUS_MAP_EQ_DROP = `!top f:A->real^1.
        continuous_map(top,euclidean) f <=>
        continuous_map(top,euclideanreal) (drop o f)`;;

let LIMIT_COMPONENTWISE_REAL = `!net (f:A->real^N) l.
        limit euclidean f l net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> limit euclideanreal (\x. f x$i) (l$i) net`;;

let CONTINUOUS_MAP_COMPONENTWISE_REAL = `!top (f:A->real^N).
        continuous_map (top,euclidean) f <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> continuous_map (top,euclideanreal) (\x. f x$i)`;;

let CONTINUOUS_MAP_LIFT = `continuous_map (euclideanreal,euclidean) lift`;;

let CONTINUOUS_MAP_DROP = `continuous_map (euclidean,euclideanreal) drop`;;

let CONTINUOUS_MAP_LIFT_EQ = `!top f:real^1->A.
        continuous_map(euclidean,top) f <=>
        continuous_map(euclideanreal,top) (f o lift)`;;

let CONTINUOUS_MAP_DROP_EQ = `!top f:real->A.
        continuous_map(euclideanreal,top) f <=>
        continuous_map(euclidean,top) (f o drop)`;;

let CONTINUOUS_MAP_LIFT_EQ_GEN = `!top s (f:real^1->A).
        continuous_map (subtopology euclidean s,top) f <=>
        continuous_map (subtopology euclideanreal (IMAGE drop s),top)
                       (f o lift)`;;

let CONTINUOUS_MAP_DROP_EQ_GEN = `!top s (f:real->A).
        continuous_map(subtopology euclideanreal s,top) f <=>
        continuous_map(subtopology euclidean (IMAGE lift s),top) (f o drop)`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic combining theorems for vector-valued continuous maps.          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MAP_VECTOR_CONST = `!(top:A topology) (b:real^N).
        continuous_map (top,euclidean) (\x. b)`;;

let CONTINUOUS_MAP_VECTOR_ADD = `!top f g:A->real^N.
        continuous_map(top,euclidean) f /\ continuous_map(top,euclidean) g
        ==> continuous_map(top,euclidean) (\x. f x + g x)`;;

let CONTINUOUS_MAP_VECTOR_SUB = `!top f g:A->real^N.
        continuous_map(top,euclidean) f /\ continuous_map(top,euclidean) g
        ==> continuous_map(top,euclidean) (\x. f x - g x)`;;

let CONTINUOUS_MAP_VECTOR_MUL = `!top c f:A->real^N.
        continuous_map(top,euclideanreal) c /\ continuous_map(top,euclidean) f
        ==> continuous_map(top,euclidean) (\x. c x % f x)`;;

let CONTINUOUS_MAP_DOT = `!top f g:A->real^N.
        continuous_map(top,euclidean) f /\ continuous_map(top,euclidean) g
        ==> continuous_map(top,euclideanreal) (\x. f x dot g x)`;;

let CONTINUOUS_MAP_VSUM = `!top k (f:A->K->real^N).
        FINITE k /\ (!i. i IN k ==> continuous_map(top,euclidean) (\x. f x i))
        ==> continuous_map(top,euclidean) (\x. vsum k (f x))`;;

let CONTINUOUS_MAP_EUCLIDEAN_COMPONENT = `!top (f:A->real^N) i.
        continuous_map(top,euclidean) f
        ==> continuous_map (top,euclideanreal) (\x. f x$i)`;;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls and spheres.                                        *)
(* ------------------------------------------------------------------------- *)

let ball = new_definition
  `ball(x,e) = { y | dist(x,y) < e}`;;

let IN_BALL = `!x y e. y IN ball(x,e) <=> dist(x,y) < e`;;

let MBALL_EUCLIDEAN = `!x:real^N r. mball euclidean_metric (x,r) = ball(x,r)`;;

let cball = new_definition
  `cball(x,e) = { y | dist(x,y) <= e}`;;

let IN_CBALL = `!x y e. y IN cball(x,e) <=> dist(x,y) <= e`;;

let MCBALL_EUCLIDEAN = `!x:real^N r. mcball euclidean_metric (x,r) = cball(x,r)`;;

let sphere = new_definition
  `sphere(x,e) = { y | dist(x,y) = e}`;;

let IN_SPHERE = `!x y e. y IN sphere(x,e) <=> dist(x,y) = e`;;

let IN_BALL_0 = `!x e. x IN ball(vec 0,e) <=> norm(x) < e`;;

let IN_CBALL_0 = `!x e. x IN cball(vec 0,e) <=> norm(x) <= e`;;

let IN_SPHERE_0 = `!x e. x IN sphere(vec 0,e) <=> norm(x) = e`;;

let BALL_TRIVIAL = `!x. ball(x,&0) = {}`;;

let CBALL_TRIVIAL = `!x. cball(x,&0) = {x}`;;

let CENTRE_IN_CBALL = `!x e. x IN cball(x,e) <=> &0 <= e`;;

let BALL_SUBSET_CBALL = `!x e. ball(x,e) SUBSET cball(x,e)`;;

let SPHERE_SUBSET_CBALL = `!x e. sphere(x,e) SUBSET cball(x,e)`;;

let SUBSET_BALL = `!x d e. d <= e ==> ball(x,d) SUBSET ball(x,e)`;;

let SUBSET_CBALL = `!x d e. d <= e ==> cball(x,d) SUBSET cball(x,e)`;;

let BALL_MAX_UNION = `!a r s. ball(a,max r s) = ball(a,r) UNION ball(a,s)`;;

let BALL_MIN_INTER = `!a r s. ball(a,min r s) = ball(a,r) INTER ball(a,s)`;;

let CBALL_MAX_UNION = `!a r s. cball(a,max r s) = cball(a,r) UNION cball(a,s)`;;

let CBALL_MIN_INTER = `!x d e. cball(x,min d e) = cball(x,d) INTER cball(x,e)`;;

let BALL_TRANSLATION = `!a x r. ball(a + x,r) = IMAGE (\y. a + y) (ball(x,r))`;;

let CBALL_TRANSLATION = `!a x r. cball(a + x,r) = IMAGE (\y. a + y) (cball(x,r))`;;

let SPHERE_TRANSLATION = `!a x r. sphere(a + x,r) = IMAGE (\y. a + y) (sphere(x,r))`;;

add_translation_invariants
  [BALL_TRANSLATION; CBALL_TRANSLATION; SPHERE_TRANSLATION];;

let BALL_LINEAR_IMAGE = `!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> ball(f x,r) = IMAGE f (ball(x,r))`;;

let CBALL_LINEAR_IMAGE = `!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> cball(f x,r) = IMAGE f (cball(x,r))`;;

let SPHERE_LINEAR_IMAGE = `!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> sphere(f x,r) = IMAGE f (sphere(x,r))`;;

add_linear_invariants
  [BALL_LINEAR_IMAGE; CBALL_LINEAR_IMAGE; SPHERE_LINEAR_IMAGE];;

let BALL_SCALING = `!c. &0 < c ==> !x r. ball(c % x,c * r) = IMAGE (\x. c % x) (ball(x,r))`;;

let CBALL_SCALING = `!c. &0 < c ==> !x r. cball(c % x,c * r) = IMAGE (\x. c % x) (cball(x,r))`;;

let SPHERE_SCALING = `!c. &0 < c
       ==> !x r. sphere(c % x,c * r) = IMAGE (\x. c % x) (sphere(x,r))`;;

add_scaling_theorems [BALL_SCALING; CBALL_SCALING; SPHERE_SCALING];;

let CBALL_DIFF_BALL = `!a r. cball(a,r) DIFF ball(a,r) = sphere(a,r)`;;

let BALL_UNION_SPHERE = `!a r. ball(a,r) UNION sphere(a,r) = cball(a,r)`;;

let SPHERE_UNION_BALL = `!a r. sphere(a,r) UNION ball(a,r)  = cball(a,r)`;;

let CBALL_DIFF_SPHERE = `!a r. cball(a,r) DIFF sphere(a,r) = ball(a,r)`;;

let OPEN_BALL = `!x e. open(ball(x,e))`;;

let CENTRE_IN_BALL = `!x e. x IN ball(x,e) <=> &0 < e`;;

let OPEN_CONTAINS_BALL = `!s. open s <=> !x. x IN s ==> ?e. &0 < e /\ ball(x,e) SUBSET s`;;

let OPEN_CONTAINS_BALL_EQ = `!s. open s ==> (!x. x IN s <=> ?e. &0 < e /\ ball(x,e) SUBSET s)`;;

let BALL_EQ_EMPTY = `!x e. (ball(x,e) = {}) <=> e <= &0`;;

let BALL_EMPTY = `!x e. e <= &0 ==> ball(x,e) = {}`;;

let OPEN_CONTAINS_CBALL = `!s. open s <=> !x. x IN s ==> ?e. &0 < e /\ cball(x,e) SUBSET s`;;

let OPEN_CONTAINS_CBALL_EQ = `!s. open s ==> (!x. x IN s <=> ?e. &0 < e /\ cball(x,e) SUBSET s)`;;

let SPHERE_EQ_EMPTY = `!a:real^N r. sphere(a,r) = {} <=> r < &0`;;

let SPHERE_EMPTY = `!a:real^N r. r < &0 ==> sphere(a,r) = {}`;;

let NEGATIONS_BALL = `!r. IMAGE (--) (ball(vec 0:real^N,r)) = ball(vec 0,r)`;;

let NEGATIONS_CBALL = `!r. IMAGE (--) (cball(vec 0:real^N,r)) = cball(vec 0,r)`;;

let NEGATIONS_SPHERE = `!r. IMAGE (--) (sphere(vec 0:real^N,r)) = sphere(vec 0,r)`;;

let ORTHOGONAL_TRANSFORMATION_BALL = `!f:real^N->real^N r.
    orthogonal_transformation f ==> IMAGE f (ball(vec 0,r)) = ball(vec 0,r)`;;

let ORTHOGONAL_TRANSFORMATION_CBALL = `!f:real^N->real^N r.
    orthogonal_transformation f ==> IMAGE f (cball(vec 0,r)) = cball(vec 0,r)`;;

let ORTHOGONAL_TRANSFORMATION_SPHERE = `!f:real^N->real^N r.
    orthogonal_transformation f
    ==> IMAGE f (sphere(vec 0,r)) = sphere(vec 0,r)`;;

(* ------------------------------------------------------------------------- *)
(* Basic "localization" results.                                             *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_OPEN = `!s:real^N->bool u.
        open_in (subtopology euclidean u) s <=> ?t. open t /\ (s = u INTER t)`;;

let OPEN_IN_INTER_OPEN = `!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\ open t
        ==> open_in (subtopology euclidean u) (s INTER t)`;;

let OPEN_IN_OPEN_INTER = `!u s. open s ==> open_in (subtopology euclidean u) (u INTER s)`;;

let OPEN_OPEN_IN_TRANS = `!s t. open s /\ open t /\ t SUBSET s
         ==> open_in (subtopology euclidean s) t`;;

let OPEN_SUBSET = `!s t:real^N->bool.
        s SUBSET t /\ open s ==> open_in (subtopology euclidean t) s`;;

let CLOSED_IN_DIFF_OPEN = `!s t. open t ==> closed_in (subtopology euclidean s) (s DIFF t)`;;

let CLOSED_IN_CLOSED = `!s:real^N->bool u.
    closed_in (subtopology euclidean u) s <=> ?t. closed t /\ (s = u INTER t)`;;

let CLOSED_SUBSET_EQ = `!u s:real^N->bool.
        closed s ==> (closed_in (subtopology euclidean u) s <=> s SUBSET u)`;;

let CLOSED_IN_INTER_CLOSED = `!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\ closed t
        ==> closed_in (subtopology euclidean u) (s INTER t)`;;

let CLOSED_IN_CLOSED_INTER = `!u s. closed s ==> closed_in (subtopology euclidean u) (u INTER s)`;;

let CLOSED_SUBSET = `!s t:real^N->bool.
        s SUBSET t /\ closed s ==> closed_in (subtopology euclidean t) s`;;

let OPEN_IN_DIFF_CLOSED = `!s t. closed t ==> open_in (subtopology euclidean s) (s DIFF t)`;;

let open_in = `!u s:real^N->bool.
        open_in (subtopology euclidean u) s <=>
          s SUBSET u /\
          !x. x IN s ==> ?e. &0 < e /\
                             !x'. x' IN u /\ dist(x',x) < e ==> x' IN s`;;

let OPEN_IN_CONTAINS_BALL = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s <=>
        s SUBSET t /\
        !x. x IN s ==> ?e. &0 < e /\ ball(x,e) INTER t SUBSET s`;;

let OPEN_IN_CONTAINS_CBALL = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s <=>
        s SUBSET t /\
        !x. x IN s ==> ?e. &0 < e /\ cball(x,e) INTER t SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* These "transitivity" results are handy too.                               *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANS_EQ = `!s t:real^N->bool.
        (!u. open_in (subtopology euclidean t) u
             ==> open_in (subtopology euclidean s) t)
        <=> open_in (subtopology euclidean s) t`;;

let OPEN_IN_OPEN_TRANS = `!s t. open_in (subtopology euclidean t) s /\ open t ==> open s`;;

let CLOSED_IN_TRANS_EQ = `!s t:real^N->bool.
        (!u. closed_in (subtopology euclidean t) u
             ==> closed_in (subtopology euclidean s) t)
        <=> closed_in (subtopology euclidean s) t`;;

let CLOSED_IN_CLOSED_TRANS = `!s t. closed_in (subtopology euclidean t) s /\ closed t ==> closed s`;;

let OPEN_IN_OPEN_EQ = `!s t. open s
         ==> (open_in (subtopology euclidean s) t <=> open t /\ t SUBSET s)`;;

let CLOSED_IN_CLOSED_EQ = `!s t. closed s
         ==> (closed_in (subtopology euclidean s) t <=>
              closed t /\ t SUBSET s)`;;

(* ------------------------------------------------------------------------- *)
(* Also some invariance theorems for relative topology.                      *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANSLATION_EQ = `!a s t. open_in (subtopology euclidean (IMAGE (\x. a + x) t))
                   (IMAGE (\x. a + x) s) <=>
           open_in (subtopology euclidean t) s`;;

add_translation_invariants [OPEN_IN_TRANSLATION_EQ];;

let CLOSED_IN_TRANSLATION_EQ = `!a s t. closed_in (subtopology euclidean (IMAGE (\x. a + x) t))
                   (IMAGE (\x. a + x) s) <=>
           closed_in (subtopology euclidean t) s`;;

add_translation_invariants [CLOSED_IN_TRANSLATION_EQ];;

let OPEN_IN_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (open_in (subtopology euclidean (IMAGE f t)) (IMAGE f s) <=>
               open_in (subtopology euclidean t) s)`;;

add_linear_invariants [OPEN_IN_INJECTIVE_LINEAR_IMAGE];;

let CLOSED_IN_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (closed_in (subtopology euclidean (IMAGE f t)) (IMAGE f s) <=>
               closed_in (subtopology euclidean t) s)`;;

add_linear_invariants [CLOSED_IN_INJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Relating two variants of Euclidean space, one within product topology.    *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_MAPS_EUCLIDEAN_SPACE_EUCLIDEAN_GEN = `!n. n <= dimindex(:N)
       ==> homeomorphic_maps
             (euclidean_space n,
              subtopology euclidean (span(IMAGE basis (1..n)):real^N->bool))
             ((\x. lambda i. if 1 <= i /\ i <= n then x i else &0),
              (\x i. if 1 <= i /\ i <= n then x$i else &0))`;;

let HOMEOMORPHIC_MAPS_EUCLIDEAN_SPACE_EUCLIDEAN = `homeomorphic_maps (euclidean_space(dimindex(:N)),euclidean:(real^N)topology)
                 ((\x. lambda i. x i),
                  (\x i. if 1 <= i /\ i <= dimindex(:N) then x$i else &0))`;;

let HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE = `!n. 1 <= n /\ n <= dimindex(:N)
       ==> homeomorphic_maps
            (nsphere(n - 1),
             subtopology euclidean
              (sphere(vec 0:real^N,&1) INTER span(IMAGE basis (1..n))))
            ((\x. lambda i. if 1 <= i /\ i <= n then x i else &0),
             (\x i. if 1 <= i /\ i <= n then x$i else &0))`;;

(* ------------------------------------------------------------------------- *)
(* Manhattan metric.                                                         *)
(* ------------------------------------------------------------------------- *)

let manhattan = new_definition
  `manhattan =
   metric ((:real^N), \(x,y). sum (1..dimindex(:N)) (\i. abs(x$i - y$i)))`;;

let MANHATTAN = `mspace manhattan = (:real^N) /\
   (!x y. mdist manhattan (x:real^N,y) =
          sum (1..dimindex(:N)) (\i. abs(x$i - y$i)))`;;

(* ------------------------------------------------------------------------- *)
(* Line segments, with open/closed overloading of (a,b) and [a,b].           *)
(* ------------------------------------------------------------------------- *)

let closed_segment = define
 `closed_segment[a,b] = {(&1 - u) % a + u % b | &0 <= u /\ u <= &1}`;;

let open_segment = new_definition
 `open_segment(a,b) = closed_segment[a,b] DIFF {a,b}`;;

let OPEN_SEGMENT_ALT = `!a b:real^N.
        ~(a = b)
        ==> open_segment(a,b) = {(&1 - u) % a + u % b | &0 < u /\ u < &1}`;;

make_overloadable "segment" `:A`;;

overload_interface("segment",`open_segment`);;
overload_interface("segment",`closed_segment`);;

let segment = `segment[a,b] = {(&1 - u) % a + u % b | &0 <= u /\ u <= &1} /\
   segment(a,b) = segment[a,b] DIFF {a,b}`;;

let SEGMENT_REFL = `(!a. segment[a,a] = {a}) /\
   (!a. segment(a,a) = {})`;;

let IN_SEGMENT = `!a b x:real^N.
        (x IN segment[a,b] <=>
         ?u. &0 <= u /\ u <= &1 /\ x = (&1 - u) % a + u % b) /\
        (x IN segment(a,b) <=>
         ~(a = b) /\ ?u. &0 < u /\ u < &1 /\ x = (&1 - u) % a + u % b)`;;

let SEGMENT_SYM = `(!a b:real^N. segment[a,b] = segment[b,a]) /\
   (!a b:real^N. segment(a,b) = segment(b,a))`;;

let ENDS_IN_SEGMENT = `!a b. a IN segment[a,b] /\ b IN segment[a,b]`;;

let ENDS_NOT_IN_SEGMENT = `!a b. ~(a IN segment(a,b)) /\ ~(b IN segment(a,b))`;;

let SEGMENT_CLOSED_OPEN = `!a b. segment[a,b] = segment(a,b) UNION {a,b}`;;

let SEGMENT_OPEN_SUBSET_CLOSED = `!a b. segment(a,b) SUBSET segment[a,b]`;;

let MIDPOINT_IN_SEGMENT = `(!a b:real^N. midpoint(a,b) IN segment[a,b]) /\
   (!a b:real^N. midpoint(a,b) IN segment(a,b) <=> ~(a = b))`;;

let BETWEEN_IN_SEGMENT = `!x a b:real^N. between x (a,b) <=> x IN segment[a,b]`;;

let IN_SEGMENT_COMPONENT = `!a b x:real^N i.
        x IN segment[a,b] /\ 1 <= i /\ i <= dimindex(:N)
        ==> min (a$i) (b$i) <= x$i /\ x$i <= max (a$i) (b$i)`;;

let SEGMENT_TRANSLATION = `(!c a b. segment[c + a,c + b] = IMAGE (\x. c + x) (segment[a,b])) /\
   (!c a b. segment(c + a,c + b) = IMAGE (\x. c + x) (segment(a,b)))`;;

add_translation_invariants
 [CONJUNCT1 SEGMENT_TRANSLATION; CONJUNCT2 SEGMENT_TRANSLATION];;

let CLOSED_SEGMENT_LINEAR_IMAGE = `!f a b. linear f
           ==> segment[f a,f b] = IMAGE f (segment[a,b])`;;

add_linear_invariants [CLOSED_SEGMENT_LINEAR_IMAGE];;

let OPEN_SEGMENT_LINEAR_IMAGE = `!f:real^M->real^N a b.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> segment(f a,f b) = IMAGE f (segment(a,b))`;;

add_linear_invariants [OPEN_SEGMENT_LINEAR_IMAGE];;

let IN_OPEN_SEGMENT = `!a b x:real^N.
        x IN segment(a,b) <=> x IN segment[a,b] /\ ~(x = a) /\ ~(x = b)`;;

let IN_OPEN_SEGMENT_ALT = `!a b x:real^N.
        x IN segment(a,b) <=>
        x IN segment[a,b] /\ ~(x = a) /\ ~(x = b) /\ ~(a = b)`;;

let COLLINEAR_DIST_IN_CLOSED_SEGMENT = `!a b x. collinear {x,a,b} /\
           dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)
           ==> x IN segment[a,b]`;;

let COLLINEAR_DIST_IN_OPEN_SEGMENT = `!a b x. collinear {x,a,b} /\
           dist(x,a) < dist(a,b) /\ dist(x,b) < dist(a,b)
           ==> x IN segment(a,b)`;;

let DIST_IN_CLOSED_SEGMENT = `(!a b x:real^N.
    x IN segment[a,b] ==> dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b))`
and DIST_IN_OPEN_SEGMENT = `(!a b x:real^N.
    x IN segment(a,b) ==> dist(x,a) < dist(a,b) /\ dist(x,b) < dist(a,b))`;;

let DIST_DECREASES_OPEN_SEGMENT = `!a b c x:real^N.
      x IN segment(a,b) ==> dist(c,x) < dist(c,a) \/ dist(c,x) < dist(c,b)`;;

let DIST_DECREASES_CLOSED_SEGMENT = `!a b c x:real^N.
      x IN segment[a,b] ==> dist(c,x) <= dist(c,a) \/ dist(c,x) <= dist(c,b)`;;

let DIST_IN_CLOSED_SEGMENT_2 = `!a b x y:real^N.
        x IN segment[a,b] /\ y IN segment[a,b] ==> dist(x,y) <= dist(a,b)`;;

(* ------------------------------------------------------------------------- *)
(* Connectedness.                                                            *)
(* ------------------------------------------------------------------------- *)

let connected = new_definition
  `connected s <=>
      ~(?e1 e2. open e1 /\ open e2 /\ s SUBSET (e1 UNION e2) /\
                (e1 INTER e2 INTER s = {}) /\
                ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

let CONNECTED_IN_EUCLIDEAN = `!s:real^N->bool. connected_in euclidean s <=> connected s`;;

let CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY = `!s:real^N->bool.
       connected_space(subtopology euclidean s) <=> connected s`;;

let CONNECTED_CLOSED = `!s:real^N->bool.
        connected s <=>
        ~(?e1 e2. closed e1 /\ closed e2 /\ s SUBSET (e1 UNION e2) /\
                  (e1 INTER e2 INTER s = {}) /\
                  ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

let CONNECTED_OPEN_IN = `!s. connected s <=>
           ~(?e1 e2.
                 open_in (subtopology euclidean s) e1 /\
                 open_in (subtopology euclidean s) e2 /\
                 s SUBSET e1 UNION e2 /\
                 e1 INTER e2 = {} /\
                 ~(e1 = {}) /\
                 ~(e2 = {}))`;;

let CONNECTED_OPEN_IN_EQ = `!s. connected s <=>
           ~(?e1 e2.
                 open_in (subtopology euclidean s) e1 /\
                 open_in (subtopology euclidean s) e2 /\
                 e1 UNION e2 = s /\ e1 INTER e2 = {} /\
                 ~(e1 = {}) /\ ~(e2 = {}))`;;

let CONNECTED_CLOSED_IN = `!s. connected s <=>
           ~(?e1 e2.
                 closed_in (subtopology euclidean s) e1 /\
                 closed_in (subtopology euclidean s) e2 /\
                 s SUBSET e1 UNION e2 /\
                 e1 INTER e2 = {} /\
                 ~(e1 = {}) /\
                 ~(e2 = {}))`;;

let CONNECTED_CLOSED_IN_EQ = `!s. connected s <=>
           ~(?e1 e2.
                 closed_in (subtopology euclidean s) e1 /\
                 closed_in (subtopology euclidean s) e2 /\
                 e1 UNION e2 = s /\ e1 INTER e2 = {} /\
                 ~(e1 = {}) /\ ~(e2 = {}))`;;

let CONNECTED_CLOPEN = `!s. connected s <=>
        !t. open_in (subtopology euclidean s) t /\
            closed_in (subtopology euclidean s) t ==> t = {} \/ t = s`;;

let CONNECTED_CLOSED_SET = `!s:real^N->bool.
        closed s
        ==> (connected s <=>
             ~(?e1 e2. closed e1 /\ closed e2 /\ ~(e1 = {}) /\ ~(e2 = {}) /\
                       e1 UNION e2 = s /\ e1 INTER e2 = {}))`;;

let CONNECTED_OPEN_SET = `!s:real^N->bool.
        open s
        ==> (connected s <=>
             ~(?e1 e2. open e1 /\ open e2 /\ ~(e1 = {}) /\ ~(e2 = {}) /\
                       e1 UNION e2 = s /\ e1 INTER e2 = {}))`;;

let CONNECTED_IFF_CONNECTABLE_POINTS = `!s:real^N->bool.
        connected s <=>
        !a b. a IN s /\ b IN s
              ==> ?t. connected t /\ t SUBSET s /\ a IN t /\ b IN t`;;

let CONNECTED_EMPTY = `connected {}`;;

let CONNECTED_SING = `!a. connected{a}`;;

let CONNECTED_SEGMENT = `(!a b:real^N. connected(segment[a,b])) /\
   (!a b:real^N. connected(segment(a,b)))`;;

let CONNECTED_UNIV = `connected(:real^N)`;;

let CLOPEN = `!s. closed s /\ open s <=> s = {} \/ s = (:real^N)`;;

let CONNECTED_UNIONS = `!P:(real^N->bool)->bool.
        (!s. s IN P ==> connected s) /\ ~(INTERS P = {})
        ==> connected(UNIONS P)`;;

let CONNECTED_UNION = `!s t:real^N->bool.
        connected s /\ connected t /\ ~(s INTER t = {})
        ==> connected (s UNION t)`;;

let CONNECTED_DIFF_OPEN_FROM_CLOSED = `!s t u:real^N->bool.
        s SUBSET t /\ t SUBSET u /\
        open s /\ closed t /\ connected u /\ connected(t DIFF s)
        ==> connected(u DIFF s)`;;

let CONNECTED_DISJOINT_UNIONS_OPEN_UNIQUE = `!f:(real^N->bool)->bool f'.
         pairwise DISJOINT f /\ pairwise DISJOINT f' /\
        (!s. s IN f ==> open s /\ connected s /\ ~(s = {})) /\
        (!s. s IN f' ==> open s /\ connected s /\ ~(s = {})) /\
        UNIONS f = UNIONS f'
        ==> f = f'`;;

let CONNECTED_FROM_CLOSED_UNION_AND_INTER_LOCAL = `!u s t:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        connected(s UNION t) /\ connected(s INTER t)
        ==> connected s /\ connected t`;;

let CONNECTED_FROM_OPEN_UNION_AND_INTER_LOCAL = `!u s t:real^N->bool.
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t /\
        connected(s UNION t) /\ connected(s INTER t)
        ==> connected s /\ connected t`;;

let CONNECTED_FROM_CLOSED_UNION_AND_INTER = `!s t:real^N->bool.
        closed s /\ closed t /\ connected(s UNION t) /\ connected(s INTER t)
        ==> connected s /\ connected t`;;

let CONNECTED_FROM_OPEN_UNION_AND_INTER = `!s t:real^N->bool.
        open s /\ open t /\ connected(s UNION t) /\ connected(s INTER t)
        ==> connected s /\ connected t`;;

(* ------------------------------------------------------------------------- *)
(* Sort of induction principle for connected sets.                           *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_INDUCTION = `!P Q s:real^N->bool.
        connected s /\
        (!t a. open_in (subtopology euclidean s) t /\ a IN t
               ==> ?z. z IN t /\ P z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x y. x IN t /\ y IN t /\ P x /\ P y /\ Q x ==> Q y)
        ==> !a b. a IN s /\ b IN s /\ P a /\ P b /\ Q a ==> Q b`;;

let CONNECTED_EQUIVALENCE_RELATION_GEN = `!P R s:real^N->bool.
        connected s /\
        (!x y. R x y ==> R y x) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!t a. open_in (subtopology euclidean s) t /\ a IN t
               ==> ?z. z IN t /\ P z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x y. x IN t /\ y IN t /\ P x /\ P y ==> R x y)
        ==> !a b. a IN s /\ b IN s /\ P a /\ P b ==> R a b`;;

let CONNECTED_INDUCTION_SIMPLE = `!P s:real^N->bool.
        connected s /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x y. x IN t /\ y IN t /\ P x ==> P y)
        ==> !a b. a IN s /\ b IN s /\ P a ==> P b`;;

let CONNECTED_EQUIVALENCE_RELATION = `!R s:real^N->bool.
        connected s /\
        (!x y. R x y ==> R y x) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x. x IN t ==> R a x)
        ==> !a b. a IN s /\ b IN s ==> R a b`;;

let LOCALLY_CONSTANT_IMP_CONSTANT = `!f:real^N->A s.
        connected s /\
        (!x. x IN s
             ==> ?u. open_in (subtopology euclidean s) u /\ x IN u /\
                     !x'. x' IN u ==> f x' = f x)
        ==> ?c. !x. x IN s ==> f x = c`;;

(* ------------------------------------------------------------------------- *)
(* Limit points.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("limit_point_of",(12,"right"));;

let limit_point_of = new_definition
 `x limit_point_of s <=>
        !t. x IN t /\ open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;

let EUCLIDEAN_DERIVED_SET_OF_IFF_LIMIT_POINT_OF = `!s. euclidean derived_set_of s = {x:real^N | x limit_point_of s}`;;

let LIMIT_POINT_IN_DERIVED_SET = `!s x:real^N. x limit_point_of s <=> x IN euclidean derived_set_of s`;;

let LIMPT_SUBSET = `!x s t. x limit_point_of s /\ s SUBSET t ==> x limit_point_of t`;;

let LIMPT_APPROACHABLE = `!x s. x limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) < e`;;

let LIMPT_APPROACHABLE_LE = `!x s. x limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) <= e`;;

let DISCRETE_SET = `!s t:real^N->bool.
        {x | x IN t /\ x limit_point_of s} = {} <=>
        !x. x IN t
            ==> ?e. &0 < e /\ !y. y IN s /\ ~(y = x) ==> e <= norm(y - x)`;;

let CLOSED_LIMPT = `!s. closed s <=> !x. x limit_point_of s ==> x IN s`;;

let LIMPT_EMPTY = `!x. ~(x limit_point_of {})`;;

let NO_LIMIT_POINT_IMP_CLOSED = `!s. ~(?x. x limit_point_of s) ==> closed s`;;

let CLOSED_POSITIVE_ORTHANT = `closed {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> &0 <= x$i}`;;

let FINITE_SET_AVOID = `!a:real^N s. FINITE s
                ==> ?d. &0 < d /\ !x. x IN s /\ ~(x = a) ==> d <= dist(a,x)`;;

let LIMIT_POINT_FINITE = `!s a. FINITE s ==> ~(a limit_point_of s)`;;

let LIMPT_SING = `!x y:real^N. ~(x limit_point_of {y})`;;

let LIMIT_POINT_UNION = `!s t x:real^N. x limit_point_of (s UNION t) <=>
                  x limit_point_of s \/ x limit_point_of t`;;

let LIMPT_INSERT = `!s x y:real^N. x limit_point_of (y INSERT s) <=> x limit_point_of s`;;

let LIMPT_DELETE = `!s a x:real^N. x limit_point_of (s DELETE a) <=> x limit_point_of s`;;

let LIMIT_POINT_UNIONS = `!f x:real^N.
      FINITE f
      ==> (x limit_point_of (UNIONS f) <=> ?s. s IN f /\ x limit_point_of s)`;;

let LIMPT_OF_LIMPTS = `!x:real^N s.
     x limit_point_of {y | y limit_point_of s} ==> x limit_point_of s`;;

let CLOSED_LIMPTS = `!s. closed {x:real^N | x limit_point_of s}`;;

let DISCRETE_IMP_CLOSED = `!s:real^N->bool e.
        &0 < e /\
        (!x y. x IN s /\ y IN s /\ norm(y - x) < e ==> y = x)
        ==> closed s`;;

let LIMPT_OF_UNIV = `!x. x limit_point_of (:real^N)`;;

let LIMPT_OF_OPEN_IN = `!s t x:real^N.
        open_in (subtopology euclidean s) t /\ x limit_point_of s /\ x IN t
        ==> x limit_point_of t`;;

let LIMPT_OF_OPEN = `!s x:real^N. open s /\ x IN s ==> x limit_point_of s`;;

let OPEN_IN_SING = `!s a. open_in (subtopology euclidean s) {a} <=>
         a IN s /\ ~(a limit_point_of s)`;;

let CLOSED_SING = `!a:real^N. closed {a}`;;

let CLOSED_IN_SING = `!u x:real^N. closed_in (subtopology euclidean u) {x} <=> x IN u`;;

let CLOSED_IN_INSERT = `!u s a:real^N.
        closed_in (subtopology euclidean u) s /\ a IN u
        ==> closed_in (subtopology euclidean u) (a INSERT s)`;;

let LIMIT_POINT_OF_LOCAL_IMP = `!u s t x:real^N.
        s SUBSET u /\ x limit_point_of s /\
        x IN t /\ open_in (subtopology euclidean u) t
        ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;

let LIMIT_POINT_OF_LOCAL = `!u s x:real^N.
        s SUBSET u /\ x IN u
        ==> (x limit_point_of s <=>
             !t. x IN t /\ open_in (subtopology euclidean u) t
                 ==> ?y. ~(y = x) /\ y IN s /\ y IN t)`;;

(* ------------------------------------------------------------------------- *)
(* Interior of a set.                                                        *)
(* ------------------------------------------------------------------------- *)

let interior = new_definition
  `interior s = {x | ?t. open t /\ x IN t /\ t SUBSET s}`;;

let EUCLIDEAN_INTERIOR_OF = `!s:real^N->bool. euclidean interior_of s = interior s`;;

let INTERIOR_EQ = `!s. (interior s = s) <=> open s`;;

let INTERIOR_OPEN = `!s. open s ==> (interior s = s)`;;

let INTERIOR_EMPTY = `interior {} = {}`;;

let INTERIOR_UNIV = `interior(:real^N) = (:real^N)`;;

let OPEN_INTERIOR = `!s. open(interior s)`;;

let INTERIOR_INTERIOR = `!s. interior(interior s) = interior s`;;

let INTERIOR_SUBSET = `!s. (interior s) SUBSET s`;;

let SUBSET_INTERIOR_EQ = `!s:real^N->bool. s SUBSET interior s <=> open s`;;

let SUBSET_INTERIOR = `!s t. s SUBSET t ==> (interior s) SUBSET (interior t)`;;

let INTERIOR_MAXIMAL = `!s t. t SUBSET s /\ open t ==> t SUBSET (interior s)`;;

let INTERIOR_MAXIMAL_EQ = `!s t:real^N->bool. open s ==> (s SUBSET interior t <=> s SUBSET t)`;;

let INTERIOR_UNIQUE = `!s t. t SUBSET s /\ open t /\ (!t'. t' SUBSET s /\ open t' ==> t' SUBSET t)
         ==> (interior s = t)`;;

let INTERIOR_EQ_UNIV = `!s. interior s = (:real^N) <=> s = (:real^N)`;;

let IN_INTERIOR = `!x s. x IN interior s <=> ?e. &0 < e /\ ball(x,e) SUBSET s`;;

let INTERIOR_INTER = `!s t:real^N->bool. interior(s INTER t) = interior s INTER interior t`;;

let INTERIOR_FINITE_INTERS = `!s:(real^N->bool)->bool.
        FINITE s ==> interior(INTERS s) = INTERS(IMAGE interior s)`;;

let INTERIOR_INTERS_SUBSET = `!f. interior(INTERS f) SUBSET INTERS (IMAGE interior f)`;;

let UNION_INTERIOR_SUBSET = `!s t:real^N->bool.
        interior s UNION interior t SUBSET interior(s UNION t)`;;

let INTERIOR_EQ_EMPTY = `!s:real^N->bool. interior s = {} <=> !t. open t /\ t SUBSET s ==> t = {}`;;

let INTERIOR_EQ_EMPTY_ALT = `!s:real^N->bool.
        interior s = {} <=>
        !t. open t /\ ~(t = {}) ==> ~(t DIFF s = {})`;;

let INTERIOR_LIMIT_POINT = `!s x:real^N. x IN interior s ==> x limit_point_of s`;;

let INTERIOR_SING = `!a:real^N. interior {a} = {}`;;

let INTERIOR_CLOSED_UNION_EMPTY_INTERIOR = `!s t:real^N->bool.
        closed(s) /\ interior(t) = {}
        ==> interior(s UNION t) = interior(s)`;;

let INTERIOR_UNION_EQ_EMPTY = `!s t:real^N->bool.
        closed s \/ closed t
        ==> (interior(s UNION t) = {} <=>
             interior s = {} /\ interior t = {})`;;

let INTERIOR_UNIONS_OPEN_SUBSETS = `!s:real^N->bool. UNIONS {t | open t /\ t SUBSET s} = interior s`;;

(* ------------------------------------------------------------------------- *)
(* Closure of a set.                                                         *)
(* ------------------------------------------------------------------------- *)

let closure = new_definition
  `closure s = s UNION {x | x limit_point_of s}`;;

let EUCLIDEAN_CLOSURE_OF = `!s:real^N->bool. euclidean closure_of s = closure s`;;

let CLOSURE_APPROACHABLE = `!x s. x IN closure(s) <=> !e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e`;;

let CLOSURE_NONEMPTY_OPEN_INTER = `!s x:real^N. x IN closure s <=> !t. x IN t /\ open t ==> ~(s INTER t = {})`;;

let CLOSURE_INTERIOR = `!s:real^N->bool. closure s = UNIV DIFF (interior (UNIV DIFF s))`;;

let INTERIOR_CLOSURE = `!s:real^N->bool. interior s = UNIV DIFF (closure (UNIV DIFF s))`;;

let CLOSED_CLOSURE = `!s. closed(closure s)`;;

let CLOSURE_HULL = `!s. closure s = closed hull s`;;

let CLOSURE_EQ = `!s. (closure s = s) <=> closed s`;;

let CLOSURE_CLOSED = `!s. closed s ==> (closure s = s)`;;

let CLOSURE_CLOSURE = `!s. closure(closure s) = closure s`;;

let CLOSURE_SUBSET = `!s. s SUBSET (closure s)`;;

let CLOSURE_INC = `!s x:real^N. x IN s ==> x IN closure s`;;

let SUBSET_CLOSURE = `!s t. s SUBSET t ==> (closure s) SUBSET (closure t)`;;

let CLOSURE_UNION = `!s t:real^N->bool. closure(s UNION t) = closure s UNION closure t`;;

let CLOSURE_UNIONS_SUBSET = `!(f:(real^N->bool)->bool).
        UNIONS {closure s | s IN f} SUBSET closure(UNIONS f)`;;

let CLOSURE_INTER_SUBSET = `!s t. closure(s INTER t) SUBSET closure(s) INTER closure(t)`;;

let CLOSURE_INTERS_SUBSET = `!f. closure(INTERS f) SUBSET INTERS(IMAGE closure f)`;;

let CLOSURE_MINIMAL = `!s t. s SUBSET t /\ closed t ==> (closure s) SUBSET t`;;

let CLOSURE_MINIMAL_EQ = `!s t:real^N->bool. closed t ==> (closure s SUBSET t <=> s SUBSET t)`;;

let CLOSURE_UNIQUE = `!s t. s SUBSET t /\ closed t /\
         (!t'. s SUBSET t' /\ closed t' ==> t SUBSET t')
         ==> closure s = t`;;

let CLOSURE_EMPTY = `closure {} = {}`;;

let CLOSURE_UNIV = `closure(:real^N) = (:real^N)`;;

let LIMPT_OF_OPEN_CLOSURE = `!s x:real^N. open s /\ x IN closure s ==> x limit_point_of s`;;

let CLOSURE_UNIONS = `!f. FINITE f ==> closure(UNIONS f) = UNIONS {closure s | s IN f}`;;

let CLOSURE_EQ_EMPTY = `!s. closure s = {} <=> s = {}`;;

let CLOSURE_SUBSET_EQ = `!s:real^N->bool. closure s SUBSET s <=> closed s`;;

let OPEN_INTER_CLOSURE_EQ_EMPTY = `!s t:real^N->bool.
        open s ==> (s INTER (closure t) = {} <=> s INTER t = {})`;;

let CLOSURE_MINIMAL_LOCAL = `!s t u:real^N->bool.
        closed_in (subtopology euclidean s) u /\ t SUBSET u
        ==> s INTER closure t SUBSET u`;;

let CLOSURE_OPEN_IN_INTER_CLOSURE = `!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\ t SUBSET u
        ==> closure(s INTER closure t) = closure(s INTER t)`;;

let OPEN_IN_INTER_CLOSURE_EQ_EMPTY = `!u s t:real^N->bool.
        open_in (subtopology euclidean u) s /\ t SUBSET u
        ==> (s INTER closure t = {} <=> s INTER t = {})`;;

let CLOSURE_OPEN_INTER_CLOSURE = `!s t:real^N->bool.
        open s ==> closure(s INTER closure t) = closure(s INTER t)`;;

let OPEN_INTER_CLOSURE_SUBSET = `!s t:real^N->bool.
        open s ==> (s INTER (closure t)) SUBSET closure(s INTER t)`;;

let OPEN_INTER_CLOSURE_EQ = `!s t:real^N->bool.
        open s ==> s INTER closure t = s INTER closure(s INTER t)`;;

let CLOSURE_OPEN_INTER_SUPERSET = `!s t:real^N->bool.
        open s /\ s SUBSET closure t ==> closure(s INTER t) = closure s`;;

let CLOSURE_COMPLEMENT = `!s:real^N->bool. closure(UNIV DIFF s) = UNIV DIFF interior(s)`;;

let INTERIOR_COMPLEMENT = `!s:real^N->bool. interior(UNIV DIFF s) = UNIV DIFF closure(s)`;;

let CLOSURE_LOCALLY_FINITE_UNIONS = `!f:(real^N->bool)->bool.
        locally_finite_in euclidean f
        ==> closure(UNIONS f) = UNIONS {closure s | s IN f}`;;

let CONNECTED_INTERMEDIATE_CLOSURE = `!s t:real^N->bool.
        connected s /\ s SUBSET t /\ t SUBSET closure s ==> connected t`;;

let CONNECTED_CLOSURE = `!s:real^N->bool. connected s ==> connected(closure s)`;;

let CONNECTED_UNION_STRONG = `!s t:real^N->bool.
        connected s /\ connected t /\ ~(closure s INTER t = {})
        ==> connected(s UNION t)`;;

let CONNECTED_INSERT = `!s a:real^N. connected s
                ==> (connected(a INSERT s) <=> s = {} \/ a IN closure s)`;;

let CONNECTED_INSERT_LIMPT = `!s a:real^N. connected s /\ a limit_point_of s ==> connected(a INSERT s)`;;

let INTERIOR_DIFF = `!s t. interior(s DIFF t) = interior(s) DIFF closure(t)`;;

let LIMPT_OF_CLOSURE = `!x:real^N s. x limit_point_of closure s <=> x limit_point_of s`;;

let PERFECT_FROM_CLOSURE = `!s:real^N->bool.
        (!x. x IN closure s ==> x limit_point_of closure s)
        ==> !x. x IN s ==> x limit_point_of s`;;

let DENSE_IMP_PERFECT = `!s. closure s = (:real^N) ==> !x. x IN s ==> x limit_point_of s`;;

let CLOSED_IN_LIMPT = `!s t. closed_in (subtopology euclidean t) s <=>
         s SUBSET t /\ !x:real^N. x limit_point_of s /\ x IN t ==> x IN s`;;

let CLOSED_IN_INTER_CLOSURE = `!s t:real^N->bool.
        closed_in (subtopology euclidean s) t <=> s INTER closure t = t`;;

let INTERIOR_CLOSURE_IDEMP = `!s:real^N->bool.
        interior(closure(interior(closure s))) = interior(closure s)`;;

let CLOSURE_INTERIOR_IDEMP = `!s:real^N->bool.
        closure(interior(closure(interior s))) = closure(interior s)`;;

let NOWHERE_DENSE_UNION = `!s t:real^N->bool.
        interior(closure(s UNION t)) = {} <=>
        interior(closure s) = {} /\ interior(closure t) = {}`;;

let NOWHERE_DENSE = `!s:real^N->bool.
        interior(closure s) = {} <=>
        !t. open t /\ ~(t = {})
            ==> ?u. open u /\ ~(u = {}) /\ u SUBSET t /\ u INTER s = {}`;;

let INTERIOR_CLOSURE_INTER_OPEN = `!s t:real^N->bool.
        open s /\ open t
        ==> interior(closure(s INTER t)) =
            interior(closure s) INTER interior(closure t)`;;

let CLOSURE_INTERIOR_UNION_CLOSED = `!s t:real^N->bool.
        closed s /\ closed t
        ==> closure(interior(s UNION t)) =
            closure(interior s) UNION closure(interior t)`;;

let REGULAR_OPEN_INTER = `!s t:real^N->bool.
        interior(closure s) = s /\ interior(closure t) = t
        ==> interior(closure(s INTER t)) = s INTER t`;;

let REGULAR_CLOSED_UNION = `!s t:real^N->bool.
        closure(interior s) = s /\ closure(interior t) = t
        ==> closure(interior(s UNION t)) = s UNION t`;;

let REGULAR_CLOSED_UNIONS = `!f:(real^N->bool)->bool.
        FINITE f /\ (!t. t IN f ==> closure(interior t) = t)
        ==> closure(interior(UNIONS f)) = UNIONS f`;;

let DIFF_CLOSURE_SUBSET = `!s t:real^N->bool. closure(s) DIFF closure t SUBSET closure(s DIFF t)`;;

let DENSE_OPEN_INTER = `!s t u:real^N->bool.
        (open_in (subtopology euclidean u) s /\ t SUBSET u \/
         open_in (subtopology euclidean u) t /\ s SUBSET u)
        ==> (u SUBSET closure (s INTER t) <=>
             u SUBSET closure s /\ u SUBSET closure t)`;;

let DENSE_OPEN_INTERS = `!g s:real^N->bool.
         FINITE g /\
         (!t. t IN g
              ==> open_in (subtopology euclidean s) t /\ s SUBSET closure t)
         ==> s SUBSET closure (INTERS g)`;;

let SEPARATION_CLOSED_IN_UNION = `!s t:real^N->bool.
        s INTER closure t = {} /\ t INTER closure s = {} <=>
        DISJOINT s t /\
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t`;;

let SEPARATION_OPEN_IN_UNION = `!s t:real^N->bool.
        s INTER closure t = {} /\ t INTER closure s = {} <=>
        DISJOINT s t /\
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t`;;

let CONNECTED_SEPARATION = `(!s:real^N->bool.
        connected s <=>
        ~(?c1 c2. c1 UNION c2 = s /\ ~(c1 = {}) /\ ~(c2 = {}) /\
                  c1 INTER closure c2 = {} /\ c2 INTER closure c1 = {}))`
and CONNECTED_SEPARATION_ALT = `(!s:real^N->bool.
        connected s <=>
        ~(?c1 c2.
            s SUBSET c1 UNION c2 /\ ~(c1 INTER s = {}) /\ ~(c2 INTER s = {}) /\
            c1 INTER closure c2 = {} /\ c2 INTER closure c1 = {}))`;;

(* ------------------------------------------------------------------------- *)
(* Frontier (aka boundary).                                                  *)
(* ------------------------------------------------------------------------- *)

let frontier = new_definition
  `frontier s = (closure s) DIFF (interior s)`;;

let EUCLIDEAN_FRONTIER_OF = `!s:real^N->bool. euclidean frontier_of s = frontier s`;;

let FRONTIER_CLOSED = `!s. closed(frontier s)`;;

let FRONTIER_CLOSURES = `!s:real^N->bool. frontier s = (closure s) INTER (closure(UNIV DIFF s))`;;

let FRONTIER_OPEN_STRADDLE_INTER = `!s u:real^N->bool.
        open u /\ ~(u INTER frontier s = {})
        ==> ~(u INTER s = {}) /\ ~(u DIFF s = {})`;;

let FRONTIER_UNION_INTERIOR = `!s:real^N->bool. frontier s UNION interior s = closure s`;;

let FRONTIER_STRADDLE = `!a:real^N s.
     a IN frontier s <=>
        !e. &0 < e ==> (?x. x IN s /\ dist(a,x) < e) /\
                       (?x. ~(x IN s) /\ dist(a,x) < e)`;;

let FRONTIER_SUBSET_CLOSED = `!s. closed s ==> (frontier s) SUBSET s`;;

let FRONTIER_EMPTY = `frontier {} = {}`;;

let FRONTIER_UNIV = `frontier(:real^N) = {}`;;

let FRONTIER_SUBSET_EQ = `!s:real^N->bool. (frontier s) SUBSET s <=> closed s`;;

let FRONTIER_COMPLEMENT = `!s:real^N->bool. frontier(UNIV DIFF s) = frontier s`;;

let FRONTIER_DISJOINT_EQ = `!s. (frontier s) INTER s = {} <=> open s`;;

let FRONTIER_INTER = `!s t:real^N->bool.
        frontier(s INTER t) =
        closure(s INTER t) INTER (frontier s UNION frontier t)`;;

let FRONTIER_INTER_SUBSET = `!s t. frontier(s INTER t) SUBSET frontier(s) UNION frontier(t)`;;

let FRONTIER_INTER_CLOSED = `!s t:real^N->bool.
        closed s /\ closed t
        ==> frontier(s INTER t) = frontier s INTER t UNION s INTER frontier t`;;

let FRONTIER_UNION_SUBSET = `!s t:real^N->bool. frontier(s UNION t) SUBSET frontier s UNION frontier t`;;

let FRONTIER_INTERIORS = `!s. frontier s = (:real^N) DIFF interior(s) DIFF interior((:real^N) DIFF s)`;;

let FRONTIER_FRONTIER_SUBSET = `!s:real^N->bool. frontier(frontier s) SUBSET frontier s`;;

let INTERIOR_FRONTIER = `!s:real^N->bool.
        interior(frontier s) = interior(closure s) DIFF closure(interior s)`;;

let THIN_FRONTIER_SUBSET = `!s:real^N->bool.
        interior(frontier s) = {} <=>
        interior(closure s) SUBSET closure(interior s)`;;

let THIN_FRONTIER_CIC = `!s:real^N->bool.
        interior(frontier s) = {} <=>
        closure(interior(closure s)) = closure(interior s)`;;

let THIN_FRONTIER_ICI = `!s:real^N->bool.
        interior(frontier s) = {} <=>
        interior(closure(interior s)) = interior(closure s)`;;

let INTERIOR_FRONTIER_EMPTY = `!s:real^N->bool. open s \/ closed s ==> interior(frontier s) = {}`;;

let FRONTIER_FRONTIER = `!s:real^N->bool. open s \/ closed s ==> frontier(frontier s) = frontier s`;;

let FRONTIER_FRONTIER_FRONTIER = `!s:real^N->bool. frontier(frontier(frontier s)) = frontier(frontier s)`;;

let REGULAR_CLOSURE_INTERIOR = `!s:real^N->bool.
        s SUBSET closure(interior s) <=>
        closure(interior s) = closure s`;;

let REGULAR_INTERIOR_CLOSURE = `!s:real^N->bool.
        interior(closure s) SUBSET s <=>
        interior(closure s) = interior s`;;

let REGULAR_CLOSED = `!s:real^N->bool.
      closure(interior s) = s <=>
      closed s /\ s SUBSET closure(interior s)`;;

let REGULAR_OPEN = `!s:real^N->bool.
        interior(closure s) = s <=>
        open s /\ interior(closure s) SUBSET s`;;

let REGULAR_CLOSURE_IMP_THIN_FRONTIER = `!s:real^N->bool.
        s SUBSET closure(interior s) ==> interior(frontier s) = {}`;;

let REGULAR_INTERIOR_IMP_THIN_FRONTIER = `!s:real^N->bool.
        interior(closure s) SUBSET s ==> interior(frontier s) = {}`;;

let UNION_FRONTIER = `!s t:real^N->bool.
        frontier(s) UNION frontier(t) =
        frontier(s UNION t) UNION
        frontier(s INTER t) UNION
        frontier(s) INTER frontier(t)`;;

let CONNECTED_INTER_FRONTIER = `!s t:real^N->bool.
        connected s /\ ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER frontier t = {})`;;

let FRONTIER_NOT_EMPTY = `!s. ~(s = {}) /\ ~(s = (:real^N)) ==> ~(frontier s = {})`;;

let FRONTIER_EQ_EMPTY = `!s. frontier s = {} <=> s = {} \/ s = (:real^N)`;;

let INTERIOR_CLOSED_EQ_EMPTY_AS_FRONTIER = `!s:real^N->bool.
        closed s /\ interior s = {} <=> ?t. open t /\ s = frontier t`;;

let FRONTIER_UNION = `!s t:real^N->bool.
        closure s INTER closure t = {}
        ==> frontier(s UNION t) = frontier(s) UNION frontier(t)`;;

let CLOSURE_UNION_FRONTIER = `!s:real^N->bool. closure s = s UNION frontier s`;;

let FRONTIER_INTERIOR_SUBSET = `!s:real^N->bool. frontier(interior s) SUBSET frontier s`;;

let FRONTIER_CLOSURE_SUBSET = `!s:real^N->bool. frontier(closure s) SUBSET frontier s`;;

let SET_DIFF_FRONTIER = `!s:real^N->bool. s DIFF frontier s = interior s`;;

let FRONTIER_INTER_SUBSET_INTER = `!s t:real^N->bool.
        frontier(s INTER t) SUBSET closure s INTER frontier t UNION
                                   frontier s INTER closure t`;;

let COMMON_FRONTIER_DOMAINS = `!s t:real^N->bool.
      open s /\ open t /\ connected s /\ connected t /\ frontier s = frontier t
      ==> s = t \/ DISJOINT s t`;;

let FRONTIER_OPEN_UNION = `!s t:real^N->bool.
        open s /\ open t /\ DISJOINT s t
        ==> frontier(s UNION t) = frontier s UNION frontier t`;;

let FRONTIER_OPEN_UNIONS = `!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> open s) /\ pairwise DISJOINT f
        ==> frontier(UNIONS f) = UNIONS {frontier s | s IN f}`;;

let CONNECTED_CLOSURE_FROM_FRONTIER = `!s:real^N->bool. connected(frontier s) ==> connected(closure s)`;;

(* ------------------------------------------------------------------------- *)
(* Useful nets in Euclidean space.                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("in_direction",(14,"right"));;

let at = new_definition
  `at a = atpointof euclidean a`;;

let at_infinity = new_definition
  `at_infinity = mk_net({{x | b <= norm x} | b IN (:real)},{})`;;

let at_posinfinity = new_definition
  `at_posinfinity = mk_net({{x | a <= x} | a IN (:real)},{})`;;

let at_neginfinity = new_definition
  `at_neginfinity = mk_net({{x | x <= a} | a IN (:real)},{})`;;

let in_direction = new_definition
  `a in_direction v = (at a) within {b | ?c. &0 <= c /\ (b - a = c % v)}`;;

let AT = `!a:real^N.
     netfilter (at a) = { u | open u /\ a IN u}`;;

let NETLIMIT_AT = `!a. netlimit(at a) = a`;;

let NETLIMIT_WITHIN = `!a:real^N s. netlimit (at a within s) = a`;;

let AT_INFINITY = `netfilter at_infinity = {{x:real^N | b <= norm x} | b IN (:real)}`
and NETLIMITS_AT_INFINITY = `netlimits at_infinity = ({}:real^N->bool)`;;

let AT_POSINFINITY = `netfilter at_posinfinity = {{x | a <= x} | a IN (:real)}`
and NETLIMITS_AT_POSINFINITY = `netlimits at_posinfinity = {}`;;

let AT_NEGINFINITY = `netfilter at_neginfinity = {{x | x <= a} | a IN (:real)}`
and NETLIMITS_AT_NEGINFINITY = `netlimits at_neginfinity = {}`;;

let WITHIN_UNIV = `!x:real^N. at x within UNIV = at x`;;

(* ------------------------------------------------------------------------- *)
(* The "eventually" property in Euclidean space.                             *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_WITHIN = `!s a:real^M p.
     eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d ==> p(x)`;;

let EVENTUALLY_WITHIN_LE = `!s a:real^M p.
     eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d ==> p(x)`;;

let EVENTUALLY_WITHIN_TOPOLOGICAL = `!P s a:real^N.
        eventually P (at a within s) <=>
        ?t. open t /\ a IN t /\
            !x. x IN s INTER (t DELETE a) ==> P x`;;

let TRIVIAL_LIMIT_WITHIN = `!a:real^N. trivial_limit (at a within s) <=> ~(a limit_point_of s)`;;

let LIM_WITHIN_CLOSED_TRIVIAL = `!a s. closed s /\ ~(a IN s) ==> trivial_limit (at a within s)`;;

let EVENTUALLY_AT = `!a p. eventually p (at a) <=>
         ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d ==> p(x)`;;

let EVENTUALLY_AT_TOPOLOGICAL = `!P a:real^N.
        eventually P (at a) <=>
        ?t. open t /\ a IN t /\ !x. x IN t DELETE a ==> P x`;;

let TRIVIAL_LIMIT_AT = `!a. ~(trivial_limit (at a))`;;

let EVENTUALLY_HAPPENS_AT = `!P a:real^N. eventually P (at a) ==> ?b. ~(b = a) /\ P b`;;

let EVENTUALLY_AT_INFINITY = `!p. eventually p at_infinity <=> ?b. !x. norm(x) >= b ==> p x`;;

let EVENTUALLY_AT_INFINITY_WITHIN = `!p s:real^N->bool.
        eventually p (at_infinity within s) <=>
        ?b. !x. x IN s /\ norm(x) >= b ==> p x`;;

let EVENTUALLY_AT_INFINITY_POS = `!p:real^N->bool.
        eventually p at_infinity <=> ?b. &0 < b /\ !x. norm x >= b ==> p x`;;

let TRIVIAL_LIMIT_AT_INFINITY = `~(trivial_limit at_infinity)`;;

let EVENTUALLY_AT_POSINFINITY = `!p. eventually p at_posinfinity <=> ?b. !x. x >= b ==> p x`;;

let TRIVIAL_LIMIT_AT_POSINFINITY = `~(trivial_limit at_posinfinity)`;;

let EVENTUALLY_AT_NEGINFINITY = `!p. eventually p at_neginfinity <=> ?b. !x. x <= b ==> p x`;;

let TRIVIAL_LIMIT_AT_NEGINFINITY = `~(trivial_limit at_neginfinity)`;;

let EVENTUALLY_AT_ZERO = `!P:real^N->bool a.
        eventually P (at a) <=> eventually (\x. P(a + x)) (at (vec 0))`;;

let EVENTUALLY_AT_WITHIN = `!P s a:real^N.
        eventually P (at a) ==> eventually P (at a within s)`;;

let EVENTUALLY_WITHIN_ZERO = `!P:real^N->bool s a.
        eventually P (at a within s) <=>
        eventually (\x. P(a + x)) (at (vec 0) within IMAGE (\x. x - a) s)`;;

let IN_INTERIOR_EVENTUALLY = `!s a:real^N. a IN interior s <=> a IN s /\ eventually (\x. x IN s) (at a)`;;

let EVENTUALLY_WITHIN_INTERIOR = `!p s x:real^N.
        x IN interior s
        ==> (eventually p (at x within s) <=> eventually p (at x))`;;

let EVENTUALLY_IN_OPEN = `!s a:real^N. open s /\ a IN s ==> eventually (\x. x IN s) (at a)`;;

let EVENTUALLY_WITHIN_OPEN = `!f a:real^M s.
        a IN s /\ open s
        ==> (eventually P (at a within s) <=> eventually P (at a))`;;

let EVENTUALLY_WITHIN_OPEN_IN = `!P a s t:real^N->bool.
         a IN t /\ open_in (subtopology euclidean s) t
         ==> (eventually P (at a within t) <=> eventually P (at a within s))`;;

let EVENTUALLY_WITHIN_INTERIOR_LOCAL = `!P a s t u:real^N->bool.
        a IN u /\ u SUBSET t /\ t SUBSET s /\
        open_in (subtopology euclidean s) u
        ==> (eventually P (at a within t) <=> eventually P (at a within s))`;;

let EVENTUALLY_SCALABLE_PROPERTY = `!P. (!c x:real^N. &0 <= c /\ P x ==> P(c % x)) /\
       eventually P (at (vec 0))
       ==> !x. P x`;;

let EVENTUALLY_SCALABLE_PROPERTY_EQ = `!P. (!c x:real^N. &0 <= c /\ P x ==> P(c % x))
       ==> (eventually P (at (vec 0)) <=> !x. P x)`;;

let ONORM_LE_EVENTUALLY = `!f:real^M->real^N b.
        linear f
        ==> (onorm f <= b <=>
             eventually (\y. norm(f y) <= b * norm y) (at (vec 0)))`;;

let EVENTUALLY_WITHIN_REFLECT = `!P s a:real^N.
        eventually (\x. P(--x)) (at(--a) within IMAGE (--) s) <=>
        eventually P (at a within s)`;;

let EVENTUALLY_AT_REFLECT = `!P a:real^N.
        eventually (\x. P(--x)) (at(--a)) <=> eventually P (at a)`;;

let EVENTUALLY_WITHIN_DELETE = `!P:real^N->bool s a.
        eventually P (at a within (s DELETE a)) <=>
        eventually P (at a within s)`;;

(* ------------------------------------------------------------------------- *)
(* Limits, defined as vacuously true when the limit is trivial.              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(12,"right"));;

let tendsto = new_definition
  `(f --> l) net <=> !e. &0 < e ==> eventually (\x. dist(f(x),l) < e) net`;;

let LIMIT_EUCLIDEAN = `!f:A->real^N x net. limit euclidean f x net <=> (f --> x) net`;;

let lim = new_definition
 `lim net f = @l. (f --> l) net`;;

let TENDSTO_ALT = `!f:A->real^N l net.
     (f --> l) net <=>
     (!s. open s /\ l IN s ==> eventually (\x. f x IN s) net)`;;

let TENDSTO_ALT_WITHIN = `!net f:A->real^N l u.
        l IN u /\ eventually (\x. f x IN u) net
        ==> ((f --> l) net <=>
             !s. open_in (subtopology euclidean u) s /\ l IN s
                 ==> eventually (\x. f x IN s) net)`;;

let LIM_EVENTUALLY_IN_OPEN_IN = `!net f:A->real^N l u s.
        l IN s /\ open_in (subtopology euclidean u) s /\
        eventually (\x. f x IN u) net /\ (f --> l) net
        ==> eventually (\x. f x IN s) net`;;

let LIM_EVENTUALLY_IN_OPEN = `!net f:A->real^N l s.
        open s /\ (f --> l) net /\ l IN s ==> eventually (\x. f x IN s) net`;;

let LIM_TRIVIAL = `!net (f:A->real^N) l. trivial_limit net ==> (f --> l) net`;;

let LIM_WITHIN_REFLECT = `!f:real^M->real^N l a s.
        ((\x. f(--x)) --> l) (at(--a) within IMAGE (--) s) <=>
        (f --> l) (at a within s)`;;

let LIM_AT_REFLECT = `!f:real^M->real^N l a.
        ((\x. f(--x)) --> l) (at(--a)) <=> (f --> l) (at a)`;;

let LIM_WITHIN_ZERO = `!f:real^M->real^N l s a.
        (f --> l) (at a within s) <=>
        ((\x. f(a + x)) --> l) (at(vec 0) within IMAGE (\x. x - a) s)`;;

let LIM_WITHIN_DELETE = `!f:real^M->real^N l s a.
        (f --> l) (at a within (s DELETE a)) <=>
        (f --> l) (at a within s)`;;

let LIM_COMPONENTWISE_REAL = `!net f:A->real^N l.
        (f --> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> limit euclideanreal (\x. f x$i) (l$i) net`;;

let LIM_COMPONENTWISE_LIFT = `!net f:A->real^N.
        (f --> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift((f x)$i)) --> lift(l$i)) net`;;

let LIM_EQ_DROP = `!(net:A net) f l:real^1.
        (f --> l) net <=> limit euclideanreal (drop o f) (drop l) net`;;

let LIM_EQ_LIFT = `!(net:A net) f l.
        limit euclideanreal f l net <=> ((lift o f) --> lift l) net`;;

(* ------------------------------------------------------------------------- *)
(* Show that they yield usual definitions in the various cases.              *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_LE = `!f:real^M->real^N l a s.
        (f --> l)(at a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d
                                   ==> dist(f(x),l) < e`;;

let LIM_WITHIN = `!f:real^M->real^N l a s.
      (f --> l) (at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d
                    ==> dist(f(x),l) < e`;;

let LIM_AT_LE = `!f l a. (f --> l) (at a) <=>
           !e. &0 < e
               ==> ?d. &0 < d /\
                       !x. &0 < dist(x,a) /\ dist(x,a) <= d
                           ==> dist (f x,l) < e`;;

let LIM_AT = `!f l:real^N a:real^M.
      (f --> l) (at a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d
                          ==> dist(f(x),l) < e`;;

let LIM_AT_INFINITY = `!f l. (f --> l) at_infinity <=>
               !e. &0 < e ==> ?b. !x. norm(x) >= b ==> dist(f(x),l) < e`;;

let LIM_AT_INFINITY_POS = `!f l. (f --> l) at_infinity <=>
         !e. &0 < e ==> ?b. &0 < b /\ !x. norm x >= b ==> dist(f x,l) < e`;;

let LIM_AT_POSINFINITY = `!f l. (f --> l) at_posinfinity <=>
               !e. &0 < e ==> ?b. !x. x >= b ==> dist(f(x),l) < e`;;

let LIM_AT_NEGINFINITY = `!f l. (f --> l) at_neginfinity <=>
               !e. &0 < e ==> ?b. !x. x <= b ==> dist(f(x),l) < e`;;

let LIM_AT_INFINITY_WITHIN = `!f:real^M->real^N l s.
        (f --> l) (at_infinity within s) <=>
        !e. &0 < e ==> ?b. !x. x IN s /\ norm(x) >= b ==> dist(f(x),l) < e`;;

let LIM_AT_INFINITY_WITHIN_POS = `!f:real^M->real^N l s.
        (f --> l) (at_infinity within s) <=>
        !e. &0 < e
            ==> ?b. &0 < b /\ !x. x IN s /\ norm(x) >= b ==> dist(f(x),l) < e`;;

let LIM_SEQUENTIALLY = `!s l. (s --> l) sequentially <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> dist(s(n),l) < e`;;

let LIM_EVENTUALLY = `!net f l. eventually (\x. f x = l) net ==> (f --> l) net`;;

let LIM_POSINFINITY_SEQUENTIALLY = `!f l. (f --> l) at_posinfinity ==> ((\n. f(&n)) --> l) sequentially`;;

let LIM_INFINITY_POSINFINITY_LIFT = `!f l:real^N. (f --> l) at_infinity ==> ((f o lift) --> l) at_posinfinity`;;

let LIM_SELF_WITHIN = `!f:real^M->real^N s a.
        (f --> f a) (at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                     !x. x IN s /\ dist(x,a) < d ==> dist(f x,f a) < e`;;

let LIM_SELF_AT = `!f:real^M->real^N a.
        (f --> f a) (at a) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                     !x. dist(x,a) < d ==> dist(f x,f a) < e`;;

let LIM_SUBSEQUENCE = `!s r l. (!m n. m < n ==> r(m) < r(n)) /\ (s --> l) sequentially
           ==> (s o r --> l) sequentially`;;

let SEQUENTIAL_LIMIT_URYSOHN = `!s l:real^N.
        (s --> l) sequentially <=>
        !r. (!m n. m < n ==> r m < r n)
            ==> ?q:num->num.
                    (!m n. m < n ==> q m < q n) /\
                    ((s o r o q) --> l) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* The expected monotonicity property.                                       *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_EMPTY = `!f l x. (f --> l) (at x within {})`;;

let LIM_WITHIN_SUBSET = `!f l a s.
    (f --> l) (at a within s) /\ t SUBSET s ==> (f --> l) (at a within t)`;;

let LIM_UNION = `!f x l s t.
        (f --> l) (at x within s) /\ (f --> l) (at x within t)
        ==> (f --> l) (at x within (s UNION t))`;;

let LIM_UNION_UNIV = `!f x l s t.
        (f --> l) (at x within s) /\ (f --> l) (at x within t) /\
        s UNION t = (:real^N)
        ==> (f --> l) (at x)`;;

(* ------------------------------------------------------------------------- *)
(* Composition of limits.                                                    *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPOSE_WITHIN = `!net f:A->real^N g:real^N->real^P s y z.
    (f --> y) net /\
    eventually (\w. f w IN s /\ (f w = y ==> g y = z)) net /\
    (g --> z) (at y within s)
    ==> ((g o f) --> z) net`;;

let LIM_COMPOSE_AT = `!net f:A->real^N g:real^N->real^P y z.
    (f --> y) net /\
    eventually (\w. f w = y ==> g y = z) net /\
    (g --> z) (at y)
    ==> ((g o f) --> z) net`;;

(* ------------------------------------------------------------------------- *)
(* Interrelations between restricted and unrestricted limits.                *)
(* ------------------------------------------------------------------------- *)

let LIM_AT_WITHIN = `!f l a s. (f --> l)(at a) ==> (f --> l)(at a within s)`;;

let LIM_WITHIN_OPEN = `!f l a:real^M s.
     a IN s /\ open s ==> ((f --> l) (at a within s) <=> (f --> l) (at a))`;;

let LIM_WITHIN_OPEN_IN = `!f:real^M->real^N l a s t.

        a IN t /\ open_in (subtopology euclidean s) t
        ==> ((f --> l) (at a within t) <=> (f --> l) (at a within s))`;;

(* ------------------------------------------------------------------------- *)
(* More limit point characterizations.                                       *)
(* ------------------------------------------------------------------------- *)

let LIMPT_SEQUENTIAL = `(!x:real^N s.
        x limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\ (f --> x) sequentially)`
and LIMPT_SEQUENTIAL_INJ = `(!x:real^N s.
        x limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\
            (!m n. f m = f n <=> m = n) /\
            (f --> x) sequentially)`
and LIMPT_SEQUENTIAL_DECREASING = `(!x:real^N s.
        x limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\
            (!m n. m < n ==> dist(f n,x) < dist(f m,x)) /\
            (f --> x) sequentially)`;;

let LIMPT_INFINITE_OPEN = `(!s x:real^N.
        x limit_point_of s <=> !t. x IN t /\ open t ==> INFINITE(s INTER t))`
and LIMPT_INFINITE_BALL = `(!s x:real^N.
        x limit_point_of s <=> !e. &0 < e ==> INFINITE(s INTER ball(x,e)))`
and LIMPT_INFINITE_CBALL = `(!s x:real^N.
        x limit_point_of s <=> !e. &0 < e ==> INFINITE(s INTER cball(x,e)))`;;

let INFINITE_OPEN_IN = `!u s:real^N->bool.
      open_in (subtopology euclidean u) s /\ (?x. x IN s /\ x limit_point_of u)
      ==> INFINITE s`;;

(* ------------------------------------------------------------------------- *)
(* Condensation points.                                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("condensation_point_of",(12,"right"));;

let condensation_point_of = new_definition
 `x condensation_point_of s <=>
        !t. x IN t /\ open t ==> ~COUNTABLE(s INTER t)`;;

let CONDENSATION_POINT_OF_SUBSET = `!x:real^N s t.
        x condensation_point_of s /\ s SUBSET t ==> x condensation_point_of t`;;

let CONDENSATION_POINT_IMP_LIMPT = `!x s. x condensation_point_of s ==> x limit_point_of s`;;

let CONDENSATION_POINT_INFINITE_BALL = `(!s x:real^N.
        x condensation_point_of s <=>
        !e. &0 < e ==> ~COUNTABLE(s INTER ball(x,e)))`
and CONDENSATION_POINT_INFINITE_CBALL = `(!s x:real^N.
        x condensation_point_of s <=>
        !e. &0 < e ==> ~COUNTABLE(s INTER cball(x,e)))`;;

let CONDENSATION_POINT_ALT = `!x:real^N s.
        x condensation_point_of s <=>
        !t. COUNTABLE t ==> x limit_point_of (s DIFF t)`;;

(* ------------------------------------------------------------------------- *)
(* Basic arithmetical combining theorems for limits.                         *)
(* ------------------------------------------------------------------------- *)

let LIM_LINEAR = `!net:(A)net h f l.
        (f --> l) net /\ linear h ==> ((\x. h(f x)) --> h l) net`;;

let LIM_CONST = `!net a:real^N. ((\x. a) --> a) net`;;

let LIM_CMUL = `!f l c. (f --> l) net ==> ((\x. c % f x) --> c % l) net`;;

let LIM_CMUL_EQ = `!net f l c.
        ~(c = &0) ==> (((\x. c % f x) --> c % l) net <=> (f --> l) net)`;;

let LIM_NEG = `!net f l:real^N. (f --> l) net ==> ((\x. --(f x)) --> --l) net`;;

let LIM_NEG_EQ = `!net f l:real^N. ((\x. --(f x)) --> --l) net <=> (f --> l) net`;;

let LIM_ADD = `!net:(A)net f g l m.
    (f --> l) net /\ (g --> m) net ==> ((\x. f(x) + g(x)) --> l + m) net`;;

let LIM_ABS = `!net:(A)net f:A->real^N l.
     (f --> l) net
     ==> ((\x. lambda i. (abs(f(x)$i))) --> (lambda i. abs(l$i)):real^N) net`;;

let LIM_LIFT_ABS_COMPONENT = `!net:(A)net f:A->real^N l k.
     (f --> l) net ==> ((\x. lift(abs(f(x)$k))) --> lift(abs(l$k))) net`;;

let LIM_SUB = `!net:(A)net f g l m.
    (f --> l) net /\ (g --> m) net ==> ((\x. f(x) - g(x)) --> l - m) net`;;

let LIM_MAX = `!net:(A)net f g l:real^N m:real^N.
    (f --> l) net /\ (g --> m) net
    ==> ((\x. lambda i. max (f(x)$i) (g(x)$i))
         --> (lambda i. max (l$i) (m$i)):real^N) net`;;

let LIM_MIN = `!net:(A)net f g l:real^N m:real^N.
    (f --> l) net /\ (g --> m) net
    ==> ((\x. lambda i. min (f(x)$i) (g(x)$i))
         --> (lambda i. min (l$i) (m$i)):real^N) net`;;

let LIM_NORM = `!net f:A->real^N l.
        (f --> l) net ==> ((\x. lift(norm(f x))) --> lift(norm l)) net`;;

let LIM_NULL = `!net f l. (f --> l) net <=> ((\x. f(x) - l) --> vec 0) net`;;

let LIM_NULL_NORM = `!net f. (f --> vec 0) net <=> ((\x. lift(norm(f x))) --> vec 0) net`;;

let LIM_NULL_CMUL_EQ = `!net f:A->real^N c.
        ((\x. c % f x) --> vec 0) net <=> c = &0 \/ (f --> vec 0) net`;;

let LIM_NULL_CMUL = `!net f c. (f --> vec 0) net ==> ((\x. c % f x) --> vec 0) net`;;

let LIM_NULL_VMUL_EQ = `!net:A net c v:real^N.
        ((\x. c x % v) --> vec 0) net <=>
        v = vec 0 \/ ((\x. lift(c x)) --> vec 0) net`;;

let LIM_NULL_VMUL = `!net:A net c v:real^N.
    ((\x. lift(c x)) --> vec 0) net ==> ((\x. c x % v) --> vec 0) net`;;

let LIM_NULL_NEG = `!net f:A->real^N. ((\x. --(f x)) --> vec 0) net <=> (f --> vec 0) net`;;

let LIM_NULL_ADD = `!net f g:A->real^N.
        (f --> vec 0) net /\ (g --> vec 0) net
        ==> ((\x. f x + g x) --> vec 0) net`;;

let LIM_NULL_SUB = `!net f g:A->real^N.
        (f --> vec 0) net /\ (g --> vec 0) net
        ==> ((\x. f x - g x) --> vec 0) net`;;

let LIM_NULL_COMPARISON = `!net f g. eventually (\x. norm(f x) <= g x) net /\
             ((\x. lift(g x)) --> vec 0) net
             ==> (f --> vec 0) net`;;

let LIM_COMPONENT = `!net f i l:real^N.
     (f --> l) net ==> ((\a. lift(f(a)$i)) --> lift(l$i)) net`;;

let LIM_TRANSFORM_BOUND = `!f g. eventually (\n. norm(f n) <= norm(g n)) net /\ (g --> vec 0) net
         ==> (f --> vec 0) net`;;

let LIM_NULL_CMUL_BOUNDED = `!f g:A->real^N B.
        eventually (\a. g a = vec 0 \/ abs(f a) <= B) net /\
        (g --> vec 0) net
        ==> ((\n. f n % g n) --> vec 0) net`;;

let LIM_NULL_VMUL_BOUNDED = `!f g:A->real^N B.
        ((lift o f) --> vec 0) net /\
        eventually (\a. f a = &0 \/ norm(g a) <= B) net
        ==> ((\n. f n % g n) --> vec 0) net`;;

let LIM_VSUM = `!net f:A->B->real^N l s.
        FINITE s /\ (!i. i IN s ==> ((f i) --> (l i)) net)
        ==> ((\x. vsum s (\i. f i x)) --> vsum s l) net`;;

let LIM_NULL_VSUM = `!net f:A->B->real^N s.
        FINITE s /\ (!a. a IN s ==> ((\x. f x a) --> vec 0) net)
        ==> ((\x. vsum s (f x)) --> vec 0) net`;;

(* ------------------------------------------------------------------------- *)
(* Deducing things about the limit from the elements.                        *)
(* ------------------------------------------------------------------------- *)

let LIM_IN_CLOSED_SET = `!net f:A->real^N s l.
        closed s /\ eventually (\x. f(x) IN s) net /\
        ~(trivial_limit net) /\ (f --> l) net
        ==> l IN s`;;

(* ------------------------------------------------------------------------- *)
(* Need to prove closed(cball(x,e)) before deducing this as a corollary.     *)
(* ------------------------------------------------------------------------- *)

let LIM_NORM_UBOUND = `!net:(A)net f (l:real^N) b.
      ~(trivial_limit net) /\
      (f --> l) net /\
      eventually (\x. norm(f x) <= b) net
      ==> norm(l) <= b`;;

let LIM_NORM_LBOUND = `!net:(A)net f (l:real^N) b.
      ~(trivial_limit net) /\ (f --> l) net /\
      eventually (\x. b <= norm(f x)) net
      ==> b <= norm(l)`;;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of the limit, when nontrivial.                                 *)
(* ------------------------------------------------------------------------- *)

let LIM_UNIQUE = `!net:(A)net f l:real^N l'.
      ~(trivial_limit net) /\ (f --> l) net /\ (f --> l') net ==> (l = l')`;;

let TENDSTO_LIM = `!net f l. ~(trivial_limit net) /\ (f --> l) net ==> lim net f = l`;;

let LIM_CONST_EQ = `!net:(A net) c d:real^N.
        ((\x. c) --> d) net <=> trivial_limit net \/ c = d`;;

(* ------------------------------------------------------------------------- *)
(* These are special for limits out of the same vector space.                *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_ID = `!a s. ((\x. x) --> a) (at a within s)`;;

let LIM_AT_ID = `!a. ((\x. x) --> a) (at a)`;;

let LIM_AT_ZERO = `!f:real^M->real^N l a.
        (f --> l) (at a) <=> ((\x. f(a + x)) --> l) (at(vec 0))`;;

(* ------------------------------------------------------------------------- *)
(* Some unwieldy but occasionally useful theorems about uniform limits.      *)
(* ------------------------------------------------------------------------- *)

let UNIFORM_LIM_ADD = `!net:(A)net P f g l m.
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm((f n x + g n x) - (l n + m n)) < e)
                     net`;;

let UNIFORM_LIM_SUB = `!net:(A)net P f g l m.
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm((f n x - g n x) - (l n - m n)) < e)
                     net`;;

(* ------------------------------------------------------------------------- *)
(* Limit under bilinear function, uniform version first.                     *)
(* ------------------------------------------------------------------------- *)

let UNIFORM_LIM_BILINEAR = `!net:(A)net P (h:real^M->real^N->real^P) f g l m b1 b2.
        bilinear h /\
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        eventually (\x. !n. P n ==> norm(m n) <= b2) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(h (f n x) (g n x) - h (l n) (m n)) < e)
                     net`;;

let LIM_BILINEAR = `!net:(A)net (h:real^M->real^N->real^P) f g l m.
        (f --> l) net /\ (g --> m) net /\ bilinear h
        ==> ((\x. h (f x) (g x)) --> (h l m)) net`;;

let BILINEAR_EPSILON_DELTA = `!bop:real^M->real^N->real^P a b e.
        bilinear bop /\ &0 < e
        ==> ?d. &0 < d /\
                !x y. norm(x - a) < d /\ norm(y - b) < d
                      ==> norm(bop x y - bop a b) < e`;;

(* ------------------------------------------------------------------------- *)
(* Transformation of limit.                                                  *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM = `!net f g l.
     ((\x. f x - g x) --> vec 0) net /\ (f --> l) net ==> (g --> l) net`;;

let LIM_TRANSFORM_EVENTUALLY = `!net f g l.
        eventually (\x. f x = g x) net /\ (f --> l) net ==> (g --> l) net`;;

let LIM_TRANSFORM_WITHIN = `!f g x s d.
        &0 < d /\
        (!x'. x' IN s /\ &0 < dist(x',x) /\ dist(x',x) < d ==> f(x') = g(x')) /\
        (f --> l) (at x within s)
        ==> (g --> l) (at x within s)`;;

let LIM_TRANSFORM_AT = `!f g x d.
        &0 < d /\
        (!x'. &0 < dist(x',x) /\ dist(x',x) < d ==> f(x') = g(x')) /\
        (f --> l) (at x)
        ==> (g --> l) (at x)`;;

let LIM_TRANSFORM_EQ = `!net f:A->real^N g l.
     ((\x. f x - g x) --> vec 0) net ==> ((f --> l) net <=> (g --> l) net)`;;

let LIM_TRANSFORM_WITHIN_SET = `!f l a s t.
        eventually (\x. x IN s <=> x IN t) (at a)
        ==> ((f --> l) (at a within s) <=> (f --> l) (at a within t))`;;

let LIM_TRANSFORM_WITHIN_SET_IMP = `!f l a s t.
        eventually (\x. x IN t ==> x IN s) (at a) /\ (f --> l) (at a within s)
        ==> (f --> l) (at a within t)`;;

(* ------------------------------------------------------------------------- *)
(* Common case assuming being away from some crucial point like 0.           *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM_AWAY_WITHIN = `!f:real^M->real^N g a b s.
        ~(a = b) /\
        (!x. x IN s /\ ~(x = a) /\ ~(x = b) ==> f(x) = g(x)) /\
        (f --> l) (at a within s)
        ==> (g --> l) (at a within s)`;;

let LIM_TRANSFORM_AWAY_AT = `!f:real^M->real^N g a b.
        ~(a = b) /\
        (!x. ~(x = a) /\ ~(x = b) ==> f(x) = g(x)) /\
        (f --> l) (at a)
        ==> (g --> l) (at a)`;;

(* ------------------------------------------------------------------------- *)
(* Alternatively, within an open set.                                        *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM_WITHIN_OPEN = `!f g:real^M->real^N s a l.
        open s /\ a IN s /\
        (!x. x IN s /\ ~(x = a) ==> f x = g x) /\
        (f --> l) (at a)
        ==> (g --> l) (at a)`;;

let LIM_TRANSFORM_WITHIN_OPEN_IN = `!f g:real^M->real^N s t a l.
        open_in (subtopology euclidean t) s /\ a IN s /\
        (!x. x IN s /\ ~(x = a) ==> f x = g x) /\
        (f --> l) (at a within t)
        ==> (g --> l) (at a within t)`;;

(* ------------------------------------------------------------------------- *)
(* Limit of linear functions is itself linear.                               *)
(* ------------------------------------------------------------------------- *)

let LINEAR_LIMIT = `!net:A net f g:real^M->real^N.
        ~trivial_limit net /\
        eventually (\i. linear(f i)) net /\
        (!x. ((\i. f i x) --> g x) net)
        ==> linear g`;;

let LINEAR_SEQUENTIAL_LIMIT = `!f g:real^M->real^N.
        eventually (\n. linear(f n)) sequentially /\
        (!x. ((\n. f n x) --> g x) sequentially)
        ==> linear g`;;

(* ------------------------------------------------------------------------- *)
(* Another quite common idiom of an explicit conditional in a sequence.      *)
(* ------------------------------------------------------------------------- *)

let LIM_CASES_FINITE_SEQUENTIALLY = `!f g l. FINITE {n | P n}
           ==> (((\n. if P n then f n else g n) --> l) sequentially <=>
                (g --> l) sequentially)`;;

let LIM_CASES_COFINITE_SEQUENTIALLY = `!f g l. FINITE {n | ~P n}
           ==> (((\n. if P n then f n else g n) --> l) sequentially <=>
                (f --> l) sequentially)`;;

let LIM_CASES_SEQUENTIALLY = `!f g l m. (((\n. if m <= n then f n else g n) --> l) sequentially <=>
              (f --> l) sequentially) /\
             (((\n. if m < n then f n else g n) --> l) sequentially <=>
              (f --> l) sequentially) /\
             (((\n. if n <= m then f n else g n) --> l) sequentially <=>
              (g --> l) sequentially) /\
             (((\n. if n < m then f n else g n) --> l) sequentially <=>
              (g --> l) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* A congruence rule allowing us to transform limits assuming not at point.  *)
(* ------------------------------------------------------------------------- *)

let LIM_CONG_WITHIN = `(!x. x IN s /\ ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (at a within s) <=> ((g --> l) (at a within s)))`;;

let LIM_CONG_AT = `(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (at a) <=> ((g --> l) (at a)))`;;

extend_basic_congs [LIM_CONG_WITHIN; LIM_CONG_AT];;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas on closure and set of possible sequential limits.           *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_SEQUENTIAL = `!s l:real^N.
     l IN closure(s) <=> ?x. (!n. x(n) IN s) /\ (x --> l) sequentially`;;

let CLOSED_CONTAINS_SEQUENTIAL_LIMIT = `!s x l:real^N.
        closed s /\ (!n. x n IN s) /\ (x --> l) sequentially ==> l IN s`;;

let CLOSED_SEQUENTIAL_LIMITS = `!s. closed s <=>
       !x l. (!n. x(n) IN s) /\ (x --> l) sequentially ==> l IN s`;;

let CLOSED_IN_SEQUENTIAL_LIMITS = `!u s:real^N->bool.
        closed_in (subtopology euclidean u) s <=>
        s SUBSET u /\
        !x l. (!n. x n IN s) /\ l IN u /\ (x --> l) sequentially
              ==> l IN s`;;

let CLOSED_APPROACHABLE = `!x s. closed s
         ==> ((!e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e) <=> x IN s)`;;

let IN_CLOSURE_DELETE = `!s x:real^N. x IN closure(s DELETE x) <=> x limit_point_of s`;;

let DENSE_LIMIT_POINTS = `!s. {x | x limit_point_of s} = (:real^N) <=> closure s = (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Some other lemmas about sequences.                                        *)
(* ------------------------------------------------------------------------- *)

let SEQ_OFFSET = `!f l k. (f --> l) sequentially ==> ((\i. f(i + k)) --> l) sequentially`;;

let SEQ_OFFSET_NEG = `!f l k. (f --> l) sequentially ==> ((\i. f(i - k)) --> l) sequentially`;;

let SEQ_OFFSET_REV = `!f l k. ((\i. f(i + k)) --> l) sequentially ==> (f --> l) sequentially`;;

let SEQ_OFFSET_EQ = `!k f l:real^N.
        ((\i. f (i + k)) --> l) sequentially <=> (f --> l) sequentially`;;

let CONVERGENT_OFFSET = `!f:num->real^N k.
     (?l. (f --> l) sequentially)
     ==> (?l. ((\i. f(i + k)) --> l) sequentially)`;;

let CONVERGENT_OFFSET_EQ = `!f:num->real^N k.
        (?l. ((\i. f(i + k)) --> l) sequentially) <=>
        (?l. (f --> l) sequentially)`;;

let CONVERGENT_OFFSET_REV = `!f:num->real^N k.
        (?l. ((\i. f(i + k)) --> l) sequentially)
        ==> (?l. (f --> l) sequentially)`;;

let SEQ_HARMONIC_OFFSET = `!a. ((\n. lift(inv(&n + a))) --> vec 0) sequentially`;;

let SEQ_HARMONIC = `((\n. lift(inv(&n))) --> vec 0) sequentially`;;

let SEQ_HARMONIC_RATIO = `!a b. ((\n. lift((&n + a) / (&n + b))) --> vec 1) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* More properties of closed balls.                                          *)
(* ------------------------------------------------------------------------- *)

let CLOSED_CBALL = `!x:real^N e. closed(cball(x,e))`;;

let CLOSURE_CBALL = `!a:real^N r. closure(cball(a,r)) = cball(a,r)`;;

let IN_INTERIOR_CBALL = `!x s. x IN interior s <=> ?e. &0 < e /\ cball(x,e) SUBSET s`;;

let LIMPT_BALL = `!x:real^N y e. y limit_point_of ball(x,e) <=> &0 < e /\ y IN cball(x,e)`;;

let CLOSURE_BALL = `!x:real^N e. &0 < e ==> (closure(ball(x,e)) = cball(x,e))`;;

let INTERIOR_BALL = `!a r. interior(ball(a,r)) = ball(a,r)`;;

let INTERIOR_CBALL = `!x:real^N e. interior(cball(x,e)) = ball(x,e)`;;

let FRONTIER_BALL = `!a e. &0 < e ==> frontier(ball(a,e)) = sphere(a,e)`;;

let FRONTIER_CBALL = `!a e. frontier(cball(a,e)) = sphere(a,e)`;;

let INTERIOR_SPHERE = `!a:real^N r. interior(sphere(a,r)) = {}`;;

let CBALL_EQ_EMPTY = `!x e. (cball(x,e) = {}) <=> e < &0`;;

let CBALL_EMPTY = `!x e. e < &0 ==> cball(x,e) = {}`;;

let CBALL_EQ_SING = `!x:real^N e. (cball(x,e) = {x}) <=> e = &0`;;

let CBALL_SING = `!x e. e = &0 ==> cball(x,e) = {x}`;;

let SPHERE_SING = `!x e. e = &0 ==> sphere(x,e) = {x}`;;

let SPHERE_EQ_SING = `!a:real^N r x. sphere(a,r) = {x} <=> x = a /\ r = &0`;;

let HAS_SIZE_SPHERE_1 = `!a:real^N r. sphere(a,r) HAS_SIZE 1 <=> r = &0`;;

let IMAGE_AFFINITY_CBALL = `!m c a:real^N r.
        IMAGE (\x. m % x + c) (cball(a,r)) =
        if &0 <= r \/ ~(m = &0) then cball(m % a + c,abs m * r) else {}`;;

let IMAGE_AFFINITY_BALL = `!m c a:real^N r.
        IMAGE (\x. m % x + c) (ball(a,r)) =
        if ~(m = &0) then ball(m % a + c,abs m * r)
        else if r <= &0 then {} else {c}`;;

let IMAGE_AFFINITY_SPHERE = `!m c a:real^N r.
        IMAGE (\x. m % x + c) (sphere(a,r)) =
        if &0 <= r \/ ~(m = &0) then sphere(m % a + c,abs m * r) else {}`;;

(* ------------------------------------------------------------------------- *)
(* For points in the interior, localization of limits makes no difference.   *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_WITHIN_INTERIOR_INTER = `!p s t x.
        x IN interior s
        ==> (eventually p (at x within s INTER t) <=>
             eventually p (at x within t))`;;

let LIM_WITHIN_INTERIOR_INTER = `!f l s x.
        x IN interior s
        ==> ((f --> l) (at x within s INTER t) <=> (f --> l) (at x within t))`;;

let LIM_WITHIN_INTERIOR = `!f l s x.
        x IN interior s
        ==> ((f --> l) (at x within s) <=> (f --> l) (at x))`;;

(* ------------------------------------------------------------------------- *)
(* A non-singleton connected set is perfect (i.e. has no isolated points).   *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_IMP_PERFECT = `!s x:real^N.
        connected s /\ ~(?a. s = {a}) /\ x IN s ==> x limit_point_of s`;;

let CONNECTED_IMP_PERFECT_CLOSED = `!s x. connected s /\ closed s /\ ~(?a. s = {a})
         ==> (x limit_point_of s <=> x IN s)`;;

let CONNECTED_LIMIT_POINTS_EQ_CLOSURE = `!s:real^N->bool.
        connected s /\ ~(?a. s = {a})
        ==> {x | x limit_point_of s} = closure s`;;

let CONNECTED_LIMIT_POINTS = `!s:real^N->bool. connected s ==> connected {x | x limit_point_of s}`;;

(* ------------------------------------------------------------------------- *)
(* Boundedness.                                                              *)
(* ------------------------------------------------------------------------- *)

let bounded = new_definition
  `bounded s <=> ?a. !x:real^N. x IN s ==> norm(x) <= a`;;

let MBOUNDED_EUCLIDEAN = `!s:real^N->bool. mbounded euclidean_metric s <=> bounded s`;;

let BOUNDED_EMPTY = `bounded {}`;;

let BOUNDED_SUBSET = `!s t. bounded t /\ s SUBSET t ==> bounded s`;;

let BOUNDED_INTERIOR = `!s:real^N->bool. bounded s ==> bounded(interior s)`;;

let BOUNDED_CLOSURE = `!s:real^N->bool. bounded s ==> bounded(closure s)`;;

let BOUNDED_CLOSURE_EQ = `!s:real^N->bool. bounded(closure s) <=> bounded s`;;

let BOUNDED_CBALL = `!x:real^N e. bounded(cball(x,e))`;;

let BOUNDED_BALL = `!x e. bounded(ball(x,e))`;;

let FINITE_IMP_BOUNDED = `!s:real^N->bool. FINITE s ==> bounded s`;;

let BOUNDED_NORM_IMAGE = `!s:real^N->bool.
        bounded s <=> bounded(IMAGE (lift o norm) s)`;;

let BOUNDED_UNION = `!s t. bounded (s UNION t) <=> bounded s /\ bounded t`;;

let BOUNDED_UNIONS = `!f. FINITE f /\ (!s. s IN f ==> bounded s) ==> bounded(UNIONS f)`;;

let BOUNDED_POS = `!s. bounded s <=> ?b. &0 < b /\ !x. x IN s ==> norm(x) <= b`;;

let BOUNDED_POS_LT = `!s. bounded s <=> ?b. &0 < b /\ !x. x IN s ==> norm(x) < b`;;

let BOUNDED_PAIRS = `!s:real^N->bool.
        bounded s <=> ?B. !x y. x IN s /\ y IN s ==> dist(x,y) <= B`;;

let BOUNDED_PAIRS_POS = `!s:real^N->bool.
        bounded s <=> ?B. &0 < B /\ !x y. x IN s /\ y IN s ==> dist(x,y) <= B`;;

let BOUNDED_INTER = `!s t. bounded s \/ bounded t ==> bounded (s INTER t)`;;

let BOUNDED_DIFF = `!s t. bounded s ==> bounded (s DIFF t)`;;

let BOUNDED_INSERT = `!x s. bounded(x INSERT s) <=> bounded s`;;

let BOUNDED_SING = `!a. bounded {a}`;;

let BOUNDED_DELETE = `!x:real^N s. bounded(s DELETE x) <=> bounded s`;;

let BOUNDED_INTERS = `!f:(real^N->bool)->bool.
        (?s:real^N->bool. s IN f /\ bounded s) ==> bounded(INTERS f)`;;

let NOT_BOUNDED_UNIV = `~(bounded (:real^N))`;;

let NOT_OPEN_SING = `!a:real^N. ~(open {a})`;;

let COBOUNDED_IMP_UNBOUNDED = `!s. bounded((:real^N) DIFF s) ==> ~bounded s`;;

let BOUNDED_LINEAR_IMAGE = `!f:real^M->real^N s. bounded s /\ linear f ==> bounded(IMAGE f s)`;;

let BOUNDED_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (bounded (IMAGE f s) <=> bounded s)`;;

add_linear_invariants [BOUNDED_LINEAR_IMAGE_EQ];;

let BOUNDED_SCALING = `!c s. bounded s ==> bounded (IMAGE (\x. c % x) s)`;;

let BOUNDED_NEGATIONS = `!s. bounded s ==> bounded (IMAGE (--) s)`;;

let BOUNDED_TRANSLATION = `!a:real^N s. bounded s ==> bounded (IMAGE (\x. a + x) s)`;;

let BOUNDED_TRANSLATION_EQ = `!a s. bounded (IMAGE (\x:real^N. a + x) s) <=> bounded s`;;

add_translation_invariants [BOUNDED_TRANSLATION_EQ];;

let BOUNDED_SCALING_EQ = `!s:real^N->bool c. bounded (IMAGE (\x. c % x) s) <=> c = &0 \/ bounded s`;;

let BOUNDED_AFFINITY_EQ = `!s m c:real^N.
        bounded (IMAGE (\x. m % x + c) s) <=> m = &0 \/ bounded s`;;

let BOUNDED_AFFINITY = `!s m c:real^N. bounded s ==> bounded (IMAGE (\x. m % x + c) s)`;;

let BOUNDED_DIFFS = `!s t:real^N->bool.
        bounded s /\ bounded t ==> bounded {x - y | x IN s /\ y IN t}`;;

let BOUNDED_SUMS = `!s t:real^N->bool.
        bounded s /\ bounded t ==> bounded {x + y | x IN s /\ y IN t}`;;

let BOUNDED_SUMS_IMAGE = `!f g t. bounded {f x | x IN t} /\ bounded {g x | x IN t}
           ==> bounded {f x + g x | x IN t}`;;

let BOUNDED_SUMS_IMAGES = `!f:A->B->real^N t s.
        FINITE s /\
        (!a. a IN s ==> bounded {f x a | x IN t})
        ==> bounded { vsum s (f x) | x IN t}`;;

let BOUNDED_SUBSET_BALL = `!s x:real^N. bounded(s) ==> ?r. &0 < r /\ s SUBSET ball(x,r)`;;

let BOUNDED_SUBSET_CBALL = `!s x:real^N. bounded(s) ==> ?r. &0 < r /\ s SUBSET cball(x,r)`;;

let UNBOUNDED_INTER_COBOUNDED = `!s t. ~bounded s /\ bounded((:real^N) DIFF t) ==> ~(s INTER t = {})`;;

let COBOUNDED_INTER_UNBOUNDED = `!s t. bounded((:real^N) DIFF s) /\ ~bounded t ==> ~(s INTER t = {})`;;

let SUBSPACE_BOUNDED_EQ_TRIVIAL = `!s:real^N->bool. subspace s ==> (bounded s <=> s = {vec 0})`;;

let BOUNDED_COMPONENTWISE = `!s:real^N->bool.
        bounded s <=> !i. 1 <= i /\ i <= dimindex(:N)
                          ==> bounded (IMAGE (\x. lift(x$i)) s)`;;

let BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC = `!s:real^N->bool. bounded s ==> ?a. s SUBSET interval(--a,a)`;;

let BOUNDED_SUBSET_OPEN_INTERVAL = `!s:real^N->bool. bounded s ==> ?a b. s SUBSET interval(a,b)`;;

let BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC = `!s:real^N->bool. bounded s ==> ?a. s SUBSET interval[--a,a]`;;

let BOUNDED_SUBSET_CLOSED_INTERVAL = `!s:real^N->bool. bounded s ==> ?a b. s SUBSET interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Some theorems on sups and infs using the notion "bounded".                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_LIFT = `!s. bounded(IMAGE lift s) <=>  ?a. !x. x IN s ==> abs(x) <= a`;;

let BOUNDED_HAS_SUP = `!s. bounded(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> x <= sup s) /\
           (!b. (!x. x IN s ==> x <= b) ==> sup s <= b)`;;

let SUP_INSERT = `!x s. bounded (IMAGE lift s)
         ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`;;

let BOUNDED_HAS_INF = `!s. bounded(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> inf s <= x) /\
           (!b. (!x. x IN s ==> b <= x) ==> b <= inf s)`;;

let INF_INSERT = `!x s. bounded (IMAGE lift s)
         ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`;;

(* ------------------------------------------------------------------------- *)
(* Subset and overlapping relations on balls.                                *)
(* ------------------------------------------------------------------------- *)

let SUBSET_BALLS = `(!a a':real^N r r'.
      ball(a,r) SUBSET ball(a',r') <=> dist(a,a') + r <= r' \/ r <= &0) /\
   (!a a':real^N r r'.
      ball(a,r) SUBSET cball(a',r') <=> dist(a,a') + r <= r' \/ r <= &0) /\
   (!a a':real^N r r'.
      cball(a,r) SUBSET ball(a',r') <=> dist(a,a') + r < r' \/ r < &0) /\
   (!a a':real^N r r'.
      cball(a,r) SUBSET cball(a',r') <=> dist(a,a') + r <= r' \/ r < &0)`;;

let INTER_BALLS_EQ_EMPTY = `(!a b:real^N r s. ball(a,r) INTER ball(b,s) = {} <=>
                     r <= &0 \/ s <= &0 \/ r + s <= dist(a,b)) /\
   (!a b:real^N r s. ball(a,r) INTER cball(b,s) = {} <=>
                     r <= &0 \/ s < &0 \/ r + s <= dist(a,b)) /\
   (!a b:real^N r s. cball(a,r) INTER ball(b,s) = {} <=>
                     r < &0 \/ s <= &0 \/ r + s <= dist(a,b)) /\
   (!a b:real^N r s. cball(a,r) INTER cball(b,s) = {} <=>
                     r < &0 \/ s < &0 \/ r + s < dist(a,b))`;;

(* ------------------------------------------------------------------------- *)
(* Compactness (the definition is the one based on convegent subsequences).  *)
(* ------------------------------------------------------------------------- *)

let compact = new_definition
  `compact s <=>
        !f:num->real^N.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) --> l) sequentially`;;

let COMPACT_IN_EUCLIDEAN = `!s:real^N->bool. compact_in euclidean s <=> compact s`;;

let COMPACT_SPACE_EUCLIDEAN_SUBTOPOLOGY = `!s:real^N->bool. compact_space (subtopology euclidean s) <=> compact s`;;

let COMPACT_IMP_CLOSED = `!s. compact s ==> closed s`;;

let COMPACT_IMP_BOUNDED = `!s. compact s ==> bounded s`;;

let COMPACT_INTERVAL = `!a b:real^N. compact(interval[a,b])`;;

let BOUNDED_CLOSED_IMP_COMPACT = `!s:real^N->bool. bounded s /\ closed s ==> compact s`;;

let COMPACT_EQ_BOUNDED_CLOSED = `!s:real^N->bool. compact s <=> bounded s /\ closed s`;;

let NOT_COMPACT_UNIV = `~compact (:real^N)`;;

let COMPACT_CLOSURE = `!s. compact(closure s) <=> bounded s`;;

let CLOSED_IN_COMPACT = `!s t:real^N->bool.
        compact s /\ closed_in (subtopology euclidean s) t
        ==> compact t`;;

let CLOSED_IN_COMPACT_EQ = `!s t. compact s
         ==> (closed_in (subtopology euclidean s) t <=>
              compact t /\ t SUBSET s)`;;

let COMPACT_EQ_HEINE_BOREL = `!s:real^N->bool.
        compact s <=>
           !f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`;;

let COMPACT_IMP_HEINE_BOREL = `!s. compact (s:real^N->bool)
       ==> !f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`;;

let COMPACT_EQ_BOLZANO_WEIERSTRASS = `!s:real^N->bool.
        compact s <=>
           !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t`;;

let BOLZANO_WEIERSTRASS_IMP_CLOSED = `!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t)
        ==> closed s`;;

let COMPACT_IMP_TOTALLY_BOUNDED = `!s:real^N->bool.
        compact s
        ==> !e. &0 < e ==> ?k. FINITE k /\ k SUBSET s /\
                               s SUBSET (UNIONS(IMAGE (\x. ball(x,e)) k))`;;

let HEINE_BOREL_LEMMA = `!s:real^N->bool.
      compact s
      ==> !t. s SUBSET (UNIONS t) /\ (!b. b IN t ==> open b)
              ==> ?e. &0 < e /\
                      !x. x IN s ==> ?b. b IN t /\ ball(x,e) SUBSET b`;;

let HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS = `!s:real^N->bool.
        (!f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
             ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f'))
        ==> !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t`;;

let BOLZANO_WEIERSTRASS_IMP_BOUNDED = `!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x limit_point_of t)
        ==> bounded s`;;

let COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY = `!s:real^N->bool.
        compact s <=>
        !f. (!t. t IN f ==> open_in(subtopology euclidean s) t) /\
            s SUBSET UNIONS f
            ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET UNIONS f'`;;

let COMPACT_EQ_HEINE_BOREL_GEN = `!c:real^N->bool.
        compact c <=>
        !f s. (!t. t IN f ==> open_in (subtopology euclidean s) t) /\
              c SUBSET UNIONS f
              ==> ?f'. f' SUBSET f /\ FINITE f' /\ c SUBSET UNIONS f'`;;

let BOUNDED_EQ_BOLZANO_WEIERSTRASS = `!s:real^N->bool.
        bounded s <=> !t. t SUBSET s /\ INFINITE t ==> ?x. x limit_point_of t`;;

let BOLZANO_WEIERSTRASS = `!s:real^N->bool. bounded s /\ INFINITE s ==> ?x. x limit_point_of s`;;

let BOUNDED_EQ_TOTALLY_BOUNDED = `!s:real^N->bool.
        bounded s <=>
        !e. &0 < e
            ==> ?k. FINITE k /\ k SUBSET s /\
                    s SUBSET (UNIONS(IMAGE (\x. ball(x,e)) k))`;;

(* ------------------------------------------------------------------------- *)
(* Convergence of bounded monotone sequences.                                *)
(* ------------------------------------------------------------------------- *)

let CONVERGENT_BOUNDED_MONOTONE_1 = `!s. bounded(IMAGE s (:num)) /\
       ((!n. drop(s n) <= drop(s(SUC n))) \/ (!n. drop(s(SUC n)) <= drop(s n)))
       ==> ?l. (s --> l) sequentially`;;

let CONVERGENT_BOUNDED_INCREASING_1 = `!s b. (!n. drop(s n) <= drop(s(SUC n))) /\ (!n. drop(s n) <= b)
         ==> ?l. (s --> l) sequentially`;;

let CONVERGENT_BOUNDED_DECREASING_1 = `!s b. (!n. drop(s(SUC n)) <= drop(s n)) /\ (!n. b <= drop(s n))
         ==> ?l. (s --> l) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Completeness.                                                             *)
(* ------------------------------------------------------------------------- *)

let cauchy = new_definition
  `cauchy (s:num->real^N) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> dist(s m,s n) < e`;;

let CAUCHY_IN_EUCLIDEAN = `!s:num->real^N. cauchy_in euclidean_metric s <=> cauchy s`;;

let complete = new_definition
  `complete s <=>
     !f:num->real^N. (!n. f n IN s) /\ cauchy f
                      ==> ?l. l IN s /\ (f --> l) sequentially`;;

let CAUCHY = `!s:num->real^N.
      cauchy s <=> !e. &0 < e ==> ?N. !n. n >= N ==> dist(s n,s N) < e`;;

let CAUCHY_SUBSEQUENCE = `!x:num->real^N r:num->num.
        (!m n. m < n ==> r m < r n) /\ cauchy x ==> cauchy (x o r)`;;

let CAUCHY_OFFSET = `!k x:num->real^N. cauchy (\i. x(i + k)) <=> cauchy x`;;

let CONVERGENT_IMP_CAUCHY = `!s l. (s --> l) sequentially ==> cauchy s`;;

let CAUCHY_IMP_BOUNDED = `!s:num->real^N. cauchy s ==> bounded {y | ?n. y = s n}`;;

let CAUCHY_CONVERGENT_SUBSEQUENCE = `!x:num->real^N r.
        cauchy x /\ (!m n. m < n ==> r m < r n) /\ ((x o r) --> l) sequentially
        ==> (x --> l) sequentially`;;

let COMPACT_IMP_COMPLETE = `!s:real^N->bool. compact s ==> complete s`;;

let COMPLETE_UNIV = `complete(:real^N)`;;

let COMPLETE_EQ_CLOSED = `!s:real^N->bool. complete s <=> closed s`;;

let CONVERGENT_EQ_CAUCHY = `!s. (?l. (s --> l) sequentially) <=> cauchy s`;;

let CONVERGENT_IMP_BOUNDED = `!s l. (s --> l) sequentially ==> bounded (IMAGE s (:num))`;;

let CONVERGENT_BOUNDED_MONOTONE_EQ = `!s. (!n. drop(s n) <= drop(s(SUC n))) \/ (!n. drop(s(SUC n)) <= drop(s n))
       ==> ((?l. (s --> l) sequentially) <=> bounded (IMAGE s (:num)))`;;

let MCOMPLETE_EUCLIDEAN = `mcomplete(euclidean_metric:(real^N)metric)`;;

let COMPLETELY_METRIZABLE_SPACE_EUCLIDEAN = `completely_metrizable_space euclidean`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type criteria for limits at a point.                               *)
(* ------------------------------------------------------------------------- *)

let CONVERGENT_EQ_ZERO_OSCILLATION = `!f:real^M->real^N a s.
        (?l. (f --> l) (at a within s)) <=>
        !e. &0 < e
            ==> ?u. open u /\ a IN u /\
                    !x y. x IN (s INTER u) DELETE a /\
                          y IN (s INTER u) DELETE a
                          ==> dist(f x,f y) < e`;;

let CONVERGENT_EQ_CAUCHY_WITHIN = `!f:real^M->real^N s a.
        (?l. (f --> l) (at a within s)) <=>
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !x x'. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d /\
                            x' IN s /\ &0 < dist(x',a) /\ dist(x',a) < d
                            ==> dist(f x,f x') < e)`;;

let CONVERGENT_EQ_CAUCHY_AT = `!f:real^M->real^N a.
        (?l. (f --> l) (at a)) <=>
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !x x'. &0 < dist(x,a) /\ dist(x,a) < d /\
                            &0 < dist(x',a) /\ dist(x',a) < d
                            ==> dist(f x,f x') < e)`;;

(* ------------------------------------------------------------------------- *)
(* Compactness properties (some orphaned lemmas no longer used here).        *)
(* ------------------------------------------------------------------------- *)

let SEQUENCE_INFINITE_LEMMA = `!f l. (!n. ~(f(n) = l)) /\ (f --> l) sequentially
         ==> INFINITE {y:real^N | ?n. y = f n}`;;

let LIMPT_OF_SEQUENCE_SUBSEQUENCE = `!f:num->real^N l.
        l limit_point_of (IMAGE f (:num))
        ==> ?r. (!m n. m < n ==> r(m) < r(n)) /\ ((f o r) --> l) sequentially`;;

let SEQUENCE_UNIQUE_LIMPT = `!f l l':real^N.
        (f --> l) sequentially /\ l' limit_point_of {y | ?n. y = f n}
        ==> l' = l`;;

let COMPACT_SEQUENCE_WITH_LIMIT_GEN = `!f l:real^N s.
        (f --> l) sequentially /\ s SUBSET IMAGE f (:num)
        ==> compact (l INSERT s)`;;

let COMPACT_SEQUENCE_WITH_LIMIT = `!f l:real^N.
        (f --> l) sequentially ==> compact (l INSERT IMAGE f (:num))`;;

let BOLZANO_WEIERSTRASS_CONTRAPOS = `!s t:real^N->bool.
        compact s /\ t SUBSET s /\
        (!x. x IN s ==> ~(x limit_point_of t))
        ==> FINITE t`;;

let DISCRETE_BOUNDED_IMP_FINITE = `!s:real^N->bool e.
        &0 < e /\
        (!x y. x IN s /\ y IN s /\ norm(y - x) < e ==> y = x) /\
        bounded s
        ==> FINITE s`;;

let FINITE_EQ_BOUNDED_DISCRETE = `!s:real^N->bool.
        FINITE s <=>
        bounded s /\
        ?r. &0 < r /\ !x y. x IN s /\ y IN s /\ norm (y - x) < r ==> x = y`;;

let DISCRETE_EQ_FINITE_BOUNDED = `!s:real^N->bool.
        bounded s ==> ({x | x limit_point_of s} = {} <=> FINITE s)`;;

let DISCRETE_EQ_FINITE_BOUNDED_CLOSED = `!s t:real^N->bool.
        closed s /\ bounded t /\ t SUBSET s
        ==> ({x | x IN s /\ x limit_point_of t} = {} <=> FINITE t)`;;

let DISCRETE_EQ_FINITE_COMPACT = `!s t:real^N->bool.
        compact s /\ t SUBSET s
        ==> ({x | x IN s /\ x limit_point_of t} = {} <=> FINITE t)`;;

let COMPACT_EMPTY = `compact {}`;;

let COMPACT_UNION = `!s t. compact s /\ compact t ==> compact (s UNION t)`;;

let COMPACT_INTER = `!s t. compact s /\ compact t ==> compact (s INTER t)`;;

let COMPACT_INTER_CLOSED = `!s t. compact s /\ closed t ==> compact (s INTER t)`;;

let CLOSED_INTER_COMPACT = `!s t. closed s /\ compact t ==> compact (s INTER t)`;;

let COMPACT_INTERS = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> compact s) /\ ~(f = {})
        ==> compact(INTERS f)`;;

let FINITE_IMP_CLOSED = `!s. FINITE s ==> closed s`;;

let FINITE_IMP_CLOSED_IN = `!s t. FINITE s /\ s SUBSET t ==> closed_in (subtopology euclidean t) s`;;

let FINITE_IMP_COMPACT = `!s. FINITE s ==> compact s`;;

let COMPACT_SING = `!a. compact {a}`;;

let COMPACT_INSERT = `!a s. compact s ==> compact(a INSERT s)`;;

let CLOSURE_SING = `!x:real^N. closure {x} = {x}`;;

let CLOSURE_INSERT = `!s a:real^N. closure(a INSERT s) = a INSERT closure s`;;

let CLOSURE_DELETE = `!s a:real^N.
        closure(s DELETE a) =
        if a limit_point_of s then closure s else closure s DELETE a`;;

let CLOSED_INSERT = `!a s. closed s ==> closed(a INSERT s)`;;

let CONNECTED_2 = `!a b:real^N. connected {a,b} <=> a = b`;;

let COMPACT_CBALL = `!x e. compact(cball(x,e))`;;

let COMPACT_FRONTIER_BOUNDED = `!s. bounded s ==> compact(frontier s)`;;

let COMPACT_FRONTIER = `!s. compact s ==> compact (frontier s)`;;

let BOUNDED_FRONTIER = `!s:real^N->bool. bounded s ==> bounded(frontier s)`;;

let FRONTIER_SUBSET_COMPACT = `!s. compact s ==> frontier s SUBSET s`;;

let OPEN_DELETE = `!s x. open s ==> open(s DELETE x)`;;

let OPEN_IN_DELETE = `!u s a:real^N.
        open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean u) (s DELETE a)`;;

let CLOSED_INTERS_COMPACT = `!s:real^N->bool.
        closed s <=> !e. compact(cball(vec 0,e) INTER s)`;;

let COMPACT_UNIONS = `!s. FINITE s /\ (!t. t IN s ==> compact t) ==> compact(UNIONS s)`;;

let COMPACT_DIFF = `!s t. compact s /\ open t ==> compact(s DIFF t)`;;

let COMPACT_SPHERE = `!a:real^N r. compact(sphere(a,r))`;;

let BOUNDED_SPHERE = `!a:real^N r. bounded(sphere(a,r))`;;

let CLOSED_SPHERE = `!a r. closed(sphere(a,r))`;;

let CLOSURE_SPHERE = `!a:real^N r. closure(sphere(a,r)) = sphere(a,r)`;;

let FRONTIER_SPHERE = `!a:real^N r. frontier(sphere(a,r)) = sphere(a,r)`;;

let FRONTIER_SING = `!a:real^N. frontier {a} = {a}`;;

let COMPACT_OPEN = `!s:real^N->bool. compact s /\ open s <=> s = {}`;;

(* ------------------------------------------------------------------------- *)
(* Finite intersection property. I could make it an equivalence in fact.     *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IMP_FIP = `!s:real^N->bool f.
        compact s /\
        (!t. t IN f ==> closed t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`;;

let CLOSED_IMP_FIP = `!s:real^N->bool f.
        closed s /\
        (!t. t IN f ==> closed t) /\ (?t. t IN f /\ bounded t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`;;

let CLOSED_IMP_FIP_COMPACT = `!s:real^N->bool f.
        closed s /\ (!t. t IN f ==> compact t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`;;

let CLOSED_FIP = `!f. (!t:real^N->bool. t IN f ==> closed t) /\ (?t. t IN f /\ bounded t) /\
       (!f'. FINITE f' /\ f' SUBSET f ==> ~(INTERS f' = {}))
       ==> ~(INTERS f = {})`;;

let COMPACT_FIP = `!f. (!t:real^N->bool. t IN f ==> compact t) /\
       (!f'. FINITE f' /\ f' SUBSET f ==> ~(INTERS f' = {}))
       ==> ~(INTERS f = {})`;;

(* ------------------------------------------------------------------------- *)
(* Bounded closed nest property (proof does not use Heine-Borel).            *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_CLOSED_NEST = `!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       bounded(s 0)
       ==> ?a:real^N. !n:num. a IN s(n)`;;

(* ------------------------------------------------------------------------- *)
(* Decreasing case does not even need compactness, just completeness.        *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST = `!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. !n:num. a IN s(n)`;;

(* ------------------------------------------------------------------------- *)
(* Strengthen it to the intersection actually being a singleton.             *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST_SING = `!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. INTERS {t | ?n:num. t = s n} = {a}`;;

(* ------------------------------------------------------------------------- *)
(* A version for a more general chain, not indexed by N.                     *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_CLOSED_CHAIN = `!f b:real^N->bool.
        (!s. s IN f ==> closed s /\ ~(s = {})) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s) /\
         b IN f /\ bounded b
         ==> ~(INTERS f = {})`;;

(* ------------------------------------------------------------------------- *)
(* Analogous things directly for compactness.                                *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CHAIN = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> compact s /\ ~(s = {})) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ~(INTERS f = {})`;;

let COMPACT_NEST = `!s. (!n. compact(s n) /\ ~(s n = {})) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> ~(INTERS {s n | n IN (:num)} = {})`;;

(* ------------------------------------------------------------------------- *)
(* Relating convergent subsequences to escaping from a compact set.          *)
(* ------------------------------------------------------------------------- *)

let SEQUENCE_ESCAPES = `!s x:num->real^N.
      (!n. x n IN s)
      ==> ((!k. k SUBSET s /\ compact k ==> FINITE {n | x n IN k}) <=>
           ~(?y r. y IN s /\
                  (!m n. m < n ==> r m < r n) /\
                  (x o r --> y) sequentially))`;;

let SEQUENCE_ESCAPES_ALT = `!s x:num->real^N.
      (!n. x n IN s)
      ==> ((!k. k SUBSET s /\ compact k
                ==> eventually (\n. ~(x n IN k)) sequentially) <=>
           ~(?y r. y IN s /\
                  (!m n. m < n ==> r m < r n) /\
                  (x o r --> y) sequentially))`;;

let CONVERGENT_SUBSEQUENCE = `!s x:num->real^N.
      (!n. x n IN s)
      ==> ((?y r. y IN s /\
                  (!m n. m < n ==> r m < r n) /\
                  (x o r --> y) sequentially) <=>
           (?k. k SUBSET s /\ compact k /\ INFINITE {n | x(n) IN k}))`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type criteria for *uniform* convergence.                           *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONVERGENT_EQ_CAUCHY = `!P s:num->A->real^N.
         (?l. !e. &0 < e
                  ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e) <=>
         (!e. &0 < e
              ==> ?N. !m n x. N <= m /\ N <= n /\ P x
                              ==> dist(s m x,s n x) < e)`;;

let UNIFORMLY_CONVERGENT_EQ_CAUCHY_ALT = `!P s:num->A->real^N.
         (?l. !e. &0 < e
                  ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e) <=>
         (!e. &0 < e
              ==> ?N. !m n x. N <= m /\ N <= n /\ m < n /\ P x
                              ==> dist(s m x,s n x) < e)`;;

let UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT = `!P (s:num->A->real^N) l.
    (!e. &0 < e
         ==> ?N. !m n x. N <= m /\ N <= n /\ P x ==> dist(s m x,s n x) < e) /\
    (!x. P x ==> !e. &0 < e ==> ?N. !n. N <= n ==> dist(s n x,l x) < e)
    ==> (!e. &0 < e ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e)`;;

(* ------------------------------------------------------------------------- *)
(* Define continuity over a net to take in restrictions of the set.          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous",(12,"right"));;

let continuous = new_definition
  `f continuous net <=> (f --> f(netlimit net)) net`;;

let CONTINUOUS_TRIVIAL_LIMIT = `!f net. trivial_limit net ==> f continuous net`;;

let CONTINUOUS_WITHIN = `!f x:real^M. f continuous (at x within s) <=> (f --> f(x)) (at x within s)`;;

let LIM_CONTINUOUS_SELF_WITHIN = `!f:real^M->real^N s x y.
        f continuous (at x within s) /\ f x = y ==> (f --> y) (at x within s)`;;

let CONTINUOUS_AT = `!f (x:real^N). f continuous (at x) <=> (f --> f(x)) (at x)`;;

let LIM_CONTINUOUS_SELF_AT = `!f:real^M->real^N x y.
        f continuous (at x) /\ f x = y ==> (f --> y) (at x)`;;

let CONTINUOUS_AT_WITHIN = `!f:real^M->real^N x s.
        f continuous (at x) ==> f continuous (at x within s)`;;

let CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL = `!a s. closed s /\ ~(a IN s) ==> f continuous (at a within s)`;;

let CONTINUOUS_TRANSFORM_WITHIN = `!f g:real^M->real^N s x d.
        &0 < d /\ x IN s /\
        (!x'. x' IN s /\ dist(x',x) < d ==> f(x') = g(x')) /\
        f continuous (at x within s)
        ==> g continuous (at x within s)`;;

let CONTINUOUS_TRANSFORM_AT = `!f g:real^M->real^N x d.
        &0 < d /\ (!x'. dist(x',x) < d ==> f(x') = g(x')) /\
        f continuous (at x)
        ==> g continuous (at x)`;;

let CONTINUOUS_TRANSFORM_WITHIN_OPEN = `!f g:real^M->real^N s a.
        open s /\ a IN s /\
        (!x. x IN s ==> f x = g x) /\
        f continuous at a
        ==> g continuous at a`;;

let CONTINUOUS_TRANSFORM_WITHIN_OPEN_IN = `!f g:real^M->real^N s t a.
        open_in (subtopology euclidean t) s /\ a IN s /\
        (!x. x IN s ==> f x = g x) /\
        f continuous (at a within t)
        ==> g continuous (at a within t)`;;

let CONTINUOUS_TRANSFORM_WITHIN_SET_IMP = `!f a s t. eventually (\x. x IN t ==> x IN s) (at a) /\
             f continuous (at a within s)
             ==> f continuous (at a within t)`;;

(* ------------------------------------------------------------------------- *)
(* Derive the epsilon-delta forms, which we often use as "definitions"       *)
(* ------------------------------------------------------------------------- *)

let continuous_within = `f continuous (at x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\ dist(x',x) < d ==> dist(f(x'),f(x)) < e`;;

let continuous_at = `f continuous (at x) <=>
        !e. &0 < e ==> ?d. &0 < d /\
                           !x'. dist(x',x) < d ==> dist(f(x'),f(x)) < e`;;

let CONTINUOUS_WITHIN_COMPARISON = `!f:real^M->real^N g:real^M->real^P s a.
        g continuous (at a within s) /\
        (!x. x IN s ==> dist(f a,f x) <= dist(g a,g x))
        ==> f continuous (at a within s)`;;

let CONTINUOUS_EQ_CAUCHY_WITHIN = `!f:real^M->real^N s a.
        f continuous (at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN a INSERT s /\ dist(x,a) < d /\
                           x' IN a INSERT s /\ dist(x',a) < d
                           ==> dist(f x,f x') < e`;;

let CONTINUOUS_EQ_CAUCHY_AT = `!f:real^M->real^N a.
        f continuous (at a) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. dist(x,a) < d /\ dist(x',a) < d
                           ==> dist(f x,f x') < e`;;

(* ------------------------------------------------------------------------- *)
(* Versions in terms of open balls.                                          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_BALL = `!f s x. f continuous (at x within s) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            IMAGE f (ball(x,d) INTER s) SUBSET ball(f x,e)`;;

let CONTINUOUS_AT_BALL = `!f x. f continuous (at x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            IMAGE f (ball(x,d)) SUBSET ball(f x,e)`;;

(* ------------------------------------------------------------------------- *)
(* For setwise continuity, just start from the epsilon-delta definitions.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous_on",(12,"right"));;
parse_as_infix ("uniformly_continuous_on",(12,"right"));;

let continuous_on = new_definition
  `f continuous_on s <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ dist(x',x) < d
                                        ==> dist(f(x'),f(x)) < e`;;

let uniformly_continuous_on = new_definition
  `f uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ dist(x',x) < d
                           ==> dist(f(x'),f(x)) < e`;;

let CONTINUOUS_MAP_EUCLIDEAN = `!f:real^N->real^M s.
     continuous_map (subtopology euclidean s,euclidean) f <=>
     f continuous_on s`;;

let CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN = `!(f:real^M->real^N).
        continuous_map (euclidean,euclidean) f <=> f continuous_on (:real^M)`;;

let CONTINUOUS_MAP_EUCLIDEAN2 = `!(f:real^M->real^N) s t.
        continuous_map (subtopology euclidean s,subtopology euclidean t) f <=>
        f continuous_on s /\ IMAGE f s SUBSET t`;;

let UNIFORMLY_CONTINUOUS_MAP_EUCLIDEAN = `!f:real^N->real^M s.
     uniformly_continuous_map
      (submetric euclidean_metric s,euclidean_metric) f <=>
     f uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_MAP_LIFT = `uniformly_continuous_map (real_euclidean_metric,euclidean_metric) lift`;;

let UNIFORMLY_CONTINUOUS_MAP_DROP = `uniformly_continuous_map (euclidean_metric,real_euclidean_metric) drop`;;

let UNIFORMLY_CONTINUOUS_MAP_EQ_LIFT = `!m f:A->real.
        uniformly_continuous_map(m,real_euclidean_metric) f <=>
        uniformly_continuous_map(m,euclidean_metric) (lift o f)`;;

let UNIFORMLY_CONTINUOUS_MAP_EQ_DROP = `!m f:A->real^1.
        uniformly_continuous_map(m,euclidean_metric) f <=>
        uniformly_continuous_map(m,real_euclidean_metric) (drop o f)`;;

let UNIFORMLY_CONTINUOUS_MAP_LIFT_EQ = `!m f:real^1->A.
        uniformly_continuous_map(euclidean_metric,m) f <=>
        uniformly_continuous_map(real_euclidean_metric,m) (f o lift)`;;

let UNIFORMLY_CONTINUOUS_MAP_DROP_EQ = `!m f:real->A.
        uniformly_continuous_map(real_euclidean_metric,m) f <=>
        uniformly_continuous_map(euclidean_metric,m) (f o drop)`;;

(* ------------------------------------------------------------------------- *)
(* Some simple consequential lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_COMPARISON = `!f:real^M->real^N g:real^M->real^P s.
        g continuous_on s /\
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) <= dist(g x,g y))
        ==> f continuous_on s`;;

let UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS = `!f s. f uniformly_continuous_on s ==> f continuous_on s`;;

let CONTINUOUS_AT_IMP_CONTINUOUS_ON = `!f s. (!x. x IN s ==> f continuous (at x)) ==> f continuous_on s`;;

let CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN = `!f s. f continuous_on s <=> !x. x IN s ==> f continuous (at x within s)`;;

let CONTINUOUS_ON = `!f (s:real^N->bool).
        f continuous_on s <=> !x. x IN s ==> (f --> f(x)) (at x within s)`;;

let CONTINUOUS_ON_EQ_CONTINUOUS_AT = `!f:real^M->real^N s.
      open s ==> (f continuous_on s <=> (!x. x IN s ==> f continuous (at x)))`;;

let CONTINUOUS_WITHIN_OPEN_IN = `!f:real^M->real^N a s t.
        a IN t /\ open_in (subtopology euclidean s) t
        ==> (f continuous (at a within t) <=> f continuous (at a within s))`;;

let CONTINUOUS_WITHIN_SUBSET = `!f s t x. f continuous (at x within s) /\ t SUBSET s
             ==> f continuous (at x within t)`;;

let CONTINUOUS_ON_SUBSET = `!f s t. f continuous_on s /\ t SUBSET s ==> f continuous_on t`;;

let UNIFORMLY_CONTINUOUS_ON_SUBSET = `!f s t. f uniformly_continuous_on s /\ t SUBSET s
           ==> f uniformly_continuous_on t`;;

let CONTINUOUS_ON_INTERIOR = `!f:real^M->real^N s x.
        f continuous_on s /\ x IN interior(s) ==> f continuous at x`;;

let CONTINUOUS_ON_EQ = `!f g s. (!x. x IN s ==> f(x) = g(x)) /\ f continuous_on s
           ==> g continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_EQ = `!f g s.
        (!x. x IN s ==> f x = g x) /\ f uniformly_continuous_on s
        ==> g uniformly_continuous_on s`;;

let CONTINUOUS_ON_RESTRICT = `!P f g:real^M->real^N s.
        (!x. x IN s ==> P x)
        ==> ((\x. if P x then f x else g x) continuous_on s <=>
             f continuous_on s)`;;

let UNIFORMLY_CONTINUOUS_ON_RESTRICT = `!P f g:real^M->real^N s.
        (!x. x IN s ==> P x)
        ==> ((\x. if P x then f x else g x) uniformly_continuous_on s <=>
             f uniformly_continuous_on s)`;;

let CONTINUOUS_ON_SING = `!f:real^M->real^N a. f continuous_on {a}`;;

let CONTINUOUS_ON_EMPTY = `!f:real^M->real^N. f continuous_on {}`;;

let CONTINUOUS_ON_NO_LIMPT = `!f:real^M->real^N s.
     ~(?x. x limit_point_of s) ==> f continuous_on s`;;

let CONTINUOUS_ON_FINITE = `!f:real^M->real^N s. FINITE s ==> f continuous_on s`;;

let CONTRACTION_IMP_CONTINUOUS_ON = `!f:real^M->real^N.
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) <= dist(x,y))
        ==> f continuous_on s`;;

let ISOMETRY_ON_IMP_CONTINUOUS_ON = `!f:real^M->real^N.
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y))
        ==> f continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Characterization of limits and continuity in terms of sequences.          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_SEQUENTIALLY = `!f s a:real^N.
        f continuous (at a within s) <=>
                !x. (!n. x(n) IN s) /\ (x --> a) sequentially
                     ==> ((f o x) --> f(a)) sequentially`;;

let CONTINUOUS_AT_SEQUENTIALLY = `!f a:real^N.
        f continuous (at a) <=>
              !x. (x --> a) sequentially
                  ==> ((f o x) --> f(a)) sequentially`;;

let CONTINUOUS_ON_SEQUENTIALLY = `!f s:real^N->bool.
        f continuous_on s <=>
              !x a. a IN s /\ (!n. x(n) IN s) /\ (x --> a) sequentially
                    ==> ((f o x) --> f(a)) sequentially`;;

let UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY = `(!f:real^M->real^N s.
        f uniformly_continuous_on s <=>
        !x y. (!n. x n IN s) /\ (!n. y n IN s) /\
              ((\n. x n - y n) --> vec 0) sequentially
              ==> ((\n. f(x(n)) - f(y(n))) --> vec 0) sequentially)`
and UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY_ALT = `(!f:real^M->real^N s.
        f uniformly_continuous_on s <=>
        !e x y. &0 < e /\
                (!n. x n IN s) /\ (!n. y n IN s) /\
                ((\n. x n - y n) --> vec 0) sequentially
                ==> ?n. dist(f(x n),f(y n)) < e)`;;

let LIM_WITHIN_SEQUENTIALLY = `!f:real^M->real^N s a l.
        (f --> l) (at a within s) <=>
        !x. (!n. x(n) IN s DELETE a) /\
            (x --> a) sequentially
            ==> ((f o x) --> l) sequentially`;;

let LIM_WITHIN_SEQUENTIALLY_INJ = `!f:real^M->real^N s a l.
        (f --> l) (at a within s) <=>
        !x. (!n. x(n) IN s DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            (x --> a) sequentially
            ==> ((f o x) --> l) sequentially`;;

let LIM_WITHIN_SEQUENTIALLY_DECREASING = `!f:real^M->real^N s a l.
        (f --> l) (at a within s) <=>
        !x. (!n. x(n) IN s DELETE a) /\
            (!m n. m < n ==> dist(x n,a) < dist(x m,a)) /\
            (x --> a) sequentially
            ==> ((f o x) --> l) sequentially`;;

let LIM_AT_SEQUENTIALLY = `!f:real^M->real^N a l.
        (f --> l) (at a) <=>
        !x. (!n. ~(x(n) = a)) /\ (x --> a) sequentially
            ==> ((f o x) --> l) sequentially`;;

let CONTINUOUS_WITHIN_SEQUENTIALLY_INJ = `(!f:real^M->real^N s a.
        f continuous at a within s <=>
        !x. (!n. x n IN s DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            (x --> a) sequentially
            ==> (f o x --> f a) sequentially)`
and CONTINUOUS_WITHIN_SEQUENTIALLY_ALT = `(!f:real^M->real^N s a.
        (f continuous at a within s) <=>
        !e x. &0 < e /\
              (!n. x n IN s DELETE a) /\
              (x --> a) sequentially /\
              (!m n. x m = x n <=> m = n)
              ==> ?n. dist(f(x n),f a) < e)`;;

let CONTINUOUS_AT_SEQUENTIALLY_ALT = `!f:real^M->real^N a.
        (f continuous at a) <=>
        !e x. &0 < e /\
              (!n. ~(x n = a)) /\
              (x --> a) sequentially /\
              (!m n. x m = x n <=> m = n)
              ==> ?n. dist(f(x n),f a) < e`;;

let CONTINUOUS_AT_SEQUENTIALLY_INJ = `!f:real^M->real^N a.
        f continuous at a <=>
        !x. (!n. ~(x n = a)) /\
            (!m n. x m = x n <=> m = n) /\
            (x --> a) sequentially
            ==> (f o x --> f a) sequentially`;;

let LIM_CONTINUOUS = `!net f:A->real^N l.
        f continuous net /\ f(netlimit net) = l ==> (f --> l) net`;;

let LIM_CONTINUOUS_FUNCTION = `!f net g l.
        f continuous (at l) /\ (g --> l) net ==> ((\x. f(g x)) --> f l) net`;;

let LIM_CONTINUOUS_FUNCTION_WITHIN = `!net f:real^M->real^N g:A->real^M l s.
       f continuous (at l within s) /\
       (g --> l) net /\ eventually (\a. g a IN s) net
       ==> ((\x. f (g x)) --> f l) net`;;

let LIMIT_POINT_OF_IMAGE_GEN = `!f:real^M->real^N s u x.
      x limit_point_of s /\
      f continuous (at x within s) /\ open u /\ x IN u /\
      FINITE {z | z IN s INTER u /\ f z =  f x}
      ==> (f x) limit_point_of (IMAGE f s)`;;

let LIMIT_POINT_OF_IMAGE = `!f:real^M->real^N s x.
      x limit_point_of s /\
      f continuous (at x within s) /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
      ==> (f x) limit_point_of (IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* A continuous function distributes over nested compact intersection.       *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMAGE_NESTED_INTERS = `!f:real^M->real^N s.
        f continuous_on s 0 /\
        (!n. compact(s n)) /\
        (!n. s(SUC n) SUBSET s n)
        ==> IMAGE f (INTERS {s n | n IN (:num)}) =
            INTERS {IMAGE f (s n) | n IN (:num)}`;;

let CONTINUOUS_IMAGE_NESTED_INTERS_GEN = `!f:real^M->real^N s m.
        f continuous_on s m /\
        (!n. m <= n ==> compact(s n)) /\
        (!n. m <= n ==> s(SUC n) SUBSET s n)
        ==> IMAGE f (INTERS {s n | m <= n}) =
            INTERS {IMAGE f (s n) | m <= n}`;;

(* ------------------------------------------------------------------------- *)
(* Combination results for pointwise continuity.                             *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CONST = `!net c. (\x. c) continuous net`;;

let CONTINUOUS_CMUL = `!f c net. f continuous net ==> (\x. c % f(x)) continuous net`;;

let CONTINUOUS_NEG = `!f net. f continuous net ==> (\x. --(f x)) continuous net`;;

let CONTINUOUS_ADD = `!f g net. f continuous net /\ g continuous net
           ==> (\x. f(x) + g(x)) continuous net`;;

let CONTINUOUS_SUB = `!f g net. f continuous net /\ g continuous net
           ==> (\x. f(x) - g(x)) continuous net`;;

let CONTINUOUS_ABS = `!(f:A->real^N) net.
        f continuous net
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) continuous net`;;

let CONTINUOUS_LIFT_ABS_COMPONENT = `!net f:A->real^N k.
     f continuous net ==> (\x. lift(abs(f x$k))) continuous net`;;

let CONTINUOUS_LIFT_ABS = `!net:(A)net f.
    (\x. lift(f x)) continuous net ==> (\x. lift(abs(f x))) continuous net`;;

let CONTINUOUS_MAX = `!(f:A->real^N) (g:A->real^N) net.
        f continuous net /\ g continuous net
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N) continuous net`;;

let CONTINUOUS_MIN = `!(f:A->real^N) (g:A->real^N) net.
        f continuous net /\ g continuous net
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N) continuous net`;;

let CONTINUOUS_MAX_1 = `!net:(A)net f g.
        (\x. lift(f x)) continuous net /\ (\x. lift(g x)) continuous net
        ==> (\x. lift(max (f x) (g x))) continuous net`;;

let CONTINUOUS_MIN_1 = `!net:(A)net f g.
        (\x. lift(f x)) continuous net /\ (\x. lift(g x)) continuous net
        ==> (\x. lift(min (f x) (g x))) continuous net`;;

let CONTINUOUS_VSUM = `!net f s. FINITE s /\ (!a. a IN s ==> (f a) continuous net)
             ==> (\x. vsum s (\a. f a x)) continuous net`;;

let CONTINUOUS_COMPONENTWISE_LIFT = `!net f:A->real^N.
        f continuous net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) continuous net`;;

(* ------------------------------------------------------------------------- *)
(* Same thing for setwise continuity.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CONST = `!s c. (\x. c) continuous_on s`;;

let CONTINUOUS_ON_CMUL = `!f c s. f continuous_on s ==> (\x. c % f(x)) continuous_on s`;;

let CONTINUOUS_ON_NEG = `!f s. f continuous_on s
         ==> (\x. --(f x)) continuous_on s`;;

let CONTINUOUS_ON_ADD = `!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) + g(x)) continuous_on s`;;

let CONTINUOUS_ON_SUB = `!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) - g(x)) continuous_on s`;;

let CONTINUOUS_ON_LIFT_ABS_COMPONENT = `!f:real^M->real^N s.
     f continuous_on s ==> (\x. lift(abs(f x$k))) continuous_on s`;;

let CONTINUOUS_ON_LIFT_ABS = `!f s:real^N->bool.
     (\x. lift(f x)) continuous_on s ==> (\x. lift(abs(f x))) continuous_on s`;;

let CONTINUOUS_ON_ABS = `!f:real^M->real^N s.
        f continuous_on s
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) continuous_on s`;;

let CONTINUOUS_ON_MAX = `!f:real^M->real^N g:real^M->real^N s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N)
            continuous_on s`;;

let CONTINUOUS_ON_MIN = `!f:real^M->real^N g:real^M->real^N s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N)
            continuous_on s`;;

let CONTINUOUS_ON_MAX_1 = `!f:real^N->real g s.
        (\x. lift(f x)) continuous_on s /\ (\x. lift(g x)) continuous_on s
        ==> (\x. lift(max (f x) (g x))) continuous_on s`;;

let CONTINUOUS_ON_MIN_1 = `!f:real^N->real g s.
        (\x. lift(f x)) continuous_on s /\ (\x. lift(g x)) continuous_on s
        ==> (\x. lift(min (f x) (g x))) continuous_on s`;;

let CONTINUOUS_ON_VSUM = `!t f s. FINITE s /\ (!a. a IN s ==> (f a) continuous_on t)
             ==> (\x. vsum s (\a. f a x)) continuous_on t`;;

let CONTINUOUS_ON_COMPONENTWISE_LIFT = `!f:real^M->real^N s.
        f continuous_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) continuous_on s`;;

let CONTINUOUS_ON_REFLECT = `!f:real^M->real^N s.
        (\x. f(--x)) continuous_on (IMAGE (--) s) <=>
        f continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Same thing for uniform continuity, using sequential formulations.         *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_ON_CONST = `!s c. (\x. c) uniformly_continuous_on s`;;

let LINEAR_UNIFORMLY_CONTINUOUS_ON = `!f:real^M->real^N s. linear f ==> f uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_COMPOSE = `!f g s. f uniformly_continuous_on s /\
           g uniformly_continuous_on (IMAGE f s)
           ==> (g o f) uniformly_continuous_on s`;;

let BILINEAR_UNIFORMLY_CONTINUOUS_ON_COMPOSE = `!f:real^M->real^N g (h:real^N->real^P->real^Q) s.
           f uniformly_continuous_on s /\ g uniformly_continuous_on s /\
           bilinear h /\ bounded(IMAGE f s) /\ bounded(IMAGE g s)
           ==> (\x. h (f x) (g x)) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_MUL = `!f g:real^M->real^N s.
        (lift o f) uniformly_continuous_on s /\ g uniformly_continuous_on s /\
        bounded(IMAGE (lift o f) s) /\ bounded(IMAGE g s)
        ==>  (\x. f x % g x) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_CMUL = `!f c s. f uniformly_continuous_on s
           ==> (\x. c % f(x)) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_VMUL = `!s:real^M->bool c v:real^N.
      (lift o c) uniformly_continuous_on s
      ==> (\x. c x % v) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_NEG = `!f s. f uniformly_continuous_on s
         ==> (\x. --(f x)) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_ADD = `!f g s. f uniformly_continuous_on s /\ g uniformly_continuous_on s
           ==> (\x. f(x) + g(x)) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_SUB = `!f g s. f uniformly_continuous_on s /\ g uniformly_continuous_on s
           ==> (\x. f(x) - g(x)) uniformly_continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_VSUM = `!t f s. FINITE s /\ (!a. a IN s ==> (f a) uniformly_continuous_on t)
             ==> (\x. vsum s (\a. f a x)) uniformly_continuous_on t`;;

let UNIFORMLY_CONTINUOUS_ON_SQRT = `!f:real^N->real s.
        (lift o f) uniformly_continuous_on s
        ==> (\x. lift(sqrt(f x))) uniformly_continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Identity function is continuous in every sense.                           *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_ID = `!a s. (\x. x) continuous (at a within s)`;;

let CONTINUOUS_AT_ID = `!a. (\x. x) continuous (at a)`;;

let CONTINUOUS_ON_ID = `!s. (\x. x) continuous_on s`;;

let UNIFORMLY_CONTINUOUS_ON_ID = `!s. (\x. x) uniformly_continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Continuity of all kinds is preserved under composition.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_COMPOSE = `!f g x s. f continuous (at x within s) /\
             g continuous (at (f x) within IMAGE f s)
             ==> (g o f) continuous (at x within s)`;;

let CONTINUOUS_AT_COMPOSE = `!f g x. f continuous (at x) /\ g continuous (at (f x))
           ==> (g o f) continuous (at x)`;;

let CONTINUOUS_ON_COMPOSE = `!f g s. f continuous_on s /\ g continuous_on (IMAGE f s)
           ==> (g o f) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Continuity in terms of open preimages.                                    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_OPEN = `!f:real^M->real^N x u.
     f continuous (at x within u) <=>
        !t. open t /\ f(x) IN t
            ==> ?s. open s /\ x IN s /\
                    !x'. x' IN s /\ x' IN u ==> f(x') IN t`;;

let CONTINUOUS_AT_OPEN = `!f:real^M->real^N x.
     f continuous (at x) <=>
        !t. open t /\ f(x) IN t
            ==> ?s. open s /\ x IN s /\
                    !x'. x' IN s ==> f(x') IN t`;;

let CONTINUOUS_ON_OPEN_GEN = `!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> (f continuous_on s <=>
         !u. open_in (subtopology euclidean t) u
             ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN u})`;;

let CONTINUOUS_ON_OPEN = `!f:real^M->real^N s.
      f continuous_on s <=>
        !t. open_in (subtopology euclidean (IMAGE f s)) t
            ==> open_in (subtopology euclidean s) {x | x IN s /\ f(x) IN t}`;;

let CONTINUOUS_OPEN_IN_PREIMAGE_GEN = `!f:real^M->real^N s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        open_in (subtopology euclidean t) u
        ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN u}`;;

let CONTINUOUS_ON_IMP_OPEN_IN = `!f:real^M->real^N s t.
        f continuous_on s /\
        open_in (subtopology euclidean (IMAGE f s)) t
        ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`;;

let CONTINUOUS_OPEN_IN_PREIMAGE_SUBSET = `!f:real^M->real^N s t u v.
        f continuous_on s /\
        IMAGE f s SUBSET t /\
        open_in (subtopology euclidean s) u /\
        open_in (subtopology euclidean t) v
        ==> open_in (subtopology euclidean s) {x | x IN u /\ f x IN v}`;;

(* ------------------------------------------------------------------------- *)
(* Similarly in terms of closed sets.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CLOSED_GEN = `!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> (f continuous_on s <=>
         !u. closed_in (subtopology euclidean t) u
             ==> closed_in (subtopology euclidean s)
                           {x | x IN s /\ f x IN u})`;;

let CONTINUOUS_ON_CLOSED = `!f:real^M->real^N s.
      f continuous_on s <=>
        !t. closed_in (subtopology euclidean (IMAGE f s)) t
            ==> closed_in (subtopology euclidean s) {x | x IN s /\ f(x) IN t}`;;

let CONTINUOUS_CLOSED_IN_PREIMAGE_GEN = `!f:real^M->real^N s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        closed_in (subtopology euclidean t) u
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN u}`;;

let CONTINUOUS_ON_IMP_CLOSED_IN = `!f:real^M->real^N s t.
        f continuous_on s /\
        closed_in (subtopology euclidean (IMAGE f s)) t
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`;;

let CONTINUOUS_CLOSED_IN_PREIMAGE_SUBSET = `!f:real^M->real^N s t u v.
        f continuous_on s /\
        IMAGE f s SUBSET t /\
        closed_in (subtopology euclidean s) u /\
        closed_in (subtopology euclidean t) v
        ==> closed_in (subtopology euclidean s) {x | x IN u /\ f x IN v}`;;

(* ------------------------------------------------------------------------- *)
(* Half-global and completely global cases.                                  *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_OPEN_IN_PREIMAGE = `!f s t.
         f continuous_on s /\ open t
         ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`;;

let CONTINUOUS_CLOSED_IN_PREIMAGE = `!f s t.
         f continuous_on s /\ closed t
         ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`;;

let CONTINUOUS_OPEN_PREIMAGE = `!f:real^M->real^N s t.
     f continuous_on s /\ open s /\ open t
     ==> open {x | x IN s /\ f(x) IN t}`;;

let CONTINUOUS_CLOSED_PREIMAGE = `!f:real^M->real^N s t.
     f continuous_on s /\ closed s /\ closed t
     ==> closed {x | x IN s /\ f(x) IN t}`;;

let CONTINUOUS_OPEN_PREIMAGE_UNIV = `!f:real^M->real^N s.
        (!x. f continuous (at x)) /\ open s ==> open {x | f(x) IN s}`;;

let CONTINUOUS_CLOSED_PREIMAGE_UNIV = `!f:real^M->real^N s.
        (!x. f continuous (at x)) /\ closed s ==> closed {x | f(x) IN s}`;;

let CONTINUOUS_OPEN_IN_PREIMAGE_EQ = `!f:real^M->real^N s.
    f continuous_on s <=>
    !t. open t ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`;;

let CONTINUOUS_CLOSED_IN_PREIMAGE_EQ = `!f:real^M->real^N s.
    f continuous_on s <=>
    !t. closed t
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`;;

let RESTRICTION_CONTINUOUS_ON = `!s t f:real^M->real^N.
     s SUBSET t ==> (RESTRICTION t f continuous_on s <=> f continuous_on s)`;;

(* ------------------------------------------------------------------------- *)
(* Linear functions are (uniformly) continuous on any set.                   *)
(* ------------------------------------------------------------------------- *)

let LINEAR_LIM_0 = `!f. linear f ==> (f --> vec 0) (at (vec 0))`;;

let LINEAR_CONTINUOUS_AT = `!f:real^M->real^N a. linear f ==> f continuous (at a)`;;

let LINEAR_CONTINUOUS_WITHIN = `!f:real^M->real^N s x. linear f ==> f continuous (at x within s)`;;

let LINEAR_CONTINUOUS_ON = `!f:real^M->real^N s. linear f ==> f continuous_on s`;;

let LINEAR_CONTINUOUS_COMPOSE = `!net f:A->real^N g:real^N->real^P.
        f continuous net /\ linear g ==> (\x. g(f x)) continuous net`;;

let LINEAR_CONTINUOUS_ON_COMPOSE = `!f:real^M->real^N g:real^N->real^P s.
        f continuous_on s /\ linear g ==> (\x. g(f x)) continuous_on s`;;

let CONTINUOUS_LIFT_COMPONENT_COMPOSE = `!net f:A->real^N i.
    f continuous net ==> (\x. lift(f x$i)) continuous net`;;

let CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE = `!f:real^M->real^N s.
        f continuous_on s
        ==> (\x. lift (f x$i)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Also bilinear functions, in composition form.                             *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_CONTINUOUS_COMPOSE = `!net f:A->real^M g:A->real^N h:real^M->real^N->real^P.
        f continuous net /\ g continuous net /\ bilinear h
        ==> (\x. h (f x) (g x)) continuous net`;;

let BILINEAR_CONTINUOUS_ON_COMPOSE = `!f g h s. f continuous_on s /\ g continuous_on s /\ bilinear h
             ==> (\x. h (f x) (g x)) continuous_on s`;;

let BILINEAR_CONTINUOUS_ON = `!bop:real^M->real^N->real^P.
        bilinear bop ==> (\z. bop (fstcart z) (sndcart z)) continuous_on UNIV`;;

let BILINEAR_DOT = `bilinear (\x y:real^N. lift(x dot y))`;;

let CONTINUOUS_LIFT_DOT2 = `!net f g:A->real^N.
        f continuous net /\ g continuous net
        ==> (\x. lift(f x dot g x)) continuous net`;;

let CONTINUOUS_ON_LIFT_DOT2 = `!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. lift(f x dot g x)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Preservation of compactness and connectedness under continuous function.  *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CONTINUOUS_IMAGE = `!f:real^M->real^N s.
        f continuous_on s /\ compact s ==> compact(IMAGE f s)`;;

let COMPACT_TRANSLATION = `!s a:real^N. compact s ==> compact (IMAGE (\x. a + x) s)`;;

let COMPACT_TRANSLATION_EQ = `!a s. compact (IMAGE (\x:real^N. a + x) s) <=> compact s`;;

add_translation_invariants [COMPACT_TRANSLATION_EQ];;

let COMPACT_LINEAR_IMAGE = `!f:real^M->real^N s. compact s /\ linear f ==> compact(IMAGE f s)`;;

let COMPACT_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (compact (IMAGE f s) <=> compact s)`;;

add_linear_invariants [COMPACT_LINEAR_IMAGE_EQ];;

let CONNECTED_CONTINUOUS_IMAGE = `!f:real^M->real^N s.
        f continuous_on s /\ connected s ==> connected(IMAGE f s)`;;

let CONNECTED_TRANSLATION = `!a s. connected s ==> connected (IMAGE (\x:real^N. a + x) s)`;;

let CONNECTED_TRANSLATION_EQ = `!a s. connected (IMAGE (\x:real^N. a + x) s) <=> connected s`;;

add_translation_invariants [CONNECTED_TRANSLATION_EQ];;

let CONNECTED_LINEAR_IMAGE = `!f:real^M->real^N s. connected s /\ linear f ==> connected(IMAGE f s)`;;

let CONNECTED_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (connected (IMAGE f s) <=> connected s)`;;

add_linear_invariants [CONNECTED_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Preservation properties for pasted sets (Cartesian products).             *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        bounded (s PCROSS t) <=>
        s = {} \/ t = {} \/ bounded s /\ bounded t`;;

let BOUNDED_PCROSS = `!s:real^M->bool t:real^N->bool.
     bounded s /\ bounded t ==> bounded (s PCROSS t)`;;

let CLOSED_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        closed (s PCROSS t) <=>
        s = {} \/ t = {} \/ closed s /\ closed t`;;

let CLOSED_PCROSS = `!s:real^M->bool t:real^N->bool.
     closed s /\ closed t ==> closed (s PCROSS t)`;;

let COMPACT_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        compact (s PCROSS t) <=>
        s = {} \/ t = {} \/ compact s /\ compact t`;;

let COMPACT_PCROSS = `!s:real^M->bool t:real^N->bool.
     compact s /\ compact t ==> compact (s PCROSS t)`;;

let OPEN_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        open (s PCROSS t) <=>
        s = {} \/ t = {} \/ open s /\ open t`;;

let OPEN_PCROSS = `!s:real^M->bool t:real^N->bool.
        open s /\ open t ==> open (s PCROSS t)`;;

let OPEN_IN_PCROSS = `!s s':real^M->bool t t':real^N->bool.
        open_in (subtopology euclidean s) s' /\
        open_in (subtopology euclidean t) t'
        ==> open_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t')`;;

let PASTECART_IN_INTERIOR_SUBTOPOLOGY = `!s t u x:real^M y:real^N.
     pastecart x y IN u /\ open_in (subtopology euclidean (s PCROSS t)) u
     ==> ?v w. open_in (subtopology euclidean s) v /\ x IN v /\
               open_in (subtopology euclidean t) w /\ y IN w /\
               (v PCROSS w) SUBSET u`;;

let PASTECART_IN_INTERIOR = `!u x:real^M y:real^N.
     pastecart x y IN u /\ open u
     ==> ?v w. open v /\ x IN v /\ open w /\ y IN w /\ (v PCROSS w) SUBSET u`;;

let OPEN_IN_PCROSS_EQ = `!s s':real^M->bool t t':real^N->bool.
        open_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t') <=>
        s' = {} \/ t' = {} \/
        open_in (subtopology euclidean s) s' /\
        open_in (subtopology euclidean t) t'`;;

let INTERIOR_PCROSS = `!s:real^M->bool t:real^N->bool.
        interior (s PCROSS t) = (interior s) PCROSS (interior t)`;;

let LIPSCHITZ_CONTINUOUS_MAP_PASTING = `lipschitz_continuous_map
      (prod_metric euclidean_metric euclidean_metric,euclidean_metric)
      (\(x:real^M,y:real^N). pastecart x y)`;;

let LIPSCHITZ_CONTINUOUS_MAP_CART_PROJECTIONS = `lipschitz_continuous_map (euclidean_metric,euclidean_metric)
                            (fstcart:real^(M,N)finite_sum->real^M) /\
   lipschitz_continuous_map(euclidean_metric,euclidean_metric)
                            (sndcart:real^(M,N)finite_sum->real^N)`;;

let LIPSCHITZ_CONTINUOUS_MAP_PASTEWISE = `!m (f:A->real^(M,N)finite_sum).
        lipschitz_continuous_map(m,euclidean_metric) f <=>
        lipschitz_continuous_map(m,euclidean_metric) (fstcart o f) /\
        lipschitz_continuous_map(m,euclidean_metric) (sndcart o f)`;;

let LIPSCHITZ_CONTINUOUS_MAP_PASTED = `!m (f:A->real^M) (g:A->real^N).
        lipschitz_continuous_map (m,euclidean_metric)
                                 (\x. pastecart (f x) (g x)) <=>
        lipschitz_continuous_map(m,euclidean_metric) f /\
        lipschitz_continuous_map(m,euclidean_metric) g`;;

let UNIFORMLY_CONTINUOUS_MAP_PASTEWISE = `!m (f:A->real^(M,N)finite_sum).
        uniformly_continuous_map(m,euclidean_metric) f <=>
        uniformly_continuous_map(m,euclidean_metric) (fstcart o f) /\
        uniformly_continuous_map(m,euclidean_metric) (sndcart o f)`;;

let UNIFORMLY_CONTINUOUS_MAP_PASTED = `!m (f:A->real^M) (g:A->real^N).
        uniformly_continuous_map (m,euclidean_metric)
                                 (\x. pastecart (f x) (g x)) <=>
        uniformly_continuous_map(m,euclidean_metric) f /\
        uniformly_continuous_map(m,euclidean_metric) g`;;

let CAUCHY_CONTINUOUS_MAP_PASTEWISE = `!m (f:A->real^(M,N)finite_sum).
        cauchy_continuous_map(m,euclidean_metric) f <=>
        cauchy_continuous_map(m,euclidean_metric) (fstcart o f) /\
        cauchy_continuous_map(m,euclidean_metric) (sndcart o f)`;;

let CAUCHY_CONTINUOUS_MAP_PASTED = `!m (f:A->real^M) (g:A->real^N).
        cauchy_continuous_map (m,euclidean_metric)
                                 (\x. pastecart (f x) (g x)) <=>
        cauchy_continuous_map(m,euclidean_metric) f /\
        cauchy_continuous_map(m,euclidean_metric) g`;;

let CONTINUOUS_MAP_PASTEWISE = `!top (f:A->real^(M,N)finite_sum).
        continuous_map(top,euclidean) f <=>
        continuous_map(top,euclidean) (fstcart o f) /\
        continuous_map(top,euclidean) (sndcart o f)`;;

let CONTINUOUS_MAP_PASTED = `!top (f:A->real^M) (g:A->real^N).
        continuous_map (top,euclidean) (\x. pastecart (f x) (g x)) <=>
        continuous_map(top,euclidean) f /\
        continuous_map(top,euclidean) g`;;

(* ------------------------------------------------------------------------- *)
(* Quotient maps are occasionally useful.                                    *)
(* ------------------------------------------------------------------------- *)

let QUASICOMPACT_OPEN_CLOSED = `!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> ((!u. u SUBSET t
              ==> (open_in (subtopology euclidean s)
                           {x | x IN s /\ f x IN u}
                   ==> open_in (subtopology euclidean t) u)) <=>
         (!u. u SUBSET t
              ==> (closed_in (subtopology euclidean s)
                             {x | x IN s /\ f x IN u}
                   ==> closed_in (subtopology euclidean t) u)))`;;

let QUOTIENT_MAP_IMP_CONTINUOUS_OPEN = `!f:real^M->real^N s t.
     IMAGE f s SUBSET t /\
     (!u. u SUBSET t
          ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
               open_in (subtopology euclidean t) u))
     ==> f continuous_on s`;;

let QUOTIENT_MAP_IMP_CONTINUOUS_CLOSED = `!f:real^M->real^N s t.
     IMAGE f s SUBSET t /\
     (!u. u SUBSET t
          ==> (closed_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
               closed_in (subtopology euclidean t) u))
     ==> f continuous_on s`;;

let OPEN_MAP_IMP_QUOTIENT_MAP = `!f:real^M->real^N s.
    f continuous_on s /\
    (!t. open_in (subtopology euclidean s) t
         ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t))
    ==> !t. t SUBSET IMAGE f s
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                 open_in (subtopology euclidean (IMAGE f s)) t)`;;

let CLOSED_MAP_IMP_QUOTIENT_MAP = `!f:real^M->real^N s.
    f continuous_on s /\
    (!t. closed_in (subtopology euclidean s) t
         ==> closed_in (subtopology euclidean (IMAGE f s)) (IMAGE f t))
    ==> !t. t SUBSET IMAGE f s
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                 open_in (subtopology euclidean (IMAGE f s)) t)`;;

let CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        (!y. y IN t ==> f(g y) = y)
        ==> (!u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u))`;;

let CONTINUOUS_LEFT_INVERSE_IMP_QUOTIENT_MAP = `!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x)
        ==> (!u. u SUBSET (IMAGE f s)
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean (IMAGE f s)) u))`;;

let QUOTIENT_MAP_OPEN_CLOSED = `!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> ((!u. u SUBSET t
              ==> (open_in (subtopology euclidean s)
                           {x | x IN s /\ f x IN u} <=>
                   open_in (subtopology euclidean t) u)) <=>
         (!u. u SUBSET t
              ==> (closed_in (subtopology euclidean s)
                             {x | x IN s /\ f x IN u} <=>
                   closed_in (subtopology euclidean t) u)))`;;

let CONTINUOUS_ON_COMPOSE_QUOTIENT = `!f:real^M->real^N g:real^N->real^P s t u.
      IMAGE f s SUBSET t /\ IMAGE g t SUBSET u /\
      (!v. v SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN v} <=>
                open_in (subtopology euclidean t) v)) /\
      (g o f) continuous_on s
      ==> g continuous_on t`;;

let LIFT_TO_QUOTIENT_SPACE = `!f:real^M->real^N h:real^M->real^P s t u.
        IMAGE f s = t /\
        (!v. v SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN v} <=>
                open_in (subtopology euclidean t) v)) /\
        h continuous_on s /\ IMAGE h s = u /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> h x = h y)
        ==> ?g. g continuous_on t /\ IMAGE g t = u /\
                !x. x IN s ==> h(x) = g(f x)`;;

let QUOTIENT_MAP_COMPOSE_EXPLICIT = `!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\
        (!v. v SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN v} <=>
                open_in (subtopology euclidean t) v)) /\
        (!v. v SUBSET u
           ==> (open_in (subtopology euclidean t) {x | x IN t /\ g x IN v} <=>
                open_in (subtopology euclidean u) v))
        ==> !v. v SUBSET u
                ==> (open_in (subtopology euclidean s)
                             {x | x IN s /\ (g o f) x IN v} <=>
                     open_in (subtopology euclidean u) v)`;;

let QUOTIENT_MAP_FROM_COMPOSITION_EXPLICIT = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!v. v SUBSET u
             ==> (open_in (subtopology euclidean s)
                          {x | x IN s /\ (g o f) x IN v} <=>
                  open_in (subtopology euclidean u) v))
        ==> !v. v SUBSET u
                ==> (open_in (subtopology euclidean t)
                              {x | x IN t /\ g x IN v} <=>
                     open_in (subtopology euclidean u) v)`;;

let QUOTIENT_MAP_FROM_SUBSET = `!f:real^M->real^N s t u.
        f continuous_on t /\ IMAGE f t SUBSET u /\
        s SUBSET t /\ IMAGE f s = u /\
        (!v. v SUBSET u
             ==> (open_in (subtopology euclidean s)
                          {x | x IN s /\ f x IN v} <=>
                  open_in (subtopology euclidean u) v))
        ==> !v. v SUBSET u
                ==> (open_in (subtopology euclidean t)
                             {x | x IN t /\ f x IN v} <=>
                     open_in (subtopology euclidean u) v)`;;

let QUOTIENT_MAP_RESTRICT = `!f:real^M->real^N s t c.
     IMAGE f s SUBSET t /\
     (!u. u SUBSET t
        ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
             open_in (subtopology euclidean t) u)) /\
     (open_in (subtopology euclidean t) c \/
      closed_in (subtopology euclidean t) c)
     ==> !u. u SUBSET c
             ==> (open_in (subtopology euclidean {x | x IN s /\ f x IN c})
                          {x | x IN {x | x IN s /\ f x IN c} /\ f x IN u} <=>
                  open_in (subtopology euclidean c) u)`;;

let CONNECTED_MONOTONE_QUOTIENT_PREIMAGE_GEN = `!f:real^M->real^N s t c.
      IMAGE f s = t /\
      (!u. u SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                open_in (subtopology euclidean t) u)) /\
      (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
      (open_in (subtopology euclidean t) c \/
       closed_in (subtopology euclidean t) c) /\
      connected c
      ==> connected {x | x IN s /\ f x IN c}`;;

let CONNECTED_MONOTONE_QUOTIENT_PREIMAGE = `!f:real^M->real^N s t.
      f continuous_on s /\ IMAGE f s = t /\
      (!u. u SUBSET t
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                open_in (subtopology euclidean t) u)) /\
      (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
      connected t
      ==> connected s`;;

(* ------------------------------------------------------------------------- *)
(* More properties of open and closed maps.                                  *)
(* ------------------------------------------------------------------------- *)

let CLOSED_MAP_CLOSURES = `!f:real^M->real^N.
        (!s. closed s ==> closed(IMAGE f s)) <=>
        (!s. closure(IMAGE f s) SUBSET IMAGE f (closure s))`;;

let OPEN_MAP_INTERIORS = `!f:real^M->real^N.
        (!s. open s ==> open(IMAGE f s)) <=>
        (!s. IMAGE f (interior s) SUBSET interior(IMAGE f s))`;;

let OPEN_MAP_RESTRICT = `!f:real^M->real^N s t t'.
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        t' SUBSET t
        ==> !u. open_in (subtopology euclidean {x | x IN s /\ f x IN t'}) u
                ==> open_in (subtopology euclidean t') (IMAGE f u)`;;

let CLOSED_MAP_RESTRICT = `!f:real^M->real^N s t t'.
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean t) (IMAGE f u)) /\
        t' SUBSET t
        ==> !u. closed_in (subtopology euclidean {x | x IN s /\ f x IN t'}) u
                ==> closed_in (subtopology euclidean t') (IMAGE f u)`;;

let QUOTIENT_MAP_OPEN_MAP_EQ = `!f:real^M->real^N s t.
       IMAGE f s SUBSET t /\
       (!u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u))
       ==> ((!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean s)
                               {x | x IN s /\ f x IN IMAGE f k}))`;;

let QUOTIENT_MAP_CLOSED_MAP_EQ = `!f:real^M->real^N s t.
       IMAGE f s SUBSET t /\
       (!u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u))
       ==> ((!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean s)
                               {x | x IN s /\ f x IN IMAGE f k}))`;;

let CLOSED_MAP_IMP_OPEN_MAP = `!f:real^M->real^N s t.
        IMAGE f s = t /\
        (!u. closed_in (subtopology euclidean s) u
                ==> closed_in (subtopology euclidean t) (IMAGE f u)) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean s)
                         {x | x IN s /\ f x IN IMAGE f u})
        ==> (!u. open_in (subtopology euclidean s) u
                 ==> open_in (subtopology euclidean t) (IMAGE f u))`;;

let OPEN_MAP_IMP_CLOSED_MAP = `!f:real^M->real^N s t.
        IMAGE f s = t /\
        (!u. open_in (subtopology euclidean s) u
                ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean s)
                         {x | x IN s /\ f x IN IMAGE f u})
        ==> (!u. closed_in (subtopology euclidean s) u
                 ==> closed_in (subtopology euclidean t) (IMAGE f u))`;;

let OPEN_MAP_IFF_CLOSED_MAP_BIJECTIVE = `!f:real^M->real^N s t.
        IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((!u. open_in (subtopology euclidean s) u
                  ==> open_in (subtopology euclidean t) (IMAGE f u)) <=>
             (!c. closed_in (subtopology euclidean s) c
                  ==> closed_in (subtopology euclidean t) (IMAGE f c)))`;;

let OPEN_MAP_FROM_COMPOSITION_SURJECTIVE = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\ IMAGE g t SUBSET u /\
        (!k. open_in (subtopology euclidean s) k
             ==> open_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. open_in (subtopology euclidean t) k
                 ==> open_in (subtopology euclidean u) (IMAGE g k))`;;

let CLOSED_MAP_FROM_COMPOSITION_SURJECTIVE = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\ IMAGE g t SUBSET u /\
        (!k. closed_in (subtopology euclidean s) k
             ==> closed_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. closed_in (subtopology euclidean t) k
                 ==> closed_in (subtopology euclidean u) (IMAGE g k))`;;

let OPEN_MAP_FROM_COMPOSITION_INJECTIVE = `!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\ IMAGE g t SUBSET u /\
        g continuous_on t /\ (!x y. x IN t /\ y IN t /\ g x = g y ==> x = y) /\
        (!k. open_in (subtopology euclidean s) k
             ==> open_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean t) (IMAGE f k))`;;

let CLOSED_MAP_FROM_COMPOSITION_INJECTIVE = `!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\ IMAGE g t SUBSET u /\
        g continuous_on t /\ (!x y. x IN t /\ y IN t /\ g x = g y ==> x = y) /\
        (!k. closed_in (subtopology euclidean s) k
             ==> closed_in (subtopology euclidean u) (IMAGE (g o f) k))
        ==> (!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k))`;;

let OPEN_MAP_CLOSED_SUPERSET_PREIMAGE = `!f:real^M->real^N s t u w.
        (!k. open_in (subtopology euclidean s) k
             ==> open_in (subtopology euclidean t) (IMAGE f k)) /\
        closed_in (subtopology euclidean s) u /\
        w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
        ==> ?v. closed_in (subtopology euclidean t) v /\
                w SUBSET v /\
                {x | x IN s /\ f(x) IN v} SUBSET u`;;

let OPEN_MAP_CLOSED_SUPERSET_PREIMAGE_EQ = `!f:real^M->real^N s t.
       IMAGE f s SUBSET t
       ==> ((!k. open_in (subtopology euclidean s) k
                 ==> open_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!u w. closed_in (subtopology euclidean s) u /\
                   w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
                   ==> ?v. closed_in (subtopology euclidean t) v /\
                           w SUBSET v /\ {x | x IN s /\ f(x) IN v} SUBSET u))`;;

let CLOSED_MAP_OPEN_SUPERSET_PREIMAGE = `!f:real^M->real^N s t u w.
        (!k. closed_in (subtopology euclidean s) k
             ==> closed_in (subtopology euclidean t) (IMAGE f k)) /\
        open_in (subtopology euclidean s) u /\
        w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
        ==> ?v. open_in (subtopology euclidean t) v /\
                w SUBSET v /\
                {x | x IN s /\ f(x) IN v} SUBSET u`;;

let CLOSED_MAP_OPEN_SUPERSET_PREIMAGE_EQ = `!f:real^M->real^N s t.
       IMAGE f s SUBSET t
       ==> ((!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!u w. open_in (subtopology euclidean s) u /\
                   w SUBSET t /\ {x | x IN s /\ f(x) IN w} SUBSET u
                   ==> ?v. open_in (subtopology euclidean t) v /\
                           w SUBSET v /\ {x | x IN s /\ f(x) IN v} SUBSET u))`;;

let CLOSED_MAP_OPEN_SUPERSET_PREIMAGE_POINT = `!f:real^M->real^N s t.
       IMAGE f s SUBSET t
       ==> ((!k. closed_in (subtopology euclidean s) k
                 ==> closed_in (subtopology euclidean t) (IMAGE f k)) <=>
            (!u y. open_in (subtopology euclidean s) u /\
                   y IN t /\ {x | x IN s /\ f(x) = y} SUBSET u
                   ==> ?v. open_in (subtopology euclidean t) v /\
                           y IN v /\ {x | x IN s /\ f(x) IN v} SUBSET u))`;;

let CONNECTED_OPEN_MONOTONE_PREIMAGE = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!c. open_in (subtopology euclidean s) c
             ==> open_in (subtopology euclidean t) (IMAGE f c)) /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y})
        ==> !c. connected c /\ c SUBSET t
                ==> connected {x | x IN s /\ f x IN c}`;;

let CONNECTED_CLOSED_MONOTONE_PREIMAGE = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y})
        ==> !c. connected c /\ c SUBSET t
                ==> connected {x | x IN s /\ f x IN c}`;;

(* ------------------------------------------------------------------------- *)
(* Proper maps, including projections out of compact sets.                   *)
(* ------------------------------------------------------------------------- *)

let PROPER_MAP_INTO_EUCLIDEAN = `!top (f:A->real^N) s.
        continuous_map(top,subtopology euclidean s) f \/ kc_space top
        ==> (proper_map(top,subtopology euclidean s) f <=>
             IMAGE f (topspace top) SUBSET s /\
             !k. k SUBSET s /\ compact k
                 ==> compact_in top {x | x IN topspace top /\ f x IN k})`;;

let PROPER_MAP_EUCLIDEAN = `!(f:real^M->real^N) s t.
        proper_map(subtopology euclidean s,subtopology euclidean t) f <=>
        IMAGE f s SUBSET t /\
        !k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}`;;

let PROPER_MAP = `!f:real^M->real^N s t.
    IMAGE f s SUBSET t
    ==> ((!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) <=>
         (!k. closed_in (subtopology euclidean s) k
              ==> closed_in (subtopology euclidean t) (IMAGE f k)) /\
         (!a. a IN t ==> compact {x | x IN s /\ f x = a}))`;;

let PROPER_MAP_EQ = `!f:real^M->real^N s t.
        IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) <=>
        (!k. closed_in (subtopology euclidean s) k
             ==> closed_in (subtopology euclidean t) (IMAGE f k)) /\
        (!a. a IN t ==> compact {x | x IN s /\ f x = a})`;;

let PROPER_MAP_FROM_COMPACT = `!f:real^M->real^N s k t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ compact s /\
        closed_in (subtopology euclidean t) k
        ==> compact {x | x IN s /\ f x IN k}`;;

let PROPER_MAP_FROM_COMPACT_ALT = `!f:real^M->real^N s t.
         compact s /\ f continuous_on s /\ IMAGE f s SUBSET t
         ==> !k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}`;;

let PROPER_MAP_EUCLIDEAN_COMPOSE = `!f:real^M->real^N g:real^N->real^P s t u.
        IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        (!k. k SUBSET u /\ compact k ==> compact {x | x IN t /\ g x IN k})
        ==> !k. k SUBSET u /\ compact k
                ==> compact {x | x IN s /\ (g o f) x IN k}`;;

let PROPER_MAP_EUCLIDEAN_FROM_COMPOSITION_LEFT = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!k. k SUBSET u /\ compact k
             ==> compact {x | x IN s /\ (g o f) x IN k})
        ==> !k. k SUBSET u /\ compact k ==> compact {x | x IN t /\ g x IN k}`;;

let PROPER_MAP_EUCLIDEAN_FROM_COMPOSITION_RIGHT = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!k. k SUBSET u /\ compact k
             ==> compact {x | x IN s /\ (g o f) x IN k})
        ==> !k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}`;;

let PROPER_MAP_FSTCART = `!s:real^M->bool t:real^N->bool k.
        compact t /\ k SUBSET s /\ compact k
        ==> compact {z | z IN s PCROSS t /\ fstcart z IN k}`;;

let CLOSED_MAP_FSTCART = `!s:real^M->bool t:real^N->bool c.
        compact t /\ closed_in (subtopology euclidean (s PCROSS t)) c
        ==> closed_in (subtopology euclidean s) (IMAGE fstcart c)`;;

let PROPER_MAP_SNDCART = `!s:real^M->bool t:real^N->bool k.
        compact s /\ k SUBSET t /\ compact k
        ==> compact {z | z IN s PCROSS t /\ sndcart z IN k}`;;

let CLOSED_MAP_SNDCART = `!s:real^M->bool t:real^N->bool c.
        compact s /\ closed_in (subtopology euclidean (s PCROSS t)) c
        ==> closed_in (subtopology euclidean t) (IMAGE sndcart c)`;;

let CLOSED_IN_COMPACT_PROJECTION = `!s:real^M->bool t:real^N->bool u.
    compact s /\ closed_in (subtopology euclidean (s PCROSS t)) u
    ==> closed_in (subtopology euclidean t)
                  {y | ?x. x IN s /\ pastecart x y IN u}`;;

let CLOSED_COMPACT_PROJECTION = `!s:real^M->bool t:real^(M,N)finite_sum->bool.
      compact s /\ closed t ==> closed {y | ?x. x IN s /\ pastecart x y IN t}`;;

let TUBE_LEMMA = `!s:real^M->bool t:real^N->bool u a.
        compact s /\ ~(s = {}) /\ {pastecart x a | x IN s} SUBSET u /\
        open_in(subtopology euclidean (s PCROSS t)) u
        ==> ?v. open_in (subtopology euclidean t) v /\ a IN v /\
                (s PCROSS v) SUBSET u`;;

let TUBE_LEMMA_GEN = `!s t t' u:real^(M,N)finite_sum->bool.
        compact s /\ ~(s = {}) /\ t SUBSET t' /\
        s PCROSS t SUBSET u /\
        open_in (subtopology euclidean (s PCROSS t')) u
        ==> ?v. open_in (subtopology euclidean t') v /\
                t SUBSET v /\
                s PCROSS v SUBSET u`;;

(* ------------------------------------------------------------------------- *)
(* Sequential characterizations of proper-ness.                              *)
(* ------------------------------------------------------------------------- *)

let PROPER_MAP_SEQUENTIALLY_IMP = `!f:real^M->real^N s t x y.
        IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        (!n. x(n) IN s) /\ y IN t /\ ((f o x) --> y) sequentially
        ==> ?z r. z IN s /\ (!m n. m < n ==> r m < r n) /\
                  ((x o r) --> z) sequentially`;;

let PROPER_MAP_SEQUENTIALLY_REV = `!f:real^M->real^N s t.
        f continuous_on s /\
        (!x y. (!n. x(n) IN s) /\ y IN t /\ ((f o x) --> y) sequentially
               ==> ?z r. z IN s /\ (!m n. m < n ==> r m < r n) /\
                         ((x o r) --> z) sequentially)
        ==> !k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}`;;

let PROPER_MAP_SEQUENTIALLY = `!f:real^M->real^N s t.
    f continuous_on s /\ IMAGE f s SUBSET t
    ==> ((!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) <=>
         !x y. (!n. x(n) IN s) /\ y IN t /\ ((f o x) --> y) sequentially
               ==> ?z r. z IN s /\
                         (!m n. m < n ==> r m < r n) /\
                         ((x o r) --> z) sequentially)`;;

let PROPER_MAP_ESCAPES_IMP = `!f:real^M->real^N s t x.
        IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        (!n:num. x n IN s) /\
        (!c. c SUBSET s /\ compact c ==> FINITE {n | x n IN c})
        ==> (!k. k SUBSET t /\ compact k ==> FINITE {n | f(x n) IN k})`;;

let PROPER_MAP_ESCAPES = `!f:real^M->real^N s t.
    f continuous_on s /\ IMAGE f s SUBSET t
    ==> ((!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) <=>
         !x. (!n:num. x n IN s) /\
             (!c. c SUBSET s /\ compact c ==> FINITE {n | x n IN c})
             ==> (!k. k SUBSET t /\ compact k ==> FINITE {n | f(x n) IN k}))`;;

(* ------------------------------------------------------------------------- *)
(* Pasting functions together on open sets.                                  *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_UNION_LOCAL_OPEN = `!f:real^M->real^N s.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ f continuous_on t
        ==> f continuous_on (s UNION t)`;;

let CONTINUOUS_ON_UNION_OPEN = `!f s t. open s /\ open t /\ f continuous_on s /\ f continuous_on t
           ==> f continuous_on (s UNION t)`;;

let CONTINUOUS_ON_CASES_LOCAL_OPEN = `!P f g:real^M->real^N s t.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ g continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) continuous_on (s UNION t)`;;

let CONTINUOUS_ON_CASES_OPEN = `!P f g s t.
           open s /\
           open t /\
           f continuous_on s /\
           g continuous_on t /\
           (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
           ==> (\x. if P x then f x else g x) continuous_on s UNION t`;;

(* ------------------------------------------------------------------------- *)
(* Closure of halflines, halfspaces and hyperplanes.                         *)
(* ------------------------------------------------------------------------- *)

let LIM_LIFT_DOT = `!f:real^M->real^N a.
        (f --> l) net ==> ((lift o (\y. a dot f(y))) --> lift(a dot l)) net`;;

let CONTINUOUS_AT_LIFT_DOT = `!a:real^N x. (lift o (\y. a dot y)) continuous at x`;;

let CONTINUOUS_ON_LIFT_DOT = `!s. (lift o (\y. a dot y)) continuous_on s`;;

let CLOSED_INTERVAL_LEFT = `!b:real^N.
     closed {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> x$i <= b$i}`;;

let CLOSED_INTERVAL_RIGHT = `!a:real^N.
     closed {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= x$i}`;;

let CLOSED_HALFSPACE_LE = `!a:real^N b. closed {x | a dot x <= b}`;;

let CLOSED_HALFSPACE_GE = `!a:real^N b. closed {x | a dot x >= b}`;;

let CLOSED_HYPERPLANE = `!a b. closed {x | a dot x = b}`;;

let CLOSURE_HYPERPLANE = `!a b. closure {x | a dot x = b} = {x | a dot x = b}`;;

let CLOSED_STANDARD_HYPERPLANE = `!k a. closed {x:real^N | x$k = a}`;;

let CLOSED_HALFSPACE_COMPONENT_LE = `!a k. closed {x:real^N | x$k <= a}`;;

let CLOSED_HALFSPACE_COMPONENT_GE = `!a k. closed {x:real^N | x$k >= a}`;;

(* ------------------------------------------------------------------------- *)
(* Openness of halfspaces.                                                   *)
(* ------------------------------------------------------------------------- *)

let OPEN_HALFSPACE_LT = `!a b. open {x | a dot x < b}`;;

let OPEN_HALFSPACE_COMPONENT_LT = `!a k. open {x:real^N | x$k < a}`;;

let OPEN_HALFSPACE_GT = `!a b. open {x | a dot x > b}`;;

let OPEN_HALFSPACE_COMPONENT_GT = `!a k. open {x:real^N | x$k > a}`;;

let OPEN_POSITIVE_MULTIPLES = `!s:real^N->bool. open s ==> open {c % x | &0 < c /\ x IN s}`;;

let OPEN_INTERVAL_LEFT = `!b:real^N. open {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> x$i < b$i}`;;

let OPEN_INTERVAL_RIGHT = `!a:real^N. open {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < x$i}`;;

let OPEN_POSITIVE_ORTHANT = `open {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 < x$i}`;;

(* ------------------------------------------------------------------------- *)
(* Closures and interiors of halfspaces.                                     *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_HALFSPACE_LE = `!a:real^N b.
        ~(a = vec 0) ==> interior {x | a dot x <= b} = {x | a dot x < b}`;;

let INTERIOR_HALFSPACE_GE = `!a:real^N b.
        ~(a = vec 0) ==> interior {x | a dot x >= b} = {x | a dot x > b}`;;

let INTERIOR_HALFSPACE_COMPONENT_LE = `!a k. interior {x:real^N | x$k <= a} = {x | x$k < a}`;;

let INTERIOR_HALFSPACE_COMPONENT_GE = `!a k. interior {x:real^N | x$k >= a} = {x | x$k > a}`;;

let CLOSURE_HALFSPACE_LT = `!a:real^N b.
        ~(a = vec 0) ==> closure {x | a dot x < b} = {x | a dot x <= b}`;;

let CLOSURE_HALFSPACE_GT = `!a:real^N b.
        ~(a = vec 0) ==> closure {x | a dot x > b} = {x | a dot x >= b}`;;

let CLOSURE_HALFSPACE_COMPONENT_LT = `!a k. closure {x:real^N | x$k < a} = {x | x$k <= a}`;;

let CLOSURE_HALFSPACE_COMPONENT_GT = `!a k. closure {x:real^N | x$k > a} = {x | x$k >= a}`;;

let INTERIOR_HYPERPLANE = `!a b. ~(a = vec 0) ==> interior {x | a dot x = b} = {}`;;

let FRONTIER_HALFSPACE_LE = `!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x <= b} = {x | a dot x = b}`;;

let FRONTIER_HALFSPACE_GE = `!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x >= b} = {x | a dot x = b}`;;

let FRONTIER_HALFSPACE_LT = `!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x < b} = {x | a dot x = b}`;;

let FRONTIER_HALFSPACE_GT = `!a:real^N b. ~(a = vec 0 /\ b = &0)
                ==> frontier {x | a dot x > b} = {x | a dot x = b}`;;

let FRONTIER_HALFSPACE_COMPONENT_LE = `!a k. frontier {x:real^N | x$k <= a} = {x | x$k = a}`;;

let FRONTIER_HALFSPACE_COMPONENT_GE = `!a k. frontier {x:real^N | x$k >= a} = {x | x$k = a}`;;

let FRONTIER_HALFSPACE_COMPONENT_LT = `!a k. frontier {x:real^N | x$k < a} = {x | x$k = a}`;;

let FRONTIER_HALFSPACE_COMPONENT_GT = `!a k. frontier {x:real^N | x$k > a} = {x | x$k = a}`;;

let INTERIOR_STANDARD_HYPERPLANE = `!k a. interior {x:real^N | x$k = a} = {}`;;

let EMPTY_INTERIOR_LOWDIM = `!s:real^N->bool. dim(s) < dimindex(:N) ==> interior s = {}`;;

let DIM_NONEMPTY_INTERIOR = `!s:real^N->bool. ~(interior s = {}) ==> dim s = dimindex(:N)`;;

(* ------------------------------------------------------------------------- *)
(* Unboundedness of halfspaces.                                              *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_HALFSPACE_COMPONENT_LE = `!a k. ~bounded {x:real^N | x$k <= a}`;;

let UNBOUNDED_HALFSPACE_COMPONENT_GE = `!a k. ~bounded {x:real^N | x$k >= a}`;;

let UNBOUNDED_HALFSPACE_COMPONENT_LT = `!a k. ~bounded {x:real^N | x$k < a}`;;

let UNBOUNDED_HALFSPACE_COMPONENT_GT = `!a k. ~bounded {x:real^N | x$k > a}`;;

let BOUNDED_HALFSPACE_LE = `!a:real^N b. bounded {x | a dot x <= b} <=> a = vec 0 /\ b < &0`;;

let BOUNDED_HALFSPACE_GE = `!a:real^N b. bounded {x | a dot x >= b} <=> a = vec 0 /\ &0 < b`;;

let BOUNDED_HALFSPACE_LT = `!a:real^N b. bounded {x | a dot x < b} <=> a = vec 0 /\ b <= &0`;;

let BOUNDED_HALFSPACE_GT = `!a:real^N b. bounded {x | a dot x > b} <=> a = vec 0 /\ &0 <= b`;;

(* ------------------------------------------------------------------------- *)
(* Equality of continuous functions on closure and related results.          *)
(* ------------------------------------------------------------------------- *)

let FORALL_IN_INTERMEDIATE_CLOSURE = `!f:real^M->real^N s s' t.
        closed t /\ f continuous_on s' /\ s SUBSET s' /\ s' SUBSET closure s /\
        (!x. x IN s ==> f x IN t)
        ==> !x. x IN s' ==> f x IN t`;;

let FORALL_IN_INTERMEDIATE_CLOSURE_EQ = `!f s s' t.
         closed t /\ f continuous_on s' /\ s SUBSET s' /\ s' SUBSET closure s
         ==> ((!x. x IN s' ==> f x IN t) <=>
              (!x. x IN s ==> f x IN t))`;;

let CONTINUOUS_LE_ON_INTERMEDIATE_CLOSURE = `!f:real^M->real s s' a.
        (lift o f) continuous_on s' /\ s SUBSET s' /\ s' SUBSET closure s /\
        (!x. x IN s ==> f(x) <= a)
        ==> !x. x IN s' ==> f(x) <= a`;;

let CONTINUOUS_GE_ON_INTERMEDIATE_CLOSURE = `!f:real^M->real s s' a.
       (lift o f) continuous_on s' /\ s SUBSET s' /\ s' SUBSET closure s /\
        (!x. x IN s ==> a <= f(x))
        ==> !x. x IN s' ==> a <= f(x)`;;

let CONTINUOUS_CONSTANT_ON_INTERMEDIATE_CLOSURE = `!f:real^M->real^N s s' a.
        f continuous_on s' /\ s SUBSET s' /\ s' SUBSET closure s /\
        (!x. x IN s ==> f(x) = a)
        ==> !x. x IN s' ==> f(x) = a`;;

let CONTINUOUS_AGREE_ON_INTERMEDIATE_CLOSURE = `!g h:real^M->real^N s s'.
        g continuous_on s' /\ h continuous_on s' /\
        s SUBSET s' /\ s' SUBSET closure s /\
        (!x. x IN s ==> g x = h x)
        ==> !x. x IN s' ==> g x = h x`;;

let FORALL_IN_CLOSURE = `!f:real^M->real^N s t.
        closed t /\ f continuous_on (closure s) /\
        (!x. x IN s ==> f x IN t)
        ==> (!x. x IN closure s ==> f x IN t)`;;

let FORALL_IN_CLOSURE_EQ = `!f s t.
         closed t /\ f continuous_on closure s
         ==> ((!x. x IN closure s ==> f x IN t) <=>
              (!x. x IN s ==> f x IN t))`;;

let SUP_CLOSURE = `!s. sup(IMAGE drop (closure s)) = sup(IMAGE drop s)`;;

let INF_CLOSURE = `!s. inf(IMAGE drop (closure s)) = inf(IMAGE drop s)`;;

let CONTINUOUS_LE_ON_CLOSURE = `!f:real^M->real s a.
        (lift o f) continuous_on closure(s) /\ (!x. x IN s ==> f(x) <= a)
        ==> !x. x IN closure(s) ==> f(x) <= a`;;

let CONTINUOUS_GE_ON_CLOSURE = `!f:real^M->real s a.
        (lift o f) continuous_on closure(s) /\ (!x. x IN s ==> a <= f(x))
        ==> !x. x IN closure(s) ==> a <= f(x)`;;

let CONTINUOUS_CONSTANT_ON_CLOSURE = `!f:real^M->real^N s a.
        f continuous_on closure(s) /\ (!x. x IN s ==> f(x) = a)
        ==> !x. x IN closure(s) ==> f(x) = a`;;

let CONTINUOUS_AGREE_ON_CLOSURE = `!g h:real^M->real^N.
        g continuous_on closure s /\ h continuous_on closure s /\
        (!x. x IN s ==> g x = h x)
        ==> !x. x IN closure s ==> g x = h x`;;

let CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT = `!f:real^M->real^N s a.
        f continuous_on s
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x = a}`;;

let CONTINUOUS_CLOSED_PREIMAGE_CONSTANT = `!f:real^M->real^N s.
      f continuous_on s /\ closed s ==> closed {x | x IN s /\ f(x) = a}`;;

(* ------------------------------------------------------------------------- *)
(* Theorems relating continuity and uniform continuity to closures.          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_INTERMEDIATE_CLOSURE = `!f:real^M->real^N s t.
        t SUBSET closure s /\
        (!x. x IN t ==> (f --> f x) (at x within s))
        ==> f continuous_on t`;;

let CONTINUOUS_ON_INTERMEDIATE_CLOSURE_EQ = `!f:real^M->real^N s t.
        s SUBSET t /\ t SUBSET closure s
        ==> (f continuous_on t <=>
             !x. x IN t ==> (f --> f x) (at x within s))`;;

let CONTINUOUS_ON_CLOSURE = `!f:real^M->real^N s.
        f continuous_on closure s <=>
        !x e. x IN closure s /\ &0 < e
              ==> ?d. &0 < d /\
                      !y. y IN s /\ dist(y,x) < d ==> dist(f y,f x) < e`;;

let CONTINUOUS_ON_CLOSURE_SEQUENTIALLY = `!f:real^M->real^N s.
        f continuous_on closure s <=>
        !x a. a IN closure s /\ (!n. x n IN s) /\ (x --> a) sequentially
              ==> ((f o x) --> f a) sequentially`;;

let CONTINUOUS_ON_INTERMEDIATE_CLOSURE_POINTWISE = `!f:real^M->real^N s t.
        s SUBSET t /\ t SUBSET closure s /\
        (!x. x IN t ==> f continuous_on (x INSERT s))
        ==> f continuous_on t`;;

let FUNCTION_EXTENSION_POINTWISE = `!f:real^M->real^N s t u.
        s SUBSET t /\ t SUBSET closure s /\
        (!x. x IN t ==> ?g. g continuous_on (x INSERT s) /\
                            IMAGE g (x INSERT s) SUBSET u /\
                            (!x. x IN s ==> g x = f x))
        ==> ?g. g continuous_on t /\
                IMAGE g t SUBSET u /\
                (!x. x IN s ==> g x = f x)`;;

let FUNCTION_EXTENSION_POINTWISE_ALT = `!f:real^M->real^N s t u.
        s SUBSET t /\ t SUBSET closure s /\ closed u /\
        f continuous_on s /\ IMAGE f s SUBSET u /\
        (!x. x IN t DIFF s ==> ?l. (f --> l) (at x within s))
        ==> ?g. g continuous_on t /\
                IMAGE g t SUBSET u /\
                (!x. x IN s ==> g x = f x)`;;

let UNIFORMLY_CONTINUOUS_ON_CLOSURE = `!f:real^M->real^N s.
        f uniformly_continuous_on s /\ f continuous_on closure s
        ==> f uniformly_continuous_on closure s`;;

(* ------------------------------------------------------------------------- *)
(* Continuity properties for square roots. We get other forms of this        *)
(* later (transcendentals.ml and realanalysis.ml) but it's nice to have      *)
(* them around earlier.                                                      *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_LIFT_SQRT = `!s. (lift o sqrt o drop) continuous_on s`;;

let CONTINUOUS_AT_SQRT = `!a. (lift o sqrt o drop) continuous (at a)`;;

let CONTINUOUS_WITHIN_LIFT_SQRT = `!a s. (lift o sqrt o drop) continuous (at a within s)`;;

let CONTINUOUS_WITHIN_SQRT_COMPOSE = `!f s a:real^N.
        (\x. lift(f x)) continuous (at a within s)
        ==> (\x. lift(sqrt(f x))) continuous (at a within s)`;;

let CONTINUOUS_AT_SQRT_COMPOSE = `!f a:real^N.
        (\x. lift(f x)) continuous (at a)
        ==> (\x. lift(sqrt(f x))) continuous (at a)`;;

let CONTINUOUS_ON_LIFT_SQRT_COMPOSE = `!f:real^N->real s.
        (lift o f) continuous_on s
        ==> (\x. lift(sqrt(f x))) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy continuity, and the extension of functions to closures.            *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_IMP_CAUCHY_CONTINUOUS = `!f:real^M->real^N s.
        f uniformly_continuous_on s
        ==> (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))`;;

let CONTINUOUS_CLOSED_IMP_CAUCHY_CONTINUOUS = `!f:real^M->real^N s.
        f continuous_on s /\ closed s
        ==> (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))`;;

let CAUCHY_CONTINUOUS_EXTENDS_TO_CLOSURE = `!f:real^M->real^N s.
        (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))
        ==> ?g. g continuous_on closure s /\ (!x. x IN s ==> g x = f x)`;;

let UNIFORMLY_CONTINUOUS_EXTENDS_TO_CLOSURE = `!f:real^M->real^N s.
   f uniformly_continuous_on s
   ==> ?g. g uniformly_continuous_on closure s /\ (!x. x IN s ==> g x = f x) /\
           !h. h continuous_on closure s /\ (!x. x IN s ==> h x = f x)
               ==> !x. x IN closure s ==> h x = g x`;;

let CAUCHY_CONTINUOUS_IMP_CONTINUOUS = `!f:real^M->real^N s.
        (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))
        ==> f continuous_on s`;;

let BOUNDED_UNIFORMLY_CONTINUOUS_IMAGE = `!f:real^M->real^N s.
        f uniformly_continuous_on s /\ bounded s ==> bounded(IMAGE f s)`;;

let LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_ON = `!f:real^M->real^N s.
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> f uniformly_continuous_on s`;;

let BOUNDED_LIPSCHITZ_IMAGE = `!f:real^M->real^N s.
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)) /\
        bounded s
        ==> bounded (IMAGE f s)`;;

let LIPSCHITZ_IMP_CONTINUOUS_ON = `!f:real^M->real^N s.
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> f continuous_on s`;;

let LIPSCHITZ_LIM = `!f:num->real^M->real^N g s b.
      (!n x y. x IN s /\ y IN s ==> norm(f n x - f n y) <= b * norm(x - y)) /\
      (!x. x IN s ==> ((\n. f n x) --> g x) sequentially)
      ==> !x y. x IN s /\ y IN s ==> norm(g x - g y) <= b * norm(x - y)`;;

let LIPSCHITZ_ON_SUP = `!P:(real^N->real^1)->bool B s.
        &0 <= B /\
        (!f. P f
             ==> !x y. x IN s /\ y IN s
                       ==> norm(f x - f y) <= B * norm(x - y)) /\
        (!x. x IN s ==> ?C. !f. P f ==> drop(f x) <= C)
        ==> !x y. x IN s /\ y IN s
                  ==> norm(lift(sup {drop(f x) | P f}) -
                           lift(sup {drop(f y) | P f}))
                      <= B * norm(x - y)`;;

let LIPSCHITZ_ON_INF = `!P:(real^N->real^1)->bool B s.
        &0 <= B /\
        (!f. P f
             ==> !x y. x IN s /\ y IN s
                       ==> norm(f x - f y) <= B * norm(x - y)) /\
        (!x. x IN s ==> ?C. !f. P f ==> C <= drop(f x))
        ==> !x y. x IN s /\ y IN s
                  ==> norm(lift(inf {drop(f x) | P f}) -
                           lift(inf {drop(f y) | P f}))
                      <= B * norm(x - y)`;;

(* ------------------------------------------------------------------------- *)
(* Occasionally useful invariance properties.                                *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_COMPOSE_EQ = `!f:real^M->real^N g:real^M->real^M h:real^M->real^M.
        g continuous at x /\ h continuous at (g x) /\
        (!y. g(h y) = y) /\ h(g x) = x
        ==> (f continuous at (g x) <=> (\x. f(g x)) continuous at x)`;;

let CONTINUOUS_AT_TRANSLATION = `!a z f:real^M->real^N.
      f continuous at (a + z) <=> (\x. f(a + x)) continuous at z`;;

add_translation_invariants [CONTINUOUS_AT_TRANSLATION];;

let CONTINUOUS_AT_LINEAR_IMAGE = `!h:real^M->real^M z f:real^M->real^N.
        linear h /\ (!x. norm(h x) = norm x)
        ==> (f continuous at (h z) <=> (\x. f(h x)) continuous at z)`;;

add_linear_invariants [CONTINUOUS_AT_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Interior of an injective image.                                           *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_IMAGE_SUBSET = `!f:real^M->real^N s.
       (!x. f continuous at x) /\ (!x y. f x = f y ==> x = y)
       ==> interior(IMAGE f s) SUBSET IMAGE f (interior s)`;;

(* ------------------------------------------------------------------------- *)
(* Making a continuous function avoid some value in a neighbourhood.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_AVOID = `!f:real^M->real^N x s a.
        f continuous (at x within s) /\ x IN s /\  ~(f x = a)
        ==> ?e. &0 < e /\ !y. y IN s /\ dist(x,y) < e ==> ~(f y = a)`;;

let CONTINUOUS_AT_AVOID = `!f:real^M->real^N x a.
        f continuous (at x) /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. dist(x,y) < e ==> ~(f y = a)`;;

let CONTINUOUS_ON_AVOID = `!f:real^M->real^N x s a.
        f continuous_on s /\ x IN s /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. y IN s /\ dist(x,y) < e ==> ~(f y = a)`;;

let CONTINUOUS_ON_OPEN_AVOID = `!f:real^M->real^N x s a.
        f continuous_on s /\ open s /\ x IN s /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. dist(x,y) < e ==> ~(f y = a)`;;

(* ------------------------------------------------------------------------- *)
(* Proving a function is constant by proving open-ness of level set.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_LEVELSET_OPEN_IN_CASES = `!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open_in (subtopology euclidean s) {x | x IN s /\ f x = a}
        ==> (!x. x IN s ==> ~(f x = a)) \/ (!x. x IN s ==> f x = a)`;;

let CONTINUOUS_LEVELSET_OPEN_IN = `!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open_in (subtopology euclidean s) {x | x IN s /\ f x = a} /\
        (?x. x IN s /\ f x = a)
        ==> (!x. x IN s ==> f x = a)`;;

let CONTINUOUS_LEVELSET_OPEN = `!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open {x | x IN s /\ f x = a} /\
        (?x. x IN s /\ f x = a)
        ==> (!x. x IN s ==> f x = a)`;;

(* ------------------------------------------------------------------------- *)
(* Some arithmetical combinations (more to prove).                           *)
(* ------------------------------------------------------------------------- *)

let OPEN_SCALING = `!s:real^N->bool c. ~(c = &0) /\ open s ==> open(IMAGE (\x. c % x) s)`;;

let OPEN_SCALING_EQ = `!s:real^N->bool c.
        open(IMAGE (\x. c % x) s) <=> (c = &0 ==> s = {}) /\ open s`;;

let OPEN_NEGATIONS = `!s:real^N->bool. open s ==> open (IMAGE (--) s)`;;

let OPEN_TRANSLATION = `!s a:real^N. open s ==> open(IMAGE (\x. a + x) s)`;;

let OPEN_TRANSLATION_EQ = `!a s. open (IMAGE (\x:real^N. a + x) s) <=> open s`;;

add_translation_invariants [OPEN_TRANSLATION_EQ];;

let OPEN_AFFINITY_EQ = `!s m c:real^N.
        open(IMAGE (\x. m % x + c) s) <=> (m = &0 ==> s = {}) /\ open s`;;

let OPEN_AFFINITY = `!s m c:real^N.
        open s /\ (m = &0 ==> s = {}) ==> open(IMAGE (\x. m % x + c) s)`;;

let INTERIOR_TRANSLATION = `!a:real^N s.
    interior (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (interior s)`;;

add_translation_invariants [INTERIOR_TRANSLATION];;

let OPEN_SUMS = `!s t:real^N->bool.
        open s \/ open t ==> open {x + y | x IN s /\ y IN t}`;;

(* ------------------------------------------------------------------------- *)
(* Upper and lower hemicontinuous functions, relation in the case of         *)
(* preimage map to open and closed maps, and fact that upper and lower       *)
(* hemicontinuity together imply continuity in the sense of the Hausdorff    *)
(* metric (at points where the function gives a bounded and nonempty set).   *)
(* ------------------------------------------------------------------------- *)

let UPPER_HEMICONTINUOUS = `!f:real^M->real^N->bool t s.
        (!x. x IN s ==> f(x) SUBSET t)
        ==> ((!u. open_in (subtopology euclidean t) u
                  ==> open_in (subtopology euclidean s)
                              {x | x IN s /\ f(x) SUBSET u}) <=>
             (!u. closed_in (subtopology euclidean t) u
                  ==> closed_in (subtopology euclidean s)
                                {x | x IN s /\ ~(f(x) INTER u = {})}))`;;

let LOWER_HEMICONTINUOUS = `!f:real^M->real^N->bool t s.
        (!x. x IN s ==> f(x) SUBSET t)
        ==> ((!u. closed_in (subtopology euclidean t) u
                  ==> closed_in (subtopology euclidean s)
                                {x | x IN s /\ f(x) SUBSET u}) <=>
             (!u. open_in (subtopology euclidean t) u
                  ==> open_in (subtopology euclidean s)
                              {x | x IN s /\ ~(f(x) INTER u = {})}))`;;

let OPEN_MAP_IFF_LOWER_HEMICONTINUOUS_PREIMAGE = `!f:real^M->real^N s t.
        IMAGE f s SUBSET t
        ==> ((!u. open_in (subtopology euclidean s) u
                  ==> open_in (subtopology euclidean t) (IMAGE f u)) <=>
             (!u. closed_in (subtopology euclidean s) u
                      ==> closed_in (subtopology euclidean t)
                                    {y | y IN t /\
                                         {x | x IN s /\ f x = y} SUBSET u}))`;;

let CLOSED_MAP_IFF_UPPER_HEMICONTINUOUS_PREIMAGE = `!f:real^M->real^N s t.
        IMAGE f s SUBSET t
        ==> ((!u. closed_in (subtopology euclidean s) u
                  ==> closed_in (subtopology euclidean t) (IMAGE f u)) <=>
             (!u. open_in (subtopology euclidean s) u
                  ==> open_in (subtopology euclidean t)
                              {y | y IN t /\
                                   {x | x IN s /\ f x = y} SUBSET u}))`;;

let UPPER_LOWER_HEMICONTINUOUS_EXPLICIT = `!f:real^M->real^N->bool t s.
      (!x. x IN s ==> f(x) SUBSET t) /\
      (!u. open_in (subtopology euclidean t) u
           ==> open_in (subtopology euclidean s)
                       {x | x IN s /\ f(x) SUBSET u}) /\
      (!u. closed_in (subtopology euclidean t) u
           ==> closed_in (subtopology euclidean s)
                         {x | x IN s /\ f(x) SUBSET u})
      ==> !x e. x IN s /\ &0 < e /\ bounded(f x) /\ ~(f x = {})
                ==> ?d. &0 < d /\
                        !x'. x' IN s /\ dist(x,x') < d
                             ==> (!y. y IN f x
                                      ==> ?y'. y' IN f x' /\ dist(y,y') < e) /\
                                 (!y'. y' IN f x'
                                       ==> ?y. y IN f x /\ dist(y',y) < e)`;;

(* ------------------------------------------------------------------------- *)
(* Connected components, considered as a "connectedness" relation or a set.  *)
(* ------------------------------------------------------------------------- *)

let connected_component = new_definition
 `connected_component s x y <=>
        ?t. connected t /\ t SUBSET s /\ x IN t /\ y IN t`;;

let CONNECTED_COMPONENT_OF_EUCLIDEAN = `!s x:real^N.
     connected_component_of (subtopology euclidean s) x =
     connected_component s x`;;

let CONNECTED_COMPONENT_IN = `!s x y. connected_component s x y ==> x IN s /\ y IN s`;;

let CONNECTED_COMPONENT_REFL = `!s x:real^N. x IN s ==> connected_component s x x`;;

let CONNECTED_COMPONENT_REFL_EQ = `!s x:real^N. connected_component s x x <=> x IN s`;;

let CONNECTED_COMPONENT_SYM = `!s x y:real^N. connected_component s x y ==> connected_component s y x`;;

let CONNECTED_COMPONENT_TRANS = `!s x y:real^N.
    connected_component s x y /\ connected_component s y z
    ==> connected_component s x z`;;

let CONNECTED_COMPONENT_OF_SUBSET = `!s t x. s SUBSET t /\ connected_component s x y
           ==> connected_component t x y`;;

let CONNECTED_COMPONENT_SET = `!s x. connected_component s x =
            { y | ?t. connected t /\ t SUBSET s /\ x IN t /\ y IN t}`;;

let CONNECTED_COMPONENT_UNIONS = `!s x. connected_component s x =
                UNIONS {t | connected t /\ x IN t /\ t SUBSET s}`;;

let CONNECTED_COMPONENT_SUBSET = `!s x. (connected_component s x) SUBSET s`;;

let CONNECTED_CONNECTED_COMPONENT_SET = `!s. connected s <=> !x:real^N. x IN s ==> connected_component s x = s`;;

let CONNECTED_COMPONENT_UNIV = `!x. connected_component(:real^N) x = (:real^N)`;;

let CONNECTED_COMPONENT_EQ_UNIV = `!s x. connected_component s x = (:real^N) <=> s = (:real^N)`;;

let CONNECTED_COMPONENT_EQ_SELF = `!s x. connected s /\ x IN s ==> connected_component s x = s`;;

let CONNECTED_IFF_CONNECTED_COMPONENT = `!s. connected s <=>
          !x y. x IN s /\ y IN s ==> connected_component s x y`;;

let CONNECTED_IMP_CONNECTED_COMPONENT = `!s a b:real^N.
     connected s /\ a IN s /\ b IN s ==> connected_component s a b`;;

let CONNECTED_COMPONENT_MAXIMAL = `!s t x:real^N.
        x IN t /\ connected t /\ t SUBSET s
        ==> t SUBSET (connected_component s x)`;;

let CONNECTED_COMPONENT_MONO = `!s t x. s SUBSET t
           ==> (connected_component s x) SUBSET (connected_component t x)`;;

let CONNECTED_CONNECTED_COMPONENT = `!s x. connected(connected_component s x)`;;

let CONNECTED_COMPONENT_EQ_EMPTY = `!s x:real^N. connected_component s x = {} <=> ~(x IN s)`;;

let CONNECTED_COMPONENT_EMPTY = `!x. connected_component {} x = {}`;;

let CONNECTED_COMPONENT_EQ = `!s x y. y IN connected_component s x
           ==> (connected_component s y = connected_component s x)`;;

let CLOSED_CONNECTED_COMPONENT = `!s x:real^N. closed s ==> closed(connected_component s x)`;;

let CONNECTED_COMPONENT_DISJOINT = `!s a b. DISJOINT (connected_component s a) (connected_component s b) <=>
             ~(a IN connected_component s b)`;;

let CONNECTED_COMPONENT_NONOVERLAP = `!s a b:real^N.
        (connected_component s a) INTER (connected_component s b) = {} <=>
        ~(a IN s) \/ ~(b IN s) \/
        ~(connected_component s a = connected_component s b)`;;

let CONNECTED_COMPONENT_OVERLAP = `!s a b:real^N.
        ~((connected_component s a) INTER (connected_component s b) = {}) <=>
        a IN s /\ b IN s /\
        connected_component s a = connected_component s b`;;

let CONNECTED_COMPONENT_SYM_EQ = `!s x y. connected_component s x y <=> connected_component s y x`;;

let CONNECTED_COMPONENT_EQ_EQ = `!s x y:real^N.
        connected_component s x = connected_component s y <=>
           ~(x IN s) /\ ~(y IN s) \/
           x IN s /\ y IN s /\ connected_component s x y`;;

let CONNECTED_EQ_CONNECTED_COMPONENT_EQ = `!s. connected s <=>
       !x y. x IN s /\ y IN s
             ==> connected_component s x = connected_component s y`;;

let CONNECTED_COMPONENT_IDEMP = `!s x:real^N. connected_component (connected_component s x) x =
                connected_component s x`;;

let CONNECTED_COMPONENT_UNIQUE = `!s c x:real^N.
        x IN c /\ c SUBSET s /\ connected c /\
        (!c'. x IN c' /\ c' SUBSET s /\ connected c'
              ==> c' SUBSET c)
        ==> connected_component s x = c`;;

let JOINABLE_CONNECTED_COMPONENT_EQ = `!s t x y:real^N.
        connected t /\ t SUBSET s /\
        ~(connected_component s x INTER t = {}) /\
        ~(connected_component s y INTER t = {})
        ==> connected_component s x = connected_component s y`;;

let CONNECTED_COMPONENT_TRANSLATION = `!a s x. connected_component (IMAGE (\x. a + x) s) (a + x) =
                IMAGE (\x. a + x) (connected_component s x)`;;

add_translation_invariants [CONNECTED_COMPONENT_TRANSLATION];;

let CONNECTED_COMPONENT_LINEAR_IMAGE = `!f s x. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> connected_component (IMAGE f s) (f x) =
               IMAGE f (connected_component s x)`;;

add_linear_invariants [CONNECTED_COMPONENT_LINEAR_IMAGE];;

let UNIONS_CONNECTED_COMPONENT = `!s:real^N->bool. UNIONS {connected_component s x |x| x IN s} = s`;;

let COMPLEMENT_CONNECTED_COMPONENT_UNIONS = `!s x:real^N.
     s DIFF connected_component s x =
     UNIONS({connected_component s y | y | y IN s} DELETE
            (connected_component s x))`;;

let CLOSED_IN_CONNECTED_COMPONENT = `!s x:real^N. closed_in (subtopology euclidean s) (connected_component s x)`;;

let OPEN_IN_CONNECTED_COMPONENT = `!s x:real^N.
        FINITE {connected_component s x |x| x IN s}
        ==> open_in (subtopology euclidean s) (connected_component s x)`;;

let CONNECTED_COMPONENT_EQUIVALENCE_RELATION = `!R s:real^N->bool.
        (!x y. R x y ==> R y x) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!a. a IN s
             ==> ?t. open_in (subtopology euclidean s) t /\ a IN t /\
                     !x. x IN t ==> R a x)
        ==> !a b. connected_component s a b ==> R a b`;;

let CONNECTED_COMPONENT_INTERMEDIATE_SUBSET = `!t u a:real^N.
        connected_component u a SUBSET t /\ t SUBSET u
        ==> connected_component t a = connected_component u a`;;

let CONNECTED_UNIONS_STRONG = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> connected s) /\
        ~(UNIONS f INTER INTERS {closure s | s IN f} = {})
        ==> connected(UNIONS f)`;;

let NOT_CONNECTED_COMPONENT_SEPARATED_UNION = `!s t x y:real^N.
        s INTER closure t = {} /\ t INTER closure s = {} /\ x IN s /\ y IN t
        ==> ~connected_component (s UNION t) x y`;;

let CONNECTED_COMPONENT_SEPARATED_UNION = `!s t x:real^N.
        s INTER closure t = {} /\ t INTER closure s = {}
        ==> connected_component (s UNION t) x =
            if x IN s then connected_component s x
            else if x IN t then connected_component t x
            else {}`;;

let CONNECTED_CONNECTED_DIFF = `!s t:real^N->bool.
        connected s /\ s SUBSET closure(s DIFF t) /\
        (!x. x IN s
             ==> ?u. x IN u /\ open_in (subtopology euclidean s) u /\
                     connected(u DIFF t))
        ==> connected(s DIFF t)`;;

let CONNECTED_COMPONENT_FINITE = `!s x:real^N.
        FINITE s ==> connected_component s x = if x IN s then {x} else {}`;;

(* ------------------------------------------------------------------------- *)
(* The set of connected components of a set.                                 *)
(* ------------------------------------------------------------------------- *)

let components = new_definition
  `components s = {connected_component s x | x | x:real^N IN s}`;;

let EUCLIDEAN_CONNECTED_COMPONENTS_OF = `!s:real^N->bool.
        connected_components_of (subtopology euclidean s) = components s`;;

let PAIRWISE_SEPARATED_COMPONENTS = `!s:real^N->bool. pairwise (separated_in euclidean) (components s)`;;

let COMPONENTS_TRANSLATION = `!a s. components(IMAGE (\x. a + x) s) =
   IMAGE (IMAGE (\x. a + x)) (components s)`;;

add_translation_invariants [COMPONENTS_TRANSLATION];;

let COMPONENTS_LINEAR_IMAGE = `!f s. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> components(IMAGE f s) = IMAGE (IMAGE f) (components s)`;;

add_linear_invariants [COMPONENTS_LINEAR_IMAGE];;

let IN_COMPONENTS = `!u:real^N->bool s. s IN components u
    <=> ?x. x IN u /\ s = connected_component u x`;;

let CONNECTED_COMPONENTS = `!s a b:real^N.
        connected_component s a b <=>
        ?c. c IN components s /\ a IN c /\ b IN c`;;

let UNIONS_COMPONENTS = `!u:real^N->bool. u = UNIONS (components u)`;;

let PAIRWISE_DISJOINT_COMPONENTS = `!u:real^N->bool. pairwise DISJOINT (components u)`;;

let IN_COMPONENTS_NONEMPTY = `!s c. c IN components s ==> ~(c = {})`;;

let IN_COMPONENTS_SUBSET = `!s c. c IN components s ==> c SUBSET s`;;

let IN_COMPONENTS_CONNECTED = `!s c. c IN components s ==> connected c`;;

let CONNECTED_COMPONENT_IN_COMPONENTS = `!s x:real^N. connected_component s x IN components s <=> x IN s`;;

let IN_COMPONENTS_MAXIMAL = `!s c:real^N->bool.
        c IN components s <=>
        ~(c = {}) /\ c SUBSET s /\ connected c /\
        !c'. ~(c' = {}) /\ c SUBSET c' /\ c' SUBSET s /\ connected c'
             ==> c' = c`;;

let JOINABLE_COMPONENTS_EQ = `!s t c1 c2.
        connected t /\ t SUBSET s /\
        c1 IN components s /\ c2 IN components s /\
        ~(c1 INTER t = {}) /\ ~(c2 INTER t = {})
        ==> c1 = c2`;;

let CLOSED_IN_COMPONENT = `!s c:real^N->bool.
        c IN components s ==> closed_in (subtopology euclidean s) c`;;

let CLOSED_COMPONENTS = `!s c. closed s /\ c IN components s ==> closed c`;;

let COMPACT_CONNECTED_COMPONENT = `!s a:real^N. compact s ==> compact(connected_component s a)`;;

let COMPACT_COMPONENTS = `!s c:real^N->bool. compact s /\ c IN components s ==> compact c`;;

let CONTINUOUS_ON_COMPONENTS_GEN = `!f:real^M->real^N s.
        (!c. c IN components s
             ==> open_in (subtopology euclidean s) c /\ f continuous_on c)
        ==> f continuous_on s`;;

let CONTINUOUS_ON_COMPONENTS_FINITE = `!f:real^M->real^N s.
        FINITE(components s) /\
        (!c. c IN components s ==> f continuous_on c)
        ==> f continuous_on s`;;

let COMPONENTS_NONOVERLAP = `!s c c'. c IN components s /\ c' IN components s
            ==> (c INTER c' = {} <=> ~(c = c'))`;;

let COMPONENTS_EQ = `!s c c'. c IN components s /\ c' IN components s
            ==> (c = c' <=> ~(c INTER c' = {}))`;;

let COMPONENTS_EQ_EMPTY = `!s. components s = {} <=> s = {}`;;

let COMPONENTS_EMPTY = `components {} = {}`;;

let CONNECTED_EQ_CONNECTED_COMPONENTS_EQ = `!s. connected s <=>
       !c c'. c IN components s /\ c' IN components s ==> c = c'`;;

let COMPONENTS_EQ_SING = `(!s:real^N->bool. components s = {s} <=> connected s /\ ~(s = {}))`
and COMPONENTS_EQ_SING_EXISTS = `(!s:real^N->bool. (?a. components s = {a}) <=> connected s /\ ~(s = {}))`;;

let CONNECTED_EQ_COMPONENTS_SING = `!s:real^N->bool. connected s <=> s = {} \/ components s = {s}`;;

let CONNECTED_EQ_COMPONENTS_SING_EXISTS = `!s:real^N->bool. connected s <=> s = {} \/ (?a. components s = {a})`;;

let CONNECTED_EQ_CARD_COMPONENTS = `!s:real^N->bool.
      connected s <=> FINITE(components s) /\ CARD(components s) <= 1`;;

let COMPONENTS_UNIV = `components(:real^N) = {(:real^N)}`;;

let CONNECTED_EQ_COMPONENTS_SUBSET_SING = `!s:real^N->bool. connected s <=> components s SUBSET {s}`;;

let CONNECTED_EQ_COMPONENTS_SUBSET_SING_EXISTS = `!s:real^N->bool. connected s <=> ?a. components s SUBSET {a}`;;

let IN_COMPONENTS_SELF = `!s:real^N->bool. s IN components s <=> connected s /\ ~(s = {})`;;

let COMPONENTS_MAXIMAL = `!s t c:real^N->bool.
     c IN components s /\ connected t /\ t SUBSET s /\ ~(c INTER t = {})
     ==> t SUBSET c`;;

let IN_COMPONENTS_MAXIMAL_ALT = `!s c:real^N->bool.
        c IN components s <=>
        ~(c = {}) /\ c SUBSET s /\ connected c /\
        (!c'. ~(c INTER c' = {}) /\ c' SUBSET s /\ connected c'
              ==> c' SUBSET c)`;;

let COMPONENTS_UNIQUE = `!s:real^N->bool k.
        UNIONS k = s /\
        (!c. c IN k
             ==> connected c /\ ~(c = {}) /\
                 !c'. connected c' /\ c SUBSET c' /\ c' SUBSET s ==> c' = c)
        ==> components s = k`;;

let COMPONENTS_UNIQUE_EQ = `!s:real^N->bool k.
        components s = k <=>
        UNIONS k = s /\
        (!c. c IN k
             ==> connected c /\ ~(c = {}) /\
                 !c'. connected c' /\ c SUBSET c' /\ c' SUBSET s ==> c' = c)`;;

let COMPONENTS_UNIQUE_2 = `!s c1 c2:real^N->bool.
        connected c1 /\ connected c2 /\ c1 UNION c2 = s /\ ~connected s
        ==> components s = {c1,c2}`;;

let EXISTS_COMPONENT_SUPERSET = `!s t:real^N->bool.
        t SUBSET s /\ ~(s = {}) /\ connected t
        ==> ?c. c IN components s /\ t SUBSET c`;;

let COMPONENTS_INTERMEDIATE_SUBSET = `!s t u:real^N->bool.
        s IN components u /\ s SUBSET t /\ t SUBSET u
        ==> s IN components t`;;

let FINITE_COMPONENTS_FINITE = `!s:real^N->bool. FINITE s ==> FINITE(components s)`;;

let COMPONENTS_FINITE = `!s:real^N->bool. FINITE s ==> components s = {{x} | x IN s}`;;

let COMPONENTS_INTER_COMPONENTS = `!s t c d:real^N->bool.
        c IN components s /\ d IN components (t INTER c)
        ==> d IN components(t INTER s)`;;

let IN_COMPONENTS_UNIONS_COMPLEMENT = `!s c:real^N->bool.
        c IN components s
        ==> s DIFF c = UNIONS(components s DELETE c)`;;

let CONNECTED_SUBSET_CLOPEN = `!u s c:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) s /\
        connected c /\ c SUBSET u /\ ~(c INTER s = {})
        ==> c SUBSET s`;;

let CLOPEN_UNIONS_COMPONENTS = `!u s:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) s
        ==> ?k. k SUBSET components u /\ s = UNIONS k`;;

let CLOPEN_IN_COMPONENTS = `!u s:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) s /\
        connected s /\ ~(s = {})
        ==> s IN components u`;;

let CONNECTED_UNIONS_PAIRWISE = `!f. (!s:real^N->bool. s IN f ==> connected s) /\
       pairwise (\s t. ~(s = {}) /\ ~(t = {}) ==> ~(s INTER t = {})) f
       ==> connected(UNIONS f)`;;

let COMPONENTS_SEPARATED_UNION = `!s t:real^N->bool.
        s INTER closure t = {} /\ t INTER closure s = {}
        ==> components(s UNION t) = components(s) UNION components(t)`;;

let COMPONENTS_COMPLEMENT_FRONTIER = `!s. components((:real^N) DIFF frontier s) =
       components(interior s) UNION components ((:real^N) DIFF closure s)`;;

let CARD_LE_COMPONENTS_UNION = `!s t:real^N->bool.
        components(s UNION t) <=_c components(s) +_c components(t)`;;

let FINITE_COMPONENTS_UNION = `!s t:real^N->bool.
        FINITE(components s) /\ FINITE(components t)
        ==> FINITE(components(s UNION t))`;;

let COUNTABLE_COMPONENTS_UNION = `!s t:real^N->bool.
        COUNTABLE(components s) /\ COUNTABLE(components t)
        ==> COUNTABLE(components(s UNION t))`;;

let MINIMAL_SEPARATING_COMMON_COMPONENT_FRONTIER_ELEMENTWISE = `!s c1 c2 a b t.
        c1 IN components((:real^N) DIFF s) /\
        c2 IN components((:real^N) DIFF s) /\
        a IN c1 /\ b IN c2 /\ frontier c1 = s /\ frontier c2 = s /\
        t PSUBSET s
        ==> connected_component ((:real^N) DIFF t) a b`;;

let MINIMAL_SEPARATING_COMMON_COMPONENT_FRONTIER = `!s t. t PSUBSET s /\ ~(s = (:real^N)) /\
         (!c. c IN components((:real^N) DIFF s) ==> frontier c = s)
         ==> connected((:real^N) DIFF t)`;;

(* ------------------------------------------------------------------------- *)
(* Continuity implies uniform continuity on a compact domain.                *)
(* ------------------------------------------------------------------------- *)

let COMPACT_UNIFORMLY_EQUICONTINUOUS = `!(fs:(real^M->real^N)->bool) s.
     (!x e. x IN s /\ &0 < e
            ==> ?d. &0 < d /\
                    (!f x'. f IN fs /\ x' IN s /\ dist (x',x) < d
                            ==> dist (f x',f x) < e)) /\
     compact s
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !f x x'. f IN fs /\ x IN s /\ x' IN s /\ dist (x',x) < d
                              ==> dist(f x',f x) < e`;;

let COMPACT_UNIFORMLY_CONTINUOUS = `!f:real^M->real^N s.
        f continuous_on s /\ compact s ==> f uniformly_continuous_on s`;;

let CONTINUOUS_EQ_CAUCHY_CONTINUOUS_CLOSED = `!f:real^M->real^N s.
        closed s
        ==> (f continuous_on s <=>
             !x. cauchy x /\ (!n. x n IN s) ==> cauchy(f o x))`;;

let UNIFORMLY_CONTINUOUS_EQ_CAUCHY_CONTINUOUS_BOUNDED = `!f:real^M->real^N s.
        bounded s
        ==> (f uniformly_continuous_on s <=>
             !x. cauchy x /\ (!n. x n IN s) ==> cauchy(f o x))`;;

let CAUCHY_CONTINUOUS_EXTENDS_TO_CAUCHY_CONTINUOUS_CLOSURE = `!f:real^M->real^N s.
        (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x))
        ==> ?g. (!x. cauchy x /\ (!n. (x n) IN closure s) ==> cauchy(g o x)) /\
                (!x. x IN s ==> g x = f x)`;;

let CAUCHY_CONTINUOUS_EQ_EXTENDS_TO_CLOSURE = `!f:real^M->real^N s.
        (!x. cauchy x /\ (!n. (x n) IN s) ==> cauchy(f o x)) <=>
        ?g. g continuous_on closure s /\ (!x. x IN s ==> g x = f x)`;;

let UNIFORMLY_CONTINUOUS_ON_UNION = `!f:real^M->real^N s t.
        bounded s /\ bounded t /\
        f uniformly_continuous_on t /\
        f continuous_on (closure s UNION t)
        ==> f uniformly_continuous_on (s UNION t)`;;

(* ------------------------------------------------------------------------- *)
(* A uniformly convergent limit of continuous functions is continuous.       *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_UNIFORM_LIMIT = `!net f:A->real^M->real^N g s.
        ~(trivial_limit net) /\
        eventually (\n. (f n) continuous_on s) net /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN s ==> norm(f n x - g x) < e) net)
        ==> g continuous_on s`;;

let CONTINUOUS_UNIFORMLY_CAUCHY_LIMIT = `!f:num->real^M->real^N s.
        eventually (\n. f n continuous_on s) sequentially /\
        (!e. &0 < e
            ==> ?N. !m n x. N <= m /\ N <= n /\ x IN s
                            ==> dist (f m x,f n x) < e)
        ==> ?g. g continuous_on s /\
                (!x. x IN s ==> ((\n. f n x) --> g x) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* Topological stuff lifted from and dropped to R                            *)
(* ------------------------------------------------------------------------- *)

let OPEN_LIFT = `!s. open(IMAGE lift s) <=>
        !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`;;

let LIMPT_APPROACHABLE_LIFT = `!x s. (lift x) limit_point_of (IMAGE lift s) <=>
         !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e`;;

let CLOSED_LIFT = `!s. closed (IMAGE lift s) <=>
        !x. (!e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e)
            ==> x IN s`;;

let CONTINUOUS_AT_LIFT_RANGE = `!f x. (lift o f) continuous (at x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            (!x'. norm(x' - x) < d
                                  ==> abs(f x' - f x) < e)`;;

let CONTINUOUS_ON_LIFT_RANGE = `!f s. (lift o f) continuous_on s <=>
         !x. x IN s
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             (!x'. x' IN s /\ norm(x' - x) < d
                                   ==> abs(f x' - f x) < e)`;;

let CONTINUOUS_LIFT_NORM_COMPOSE = `!net f:A->real^N.
        f continuous net
        ==> (\x. lift(norm(f x))) continuous net`;;

let CONTINUOUS_ON_LIFT_NORM_COMPOSE = `!f:real^M->real^N s.
        f continuous_on s
        ==> (\x. lift(norm(f x))) continuous_on s`;;

let CONTINUOUS_AT_LIFT_NORM = `!x. (lift o norm) continuous (at x)`;;

let CONTINUOUS_ON_LIFT_NORM = `!s. (lift o norm) continuous_on s`;;

let PROPER_MAP_NORM_SIMPLE = `!k. compact k ==> compact {x:real^N | lift(norm x) IN k}`;;

let PROPER_MAP_NORM = `!s t. closed s
         ==> !k. k SUBSET t /\ compact k
                 ==> compact {x:real^N | x IN s /\ lift(norm x) IN k}`;;

let CLOSED_MAP_NORM = `!s:real^N->bool. closed s ==> closed (IMAGE (lift o norm) s)`;;

let CONTINUOUS_AT_LIFT_COMPONENT = `!i a. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous (at a)`;;

let CONTINUOUS_ON_LIFT_COMPONENT = `!i s. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous_on s`;;

let CONTINUOUS_AT_LIFT_INFNORM = `!x:real^N. (lift o infnorm) continuous (at x)`;;

let CONTINUOUS_AT_LIFT_DIST = `!a:real^N x. (lift o (\x. dist(a,x))) continuous (at x)`;;

let CONTINUOUS_ON_LIFT_DIST = `!a s. (lift o (\x. dist(a,x))) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Hence some handy theorems on distance, diameter etc. of/from a set.       *)
(* ------------------------------------------------------------------------- *)

let COMPACT_ATTAINS_SUP = `!s. compact (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> y <= x`;;

let COMPACT_ATTAINS_INF = `!s. compact (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> x <= y`;;

let CONTINUOUS_ATTAINS_SUP = `!f:real^N->real s.
        compact s /\ ~(s = {}) /\ (lift o f) continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(y) <= f(x)`;;

let CONTINUOUS_ATTAINS_INF = `!f:real^N->real s.
        compact s /\ ~(s = {}) /\ (lift o f) continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(x) <= f(y)`;;

let DISTANCE_ATTAINS_SUP = `!s a. compact s /\ ~(s = {})
         ==> ?x. x IN s /\ !y. y IN s ==> dist(a,y) <= dist(a,x)`;;

(* ------------------------------------------------------------------------- *)
(* For *minimal* distance, we only need closure, not compactness.            *)
(* ------------------------------------------------------------------------- *)

let DISTANCE_ATTAINS_INF = `!s a:real^N.
        closed s /\ ~(s = {})
        ==> ?x. x IN s /\ !y. y IN s ==> dist(a,x) <= dist(a,y)`;;

(* ------------------------------------------------------------------------- *)
(* We can now extend limit compositions to consider the scalar multiplier.   *)
(* ------------------------------------------------------------------------- *)

let LIM_MUL = `!net:(A)net f l:real^N c d.
        ((lift o c) --> lift d) net /\ (f --> l) net
        ==> ((\x. c(x) % f(x)) --> (d % l)) net`;;

let LIM_LIFT_POW = `!net:(A)net f l n.
        ((\a. lift(f a)) --> lift l) net
        ==> ((\a. lift(f(a) pow n)) --> lift(l pow n)) net`;;

let LIM_LIFT_PRODUCT = `!net:(A)net f g (t:B->bool).
        FINITE t /\
        (!i. i IN t ==> ((\x. lift(f x i)) --> lift(g i)) net)
        ==> ((\x. lift(product t (f x))) --> lift(product t g)) net`;;

let LIM_VMUL = `!net:(A)net c d v:real^N.
        ((lift o c) --> lift d) net ==> ((\x. c(x) % v) --> d % v) net`;;

let CONTINUOUS_VMUL = `!net c v. (lift o c) continuous net ==> (\x. c(x) % v) continuous net`;;

let CONTINUOUS_MUL = `!net f c. (lift o c) continuous net /\ f continuous net
             ==> (\x. c(x) % f(x)) continuous net`;;

let CONTINUOUS_ON_VMUL = `!s c v. (lift o c) continuous_on s ==> (\x. c(x) % v) continuous_on s`;;

let CONTINUOUS_ON_MUL = `!s c f. (lift o c) continuous_on s /\ f continuous_on s
           ==> (\x. c(x) % f(x)) continuous_on s`;;

let CONTINUOUS_LIFT_POW = `!net f:A->real n.
        (\x. lift(f x)) continuous net
        ==> (\x. lift(f x pow n)) continuous net`;;

let CONTINUOUS_ON_LIFT_POW = `!f:real^N->real s n.
        (\x. lift(f x)) continuous_on s
        ==> (\x. lift(f x pow n)) continuous_on s`;;

let CONTINUOUS_LIFT_PRODUCT = `!net:(A)net f (t:B->bool).
        FINITE t /\
        (!i. i IN t ==> (\x. lift(f x i)) continuous net)
        ==> (\x. lift(product t (f x))) continuous net`;;

let CONTINUOUS_ON_LIFT_PRODUCT = `!f:real^N->A->real s t.
        FINITE t /\
        (!i. i IN t ==> (\x. lift(f x i)) continuous_on s)
        ==> (\x. lift(product t (f x))) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Continuity of inverse.                                                    *)
(* ------------------------------------------------------------------------- *)

let LIM_INV = `!net:(A)net f l.
        ((lift o f) --> lift l) net /\ ~(l = &0)
        ==> ((lift o inv o f) --> lift(inv l)) net`;;

let CONTINUOUS_INV = `!net f. (lift o f) continuous net /\ ~(f(netlimit net) = &0)
           ==> (lift o inv o f) continuous net`;;

let CONTINUOUS_AT_WITHIN_INV = `!f s a:real^N.
        (lift o f) continuous (at a within s) /\ ~(f a = &0)
        ==> (lift o inv o f) continuous (at a within s)`;;

let CONTINUOUS_AT_INV = `!f a. (lift o f) continuous at a /\ ~(f a = &0)
         ==> (lift o inv o f) continuous at a`;;

let CONTINUOUS_ON_INV = `!f s. (lift o f) continuous_on s /\ (!x. x IN s ==> ~(f x = &0))
         ==> (lift o inv o f) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* More preservation properties for pasted sets (Cartesian products).        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MAP_PASTECART = `continuous_map
     (prod_topology (euclidean:(real^M)topology) (euclidean:(real^N)topology),
      euclidean)
     (\(x,y). pastecart x y)`;;

let LIM_PASTECART = `!net f:A->real^M g:A->real^N.
        (f --> a) net /\ (g --> b) net
        ==> ((\x. pastecart (f x) (g x)) --> pastecart a b) net`;;

let LIM_PASTECART_EQ = `!net f:A->real^M g:A->real^N.
        ((\x. pastecart (f x) (g x)) --> pastecart a b) net <=>
        (f --> a) net /\ (g --> b) net`;;

let CONTINUOUS_PASTECART = `!net f:A->real^M g:A->real^N.
        f continuous net /\ g continuous net
        ==> (\x. pastecart (f x) (g x)) continuous net`;;

let CONTINUOUS_ON_PASTECART = `!f:real^M->real^N g:real^M->real^P s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. pastecart (f x) (g x)) continuous_on s`;;

let CONTINUOUS_FSTCART = `!net f:A->real^(M,N)finite_sum.
      f continuous net ==> (\x. fstcart(f x)) continuous net`;;

let CONTINUOUS_SNDCART = `!net f:A->real^(M,N)finite_sum.
      f continuous net ==> (\x. sndcart(f x)) continuous net`;;

let CONTINUOUS_ON_FSTCART = `!f:real^M->real^(N,P)finite_sum.
        f continuous_on s ==> (\x. fstcart(f x)) continuous_on s`;;

let CONTINUOUS_ON_SNDCART = `!f:real^M->real^(N,P)finite_sum.
        f continuous_on s ==> (\x. sndcart(f x)) continuous_on s`;;

let CONNECTED_PCROSS = `!s:real^M->bool t:real^N->bool.
        connected s /\ connected t
        ==> connected (s PCROSS t)`;;

let CONNECTED_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        connected (s PCROSS t) <=>
        s = {} \/ t = {} \/ connected s /\ connected t`;;

let CONNECTED_COMPONENT_PCROSS = `!s t a:real^M b:real^N.
        connected_component (s PCROSS t) (pastecart a b) =
        connected_component s a PCROSS connected_component t b`;;

let COMPONENTS_PCROSS = `!s:real^M->bool t:real^N->bool.
    components(s PCROSS t) =
    {c PCROSS d | c IN components s /\ d IN components t}`;;

let CLOSURE_PCROSS = `!s:real^M->bool t:real^N->bool.
        closure (s PCROSS t) = (closure s) PCROSS (closure t)`;;

let LIMPT_PCROSS = `!s:real^M->bool t:real^N->bool x y.
        x limit_point_of s /\ y limit_point_of t
        ==> (pastecart x y) limit_point_of (s PCROSS t)`;;

let CLOSED_IN_PCROSS = `!s:real^M->bool s' t:real^N->bool t'.
        closed_in (subtopology euclidean s) s' /\
        closed_in (subtopology euclidean t) t'
        ==> closed_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t')`;;

let CLOSED_IN_PCROSS_EQ = `!s s':real^M->bool t t':real^N->bool.
        closed_in (subtopology euclidean (s PCROSS t)) (s' PCROSS t') <=>
        s' = {} \/ t' = {} \/
        closed_in (subtopology euclidean s) s' /\
        closed_in (subtopology euclidean t) t'`;;

let FRONTIER_PCROSS = `!s:real^M->bool t:real^N->bool.
        frontier(s PCROSS t) = frontier s PCROSS closure t UNION
                               closure s PCROSS frontier t`;;

(* ------------------------------------------------------------------------- *)
(* Hence some useful properties follow quite easily.                         *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_SCALING = `!s:real^N->bool c. connected s ==> connected (IMAGE (\x. c % x) s)`;;

let CONNECTED_NEGATIONS = `!s:real^N->bool. connected s ==> connected (IMAGE (--) s)`;;

let CONNECTED_SCALING_EQ = `!s:real^N->bool c.
        connected (IMAGE (\x. c % x) s) <=> c = &0 \/ connected s`;;

let CONNECTED_AFFINITY_EQ = `!s m c:real^N.
        connected (IMAGE (\x. m % x + c) s) <=> m = &0 \/ connected s`;;

let CONNECTED_AFFINITY = `!s m c:real^N. connected s ==> connected (IMAGE (\x. m % x + c) s)`;;

let CONNECTED_SUMS = `!s t:real^N->bool.
        connected s /\ connected t ==> connected {x + y | x IN s /\ y IN t}`;;

let COMPACT_SCALING = `!s:real^N->bool c. compact s ==> compact (IMAGE (\x. c % x) s)`;;

let COMPACT_SCALING_EQ = `!s:real^N->bool c. compact (IMAGE (\x. c % x) s) <=> c = &0 \/ compact s`;;

let COMPACT_NEGATIONS = `!s:real^N->bool. compact s ==> compact (IMAGE (--) s)`;;

let COMPACT_SUMS = `!s:real^N->bool t.
        compact s /\ compact t ==> compact {x + y | x IN s /\ y IN t}`;;

let COMPACT_DIFFERENCES = `!s:real^N->bool t.
        compact s /\ compact t ==> compact {x - y | x IN s /\ y IN t}`;;

let COMPACT_AFFINITY_EQ = `!s m c:real^N.
        compact (IMAGE (\x. m % x + c) s) <=> m = &0 \/ compact s`;;

let COMPACT_AFFINITY = `!s m c:real^N. compact s ==> compact (IMAGE (\x. m % x + c) s)`;;

(* ------------------------------------------------------------------------- *)
(* Hence we get the following.                                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_SUP_MAXDISTANCE = `!s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\
                  !u v. u IN s /\ v IN s ==> norm(u - v) <= norm(x - y)`;;

(* ------------------------------------------------------------------------- *)
(* We can state this in terms of diameter of a set.                          *)
(* ------------------------------------------------------------------------- *)

let diameter = new_definition
  `diameter s =
        if s = {} then &0
        else sup {norm(x - y) | x IN s /\ y IN s}`;;

let MDIAMETER_EUCLIDEAN = `mdiameter euclidean_metric:(real^N->bool)->real = diameter`;;

let DIAMETER_BOUNDED = `!s. bounded s
       ==> (!x:real^N y. x IN s /\ y IN s ==> norm(x - y) <= diameter s) /\
           (!d. &0 <= d /\ d < diameter s
                ==> ?x y. x IN s /\ y IN s /\ norm(x - y) > d)`;;

let DIAMETER_BOUNDED_BOUND = `!s x y. bounded s /\ x IN s /\ y IN s ==> norm(x - y) <= diameter s`;;

let DIAMETER_COMPACT_ATTAINED = `!s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\ (norm(x - y) = diameter s)`;;

let DIAMETER_TRANSLATION = `!a s. diameter (IMAGE (\x. a + x) s) = diameter s`;;

add_translation_invariants [DIAMETER_TRANSLATION];;

let DIAMETER_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x. norm(f x) = norm x)
        ==> diameter(IMAGE f s) = diameter s`;;

add_linear_invariants [DIAMETER_LINEAR_IMAGE];;

let DIAMETER_EMPTY = `diameter {} = &0`;;

let DIAMETER_SING = `!a:real^N. diameter {a} = &0`;;

let DIAMETER_POS_LE = `!s:real^N->bool. bounded s ==> &0 <= diameter s`;;

let DIAMETER_SUBSET = `!s t:real^N->bool. s SUBSET t /\ bounded t ==> diameter s <= diameter t`;;

let DIAMETER_CLOSURE = `!s:real^N->bool. diameter(closure s) = diameter s`;;

let DIAMETER_SUBSET_CBALL_NONEMPTY = `!s:real^N->bool.
       bounded s /\ ~(s = {}) ==> ?z. z IN s /\ s SUBSET cball(z,diameter s)`;;

let DIAMETER_SUBSET_CBALL = `!s:real^N->bool. bounded s ==> ?z. s SUBSET cball(z,diameter s)`;;

let DIAMETER_EQ_0 = `!s:real^N->bool.
        bounded s ==> (diameter s = &0 <=> s = {} \/ ?a. s = {a})`;;

let DIAMETER_LE = `!s:real^N->bool.
        (~(s = {}) \/ &0 <= d) /\
        (!x y. x IN s /\ y IN s ==> norm(x - y) <= d) ==> diameter s <= d`;;

let BOUNDED_AND_DIAMETER_LE = `!s:real^N->bool r.
        bounded s /\ diameter s <= r <=>
        &0 <= r /\ !x y. x IN s /\ y IN s ==> dist(x,y) <= r`;;

let DIST_LE_DIAMETER = `!s a b:real^N. bounded s /\ a IN s /\ b IN s ==> dist(a,b) <= diameter s`;;

let DIAMETER_CBALL = `!a:real^N r. diameter(cball(a,r)) = if r < &0 then &0 else &2 * r`;;

let DIAMETER_BALL = `!a:real^N r. diameter(ball(a,r)) = if r < &0 then &0 else &2 * r`;;

let DIAMETER_SCALING = `!a s:real^N->bool.
        bounded s ==> diameter(IMAGE (\x. a % x) s) = abs a * diameter s`;;

let DIAMETER_AFFINITY = `!s m c:real^N.
        bounded s
        ==> diameter(IMAGE (\x. m % x + c) s) = abs m * diameter s`;;

let DIAMETER_SUMS = `!s t:real^N->bool.
        bounded s /\ bounded t
        ==> diameter {x + y | x IN s /\ y IN t} <= diameter s + diameter t`;;

let DIAMETER_LE_SUMS_RIGHT = `!s t:real^N->bool.
        ~(t = {}) /\ bounded s /\ bounded t
        ==> diameter s <= diameter {x + y | x IN s /\ y IN t}`;;

let DIAMETER_LE_SUMS_LEFT = `!s t:real^N->bool.
        ~(s = {}) /\ bounded s /\ bounded t
        ==> diameter t <= diameter {x + y | x IN s /\ y IN t}`;;

let DIAMETER_UNION_LE = `!s t:real^N->bool.
        bounded s /\ bounded t /\ ~(s INTER t = {})
        ==> diameter(s UNION t) <= diameter s + diameter t`;;

(* ------------------------------------------------------------------------- *)
(* Related results with closure as the conclusion.                           *)
(* ------------------------------------------------------------------------- *)

let CLOSED_SCALING = `!s:real^N->bool c. closed s ==> closed (IMAGE (\x. c % x) s)`;;

let CLOSED_NEGATIONS = `!s:real^N->bool. closed s ==> closed (IMAGE (--) s)`;;

let COMPACT_CLOSED_SUMS = `!s:real^N->bool t.
        compact s /\ closed t ==> closed {x + y | x IN s /\ y IN t}`;;

let CLOSED_COMPACT_SUMS = `!s:real^N->bool t.
        closed s /\ compact t ==> closed {x + y | x IN s /\ y IN t}`;;

let CLOSURE_SUMS = `!s t:real^N->bool.
        bounded s \/ bounded t
        ==> closure {x + y | x IN s /\ y IN t} =
            {x + y | x IN closure s /\ y IN closure t}`;;

let COMPACT_CLOSED_DIFFERENCES = `!s:real^N->bool t.
        compact s /\ closed t ==> closed {x - y | x IN s /\ y IN t}`;;

let CLOSED_COMPACT_DIFFERENCES = `!s:real^N->bool t.
        closed s /\ compact t ==> closed {x - y | x IN s /\ y IN t}`;;

let CLOSED_TRANSLATION_EQ = `!a s. closed (IMAGE (\x:real^N. a + x) s) <=> closed s`;;

let CLOSED_TRANSLATION = `!s a:real^N. closed s ==> closed (IMAGE (\x. a + x) s)`;;

add_translation_invariants [CLOSED_TRANSLATION_EQ];;

let COMPLETE_TRANSLATION_EQ = `!a s. complete(IMAGE (\x:real^N. a + x) s) <=> complete s`;;

add_translation_invariants [COMPLETE_TRANSLATION_EQ];;

let CLOSED_SCALING_EQ = `!s:real^N->bool c. closed (IMAGE (\x. c % x) s) <=> c = &0 \/ closed s`;;

let CLOSED_AFFINITY_EQ = `!s m c:real^N.
        closed (IMAGE (\x. m % x + c) s) <=> m = &0 \/ closed s`;;

let CLOSED_AFFINITY = `!s m c:real^N. closed s ==> closed (IMAGE (\x. m % x + c) s)`;;

let TRANSLATION_DIFF = `!s t:real^N->bool.
        IMAGE (\x. a + x) (s DIFF t) =
        (IMAGE (\x. a + x) s) DIFF (IMAGE (\x. a + x) t)`;;

let CLOSURE_TRANSLATION = `!a s. closure(IMAGE (\x:real^N. a + x) s) = IMAGE (\x. a + x) (closure s)`;;

add_translation_invariants [CLOSURE_TRANSLATION];;

let FRONTIER_TRANSLATION = `!a s. frontier(IMAGE (\x:real^N. a + x) s) = IMAGE (\x. a + x) (frontier s)`;;

add_translation_invariants [FRONTIER_TRANSLATION];;

let DIAMETER_LT_SUMS_RIGHT = `!s t:real^N->bool.
        ~(s = {}) /\ ~(?a. t SUBSET {a}) /\ bounded s /\ bounded t
        ==> diameter s < diameter {x + y | x IN s /\ y IN t}`;;

let DIAMETER_LT_SUMS_LEFT = `!s t:real^N->bool.
        ~(?a. s SUBSET {a}) /\ ~(t = {}) /\ bounded s /\ bounded t
        ==> diameter t < diameter {x + y | x IN s /\ y IN t}`;;

(* ------------------------------------------------------------------------- *)
(* It is always possible to shrink a ball containing a compact set.          *)
(* ------------------------------------------------------------------------- *)

let COMPACT_SHRINK_ENCLOSING_BALL = `!s x:real^N r. &0 < r /\ compact s /\ s SUBSET ball(x,r)
                  ==> ?r'. &0 < r' /\ r' < r /\ s SUBSET ball(x,r')`;;

let COMPACT_SHRINK_ENCLOSING_BALL_INFTY = `!s b. compact s /\ (!x:real^N. x IN s ==> b * norm x < &1)
         ==> ?r. &0 < r /\ b * r < &1 /\ !x. x IN s ==> norm x < r`;;

(* ------------------------------------------------------------------------- *)
(* Separation between points and sets.                                       *)
(* ------------------------------------------------------------------------- *)

let SEPARATE_POINT_CLOSED = `!s a:real^N.
        closed s /\ ~(a IN s)
        ==> ?d. &0 < d /\ !x. x IN s ==> d <= dist(a,x)`;;

let SEPARATE_COMPACT_CLOSED = `!s t:real^N->bool.
        compact s /\ closed t /\ s INTER t = {}
        ==> ?d. &0 < d /\ !x y. x IN s /\ y IN t ==> d <= dist(x,y)`;;

let SEPARATE_CLOSED_COMPACT = `!s t:real^N->bool.
        closed s /\ compact t /\ s INTER t = {}
        ==> ?d. &0 < d /\ !x y. x IN s /\ y IN t ==> d <= dist(x,y)`;;

(* ------------------------------------------------------------------------- *)
(* Representing sets as the union of a chain of compact sets.                *)
(* ------------------------------------------------------------------------- *)

let CLOSED_UNION_COMPACT_SUBSETS = `!s. closed s
       ==> ?f:num->real^N->bool.
                (!n. compact(f n)) /\
                (!n. (f n) SUBSET s) /\
                (!n. (f n) SUBSET f(n + 1)) /\
                UNIONS {f n | n IN (:num)} = s /\
                (!k. compact k /\ k SUBSET s
                     ==> ?N. !n. n >= N ==> k SUBSET (f n))`;;

let OPEN_UNION_COMPACT_SUBSETS = `!s. open s
       ==> ?f:num->real^N->bool.
                (!n. compact(f n)) /\
                (!n. (f n) SUBSET s) /\
                (!n. (f n) SUBSET interior(f(n + 1))) /\
                UNIONS {f n | n IN (:num)} = s /\
                (!k. compact k /\ k SUBSET s
                     ==> ?N. !n. n >= N ==> k SUBSET (f n))`;;

(* ------------------------------------------------------------------------- *)
(* Closed-graph characterization of continuity.                              *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CLOSED_GRAPH_GEN = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t
        ==> closed_in (subtopology euclidean (s PCROSS t))
                      {pastecart x (f x) | x IN s}`;;

let CONTINUOUS_CLOSED_GRAPH_EQ = `!f:real^M->real^N s t.
        compact t /\ IMAGE f s SUBSET t
        ==> (f continuous_on s <=>
             closed_in (subtopology euclidean (s PCROSS t))
                       {pastecart x (f x) | x IN s})`;;

let CONTINUOUS_CLOSED_GRAPH = `!f:real^M->real^N s.
        closed s /\ f continuous_on s ==> closed {pastecart x (f x) | x IN s}`;;

let CONTINUOUS_FROM_CLOSED_GRAPH = `!f:real^M->real^N s t.
        compact t /\ IMAGE f s SUBSET t /\
        closed {pastecart x (f x) | x IN s}
        ==> f continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* More topological properties of intervals.                                 *)
(* ------------------------------------------------------------------------- *)

let OPEN_INTERVAL_LEMMA = `!a b x. a < x /\ x < b
           ==> ?d. &0 < d /\ !x'. abs(x' - x) < d ==> a < x' /\ x' < b`;;

let OPEN_INTERVAL = `!a:real^N b. open(interval (a,b))`;;

let CLOSED_INTERVAL = `!a:real^N b. closed(interval [a,b])`;;

let INTERIOR_CLOSED_INTERVAL = `!a:real^N b. interior(interval [a,b]) = interval (a,b)`;;

let INTERIOR_INTERVAL = `(!a b. interior(interval[a,b]) = interval(a,b)) /\
   (!a b. interior(interval(a,b)) = interval(a,b))`;;

let BOUNDED_CLOSED_INTERVAL = `!a b:real^N. bounded (interval [a,b])`;;

let BOUNDED_INTERVAL = `(!a b. bounded (interval [a,b])) /\ (!a b. bounded (interval (a,b)))`;;

let NOT_INTERVAL_UNIV = `(!a b. ~(interval[a,b] = (:real^N))) /\
   (!a b. ~(interval(a,b) = (:real^N)))`;;

let OPEN_INTERVAL_MIDPOINT = `!a b:real^N.
        ~(interval(a,b) = {}) ==> (inv(&2) % (a + b)) IN interval(a,b)`;;

let OPEN_CLOSED_INTERVAL_CONVEX = `!a b x y:real^N e.
        x IN interval(a,b) /\ y IN interval[a,b] /\ &0 < e /\ e <= &1
        ==> (e % x + (&1 - e) % y) IN interval(a,b)`;;

let CLOSURE_OPEN_INTERVAL = `!a b:real^N.
     ~(interval(a,b) = {}) ==> closure(interval(a,b)) = interval[a,b]`;;

let CLOSURE_INTERVAL = `(!a b. closure(interval[a,b]) = interval[a,b]) /\
   (!a b. closure(interval(a,b)) =
          if interval(a,b) = {} then {} else interval[a,b])`;;

let FRONTIER_CLOSED_INTERVAL = `!a b. frontier(interval[a,b]) = interval[a,b] DIFF interval(a,b)`;;

let FRONTIER_OPEN_INTERVAL = `!a b. frontier(interval(a,b)) =
                if interval(a,b) = {} then {}
                else interval[a,b] DIFF interval(a,b)`;;

let INTER_INTERVAL_MIXED_EQ_EMPTY = `!a b c d:real^N.
        ~(interval(c,d) = {})
        ==> (interval(a,b) INTER interval[c,d] = {} <=>
             interval(a,b) INTER interval(c,d) = {})`;;

let INTERVAL_TRANSLATION = `(!c a b. interval[c + a,c + b] = IMAGE (\x. c + x) (interval[a,b])) /\
   (!c a b. interval(c + a,c + b) = IMAGE (\x. c + x) (interval(a,b)))`;;

add_translation_invariants
 [CONJUNCT1 INTERVAL_TRANSLATION; CONJUNCT2 INTERVAL_TRANSLATION];;

let EMPTY_AS_INTERVAL = `{} = interval[vec 1,vec 0]`;;

let UNIT_INTERVAL_NONEMPTY = `~(interval[vec 0:real^N,vec 1] = {}) /\
   ~(interval(vec 0:real^N,vec 1) = {})`;;

let IMAGE_STRETCH_INTERVAL = `!a b:real^N m.
    IMAGE (\x. lambda k. m(k) * x$k) (interval[a,b]) =
        if interval[a,b] = {} then {}
        else interval[(lambda k. min (m(k) * a$k) (m(k) * b$k)):real^N,
                      (lambda k. max (m(k) * a$k) (m(k) * b$k))]`;;

let INTERVAL_IMAGE_STRETCH_INTERVAL = `!a b:real^N m. ?u v:real^N.
     IMAGE (\x. lambda k. m k * x$k) (interval[a,b]) = interval[u,v]`;;

let CLOSED_INTERVAL_IMAGE_UNIT_INTERVAL = `!a b:real^N.
        ~(interval[a,b] = {})
        ==> interval[a,b] = IMAGE (\x:real^N. a + x)
                                  (IMAGE (\x. (lambda i. (b$i - a$i) * x$i))
                                         (interval[vec 0:real^N,vec 1]))`;;

let SUMS_INTERVALS = `(!a b c d:real^N.
        ~(interval[a,b] = {}) /\ ~(interval[c,d] = {})
        ==> {x + y | x IN interval[a,b] /\ y IN interval[c,d]} =
            interval[a+c,b+d]) /\
   (!a b c d:real^N.
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {})
        ==> {x + y | x IN interval(a,b) /\ y IN interval(c,d)} =
            interval(a+c,b+d))`;;

let PCROSS_INTERVAL = `!a b:real^M c d:real^N.
        interval[a,b] PCROSS interval[c,d] =
        interval[pastecart a c,pastecart b d]`;;

let OPEN_CONTAINS_INTERVAL = `(!s:real^N->bool.
        open s <=>
        !x. x IN s ==> ?a b. x IN interval(a,b) /\ interval[a,b] SUBSET s)`
and OPEN_CONTAINS_OPEN_INTERVAL = `(!s:real^N->bool.
        open s <=>
        !x. x IN s ==> ?a b. x IN interval(a,b) /\ interval(a,b) SUBSET s)`;;

let DIAMETER_INTERVAL = `(!a b:real^N.
        diameter(interval[a,b]) =
        if interval[a,b] = {} then &0 else norm(b - a)) /\
   (!a b:real^N.
        diameter(interval(a,b)) =
        if interval(a,b) = {} then &0 else norm(b - a))`;;

let IMAGE_TWIZZLE_INTERVAL = `!p a b. dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
           ==> IMAGE ((\x. lambda i. x$(p i)):real^M->real^N) (interval[a,b]) =
               interval[(lambda i. a$(p i)),(lambda i. b$(p i))]`;;

let EQ_INTERVAL = `(!a b c d:real^N.
        interval[a,b] = interval[c,d] <=>
        interval[a,b] = {} /\ interval[c,d] = {} \/ a = c /\ b = d) /\
   (!a b c d:real^N.
        interval[a,b] = interval(c,d) <=>
        interval[a,b] = {} /\ interval(c,d) = {}) /\
   (!a b c d:real^N.
        interval(a,b) = interval[c,d] <=>
        interval(a,b) = {} /\ interval[c,d] = {}) /\
   (!a b c d:real^N.
        interval(a,b) = interval(c,d) <=>
        interval(a,b) = {} /\ interval(c,d) = {} \/ a = c /\ b = d)`;;

let CLOSED_INTERVAL_EQ = `(!a b:real^N. closed(interval[a,b])) /\
   (!a b:real^N. closed(interval(a,b)) <=> interval(a,b) = {})`;;

let OPEN_INTERVAL_EQ = `(!a b:real^N. open(interval[a,b]) <=> interval[a,b] = {}) /\
   (!a b:real^N. open(interval(a,b)))`;;

let COMPACT_INTERVAL_EQ = `(!a b:real^N. compact(interval[a,b])) /\
   (!a b:real^N. compact(interval(a,b)) <=> interval(a,b) = {})`;;

let CLOSED_INTERVAL_DROPOUT = `!k a b. dimindex(:M) + 1 = dimindex(:N) /\
           1 <= k /\ k <= dimindex(:N) /\
           a$k <= b$k
           ==> interval[dropout k a,dropout k b] =
               IMAGE (dropout k:real^N->real^M) (interval[a,b])`;;

let IMAGE_DROPOUT_CLOSED_INTERVAL = `!k a b. dimindex(:M) + 1 = dimindex(:N) /\
           1 <= k /\ k <= dimindex(:N)
           ==> IMAGE (dropout k:real^N->real^M) (interval[a,b]) =
                  if a$k <= b$k then interval[dropout k a,dropout k b]
                  else {}`;;

let EQ_BALLS = `(!a a':real^N r r'.
      ball(a,r) = ball(a',r') <=> a = a' /\ r = r' \/ r <= &0 /\ r' <= &0) /\
   (!a a':real^N r r'.
      ball(a,r) = cball(a',r') <=> r <= &0 /\ r' < &0) /\
   (!a a':real^N r r'.
      cball(a,r) = ball(a',r') <=> r < &0 /\ r' <= &0) /\
   (!a a':real^N r r'.
      cball(a,r) = cball(a',r') <=> a = a' /\ r = r' \/ r < &0 /\ r' < &0)`;;

(* ------------------------------------------------------------------------- *)
(* Some special cases for intervals in R^1.                                  *)
(* ------------------------------------------------------------------------- *)

let IN_INTERVAL_1 = `!a b x:real^1.
        (x IN interval[a,b] <=> drop a <= drop x /\ drop x <= drop b) /\
        (x IN interval(a,b) <=> drop a < drop x /\ drop x < drop b)`;;

let REAL_INTERVAL_INTERVAL = `real_interval[a,b] = IMAGE drop (interval[lift a,lift b]) /\
   real_interval(a,b) = IMAGE drop (interval(lift a,lift b))`;;

let INTERVAL_REAL_INTERVAL = `interval[a,b] = IMAGE lift (real_interval[drop a,drop b]) /\
   interval(a,b) = IMAGE lift (real_interval(drop a,drop b))`;;

let DROP_IN_REAL_INTERVAL = `(!a b x. drop x IN real_interval[a,b] <=> x IN interval[lift a,lift b]) /\
   (!a b x. drop x IN real_interval(a,b) <=> x IN interval(lift a,lift b))`;;

let LIFT_IN_INTERVAL = `(!a b x. lift x IN interval[a,b] <=> x IN real_interval[drop a,drop b]) /\
   (!a b x. lift x IN interval(a,b) <=> x IN real_interval(drop a,drop b))`;;

let IMAGE_LIFT_REAL_INTERVAL = `IMAGE lift (real_interval[a,b]) = interval[lift a,lift b] /\
   IMAGE lift (real_interval(a,b)) = interval(lift a,lift b)`;;

let IMAGE_DROP_INTERVAL = `IMAGE drop (interval[a,b]) = real_interval[drop a,drop b] /\
   IMAGE drop (interval(a,b)) = real_interval(drop a,drop b)`;;

let INTERVAL_CASES_1 = `!x:real^1. x IN interval[a,b] ==> x IN interval(a,b) \/ (x = a) \/ (x = b)`;;

let INTERVAL_EQ_EMPTY_1 = `!a b:real^1.
        (interval[a,b] = {} <=> drop b < drop a) /\
        (interval(a,b) = {} <=> drop b <= drop a)`;;

let INTERVAL_NE_EMPTY_1 = `(!a b:real^1. ~(interval[a,b] = {}) <=> drop a <= drop b) /\
   (!a b:real^1. ~(interval(a,b) = {}) <=> drop a < drop b)`;;

let UNION_INTERVAL_1 = `!a b c:real^1.
    c IN interval[a,b] ==> interval[a,c] UNION interval[c,b] = interval[a,b]`;;

let SUBSET_INTERVAL_1 = `!a b c d.
        (interval[a,b] SUBSET interval[c,d] <=>
                drop b < drop a \/
                drop c <= drop a /\ drop a <= drop b /\ drop b <= drop d) /\
        (interval[a,b] SUBSET interval(c,d) <=>
                drop b < drop a \/
                drop c < drop a /\ drop a <= drop b /\ drop b < drop d) /\
        (interval(a,b) SUBSET interval[c,d] <=>
                drop b <= drop a \/
                drop c <= drop a /\ drop a < drop b /\ drop b <= drop d) /\
        (interval(a,b) SUBSET interval(c,d) <=>
                drop b <= drop a \/
                drop c <= drop a /\ drop a < drop b /\ drop b <= drop d)`;;

let EQ_INTERVAL_1 = `!a b c d:real^1.
       (interval[a,b] = interval[c,d] <=>
          drop b < drop a /\ drop d < drop c \/
          drop a = drop c /\ drop b = drop d)`;;

let DISJOINT_INTERVAL_1 = `!a b c d:real^1.
        (interval[a,b] INTER interval[c,d] = {} <=>
          drop b < drop a \/ drop d < drop c \/
          drop b < drop c \/ drop d < drop a) /\
        (interval[a,b] INTER interval(c,d) = {} <=>
          drop b < drop a \/ drop d <= drop c \/
          drop b <= drop c \/ drop d <= drop a) /\
        (interval(a,b) INTER interval[c,d] = {} <=>
          drop b <= drop a \/ drop d < drop c \/
          drop b <= drop c \/ drop d <= drop a) /\
        (interval(a,b) INTER interval(c,d) = {} <=>
          drop b <= drop a \/ drop d <= drop c \/
          drop b <= drop c \/ drop d <= drop a)`;;

let OPEN_CLOSED_INTERVAL_1 = `!a b:real^1. interval(a,b) = interval[a,b] DIFF {a,b}`;;

let CLOSED_OPEN_INTERVAL_1 = `!a b:real^1. drop a <= drop b ==> interval[a,b] = interval(a,b) UNION {a,b}`;;

let BALL_1 = `!x:real^1 r. cball(x,r) = interval[x - lift r,x + lift r] /\
                ball(x,r) = interval(x - lift r,x + lift r)`;;

let SPHERE_1 = `!a:real^1 r. sphere(a,r) = if r < &0 then {} else {a - lift r,a + lift r}`;;

let FINITE_SPHERE_1 = `!a:real^1 r. FINITE(sphere(a,r))`;;

let FINITE_INTERVAL_1 = `(!a b. FINITE(interval[a,b]) <=> drop b <= drop a) /\
   (!a b. FINITE(interval(a,b)) <=> drop b <= drop a)`;;

let BALL_INTERVAL = `!x:real^1 e. ball(x,e) = interval(x - lift e,x + lift e)`;;

let CBALL_INTERVAL = `!x:real^1 e. cball(x,e) = interval[x - lift e,x + lift e]`;;

let BALL_INTERVAL_0 = `!e. ball(vec 0:real^1,e) = interval(--lift e,lift e)`;;

let CBALL_INTERVAL_0 = `!e. cball(vec 0:real^1,e) = interval[--lift e,lift e]`;;

let INTER_INTERVAL_1 = `!a b c d:real^1.
        interval[a,b] INTER interval[c,d] =
        interval[lift(max (drop a) (drop c)),lift(min (drop b) (drop d))]`;;

let CLOSED_DIFF_OPEN_INTERVAL_1 = `!a b:real^1.
        interval[a,b] DIFF interval(a,b) =
        if interval[a,b] = {} then {} else {a,b}`;;

let INTERVAL_1 = `(!a b:real^1. interval[a,b] =
                 if drop a <= drop b then cball(midpoint(a,b),dist(a,b) / &2)
                 else {}) /\
   (!a b:real^1. interval(a,b) =
                 if drop a < drop b then ball(midpoint(a,b),dist(a,b) / &2)
                 else {})`;;

let SEGMENT_1 = `(!a b. segment[a,b] =
          if drop a <= drop b then interval[a,b] else interval[b,a]) /\
   (!a b. segment(a,b) =
          if drop a <= drop b then interval(a,b) else interval(b,a))`;;

let OPEN_SEGMENT_1 = `!a b:real^1. open(segment(a,b))`;;

let INTERVAL_SUBSET_SEGMENT_1 = `(!a b:real^1. interval[a,b] SUBSET segment[a,b]) /\
   (!a b:real^1. interval(a,b) SUBSET segment(a,b))`;;

let SEGMENT_SCALAR_MULTIPLE = `(!a b v. segment[a % v,b % v] =
            {x % v:real^N | a <= x /\ x <= b \/ b <= x /\ x <= a}) /\
   (!a b v. ~(v = vec 0)
            ==> segment(a % v,b % v) =
                {x % v:real^N | a < x /\ x < b \/ b < x /\ x < a})`;;

let FINITE_INTER_COLLINEAR_OPEN_SEGMENTS = `!a b c d:real^N.
        collinear{a,b,c}
        ==> (FINITE(segment(a,b) INTER segment(c,d)) <=>
             segment(a,b) INTER segment(c,d) = {})`;;

let BOUNDED_SEPARATION_1D = `!s:real^N->bool.
        dimindex(:N) = 1 /\ bounded s
        ==> (connected((:real^N) DIFF s) <=> s = {})`;;

(* ------------------------------------------------------------------------- *)
(* Intervals in general, including infinite and mixtures of open and closed. *)
(* ------------------------------------------------------------------------- *)

let is_interval = new_definition
  `is_interval(s:real^N->bool) <=>
        !a b x. a IN s /\ b IN s /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> (a$i <= x$i /\ x$i <= b$i) \/
                         (b$i <= x$i /\ x$i <= a$i))
                ==> x IN s`;;

let IS_INTERVAL_INTERVAL = `!a:real^N b. is_interval(interval (a,b)) /\ is_interval(interval [a,b])`;;

let IS_INTERVAL_EMPTY = `is_interval {}`;;

let IS_INTERVAL_UNIV = `is_interval(UNIV:real^N->bool)`;;

let IS_INTERVAL_TRANSLATION_EQ = `!a:real^N s. is_interval(IMAGE (\x. a + x) s) <=> is_interval s`;;

add_translation_invariants [IS_INTERVAL_TRANSLATION_EQ];;

let IS_INTERVAL_TRANSLATION = `!s a:real^N. is_interval s ==> is_interval(IMAGE (\x. a + x) s)`;;

let IS_INTERVAL_POINTWISE = `!s:real^N->bool x.
        is_interval s /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> ?a. a IN s /\ a$i = x$i)
        ==> x IN s`;;

let IS_INTERVAL_COMPACT = `!s:real^N->bool. is_interval s /\ compact s <=> ?a b. s = interval[a,b]`;;

let IS_INTERVAL_1 = `!s:real^1->bool.
        is_interval s <=>
          !a b x. a IN s /\ b IN s /\ drop a <= drop x /\ drop x <= drop b
                  ==> x IN s`;;

let IS_INTERVAL_1_CASES = `!s:real^1->bool.
        is_interval s <=>
        s = {} \/
        s = (:real^1) \/
        (?a. s = {x | a < drop x}) \/
        (?a. s = {x | a <= drop x}) \/
        (?b. s = {x | drop x <= b}) \/
        (?b. s = {x | drop x < b}) \/
        (?a b. s = {x | a < drop x /\ drop x < b}) \/
        (?a b. s = {x | a < drop x /\ drop x <= b}) \/
        (?a b. s = {x | a <= drop x /\ drop x < b}) \/
        (?a b. s = {x | a <= drop x /\ drop x <= b})`;;

let IS_INTERVAL_1_CLAUSES = `is_interval({}:real^1->bool) /\
   is_interval (:real^1) /\
   (!a. is_interval {x | a < drop x}) /\
   (!a. is_interval {x | a <= drop x}) /\
   (!b. is_interval {x | drop x < b}) /\
   (!b. is_interval {x | drop x <= b}) /\
   (!a b. is_interval {x | a < drop x /\ drop x < b}) /\
   (!a b. is_interval {x | a < drop x /\ drop x <= b}) /\
   (!a b. is_interval {x | a <= drop x /\ drop x < b}) /\
   (!a b. is_interval {x | a <= drop x /\ drop x <= b})`;;

let IS_REALINTERVAL_IS_INTERVAL = `!s. is_realinterval s <=> is_interval(IMAGE lift s)`;;

let IS_INTERVAL_PCROSS = `!s:real^M->bool t:real^N->bool.
        is_interval s /\ is_interval t ==> is_interval(s PCROSS t)`;;

let IS_INTERVAL_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        is_interval(s PCROSS t) <=>
        s = {} \/ t = {} \/ is_interval s /\ is_interval t`;;

let IS_INTERVAL_INTER = `!s t:real^N->bool.
        is_interval s /\ is_interval t ==> is_interval(s INTER t)`;;

let INTERVAL_SUBSET_IS_INTERVAL = `!s a b:real^N.
     is_interval s
     ==> (interval[a,b] SUBSET s <=> interval[a,b] = {} \/ a IN s /\ b IN s)`;;

let INTERVAL_CONTAINS_COMPACT_NEIGHBOURHOOD = `!s x:real^N.
        is_interval s /\ x IN s
        ==> ?a b d. &0 < d /\ x IN interval[a,b] /\
                    interval[a,b] SUBSET s /\
                    ball(x,d) INTER s SUBSET interval[a,b]`;;

let IS_INTERVAL_SUMS = `!s t:real^N->bool.
        is_interval s /\ is_interval t
        ==> is_interval {x + y | x IN s /\ y IN t}`;;

let IS_INTERVAL_SING = `!a:real^N. is_interval {a}`;;

let INTERVAL_EQ_SING = `(!a b x:real^N. interval[a,b] = {x} <=> a = x /\ b = x) /\
   (!a b x:real^N. ~(interval(a,b) = {x}))`;;

let IS_INTERVAL_SCALING = `!s:real^N->bool c. is_interval s ==> is_interval(IMAGE (\x. c % x) s)`;;

let IS_INTERVAL_SCALING_EQ = `!s:real^N->bool c.
        is_interval(IMAGE (\x. c % x) s) <=> c = &0 \/ is_interval s`;;

let IS_INTERVAL_REFLECT = `!s:real^N->bool. is_interval(IMAGE (--) s) <=> is_interval s`;;

let lemma =
 `!c. &0 < c
       ==> !s:real^N->bool. is_interval(IMAGE (\x. c % x) s) <=>
                            is_interval s` in
add_scaling_theorems [lemma];;

let CARD_FRONTIER_INTERVAL_1 = `!s:real^1->bool.
        is_interval s ==> FINITE(frontier s) /\ CARD(frontier s) <= 2`;;

let UNION_INTERVAL_SUBSET_INTERVAL = `!s a b c d:real^N.
        is_interval s /\
        interval[a,b] SUBSET s /\ interval[c,d] SUBSET s
        ==> ?u v. interval[a,b] UNION interval[c,d] SUBSET interval[u,v] /\
                  interval[u,v] SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* Limit component bounds.                                                   *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPONENT_UBOUND = `!net:(A)net f (l:real^N) b k.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. (f x)$k <= b) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> l$k <= b`;;

let LIM_COMPONENT_LBOUND = `!net:(A)net f (l:real^N) b k.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= (f x)$k) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> b <= l$k`;;

let LIM_COMPONENT_EQ = `!net f:A->real^N i l b.
        (f --> l) net /\ 1 <= i /\ i <= dimindex(:N) /\
        ~(trivial_limit net) /\ eventually (\x. f(x)$i = b) net
        ==> l$i = b`;;

let LIM_COMPONENT_LE = `!net:(A)net f:A->real^N g:A->real^N k l m.
         ~(trivial_limit net) /\ (f --> l) net /\ (g --> m) net /\
        eventually (\x. (f x)$k <= (g x)$k) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> l$k <= m$k`;;

let LIM_DROP_LE = `!net:(A)net f g l m.
         ~(trivial_limit net) /\ (f --> l) net /\ (g --> m) net /\
        eventually (\x. drop(f x) <= drop(g x)) net
        ==> drop l <= drop m`;;

let LIM_DROP_UBOUND = `!net f:A->real^1 l b.
        (f --> l) net /\
        ~(trivial_limit net) /\ eventually (\x. drop(f x) <= b) net
        ==> drop l <= b`;;

let LIM_DROP_LBOUND = `!net f:A->real^1 l b.
        (f --> l) net /\
        ~(trivial_limit net) /\ eventually (\x. b <= drop(f x)) net
        ==> b <= drop l`;;

let LIMIT_PAIR_DROP_LE = `!net1:(A)net net2:(B)net f g l m.
        ~(trivial_limit net1) /\ ~(trivial_limit net2) /\
        (f --> l) net1 /\ (g --> m) net2 /\
        eventually (\x. eventually (\y. drop(f x) <= drop(g y)) net2) net1
        ==> drop l <= drop m`;;

(* ------------------------------------------------------------------------- *)
(* Also extending closed bounds to closures.                                 *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLOSURE_SUBSET = `!f (s:real^N->bool) (t:real^M->bool).
      f continuous_on closure s /\ closed t /\ IMAGE f s SUBSET t
      ==> IMAGE f (closure s) SUBSET t`;;

let CLOSURE_IMAGE_CLOSURE = `!f:real^M->real^N s.
        f continuous_on closure s
        ==> closure(IMAGE f (closure s)) = closure(IMAGE f s)`;;

let CLOSURE_IMAGE_BOUNDED = `!f:real^M->real^N s.
        f continuous_on closure s /\ bounded s
        ==> closure(IMAGE f s) = IMAGE f (closure s)`;;

let CONTINUOUS_ON_CLOSURE_NORM_LE = `!f:real^N->real^M s x b.
      f continuous_on (closure s) /\
      (!y. y IN s ==> norm(f y) <= b) /\
      x IN (closure s)
      ==> norm(f x) <= b`;;

let CONTINUOUS_ON_CLOSURE_COMPONENT_LE = `!f:real^N->real^M s x b k.
      f continuous_on (closure s) /\
      (!y. y IN s ==> (f y)$k <= b) /\
      x IN (closure s)
      ==> (f x)$k <= b`;;

let CONTINUOUS_ON_CLOSURE_COMPONENT_GE = `!f:real^N->real^M s x b k.
      f continuous_on (closure s) /\
      (!y. y IN s ==> b <= (f y)$k) /\
      x IN (closure s)
      ==> b <= (f x)$k`;;

let CONTINUOUS_MAP_CLOSURES_GEN = `!f:real^M->real^N s.
        f continuous_on s <=>
        !t. t SUBSET s
            ==> IMAGE f (s INTER closure t) SUBSET closure(IMAGE f t)`;;

let CONTINUOUS_MAP_CLOSURES = `!f:real^M->real^N.
        f continuous_on UNIV <=>
        !s. IMAGE f (closure s) SUBSET closure(IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* Relating images and frontiers.                                            *)
(* ------------------------------------------------------------------------- *)

let PROPER_MAP_ESCAPES_FROM_IMAGE = `!f:real^M->real^N s t x r a b.
        IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k
             ==> compact {x | x IN s /\ f x IN k}) /\
        (!n. x n IN s) /\ ~(a IN s) /\ (x --> a) sequentially /\
        (!m n. m < n ==> r m < r n) /\ ((f o x o r) --> b) sequentially
        ==> ~(b IN IMAGE f s)`;;

let FRONTIER_PROPER_MAP_IMAGE_SUBSET_GEN = `!f:real^M->real^N s t.
        IMAGE f s SUBSET t /\
        f continuous_on closure s /\
        (!k. k SUBSET t /\ compact k
             ==> compact {x | x IN s /\ f x IN k})
        ==> IMAGE f (closure s DIFF s) SUBSET
            closure(IMAGE f s) DIFF IMAGE f s`;;

let FRONTIER_PROPER_MAP_IMAGE_SUBSET = `!f:real^M->real^N s t.
        IMAGE f s SUBSET t /\
        open s /\
        f continuous_on closure s /\
        (!k. k SUBSET t /\ compact k
             ==> compact {x | x IN s /\ f x IN k})
        ==> IMAGE f (frontier s) SUBSET frontier(IMAGE f s)`;;

let FRONTIER_CLOPEN_MAP_IMAGE_SUBSET = `!f:real^M->real^N s.
        closed(IMAGE f (closure s)) /\ open(IMAGE f (interior s))
        ==> frontier(IMAGE f s) SUBSET IMAGE f (frontier s)`;;

let FRONTIER_OPEN_MAP_IMAGE_SUBSET = `!f:real^M->real^N s.
        bounded s /\ f continuous_on closure s /\ open(IMAGE f (interior s))
        ==> frontier(IMAGE f s) SUBSET IMAGE f (frontier s)`;;

let FRONTIER_PROPER_CLOPEN_MAP_IMAGE = `!f:real^M->real^N s t.
        open s /\ IMAGE f s SUBSET t /\ f continuous_on closure s /\
        open(IMAGE f s) /\ closed(IMAGE f (closure s)) /\
        (!k. k SUBSET t /\ compact k
             ==> compact {x | x IN s /\ f x IN k})
        ==> IMAGE f (frontier s) = frontier(IMAGE f s)`;;

let FRONTIER_PROPER_OPEN_MAP_IMAGE = `!f:real^M->real^N s t.
        bounded s /\ open s /\ open(IMAGE f s) /\
        f continuous_on closure s /\
        IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k
             ==> compact {x | x IN s /\ f x IN k})
        ==> IMAGE f (frontier s) = frontier(IMAGE f s)`;;

let FRONTIER_CLOPEN_MAP_IMAGE = `!f:real^M->real^N s t.
        open s /\ open(IMAGE f s) /\ closed(IMAGE f (closure s)) /\
        f continuous_on closure s /\
        (!y. compact {x | x IN s /\ f x = y}) /\
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c))
        ==> IMAGE f (frontier s) = frontier(IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* Limits relative to a union.                                               *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_UNION = `(f --> l) (at x within (s UNION t)) <=>
   (f --> l) (at x within s) /\ (f --> l) (at x within t)`;;

let CONTINUOUS_ON_UNION = `!f s t. closed s /\ closed t /\ f continuous_on s /\ f continuous_on t
           ==> f continuous_on (s UNION t)`;;

let CONTINUOUS_ON_CASES = `!P f g:real^M->real^N s t.
        closed s /\ closed t /\ f continuous_on s /\ g continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) continuous_on (s UNION t)`;;

let CONTINUOUS_ON_UNION_LOCAL = `!f:real^M->real^N s.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ f continuous_on t
        ==> f continuous_on (s UNION t)`;;

let CONTINUOUS_ON_CASES_LOCAL = `!P f g:real^M->real^N s t.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ g continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) continuous_on (s UNION t)`;;

let CONTINUOUS_ON_CASES_LE = `!f g:real^M->real^N h s a.
        f continuous_on {t | t IN s /\ h t <= a} /\
        g continuous_on {t | t IN s /\ a <= h t} /\
        (lift o h) continuous_on s /\
        (!t. t IN s /\ h t = a ==> f t = g t)
        ==> (\t. if h t <= a then f(t) else g(t)) continuous_on s`;;

let CONTINUOUS_ON_CASES_1 = `!f g:real^1->real^N s a.
        f continuous_on {t | t IN s /\ drop t <= a} /\
        g continuous_on {t | t IN s /\ a <= drop t} /\
        (lift a IN s ==> f(lift a) = g(lift a))
        ==> (\t. if drop t <= a then f(t) else g(t)) continuous_on s`;;

let EXTENSION_FROM_CLOPEN = `!f:real^M->real^N s t u.
        open_in (subtopology euclidean s) t /\
        closed_in (subtopology euclidean s) t /\
        f continuous_on t /\ IMAGE f t SUBSET u /\ (u = {} ==> s = {})
        ==> ?g. g continuous_on s /\ IMAGE g s SUBSET u /\
                !x. x IN t ==> g x = f x`;;

let CONTINUOUS_ON_CLOPEN_INDICATOR = `!s t:real^M->bool a b:real^N.
        (\x. if x IN t then a else b) continuous_on s <=>
        a = b \/
        open_in (subtopology euclidean s) (s INTER t) /\
        closed_in (subtopology euclidean s) (s INTER t)`;;

(* ------------------------------------------------------------------------- *)
(* Various formulations of limits for linear operators.                      *)
(* ------------------------------------------------------------------------- *)

let LIM_NULL_ONORM = `(!net f:A->real^M->real^N.
        (!a. linear(f a))
        ==> (((\a. lift(onorm(f a))) --> vec 0) net <=>
             !x. ((\a. f a x) --> vec 0) net))`
and LIM_NULL_ONORM_COMPONENTWISE = `(!net f:A->real^M->real^N.
        (!a. linear(f a))
        ==> (((\a. lift(onorm(f a))) --> vec 0) net <=>
             !i. 1 <= i /\ i <= dimindex(:M)
                 ==> ((\a. f a (basis i)) --> vec 0) net))`;;

let LIM_NULL_MATRIX_ONORM = `!net A:A->real^M^N.
        ((\a. lift(onorm(\x. A a ** x))) --> vec 0) net <=>
        !x. ((\a. A a ** x) --> vec 0) net`;;

let LIM_NULL_MATRIX_ONORM_COMPONENTWISE = `!net A:A->real^M^N.
        ((\a. lift(onorm(\x. A a ** x))) --> vec 0) net <=>
        !i j. 1 <= i /\ i <= dimindex(:N) /\
              1 <= j /\ j <= dimindex(:M)
              ==> ((\a. lift(A a$i$j)) --> vec 0) net`;;

let LIM_NULL_ONORM = `!net f:A->real^M->real^N g:real^M->real^N.
        (!a. linear(f a)) /\ linear g /\
        ((\a. lift(onorm(\x. f a x - g x))) --> vec 0) net
        ==> ((\a. lift(onorm(f a))) --> lift(onorm g)) net`;;

let LIM_MATRIX_COMPONENTWISE = `!net A:A->real^M^N B.
        (!x. ((\a. A a ** x) --> B ** x) net) <=>
        !i j. 1 <= i /\ i <= dimindex(:N) /\
              1 <= j /\ j <= dimindex(:M)
              ==> ((\a. lift(A a$i$j)) --> lift(B$i$j)) net`;;

let CONTINUOUS_MATRIX_COMPONENTWISE = `!net (A:A->real^M^N).
        (!x. (\a. A a ** x) continuous net) <=>
        !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:M)
              ==> (\a. lift (A a$i$j)) continuous net`;;

let CONTINUOUS_ON_MATRIX_COMPONENTWISE = `!A:real^P->real^M^N s.
        (!x. (\a. A a ** x) continuous_on s) <=>
        !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex (:M)
              ==> (\a. lift (A a$i$j)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Limits and continuity of matrices as flattened vectors.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MATRIX_VECTOR_MUL = `!net A:A->real^N^M v:A->real^N.
        (vectorize o A) continuous net /\ v continuous net
        ==> (\x. (A x) ** (v x)) continuous net`;;

let CONTINUOUS_ON_MATRIX_VECTOR_MUL = `!A:real^P->real^N^M v:real^P->real^N s.
        (vectorize o A) continuous_on s /\ v continuous_on s
        ==> (\x. (A x) ** (v x)) continuous_on s`;;

let CONTINUOUS_MATRIX_MUL = `!net A:A->real^N^M B:A->real^P^N.
        (vectorize o A) continuous net /\ (vectorize o B) continuous net
        ==> (\x. vectorize((A x) ** (B x))) continuous net`;;

let CONTINUOUS_ON_MATRIX_MUL = `!A:real^Q->real^N^M B:real^Q->real^P^N s.
        (vectorize o A) continuous_on s /\ (vectorize o B) continuous_on s
        ==> (\x. vectorize((A x) ** (B x))) continuous_on s`;;

let LIM_VECTORIZE_COMPONENTWISE = `!net (A:A->real^N^M) B.
        ((\a. vectorize(A a)) --> vectorize B) net <=>
        !i j. 1 <= i /\ i <= dimindex (:M) /\ 1 <= j /\ j <= dimindex (:N)
              ==> ((\a. lift (A a$i$j)) --> lift (B$i$j)) net`;;

let CONTINUOUS_VECTORIZE_COMPONENTWISE = `!net (A:A->real^N^M).
        (\a. vectorize(A a)) continuous net <=>
        !i j. 1 <= i /\ i <= dimindex (:M) /\ 1 <= j /\ j <= dimindex (:N)
              ==> (\a. lift (A a$i$j)) continuous net`;;

let CONTINUOUS_ON_VECTORIZE_COMPONENTWISE = `!(A:real^P->real^N^M) s.
        (\a. vectorize(A a)) continuous_on s <=>
        !i j. 1 <= i /\ i <= dimindex (:M) /\ 1 <= j /\ j <= dimindex (:N)
              ==> (\a. lift (A a$i$j)) continuous_on s`;;

let LINEAR_TRANSP = `linear(vectorize o (transp:real^N^M->real^M^N) o matrify)`;;

let LIM_MATRIX_VECTORIZE = `!net A:A->real^M^N B.
        (!x. ((\a. A a ** x) --> B ** x) net) <=>
        ((\a. vectorize (A a)) --> vectorize B) net`;;

let CONTINUOUS_MATRIX_VECTORIZE = `!net (A:A->real^N^M).
        (!x. (\a. A a ** x) continuous net) <=>
        (\a. vectorize(A a)) continuous net`;;

let CONTINUOUS_ON_MATRIX_VECTORIZE = `!A:real^P->real^N^M s.
        (!x. (\a. A a ** x) continuous_on s) <=>
        (\a. vectorize(A a)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Some more convenient intermediate-value theorem formulations.             *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_IVT_HYPERPLANE = `!s x y:real^N a b.
        connected s /\
        x IN s /\ y IN s /\ a dot x <= b /\ b <= a dot y
        ==> ?z. z IN s /\ a dot z = b`;;

let CONNECTED_IVT_COMPONENT = `!s x y:real^N a k.
        connected s /\ x IN s /\ y IN s /\
        1 <= k /\ k <= dimindex(:N) /\ x$k <= a /\ a <= y$k
        ==> ?z. z IN s /\ z$k = a`;;

(* ------------------------------------------------------------------------- *)
(* Rather trivial observation that we can map any connected set on segment.  *)
(* ------------------------------------------------------------------------- *)

let MAPPING_CONNECTED_ONTO_SEGMENT = `!s:real^M->bool a b:real^N.
        connected s /\ ~(?a. s SUBSET {a})
        ==> ?f. f continuous_on s /\ IMAGE f s = segment[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Also more convenient formulations of monotone convergence.                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_INCREASING_CONVERGENT = `!s:num->real^1.
        bounded {s n | n IN (:num)} /\ (!n. drop(s n) <= drop(s(SUC n)))
        ==> ?l. (s --> l) sequentially`;;

let BOUNDED_DECREASING_CONVERGENT = `!s:num->real^1.
        bounded {s n | n IN (:num)} /\ (!n. drop(s(SUC n)) <= drop(s(n)))
        ==> ?l. (s --> l) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Since we'll use some cardinality reasoning, add invariance theorems.      *)
(* ------------------------------------------------------------------------- *)

let card_translation_invariants =
 `(!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s =_c t <=> s =_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s =_c IMAGE (\x. a + x) t <=> s =_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s <_c t <=> s <_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s <_c IMAGE (\x. a + x) t <=> s <_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s <=_c t <=> s <=_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s <=_c IMAGE (\x. a + x) t <=> s <=_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s >_c t <=> s >_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s >_c IMAGE (\x. a + x) t <=> s >_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s >=_c t <=> s >=_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s >=_c IMAGE (\x. a + x) t <=> s >=_c t)` in
add_translation_invariants card_translation_invariants;;

let card_linear_invariants = 
`(!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s =_c t <=> s =_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s =_c IMAGE f t <=> s =_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s <_c t <=> s <_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s <_c IMAGE f t <=> s <_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s <=_c t <=> s <=_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s <=_c IMAGE f t <=> s <=_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s >_c t <=> s >_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s >_c IMAGE f t <=> s >_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s >=_c t <=> s >=_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s >=_c IMAGE f t <=> s >=_c t))` in
add_linear_invariants card_linear_invariants;;

(* ------------------------------------------------------------------------- *)
(* Basic homeomorphism definitions.                                          *)
(* ------------------------------------------------------------------------- *)

let homeomorphism = new_definition
  `homeomorphism (s,t) (f,g) <=>
     (!x. x IN s ==> (g(f(x)) = x)) /\ (IMAGE f s = t) /\ f continuous_on s /\
     (!y. y IN t ==> (f(g(y)) = y)) /\ (IMAGE g t = s) /\ g continuous_on t`;;

parse_as_infix("homeomorphic",(12,"right"));;

let homeomorphic = new_definition
  `s homeomorphic t <=> ?f g. homeomorphism (s,t) (f,g)`;;

let HOMEOMORPHISM = `!s:real^M->bool t:real^N->bool f g.
        homeomorphism (s,t) (f,g) <=>
         f continuous_on s /\ IMAGE f s SUBSET t /\
         g continuous_on t /\ IMAGE g t SUBSET s /\
         (!x. x IN s ==> g (f x) = x) /\
         (!y. y IN t ==> f (g y) = y)`;;

let HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY = `!f:real^M->real^N g s t.
        homeomorphic_maps
          (subtopology euclidean s,subtopology euclidean t)
          (f,g) <=>
        homeomorphism (s,t) (f,g)`;;

let HOMEOMORPHIC_SPACE_EUCLIDEAN = `!(s:real^M->bool) (t:real^N->bool).
     (subtopology euclidean s) homeomorphic_space (subtopology euclidean t) <=>
     s homeomorphic t`;;

let HOMEOMORPHISM_IMP_HOMEOMORPHIC = `!f:real^M->real^N g s t. homeomorphism (s,t) (f,g) ==> s homeomorphic t`;;

let HOMEOMORPHISM_OF_SUBSETS = `!f g s t s' t'.
    homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ t' SUBSET t /\ IMAGE f s' = t'
    ==> homeomorphism (s',t') (f,g)`;;

let HOMEOMORPHISM_OF_SUBSETS_ALT = `!f:real^M->real^N g s t s' t'.
        homeomorphism (s,t) (f,g) /\
        s' SUBSET s /\
        t' SUBSET t /\
        (!x. x IN s ==> (f x IN t' <=> x IN s'))
        ==> homeomorphism (s',t') (f,g)`;;

let HOMEOMORPHISM_ID = `!s:real^N->bool. homeomorphism (s,s) ((\x. x),(\x. x))`;;

let HOMEOMORPHISM_I = `!s:real^N->bool. homeomorphism (s,s) (I,I)`;;

let HOMEOMORPHIC_REFL = `!s:real^N->bool. s homeomorphic s`;;

let HOMEOMORPHISM_SYM = `!f:real^M->real^N g s t.
        homeomorphism (s,t) (f,g) <=> homeomorphism (t,s) (g,f)`;;

let HOMEOMORPHIC_SYM = `!s t. s homeomorphic t <=> t homeomorphic s`;;

let HOMEOMORPHISM_COMPOSE = `!f:real^M->real^N g h:real^N->real^P k s t u.
        homeomorphism (s,t) (f,g) /\ homeomorphism (t,u) (h,k)
        ==> homeomorphism (s,u) (h o f,g o k)`;;

let HOMEOMORPHIC_TRANS = `!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homeomorphic t /\ t homeomorphic u ==> s homeomorphic u`;;

let HOMEOMORPHISM_EQ = `!f:real^M->real^N g f' g' s t.
        homeomorphism (s,t) (f,g) /\
        (!x. x IN s ==> f' x = f x) /\
        (!y. y IN t ==> g' y = g y)
        ==> homeomorphism (s,t) (f',g')`;;

let LINEAR_IMP_HOMEOMORPHISM = `!f:real^M->real^N g:real^N->real^M s t.
        linear f /\ linear g /\ g o f = I /\ IMAGE f s = t
        ==> homeomorphism (s,t) (f,g)`;;

let ORTHOGONAL_TRANSFORMATION_IMP_HOMEOMORPHISM = `!f:real^N->real^N s t.
        orthogonal_transformation f /\ IMAGE f s = t
        ==> ?g. orthogonal_transformation g /\
                homeomorphism (s,t) (f,g)`;;

let HOMEOMORPHIC_SELF_IMAGE = `!f:real^M->real^N g s t u.
        homeomorphism (s,t) (f,g) /\ u SUBSET s
        ==> IMAGE f u homeomorphic u`;;

let HOMEOMORPHIC_IMP_CARD_EQ = `!s:real^M->bool t:real^N->bool. s homeomorphic t ==> s =_c t`;;

let HOMEOMORPHIC_FINITENESS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (FINITE s <=> FINITE t)`;;

let HOMEOMORPHISM_FINITENESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (FINITE(IMAGE f k) <=> FINITE k)`;;

let HOMEOMORPHIC_INFINITENESS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (INFINITE s <=> INFINITE t)`;;

let HOMEOMORPHISM_INFINITENESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (INFINITE(IMAGE f k) <=> INFINITE k)`;;

let HOMEOMORPHIC_COUNTABILITY = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (COUNTABLE s <=> COUNTABLE t)`;;

let HOMEOMORPHISM_COUNTABILITY = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (COUNTABLE(IMAGE f k) <=> COUNTABLE k)`;;

let HOMEOMORPHIC_EMPTY = `(!s. (s:real^N->bool) homeomorphic ({}:real^M->bool) <=> s = {}) /\
   (!s. ({}:real^M->bool) homeomorphic (s:real^N->bool) <=> s = {})`;;

let HOMEOMORPHIC_MINIMAL = `!s t. s homeomorphic t <=>
            ?f g. (!x. x IN s ==> f(x) IN t /\ (g(f(x)) = x)) /\
                  (!y. y IN t ==> g(y) IN s /\ (f(g(y)) = y)) /\
                  f continuous_on s /\ g continuous_on t`;;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (IMAGE f s) homeomorphic s`;;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ = `!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((IMAGE f s) homeomorphic t <=> s homeomorphic t)`;;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ = `!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (s homeomorphic (IMAGE f t) <=> s homeomorphic t)`;;

add_linear_invariants
  [HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
   HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ];;

let HOMEOMORPHIC_TRANSLATION_SELF = `!a:real^N s. (IMAGE (\x. a + x) s) homeomorphic s`;;

let HOMEOMORPHIC_TRANSLATION_LEFT_EQ = `!a:real^N s t.
      (IMAGE (\x. a + x) s) homeomorphic t <=> s homeomorphic t`;;

let HOMEOMORPHIC_TRANSLATION_RIGHT_EQ = `!a:real^N s t.
      s homeomorphic (IMAGE (\x. a + x) t) <=> s homeomorphic t`;;

add_translation_invariants
  [HOMEOMORPHIC_TRANSLATION_LEFT_EQ;
   HOMEOMORPHIC_TRANSLATION_RIGHT_EQ];;

let INVOLUTION_IMP_HOMEOMORPHISM_GEN = `!f:real^N->real^N u s.
        f continuous_on u /\
        s UNION IMAGE f s SUBSET u /\
        (!x. x IN s ==> f(f x) = x)
        ==> homeomorphism(s,IMAGE f s) (f,f)`;;

let INVOLUTION_IMP_HOMEOMORPHISM = `!f:real^N->real^N s.
        f continuous_on s /\ IMAGE f s SUBSET s /\ (!x. x IN s ==> f(f x) = x)
        ==> homeomorphism(s,s) (f,f)`;;

let HOMEOMORPHISM_IMP_QUOTIENT_MAP = `!f:real^M->real^N g s t.
    homeomorphism (s,t) (f,g)
    ==> !u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u)`;;

let HOMEOMORPHIC_PCROSS = `!s:real^M->bool t:real^N->bool s':real^P->bool t':real^Q->bool.
        s homeomorphic s' /\ t homeomorphic t'
        ==> (s PCROSS t) homeomorphic (s' PCROSS t')`;;

let HOMEOMORPHIC_PCROSS_SYM = `!s:real^M->bool t:real^N->bool. (s PCROSS t) homeomorphic (t PCROSS s)`;;

let HOMEOMORPHIC_PCROSS_ASSOC = `!s:real^M->bool t:real^N->bool u:real^P->bool.
        (s PCROSS (t PCROSS u)) homeomorphic ((s PCROSS t) PCROSS u)`;;

let HOMEOMORPHIC_SCALING_LEFT = `!c. &0 < c
       ==> !s t. (IMAGE (\x. c % x) s) homeomorphic t <=> s homeomorphic t`;;

let HOMEOMORPHIC_SCALING_RIGHT = `!c. &0 < c
       ==> !s t. s homeomorphic (IMAGE (\x. c % x) t) <=> s homeomorphic t`;;

let HOMEOMORPHIC_SUBSPACES = `!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t ==> s homeomorphic t`;;

let HOMEOMORPHIC_FINITE = `!s:real^M->bool t:real^N->bool.
        FINITE s /\ FINITE t ==> (s homeomorphic t <=> CARD s = CARD t)`;;

let HOMEOMORPHIC_FINITE_STRONG = `!s:real^M->bool t:real^N->bool.
        FINITE s \/ FINITE t
        ==> (s homeomorphic t <=> FINITE s /\ FINITE t /\ CARD s = CARD t)`;;

let HOMEOMORPHIC_HAS_SIZE = `!s:real^M->bool t:real^N->bool n.
        s homeomorphic t ==> (s HAS_SIZE n <=> t HAS_SIZE n)`;;

let HOMEOMORPHISM_HAS_SIZE_EQ = `!f:real^M->real^N g s t k n.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> ((IMAGE f k) HAS_SIZE n <=> k HAS_SIZE n)`;;

let HOMEOMORPHIC_SING = `!a:real^M b:real^N. {a} homeomorphic {b}`;;

let HOMEOMORPHIC_PCROSS_SING = `(!s:real^M->bool a:real^N. s homeomorphic (s PCROSS {a})) /\
   (!s:real^M->bool a:real^N. s homeomorphic ({a} PCROSS s))`;;

let LIFT_TO_QUOTIENT_SPACE_UNIQUE = `!f:real^M->real^N g:real^M->real^P s t u.
        IMAGE f s = t /\
        IMAGE g s = u /\
        (!v. v SUBSET t
             ==> (open_in (subtopology euclidean s)
                  {x | x IN s /\ f x IN v} <=>
                  open_in (subtopology euclidean t) v)) /\
         (!v. v SUBSET u
             ==> (open_in (subtopology euclidean s)
                  {x | x IN s /\ g x IN v} <=>
                  open_in (subtopology euclidean u) v)) /\
        (!x y. x IN s /\ y IN s ==> (f x = f y <=> g x = g y))
        ==> t homeomorphic u`;;

let HOMOEOMORPHISM_PASTE = `!f:real^M->real^N g f' g' s t s' t'.
        homeomorphism (s,t) (f,g) /\ homeomorphism (s',t') (f',g') /\
        (open_in (subtopology euclidean (s UNION s')) s /\
         open_in (subtopology euclidean (s UNION s')) s' /\
         open_in (subtopology euclidean (t UNION t')) t /\
         open_in (subtopology euclidean (t UNION t')) t' \/
         closed_in (subtopology euclidean (s UNION s')) s /\
         closed_in (subtopology euclidean (s UNION s')) s' /\
         closed_in (subtopology euclidean (t UNION t')) t /\
         closed_in (subtopology euclidean (t UNION t')) t') /\
        (!x. x IN s INTER s' ==> f' x = f x) /\
        (!y. y IN t INTER t' ==> g' y = g y)
        ==> ?h k. homeomorphism (s UNION s',t UNION t') (h,k) /\
                  (!x. x IN s ==> h x = f x) /\ (!x. x IN s' ==> h x = f' x) /\
                  (!y. y IN t ==> k y = g y) /\ (!y. y IN t' ==> k y = g' y) /\
                  IMAGE h s = t /\ IMAGE h s' = t' /\
                  IMAGE k t = s /\ IMAGE k t' = s' /\
                  IMAGE h (s INTER s') = t INTER t' /\
                  IMAGE h (s DIFF s') = t DIFF t' /\
                  IMAGE h (s' DIFF s) = t' DIFF t /\
                  IMAGE k (t INTER t') = s INTER s' /\
                  IMAGE k (t DIFF t') = s DIFF s' /\
                  IMAGE k (t' DIFF t) = s' DIFF s`;;

(* ------------------------------------------------------------------------- *)
(* Domain of a continuous function is homeomorphic to its graph.             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_GRAPH_EXPLICIT = `!f:real^M->real^N s.
        homeomorphism (s,{pastecart x (f x) | x IN s})
                      ((\x. pastecart x (f x)),fstcart) <=>
        f continuous_on s`;;

let HOMEOMORPHISM_GRAPH = `!f:real^M->real^N s.
        (?g. homeomorphism (s,{pastecart x (f x) | x IN s})
                           ((\x. pastecart x (f x)),g)) <=>
        f continuous_on s`;;

let HOMEOMORPHIC_GRAPH = `!f:real^M->real^N s.
        f continuous_on s ==> {pastecart x (f x) | x IN s} homeomorphic s`;;

(* ------------------------------------------------------------------------- *)
(* Inverse function property for open/closed maps.                           *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_INVERSE_OPEN_MAP = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u))
        ==> g continuous_on t`;;

let CONTINUOUS_ON_INVERSE_CLOSED_MAP = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x) /\
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean t) (IMAGE f u))
        ==> g continuous_on t`;;

let CONTINUOUS_INVERSE_INJECTIVE_PROPER_MAP = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x. x IN s ==> g(f x) = x) /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k})
        ==> g continuous_on t`;;

let HOMEOMORPHISM_INJECTIVE_OPEN_MAP = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u))
        ==> ?g. homeomorphism (s,t) (f,g)`;;

let HOMEOMORPHISM_INJECTIVE_CLOSED_MAP = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean t) (IMAGE f u))
        ==> ?g. homeomorphism (s,t) (f,g)`;;

let HOMEOMORPHISM_IMP_OPEN_MAP = `!f:real^M->real^N g s t u.
        homeomorphism (s,t) (f,g) /\ open_in (subtopology euclidean s) u
        ==> open_in (subtopology euclidean t) (IMAGE f u)`;;

let HOMEOMORPHISM_IMP_CLOSED_MAP = `!f:real^M->real^N g s t u.
        homeomorphism (s,t) (f,g) /\ closed_in (subtopology euclidean s) u
        ==> closed_in (subtopology euclidean t) (IMAGE f u)`;;

let HOMEOMORPHISM_INJECTIVE_OPEN_MAP_EQ = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((?g. homeomorphism (s,t) (f,g)) <=>
             !u. open_in (subtopology euclidean s) u
                 ==> open_in (subtopology euclidean t) (IMAGE f u))`;;

let HOMEOMORPHISM_INJECTIVE_CLOSED_MAP_EQ = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((?g. homeomorphism (s,t) (f,g)) <=>
             !u. closed_in (subtopology euclidean s) u
                 ==> closed_in (subtopology euclidean t) (IMAGE f u))`;;

let INJECTIVE_MAP_OPEN_IFF_CLOSED = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((!u. open_in (subtopology euclidean s) u
                  ==> open_in (subtopology euclidean t) (IMAGE f u)) <=>
             (!u. closed_in (subtopology euclidean s) u
                  ==> closed_in (subtopology euclidean t) (IMAGE f u)))`;;

(* ------------------------------------------------------------------------- *)
(* Transformation theorems for open, interior etc. under homeomorphism.      *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_OPEN_IN_EQ = `!f:real^M->real^N g s t u v.
        homeomorphism (s,t) (f,g) /\ u SUBSET s /\ v SUBSET s
        ==> (open_in (subtopology euclidean (IMAGE f u)) (IMAGE f v) <=>
             open_in  (subtopology euclidean u) v)`;;

let HOMEOMORPHISM_OPENNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (open_in (subtopology euclidean t) (IMAGE f k) <=>
             open_in (subtopology euclidean s) k)`;;

let HOMEOMORPHISM_CLOSED_IN_EQ = `!f:real^M->real^N g s t u v.
        homeomorphism (s,t) (f,g) /\ u SUBSET s /\ v SUBSET s
        ==> (closed_in (subtopology euclidean (IMAGE f u)) (IMAGE f v) <=>
             closed_in  (subtopology euclidean u) v)`;;

let HOMEOMORPHISM_CLOSEDNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (closed_in (subtopology euclidean t) (IMAGE f k) <=>
             closed_in (subtopology euclidean s) k)`;;

let HOMEOMORPHISM_DERIVED_SET_OF = `!f:real^M->real^N g s t u.
           homeomorphism (s,t) (f,g) /\ u SUBSET s
           ==> IMAGE f ((subtopology euclidean s) derived_set_of u) =
               (subtopology euclidean t) derived_set_of (IMAGE f u)`;;

let HOMEOMORPHISM_CLOSURE_OF = `!f:real^M->real^N g s t u.
           homeomorphism (s,t) (f,g) /\ u SUBSET s
           ==> IMAGE f ((subtopology euclidean s) closure_of u) =
               (subtopology euclidean t) closure_of (IMAGE f u)`;;

let HOMEOMORPHISM_INTERIOR_OF = `!f:real^M->real^N g s t u.
           homeomorphism (s,t) (f,g) /\ u SUBSET s
           ==> IMAGE f ((subtopology euclidean s) interior_of u) =
               (subtopology euclidean t) interior_of (IMAGE f u)`;;

let HOMEOMORPHISM_FRONTIER_OF = `!f:real^M->real^N g s t u.
           homeomorphism (s,t) (f,g) /\ u SUBSET s
           ==> IMAGE f ((subtopology euclidean s) frontier_of u) =
               (subtopology euclidean t) frontier_of (IMAGE f u)`;;

let HOMEOMORPHISM_CLOSURE = `!f:real^M->real^N g s t u.
        homeomorphism (s,t) (f,g) /\ u SUBSET s
        ==> t INTER closure (IMAGE f u) = IMAGE f (s INTER closure u)`;;

let HOMEOMORPHISM_CONNECTED_COMPONENT = `!f:real^M->real^N g s t x.
        homeomorphism (s,t) (f,g) /\ x IN s
        ==> connected_component (IMAGE f s) (f x) =
            IMAGE f (connected_component s x)`;;

let HOMEOMORPHISM_COMPONENTS = `!f:real^M->real^N g s t.
        homeomorphism (s,t) (f,g)
        ==> components t = IMAGE (IMAGE f) (components s)`;;

let LOCAL_HOMEOMORPHISM_IMP_OPEN_MAP = `!f:real^M->real^N s t.
        (!x. x IN s
             ==> ?u v g. x IN u /\
                         open_in (subtopology euclidean s) u /\
                         open_in (subtopology euclidean t) v /\
                         homeomorphism (u,v) (f,g))
        ==> !u. open_in (subtopology euclidean s) u
                ==> open_in (subtopology euclidean t) (IMAGE f u)`;;

let DERIVED_SET_OF_TRANSLATION = `!a:real^N u s.
        (subtopology euclidean (IMAGE (\x. a + x) u)) derived_set_of
        (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (subtopology euclidean u derived_set_of s)`;;

add_translation_invariants [DERIVED_SET_OF_TRANSLATION];;

let CLOSURE_OF_TRANSLATION = `!a:real^N u s.
        (subtopology euclidean (IMAGE (\x. a + x) u)) closure_of
        (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (subtopology euclidean u closure_of s)`;;

add_translation_invariants [CLOSURE_OF_TRANSLATION];;

let INTERIOR_OF_TRANSLATION = `!a:real^N u s.
        (subtopology euclidean (IMAGE (\x. a + x) u)) interior_of
        (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (subtopology euclidean u interior_of s)`;;

add_translation_invariants [INTERIOR_OF_TRANSLATION];;

let FRONTIER_OF_TRANSLATION = `!a:real^N u s.
        (subtopology euclidean (IMAGE (\x. a + x) u)) frontier_of
        (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (subtopology euclidean u frontier_of s)`;;

add_translation_invariants [FRONTIER_OF_TRANSLATION];;

let DERIVED_SET_OF_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N u s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (subtopology euclidean (IMAGE f u)) derived_set_of (IMAGE f s) =
            IMAGE f (subtopology euclidean u derived_set_of s)`;;

add_linear_invariants [DERIVED_SET_OF_INJECTIVE_LINEAR_IMAGE];;

let CLOSURE_OF_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N u s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (subtopology euclidean (IMAGE f u)) closure_of (IMAGE f s) =
            IMAGE f (subtopology euclidean u closure_of s)`;;

add_linear_invariants [CLOSURE_OF_INJECTIVE_LINEAR_IMAGE];;

let FRONTIER_OF_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N u s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (subtopology euclidean (IMAGE f u)) frontier_of (IMAGE f s) =
            IMAGE f (subtopology euclidean u frontier_of s)`;;

add_linear_invariants [FRONTIER_OF_INJECTIVE_LINEAR_IMAGE];;

let INTERIOR_OF_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N u s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (subtopology euclidean (IMAGE f u)) interior_of (IMAGE f s) =
            IMAGE f (subtopology euclidean u interior_of s)`;;

add_linear_invariants [INTERIOR_OF_INJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Relatively weak hypotheses if the domain of the function is compact.      *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_CLOSED_MAP_EXPLICIT = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s
        ==> !u. closed_in (subtopology euclidean s) u
                ==> closed_in (subtopology euclidean t) (IMAGE f u)`;;

let CONTINUOUS_IMP_QUOTIENT_MAP_EXPLICIT = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s
        ==> !u. u SUBSET t
                ==> (open_in (subtopology euclidean s)
                             {x | x IN s /\ f x IN u} <=>
                     open_in (subtopology euclidean t) u)`;;

let CONTINUOUS_ON_INVERSE = `!f:real^M->real^N g s.
        f continuous_on s /\ compact s /\ (!x. x IN s ==> (g(f(x)) = x))
        ==> g continuous_on (IMAGE f s)`;;

let HOMEOMORPHISM_COMPACT = `!s f t. compact s /\ f continuous_on s /\ (IMAGE f s = t) /\
           (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> ?g. homeomorphism(s,t) (f,g)`;;

let HOMEOMORPHIC_COMPACT = `!s f t. compact s /\ f continuous_on s /\ (IMAGE f s = t) /\
           (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> s homeomorphic t`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about composition of homeomorphisms.                               *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_FROM_COMPOSITION_SURJECTIVE = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (?h. homeomorphism (s,u) (g o f,h))
        ==> (?f'. homeomorphism (s,t) (f,f')) /\
            (?g'. homeomorphism (t,u) (g,g'))`;;

let HOMEOMORPHISM_FROM_COMPOSITION_INJECTIVE = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!x y. x IN t /\ y IN t /\ g x = g y ==> x = y) /\
        (?h. homeomorphism (s,u) (g o f,h))
        ==> (?f'. homeomorphism (s,t) (f,f')) /\
            (?g'. homeomorphism (t,u) (g,g'))`;;

(* ------------------------------------------------------------------------- *)
(* Preservation of topological properties.                                   *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_COMPACTNESS = `!s t. s homeomorphic t ==> (compact s <=> compact t)`;;

let HOMEOMORPHIC_CONNECTEDNESS = `!s t. s homeomorphic t ==> (connected s <=> connected t)`;;

let HOMEOMORPHISM_COMPACTNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (compact(IMAGE f k) <=> compact k)`;;

let HOMEOMORPHISM_CONNECTEDNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (connected(IMAGE f k) <=> connected k)`;;

(* ------------------------------------------------------------------------- *)
(* Results on translation, scaling etc.                                      *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_SCALING = `!s:real^N->bool c. ~(c = &0) ==> s homeomorphic (IMAGE (\x. c % x) s)`;;

let HOMEOMORPHIC_TRANSLATION = `!s a:real^N. s homeomorphic (IMAGE (\x. a + x) s)`;;

let HOMEOMORPHIC_AFFINITY = `!s a:real^N c. ~(c = &0) ==> s homeomorphic (IMAGE (\x. c % x + a) s)`;;

let HOMEOMORPHIC_BALLS = `(!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> ball(a,d) homeomorphic ball(b,e))`
and HOMEOMORPHIC_CBALLS = `(!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> cball(a,d) homeomorphic cball(b,e))`
and HOMEOMORPHIC_SPHERES = `(!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> sphere(a,d) homeomorphic sphere(b,e))`;;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of one-point compactifications.                             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_ONE_POINT_COMPACTIFICATIONS = `!f:real^M->real^N g:real^N->real^M s t a b.
        compact s /\ compact t /\ a IN s /\ b IN t /\
        homeomorphism (s DELETE a,t DELETE b) (f,g)
        ==> ?f' g'. homeomorphism (s,t) (f',g') /\
                    f' a = b /\ g' b = a /\
                    (!x. x IN s DELETE a ==> f' x = f x) /\
                    (!y. y IN t DELETE b ==> g' y = g y)`;;

let HOMEOMORPHIC_ONE_POINT_COMPACTIFICATIONS = `!s:real^M->bool t:real^N->bool a b.
        compact s /\ compact t /\ a IN s /\ b IN t /\
        (s DELETE a) homeomorphic (t DELETE b)
        ==> s homeomorphic t`;;

let BOUNDED_IMAGE_IN_COMPACTIFICATION = `!f:real^M->real^N g u s t c.
        homeomorphism (u,s DIFF t) (f,g) /\
        compact s /\ closed u /\ c SUBSET u
        ==> (bounded c <=> closure(IMAGE f c) INTER t = {})`;;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms between open intervals in real^1 and then in real^N.       *)
(* Could prove similar things for closed intervals, but they drop out of     *)
(* later stuff in "convex.ml" even more easily.                              *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_OPEN_INTERVALS_1 = `!a b c d.
        drop a < drop b /\ drop c < drop d
        ==> interval(a,b) homeomorphic interval(c,d)`;;

let HOMEOMORPHIC_OPEN_INTERVAL_UNIV_1 = `!a b. drop a < drop b ==> interval(a,b) homeomorphic (:real^1)`;;

let HOMEOMORPHIC_OPEN_INTERVALS = `!a b:real^N c d:real^N.
        (interval(a,b) = {} <=> interval(c,d) = {})
        ==> interval(a,b) homeomorphic interval(c,d)`;;

let HOMEOMORPHIC_OPEN_INTERVAL_UNIV = `!a b:real^N.
        ~(interval(a,b) = {})
        ==> interval(a,b) homeomorphic (:real^N)`;;

let HOMEOMORPHIC_BALL_UNIV = `!a:real^N r. &0 < r ==> ball(a,r) homeomorphic (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Cardinalities of various useful sets.                                     *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_EUCLIDEAN = `(:real^N) =_c (:real)`;;

let UNCOUNTABLE_EUCLIDEAN = `~COUNTABLE(:real^N)`;;

let CARD_EQ_INTERVAL = `(!a b:real^N. ~(interval(a,b) = {}) ==> interval[a,b] =_c (:real)) /\
   (!a b:real^N. ~(interval(a,b) = {}) ==> interval(a,b) =_c (:real))`;;

let UNCOUNTABLE_INTERVAL = `(!a b. ~(interval(a,b) = {}) ==> ~COUNTABLE(interval[a,b])) /\
   (!a b. ~(interval(a,b) = {}) ==> ~COUNTABLE(interval(a,b)))`;;

let COUNTABLE_OPEN_INTERVAL = `!a b. COUNTABLE(interval(a,b)) <=> interval(a,b) = {}`;;

let CARD_EQ_OPEN = `!s:real^N->bool. open s /\ ~(s = {}) ==> s =_c (:real)`;;

let UNCOUNTABLE_OPEN = `!s:real^N->bool. open s /\ ~(s = {}) ==> ~(COUNTABLE s)`;;

let CARD_EQ_BALL = `!a:real^N r. &0 < r ==> ball(a,r) =_c (:real)`;;

let CARD_EQ_CBALL = `!a:real^N r. &0 < r ==> cball(a,r) =_c (:real)`;;

let FINITE_IMP_NOT_OPEN = `!s:real^N->bool. FINITE s /\ ~(s = {}) ==> ~(open s)`;;

let OPEN_IMP_INFINITE = `!s. open s ==> s = {} \/ INFINITE s`;;

let EMPTY_INTERIOR_FINITE = `!s:real^N->bool. FINITE s ==> interior s = {}`;;

let FINITE_CBALL = `!a:real^N r. FINITE(cball(a,r)) <=> r <= &0`;;

let FINITE_BALL = `!a:real^N r. FINITE(ball(a,r)) <=> r <= &0`;;

let CARD_EQ_CONNECTED = `!s a b:real^N.
        connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`;;

let UNCOUNTABLE_CONNECTED = `!s a b:real^N.
        connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`;;

let CARD_LT_IMP_DISCONNECTED = `!s x:real^N. s <_c (:real) /\ x IN s ==> connected_component s x = {x}`;;

let COUNTABLE_IMP_DISCONNECTED = `!s x:real^N. COUNTABLE s /\ x IN s ==> connected_component s x = {x}`;;

let CONNECTED_CARD_EQ_IFF_NONTRIVIAL = `!s:real^N->bool.
        connected s ==> (s =_c (:real) <=> ~(?a. s SUBSET {a}))`;;

let CONNECTED_CARD_LT_IFF_TRIVIAL = `!s:real^N->bool. connected s ==> (s <_c (:real) <=> ?a. s SUBSET {a})`;;

let SMALL_IMP_TOTALLY_DISCONNECTED = `!s:real^N->bool. s <_c (:real) ==> components s = IMAGE (\x. {x}) s`;;

let FINITE_IMP_TOTALLY_DISCONNECTED = `!s:real^N->bool. FINITE s ==> components s = IMAGE (\x. {x}) s`;;

(* ------------------------------------------------------------------------- *)
(* "Iff" forms of constancy of function from connected set into a set that   *)
(* is smaller than R, or countable, or finite, or disconnected, or discrete. *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_DISCONNECTED_RANGE_CONSTANT_EQ = `(!s. connected s <=>
         !f:real^M->real^N t.
            f continuous_on s /\ IMAGE f s SUBSET t /\
            (!y. y IN t ==> connected_component t y = {y})
            ==> ?a. !x. x IN s ==> f x = a)`
and CONTINUOUS_DISCRETE_RANGE_CONSTANT_EQ = `(!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\
            (!x. x IN s
                 ==> ?e. &0 < e /\
                         !y. y IN s /\ ~(f y = f x) ==> e <= norm(f y - f x))
            ==> ?a. !x. x IN s ==> f x = a)`
and CONTINUOUS_FINITE_RANGE_CONSTANT_EQ = `(!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\ FINITE(IMAGE f s)
            ==> ?a. !x. x IN s ==> f x = a)`;;

let CONTINUOUS_DISCONNECTED_RANGE_CONSTANT = `!f:real^M->real^N s.
        connected s /\
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!y. y IN t ==> connected_component t y = {y})
        ==> ?a. !x. x IN s ==> f x = a`;;

let CONTINUOUS_DISCRETE_RANGE_CONSTANT = `!f:real^M->real^N s.
        connected s /\
        f continuous_on s /\
        (!x. x IN s
             ==> ?e. &0 < e /\
                     !y. y IN s /\ ~(f y = f x) ==> e <= norm(f y - f x))
        ==> ?a. !x. x IN s ==> f x = a`;;

let CONTINUOUS_FINITE_RANGE_CONSTANT = `!f:real^M->real^N s.
        connected s /\
        f continuous_on s /\
        FINITE(IMAGE f s)
        ==> ?a. !x. x IN s ==> f x = a`;;

let CONTINUOUS_COUNTABLE_RANGE_CONSTANT_EQ = `!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\ COUNTABLE(IMAGE f s)
            ==> ?a. !x. x IN s ==> f x = a`;;

let CONTINUOUS_CARD_LT_RANGE_CONSTANT_EQ = `!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\ (IMAGE f s) <_c (:real)
            ==> ?a. !x. x IN s ==> f x = a`;;

let CONTINUOUS_COUNTABLE_RANGE_CONSTANT = `!f:real^M->real^N s.
        connected s /\ f continuous_on s /\ COUNTABLE(IMAGE f s)
        ==> ?a. !x. x IN s ==> f x = a`;;

let CONTINUOUS_CARD_LT_RANGE_CONSTANT = `!f:real^M->real^N s.
        connected s /\ f continuous_on s /\ (IMAGE f s) <_c (:real)
        ==> ?a. !x. x IN s ==> f x = a`;;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of hyperplanes.                                             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_HYPERPLANES = `!a:real^N b c:real^N d.
        ~(a = vec 0) /\ ~(c = vec 0)
        ==> {x | a dot x = b} homeomorphic {x | c dot x = d}`;;

let HOMEOMORPHIC_HYPERPLANE_STANDARD_HYPERPLANE = `!a:real^N b k c.
        ~(a = vec 0) /\ 1 <= k /\ k <= dimindex(:N)
        ==> {x | a dot x = b} homeomorphic {x:real^N | x$k = c}`;;

let HOMEOMORPHIC_STANDARD_HYPERPLANE_HYPERPLANE = `!a:real^N b k c.
        ~(a = vec 0) /\ 1 <= k /\ k <= dimindex(:N)
        ==> {x:real^N | x$k = c} homeomorphic {x | a dot x = b}`;;

let HOMEOMORPHIC_HYPERPLANE_UNIV = `!a b. ~(a = vec 0) /\ dimindex(:N) = dimindex(:M) + 1
         ==> {x:real^N | a dot x = b} homeomorphic (:real^M)`;;

(* ------------------------------------------------------------------------- *)
(* "Isometry" (up to constant bounds) of injective linear map etc.           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_ISOMETRIC = `!f s e x.
        &0 < e /\ subspace s /\
        linear f /\ (!x. x IN s ==> norm(f x) >= e * norm(x)) /\
        (!n. x(n) IN s) /\ cauchy(f o x)
        ==> cauchy x`;;

let COMPLETE_ISOMETRIC_IMAGE = `!f:real^M->real^N s e.
        &0 < e /\ subspace s /\
        linear f /\ (!x. x IN s ==> norm(f x) >= e * norm(x)) /\
        complete s
        ==> complete(IMAGE f s)`;;

let INJECTIVE_IMP_ISOMETRIC = `!f:real^M->real^N s.
        closed s /\ subspace s /\
        linear f /\ (!x. x IN s /\ (f x = vec 0) ==> (x = vec 0))
        ==> ?e. &0 < e /\ !x. x IN s ==> norm(f x) >= e * norm(x)`;;

let CLOSED_INJECTIVE_IMAGE_SUBSPACE = `!f s. subspace s /\
         linear f /\
         (!x. x IN s /\ f(x) = vec 0 ==> x = vec 0) /\
         closed s
         ==> closed(IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* Relating linear images to open/closed/interior/closure.                   *)
(* ------------------------------------------------------------------------- *)

let OPEN_SURJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> !s. open s ==> open(IMAGE f s)`;;

let OPEN_BIJECTIVE_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (open(IMAGE f s) <=> open s)`;;

add_linear_invariants [OPEN_BIJECTIVE_LINEAR_IMAGE_EQ];;

let OPEN_INVERTIBLE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ invertible(matrix f) /\ open s
        ==> open(IMAGE f s)`;;

let CLOSED_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> !s. closed s ==> closed(IMAGE f s)`;;

let CLOSED_INJECTIVE_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (closed(IMAGE f s) <=> closed s)`;;

add_linear_invariants [CLOSED_INJECTIVE_LINEAR_IMAGE_EQ];;

let CLOSURE_LINEAR_IMAGE_SUBSET = `!f:real^M->real^N s.
        linear f ==> IMAGE f (closure s) SUBSET closure(IMAGE f s)`;;

let CLOSURE_INJECTIVE_LINEAR_IMAGE  = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> closure(IMAGE f s) = IMAGE f (closure s)`;;

add_linear_invariants [CLOSURE_INJECTIVE_LINEAR_IMAGE];;

let CLOSURE_BOUNDED_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ bounded s
        ==> closure(IMAGE f s) = IMAGE f (closure s)`;;

let LINEAR_INTERIOR_IMAGE_SUBSET = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
       ==> interior(IMAGE f s) SUBSET IMAGE f (interior s)`;;

let LINEAR_IMAGE_SUBSET_INTERIOR = `!f:real^M->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> IMAGE f (interior s) SUBSET interior(IMAGE f s)`;;

let INTERIOR_BIJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`;;

add_linear_invariants [INTERIOR_BIJECTIVE_LINEAR_IMAGE];;

let FRONTIER_BIJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`;;

add_linear_invariants [FRONTIER_BIJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Corollaries, reformulations and special cases for M = N.                  *)
(* ------------------------------------------------------------------------- *)

let IN_INTERIOR_LINEAR_IMAGE = `!f:real^M->real^N g s x.
        linear f /\ linear g /\ (f o g = I) /\ x IN interior s
        ==> (f x) IN interior (IMAGE f s)`;;

let LINEAR_OPEN_MAPPING = `!f:real^M->real^N g.
        linear f /\ linear g /\ (f o g = I)
        ==> !s. open s ==> open(IMAGE f s)`;;

let INTERIOR_INJECTIVE_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`;;

let INTERIOR_SURJECTIVE_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`;;

let CLOSURE_SURJECTIVE_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> closure(IMAGE f s) = IMAGE f (closure s)`;;

let FRONTIER_INJECTIVE_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`;;

let FRONTIER_SURJECTIVE_LINEAR_IMAGE = `!f:real^N->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`;;

let COMPLETE_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> !s. complete s ==> complete(IMAGE f s)`;;

let COMPLETE_INJECTIVE_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (complete(IMAGE f s) <=> complete s)`;;

add_linear_invariants [COMPLETE_INJECTIVE_LINEAR_IMAGE_EQ];;

let LIMPT_INJECTIVE_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((f x) limit_point_of (IMAGE f s) <=> x limit_point_of s)`;;

add_linear_invariants [LIMPT_INJECTIVE_LINEAR_IMAGE_EQ];;

let LIMPT_TRANSLATION_EQ = `!a s x. (a + x) limit_point_of (IMAGE (\y. a + y) s) <=> x limit_point_of s`;;

add_translation_invariants [LIMPT_TRANSLATION_EQ];;

let OPEN_OPEN_LEFT_PROJECTION = `!s t:real^(M,N)finite_sum->bool.
        open s /\ open t ==> open {x | x IN s /\ ?y. pastecart x y IN t}`;;

let OPEN_OPEN_RIGHT_PROJECTION = `!s t:real^(M,N)finite_sum->bool.
        open s /\ open t ==> open {y | y IN s /\ ?x. pastecart x y IN t}`;;

let OPEN_MAP_FSTCART = `!s:real^(M,N)finite_sum->bool.
        open s ==> open(IMAGE fstcart s)`;;

let OPEN_MAP_SNDCART = `!s:real^(M,N)finite_sum->bool.
        open s ==> open(IMAGE sndcart s)`;;

(* ------------------------------------------------------------------------- *)
(* Even more special cases.                                                  *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_SCALING = `!s:real^N->bool c.
        interior (IMAGE (\x. c % x) s) =
        if c = &0 then {} else IMAGE (\x. c % x) (interior s)`;;

let INTERIOR_AFFINITY = `!s m c:real^N.
        interior(IMAGE (\x. m % x + c) s) =
        if m = &0 then {} else IMAGE (\x. m % x + c) (interior s)`;;

let CLOSURE_SCALING = `!s:real^N->bool c.
        closure(IMAGE (\x. c % x) s) = IMAGE (\x. c % x) (closure s)`;;

let CLOSURE_AFFINITY = `!s m c:real^N.
        closure(IMAGE (\x. m % x + c) s) = IMAGE (\x. m % x + c) (closure s)`;;

let FRONTIER_SCALING = `!s:real^N->bool c.
        frontier (IMAGE (\x. c % x) s) =
        if c = &0 /\ s = (:real^N) then {vec 0}
        else IMAGE (\x. c % x) (frontier s)`;;

let FRONTIER_AFFINITY = `!s m c:real^N.
        frontier (IMAGE (\x. m % x + c) s) =
        if m = &0 /\ s = (:real^N) then {c}
        else IMAGE (\x. m % x + c) (frontier s)`;;

let INTERIOR_NEGATIONS = `!s. interior(IMAGE (--) s) = IMAGE (--) (interior s)`;;

let SYMMETRIC_INTERIOR = `!s:real^N->bool.
        (!x. x IN s ==> --x IN s)
        ==> !x. x IN interior s ==> (--x) IN interior s`;;

let CLOSURE_NEGATIONS = `!s. closure(IMAGE (--) s) = IMAGE (--) (closure s)`;;

let SYMMETRIC_CLOSURE = `!s:real^N->bool.
        (!x. x IN s ==> --x IN s)
        ==> !x. x IN closure s ==> (--x) IN closure s`;;

(* ------------------------------------------------------------------------- *)
(* Some properties of a canonical subspace.                                  *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_SUBSTANDARD = `!d. subspace
         {x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0}`;;

let CLOSED_SUBSTANDARD = `!d. closed
        {x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0}`;;

let DIM_SUBSTANDARD = `!d. d <= dimindex(:N)
       ==> (dim {x:real^N | !i. d < i /\ i <= dimindex(:N)
                                ==> x$i = &0} =
            d)`;;

(* ------------------------------------------------------------------------- *)
(* Hence closure and completeness of all subspaces.                          *)
(* ------------------------------------------------------------------------- *)

let CLOSED_SUBSPACE = `!s:real^N->bool. subspace s ==> closed s`;;

let COMPLETE_SUBSPACE = `!s:real^N->bool. subspace s ==> complete s`;;

let CLOSED_SPAN = `!s. closed(span s)`;;

let CLOSURE_SUBSET_SPAN = `!s:real^N->bool. closure s SUBSET span s`;;

let DIM_CLOSURE = `!s:real^N->bool. dim(closure s) = dim s`;;

let CLOSED_BOUNDEDPREIM_CONTINUOUS_IMAGE = `!f:real^M->real^N s.
      closed s /\ f continuous_on s /\
      (!e. bounded {x | x IN s /\ norm(f x) <= e})
      ==> closed(IMAGE f s)`;;

let CLOSED_INJECTIVE_IMAGE_SUBSET_SUBSPACE = `!f:real^M->real^N s t.
        closed s /\ s SUBSET t /\ subspace t /\
        linear f /\
        (!x. x IN t /\ f(x) = vec 0 ==> x = vec 0)
        ==> closed(IMAGE f s)`;;

let BASIS_COORDINATES_LIPSCHITZ = `!b:real^N->bool.
        independent b
        ==> ?B. &0 < B /\
                !c v. v IN b
                      ==> abs(c v) <= B * norm(vsum b (\v. c(v) % v))`;;

let COMPLEMENTARY_SUM_COMPONENTS_LIPSCHITZ = `!s t:real^N->bool.
        subspace s /\ subspace t /\ s INTER t SUBSET {vec 0}
        ==> ?B. &0 < B /\
                !x y. x IN s /\ y IN t ==> norm(x) <= B * norm(x + y)`;;

let BASIS_COORDINATES_CONTINUOUS = `!b:real^N->bool e.
        independent b /\ &0 < e
        ==> ?d. &0 < d /\
                !c. norm(vsum b (\v. c(v) % v)) < d
                    ==> !v. v IN b ==> abs(c v) < e`;;

let COMPLEMENTARY_SUM_HOMEOMORPHIC_PCROSS = `!s t:real^N->bool.
        span s INTER span t SUBSET {vec 0}
        ==> {x + y | x IN s /\ y IN t} homeomorphic (s PCROSS t)`;;

(* ------------------------------------------------------------------------- *)
(* Affine transformations of intervals.                                      *)
(* ------------------------------------------------------------------------- *)

let AFFINITY_INVERSES = `!m c. ~(m = &0)
         ==> (\x. m % x + c) o (\x. inv(m) % x + (--(inv(m) % c))) = I /\
             (\x. inv(m) % x + (--(inv(m) % c))) o (\x. m % x + c) = I`;;

let REAL_AFFINITY_LE = `!m c x y. &0 < m ==> (m * x + c <= y <=> x <= inv(m) * y + --(c / m))`;;

let REAL_LE_AFFINITY = `!m c x y. &0 < m ==> (y <= m * x + c <=> inv(m) * y + --(c / m) <= x)`;;

let REAL_AFFINITY_LT = `!m c x y. &0 < m ==> (m * x + c < y <=> x < inv(m) * y + --(c / m))`;;

let REAL_LT_AFFINITY = `!m c x y. &0 < m ==> (y < m * x + c <=> inv(m) * y + --(c / m) < x)`;;

let REAL_AFFINITY_EQ = `!m c x y. ~(m = &0) ==> (m * x + c = y <=> x = inv(m) * y + --(c / m))`;;

let REAL_EQ_AFFINITY = `!m c x y. ~(m = &0) ==> (y = m * x + c  <=> inv(m) * y + --(c / m) = x)`;;

let VECTOR_AFFINITY_EQ = `!m c x y. ~(m = &0)
             ==> (m % x + c = y <=> x = inv(m) % y + --(inv(m) % c))`;;

let VECTOR_EQ_AFFINITY = `!m c x y. ~(m = &0)
             ==> (y = m % x + c <=> inv(m) % y + --(inv(m) % c) = x)`;;

let IMAGE_AFFINITY_INTERVAL = `!a b:real^N m c.
        IMAGE (\x. m % x + c) (interval[a,b]) =
            if interval[a,b] = {} then {}
            else if &0 <= m then interval[m % a + c,m % b + c]
            else interval[m % b + c,m % a + c]`;;

(* ------------------------------------------------------------------------- *)
(* Some matrix identities are easier to deduce for invertible matrices. We   *)
(* can then extend by continuity, which is why this material needs to be     *)
(* here after basic topological notions have been defined.                   *)
(* ------------------------------------------------------------------------- *)

let LIM_LIFT_DET = `!(A:A->real^N^N) (B:real^N^N) net.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N)
               ==> ((\x. lift(A x$i$j)) --> lift(B$i$j)) net)
        ==> ((\x. lift(det(A x))) --> lift(det B)) net`;;

let LIM_COFACTOR = `!net A:A->real^N^N B.
        (!x. ((\a. A a ** x) --> B ** x) net)
        ==> !x. ((\a. cofactor(A a) ** x) --> cofactor B ** x) net`;;

let LIM_MATRIX_TRANSP = `!net A:A->real^M^N B.
        (!x. ((\a. transp(A a) ** x) --> transp B ** x) net) <=>
        (!x. ((\a. A a ** x) --> B ** x) net)`;;

let LIM_MATRIX_INV = `!net A:A->real^N^N B.
        (!x. ((\a. A a ** x) --> B ** x) net) /\ ~(det B = &0)
        ==> !x. ((\a. matrix_inv(A a) ** x) --> matrix_inv B ** x) net`;;

let CONTINUOUS_LIFT_DET = `!(A:A->real^N^N) net.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N)
               ==> (\x. lift(A x$i$j)) continuous net)
        ==> (\x. lift(det(A x))) continuous net`;;

let CONTINUOUS_ON_LIFT_DET = `!A:real^M->real^N^N s.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N)
               ==> (\x. lift(A x$i$j)) continuous_on s)
        ==> (\x. lift(det(A x))) continuous_on s`;;

let CONTINUOUS_DET_VECTORIZE = `!net A:A->real^N^N.
        (\a. vectorize(A a)) continuous net
        ==> (\a. lift(det(A a))) continuous net`;;

let CONTINUOUS_ON_DET_VECTORIZE = `!A:real^M->real^N^N.
        (\a. vectorize(A a)) continuous_on s
        ==> (\a. lift(det(A a))) continuous_on s`;;

let CONTINUOUS_DET_EXPLICIT = `!A:real^N^N e.
        &0 < e
        ==> ?d. &0 < d /\
                !A':real^N^N.
                    (!i j. 1 <= i /\ i <= dimindex(:N) /\
                           1 <= j /\ j <= dimindex(:N)
                           ==> abs(A'$i$j - A$i$j) < d)
                    ==> abs(det A' - det A) < e`;;

let NEARBY_INVERTIBLE_MATRIX = `!A:real^N^N.
     ?e. &0 < e /\ !x. ~(x = &0) /\ abs x < e ==> invertible(A + x %% mat 1)`;;

let NEARBY_INVERTIBLE_MATRIX_GEN = `!A B:real^N^N.
        invertible B
        ==> ?e. &0 < e /\
                !x. ~(x = &0) /\ abs x < e ==> invertible(A + x %% B)`;;

let MATRIX_WLOG_INVERTIBLE = `!P. (!A:real^N^N. invertible A ==> P A) /\
       (!A:real^N^N. ?d. &0 < d /\
                         closed {x | x IN cball(vec 0,d) /\
                                     P(A + drop x %% mat 1)})
       ==> !A:real^N^N. P A`;;

let SYLVESTER_DETERMINANT_IDENTITY = `!A:real^N^M B:real^M^N. det(mat 1 + A ** B) = det(mat 1 + B ** A)`;;

let COFACTOR_MATRIX_MUL = `!A B:real^N^N. cofactor(A ** B) = cofactor(A) ** cofactor(B)`;;

let DET_COFACTOR = `!A:real^N^N. det(cofactor A) = det(A) pow (dimindex(:N) - 1)`;;

let INVERTIBLE_COFACTOR = `!A:real^N^N. invertible(cofactor A) <=> dimindex(:N) = 1 \/ invertible A`;;

let COFACTOR_COFACTOR = `!A:real^N^N.
     2 <= dimindex(:N)
     ==> cofactor(cofactor A) = (det(A) pow (dimindex(:N) - 2)) %% A`;;

let RANK_COFACTOR_EQ_FULL = `!A:real^N^N. rank(cofactor A) = dimindex(:N) <=>
                dimindex(:N) = 1 \/ rank A = dimindex(:N)`;;

let COFACTOR_EQ_0 = `!A:real^N^N. cofactor A = mat 0 <=> rank(A) < dimindex(:N) - 1`;;

let RANK_COFACTOR_EQ_1 = `!A:real^N^N. rank(cofactor A) = 1 <=>
                dimindex(:N) = 1 \/ rank A = dimindex(:N) - 1`;;

let RANK_COFACTOR = `!A:real^N^N.
        rank(cofactor A) = if rank(A) = dimindex(:N) then dimindex(:N)
                           else if rank(A) = dimindex(:N) - 1 then 1
                           else 0`;;

let SAME_EIGENVALUES_TRANSP = `!A:real^N^N c.
     (?v. ~(v = vec 0) /\ transp(A) ** v = c % v) <=>
     (?v. ~(v = vec 0) /\ A ** v = c % v)`;;

let SAME_EIGENVALUES_SIMILAR = `!S:real^N^N A c.
        invertible S
        ==> ((?v. ~(v = vec 0) /\ (matrix_inv S ** A ** S) ** v = c % v) <=>
             (?v. ~(v = vec 0) /\ A ** v = c % v))`;;

let SAME_EIGENVALUES_MATRIX_MUL = `!A B:real^N^N c.
     (?v. ~(v = vec 0) /\ (A ** B) ** v = c % v) <=>
     (?v. ~(v = vec 0) /\ (B ** A) ** v = c % v)`;;

let SAME_EIGENVECTORS_MATRIX_INV = `!A:real^N^N c v.
        symmetric_matrix A
        ==> (matrix_inv A ** v = c % v <=> A ** v = inv(c) % v)`;;

let NORMAL_MATRIX_SAME_EIGENPAIRS_TRANSP = `!A:real^N^N.
        normal_matrix A
        ==> !c v. transp A ** v = c % v <=> A ** v = c % v`;;

let NORMAL_MATRIX_SAME_EIGENVECTORS_TRANSP = `!A:real^N^N.
        normal_matrix A
        ==> !v. ((?c. transp A ** v = c % v) <=> (?c. A ** v = c % v))`;;

(* ------------------------------------------------------------------------- *)
(* Not in so many words, but combining this with intermediate value theorem  *)
(* implies the determinant is an open map.                                   *)
(* ------------------------------------------------------------------------- *)

let DET_OPEN_MAP = `!A:real^N^N e.
        &0 < e
        ==> (?B:real^N^N. (!i j. abs(B$i$j - A$i$j) < e) /\ det B < det A) /\
            (?C:real^N^N. (!i j. abs(C$i$j - A$i$j) < e) /\ det C > det A)`;;

(* ------------------------------------------------------------------------- *)
(* Existence of eigenvectors. The proof is only in this file because it uses *)
(* a few simple results about continuous functions (at least                 *)
(* CONTINUOUS_ON_LIFT_DOT2, CONTINUOUS_ATTAINS_SUP and CLOSED_SUBSPACE).     *)
(* ------------------------------------------------------------------------- *)

let SELF_ADJOINT_HAS_EIGENVECTOR_IN_SUBSPACE = `!f:real^N->real^N s.
        linear f /\ adjoint f = f /\
        subspace s /\ ~(s = {vec 0}) /\ (!x. x IN s ==> f x IN s)
        ==> ?v c. v IN s /\ norm(v) = &1 /\ f(v) = c % v`;;

let SELF_ADJOINT_HAS_EIGENVECTOR = `!f:real^N->real^N.
        linear f /\ adjoint f = f ==> ?v c. norm(v) = &1 /\ f(v) = c % v`;;

let SELF_ADJOINT_HAS_EIGENVECTOR_BASIS_OF_SUBSPACE = `!f:real^N->real^N s.
        linear f /\ adjoint f = f /\
        subspace s /\ (!x. x IN s ==> f x IN s)
        ==> ?b. b SUBSET s /\
                pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1 /\ ?c. f(x) = c % x) /\
                independent b /\
                span b = s /\
                b HAS_SIZE dim s`;;

let SELF_ADJOINT_HAS_EIGENVECTOR_BASIS = `!f:real^N->real^N.
        linear f /\ adjoint f = f
        ==> ?b. pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1 /\ ?c. f(x) = c % x) /\
                independent b /\
                span b = (:real^N) /\
                b HAS_SIZE (dimindex(:N))`;;

let EIGENVALUE_LOWERBOUND_DOT = `!A:real^N^N a.
        symmetric_matrix A /\
        (!c v. A ** v = c % v /\ ~(v = vec 0) ==> a <= c)
        ==> !x. a * norm(x) pow 2 <= x dot (A ** x)`;;

let EIGENVALUE_LOWERBOUND_DOT_EQ = `!A:real^N^N a.
        symmetric_matrix A
        ==> ((!c v. A ** v = c % v /\ ~(v = vec 0) ==> a <= c) <=>
             (!x. a * norm(x) pow 2 <= x dot (A ** x)))`;;

(* ------------------------------------------------------------------------- *)
(* Diagonalization of symmetric matrix.                                      *)
(* ------------------------------------------------------------------------- *)

let SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT = `!A:real^N^N.
      symmetric_matrix A
      ==> ?P d. orthogonal_matrix P /\
                transp P ** A ** P = (lambda i j. if i = j then d i else &0)`;;

let SYMMETRIC_MATRIX_IMP_DIAGONALIZABLE = `!A:real^N^N.
     symmetric_matrix A
     ==> ?P. orthogonal_matrix P /\ diagonal_matrix(transp P ** A ** P)`;;

let SYMMETRIC_MATRIX_EQ_DIAGONALIZABLE = `!A:real^N^N.
     symmetric_matrix A <=>
     ?P. orthogonal_matrix P /\ diagonal_matrix(transp P ** A ** P)`;;

let SYMMETRIC_MATRIX_EQ_DIAGONALIZABLE_ALT = `!A:real^N^N.
        symmetric_matrix A <=>
        ?P D. orthogonal_matrix P /\ diagonal_matrix D /\
              A = transp P ** D ** P`;;

(* ------------------------------------------------------------------------- *)
(* Hence deduce more general results using diagonalization.                  *)
(* ------------------------------------------------------------------------- *)

let TRACE_MATRIX_INV_LMUL = `!A:real^N^M. trace(matrix_inv A ** A) = &(rank A)`;;

let TRACE_MATRIX_INV_RMUL = `!A:real^N^M. trace(A ** matrix_inv A) = &(rank A)`;;

let IDEMPOTENT_MATRIX_TRACE_EQ_RANK = `!A:real^N^N. A ** A = A ==> trace A = &(rank A)`;;

let POSITIVE_SEMIDEFINITE_EIGENVALUES = `!A:real^N^N. positive_semidefinite A <=>
                symmetric_matrix A /\
                !c v. A ** v = c % v /\ ~(v = vec 0) ==> &0 <= c`;;

let POSITIVE_DEFINITE_EIGENVALUES = `!A:real^N^N. positive_definite A <=>
                symmetric_matrix A /\
                !c v. A ** v = c % v /\ ~(v = vec 0) ==> &0 < c`;;

let POSITIVE_SEMIDEFINITE_COVARIANCE_EQ = `(!A:real^N^N. positive_semidefinite A <=>
                 ?S:real^N^N. A = transp S ** S)`
and POSITIVE_SEMIDEFINITE_COVARIANCE_EQ_ALT = `(!A:real^N^N. positive_semidefinite A <=>
                 ?S:real^N^N. positive_semidefinite S /\ A = transp S ** S)`;;

let POSITIVE_SEMIDEFINITE_SQRT_EQ = `!A:real^N^N.
        positive_semidefinite A <=>
        ?S:real^N^N. positive_semidefinite S /\ A = S ** S`;;

let POSITIVE_SEMIDEFINITE_SQRT = `!A:real^N^N. positive_semidefinite A ==> ?S:real^N^N. A = S ** S`;;

let POSITIVE_DEFINITE_COVARIANCE_EQ = `!A:real^N^N.
        positive_definite A <=>
        ?S:real^N^N. invertible S /\ transp S ** S = A`;;

let POSITIVE_DEFINITE_COVARIANCE_EQ_ALT = `!A:real^N^N.
        positive_definite A <=> ?S. positive_definite S /\ transp S ** S = A`;;

let DET_POSITIVE_SEMIDEFINITE = `!A:real^N^N. positive_semidefinite A ==> &0 <= det A`;;

let DET_POSITIVE_DEFINITE = `!A:real^N^N. positive_definite A ==> &0 < det A`;;

let POSITIVE_SEMIDEFINITE_DIAGONAL_INEQUALITY = `!A:real^N^N i j.
        positive_semidefinite A /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> A$i$j pow 2 <= A$i$i * A$j$j`;;

let TRACE_COVARIANCE_POSITIVE_SEMIDEFINITE_LE = `!A:real^N^N.
        positive_semidefinite A ==> trace(transp A ** A) <= trace(A) pow 2`;;

let TRACE_SQUARE_POSITIVE_SEMIDEFINITE_LE = `!A:real^N^N.
        positive_semidefinite A ==> trace(A ** A) <= trace(A) pow 2`;;

let TRACE_MUL_POSITIVE_SEMIDEFINITE_LE = `!A B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> trace(A ** B) <= trace(A) * trace(B)`;;

let POSITIVE_SEMIDEFINITE_ZERO_ROW = `!A:real^N^N i.
        positive_semidefinite A /\ 1 <= i /\ i <= dimindex(:N) /\ A$i$i = &0
        ==> row i A = vec 0`;;

let POSITIVE_SEMIDEFINITE_ZERO_COLUMN = `!A:real^N^N i.
        positive_semidefinite A /\ 1 <= i /\ i <= dimindex(:N) /\ A$i$i = &0
        ==> column i A = vec 0`;;

let POSITIVE_SEMIDEFINITE_TRACE_EQ_0 = `!A:real^N^N. positive_semidefinite A ==> (trace A = &0 <=> A = mat 0)`;;

let COVARIANCE_MATRIX_EQ_SQUARE = `!A:real^N^N. transp A ** A = A ** A <=> symmetric_matrix A`;;

let TRACE_MUL_POSITIVE_SEMIDEFINITE = `(!A:real^N^N B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> &0 <= trace(A ** B))`
and TRACE_MUL_POSITIVE_SEMIDEFINITE_EQ_0 = `(!A:real^N^N B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> (trace(A ** B) = &0 <=> A ** B = mat 0))`;;

let TRACE_MUL_POSITIVE_SEMIDEFINITE_DEFINITE_EQ_0 = `!A:real^N^N B:real^N^N.
        positive_semidefinite A /\ positive_definite B
        ==> (trace(A ** B) = &0 <=> A = mat 0)`;;

let TRACE_MUL_POSITIVE_DEFINITE_SEMIDEFINITE_EQ_0 = `!A:real^N^N B:real^N^N.
        positive_definite A /\ positive_semidefinite B
        ==> (trace(A ** B) = &0 <=> B = mat 0)`;;

let POSITIVE_SEMIDEFINITE_AND_ORTHOGONAL = `!A:real^N^N.
        positive_semidefinite A /\ orthogonal_matrix A
        ==> A = mat 1`;;

let POSITIVE_SEMIDEFINITE_INV = `!A:real^N^N.
     positive_semidefinite(matrix_inv A) <=> positive_semidefinite A`;;

let POSITIVE_DEFINITE_INV = `!A:real^N^N.
     positive_definite(matrix_inv A) <=> positive_definite A`;;

let POSITIVE_DEFINITE_COFACTOR = `!A:real^N^N. positive_definite A ==> positive_definite(cofactor A)`;;

let POSITIVE_SEMIDEFINITE_COFACTOR = `!A:real^N^N. positive_semidefinite A ==> positive_semidefinite(cofactor A)`;;

let POSITIVE_DEFINITE_COFACTOR_EQ = `!A:real^N^N.
        positive_definite A <=>
        positive_definite(cofactor A) /\ &0 < det A`;;

let POSITIVE_SEMIDEFINITE_COVARIANCE_UNIQUE = `!A:real^N^N. positive_semidefinite A <=>
                ?!S. positive_semidefinite S /\ A = transp S ** S`;;

let POSITIVE_SEMIDEFINITE_SQRT_UNIQUE = `!A:real^N^N. positive_semidefinite A <=>
                ?!S. positive_semidefinite S /\ A = S ** S`;;

let POSITIVE_SEMIDEFINITE_MUL_EQ = `!A:real^N^N B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> (positive_semidefinite(A ** B) <=> A ** B = B ** A)`;;

let POSITIVE_SEMIDEFINITE_MUL = `!A:real^N^N B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B /\ A ** B = B ** A
        ==> positive_semidefinite(A ** B)`;;

let POSITIVE_DEFINITE_MUL_EQ = `!A:real^N^N B:real^N^N.
        positive_definite A /\ positive_definite B
        ==> (positive_definite(A ** B) <=> A ** B = B ** A)`;;

let POSITIVE_DEFINITE_MUL = `!A:real^N^N B:real^N^N.
        positive_definite A /\ positive_definite B /\ A ** B = B ** A
        ==> positive_definite(A ** B)`;;

let COMMUTING_WITH_SQUARE_ROOT_MATRIX = `!A S B:real^N^N.
        positive_semidefinite S /\ S ** S = A /\ A ** B = B ** A
        ==> S ** B = B ** S`;;

let POSITIVE_SEMIDEFINITE_MUL_EIGENVALUES = `!A B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> !c v. (A ** B) ** v = c % v /\ ~(v = vec 0) ==> &0 <= c`;;

let POSITIVE_SEMIDEFINITE_2_DET = `!A:real^2^2. positive_semidefinite A <=>
                symmetric_matrix A /\
                &0 <= A$1$1 /\ &0 <= A$2$2 /\ &0 <= det A`;;

let POSITIVE_SEMIDEFINITE_2 = `!A:real^2^2. positive_semidefinite A <=>
                A$2$1 = A$1$2 /\
                &0 <= A$1$1 /\ &0 <= A$2$2 /\ A$1$2 pow 2 <= A$1$1 * A$2$2`;;

let POSITIVE_DEFINITE_2_DET = `!A:real^2^2. positive_definite A <=>
                symmetric_matrix A /\ &0 < A$1$1 /\ &0 < A$2$2 /\ &0 < det A`;;

let POSITIVE_DEFINITE_2 = `!A:real^2^2. positive_definite A <=>
                A$2$1 = A$1$2 /\
                &0 < A$1$1 /\ &0 < A$2$2 /\ A$1$2 pow 2 < A$1$1 * A$2$2`;;

let REAL_LE_NORM_MATRIX_MUL_DET = `!A B:real^N^N.
        (!x. norm(A ** x) <= norm(B ** x)) ==> abs(det A) <= abs(det B)`;;

let DET_LE_ONORM_POW = `!A:real^N^N. abs(det A) <= onorm(\x. A ** x) pow (dimindex(:N))`;;

let ONORM_INVERSE_DET_LE_ONORM_POW = `!A:real^N^N.
        invertible A
        ==> onorm(\x. matrix_inv A ** x) * det A
            <= onorm(\x. A ** x) pow (dimindex(:N) - 1)`;;

let ONORM_INVERSE_DET_LE_ONORM_POW_ALT = `!f g:real^N->real^N.
        linear f /\ linear g /\ f o g = I
        ==> onorm f * det(matrix g) <= onorm g pow (dimindex(:N) - 1)`;;

let HADAMARD_INEQUALITY_PSD = `!A:real^N^N.
    positive_semidefinite A ==> det A <= product(1..dimindex(:N)) (\i. A$i$i)`;;

let POSITIVE_DEFINITE_NEARBY = `!A:real^N^N.
        positive_definite A
        ==> ?e. &0 < e /\
                !B. symmetric_matrix B /\ onorm(\x. (B - A) ** x) < e
                    ==> positive_definite B`;;

let POSITIVE_DEFINITE_EQ_CONGRUENT_IDENTITY = `(!A:real^N^N.
        positive_definite A <=> ?B:real^N^N. transp B ** A ** B = mat 1)`
and POSITIVE_DEFINITE_EQ_CONGRUENT_IDENTITY_ALT = `(!A:real^N^N.
        positive_definite A <=>
        ?B:real^N^N. invertible B /\ transp B ** A ** B = mat 1)`;;

let POSITIVE_DEFINITE_EVENTUALLY = `!A:real^N^N.
        symmetric_matrix A
        ==> ?a. !x. a <= x ==> positive_definite(A + x %% mat 1)`;;

let POSITIVE_SEMIDEFINITE_HADAMARD_PRODUCT = `(!A:real^N^N B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> positive_semidefinite((lambda i j. A$i$j * B$i$j):real^N^N))`
and POSITIVE_DEFINITE_HADAMARD_PRODUCT = `(!A:real^N^N B:real^N^N.
        positive_definite A /\ positive_definite B
        ==> positive_definite((lambda i j. A$i$j * B$i$j):real^N^N))`;;

(* ------------------------------------------------------------------------- *)
(* Polar decomposition.                                                      *)
(* ------------------------------------------------------------------------- *)

let RIGHT_POLAR_DECOMPOSITION = `!A:real^N^N.
        ?U:real^N^N P:real^N^N.
                orthogonal_matrix U /\ positive_semidefinite P /\ U ** P = A`;;

let LEFT_POLAR_DECOMPOSITION = `!A:real^N^N.
        ?U:real^N^N P:real^N^N.
                orthogonal_matrix U /\ positive_semidefinite P /\ P ** U = A`;;

let RIGHT_POLAR_DECOMPOSITION_INVERTIBLE = `!A:real^N^N.
        invertible A <=>
        ?U:real^N^N P:real^N^N.
                orthogonal_matrix U /\ positive_definite P /\ U ** P = A`;;

let LEFT_POLAR_DECOMPOSITION_INVERTIBLE = `!A:real^N^N.
        invertible A <=>
        ?U:real^N^N P:real^N^N.
                orthogonal_matrix U /\ positive_definite P /\ P ** U = A`;;

let NORMAL_RIGHT_POLAR_DECOMPOSITION = `!A U P:real^N^N.
        orthogonal_matrix U /\ positive_semidefinite P /\ U ** P = A
        ==> (normal_matrix A <=> P ** U = U ** P)`;;

let NORMAL_LEFT_POLAR_DECOMPOSITION = `!A U P:real^N^N.
        orthogonal_matrix U /\ positive_semidefinite P /\ P ** U = A
        ==> (normal_matrix A <=> P ** U = U ** P)`;;

let NORMAL_BIPOLAR_DECOMPOSITION = `!A:real^N^N.
        normal_matrix A <=>
        ?U P. orthogonal_matrix U /\ positive_semidefinite P /\
              U ** P = A /\ P ** U = A`;;

let LEFT_POLAR_DECOMPOSITION_UNIQUE = `!A:real^N^N.
        ?!P. ?U. orthogonal_matrix U /\ positive_semidefinite P /\ P ** U = A`;;

let RIGHT_POLAR_DECOMPOSITION_UNIQUE = `!A:real^N^N.
        ?!P. ?U. orthogonal_matrix U /\ positive_semidefinite P /\ U ** P = A`;;

let LEFT_POLAR_DECOMPOSITION_INVERTIBLE_UNIQUE = `!A:real^N^N U V P S.
        invertible A /\
        orthogonal_matrix U /\ positive_semidefinite P /\
        orthogonal_matrix V /\ positive_semidefinite S /\
        P ** U = A /\ S ** V = A
        ==> P = S /\ U = V`;;

let RIGHT_POLAR_DECOMPOSITION_INVERTIBLE_UNIQUE = `!A:real^N^N U V P S.
        invertible A /\
        orthogonal_matrix U /\ positive_semidefinite P /\
        orthogonal_matrix V /\ positive_semidefinite S /\
        U ** P = A /\ V ** S = A
        ==> P = S /\ U = V`;;

let COVARIANCE_UNIQUE_UP_TO_ORTHOGONAL = `!A B:real^N^N.
        transp A ** A = transp B ** B <=>
        ?U. orthogonal_matrix U /\ U ** A = B`;;

let COVARIANCE_UNIQUE_UP_TO_ORTHOGONAL_ALT = `!A B:real^N^N.
        A ** transp A = B ** transp B <=>
        ?U. orthogonal_matrix U /\ A ** U = B`;;

let NORMAL_MATRIX_SIMILAR_TRANSP = `!A:real^N^N.
        normal_matrix A <=>
        ?U. orthogonal_matrix U /\ U ** transp A = A`;;

let NORMAL_MATRIX_SIMILAR_TRANSP_ALT = `!A:real^N^N.
        normal_matrix A <=>
        ?U. orthogonal_matrix U /\ transp A ** U = A`;;

let MATRIX_DIAGONALIZABLE = `!A:real^N^N.
        ?P D Q. orthogonal_matrix P /\
                diagonal_matrix D /\
                orthogonal_matrix Q /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= D$i$i) /\
                A = P ** D ** Q`;;

(* ------------------------------------------------------------------------- *)
(* Infinite sums of vectors. Allow general starting point (and more).        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("sums",(12,"right"));;

let sums = new_definition
  `(f sums l) s = ((\n. vsum(s INTER (0..n)) f) --> l) sequentially`;;

let infsum = new_definition
 `infsum s f = @l. (f sums l) s`;;

let summable = new_definition
 `summable s f = ?l. (f sums l) s`;;

let SUMS_SUMMABLE = `!f l s. (f sums l) s ==> summable s f`;;

let SUMS_INFSUM = `!f s. (f sums (infsum s f)) s <=> summable s f`;;

let SUMS_LIM = `!f:num->real^N s.
      (f sums lim sequentially (\n. vsum (s INTER (0..n)) f)) s
      <=> summable s f`;;

let SERIES_FROM = `!f l k. (f sums l) (from k) = ((\n. vsum(k..n) f) --> l) sequentially`;;

let SERIES_UNIQUE = `!f:num->real^N l l' s. (f sums l) s /\ (f sums l') s ==> (l = l')`;;

let INFSUM_UNIQUE = `!f:num->real^N l s. (f sums l) s ==> infsum s f = l`;;

let SERIES_TERMS_TOZERO = `!f l n. (f sums l) (from n) ==> (f --> vec 0) sequentially`;;

let SERIES_FINITE = `!f s. FINITE s ==> (f sums (vsum s f)) s`;;

let SERIES_FINITE_EQ = `!f:num->real^N s y.
        FINITE s ==> ((f sums y) s <=> vsum s f = y)`;;

let SERIES_LINEAR = `!f h l s. (f sums l) s /\ linear h ==> ((\n. h(f n)) sums h l) s`;;

let SERIES_0 = `!s. ((\n. vec 0) sums (vec 0)) s`;;

let SERIES_ADD = `!x x0 y y0 s.
     (x sums x0) s /\ (y sums y0) s ==> ((\n. x n + y n) sums (x0 + y0)) s`;;

let SERIES_SUB = `!x x0 y y0 s.
     (x sums x0) s /\ (y sums y0) s ==> ((\n. x n - y n) sums (x0 - y0)) s`;;

let SERIES_CMUL = `!x x0 c s. (x sums x0) s ==> ((\n. c % x n) sums (c % x0)) s`;;

let SERIES_NEG = `!x x0 s. (x sums x0) s ==> ((\n. --(x n)) sums (--x0)) s`;;

let SUMS_IFF = `!f g k. (!x. x IN k ==> f x = g x) ==> ((f sums l) k <=> (g sums l) k)`;;

let SUMS_EQ = `!f g k. (!x. x IN k ==> f x = g x) /\ (f sums l) k ==> (g sums l) k`;;

let SUMS_0 = `!f:num->real^N s. (!n. n IN s ==> f n = vec 0) ==> (f sums vec 0) s`;;

let SERIES_FINITE_SUPPORT = `!f:num->real^N s k.
     FINITE (s INTER k) /\ (!x. x IN k /\ ~(x IN s) ==> f x = vec 0)
     ==> (f sums vsum (s INTER k) f) k`;;

let SERIES_COMPONENT = `!f s l:real^N k. (f sums l) s /\ 1 <= k /\ k <= dimindex(:N)
                    ==> ((\i. lift(f(i)$k)) sums lift(l$k)) s`;;

let SERIES_DIFFS = `!f:num->real^N k.
        (f --> vec 0) sequentially
        ==> ((\n. f(n) - f(n + 1)) sums f(k)) (from k)`;;

let SERIES_TRIVIAL = `!f. (f sums vec 0) {}`;;

let SERIES_RESTRICT = `!f k l:real^N.
        ((\n. if n IN k then f(n) else vec 0) sums l) (:num) <=>
        (f sums l) k`;;

let SERIES_VSUM = `!f l k s. FINITE s /\ s SUBSET k /\ (!x. ~(x IN s) ==> f x = vec 0) /\
             vsum s f = l ==> (f sums l) k`;;

let SUMS_REINDEX = `!k a l:real^N n.
   ((\x. a(x + k)) sums l) (from n) <=> (a sums l) (from(n + k))`;;

let SUMS_REINDEX_GEN = `!k a l:real^N s.
     ((\x. a(x + k)) sums l) s <=> (a sums l) (IMAGE (\i. i + k) s)`;;

let SERIES_EVEN = `!f l:real^N n.
    (f sums l) (from n) <=>
    ((\i. if EVEN i then f(i DIV 2) else vec 0) sums l) (from (2 * n))`;;

let SERIES_ODD = `!f l:real^N n.
    (f sums l) (from n) <=>
    ((\i. if ODD i then f(i DIV 2) else vec 0) sums l) (from (2 * n + 1))`;;

let SERIES_PASTECART = `!f1:num->real^N f2:num->real^M l1 l2 s.
        ((\x. pastecart (f1 x) (f2 x)) sums (pastecart l1 l2)) s <=>
        (f1 sums l1) s /\ (f2 sums l2) s`;;

(* ------------------------------------------------------------------------- *)
(* Similar combining theorems just for summability.                          *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_LINEAR = `!f h s. summable s f /\ linear h ==> summable s (\n. h(f n))`;;

let SUMMABLE_0 = `!s. summable s (\n. vec 0)`;;

let SUMMABLE_ADD = `!x y s. summable s x /\ summable s y ==> summable s (\n. x n + y n)`;;

let SUMMABLE_SUB = `!x y s. summable s x /\ summable s y ==> summable s (\n. x n - y n)`;;

let SUMMABLE_CMUL = `!s x c. summable s x ==> summable s (\n. c % x n)`;;

let SUMMABLE_NEG = `!x s. summable s x ==> summable s (\n. --(x n))`;;

let SUMMABLE_IFF = `!f g k. (!x. x IN k ==> f x = g x) ==> (summable k f <=> summable k g)`;;

let SUMMABLE_EQ = `!f g k. (!x. x IN k ==> f x = g x) /\ summable k f ==> summable k g`;;

let SUMMABLE_FINITE = `!k f:num->real^N. FINITE k ==> summable k f`;;

let SUMMABLE_COMPONENT = `!f:num->real^N s k.
        summable s f /\ 1 <= k /\ k <= dimindex(:N)
        ==> summable s (\i. lift(f(i)$k))`;;

let SERIES_SUBSET = `!x s t l.
        s SUBSET t /\
        ((\i. if i IN s then x i else vec 0) sums l) t
        ==> (x sums l) s`;;

let SUMMABLE_SUBSET = `!x s t.
        s SUBSET t /\
        summable t (\i. if i IN s then x i else vec 0)
        ==> summable s x`;;

let SUMMABLE_TRIVIAL = `!f:num->real^N. summable {} f`;;

let SUMMABLE_RESTRICT = `!f:num->real^N k.
        summable (:num) (\n. if n IN k then f(n) else vec 0) <=>
        summable k f`;;

let SUMS_FINITE_DIFF = `!f:num->real^N t s l.
        t SUBSET s /\ FINITE t /\ (f sums l) s
        ==> (f sums (l - vsum t f)) (s DIFF t)`;;

let SUMS_FINITE_UNION = `!f:num->real^N s t l.
        FINITE t /\ (f sums l) s
        ==> (f sums (l + vsum (t DIFF s) f)) (s UNION t)`;;

let SUMS_OFFSET = `!f l:real^N m n.
           (f sums l) (from m) /\ 0 < n /\ m <= n
           ==> (f sums l - vsum (m..n - 1) f) (from n)`;;

let SUMS_OFFSET_REV = `!f:num->real^N l m n.
        (f sums l) (from m) /\ 0 < m /\ n <= m

        ==> (f sums (l + vsum(n..m-1) f)) (from n)`;;

let SUMMABLE_REINDEX = `!k a n. summable (from n) (\x. a (x + k)) <=> summable (from(n + k)) a`;;

let SUMMABLE_EVEN = `!f:num->real^N n.
        summable (from n) f <=>
        summable (from (2 * n)) (\i. if EVEN i then f(i DIV 2) else vec 0)`;;

let SUMMABLE_ODD = `!f:num->real^N n.
        summable (from n) f <=>
        summable (from (2 * n + 1)) (\i. if ODD i then f(i DIV 2) else vec 0)`;;

let SERIES_DROP_LE = `!f g s a b.
        (f sums a) s /\ (g sums b) s /\
        (!x. x IN s ==> drop(f x) <= drop(g x))
        ==> drop a <= drop b`;;

let SERIES_DROP_POS = `!f s a.
        (f sums a) s /\ (!x. x IN s ==> &0 <= drop(f x))
        ==> &0 <= drop a`;;

let SERIES_BOUND = `!f:num->real^N g s a b.
        (f sums a) s /\ ((lift o g) sums (lift b)) s /\
        (!i. i IN s ==> norm(f i) <= g i)
        ==> norm(a) <= b`;;

(* ------------------------------------------------------------------------- *)
(* Similar combining theorems for infsum.                                    *)
(* ------------------------------------------------------------------------- *)

let INFSUM_LINEAR = `!f h s. summable s f /\ linear h
           ==> infsum s (\n. h(f n)) = h(infsum s f)`;;

let INFSUM_0 = `infsum s (\i. vec 0) = vec 0`;;

let INFSUM_ADD = `!x y s. summable s x /\ summable s y
           ==> infsum s (\i. x i + y i) = infsum s x + infsum s y`;;

let INFSUM_SUB = `!x y s. summable s x /\ summable s y
           ==> infsum s (\i. x i - y i) = infsum s x - infsum s y`;;

let INFSUM_CMUL = `!s x c. summable s x ==> infsum s (\n. c % x n) = c % infsum s x`;;

let INFSUM_NEG = `!s x. summable s x ==> infsum s (\n. --(x n)) = --(infsum s x)`;;

let INFSUM_EQ = `!f g k. summable k f /\ summable k g /\ (!x. x IN k ==> f x = g x)
           ==> infsum k f = infsum k g`;;

let INFSUM_RESTRICT = `!k a:num->real^N.
        infsum (:num) (\n. if n IN k then a n else vec 0) = infsum k a`;;

let PARTIAL_SUMS_COMPONENT_LE_INFSUM = `!f:num->real^N s k n.
        1 <= k /\ k <= dimindex(:N) /\
        (!i. i IN s ==> &0 <= (f i)$k) /\
        summable s f
        ==> (vsum (s INTER (0..n)) f)$k <= (infsum s f)$k`;;

let PARTIAL_SUMS_DROP_LE_INFSUM = `!f s n.
        (!i. i IN s ==> &0 <= drop(f i)) /\
        summable s f
        ==> drop(vsum (s INTER (0..n)) f) <= drop(infsum s f)`;;

let INFSUM_EVEN = `!f:num->real^N n.
        infsum (from n) f =
        infsum (from (2 * n)) (\i. if EVEN i then f(i DIV 2) else vec 0)`;;

let INFSUM_ODD = `!f:num->real^N n.
        infsum (from n) f =
        infsum (from (2 * n + 1)) (\i. if ODD i then f(i DIV 2) else vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy criterion for series.                                              *)
(* ------------------------------------------------------------------------- *)

let SEQUENCE_CAUCHY_WLOG = `!P s. (!m n:num. P m /\ P n ==> dist(s m,s n) < e) <=>
         (!m n. P m /\ P n /\ m <= n ==> dist(s m,s n) < e)`;;

let VSUM_DIFF_LEMMA = `!f:num->real^N k m n.
        m <= n
        ==> vsum(k INTER (0..n)) f - vsum(k INTER (0..m)) f =
            vsum(k INTER (m+1..n)) f`;;

let NORM_VSUM_TRIVIAL_LEMMA = `!e. &0 < e ==> (P ==> norm(vsum(s INTER (m..n)) f) < e <=>
                   P ==> n < m \/ norm(vsum(s INTER (m..n)) f) < e)`;;

let SERIES_CAUCHY = `!f s. (?l. (f sums l) s) =
         !e. &0 < e
             ==> ?N. !m n. m >= N
                           ==> norm(vsum(s INTER (m..n)) f) < e`;;

let SUMMABLE_CAUCHY = `!f s. summable s f <=>
         !e. &0 < e
             ==> ?N. !m n. m >= N ==> norm(vsum(s INTER (m..n)) f) < e`;;

let SUMMABLE_IFF_EVENTUALLY = `!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n)
           ==> (summable k f <=> summable k g)`;;

let SUMMABLE_EQ_EVENTUALLY = `!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n) /\ summable k f
           ==> summable k g`;;

let SUMMABLE_IFF_COFINITE = `!f s t. FINITE((s DIFF t) UNION (t DIFF s))
           ==> (summable s f <=> summable t f)`;;

let SUMMABLE_EQ_COFINITE = `!f s t. FINITE((s DIFF t) UNION (t DIFF s)) /\ summable s f
           ==> summable t f`;;

let SUMMABLE_FROM_ELSEWHERE = `!f m n. summable (from m) f ==> summable (from n) f`;;

let SUMMABLE_FROM_ELSEWHERE_EQ = `!n m f:num->real^N. summable (from m) f <=> summable (from n) f`;;

(* ------------------------------------------------------------------------- *)
(* Uniform vesion of Cauchy criterion.                                       *)
(* ------------------------------------------------------------------------- *)

let SERIES_CAUCHY_UNIFORM = `!P f:A->num->real^N k.
        (?l. !e. &0 < e
                 ==> ?N. !n x. N <= n /\ P x
                               ==> dist(vsum(k INTER (0..n)) (f x),
                                        l x) < e) <=>
        (!e. &0 < e ==> ?N. !m n x. N <= m /\ P x
                                    ==> norm(vsum(k INTER (m..n)) (f x)) < e)`;;

(* ------------------------------------------------------------------------- *)
(* So trivially, terms of a convergent series go to zero.                    *)
(* ------------------------------------------------------------------------- *)

let SERIES_GOESTOZERO = `!s x. summable s x
         ==> !e. &0 < e
                 ==> eventually (\n. n IN s ==> norm(x n) < e) sequentially`;;

let SUMMABLE_IMP_TOZERO = `!f:num->real^N k.
       summable k f
       ==> ((\n. if n IN k then f(n) else vec 0) --> vec 0) sequentially`;;

let SUMMABLE_IMP_BOUNDED = `!f:num->real^N k. summable k f ==> bounded (IMAGE f k)`;;

let SUMMABLE_IMP_SUMS_BOUNDED = `!f:num->real^N k.
       summable (from k) f ==> bounded { vsum(k..n) f | n IN (:num) }`;;

(* ------------------------------------------------------------------------- *)
(* Comparison test.                                                          *)
(* ------------------------------------------------------------------------- *)

let SERIES_COMPARISON = `!f g s. (?l. ((lift o g) sums l) s) /\
           (?N. !n. n >= N /\ n IN s ==> norm(f n) <= g n)
           ==> ?l:real^N. (f sums l) s`;;

let SUMMABLE_COMPARISON = `!f g s. summable s (lift o g) /\
           (?N. !n. n >= N /\ n IN s ==> norm(f n) <= g n)
           ==> summable s f`;;

let SERIES_LIFT_ABSCONV_IMP_CONV = `!x:num->real^N k. summable k (\n. lift(norm(x n))) ==> summable k x`;;

let SUMMABLE_SUBSET_ABSCONV = `!x:num->real^N s t.
        summable s (\n. lift(norm(x n))) /\ t SUBSET s
        ==> summable t (\n. lift(norm(x n)))`;;

let SERIES_COMPARISON_BOUND = `!f:num->real^N g s a.
        (g sums a) s /\ (!i. i IN s ==> norm(f i) <= drop(g i))
        ==> ?l. (f sums l) s /\ norm(l) <= drop a`;;

(* ------------------------------------------------------------------------- *)
(* Uniform version of comparison test.                                       *)
(* ------------------------------------------------------------------------- *)

let SERIES_COMPARISON_UNIFORM = `!f g P s. (?l. ((lift o g) sums l) s) /\
             (?N. !n x. N <= n /\ n IN s /\ P x ==> norm(f x n) <= g n)
             ==> ?l:A->real^N.
                    !e. &0 < e
                        ==> ?N. !n x. N <= n /\ P x
                                      ==> dist(vsum(s INTER (0..n)) (f x),
                                               l x) < e`;;

(* ------------------------------------------------------------------------- *)
(* Ratio test.                                                               *)
(* ------------------------------------------------------------------------- *)

let SERIES_RATIO = `!c a s N.
      c < &1 /\
      (!n. n >= N ==> norm(a(SUC n)) <= c * norm(a(n)))
      ==> ?l:real^N. (a sums l) s`;;

let SUMMABLE_RATIO = `!c a:num->real^N s N.
      c < &1 /\
      (!n. n >= N ==> norm(a(SUC n)) <= c * norm(a(n)))
      ==> summable s a`;;

let SUMMABLE_REAL_GP = `!x k. abs x < &1 ==> summable k (\n. lift(x pow n))`;;

(* ------------------------------------------------------------------------- *)
(* Ostensibly weaker versions of the boundedness of partial sums.            *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_PARTIAL_SUMS = `!f:num->real^N k.
        bounded { vsum(k..n) f | n IN (:num) }
        ==> bounded { vsum(m..n) f | m IN (:num) /\ n IN (:num) }`;;

(* ------------------------------------------------------------------------- *)
(* General Dirichlet convergence test (could make this uniform on a set).    *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_BILINEAR_PARTIAL_PRE = `!f g h:real^M->real^N->real^P l k.
        bilinear h /\
        ((\n. h (f(n + 1)) (g(n))) --> l) sequentially /\
        summable (from k) (\n. h (f(n + 1) - f(n)) (g(n)))
        ==> summable (from k) (\n. h (f n) (g(n) - g(n - 1)))`;;

let SERIES_DIRICHLET_BILINEAR = `!f g h:real^M->real^N->real^P k m p l.
        bilinear h /\
        bounded { vsum (m..n) f | n IN (:num)} /\
        summable (from p) (\n. lift(norm(g(n + 1) - g(n)))) /\
        ((\n. h (g(n + 1)) (vsum(1..n) f)) --> l) sequentially
        ==> summable (from k) (\n. h (g n) (f n))`;;

let SERIES_DIRICHLET = `!f:num->real^N g N k m.
        bounded { vsum (m..n) f | n IN (:num)} /\
        (!n. N <= n ==> g(n + 1) <= g(n)) /\
        ((lift o g) --> vec 0) sequentially
        ==> summable (from k) (\n. g(n) % f(n))`;;

(* ------------------------------------------------------------------------- *)
(* Rearranging absolutely convergent series.                                 *)
(* ------------------------------------------------------------------------- *)

let SERIES_INJECTIVE_IMAGE_STRONG = `!x:num->real^N s f.
        summable (IMAGE f s) (\n. lift(norm(x n))) /\
        (!m n. m IN s /\ n IN s /\ f m = f n ==> m = n)
        ==> ((\n. vsum (IMAGE f s INTER (0..n)) x -
                  vsum (s INTER (0..n)) (x o f)) --> vec 0)
            sequentially`;;

let SERIES_INJECTIVE_IMAGE = `!x:num->real^N s f l.
        summable (IMAGE f s) (\n. lift(norm(x n))) /\
        (!m n. m IN s /\ n IN s /\ f m = f n ==> m = n)
        ==> (((x o f) sums l) s <=> (x sums l) (IMAGE f s))`;;

let SERIES_REARRANGE_EQ = `!x:num->real^N s p l.
        summable s (\n. lift(norm(x n))) /\ p permutes s
        ==> (((x o p) sums l) s <=> (x sums l) s)`;;

let SERIES_REARRANGE = `!x:num->real^N s p l.
        summable s (\n. lift(norm(x n))) /\ p permutes s /\ (x sums l) s
        ==> ((x o p) sums l) s`;;

let SUMMABLE_REARRANGE = `!x s p.
        summable s (\n. lift(norm(x n))) /\ p permutes s
        ==> summable s (x o p)`;;

(* ------------------------------------------------------------------------- *)
(* Some general theorems about series averages, convolutions etc.            *)
(* ------------------------------------------------------------------------- *)

let TOEPLITZ_BILINEAR_SERIES_NULL = `!(bop:real^M->real^N->real^P) a x m b.
        bilinear bop /\
        (x --> vec 0) sequentially /\
        (!p. ((\n. a n p) --> vec 0) sequentially) /\
        (!n. sum (0..n) (\i. norm(a n i)) <= b)
        ==> ((\n. vsum(m..n) (\i. bop (a n i) (x i))) --> vec 0) sequentially`;;

let TOEPLITZ_BILINEAR_SERIES = `!(bop:real^M->real^N->real^P) a x m r l i b.
        bilinear bop /\
        (x --> l) sequentially /\
        (!p. ((\n. a n p) --> vec 0) sequentially) /\
        (((\n. vsum(r..n) (\i. a n i))) --> i) sequentially /\
        (!n. sum (0..n) (\i. norm(a n i)) <= b)
        ==> ((\n. vsum(m..n) (\i. bop (a n i) (x i))) --> bop i l)
             sequentially`;;

let LIM_BILINEAR_CONVOLUTION = `!(bop:real^M->real^N->real^P) x y m k a b.
     bilinear bop /\ (x --> a) sequentially /\ (y --> b) sequentially
     ==> ((\n. inv(&n + k) % vsum(m..n) (\i. bop (x i) (y(n - i))))
          --> bop a b) sequentially`;;

let LIM_CESARO = `!a l:real^N m k.
        (a --> l) sequentially
        ==> ((\n. inv(&n + k) % vsum(m..n) a) --> l) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Multiplication (in a general bilinear sense) of series.                   *)
(* ------------------------------------------------------------------------- *)

let SERIES_BILINEAR = `!bop:real^M->real^N->real^P x y a b.
        bilinear bop /\ (x sums a) (from 0) /\ (y sums b) (from 0) /\
        (summable (from 0) (\n. lift(norm(x n))) \/
         summable (from 0) (\n. lift(norm(y n))))
        ==> ((\n. vsum(0..n) (\i. bop (x i) (y(n - i)))) sums bop a b)
            (from 0)`;;

let SERIES_BILINEAR_UNIQUE = `!bop:real^M->real^N->real^P x y a b c.
        bilinear bop /\
        (x sums a) (from 0) /\ (y sums b) (from 0) /\
        ((\n. vsum (0..n) (\i. bop (x i) (y(n - i)))) sums c) (from 0)
        ==> bop a b = c`;;

let SUMMABLE_BILINEAR_LEFT = `!bop:real^M->real^N->real^P x y m n p.
        bilinear bop /\
        summable (from m) (\n. lift(norm(x n))) /\ summable (from n) y
        ==> summable (from p) (\n. vsum(0..n) (\i. bop (x i) (y(n - i))))`;;

let SUMMABLE_BILINEAR_RIGHT = `!bop:real^M->real^N->real^P x y m n p.
        bilinear bop /\
        summable (from m) x /\ summable (from n) (\n. lift(norm(y n)))
        ==> summable (from p) (\n. vsum(0..n) (\i. bop (x i) (y(n - i))))`;;

(* ------------------------------------------------------------------------- *)
(* Relate Cauchy sequences to summability or absolute convergence.           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_EQ_SUMMABLE = `!x:num->real^N. cauchy x <=> summable (from 0) (\n. x(n + 1) - x n)`;;

let CAUCHY_ABSOLUTELY_SUMMABLE_SUBSEQUENCE = `!x:num->real^N.
        cauchy x
        ==> ?r. (!m n. m < n ==> r m < r n) /\
                summable (from 0) (\n. lift(dist(x(r(n + 1)),x(r n))))`;;

let ABSOLUTELY_SUMMABLE_IMP_CAUCHY = `!x:num->real^N.
        summable (from 0) (\n. lift(dist(x(n + 1),x n))) ==> cauchy x`;;

let COMPLETE_ABSOLUTELY_SUMMABLE = `!s:real^N->bool.
        complete s <=>
        !f. (!n. f n IN s) /\ summable (from 0) (\n. lift(dist(f(n + 1),f n)))
            ==> ?l. l IN s /\ (f --> l) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Banach fixed point theorem (not really topological...)                    *)
(* ------------------------------------------------------------------------- *)

let BANACH_FIX = `!f s c. complete s /\ ~(s = {}) /\
           &0 <= c /\ c < &1 /\
           (IMAGE f s) SUBSET s /\
           (!x y. x IN s /\ y IN s ==> dist(f(x),f(y)) <= c * dist(x,y))
           ==> ?!x:real^N. x IN s /\ (f x = x)`;;

(* ------------------------------------------------------------------------- *)
(* Edelstein fixed point theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let EDELSTEIN_FIX = `!f s. compact s /\ ~(s = {}) /\ (IMAGE f s) SUBSET s /\
         (!x y. x IN s /\ y IN s /\ ~(x = y) ==> dist(f(x),f(y)) < dist(x,y))
         ==> ?!x:real^N. x IN s /\ f x = x`;;

(* ------------------------------------------------------------------------- *)
(* Simple n-ary generalizations of Banach and Edelstein theorems.            *)
(* ------------------------------------------------------------------------- *)

let BANACH_FIX_ITER = `!f s:real^N->bool c n.
           complete s /\
           ~(s = {}) /\
           &0 <= c /\
           c < &1 /\
           IMAGE f s SUBSET s /\
           (!x y. x IN s /\ y IN s
                  ==> dist (ITER n f x,ITER n f y) <= c * dist (x,y))
           ==> ?!x. x IN s /\ f x = x`;;

let EDELSTEIN_FIX_ITER = `!f s n.
        compact s /\ ~(s = {}) /\ (IMAGE f s) SUBSET s /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> dist(ITER n f x,ITER n f y) < dist(x,y))
        ==> ?!x:real^N. x IN s /\ f x = x`;;

(* ------------------------------------------------------------------------- *)
(* Dini's theorem.                                                           *)
(* ------------------------------------------------------------------------- *)

let DINI = `!f:num->real^N->real^1 g s.
        compact s /\ (!n. (f n) continuous_on s) /\ g continuous_on s /\
        (!x. x IN s ==> ((\n. (f n x)) --> g x) sequentially) /\
        (!n x. x IN s ==> drop(f n x) <= drop(f (n + 1) x))
        ==> !e. &0 < e
                ==> eventually (\n. !x. x IN s ==> norm(f n x - g x) < e)
                               sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Closest point of a (closed) set to a point.                               *)
(* ------------------------------------------------------------------------- *)

let closest_point = new_definition
 `closest_point s a = @x. x IN s /\ !y. y IN s ==> dist(a,x) <= dist(a,y)`;;

let CLOSEST_POINT_EXISTS = `!s a. closed s /\ ~(s = {})
         ==> (closest_point s a) IN s /\
             !y. y IN s ==> dist(a,closest_point s a) <= dist(a,y)`;;

let CLOSEST_POINT_IN_SET = `!s a. closed s /\ ~(s = {}) ==> (closest_point s a) IN s`;;

let CLOSEST_POINT_LE = `!s a x. closed s /\ x IN s ==> dist(a,closest_point s a) <= dist(a,x)`;;

let CLOSEST_POINT_SELF = `!s x:real^N. x IN s ==> closest_point s x = x`;;

let CLOSEST_POINT_REFL = `!s x:real^N. closed s /\ ~(s = {}) ==> (closest_point s x = x <=> x IN s)`;;

let DIST_CLOSEST_POINT_LIPSCHITZ = `!s x y:real^N.
        closed s /\ ~(s = {})
        ==> abs(dist(x,closest_point s x) - dist(y,closest_point s y))
            <= dist(x,y)`;;

let CONTINUOUS_AT_DIST_CLOSEST_POINT = `!s x:real^N.
        closed s /\ ~(s = {})
        ==> (\x. lift(dist(x,closest_point s x))) continuous (at x)`;;

let CONTINUOUS_ON_DIST_CLOSEST_POINT = `!s t. closed s /\ ~(s = {})
         ==> (\x. lift(dist(x,closest_point s x))) continuous_on t`;;

let UNIFORMLY_CONTINUOUS_ON_DIST_CLOSEST_POINT = `!s t:real^N->bool.
        closed s /\ ~(s = {})
        ==> (\x. lift(dist(x,closest_point s x))) uniformly_continuous_on t`;;

let SEGMENT_TO_CLOSEST_POINT = `!s a:real^N.
        closed s /\ ~(s = {})
        ==> segment(a,closest_point s a) INTER s = {}`;;

let SEGMENT_TO_POINT_EXISTS = `!s a:real^N.
        closed s /\ ~(s = {}) ==> ?b. b IN s /\ segment(a,b) INTER s = {}`;;

let CLOSEST_POINT_IN_INTERIOR = `!s x:real^N.
        closed s /\ ~(s = {})
        ==> ((closest_point s x) IN interior s <=> x IN interior s)`;;

let CLOSEST_POINT_IN_FRONTIER = `!s x:real^N.
        closed s /\ ~(s = {}) /\ ~(x IN interior s)
        ==> (closest_point s x) IN frontier s`;;

let CLOSEST_POINT_FRONTIER = `!s x:real^N.
        ~(x IN interior s)
        ==> closest_point (frontier s) x = closest_point (closure s) x`;;

(* ------------------------------------------------------------------------- *)
(* More general infimum of distance between two sets.                        *)
(* ------------------------------------------------------------------------- *)

let setdist = new_definition
 `setdist(s,t) =
        if s = {} \/ t = {} then &0
        else inf {dist(x,y) | x IN s /\ y IN t}`;;

let SETDIST_EMPTY = `(!t. setdist({},t) = &0) /\ (!s. setdist(s,{}) = &0)`;;

let SETDIST_POS_LE = `!s t. &0 <= setdist(s,t)`;;

let SETDIST_POS_LT = `!s t:real^N->bool. &0 < setdist(s,t) <=> ~(setdist(s,t) = &0)`;;

let SETDIST_SUBSETS_EQ = `!s t s' t':real^N->bool.
     s' SUBSET s /\ t' SUBSET t /\
     (!x y. x IN s /\ y IN t
            ==> ?x' y'. x' IN s' /\ y' IN t' /\ dist(x',y') <= dist(x,y))
     ==> setdist(s',t') = setdist(s,t)`;;

let REAL_LE_SETDIST = `!s t:real^N->bool d.
        ~(s = {}) /\ ~(t = {}) /\
        (!x y. x IN s /\ y IN t ==> d <= dist(x,y))
        ==> d <= setdist(s,t)`;;

let SETDIST_LE_DIST = `!s t x y:real^N. x IN s /\ y IN t ==> setdist(s,t) <= dist(x,y)`;;

let REAL_LE_SETDIST_EQ = `!d s t:real^N->bool.
        d <= setdist(s,t) <=>
        (!x y. x IN s /\ y IN t ==> d <= dist(x,y)) /\
        (s = {} \/ t = {} ==> d <= &0)`;;

let REAL_SETDIST_LT_EXISTS = `!s t:real^N->bool b.
        ~(s = {}) /\ ~(t = {}) /\ setdist(s,t) < b
        ==> ?x y. x IN s /\ y IN t /\ dist(x,y) < b`;;

let SETDIST_REFL = `!s:real^N->bool. setdist(s,s) = &0`;;

let SETDIST_SYM = `!s t. setdist(s,t) = setdist(t,s)`;;

let SETDIST_TRIANGLE = `!s a t:real^N->bool.
        setdist(s,t) <= setdist(s,{a}) + setdist({a},t)`;;

let SETDIST_SINGS = `!x y. setdist({x},{y}) = dist(x,y)`;;

let SETDIST_SCALING = `!a s t:real^N->bool.
        setdist(IMAGE (\x. a % x) s,IMAGE (\x. a % x) t) =
        abs a * setdist(s,t)`;;

let SETDIST_UNIFORMLY_CONTINUOUS_ON = `(!f:real^M->real^N s.
        f uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !t t'. t SUBSET s /\ t' SUBSET s /\ setdist(t',t) < d
                           ==> setdist(IMAGE f t',IMAGE f t) < e)`
and SETDIST_UNIFORMLY_CONTINUOUS_ON_ALT = `(!f:real^M->real^N s.
        f uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !t t'. t SUBSET s /\ t' SUBSET s /\
                           bounded t /\ bounded t' /\
                           setdist(t',t) < d
                           ==> setdist(IMAGE f t',IMAGE f t) < e)`;;

let th =
 `!c. &0 < c
       ==> !s t. setdist(IMAGE (\x. c % x) s,IMAGE (\x. c % x) t) =
                 c * setdist(s,t)`in
add_scaling_theorems [th];;

let SETDIST_SING_TRIANGLE = `!s x y:real^N. abs(setdist({x},s) - setdist({y},s)) <= dist(x,y)`;;

let CONTINUOUS_AT_LIFT_SETDIST = `!s x:real^N. (\y. lift(setdist({y},s))) continuous (at x)`;;

let CONTINUOUS_ON_LIFT_SETDIST = `!s t:real^N->bool. (\y. lift(setdist({y},s))) continuous_on t`;;

let UNIFORMLY_CONTINUOUS_ON_LIFT_SETDIST = `!s t:real^N->bool.
         (\y. lift(setdist({y},s))) uniformly_continuous_on t`;;

let SETDIST_DIFFERENCES = `!s t. setdist(s,t) = setdist({vec 0},{x - y:real^N | x IN s /\ y IN t})`;;

let SETDIST_SUBSET_RIGHT = `!s t u:real^N->bool.
    ~(t = {}) /\ t SUBSET u ==> setdist(s,u) <= setdist(s,t)`;;

let SETDIST_SUBSET_LEFT = `!s t u:real^N->bool.
    ~(s = {}) /\ s SUBSET t ==> setdist(t,u) <= setdist(s,u)`;;

let SETDIST_CLOSURE = `(!s t:real^N->bool. setdist(closure s,t) = setdist(s,t)) /\
   (!s t:real^N->bool. setdist(s,closure t) = setdist(s,t))`;;

let SETDIST_FRONTIER = `(!s t:real^N->bool.
        DISJOINT s t ==> setdist(frontier s,t) = setdist(s,t)) /\
   (!s t:real^N->bool.
        DISJOINT s t ==> setdist(s,frontier t) = setdist(s,t))`;;

let SETDIST_COMPACT_CLOSED = `!s t:real^N->bool.
        compact s /\ closed t /\ ~(s = {}) /\ ~(t = {})
        ==> ?x y. x IN s /\ y IN t /\ dist(x,y) = setdist(s,t)`;;

let SETDIST_CLOSED_COMPACT = `!s t:real^N->bool.
        closed s /\ compact t /\ ~(s = {}) /\ ~(t = {})
        ==> ?x y. x IN s /\ y IN t /\ dist(x,y) = setdist(s,t)`;;

let SETDIST_EQ_0_COMPACT_CLOSED = `!s t:real^N->bool.
        compact s /\ closed t
        ==> (setdist(s,t) = &0 <=> s = {} \/ t = {} \/ ~(s INTER t = {}))`;;

let SETDIST_EQ_0_CLOSED_COMPACT = `!s t:real^N->bool.
        closed s /\ compact t
        ==> (setdist(s,t) = &0 <=> s = {} \/ t = {} \/ ~(s INTER t = {}))`;;

let SETDIST_EQ_0_BOUNDED = `!s t:real^N->bool.
        (bounded s \/ bounded t)
        ==> (setdist(s,t) = &0 <=>
             s = {} \/ t = {} \/ ~(closure(s) INTER closure(t) = {}))`;;

let SETDIST_TRANSLATION = `!a:real^N s t.
        setdist(IMAGE (\x. a + x) s,IMAGE (\x. a + x) t) = setdist(s,t)`;;

add_translation_invariants [SETDIST_TRANSLATION];;

let SETDIST_LINEAR_IMAGE = `!f:real^M->real^N s t.
        linear f /\ (!x. norm(f x) = norm x)
        ==> setdist(IMAGE f s,IMAGE f t) = setdist(s,t)`;;

add_linear_invariants [SETDIST_LINEAR_IMAGE];;

let SETDIST_UNIQUE = `!s t a b:real^N d.
        a IN s /\ b IN t /\ dist(a,b) = d /\
        (!x y. x IN s /\ y IN t ==> dist(a,b) <= dist(x,y))
        ==> setdist(s,t) = d`;;

let SETDIST_UNIV = `(!s. setdist(s,(:real^N)) = &0) /\
   (!t. setdist((:real^N),t) = &0)`;;

let SETDIST_ZERO = `!s t:real^N->bool. ~(DISJOINT s t) ==> setdist(s,t) = &0`;;

let SETDIST_ZERO_STRONG = `!s t:real^N->bool.
      ~(DISJOINT (closure s) (closure t)) ==> setdist(s,t) = &0`;;

let SETDIST_FRONTIERS = `!s t:real^N->bool.
        setdist(s,t) =
        if DISJOINT s t then setdist(frontier s,frontier t) else &0`;;

let SETDIST_SING_FRONTIER = `!s x:real^N. ~(x IN s) ==> setdist({x},frontier s) = setdist({x},s)`;;

let SETDIST_CLOSEST_POINT = `!a:real^N s.
      closed s /\ ~(s = {}) ==> setdist({a},s) = dist(a,closest_point s a)`;;

let SETDIST_EQ_0_SING = `(!s x:real^N. setdist({x},s) = &0 <=> s = {} \/ x IN closure s) /\
   (!s x:real^N. setdist(s,{x}) = &0 <=> s = {} \/ x IN closure s)`;;

let SETDIST_EQ_0_CLOSED = `!s x. closed s ==> (setdist({x},s) = &0 <=> s = {} \/ x IN s)`;;

let SETDIST_EQ_0_CLOSED_IN = `!u s x. closed_in (subtopology euclidean u) s /\ x IN u
           ==> (setdist({x},s) = &0 <=> s = {} \/ x IN s)`;;

let SETDIST_SING_IN_SET = `!x s. x IN s ==> setdist({x},s) = &0`;;

let SETDIST_SING_FRONTIER_CASES = `!s x:real^N.
        setdist({x},s) = if x IN s then &0 else setdist({x},frontier s)`;;

let SETDIST_LE_SING = `!s t x:real^N. x IN s ==> setdist(s,t) <= setdist({x},t)`;;

let SETDIST_BALLS = `(!a b:real^N r s.
        setdist(ball(a,r),ball(b,s)) =
        if r <= &0 \/ s <= &0 then &0 else max (&0) (dist(a,b) - (r + s))) /\
   (!a b:real^N r s.
        setdist(ball(a,r),cball(b,s)) =
        if r <= &0 \/ s < &0 then &0 else max (&0) (dist(a,b) - (r + s))) /\
   (!a b:real^N r s.
        setdist(cball(a,r),ball(b,s)) =
        if r < &0 \/ s <= &0 then &0 else max (&0) (dist(a,b) - (r + s))) /\
   (!a b:real^N r s.
        setdist(cball(a,r),cball(b,s)) =
        if r < &0 \/ s < &0 then &0 else max (&0) (dist(a,b) - (r + s)))`;;

let OPEN_TRANSLATION_SUBSET_PREIMAGE = `!s t:real^N->bool.
        compact s /\ open t ==> open {a | IMAGE (\x. a + x) s SUBSET t}`;;

(* ------------------------------------------------------------------------- *)
(* A nice characterization of uniform continuity via setdist.                *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_ON_SETDIST = `!f:real^M->real^N s t t'.
        f uniformly_continuous_on s /\
        t SUBSET s /\ t' SUBSET s /\ setdist(t,t') = &0
        ==> setdist(IMAGE f t,IMAGE f t') = &0`;;

let UNIFORMLY_CONTINUOUS_ON_SETDIST_EQ = `!f:real^M->real^N s.
        f uniformly_continuous_on s <=>
        !t t'. t SUBSET s /\ t' SUBSET s /\ setdist(t,t') = &0
              ==> setdist(IMAGE f t,IMAGE f t') = &0`;;

(* ------------------------------------------------------------------------- *)
(* Use set distance for an easy proof of separation properties etc.          *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_SEPARATED_UNION = `!s t:real^N->bool.
        &0 < setdist(s,t)
        ==> open_in (subtopology euclidean (s UNION t)) s /\
            open_in (subtopology euclidean (s UNION t)) t`;;

let CLOSED_IN_SEPARATED_UNION = `!s t:real^N->bool.
        &0 < setdist(s,t)
        ==> closed_in (subtopology euclidean (s UNION t)) s /\
            closed_in (subtopology euclidean (s UNION t)) t`;;

let COMPACT_IN_SEPARATED_UNION = `!s t:real^N->bool.
        compact(s UNION t) /\ &0 < setdist(s,t) ==> compact s /\ compact t`;;

let CONNECTED_IMP_NONSEPARATED_UNION = `!s t:real^N->bool. connected(s UNION t) ==> setdist(s,t) = &0`;;

let SEPARATION_CLOSURES = `!s t:real^N->bool.
        s INTER closure(t) = {} /\ t INTER closure(s) = {}
        ==> ?u v. DISJOINT u v /\ open u /\ open v /\
                  s SUBSET u /\ t SUBSET v`;;

let SEPARATION_NORMAL = `!s t:real^N->bool.
        closed s /\ closed t /\ s INTER t = {}
        ==> ?u v. open u /\ open v /\
                  s SUBSET u /\ t SUBSET v /\ u INTER v = {}`;;

let SEPARATION_NORMAL_LOCAL_CLOSURES = `!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        DISJOINT s t
        ==> ?s' t'. open_in (subtopology euclidean u) s' /\
                    open_in (subtopology euclidean u) t' /\
                    s SUBSET s' /\ t SUBSET t' /\ DISJOINT s' t' /\
                    DISJOINT (subtopology euclidean u closure_of s')
                             (subtopology euclidean u closure_of t')`;;

let SEPARATION_NORMAL_LOCAL = `!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        s INTER t = {}
        ==> ?s' t'. open_in (subtopology euclidean u) s' /\
                    open_in (subtopology euclidean u) t' /\
                    s SUBSET s' /\ t SUBSET t' /\ s' INTER t' = {}`;;

let SEPARATION_NORMAL_CLOSURES = `!s t:real^N->bool.
        closed s /\ closed t /\ DISJOINT s t
        ==> ?s' t'. open s' /\ open t' /\
                    s SUBSET s' /\ t SUBSET t' /\ DISJOINT s' t' /\
                    DISJOINT (closure s') (closure t')`;;

let SEPARATION_NORMAL_COMPACT = `!s t:real^N->bool.
        compact s /\ closed t /\ s INTER t = {}
        ==> ?u v. open u /\ compact(closure u) /\ open v /\
                  s SUBSET u /\ t SUBSET v /\ u INTER v = {}`;;

let SEPARATION_HAUSDORFF = `!x:real^N y.
      ~(x = y)
      ==> ?u v. open u /\ open v /\ x IN u /\ y IN v /\ (u INTER v = {})`;;

let SEPARATION_T2 = `!x:real^N y.
        ~(x = y) <=> ?u v. open u /\ open v /\ x IN u /\ y IN v /\
                           (u INTER v = {})`;;

let SEPARATION_T1 = `!x:real^N y.
        ~(x = y) <=> ?u v. open u /\ open v /\ x IN u /\ ~(y IN u) /\
                           ~(x IN v) /\ y IN v`;;

let SEPARATION_T0 = `!x:real^N y. ~(x = y) <=> ?u. open u /\ ~(x IN u <=> y IN u)`;;

let CLOSED_IN_EQ_CONTINUOUS_LEVELSET = `!u s a.
        closed_in (subtopology euclidean u) s <=>
        ?f:real^M->real^N. f continuous_on u /\ {x | x IN u /\ f x = a} = s`;;

let CLOSED_EQ_CONTINUOUS_LEVELSET = `!s a.
        closed s <=>
        ?f:real^M->real^N. f continuous_on (:real^M) /\ {x | f x = a} = s`;;

let CONNECTED = `!s:real^N->bool.
      connected s <=>
      ~(?e1 e2. open e1 /\ open e2 /\ s SUBSET (e1 UNION e2) /\
                e1 INTER e2 = {} /\ ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

(* ------------------------------------------------------------------------- *)
(* Connectedness of the intersection of a chain.                             *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_CHAIN = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> compact s /\ connected s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> connected(INTERS f)`;;

let CONNECTED_CHAIN_GEN = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> closed s /\ connected s) /\
        (?s. s IN f /\ compact s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> connected(INTERS f)`;;

let CONNECTED_NEST = `!s. (!n. compact(s n) /\ connected(s n)) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> connected(INTERS {(s:num->real^N->bool) n | n IN (:num)})`;;

let CONNECTED_NEST_GEN = `!s. (!n. closed(s n) /\ connected(s n)) /\ (?n. compact(s n)) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> connected(INTERS {(s:num->real^N->bool) n | n IN (:num)})`;;

(* ------------------------------------------------------------------------- *)
(* Hausdorff distance between sets.                                          *)
(* ------------------------------------------------------------------------- *)

let hausdist = new_definition
 `hausdist(s:real^N->bool,t:real^N->bool) =
        let ds = {setdist({x},t) | x IN s} UNION {setdist({y},s) | y IN t} in
        if ~(ds = {}) /\ (?b. !d. d IN ds ==> d <= b) then sup ds
        else &0`;;

let HAUSDIST_POS_LE = `!s t:real^N->bool. &0 <= hausdist(s,t)`;;

let HAUSDIST_POS_LT = `!s t:real^N->bool. &0 < hausdist(s,t) <=> ~(hausdist(s,t) = &0)`;;

let REAL_ABS_HAUSDIST = `!s t:real^N->bool. abs(hausdist(s,t)) = hausdist(s,t)`;;

let HAUSDIST_REFL = `!s:real^N->bool. hausdist(s,s) = &0`;;

let HAUSDIST_SYM = `!s t:real^N->bool. hausdist(s,t) = hausdist(t,s)`;;

let HAUSDIST_EMPTY = `(!t:real^N->bool. hausdist ({},t) = &0) /\
   (!s:real^N->bool. hausdist (s,{}) = &0)`;;

let HAUSDIST_SINGS = `!x y:real^N. hausdist({x},{y}) = dist(x,y)`;;

let HAUSDIST_SCALING = `!a s t:real^N->bool.
        hausdist(IMAGE (\x. a % x) s,IMAGE (\x. a % x) t) =
        abs a * hausdist(s,t)`;;

let th =
 `!c. &0 < c
       ==> !s t. hausdist(IMAGE (\x. c % x) s,IMAGE (\x. c % x) t) =
                 c * hausdist(s,t)` in
add_scaling_theorems [th];;

let HAUSDIST_EQ = `!s t:real^M->bool s' t':real^N->bool.
        (!b. (!x. x IN s ==> setdist({x},t) <= b) /\
             (!y. y IN t ==> setdist({y},s) <= b) <=>
             (!x. x IN s' ==> setdist({x},t') <= b) /\
             (!y. y IN t' ==> setdist({y},s') <= b))
        ==> hausdist(s,t) = hausdist(s',t')`;;

let HAUSDIST_TRANSLATION = `!a s t:real^N->bool.
        hausdist(IMAGE (\x. a + x) s,IMAGE (\x. a + x) t) = hausdist(s,t)`;;

add_translation_invariants [HAUSDIST_TRANSLATION];;

let HAUSDIST_LINEAR_IMAGE = `!f:real^M->real^N s t.
           linear f /\ (!x. norm(f x) = norm x)
           ==> hausdist(IMAGE f s,IMAGE f t) = hausdist(s,t)`;;

add_linear_invariants [HAUSDIST_LINEAR_IMAGE];;

let HAUSDIST_CLOSURE = `(!s t:real^N->bool. hausdist(closure s,t) = hausdist(s,t)) /\
   (!s t:real^N->bool. hausdist(s,closure t) = hausdist(s,t))`;;

let REAL_HAUSDIST_LE = `!s t:real^N->bool b.
        ~(s = {}) /\ ~(t = {}) /\
        (!x. x IN s ==> setdist({x},t) <= b) /\
        (!y. y IN t ==> setdist({y},s) <= b)
        ==> hausdist(s,t) <= b`;;

let REAL_HAUSDIST_LE_SUMS = `!s t:real^N->bool b.
        ~(s = {}) /\ ~(t = {}) /\
        s SUBSET {y + z | y IN t /\ z IN cball(vec 0,b)} /\
        t SUBSET {y + z | y IN s /\ z IN cball(vec 0,b)}
        ==> hausdist(s,t) <= b`;;

let REAL_LE_HAUSDIST  = `!s t:real^N->bool a b c z.
        ~(s = {}) /\ ~(t = {}) /\
        (!x. x IN s ==> setdist({x},t) <= b) /\
        (!y. y IN t ==> setdist({y},s) <= c) /\
        (z IN s /\ a <= setdist({z},t) \/ z IN t /\ a <= setdist({z},s))
        ==> a <= hausdist(s,t)`;;

let SETDIST_LE_HAUSDIST = `!s t:real^N->bool.
        bounded s /\ bounded t ==> setdist(s,t) <= hausdist(s,t)`;;

let SETDIST_SING_LE_HAUSDIST = `!s t x:real^N.
        bounded s /\ bounded t /\ x IN s ==> setdist({x},t) <= hausdist(s,t)`;;

let SETDIST_HAUSDIST_TRIANGLE = `!s t u:real^N->bool.
        ~(t = {}) /\ bounded t /\ bounded u
        ==> setdist(s,u) <= setdist(s,t) + hausdist(t,u)`;;

let HAUSDIST_SETDIST_TRIANGLE = `!s t u:real^N->bool.
        ~(t = {}) /\ bounded s /\ bounded t
        ==> setdist(s,u) <= hausdist(s,t) + setdist(t,u)`;;

let REAL_LT_HAUSDIST_POINT_EXISTS = `!s t x:real^N d.
        bounded s /\ bounded t /\ ~(t = {}) /\ hausdist(s,t) < d /\ x IN s
        ==> ?y. y IN t /\ dist(x,y) < d`;;

let HAUSDIST_UNIFORMLY_CONTINUOUS_ON = `!f:real^M->real^N s.
        f uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !t t'. t SUBSET s /\ t' SUBSET s /\
                           bounded t /\ bounded t' /\
                           hausdist(t',t) < d
                           ==> hausdist(IMAGE f t',IMAGE f t) < e`;;

let SUBSET_COMPACT_HAUSDIST_LIMIT = `!f s t:real^N->bool.
        compact s /\ ~(s = {}) /\
        (!n. t SUBSET f n) /\ (!n. bounded(f n)) /\
        ((\n. lift(hausdist (f n,s))) --> vec 0) sequentially
        ==> t SUBSET s`;;

let UPPER_LOWER_HEMICONTINUOUS = `!f:real^M->real^N->bool t s.
      (!x. x IN s ==> f(x) SUBSET t) /\
      (!u. open_in (subtopology euclidean t) u
           ==> open_in (subtopology euclidean s)
                       {x | x IN s /\ f(x) SUBSET u}) /\
      (!u. closed_in (subtopology euclidean t) u
           ==> closed_in (subtopology euclidean s)
                         {x | x IN s /\ f(x) SUBSET u})
      ==> !x e. x IN s /\ &0 < e /\ bounded(f x)
                ==> ?d. &0 < d /\
                        !x'. x' IN s /\ dist(x,x') < d
                             ==> hausdist(f x,f x') < e`;;

let HAUSDIST_NONTRIVIAL = `!s t:real^N->bool.
        bounded s /\ bounded t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) =
            sup({setdist ({x},t) | x IN s} UNION {setdist ({y},s) | y IN t})`;;

let HAUSDIST_NONTRIVIAL_ALT = `!s t:real^N->bool.
        bounded s /\ bounded t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) = max (sup {setdist ({x},t) | x IN s})
                                (sup {setdist ({y},s) | y IN t})`;;

let REAL_HAUSDIST_LE_EQ = `!s t:real^N->bool b.
        ~(s = {}) /\ ~(t = {}) /\ bounded s /\ bounded t
        ==> (hausdist(s,t) <= b <=>
             (!x. x IN s ==> setdist({x},t) <= b) /\
             (!y. y IN t ==> setdist({y},s) <= b))`;;

let HAUSDIST_UNION_LE = `!s t u:real^N->bool.
        bounded s /\ bounded t /\ bounded u /\ ~(t = {}) /\ ~(u = {})
        ==> hausdist(s UNION t,s UNION u) <= hausdist(t,u)`;;

let HAUSDIST_INSERT_LE = `!s t a:real^N.
        bounded s /\ bounded t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(a INSERT s,a INSERT t) <= hausdist(s,t)`;;

let HAUSDIST_COMPACT_EXISTS = `!s t:real^N->bool.
        bounded s /\ compact t /\ ~(t = {})
        ==> !x. x IN s ==> ?y. y IN t /\ dist(x,y) <= hausdist(s,t)`;;

let HAUSDIST_TRIANGLE = `!s t u:real^N->bool.
        bounded s /\ bounded t /\ bounded u /\ ~(t = {})
        ==> hausdist(s,u) <= hausdist(s,t) + hausdist(t,u)`;;

let HAUSDIST_COMPACT_SUMS = `!s t:real^N->bool.
        bounded s /\ compact t /\ ~(t = {})
        ==> s SUBSET {y + z | y IN t /\ z IN cball(vec 0,hausdist(s,t))}`;;

let HAUSDIST_SUMS_LE = `!s t u v:real^N->bool.
        bounded s /\ bounded t /\ bounded u /\ bounded v
        ==> hausdist({x + y | x IN s /\ y IN t},{x + y | x IN u /\ y IN v})
            <= hausdist(s,u) + hausdist(t,v)`;;

let HAUSDIST_SUMS_LE_LCANCEL = `!s t u:real^N->bool.
        bounded s /\ bounded t /\ bounded u
        ==> hausdist({x + y | x IN s /\ y IN t},{x + y | x IN s /\ y IN u})
            <= hausdist(t,u)`;;

let HAUSDIST_SUMS_LE_RCANCEL = `!s t u:real^N->bool.
        bounded s /\ bounded t /\ bounded u
        ==> hausdist({x + y | x IN s /\ y IN u},{x + y | x IN t /\ y IN u})
            <= hausdist(s,t)`;;

let HAUSDIST_EQ_0 = `!s t:real^N->bool.
      bounded s /\ bounded t
      ==> (hausdist(s,t) = &0 <=> s = {} \/ t = {} \/ closure s = closure t)`;;

let HAUSDIST_COMPACT_NONTRIVIAL = `!s t:real^N->bool.
        compact s /\ compact t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) =
            inf {e | &0 <= e /\
                   s SUBSET {x + y | x IN t /\ norm y <= e} /\
                   t SUBSET {x + y | x IN s /\ norm y <= e}}`;;

let HAUSDIST_BALLS = `(!a b:real^N r s.
        hausdist(ball(a,r),ball(b,s)) =
        if r <= &0 \/ s <= &0 then &0 else dist(a,b) + abs(r - s)) /\
   (!a b:real^N r s.
        hausdist(ball(a,r),cball(b,s)) =
        if r <= &0 \/ s < &0 then &0 else dist(a,b) + abs(r - s)) /\
   (!a b:real^N r s.
        hausdist(cball(a,r),ball(b,s)) =
        if r < &0 \/ s <= &0 then &0 else dist(a,b) + abs(r - s)) /\
   (!a b:real^N r s.
        hausdist(cball(a,r),cball(b,s)) =
        if r < &0 \/ s < &0 then &0 else dist(a,b) + abs(r - s))`;;

let HAUSDIST_ALT = `!s t:real^N->bool.
        bounded s /\ bounded t /\ ~(s = {}) /\ ~(t = {})
        ==> hausdist(s,t) =
            sup {abs(setdist({x},s) - setdist({x},t)) | x IN (:real^N)}`;;

let DIAMETERS_HAUSDIST_BOUND = `!s t:real^N->bool.
        bounded s /\ ~(s = {}) /\ bounded t /\ ~(t = {})
        ==> abs(diameter s - diameter t) <= &2 * hausdist(s,t)`;;

let CONTINUOUS_DIAMETER = `!s:real^N->bool e.
        bounded s /\ ~(s = {}) /\ &0 < e
        ==> ?d. &0 < d /\
                !t. bounded t /\ ~(t = {}) /\ hausdist(s,t) < d
                    ==> abs(diameter s - diameter t) < e`;;

let CONNECTED_HAUSDIST_LIMIT = `!s k:real^N->bool.
        (!n. bounded(s n) /\ connected(s n) /\ ~(s n = {})) /\
        compact k /\ ((\n. lift (hausdist(s n,k))) --> vec 0) sequentially
        ==> connected k`;;

let HAUSDIST_COMPACT_INTERS_LIMIT = `!s:num->(real^N->bool).
        (!n. compact(s n)) /\ (!n. s(SUC n) SUBSET s n)
        ==> ((\n. lift(hausdist(s n,INTERS {s i | i IN (:num)}))) --> vec 0)
            sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Hausdorff metric inherits completeness, total boundedness, compactness.   *)
(* ------------------------------------------------------------------------- *)

let COMPLETE_HAUSDIST_UNIV = `!f:num->(real^N->bool).
        (!n. bounded(f n) /\ ~(f n = {})) /\
        (!e. &0 < e
             ==> ?N. !m n. m >= N /\ n >= N ==> hausdist(f m,f n) < e)
        ==> ?s. compact s /\ ~(s = {}) /\
                ((\n. lift(hausdist(f n,s))) --> vec 0) sequentially`;;

let COMPLETE_HAUSDIST = `!f:num->(real^N->bool) c.
        closed c /\
        (!n. bounded(f n) /\ ~(f n = {}) /\ f n SUBSET c) /\
        (!e. &0 < e
             ==> ?N. !m n. m >= N /\ n >= N ==> hausdist(f m,f n) < e)
        ==> ?s. compact s /\ ~(s = {}) /\ s SUBSET c /\
                ((\n. lift(hausdist(f n,s))) --> vec 0) sequentially`;;

let TOTALLY_BOUNDED_HAUSDIST = `!s:real^N->bool e.
        bounded s /\ &0 < e
        ==> ?k. FINITE k /\
                (!u. u IN k ==> ~(u = {}) /\ u SUBSET s) /\
                (!t. t SUBSET s /\ ~(t = {})
                     ==> ?u. u IN k /\ hausdist(t,u) < e)`;;

let COMPACT_HAUSDIST = `!f:num->(real^N->bool) c.
        compact c /\ (!n. ~(f n = {}) /\ f n SUBSET c)
        ==> ?r s. (!m n. m < n ==> r m < r n) /\
                  compact s /\ ~(s = {}) /\ s SUBSET c /\
                  ((\n. lift(hausdist(f(r n),s))) --> vec 0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Isometries are embeddings, and even surjective in the compact case.       *)
(* ------------------------------------------------------------------------- *)

let ISOMETRY_IMP_OPEN_MAP = `!f:real^M->real^N s t u.
        IMAGE f s = t /\
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y)) /\
        open_in (subtopology euclidean s) u
        ==> open_in (subtopology euclidean t) (IMAGE f u)`;;

let ISOMETRY_IMP_EMBEDDING = `!f:real^M->real^N s t.
        IMAGE f s = t /\ (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y))
        ==> ?g. homeomorphism (s,t) (f,g)`;;

let ISOMETRY_IMP_HOMEOMORPHISM_COMPACT = `!f s:real^N->bool.
        compact s /\ IMAGE f s SUBSET s /\
        (!x y. x IN s /\ y IN s ==> dist(f x,f y) = dist(x,y))
        ==> ?g. homeomorphism (s,s) (f,g)`;;

(* ------------------------------------------------------------------------- *)
(* Urysohn's lemma (for real^N, where the proof is easy using distances).    *)
(* ------------------------------------------------------------------------- *)

let URYSOHN_LOCAL_STRONG = `!s t u a b.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        s INTER t = {} /\ ~(a = b)
        ==> ?f:real^N->real^M.
               f continuous_on u /\
               (!x. x IN u ==> f(x) IN segment[a,b]) /\
               (!x. x IN u ==> (f x = a <=> x IN s)) /\
               (!x. x IN u ==> (f x = b <=> x IN t))`;;

let URYSOHN_LOCAL = `!s t u a b.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        s INTER t = {}
        ==> ?f:real^N->real^M.
               f continuous_on u /\
               (!x. x IN u ==> f(x) IN segment[a,b]) /\
               (!x. x IN s ==> f x = a) /\
               (!x. x IN t ==> f x = b)`;;

let URYSOHN_STRONG = `!s t a b.
        closed s /\ closed t /\ s INTER t = {} /\ ~(a = b)
        ==> ?f:real^N->real^M.
               f continuous_on (:real^N) /\ (!x. f(x) IN segment[a,b]) /\
               (!x. f x = a <=> x IN s) /\ (!x. f x = b <=> x IN t)`;;

let URYSOHN = `!s t a b.
        closed s /\ closed t /\ s INTER t = {}
        ==> ?f:real^N->real^M.
               f continuous_on (:real^N) /\ (!x. f(x) IN segment[a,b]) /\
               (!x. x IN s ==> f x = a) /\ (!x. x IN t ==> f x = b)`;;

(* ------------------------------------------------------------------------- *)
(* Density of points with rational, or just dyadic rational, coordinates.    *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_DYADIC_RATIONALS = `closure { inv(&2 pow n) % x |n,x|
             !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) } = (:real^N)`;;

let CLOSURE_RATIONAL_COORDINATES = `closure { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) } =
   (:real^N)`;;

let CLOSURE_DYADIC_RATIONALS_IN_OPEN_SET = `!s:real^N->bool.
        open s
        ==> closure(s INTER
                    { inv(&2 pow n) % x | n,x |
                      !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }) =
            closure s`;;

let CLOSURE_RATIONALS_IN_OPEN_SET = `!s:real^N->bool.
      open s
      ==> closure(s INTER
                  { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }) =
          closure s`;;

(* ------------------------------------------------------------------------- *)
(* Various separability-type properties.                                     *)
(* ------------------------------------------------------------------------- *)

let UNIV_SECOND_COUNTABLE = `?b. COUNTABLE b /\ (!c. c IN b ==> open c) /\
       !s:real^N->bool. open s ==> ?u. u SUBSET b /\ s = UNIONS u`;;

let UNIV_SECOND_COUNTABLE_SEQUENCE = `?b:num->real^N->bool.
        (!m n. b m = b n <=> m = n) /\
        (!n. open(b n)) /\
        (!s. open s ==> ?k. s = UNIONS {b n | n IN k})`;;

let SUBSET_SECOND_COUNTABLE = `!s:real^N->bool.
       ?b. COUNTABLE b /\
           (!c. c IN b ==> ~(c = {}) /\ open_in(subtopology euclidean s) c) /\
           !t. open_in(subtopology euclidean s) t
               ==> ?u. u SUBSET b /\ t = UNIONS u`;;

let SEPARABLE = `!s:real^N->bool.
        ?t. COUNTABLE t /\ t SUBSET s /\ s SUBSET closure t`;;

let OPEN_SET_RATIONAL_COORDINATES = `!s. open s /\ ~(s = {})
       ==> ?x:real^N. x IN s /\
                      !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)`;;

let OPEN_COUNTABLE_UNION_OPEN_INTERVALS = `(!s:real^N->bool.
        open s
        ==> ?D. COUNTABLE D /\
                (!i. i IN D ==> i SUBSET s /\ ?a b. i = interval(a,b)) /\
                UNIONS D = s)`
and OPEN_COUNTABLE_UNION_CLOSED_INTERVALS = `(!s:real^N->bool.
        open s
        ==> ?D. COUNTABLE D /\
                (!i. i IN D ==> i SUBSET s /\ ?a b. i = interval[a,b]) /\
                UNIONS D = s)`;;

let LINDELOF = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> open s)
        ==> ?f'. f' SUBSET f /\ COUNTABLE f' /\ UNIONS f' = UNIONS f`;;

let LINDELOF_OPEN_IN = `!f u:real^N->bool.
        (!s. s IN f ==> open_in (subtopology euclidean u) s)
        ==> ?f'. f' SUBSET f /\ COUNTABLE f' /\ UNIONS f' = UNIONS f`;;

let COUNTABLE_DISJOINT_OPEN_IN_SUBSETS = `!f:(real^N->bool)->bool u.
        (!s. s IN f ==> open_in (subtopology euclidean u) s) /\
        pairwise DISJOINT f
        ==> COUNTABLE f`;;

let COUNTABLE_DISJOINT_OPEN_SUBSETS = `!f. (!s:real^N->bool. s IN f ==> open s) /\ pairwise DISJOINT f
       ==> COUNTABLE f`;;

let COUNTABLE_DISJOINT_NONEMPTY_INTERIOR_SUBSETS = `!f:(real^N->bool)->bool.
        (!s. s IN f /\ interior s = {} ==> s = {}) /\ pairwise DISJOINT f
        ==> COUNTABLE f`;;

let COUNTABLE_COMPACT_OPEN_IN = `!u:real^N->bool.
        COUNTABLE {c | compact c /\ open_in (subtopology euclidean u) c}`;;

let COUNTABLE_CLOPEN_IN = `!u:real^N->bool.
        compact u
        ==> COUNTABLE {c | closed_in (subtopology euclidean u) c /\
                           open_in (subtopology euclidean u) c}`;;

let CARD_EQ_OPEN_SETS = `{s:real^N->bool | open s} =_c (:real)`;;

let CARD_EQ_CLOSED_SETS = `{s:real^N->bool | closed s} =_c (:real)`;;

let CARD_EQ_COMPACT_SETS = `{s:real^N->bool | compact s} =_c (:real)`;;

let COUNTABLE_NON_CONDENSATION_POINTS = `!s:real^N->bool. COUNTABLE(s DIFF {x | x condensation_point_of s})`;;

let COUNTABLE_NON_LIMIT_POINTS = `!s:real^N->bool. COUNTABLE(s DIFF {x | x limit_point_of s})`;;

let COUNTABLE_ISOLATED_SET = `!s:real^N->bool.
        (!a. a IN s ==> ~(a limit_point_of s)) ==> COUNTABLE s`;;

let CARD_EQ_CONDENSATION_POINTS_IN_SET = `!s:real^N->bool.
     ~(COUNTABLE s) ==> {x | x IN s /\ x condensation_point_of s} =_c s`;;

let LIMPT_OF_CONDENSATION_POINTS = `(!x:real^N s.
        x limit_point_of {y | y condensation_point_of s} <=>
        x condensation_point_of s)`
and CONDENSATION_POINT_OF_CONDENSATION_POINTS = `(!x:real^N s.
        x condensation_point_of {y | y condensation_point_of s} <=>
        x condensation_point_of s)`;;

let CLOSED_CONDENSATION_POINTS = `!s:real^N->bool. closed {x | x condensation_point_of s}`;;

let CANTOR_BENDIXSON_GEN = `!s:real^N->bool.
      ?t u.
        closed_in (subtopology euclidean s) t /\
        (!x. x IN t ==> x condensation_point_of t) /\
        COUNTABLE u /\ DISJOINT t u /\ s = t UNION u`;;

let CANTOR_BENDIXSON = `!s:real^N->bool.
        closed s
        ==> ?t u. closed t /\ (!x. x IN t ==> x limit_point_of t) /\
                  COUNTABLE u /\ DISJOINT t u /\ s = t UNION u`;;

(* ------------------------------------------------------------------------- *)
(* A discrete set is countable, and an uncountable set has a limit point.    *)
(* ------------------------------------------------------------------------- *)

let DISCRETE_IMP_COUNTABLE = `!s:real^N->bool.
        (!x. x IN s ==> ?e. &0 < e /\
                            !y. y IN s /\ ~(y = x) ==> e <= norm(y - x))
        ==> COUNTABLE s`;;

let UNCOUNTABLE_CONTAINS_LIMIT_POINT = `!s. ~(COUNTABLE s) ==> ?x. x IN s /\ x limit_point_of s`;;

(* ------------------------------------------------------------------------- *)
(* Theorems about left and right limits on R^1                               *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_WITHIN_RIGHT_ALT_GEN = `!P s a. eventually P (at a within {x | x IN s /\ drop a <= drop x}) <=>
           eventually P (at a within {x | x IN s /\ drop a < drop x})`;;

let EVENTUALLY_WITHIN_RIGHT_ALT = `!P a. eventually P (at a within {x | drop a <= drop x}) <=>
         eventually P (at a within {x | drop a < drop x})`;;

let RIGHT_LIMIT_WITHIN_ALT = `!f l s a. (f --> l) (at a within {x | x IN s /\ drop a <= drop x}) <=>
             (f --> l) (at a within {x | x IN s /\ drop a < drop x})`;;

let RIGHT_LIMIT_ALT = `!f l a. (f --> l) (at a within {x | drop a <= drop x}) <=>
           (f --> l) (at a within {x | drop a < drop x})`;;

let EVENTUALLY_WITHIN_LEFT_ALT_GEN = `!P s a. eventually P (at a within {x | x IN s /\ drop x <= drop a}) <=>
           eventually P (at a within {x | x IN s /\ drop x < drop a})`;;

let EVENTUALLY_WITHIN_LEFT_ALT = `!P a. eventually P (at a within {x | drop x <= drop a}) <=>
         eventually P (at a within {x | drop x < drop a})`;;

let LEFT_LIMIT_WITHIN_ALT = `!f l s a. (f --> l) (at a within {x | x IN s /\ drop x <= drop a}) <=>
             (f --> l) (at a within {x | x IN s /\ drop x < drop a})`;;

let LEFT_LIMIT_ALT = `!f l a. (f --> l) (at a within {x | drop x <= drop a}) <=>
           (f --> l) (at a within {x | drop x < drop a})`;;

let TWO_SIDED_LIMIT_WITHIN = `!f s a l:real^N.
        (f --> l) (at a within s) <=>
        (f --> l) (at a within s INTER {x | drop x <= drop a}) /\
        (f --> l) (at a within s INTER {x | drop a <= drop x})`;;

let TWO_SIDED_LIMIT_AT = `!f a l:real^N.
        (f --> l) (at a) <=>
        (f --> l) (at a within {x | drop x <= drop a}) /\
        (f --> l) (at a within {x | drop a <= drop x})`;;

let NON_TRIVIAL_LIMIT_LEFT = `!a. ~trivial_limit (at a within {x | drop x <= drop a})`;;

let NON_TRIVIAL_LIMIT_RIGHT = `!a. ~trivial_limit (at a within {x | drop a <= drop x})`;;

let COUNTABLE_TRIVIAL_RIGHT_LIMITS = `!s. COUNTABLE {x | x IN s /\
                      trivial_limit
                        (at x within {t | t IN s /\ drop x <= drop t})}`;;

let COUNTABLE_TRIVIAL_LEFT_LIMITS = `!s. COUNTABLE {x | x IN s /\
                      trivial_limit
                        (at x within {t | t IN s /\ drop t <= drop x})}`;;

let COUNTABLE_NONCONTINUOUS_RIGHT_LIMITS = `!f:real^1->real^N s.
      COUNTABLE
       {x | x IN s /\
            (?l. (f --> l) (at x within {t | t IN s /\ drop x <= drop t})) /\
            ~(f continuous (at x within s))}`;;

let COUNTABLE_NONCONTINUOUS_LEFT_LIMITS = `!f:real^1->real^N s.
      COUNTABLE {x | x IN s /\
                     (?l. (f --> l)
                          (at x within {t | t IN s /\ drop t <= drop x})) /\
                     ~(f continuous (at x within s))}`;;

let COUNTABLE_NONCONTINUOUS_ONE_SIDED_LIMITS = `!f:real^1->real^N s.
      COUNTABLE {x | x IN s /\
                     ((?l. (f --> l)
                           (at x within {t | t IN s /\ drop t <= drop x})) \/
                      (?l. (f --> l)
                           (at x within {t | t IN s /\ drop x <= drop t}))) /\
                     ~(f continuous (at x within s))}`;;

(* ------------------------------------------------------------------------- *)
(* A closed local homeomorphism is proper: it actually has finite preimages. *)
(* ------------------------------------------------------------------------- *)

let CLOSED_LOCAL_HOMEOMORPHISM_IMP_PROPER_GEN = `!f:real^M->real^N s t.
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
        (!w x. open_in (subtopology euclidean s) w /\ x IN w
               ==> ?u. open_in (subtopology euclidean s) u /\
                       {x} PSUBSET u /\ u SUBSET w /\
                       f continuous_on u /\
                       (!x'. x' IN u /\ ~(x' = x) ==> ~(f x' = f x)))
          ==> !y. FINITE {x | x IN s /\ f x = y}`;;

let CLOSED_LOCAL_HOMEOMORPHISM_IMP_PROPER = `!f:real^M->real^N s t.
        (!x. connected_component s x = {x} ==> s = {x}) /\
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
        (!x. x IN s
             ==> ?u v g. x IN u /\
                         open_in (subtopology euclidean s) u /\
                         open_in (subtopology euclidean t) v /\
                         homeomorphism (u,v) (f,g))
        ==> !k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}`;;

(* ------------------------------------------------------------------------- *)
(* The Brouwer reduction theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let BROUWER_REDUCTION_THEOREM_GEN = `!P s:real^N->bool.
        (!f. (!n. closed(f n) /\ P(f n)) /\ (!n. f(SUC n) SUBSET f(n))
              ==> P(INTERS {f n | n IN (:num)})) /\
        closed s /\ P s
        ==> ?t. t SUBSET s /\ closed t /\ P t /\
                (!u. u SUBSET s /\ closed u /\ P u ==> ~(u PSUBSET t))`;;

let BROUWER_REDUCTION_THEOREM = `!P s:real^N->bool.
        (!f. (!n. compact(f n) /\ ~(f n = {}) /\ P(f n)) /\
             (!n. f(SUC n) SUBSET f(n))
             ==> P(INTERS {f n | n IN (:num)})) /\
        compact s /\ ~(s = {}) /\ P s
        ==> ?t. t SUBSET s /\ compact t /\ ~(t = {}) /\ P t /\
                (!u. u SUBSET s /\ closed u /\ ~(u = {}) /\ P u
                     ==> ~(u PSUBSET t))`;;

let MINIMAL_CONTINUUM = `!t s:real^N->bool.
        t SUBSET s /\ compact s /\ connected s
        ==> ?u. t SUBSET u /\ u SUBSET s /\ compact u /\ connected u /\
                !v. v SUBSET u /\ t SUBSET v /\ compact v /\ connected v
                    ==> v = u`;;

(* ------------------------------------------------------------------------- *)
(* The Arzela-Ascoli theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let FUNCTION_CONVERGENT_SUBSEQUENCE = `!f:num->real^M->real^N s M.
        COUNTABLE s /\ (!n x. x IN s ==> norm(f n x) <= M)
        ==> ?k. (!m n:num. m < n ==> k m < k n) /\
                !x. x IN s ==> ?l. ((\n. f (k n) x) --> l) sequentially`;;

let ARZELA_ASCOLI = `!f:num->real^M->real^N s M.
        compact s /\
        (!n x. x IN s ==> norm(f n x) <= M) /\
        (!x e. x IN s /\ &0 < e
               ==> ?d. &0 < d /\
                       !n y. y IN s /\ norm(x - y) < d
                             ==> norm(f n x - f n y) < e)
        ==> ?g. g continuous_on s /\
                ?r. (!m n:num. m < n ==> r m < r n) /\
                    !e. &0 < e
                        ==> ?N. !n x. n >= N /\ x IN s
                                      ==> norm(f(r n) x - g x) < e`;;

let ARZELA_ASCOLI_LIPSCHITZ = `!f:num->real^M->real^N s t b.
     compact s /\ bounded t /\
     (!n x. x IN s ==> ~(IMAGE (f n) s INTER t = {})) /\
     (!n x y. x IN s /\ y IN s ==> norm(f n x - f n y) <= b * norm(x - y))
     ==> ?g. (!x y. x IN s /\ y IN s ==> norm(g x - g y) <= b * norm(x - y)) /\
             ?r. (!m n. m < n ==> r m < r n) /\
                 !e. &0 < e
                     ==> ?N. !n:num x. n >= N /\ x IN s
                                       ==> norm(f (r n) x - g x) < e`;;

(* ------------------------------------------------------------------------- *)
(* Basics about "local" properties in general.                               *)
(* ------------------------------------------------------------------------- *)

let locally = new_definition
 `locally P (s:real^N->bool) <=>
        !w x. open_in (subtopology euclidean s) w /\ x IN w
              ==> ?u v. open_in (subtopology euclidean s) u /\ P v /\
                        x IN u /\ u SUBSET v /\ v SUBSET w`;;

let NEIGHBOURHOOD_BASE_OF_EUCLIDEAN = `!P s:real^N->bool.
        neighbourhood_base_of P (subtopology euclidean s) <=> locally P s`;;

let LOCALLY_MONO = `!P Q s. (!t. P t ==> Q t) /\ locally P s ==> locally Q s`;;

let LOCALLY_OPEN_SUBSET = `!P s t:real^N->bool.
        locally P s /\ open_in (subtopology euclidean s) t
        ==> locally P t`;;

let LOCALLY_LOCALLY = `(!P:(real^N->bool)->bool. locally (locally P) = locally P)`
and LOCALLY_ON_OPEN_SUBSETS = `(!P s:real^N->bool.
        locally P s <=>
        !a. a IN s
            ==> ?v. open_in (subtopology euclidean s) v /\
                    a IN v /\ locally P v)`
and LOCALLY_ON_NBDS = `(!P s:real^N->bool.
        locally P s <=>
        !a. a IN s
            ==> ?u v. open_in (subtopology euclidean s) u /\
                    a IN u /\ u SUBSET v /\ v SUBSET s /\ locally P v)`;;

let LOCALLY_AND_SUBSET = `!s:real^N->bool. locally P s <=> locally (\t. t SUBSET s /\ P t) s`;;

let LOCALLY_AND_OPEN_IN = `!P s:real^N->bool.
        locally (\u. open_in (subtopology euclidean s) u /\ P u) s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\ P u /\
                      x IN u /\
                      u SUBSET v`;;

let LOCALLY_AND_SMALL_LT = `(!P:(real^N->bool)->bool e.
        &0 < e
        ==> locally P = locally (\s. P s /\ bounded s /\ diameter s < e))`
and LOCALLY_AND_SMALL_LE = `(!P:(real^N->bool)->bool e.
        &0 < e
        ==> locally P = locally (\s. P s /\ bounded s /\ diameter s <= e))`;;

let LOCALLY_OPEN_BASIS = `!P s:real^N->bool.
        locally (\u. open_in (subtopology euclidean s) u /\ P u) s <=>
        ?b. COUNTABLE b /\
            (!c. c IN b
                 ==> ~(c = {}) /\
                     open_in (subtopology euclidean s) c /\
                     P c) /\
            (!t. open_in (subtopology euclidean s) t
                 ==> ?u. u SUBSET b /\ t = UNIONS u)`;;

let LOCALLY_AND_OPEN_IN_IDEMPOT = `!P s:real^N->bool.
        locally (\u. open_in (subtopology euclidean s) u /\
                     locally (\v. open_in (subtopology euclidean u) v /\
                                  P v) u) s <=>
        locally (\u. open_in (subtopology euclidean s) u /\ P u) s`;;

let LOCALLY_IMP_COUNTABLE_UNION_OF = `!P s:real^N->bool. locally P s ==> (COUNTABLE UNION_OF P) s`;;

let LOCALLY_IMP_FINITE_UNION_OF = `!P s:real^N->bool. compact s /\ locally P s ==> (FINITE UNION_OF P) s`;;

let LOCALLY_DIFF_CLOSED = `!P s t:real^N->bool.
        locally P s /\ closed_in (subtopology euclidean s) t
        ==> locally P (s DIFF t)`;;

let LOCALLY_CLOSED_IN_EXPLICIT = `!s v a:real^N.
        a IN v /\ open_in (subtopology euclidean s) v
        ==> ?u. a IN u /\
                open_in (subtopology euclidean s) u /\
                u SUBSET v /\
                (subtopology euclidean s) closure_of u SUBSET v`;;

let LOCALLY_CLOSED_IN = `!s:real^N->bool. locally (closed_in (subtopology euclidean s)) s`;;

let LOCALLY_EMPTY = `!P. locally P {}`;;

let LOCALLY_SING = `!P a. locally P {a} <=> P {a}`;;

let LOCALLY_INTER = `!P:(real^N->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> !s t. locally P s /\ locally P t ==> locally P (s INTER t)`;;

let LOCALLY_INTER_OPEN = `!P s t u:real^N->bool.
        locally P s /\
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t
        ==> locally P (s INTER t)`;;

let LOCALLY_OPEN_INTER = `!P s t u:real^N->bool.
        locally P t /\
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t
        ==> locally P (s INTER t)`;;

let LOCALLY_PCROSS = `!P Q R.
        (!s:real^M->bool t:real^N->bool. P s /\ Q t ==> R(s PCROSS t))
        ==> (!s t. locally P s /\ locally Q t ==> locally R (s PCROSS t))`;;

let HOMEOMORPHISM_LOCALLY = `!P Q f:real^N->real^M g.
        (!s t. homeomorphism (s,t) (f,g) ==> (P s <=> Q t))
        ==> (!s t. homeomorphism (s,t) (f,g)
                   ==> (locally P s <=> locally Q t))`;;

let HOMEOMORPHIC_LOCALLY = `!P Q. (!s:real^N->bool t:real^M->bool. s homeomorphic t ==> (P s <=> Q t))
         ==> (!s t. s homeomorphic t ==> (locally P s <=> locally Q t))`;;

let LOCALLY_TRANSLATION = `!P:(real^N->bool)->bool.
        (!a s. P (IMAGE (\x. a + x) s) <=> P s)
        ==> (!a s. locally P (IMAGE (\x. a + x) s) <=> locally P s)`;;

let LOCALLY_INJECTIVE_LINEAR_IMAGE = `!P:(real^N->bool)->bool Q:(real^M->bool)->bool.
        (!f s. linear f /\ (!x y. f x = f y ==> x = y)
               ==> (P (IMAGE f s) <=> Q s))
        ==>  (!f s. linear f /\ (!x y. f x = f y ==> x = y)
                    ==> (locally P (IMAGE f s) <=> locally Q s))`;;

let LOCALLY_OPEN_MAP_IMAGE = `!P Q f:real^M->real^N s.
        f continuous_on s /\
        (!t. open_in (subtopology euclidean s) t
              ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t)) /\
        (!t. t SUBSET s /\ P t ==> Q(IMAGE f t)) /\
        locally P s
        ==> locally Q (IMAGE f s)`;;

let LOCALLY_FINE_COVERING_COMPACT = `!P s:real^N->bool e.
        compact s /\ locally P s /\ &0 < e
        ==> ?f. FINITE f /\ UNIONS f = s /\
                !c. c IN f ==> P c /\ bounded c /\ diameter c <= e`;;

let LOCALLY_COUNTABLE = `!s:real^N->bool. locally COUNTABLE s <=> COUNTABLE s`;;

let LOCALLY_CONSTANT = `!f:real^N->A s.
        connected s
        ==> (locally (\u. ?c. !x. x IN u ==> f x = c) s <=>
             ?c. !x. x IN s ==> f x = c)`;;

let LOCALLY_CONTINUOUS_ON = `(!f:real^M->real^N s.
        locally (\u. f continuous_on u) s <=> f continuous_on s)`
and LOCALLY_CONTINUOUS_ON_ALT = `(!f:real^M->real^N s.
        f continuous_on s <=>
        !x. x IN s ==> ?u v. open_in (subtopology euclidean s) u /\
                             x IN u /\ u SUBSET v /\ f continuous_on v)`
and LOCALLY_CONTINUOUS_ON_EXPLICIT = `(!f:real^M->real^N s.
        f continuous_on s <=>
        !x. x IN s ==> ?u. open_in (subtopology euclidean s) u /\
                           x IN u /\ f continuous_on u)`;;

let LOCALLY_TO_COMPACTLY = `!P s c:real^N->bool.
        (!t u. t SUBSET u /\ u SUBSET s /\ P u ==> P t) /\
        (!f. FINITE f /\ (!t. t IN f ==> P t /\ t SUBSET s)
             ==> P(UNIONS f)) /\
        locally P s /\ compact c /\ c SUBSET s
        ==> P c`;;

(* ------------------------------------------------------------------------- *)
(* Local compactness.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_COMPACT_SPACE_SUBTOPOLOGY_EUCLIDEAN = `!s:real^N->bool.
        locally_compact_space(subtopology euclidean s) <=>
        locally compact s`;;

let LOCALLY_COMPACT = `!s:real^N->bool.
        locally compact s <=>
        !x. x IN s ==> ?u v. x IN u /\ u SUBSET v /\ v SUBSET s /\
                             open_in (subtopology euclidean s) u /\
                             compact v`;;

let LOCALLY_COMPACT_ALT = `!s:real^N->bool.
        locally compact s <=>
        !x. x IN s
            ==> ?u. x IN u /\
                    open_in (subtopology euclidean s) u /\
                    compact(closure u) /\ closure u SUBSET s`;;

let LOCALLY_COMPACT_INTER_CBALL = `!s:real^N->bool.
        locally compact s <=>
        !x. x IN s ==> ?e. &0 < e /\ closed(cball(x,e) INTER s)`;;

let LOCALLY_COMPACT_INTER_CBALLS = `!s:real^N->bool.
      locally compact s <=>
      !x. x IN s ==> ?e. &0 < e /\ !d. d <= e ==> closed(cball(x,d) INTER s)`;;

let LOCALLY_COMPACT_COMPACT = `!s:real^N->bool.
        locally compact s <=>
        !k. k SUBSET s /\ compact k
            ==> ?u v. k SUBSET u /\
                      u SUBSET v /\
                      v SUBSET s /\
                      open_in (subtopology euclidean s) u /\
                      compact v`;;

let LOCALLY_COMPACT_COMPACT_ALT = `!s:real^N->bool.
        locally compact s <=>
        !k. k SUBSET s /\ compact k
            ==> ?u. k SUBSET u /\
                    open_in (subtopology euclidean s) u /\
                    compact(closure u) /\ closure u SUBSET s`;;

let LOCALLY_COMPACT_COMPACT_SUBOPEN = `!s:real^N->bool.
        locally compact s <=>
        !k t. k SUBSET s /\ compact k /\ open t /\ k SUBSET t
              ==> ?u v. k SUBSET u /\ u SUBSET v /\ u SUBSET t /\ v SUBSET s /\
                        open_in (subtopology euclidean s) u /\
                        compact v`;;

let OPEN_IMP_LOCALLY_COMPACT = `!s:real^N->bool. open s ==> locally compact s`;;

let CLOSED_IMP_LOCALLY_COMPACT = `!s:real^N->bool. closed s ==> locally compact s`;;

let IS_INTERVAL_LOCALLY_COMPACT_INTERVAL = `!s:real^N->bool.
        is_interval s ==> locally (\k. ?a b. k = interval[a,b]) s`;;

let IS_INTERVAL_IMP_LOCALLY_COMPACT = `!s:real^N->bool. is_interval s ==> locally compact s`;;

let LOCALLY_COMPACT_UNIV = `locally compact (:real^N)`;;

let LOCALLY_COMPACT_INTER = `!s t:real^N->bool.
        locally compact s /\ locally compact t
        ==> locally compact (s INTER t)`;;

let LOCALLY_COMPACT_OPEN_IN = `!s t:real^N->bool.
        open_in (subtopology euclidean s) t /\ locally compact s
        ==> locally compact t`;;

let LOCALLY_COMPACT_CLOSED_IN = `!s t:real^N->bool.
        closed_in (subtopology euclidean s) t /\ locally compact s
        ==> locally compact t`;;

let LOCALLY_COMPACT_DELETE = `!s a:real^N. locally compact s ==> locally compact (s DELETE a)`;;

let SIGMA_COMPACT = `!s:real^N->bool.
        locally compact s
        ==> ?f. COUNTABLE f /\ (!t. t IN f ==> compact t) /\ UNIONS f = s`;;

let HOMEOMORPHIC_LOCAL_COMPACTNESS = `!s t:real^N->bool.
        s homeomorphic t ==> (locally compact s <=> locally compact t)`;;

let LOCALLY_COMPACT_TRANSLATION_EQ = `!a:real^N s. locally compact (IMAGE (\x. a + x) s) <=>
                locally compact s`;;

add_translation_invariants [LOCALLY_COMPACT_TRANSLATION_EQ];;

let LOCALLY_COMPACT_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally compact (IMAGE f s) <=> locally compact s)`;;

add_linear_invariants [LOCALLY_COMPACT_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_LOCAL_COMPACTNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (locally compact (IMAGE f k) <=> locally compact k)`;;

let LOCALLY_CLOSED = `!s:real^N->bool. locally closed s <=> locally compact s`;;

let LOCALLY_COMPACT_CLOSED_UNION = `!s t u:real^N->bool.
        locally compact s /\ locally compact t /\
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t
        ==> locally compact (s UNION t)`;;

let LOCALLY_COMPACT_OPEN_UNIONS = `!f:(real^N->bool)->bool u.
        (!c. c IN f ==> locally compact c) /\
        (!c. c IN f ==> open_in (subtopology euclidean u) c)
        ==> locally compact (UNIONS f)`;;

let LOCALLY_COMPACT_OPEN_UNION = `!s t:real^N->bool u.
        locally compact s /\ locally compact t /\
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t
        ==> locally compact (s UNION t)`;;

let LOCALLY_COMPACT_PCROSS = `!s:real^M->bool t:real^N->bool.
        locally compact s /\ locally compact t
        ==> locally compact (s PCROSS t)`;;

let LOCALLY_COMPACT_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        locally compact (s PCROSS t) <=>
        s = {} \/ t = {} \/ locally compact s /\ locally compact t`;;

let OPEN_IN_LOCALLY_COMPACT = `!s t:real^N->bool.
        locally compact s
        ==> (open_in (subtopology euclidean s) t <=>
             t SUBSET s /\
             !k. compact k /\ k SUBSET s
                 ==> open_in (subtopology euclidean k) (k INTER t))`;;

let LOCALLY_COMPACT_PROPER_IMAGE_EQ = `!f:real^M->real^N s.
        f continuous_on s /\
        (!k. k SUBSET (IMAGE f s) /\ compact k
             ==> compact {x | x IN s /\ f x IN k})
        ==> (locally compact s <=> locally compact (IMAGE f s))`;;

let LOCALLY_COMPACT_PROPER_IMAGE = `!f:real^M->real^N s.
        f continuous_on s /\
        (!k. k SUBSET (IMAGE f s) /\ compact k
             ==> compact {x | x IN s /\ f x IN k}) /\
        locally compact s
        ==> locally compact (IMAGE f s)`;;

let LOCALLY_COMPACT_PROPER_CONTINUOUS_PREIMAGE = `!f:real^M->real^N s t c.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!k. k SUBSET t /\ compact k
             ==> compact {x | x IN s /\ f x IN k}) /\
        locally compact c /\ c SUBSET t
        ==> locally compact {x | x IN s /\ f x IN c}`;;

let MUMFORD_LEMMA = `!f:real^M->real^N s t y.
        f continuous_on s /\ IMAGE f s SUBSET t /\ locally compact s /\
        y IN t /\ compact {x | x IN s /\ f x = y}
        ==> ?u v. open_in (subtopology euclidean s) u /\
                  open_in (subtopology euclidean t) v /\
                  {x | x IN s /\ f x = y} SUBSET u /\ y IN v /\
                  IMAGE f u SUBSET v /\
                  (!k. k SUBSET v /\ compact k
                       ==> compact {x | x IN u /\ f x IN k})`;;

let LOCALLY_EQ_COMPACTLY = `!P s:real^N->bool.
        (!t u. t SUBSET u /\ u SUBSET s /\ P u ==> P t) /\
        (!f. FINITE f /\ (!t. t IN f ==> P t /\ t SUBSET s)
             ==> P(UNIONS f)) /\
        locally compact s
        ==> (locally P s <=> !c. compact c /\ c SUBSET s ==> P c)`;;

(* ------------------------------------------------------------------------- *)
(* Locally compact sets are closed in an open set and are homeomorphic       *)
(* to an absolutely closed set if we have one more dimension to play with.   *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_COMPACT_OPEN_INTER_CLOSURE = `!s:real^N->bool. locally compact s ==> ?t. open t /\ s = t INTER closure s`;;

let LOCALLY_COMPACT_CLOSED_IN_OPEN = `!s:real^N->bool.
    locally compact s ==> ?t. open t /\ closed_in (subtopology euclidean t) s`;;

let LOCALLY_COMPACT_HOMEOMORPHISM_PROJECTION_CLOSED = `!s:real^M->bool.
        locally compact s
        ==> ?t:real^(M,N)finite_sum->bool f.
                closed t /\ homeomorphism (s,t) (f,fstcart)`;;

let LOCALLY_COMPACT_CLOSED_INTER_OPEN = `!s:real^N->bool.
        locally compact s <=> ?t u. closed t /\ open u /\ s = t INTER u`;;

let LOCALLY_COMPACT_CLOSED_DIFF = `!s:real^N->bool.
        locally compact s <=> ?t u. closed t /\ closed u /\ t DIFF u = s`;;

let LOCALLY_COMPACT_CLOSURE_DIFF = `!s:real^N->bool. locally compact s <=> closed(closure s DIFF s)`;;

(* ------------------------------------------------------------------------- *)
(* F_sigma and G_delta sets.                                                 *)
(* ------------------------------------------------------------------------- *)

let gdelta = new_definition
 `gdelta(s:real^N->bool) <=> (COUNTABLE INTERSECTION_OF open) s`;;

let fsigma = new_definition
 `fsigma (s:real^N->bool) <=> (COUNTABLE UNION_OF closed) s`;;

let FSIGMA_IN_EUCLIDEAN = `fsigma_in euclidean = fsigma`;;

let GDELTA_IN_EUCLIDEAN = `gdelta_in euclidean = gdelta`;;

let FSIGMA_UNIONS_COMPACT = `!s:real^N->bool. fsigma s <=> (COUNTABLE UNION_OF compact) s`;;

let GDELTA_COMPLEMENT = `!s. gdelta((:real^N) DIFF s) <=> fsigma s`;;

let FSIGMA_ASCENDING = `!s:real^N->bool.
        fsigma s <=>
        ?c. (!n. compact(c n)) /\ (!n. c n SUBSET c(SUC n)) /\
            UNIONS {c n | n IN (:num)} = s`;;

let FSIGMA_COMPLEMENT = `!s. fsigma((:real^N) DIFF s) <=> gdelta s`;;

let GDELTA_DESCENDING = `!s:real^N->bool.
        gdelta s <=>
        ?u. (!n. open(u n)) /\ (!n. u(SUC n) SUBSET u n) /\
            INTERS {u n | n IN (:num)} = s`;;

let GDELTA_TRANSLATION = `!a:real^N s. gdelta (IMAGE (\x. a + x) s) <=> gdelta s`;;

let FSIGMA_TRANSLATION = `!a:real^N s. fsigma (IMAGE (\x. a + x) s) <=> fsigma s`;;

add_translation_invariants [GDELTA_TRANSLATION; FSIGMA_TRANSLATION];;

let GDELTA_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (gdelta(IMAGE f s) <=> gdelta s)`;;

let FSIGMA_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (fsigma(IMAGE f s) <=> fsigma s)`;;

add_linear_invariants [GDELTA_LINEAR_IMAGE; FSIGMA_LINEAR_IMAGE];;

let FSIGMA_LOCALLY_COMPACT = `!s:real^N->bool. locally compact s ==> fsigma s`;;

let OPEN_IMP_FSIGMA = `!s:real^N->bool. open s ==> fsigma s`;;

let CLOSED_IMP_FSIGMA = `!s:real^N->bool. closed s ==> fsigma s`;;

let CLOSED_IMP_GDELTA = `!s:real^N->bool. closed s ==> gdelta s`;;

let FSIGMA_SING = `!x:real^N. fsigma {x}`;;

let GDELTA_SING = `!x:real^N. gdelta {x}`;;

let OPEN_IMP_GDELTA = `!s:real^N->bool. open s ==> gdelta s`;;

let GDELTA_EMPTY = `gdelta {}`;;

let FSIGMA_EMPTY = `fsigma {}`;;

let GDELTA_UNIV = `gdelta (:real^N)`;;

let FSIGMA_UNIV = `fsigma (:real^N)`;;

let GDELTA_INTERS = `!g:(real^N->bool)->bool.
        COUNTABLE g /\ (!u. u IN g ==> gdelta u) ==> gdelta(INTERS g)`;;

let GDELTA_INTER = `!s t:real^N->bool. gdelta s /\ gdelta t ==> gdelta(s INTER t)`;;

let GDELTA_DIFF = `!s t:real^N->bool. gdelta s /\ fsigma t ==> gdelta(s DIFF t)`;;

let FSIGMA_UNIONS = `!g:(real^N->bool)->bool.
        COUNTABLE g /\ (!u. u IN g ==> fsigma u) ==> fsigma(UNIONS g)`;;

let COUNTABLE_IMP_FSIGMA = `!s:real^N->bool. COUNTABLE s ==> fsigma s`;;

let FSIGMA_UNION = `!s t:real^N->bool. fsigma s /\ fsigma t ==> fsigma(s UNION t)`;;

let GDELTA_UNION = `!s t:real^N->bool. gdelta s /\ gdelta t ==> gdelta(s UNION t)`;;

let FSIGMA_INTER = `!s t:real^N->bool. fsigma s /\ fsigma t ==> fsigma(s INTER t)`;;

let FSIGMA_DIFF = `!s t:real^N->bool. fsigma s /\ gdelta t ==> fsigma(s DIFF t)`;;

let GDELTA_UNIONS = `!g:(real^N->bool)->bool.
        FINITE g /\ (!u. u IN g ==> gdelta u) ==> gdelta(UNIONS g)`;;

let FSIGMA_INTERS = `!g:(real^N->bool)->bool.
        FINITE g /\ (!u. u IN g ==> fsigma u) ==> fsigma(INTERS g)`;;

let OPEN_IN_FSIGMA = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ fsigma t ==> fsigma s`;;

let CLOSED_IN_FSIGMA = `!s t:real^N->bool.
        closed_in (subtopology euclidean t) s /\ fsigma t ==> fsigma s`;;

let OPEN_IN_GDELTA = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ gdelta t ==> gdelta s`;;

let CLOSED_IN_GDELTA = `!s t:real^N->bool.
        closed_in (subtopology euclidean t) s /\ gdelta t ==> gdelta s`;;

let GDELTA_LOCALLY_COMPACT = `!s:real^N->bool. locally compact s ==> gdelta s`;;

let FSIGMA_CONTINUOUS_IMAGE = `!f:real^M->real^N s. f continuous_on s /\ fsigma s ==> fsigma (IMAGE f s)`;;

let HOMEOMORPHIC_FSIGMANESS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (fsigma s <=> fsigma t)`;;

let HOMEOMORPHISM_FSIGMANESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (fsigma(IMAGE f k) <=> fsigma k)`;;

let FSIGMA_FSIGMA_PROJECTION = `!s:real^M->bool t:real^(M,N)finite_sum->bool.
      IMAGE fstcart t SUBSET s /\ fsigma t
      ==> fsigma {y | ?x. x IN s /\ pastecart x y IN t}`;;

let CONTINUOUS_FSIGMA_PREIMAGE = `!f:real^M->real^N s t.
        f continuous_on s /\ fsigma s /\ fsigma t
        ==> fsigma {x | x IN s /\ f x IN t}`;;

let CONTINUOUS_GDELTA_PREIMAGE = `!f:real^M->real^N s t.
        f continuous_on s /\ gdelta s /\ gdelta t
        ==> gdelta {x | x IN s /\ f x IN t}`;;

let FSIGMA_PROPER_PREIMAGE = `!f:real^M->real^N s t.
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k})
        ==> (!k. k SUBSET t /\ fsigma k ==> fsigma {x | x IN s /\ f x IN k})`;;

let FSIGMA_PCROSS = `!s:real^M->bool t:real^N->bool.
        fsigma s /\ fsigma t ==> fsigma(s PCROSS t)`;;

let FSIGMA_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        fsigma(s PCROSS t) <=> s = {} \/ t = {} \/ fsigma s /\ fsigma t`;;

let GDELTA_PCROSS = `!s:real^M->bool t:real^N->bool.
        gdelta s /\ gdelta t ==> gdelta(s PCROSS t)`;;

let GDELTA_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        gdelta(s PCROSS t) <=> s = {} \/ t = {} \/ gdelta s /\ gdelta t`;;

let CARD_EQ_GDELTA_SETS = `{s:real^N->bool | gdelta s} =_c (:real)`;;

let CARD_EQ_FSIGMA_SETS = `{s:real^N->bool | fsigma s} =_c (:real)`;;

let GDELTA_POINTS_OF_CONVERGENCE_WITHIN = `!f:real^M->real^N s. gdelta {x | ?l. (f --> l) (at x within s)}`;;

let GDELTA_POINTS_OF_CONVERGENCE_AT = `!f:real^M->real^N. gdelta {x | ?l. (f --> l) (at x)}`;;

let GDELTA_POINTS_OF_CONTINUITY_WITHIN = `!f:real^M->real^N s.
        ?t. gdelta t /\
            {x | x IN s /\ f continuous (at x within s)} = s INTER t`;;

let GDELTA_POINTS_OF_CONTINUITY = `!f:real^M->real^N. gdelta {x | f continuous at x}`;;

(* ------------------------------------------------------------------------- *)
(* Lavrentiev extension theorem.                                             *)
(* ------------------------------------------------------------------------- *)

let LAVRENTIEV = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ gdelta t
        ==> ?u g. gdelta u /\ s SUBSET u /\ u SUBSET closure s /\
                  g continuous_on u /\ IMAGE g u SUBSET t /\
                  !x. x IN s ==> g x = f x`;;

let LAVRENTIEV_HOMEOMORPHISM = `!f:real^M->real^N f' s s'.
        homeomorphism (s,s') (f,f')
        ==> ?u u' g g'.
                gdelta u /\ s SUBSET u /\ u SUBSET closure s /\
                gdelta u' /\ s' SUBSET u' /\ u' SUBSET closure s' /\
                (!x. x IN s ==> g x = f x) /\ (!x. x IN s' ==> g' x = f' x) /\
                homeomorphism (u,u') (g,g')`;;

let LAVRENTIEV_HOMEOMORPHISM_SELF = `!f:real^N->real^N f' s.
        homeomorphism (s,s) (f,f')
        ==> ?u g g'.
                gdelta u /\ s SUBSET u /\ u SUBSET closure s /\
                (!x. x IN s ==> g x = f x /\ g' x = f' x) /\
                homeomorphism (u,u) (g,g')`;;

let HOMEOMORPHIC_GDELTANESS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (gdelta s <=> gdelta t)`;;

let HOMEOMORPHISM_GDELTANESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (gdelta(IMAGE f k) <=> gdelta k)`;;

(* ------------------------------------------------------------------------- *)
(* Effective countability of closed or open chains.                          *)
(* ------------------------------------------------------------------------- *)

let EFFECTIVELY_COUNTABLE_CLOPEN_IN_CHAIN_UNIONS = `!f v:real^N->bool.
        (!s. s IN f ==> closed_in (subtopology euclidean v) s \/
                        open_in (subtopology euclidean v) s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?f'. COUNTABLE f' /\ f' SUBSET f /\ UNIONS f' = UNIONS f`;;

let COUNTABLE_ASCENDING_CLOPEN_IN_CHAIN = `!f v:real^N->bool.
        ~(f = {}) /\
        (!s. s IN f ==> closed_in (subtopology euclidean v) s \/
                        open_in (subtopology euclidean v) s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?u. (!n. u(n) IN f) /\ (!n. u(n) SUBSET u(SUC n)) /\
                UNIONS {u n | n IN (:num)} = UNIONS f`;;

let EFFECTIVELY_COUNTABLE_CLOPEN_IN_CHAIN_INTERS = `!f v:real^N->bool.
        (!s. s IN f ==> closed_in (subtopology euclidean v) s \/
                        open_in (subtopology euclidean v) s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?f'. COUNTABLE f' /\ f' SUBSET f /\ INTERS f' = INTERS f`;;

let COUNTABLE_DESCENDING_CLOPEN_IN_CHAIN = `!f v:real^N->bool.
        ~(f = {}) /\
        (!s. s IN f ==> closed_in (subtopology euclidean v) s \/
                        open_in (subtopology euclidean v) s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?u. (!n. u(n) IN f) /\ (!n. u(SUC n) SUBSET u n) /\
                INTERS {u n | n IN (:num)} = INTERS f`;;

let EFFECTIVELY_COUNTABLE_CLOPEN_CHAIN_UNIONS = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> closed s \/ open s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?f'. COUNTABLE f' /\ f' SUBSET f /\ UNIONS f' = UNIONS f`;;

let COUNTABLE_ASCENDING_CLOPEN_CHAIN = `!f:(real^N->bool)->bool.
        ~(f = {}) /\
        (!s. s IN f ==> closed s \/ open s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?u. (!n. u(n) IN f) /\ (!n. u(n) SUBSET u(SUC n)) /\
                UNIONS {u n | n IN (:num)} = UNIONS f`;;

let EFFECTIVELY_COUNTABLE_CLOPEN_CHAIN_INTERS = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> closed s \/ open s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?f'. COUNTABLE f' /\ f' SUBSET f /\ INTERS f' = INTERS f`;;

let COUNTABLE_DESCENDING_CLOPEN_CHAIN = `!f:(real^N->bool)->bool.
        ~(f = {}) /\
        (!s. s IN f ==> closed s \/ open s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> ?u. (!n. u(n) IN f) /\ (!n. u(SUC n) SUBSET u n) /\
                INTERS {u n | n IN (:num)} = INTERS f`;;

let FSIGMA_UNIONS_CLOPEN_CHAIN = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> closed s \/ open s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> fsigma(UNIONS f)`;;

let GDELTA_INTERS_CLOPEN_CHAIN = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> closed s \/ open s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> gdelta(INTERS f)`;;

let CANTOR_BAIRE_STATIONARY_PRINCIPLE = `!f:A->real^N->bool v w.
        woset w /\ ~COUNTABLE {(x,y) | w x y} /\
        (!v. v inseg w /\ ~(v = w) ==> COUNTABLE {(x,y) | v x y}) /\
        (!i. i IN fld w ==> closed_in (subtopology euclidean v) (f i) \/
                            open_in (subtopology euclidean v) (f i)) /\
        (!i j. w i j ==> f j SUBSET f i)
        ==> ?k. k IN fld w /\ !i. w k i ==> f i = f k`;;

(* ------------------------------------------------------------------------- *)
(* Very basics about Borel sets.                                             *)
(* ------------------------------------------------------------------------- *)

let borel_RULES,borel_INDUCT,borel_CASES = new_inductive_definition
 `(!s. open s ==> borel s) /\
  (!s. borel s ==> borel((:real^N) DIFF s)) /\
  (!u. COUNTABLE u /\ (!s. s IN u ==> borel s) ==> borel(UNIONS u))`;;

let BOREL_IN_EUCLIDEAN = `borel_in euclidean = borel:(real^N->bool)->bool`;;

let BOREL_INDUCT_COMPACT = `!P. (!s. compact s ==> P s) /\
       (!s. P s ==> P ((:real^N) DIFF s)) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (UNIONS u))
       ==> !a. borel a ==> P a`;;

let BOREL_INDUCT_COMPACT_DIFF = `!P. (!s. compact s ==> P s) /\
       (!s t. P s /\ P t ==> P(s DIFF t)) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (UNIONS u))
       ==> !a:real^N->bool. borel a ==> P a`;;

let BOREL_INDUCT_COMPACT_ALT = `!P. (!s. compact s ==> P s) /\
       (!s. P s ==> P((:real^N) DIFF s)) /\
       (!u. COUNTABLE u /\ ~(u = {}) /\ (!s. s IN u ==> P s) ==> P(INTERS u))
       ==> !a:real^N->bool. borel a ==> P a`;;

let BOREL_INDUCT_UNIONS_INTERS = `!P. (!s. open s ==> P s) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (UNIONS u)) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (INTERS u))
       ==> !a:real^N->bool. borel a ==> P a`;;

let BOREL_INDUCT_COMPACT_UNIONS_INTERS = `!P. (!s. compact s ==> P s) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (UNIONS u)) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (INTERS u))
       ==> !a:real^N->bool. borel a ==> P a`;;

let BOREL_INDUCT_CLOSED_UNIONS_INTERS = `!P. (!s. closed s ==> P s) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (UNIONS u)) /\
       (!u. COUNTABLE u /\ (!s. s IN u ==> P s) ==> P (INTERS u))
       ==> !a:real^N->bool. borel a ==> P a`;;

let OPEN_IMP_BOREL = `!s:real^N->bool. open s ==> borel s`;;

let BOREL_COMPLEMENT = `!s. borel((:real^N) DIFF s) <=> borel s`;;

let BOREL_UNIONS = `!u. COUNTABLE u /\ (!s:real^N->bool. s IN u ==> borel s)
       ==> borel(UNIONS u)`;;

let BOREL_INTERS = `!u. COUNTABLE u /\ (!s:real^N->bool. s IN u ==> borel s)
       ==> borel(INTERS u)`;;

let BOREL_EMPTY = `borel {}`;;

let BOREL_UNIV = `borel(:real^N)`;;

let BOREL_UNION = `!s t:real^N->bool. borel s /\ borel t ==> borel(s UNION t)`;;

let BOREL_INTER = `!s t:real^N->bool. borel s /\ borel t ==> borel(s INTER t)`;;

let BOREL_DIFF = `!s t:real^N->bool. borel s /\ borel t ==> borel(s DIFF t)`;;

let CLOSED_IMP_BOREL = `!s:real^N->bool. closed s ==> borel s`;;

let COMPACT_IMP_BOREL = `!s:real^N->bool. compact s ==> borel s`;;

let FSIGMA_IMP_BOREL = `!s:real^N->bool. fsigma s ==> borel s`;;

let GDELTA_IMP_BOREL = `!s:real^N->bool. gdelta s ==> borel s`;;

let LOCALLY_COMPACT_IMP_BOREL = `!s:real^N->bool. locally compact s ==> borel s`;;

let OPEN_IN_BOREL = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ borel t ==> borel s`;;

let CLOSED_IN_BOREL = `!s t:real^N->bool.
        closed_in (subtopology euclidean t) s /\ borel t ==> borel s`;;

let CONTINUOUS_BOREL_PREIMAGE = `!f:real^M->real^N s t.
        f continuous_on s /\ borel s /\ borel t
        ==> borel {x | x IN s /\ f x IN t}`;;

let HOMEOMORPHIC_BORELNESS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (borel s <=> borel t)`;;

let BOREL_TRANSLATION = `!a:real^N s. borel (IMAGE (\x. a + x) s) <=> borel s`;;

add_translation_invariants [BOREL_TRANSLATION];;

let BOREL_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (borel(IMAGE f s) <=> borel s)`;;

add_linear_invariants [BOREL_LINEAR_IMAGE];;

let HOMEOMORPHISM_BORELNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (borel(IMAGE f k) <=> borel k)`;;

let BOREL_PCROSS = `!s:real^M->bool t:real^N->bool. borel s /\ borel t ==> borel(s PCROSS t)`;;

let BOREL_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        borel(s PCROSS t) <=> s = {} \/ t = {} \/ borel s /\ borel t`;;

let LAVRENTIEV_BOREL = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ borel t
        ==> ?u g. borel u /\ s SUBSET u /\ u SUBSET closure s /\
                  g continuous_on u /\ IMAGE g u SUBSET t /\
                  !x. x IN s ==> g x = f x`;;

(* ------------------------------------------------------------------------- *)
(* Baire functions. We only define these for finite indices, since I can't   *)
(* imagine ever using any indexed by higher ordinals. But this means         *)
(* that "borel_measurable" is strictly stronger than "baire n for some n".   *)
(* ------------------------------------------------------------------------- *)

let baire = define
 `(baire 0 s (f:real^M->real^N) <=> f continuous_on s) /\
  (baire (SUC n) s f <=>
        ?g. (!k. baire n s (g k)) /\
            (!x. x IN s ==> ((\k. g k x) --> f x) sequentially))`;;

let BAIRE_MONO = `!f:real^M->real^N s m n. baire m s f /\ m <= n ==> baire n s f`;;

let CONTINUOUS_ON_IMP_BAIRE = `!f:real^M->real^N s n. f continuous_on s ==> baire n s f`;;

let BAIRE_SUBSET = `!f:real^M->real^N s t n.
        baire n s f /\ t SUBSET s ==> baire n t f`;;

let BAIRE_EQ = `!f:real^M->real^N g s n.
        (!x. x IN s ==> f x = g x) /\ baire n s f
        ==> baire n s g`;;

let BAIRE_CONST = `!s:real^M->bool n a:real^N. baire n s (\x. a)`;;

let BAIRE_PASTECART = `!f:real^M->real^N g:real^M->real^P s n.
        baire n s f /\ baire n s g
        ==> baire n s (\x. pastecart (f x) (g x))`;;

let BAIRE_COMPOSE_CONTINUOUS = `!f:real^M->real^N g:real^N->real^P s k.
        f continuous_on s /\ baire k (IMAGE f s) g ==> baire k s (g o f)`;;

let BAIRE_CONTINUOUS_COMPOSE_UNIV = `!f:real^N->real^P g:real^M->real^N s n.
        f continuous_on (:real^N) /\ baire n s g
        ==> baire n s (f o g)`;;

let BAIRE_CMUL = `!f:real^M->real^N s c n.
        baire n s f ==> baire n s (\x. c % f x)`;;

let BAIRE_BILINEAR = `!bop:real^N->real^P->real^Q f g s:real^M->bool n.
        bilinear bop /\ baire n s f /\ baire n s g
        ==> baire n s (\x. bop (f x) (g x))`;;

let BAIRE_ADD = `!f g:real^M->real^N s n.
        baire n s f /\ baire n s g ==> baire n s (\x. f x + g x)`;;

let BAIRE_SUB = `!f g:real^M->real^N s n.
        baire n s f /\ baire n s g
        ==> baire n s (\x. f x - g x)`;;

let BAIRE_MUL = `!f g:real^M->real^N s n.
        baire n s (\x. lift(f x)) /\ baire n s g
        ==> baire n s (\x. f x % g x)`;;

let BAIRE_VSUM = `!f:A->real^M->real^N s t n.
        FINITE t /\ (!i. i IN t ==> baire n s (f i))
        ==> baire n s (\x. vsum t (\i. f i x))`;;

let BAIRE_PRODUCT = `!f:A->real^N->real s t n.
        FINITE t /\ (!i. i IN t ==> baire n s (\x. lift(f i x)))
        ==> baire n s (\x. lift(product t (\i. f i x)))`;;

let BAIRE_NORM = `!f:real^M->real^N s n. baire n s f ==> baire n s (\x. lift(norm(f x)))`;;

let BAIRE_MAX = `!f g:real^N->real s n.
        baire n s (\x. lift(f x)) /\ baire n s (\x. lift(g x))
        ==> baire n s (\x. lift(max (f x) (g x)))`;;

let BAIRE_MIN = `!f g:real^N->real s n.
        baire n s (\x. lift(f x)) /\ baire n s (\x. lift(g x))
        ==> baire n s (\x. lift(min (f x) (g x)))`;;

let BAIRE_COMPONENTWISE = `!f:real^M->real^N s n.
        baire n s f <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> baire n s (\x. lift(f x$i))`;;

let BAIRE_UNIFORM_LIMIT = `!f g:real^M->real^N s k.
        eventually (\n. baire k s (f n)) sequentially /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN s ==> norm(f n x - g x) < e)
                            sequentially)
        ==> baire k s g`;;

let BAIRE_UNIFORM_APPROXIMATION = `!f:real^M->real^N s k.
        baire k s f <=>
        !e. &0 < e ==> ?g. baire k s g /\ !x. x IN s ==> norm(g x - f x) < e`;;

let FSIGMA_BAIRE1_PREIMAGE_OPEN_GEN = `!f:real^M->real^N g s t u.
        IMAGE f s SUBSET t /\
        open_in (subtopology euclidean t) u /\
        (!n. (g n) continuous_on s) /\
        (!x. x IN s ==> ((\n. g n x) --> f x) sequentially)
        ==> ?c. COUNTABLE c /\
                (!t. t IN c ==> closed_in (subtopology euclidean s) t) /\
                UNIONS c = {x | x IN s /\ f(x) IN u}`;;

let FSIGMA_BAIRE1_PREIMAGE_OPEN = `!f:real^M->real^N s u.
        fsigma s /\ open u /\ baire 1 s f
        ==> fsigma {x | x IN s /\ f(x) IN u}`;;

let GDELTA_BAIRE1_PREIMAGE_CLOSED = `!f:real^M->real^N s c.
        gdelta s /\ closed c /\ baire 1 s f
        ==> gdelta {x | x IN s /\ f(x) IN c}`;;

(* ------------------------------------------------------------------------- *)
(* Delta_n sets (defined via "baire" on indicator, not a special constant).  *)
(* We can then express Sigma_n and Pi_n using "COUNTABLE UNION_OF ..." and   *)
(* "COUNTABLE INTERSECTION_OF ...". While a bit verbose, and breaking down   *)
(* for the 0 case, it is adequate for use in occasional lemmas.              *)
(* ------------------------------------------------------------------------- *)

let BAIRE_INDICATOR_EMPTY = `!n. baire n u (indicator {})`;;

let BAIRE_INDICATOR_UNIV = `!n. baire n u (indicator (:real^N))`;;

let BAIRE_INDICATOR_REFL = `!u:real^N->bool n. baire n u (indicator u)`;;

let BAIRE_INDICATOR_COMPLEMENT = `!u s:real^N->bool n.
        baire n u (indicator(u DIFF s)) <=>
        baire n u (indicator s)`;;

let BAIRE_INDICATOR_COMPLEMENT_UNIV = `!u s n.
        baire n u (indicator((:real^N) DIFF s)) <=> baire n u (indicator s)`;;

let BAIRE_INDICATOR_INTER = `!u s t:real^N->bool n.
        baire n u (indicator s) /\ baire n u (indicator t)
        ==> baire n u (indicator(s INTER t))`;;

let BAIRE_INDICATOR_UNION = `!u s t:real^N->bool n.
        baire n u (indicator s) /\ baire n u (indicator t)
        ==> baire n u (indicator(s UNION t))`;;

let BAIRE_INDICATOR_DIFF = `!u s t:real^N->bool n.
        baire n u (indicator s) /\ baire n u (indicator t)
        ==> baire n u (indicator(s DIFF t))`;;

let BAIRE_INDICATOR_INTERS = `!f n. FINITE f /\
         (!s. s IN f ==> baire n u (indicator s))
         ==> baire n u (indicator(INTERS f))`;;

let BAIRE_INDICATOR_UNIONS = `!f n. FINITE f /\
         (!s. s IN f ==> baire n u (indicator s))
         ==> baire n u (indicator(UNIONS f))`;;

let BAIRE0_INDICATOR = `!s. baire 0 (:real^N) (indicator s) <=> s = {} \/ s = (:real^N)`;;

let COUNTABLE_UNION_OF_BAIRE0_INDICATOR = `!s. (COUNTABLE UNION_OF baire 0 (:real^N) o indicator) s <=>
       s = {} \/ s = (:real^N)`;;

let COUNTABLE_INTERSECTION_OF_BAIRE0_INDICATOR = `!s. (COUNTABLE INTERSECTION_OF baire 0 (:real^N) o indicator) s <=>
       s = {} \/ s = (:real^N)`;;

let BAIRE1_INDICATOR = `!s. baire 1 (:real^N) (indicator s) <=> fsigma s /\ gdelta s`;;

let GDELTA_BAIRE = `!s. gdelta s <=>
       (COUNTABLE INTERSECTION_OF baire 1 (:real^N) o indicator) s`;;

let FSIGMA_BAIRE = `!s. fsigma s <=> (COUNTABLE UNION_OF baire 1 (:real^N) o indicator) s`;;

let CLOSED_IMP_BAIRE1_INDICATOR = `!s. closed s ==> baire 1 (:real^N) (indicator s)`;;

let OPEN_IMP_BAIRE1_INDICATOR = `!s. open s ==> baire 1 (:real^N) (indicator s)`;;

let BAIRE_INDICATOR_CONTINUOUS_PREIMAGE = `!f:real^M->real^N s t u k.
        baire k u (indicator t) /\ f continuous_on s /\ IMAGE f s SUBSET u
        ==> baire k s (indicator {x | x IN s /\ f x IN t})`;;

let BAIRE_INDICATOR_CONTINUOUS_PREIMAGE_UNIV = `!f s k. baire k (:real^N) (indicator s) /\ f continuous_on (:real^M)
           ==> baire k (:real^M) (indicator {x | f x IN s})`;;

let BAIRE_INDICATOR_TRANSLATION = `!a s k. baire k (:real^N) (indicator (IMAGE (\x. a + x) s)) <=>
           baire k (:real^N) (indicator s)`;;

let BAIRE_INDICATOR_INJECTIVE_LINEAR_IMAGE = `!f s k.
        1 <= k /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> (baire k (:real^N) (indicator (IMAGE f s)) <=>
             baire k (:real^M) (indicator s))`;;

let BAIRE_INDICATOR_BIJECTIVE_LINEAR_IMAGE = `!f s k.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (baire k (:real^N) (indicator (IMAGE f s)) <=>
             baire k (:real^M) (indicator s))`;;

add_translation_invariants [BAIRE_INDICATOR_TRANSLATION];;

add_linear_invariants [BAIRE_INDICATOR_BIJECTIVE_LINEAR_IMAGE];;

let COUNTABLE_UNION_OF_BAIRE_INDICATOR_TRANSLATION = `!a s k. (COUNTABLE UNION_OF baire k (:real^N) o indicator)
           (IMAGE (\x. a + x) s) <=>
           (COUNTABLE UNION_OF baire k (:real^N) o indicator) s`;;

add_translation_invariants [COUNTABLE_UNION_OF_BAIRE_INDICATOR_TRANSLATION];;

let COUNTABLE_INTERSECTION_OF_BAIRE_INDICATOR_TRANSLATION = `!a s k. (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator)
           (IMAGE (\x. a + x) s) <=>
           (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) s`;;

add_translation_invariants
  [COUNTABLE_INTERSECTION_OF_BAIRE_INDICATOR_TRANSLATION];;

let COUNTABLE_UNION_OF_BAIRE_INDICATOR_BIJECTIVE_LINEAR_IMAGE = `!f s k.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ((COUNTABLE UNION_OF baire k (:real^N) o indicator) (IMAGE f s) <=>
             (COUNTABLE UNION_OF baire k (:real^M) o indicator) s)`;;

add_linear_invariants
 [COUNTABLE_UNION_OF_BAIRE_INDICATOR_BIJECTIVE_LINEAR_IMAGE];;

let COUNTABLE_INTERSECTION_OF_BAIRE_INDICATOR_BIJECTIVE_LINEAR_IMAGE = `!f s k.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ((COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator)
             (IMAGE f s) <=>
             (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator) s)`;;

add_linear_invariants
 [COUNTABLE_INTERSECTION_OF_BAIRE_INDICATOR_BIJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* The reduction theorem for Sigma_n sets and consequences.                  *)
(* ------------------------------------------------------------------------- *)

let FSIGMA_REDUCTION_GEN_ALT = `!s:num->real^N->bool k.
     (!n. (COUNTABLE UNION_OF baire k (:real^N) o indicator) (s n))
     ==> ?t. (!n. (COUNTABLE UNION_OF baire k (:real^N) o indicator) (t n)) /\
             (!n. t n SUBSET s n) /\
             pairwise (\m n. DISJOINT (t m) (t n)) (:num) /\
             UNIONS {t n | n IN (:num)} = UNIONS {s n | n IN (:num)}`;;

let FSIGMA_REDUCTION_GEN_2 = `!s t k.
       (COUNTABLE UNION_OF baire k (:real^N) o indicator) s /\
       (COUNTABLE UNION_OF baire k (:real^N) o indicator) t
       ==> ?s' t'. (COUNTABLE UNION_OF baire k (:real^N) o indicator) s' /\
                   (COUNTABLE UNION_OF baire k (:real^N) o indicator) t' /\
                   s' SUBSET s /\ t' SUBSET t /\ DISJOINT s' t' /\
                   s' UNION t' = s UNION t`;;

let FSIGMA_REDUCTION = `!s:num->real^N->bool.
        (!n. fsigma(s n))
        ==> ?t. (!n. fsigma(t n)) /\
                (!n. t n SUBSET s n) /\
                pairwise (\m n. DISJOINT (t m) (t n)) (:num) /\
                UNIONS {t n | n IN (:num)} = UNIONS {s n | n IN (:num)}`;;

let BAIRE_INDICATOR_SUC,BAIRE_INDICATOR_DELTA,FGSIGMA_BAIRE_PREIMAGE_OPEN_ALT,
    FSIGMA_REDUCTION_GEN,GDELTA_SEPARATION_GEN =
  let clemma = MESON[BAIRE_INDICATOR_COMPLEMENT; o_THM]
     `(baire k (:real^N) o indicator) ((:real^N) DIFF s) =
      (baire k (:real^N) o indicator) s` in
  let slemma = `!s t k.
      (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) s /\
      (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) t /\
      DISJOINT s t
      ==> ?u. (COUNTABLE UNION_OF baire k (:real^N) o indicator) u /\
              (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) u /\
              s SUBSET u /\ DISJOINT u t` in
  let BAIRE_INDICATOR_SUC = `(!s n. 1 <= n
            ==> ((COUNTABLE UNION_OF
                  COUNTABLE INTERSECTION_OF baire n (:real^N) o indicator) s /\
                 (COUNTABLE INTERSECTION_OF
                  COUNTABLE UNION_OF baire n (:real^N) o indicator) s <=>
                 baire (n + 1) (:real^N) (indicator s)))`
and BAIRE_INDICATOR_DELTA = `(!s n. (COUNTABLE UNION_OF baire n (:real^N) o indicator) s /\
            (COUNTABLE INTERSECTION_OF baire n (:real^N) o indicator) s <=>
            baire n (:real^N) (indicator s))`
and FGSIGMA_BAIRE_PREIMAGE_OPEN_ALT = `(!f u n. 1 <= n /\ baire (n + 1) (:real^N) (f:real^N->real^1) /\ open u
              ==> (COUNTABLE UNION_OF
                   COUNTABLE INTERSECTION_OF baire n (:real^N) o indicator)
                  {x | f x IN u})` in
  let FSIGMA_REDUCTION_GEN = `!s k. (!n. (COUNTABLE UNION_OF baire k (:real^N) o indicator) (s n)) /\
           UNIONS {s n | n IN (:num)} = (:real^N)
           ==> ?t. (!n. baire k (:real^N) (indicator(t n))) /\
                   (!n. t n SUBSET s n) /\
                   pairwise (\m n. DISJOINT (t m) (t n)) (:num) /\
                   UNIONS {t n | n IN (:num)} = (:real^N)` in
  let GDELTA_SEPARATION_GEN = `!s t k.
          (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) s /\
          (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) t /\
          DISJOINT s t
          ==> ?u. baire k (:real^N) (indicator u) /\
                  s SUBSET u /\ DISJOINT u t` in
  BAIRE_INDICATOR_SUC,BAIRE_INDICATOR_DELTA,FGSIGMA_BAIRE_PREIMAGE_OPEN_ALT,
  FSIGMA_REDUCTION_GEN,GDELTA_SEPARATION_GEN;;

let COUNTABLE_UNION_OF_BAIRE_INDICATOR = `!s k. (COUNTABLE UNION_OF baire k (:real^N) o indicator) s
         ==> baire (k + 1) (:real^N) (indicator s)`;;

let COUNTABLE_INTERSECTION_OF_BAIRE_INDICATOR = `!s k. (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) s
         ==> baire (k + 1) (:real^N) (indicator s)`;;

let GDELTA_SEPARATION = `!s t:real^N->bool.
        gdelta s /\ gdelta t /\ DISJOINT s t
        ==> ?u. fsigma u /\ gdelta u /\ s SUBSET u /\ DISJOINT u t`;;

(* ------------------------------------------------------------------------- *)
(* More on Baire functions including the full preimage characterization.     *)
(* ------------------------------------------------------------------------- *)

let FSIGMA_BAIRE_PREIMAGE_OPEN_GEN = `!f:real^M->real^N s u k.
        1 <= k /\ baire k s f /\ open u
        ==> ?t. (COUNTABLE UNION_OF baire k (:real^M) o indicator) t /\
                {x | x IN s /\ f(x) IN u} = s INTER t`;;

let FSIGMA_BAIRE_PREIMAGE_OPEN = `!f:real^M->real^N s u k.
        1 <= k /\ baire k s f /\
        (COUNTABLE UNION_OF baire k (:real^M) o indicator) s /\ open u
        ==> (COUNTABLE UNION_OF baire k (:real^M) o indicator)
            {x | x IN s /\ f(x) IN u}`;;

let GDELTA_BAIRE_PREIMAGE_CLOSED_GEN = `!f:real^M->real^N s u k.
        1 <= k /\ baire k s f /\ closed u
        ==> ?t. (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator) t /\
                {x | x IN s /\ f(x) IN u} = s INTER t`;;

let GDELTA_BAIRE_PREIMAGE_CLOSED = `!f:real^M->real^N s u k.
        1 <= k /\ baire k s f /\
        (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator) s /\ closed u
        ==> (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator)
            {x | x IN s /\ f(x) IN u}`;;

let BAIRE_EQ_FSIGMA_PREIMAGE_OPEN_GEN = `!f:real^M->real^N s k.
      1 <= k
      ==> (baire k s f <=>
           !u. open u
               ==> ?t. (COUNTABLE UNION_OF baire k (:real^M) o indicator) t /\
                       {x | x IN s /\ f(x) IN u} = s INTER t)`;;

let BAIRE_EQ_FSIGMA_PREIMAGE_OPEN = `!f:real^M->real^N s k.
      1 <= k /\ (COUNTABLE UNION_OF baire k (:real^M) o indicator) s
      ==> (baire k s f <=>
           !u. open u
               ==> (COUNTABLE UNION_OF baire k (:real^M) o indicator)
                   {x | x IN s /\ f(x) IN u})`;;

let BAIRE_EQ_FSIGMA_PREIMAGE_ALT = `!f:real^M->real^N s k.
      1 <= k
      ==> ((COUNTABLE UNION_OF baire k (:real^M) o indicator) s /\
            baire k s f <=>
            !u. open u
                ==> (COUNTABLE UNION_OF baire k (:real^M) o indicator)
                    {x | x IN s /\ f(x) IN u})`;;

let BAIRE_EQ_GDELTA_PREIMAGE_CLOSED_GEN = `!f:real^M->real^N s k.
      1 <= k
      ==> (baire k s f <=>
           !u. closed u
               ==> ?t. (COUNTABLE INTERSECTION_OF
                        baire k (:real^M) o indicator) t /\
                       {x | x IN s /\ f(x) IN u} = s INTER t)`;;

let BAIRE_EQ_GDELTA_PREIMAGE_CLOSED = `!f:real^M->real^N s k.
      1 <= k /\ (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator) s
      ==> (baire k s f <=>
           !u. closed u
               ==> (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator)
                   {x | x IN s /\ f(x) IN u})`;;

let BAIRE_EQ_GDELTA_PREIMAGE_ALT = `!f:real^M->real^N s k.
      1 <= k
      ==> ((COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator) s /\
            baire k s f <=>
            !u. closed u
                ==> (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator)
                    {x | x IN s /\ f(x) IN u})`;;

let COUNTABLE_DISCONTINUITIES_IMP_BAIRE1 = `!f:real^M->real^N s.
        COUNTABLE {x | x IN s /\ ~(f continuous (at x within s))}
        ==> baire 1 s f`;;

let COUNTABLE_NEITHER_SIDED_LIMITS_IMP_BAIRE1_GEN = `!f:real^1->real^N s.
      COUNTABLE {x | x IN s /\
                     ~(?l. (f --> l)
                           (at x within {t | t IN s /\ drop t <= drop x})) /\
                     ~(?l. (f --> l)
                           (at x within {t | t IN s /\ drop x <= drop t}))}
      ==> baire 1 s f`;;

let COUNTABLE_NEITHER_SIDED_LIMITS_IMP_BAIRE1 = `!f:real^1->real^N s.
      COUNTABLE {x | x IN s /\
                     ~(?l. (f --> l) (at x within {t | drop t <= drop x})) /\
                     ~(?l. (f --> l) (at x within {t | drop x <= drop t}))}
      ==> baire 1 s f`;;

(* ------------------------------------------------------------------------- *)
(* Extending Baire functions and more miscellaneous properties.              *)
(* ------------------------------------------------------------------------- *)

let BAIRE_EXTENSION = `!f:real^M->real^N s k.
        baire k s f /\
        (COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator) s
        ==> ?g. baire k (:real^M) g /\ !x. x IN s ==> g x = f x`;;

let BAIRE_LAVRENTIEV = `!f:real^M->real^N s k.
        baire k s f
        ==> ?u g. (COUNTABLE INTERSECTION_OF
                    baire (k + 1) (:real^M) o indicator) u /\
                  s SUBSET u /\
                  u SUBSET closure s /\
                  baire k u g /\
                  !x. x IN s ==> g x = f x`;;

let BAIRE_CASES = `!f:real^M->real^N g s t k.
        baire k s f /\ baire k (t DIFF s) g /\ baire k (:real^M) (indicator s)
        ==>  baire k t (\x. if x IN s then f x else g x)`;;

let BAIRE_RESTRICT = `!f:real^M->real^N s k.
        baire k s f /\ baire k (:real^M) (indicator s)
        ==> baire k (:real^M) (\x. if x IN s then f x else vec 0)`;;

let BAIRE_FSIGMA_PREIMAGE_GEN = `!f:real^M->real^N s u m n.
        baire m s f /\ (COUNTABLE UNION_OF baire n (:real^N) o indicator) u
        ==> ?c. (COUNTABLE UNION_OF baire (m + n) (:real^M) o indicator) c /\
                {x | x IN s /\ f x IN u} = s INTER c`;;

let BAIRE_COMPOSE = `!m n f:real^M->real^N g:real^N->real^P s.
        baire m s f /\ baire n (IMAGE f s) g
        ==> baire (m + n) s (g o f)`;;

let BAIRE_CONTINUOUS_COMPOSE = `!f:real^M->real^N g:real^N->real^P s k.
        baire k s f /\ g continuous_on IMAGE f s ==> baire k s (g o f)`;;

let HOMEOMORPHIC_BAIRE_INDICATOR = `!s t k. s homeomorphic t /\ 1 <= k
        ==> (baire k (:real^M) (indicator s) <=>
             baire k (:real^N) (indicator t))`;;

let HOMEOMORPHIC_COUNTABLE_UNION_OF_BAIRE_INDICATOR = `!s t k. s homeomorphic t /\ 1 <= k
        ==> ((COUNTABLE UNION_OF baire k (:real^M) o indicator) s <=>
             (COUNTABLE UNION_OF baire k (:real^N) o indicator) t)`;;

let HOMEOMORPHIC_COUNTABLE_INTERSECTION_OF_BAIRE_INDICATOR = `!s t k. s homeomorphic t /\ 1 <= k
        ==> ((COUNTABLE INTERSECTION_OF baire k (:real^M) o indicator) s <=>
             (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) t)`;;

let FSIGMA_DISJOINT_GEN = `!k s. (COUNTABLE UNION_OF baire k (:real^N) o indicator) s <=>
         ((COUNTABLE INTER pairwise DISJOINT) UNION_OF
          baire k (:real^N) o indicator) s`;;

let FSIGMA_GDELTA_GEN = `!k s. 1 <= k
         ==> ((COUNTABLE UNION_OF baire (k + 1) (:real^N) o indicator) s <=>
              (COUNTABLE UNION_OF
               COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) s)`;;

let GDELTA_FSIGMA_GEN = `!k s.
     1 <= k
     ==> ((COUNTABLE INTERSECTION_OF baire (k + 1) (:real^N) o indicator) s <=>
          (COUNTABLE INTERSECTION_OF
           COUNTABLE UNION_OF baire k (:real^N) o indicator) s)`;;

let FSIGMA_GDELTA_DISJOINT = `!k s. 1 <= k
         ==> ((COUNTABLE UNION_OF baire (k + 1) (:real^N) o indicator) s <=>
              ((COUNTABLE INTER pairwise DISJOINT) UNION_OF
               COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) s)`;;

let LOCALLY_BAIRE = `(!f:real^M->real^N s k. locally (\u. baire k u f) s <=> baire k s f)`
and LOCALLY_BAIRE_ALT = `(!f:real^M->real^N s k.
        baire k s f <=>
        (!x. x IN s ==> ?u v. open_in (subtopology euclidean s) u /\
                              x IN u /\ u SUBSET v /\ baire k v f))`
and LOCALLY_BAIRE_EXPLICIT = `(!f:real^M->real^N s k.
        baire k s f <=>
        (!x. x IN s ==> ?u. open_in (subtopology euclidean s) u /\
                            x IN u /\ baire k u f))`;;

let FSIGMA_LOCALLY_GEN = `!u s k. 1 <= k /\ (COUNTABLE UNION_OF baire k u o indicator) s
           ==> ?t. (COUNTABLE UNION_OF baire k (:real^N) o indicator) t /\
                   u INTER t = u INTER s`;;

let FSIGMA_LOCALLY_EQ = `!u s k. 1 <= k
           ==> (s SUBSET u /\ (COUNTABLE UNION_OF baire k u o indicator) s <=>
                ?t. (COUNTABLE UNION_OF baire k (:real^N) o indicator) t /\
                    u INTER t = s)`;;

let FSIGMA_LOCALLY_TRANS = `!s t u:real^N->bool k.
        1 <= k /\ s SUBSET t /\ t SUBSET u /\
        (COUNTABLE UNION_OF baire k t o indicator) s /\
        (COUNTABLE UNION_OF baire k u o indicator) t
        ==> (COUNTABLE UNION_OF baire k u o indicator) s`;;

let GDELTA_LOCALLY_GEN = `!u s k.
        1 <= k /\ (COUNTABLE INTERSECTION_OF baire k u o indicator) s
        ==> ?t. (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) t /\
                u INTER t = u INTER s`;;

let GDELTA_LOCALLY_EQ = `!u s k.
    1 <= k
    ==> (s SUBSET u /\
         (COUNTABLE INTERSECTION_OF baire k u o indicator) s <=>
         ?t. (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) t /\
             u INTER t = s)`;;

let GDELTA_LOCALLY_TRANS = `!s t u:real^N->bool k.
        1 <= k /\ s SUBSET t /\ t SUBSET u /\
        (COUNTABLE INTERSECTION_OF baire k t o indicator) s /\
        (COUNTABLE INTERSECTION_OF baire k u o indicator) t
        ==> (COUNTABLE INTERSECTION_OF baire k u o indicator) s`;;

let BAIRE_INDICATOR_LOCALLY = `!u s k.
        1 <= k /\ baire k u (indicator s) /\
        (COUNTABLE INTERSECTION_OF baire k (:real^N) o indicator) u
        ==> ?t. baire k (:real^N) (indicator t) /\ u INTER t = u INTER s`;;

(* ------------------------------------------------------------------------- *)
(* Basics on Borel measurability. We define it as "Baire function" and later *)
(* prove (BOREL_MEASURABLE_PREIMAGE_BOREL) that it is equivalent to another  *)
(* natural definition when the domain is a Borel set.                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("borel_measurable_on",(12,"right"));;

let borel_measurable_RULES,borel_measurable_INDUCT,borel_measurable_CASES =
 new_inductive_definition
 `(!f:real^M->real^N s. f continuous_on s ==> f borel_measurable_on s) /\
  (!(f:num->real^M->real^N) g s.
        (!n. f n borel_measurable_on s) /\
        (!x. x IN s ==> ((\n. f n x) --> g x) sequentially)
        ==> g borel_measurable_on s)`;;

let CONTINUOUS_IMP_BOREL_MEASURABLE_ON = `!f:real^M->real^N s. f continuous_on s ==> f borel_measurable_on s`;;

let BAIRE_IMP_BOREL_MEASURABLE = `!f:real^M->real^N s n. baire n s f ==> f borel_measurable_on s`;;

let BOREL_MEASURABLE_ON_SUBSET = `!f:real^M->real^N s t.
        f borel_measurable_on s /\ t SUBSET s ==> f borel_measurable_on t`;;

let BOREL_MEASURABLE_EQ = `!f:real^M->real^N g s.
        (!x. x IN s ==> f x = g x) /\ f borel_measurable_on s
        ==> g borel_measurable_on s`;;

let BOREL_MEASURABLE_PASTECART = `!f:real^M->real^N g:real^M->real^P s.
        f borel_measurable_on s /\ g borel_measurable_on s
        ==> (\x. pastecart (f x) (g x)) borel_measurable_on s`;;

let BOREL_MEASURABLE_CONTINUOUS_COMPOSE = `!f:real^N->real^P g:real^M->real^N s.
        f continuous_on (:real^N) /\ g borel_measurable_on s
        ==> (f o g) borel_measurable_on s`;;

let BOREL_MEASURABLE_CMUL = `!f:real^M->real^N s c.
        f borel_measurable_on s ==> (\x. c % f x) borel_measurable_on s`;;

let BOREL_MEASURABLE_BILINEAR = `!bop:real^N->real^P->real^Q f g s:real^M->bool.
        bilinear bop /\ f borel_measurable_on s /\ g borel_measurable_on s
        ==> (\x. bop (f x) (g x)) borel_measurable_on s`;;

let BOREL_MEASURABLE_ADD = `!f g:real^M->real^N s.
        f borel_measurable_on s /\ g borel_measurable_on s
        ==> (\x. f x + g x) borel_measurable_on s`;;

let BOREL_MEASURABLE_SUB = `!f g:real^M->real^N s.
        f borel_measurable_on s /\ g borel_measurable_on s
        ==> (\x. f x - g x) borel_measurable_on s`;;

let BOREL_MEASURABLE_CONST = `!s:real^M->bool c:real^N. (\x. c) borel_measurable_on s`;;

let BOREL_MEASURABLE_VSUM = `!f:A->real^M->real^N s t.
        FINITE t /\ (!i. i IN t ==> f i borel_measurable_on s)
        ==> (\x. vsum t (\i. f i x)) borel_measurable_on s`;;

let BOREL_MEASURABLE_MUL = `!f g:real^M->real^N s.
        (\x. lift(f x)) borel_measurable_on s /\ g borel_measurable_on s
        ==> (\x. f x % g x) borel_measurable_on s`;;

let BOREL_MEASURABLE_NORM = `!f:real^M->real^N s.
        f borel_measurable_on s
        ==> (\x. lift(norm(f x))) borel_measurable_on s`;;

let BOREL_MEASURABLE_MAX = `!f g:real^N->real s.
        (\x. lift(f x)) borel_measurable_on s /\
        (\x. lift(g x)) borel_measurable_on s
        ==> (\x. lift(max (f x) (g x))) borel_measurable_on s`;;

let BOREL_MEASURABLE_MIN = `!f g:real^N->real s.
        (\x. lift(f x)) borel_measurable_on s /\
        (\x. lift(g x)) borel_measurable_on s
        ==> (\x. lift(min (f x) (g x))) borel_measurable_on s`;;

let BOREL_MEASURABLE_PRODUCT = `!f:A->real^N->real s t.
        FINITE t /\ (!i. i IN t ==> (\x. lift(f i x)) borel_measurable_on s)
        ==> (\x. lift(product t (\i. f i x))) borel_measurable_on s`;;

let BOREL_MEASURABLE_COMPONENTWISE = `!f:real^M->real^N s.
        f borel_measurable_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f x$i)) borel_measurable_on s`;;

let BOREL_BOREL_MEASURABLE_PREIMAGE = `!f:real^M->real^N s t.
        f borel_measurable_on s /\ borel s /\ borel t
        ==> borel {x | x IN s /\ f x IN t}`;;

let BOREL_MEASURABLE_INDICATOR = `!s. indicator s borel_measurable_on (:real^N) <=> borel s`;;

let BOREL_MEASURABLE_ON_INDICATOR = `!s t:real^N->bool.
        borel s
        ==> (indicator t borel_measurable_on s <=> borel(s INTER t))`;;

let BOREL_MEASURABLE_PREIMAGE_BOREL = `!f:real^M->real^N s.
        borel s /\ f borel_measurable_on s <=>
        !t. borel t ==> borel {x | x IN s /\ f x IN t}`;;

let BOREL_MEASURABLE_EXTENSION = `!f:real^M->real^N s t.
        f borel_measurable_on s /\ IMAGE f s SUBSET t /\ borel t
        ==> ?g. g borel_measurable_on (:real^M) /\
                (~(t = {}) ==> IMAGE g (:real^M) SUBSET t) /\
                (!x. x IN s ==> g x = f x)`;;

let BOREL_MEASURABLE_COMPOSE = `!f:real^M->real^N g:real^N->real^P s.
        f borel_measurable_on s /\ g borel_measurable_on IMAGE f s
         ==> g o f borel_measurable_on s`;;

let BOREL_MEASURABLE_CASES = `!f g:real^M->real^N s t.
        f borel_measurable_on s /\ g borel_measurable_on (t DIFF s) /\ borel s
        ==> (\x. if x IN s then f x else g x) borel_measurable_on t`;;

let BOREL_MEASURABLE_RESTRICT = `!f:real^M->real^N s.
        f borel_measurable_on s /\ borel s
        ==> (\x. if x IN s then f x else vec 0) borel_measurable_on (:real^M)`;;

(* ------------------------------------------------------------------------- *)
(* The relation with the general borel_measurable is slightly subtler        *)
(* ------------------------------------------------------------------------- *)

let BOREL_MEASURABLE_MAP_EUCLIDEAN_SUBTOPOLOGY = `!(f:real^M->real^N) s.
        borel s
        ==> (borel_measurable_map(subtopology euclidean s,euclidean) f <=>
             f borel_measurable_on s)`;;

let BOREL_MEASURABLE_MAP_EUCLIDEAN = `!(f:real^M->real^N).
        borel_measurable_map(euclidean,euclidean) f <=> 
        f borel_measurable_on (:real^M)`;;

(* ------------------------------------------------------------------------- *)
(* Analytic sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let analytic = new_definition
 `analytic s = suslin compact s`;;

let COMPACT_IMP_ANALYTIC = `!s. compact s ==> analytic s`;;

let ANALYTIC_EMPTY = `analytic({}:real^N->bool)`;;

let ANALYTIC_UNIONS = `!u:(real^N->bool)->bool.
        COUNTABLE u /\ (!s. s IN u ==> analytic s) ==> analytic(UNIONS u)`;;

let ANALYTIC_UNION = `!s t:real^N->bool. analytic s /\ analytic t ==> analytic(s UNION t)`;;

let LOCALLY_COMPACT_IMP_ANALYTIC = `!s:real^N->bool. locally compact s ==> analytic s`;;

let OPEN_IMP_ANALYTIC = `!s:real^N->bool. open s ==> analytic s`;;

let CLOSED_IMP_ANALYTIC = `!s:real^N->bool. closed s ==> analytic s`;;

let ANALYTIC_UNIV = `analytic(:real^N)`;;

let ANALYTIC_INTERS = `!u:(real^N->bool)->bool.
        COUNTABLE u /\ (!s. s IN u ==> analytic s) ==> analytic(INTERS u)`;;

let ANALYTIC_INTER = `!s t:real^N->bool. analytic s /\ analytic t ==> analytic(s INTER t)`;;

let OPEN_IN_ANALYTIC = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ analytic t ==> analytic s`;;

let CLOSED_IN_ANALYTIC = `!s t:real^N->bool.
        closed_in (subtopology euclidean t) s /\ analytic t ==> analytic s`;;

let BOREL_IMP_ANALYTIC = `!s:real^N->bool. borel s ==> analytic s`;;

let GDELTA_IMP_ANALYTIC = `!s:real^N->bool. gdelta s ==> analytic s`;;

let FSIGMA_IMP_ANALYTIC = `!s:real^N->bool. fsigma s ==> analytic s`;;

let ANALYTIC_PCROSS = `!s:real^M->bool t:real^N->bool.
        analytic s /\ analytic t ==> analytic(s PCROSS t)`;;

let ANALYTIC_BOREL_MEASURABLE_PREIMAGE = `!f:real^M->real^N s t.
        f borel_measurable_on s /\ analytic s /\ analytic t
        ==> analytic {x | x IN s /\ f x IN t}`;;

let ANALYTIC_CONTINUOUS_PREIMAGE = `!f:real^M->real^N s t.
        f continuous_on s /\ analytic s /\ analytic t
        ==> analytic {x | x IN s /\ f x IN t}`;;

let ANALYTIC_CONTINUOUS_IMAGE = `!f:real^M->real^N s.
        analytic s /\ f continuous_on s ==> analytic(IMAGE f s)`;;

let HOMEOMORPHIC_ANALYTICITY = `!s:real^M->bool t:real^N->bool.
     s homeomorphic t ==> (analytic s <=> analytic t)`;;

let ANALYTIC_TRANSLATION = `!a:real^N s. analytic (IMAGE (\x. a + x) s) <=> analytic s`;;

add_translation_invariants [ANALYTIC_TRANSLATION];;

let ANALYTIC_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (analytic(IMAGE f s) <=> analytic s)`;;

add_linear_invariants [ANALYTIC_LINEAR_IMAGE];;

let ANALYTIC_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        analytic(s PCROSS t) <=> s = {} \/ t = {} \/ analytic s /\ analytic t`;;

let ANALYTIC_BOREL_MEASURABLE_IMAGE = `!f:real^M->real^N s.
        analytic s /\ f borel_measurable_on s ==> analytic(IMAGE f s)`;;

let CARD_EQ_ANALYTIC_SETS = `{s:real^N->bool | analytic s} =_c (:real)`;;

let CARD_EQ_BOREL_SETS = `{s:real^N->bool | borel s} =_c (:real)`;;

let CARD_EQ_BOREL_MEASURABLE_FUNCTIONS = `{f:real^M->real^N | f borel_measurable_on UNIV} =_c (:real)`;;

let CARD_EQ_BAIRE_FUNCTIONS = `{f:real^M->real^N | baire k UNIV f} =_c (:real)`;;

(* ------------------------------------------------------------------------- *)
(* Some Borel variants of the measurability of the Banach indicatrix.        *)
(* ------------------------------------------------------------------------- *)

let FSIGMA_PREIMAGE_CARD_GE = `!f:real^M->real^N s n.
        f continuous_on s /\ fsigma s
        ==> fsigma {y | FINITE {x | x IN s /\ f x = y}
                        ==> n <= CARD {x | x IN s /\ f x = y}}`;;

let GDELTA_PREIMAGE_CARD_LE = `!f:real^M->real^N s n.
        f continuous_on s /\ fsigma s
        ==> gdelta {y | FINITE {x | x IN s /\ f x = y} /\
                        CARD {x | x IN s /\ f x = y} <= n}`;;

let BOREL_PREIMAGE_HAS_SIZE = `!f:real^M->real^N s n.
        f continuous_on s /\ fsigma s
        ==> borel {y | {x | x IN s /\ f x = y} HAS_SIZE n}`;;

let BOREL_PREIMAGE_FINITE = `!f:real^M->real^N s.
        f continuous_on s /\ fsigma s
        ==> borel {y | FINITE {x | x IN s /\ f x = y}}`;;

let BOREL_PREIMAGE_INFINITE = `!f:real^M->real^N s.
        f continuous_on s /\ fsigma s
        ==> borel {y | INFINITE {x | x IN s /\ f x = y}}`;;

(* ------------------------------------------------------------------------- *)
(* Forms of the Baire property of dense sets.                                *)
(* ------------------------------------------------------------------------- *)

let BAIRE = `!g s:real^N->bool.
        locally compact s /\ COUNTABLE g /\
        (!t. t IN g
             ==> open_in (subtopology euclidean s) t /\ s SUBSET closure t)
        ==> s SUBSET closure(INTERS g)`;;

let BAIRE_ALT = `!g s:real^N->bool.
        locally compact s /\ ~(s = {}) /\ COUNTABLE g /\ UNIONS g = s
        ==> ?t u. t IN g /\ open_in (subtopology euclidean s) u /\ ~(u = {}) /\
                  u SUBSET (closure t)`;;

let NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED_IN = `!u g:(real^N->bool)->bool.
        locally compact u /\
        COUNTABLE g /\
        (!s. s IN g
             ==> closed_in (subtopology euclidean u) s /\
                 (subtopology euclidean u) interior_of s = {})
        ==> (subtopology euclidean u) interior_of (UNIONS g) = {}`;;

let NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED = `!g:(real^N->bool)->bool.
        COUNTABLE g /\ (!s. s IN g ==> closed s /\ interior s = {})
        ==> interior(UNIONS g) = {}`;;

let NOWHERE_DENSE_COUNTABLE_UNIONS = `!g:(real^N->bool)->bool.
        COUNTABLE g /\ (!s. s IN g ==> interior(closure s) = {})
        ==> interior(UNIONS g) = {}`;;

(* ------------------------------------------------------------------------- *)
(* Some cute Baire applications from Silverman's paper in AMM vol. 102       *)
(* "Intervals Contained in Arithmetic Combinations of Sets". These are       *)
(* somewhat like the Steinhaus/Piccard theorems. There are other variants.   *)
(* ------------------------------------------------------------------------- *)

let SILVERMAN_STEINHAUSLIKE = `!s t:real^N->bool.
        gdelta s /\ gdelta t /\
        (:real^N) SUBSET closure s /\ (:real^N) SUBSET closure t
        ==> {x + y | x IN s /\ y IN t} = (:real^N)`;;

let DENSE_GDELTA_IMP_LARGE = `!s:real^N->bool.
        gdelta s /\ (:real^N) SUBSET closure s
        ==> s =_c (:real)`;;

let NOT_GDELTA_DENSE_COUNTABLE = `!s. COUNTABLE s /\ closure s = (:real^N) ==> ~(gdelta s)`;;

(* ------------------------------------------------------------------------- *)
(* Finding borel subsets where a function is injective (mainly looking       *)
(* ahead to measure theory but maybe of some independent interest).          *)
(* ------------------------------------------------------------------------- *)

let GDELTA_CONTINUOUS_FUNCTION_MINIMA = `!f:real^M->real^N s.
        f continuous_on s /\ compact s
        ==> gdelta {x | x IN s /\
                        !y. y IN s /\ f x = f y
                            ==> x = y \/
                                ?k. 1 <= k /\ k <= dimindex(:M) /\
                                    (!i. 1 <= i /\ i < k
                                         ==> x$i <= y$i) /\
                                    x$k < y$k}`;;

let GDELTA_DOMAIN_OF_INJECTIVITY_CONTINUOUS = `!f:real^M->real^N s.
        f continuous_on s /\ compact s
        ==> ?t. gdelta t /\ t SUBSET s /\
                IMAGE f t = IMAGE f s /\
                !x y. x IN t /\ y IN t /\ f x = f y ==> x = y`;;

let BOREL_DOMAIN_OF_INJECTIVITY_CONTINUOUS_GEN = `!f:real^M->real^N u.
        COUNTABLE u /\
        (!k. k IN u ==> compact k /\ f continuous_on k)
        ==> ?t. borel t /\ t SUBSET UNIONS u /\
                IMAGE f t = IMAGE f (UNIONS u) /\
                !x y. x IN t /\ y IN t /\ f x = f y ==> x = y`;;

let BOREL_DOMAIN_OF_INJECTIVITY_CONTINUOUS = `!f:real^M->real^N s.
        f continuous_on s /\ fsigma s
        ==> ?t. borel t /\ t SUBSET s /\
                IMAGE f t = IMAGE f s /\
                !x y. x IN t /\ y IN t /\ f x = f y ==> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Partitions of unity subordinate to open coverings. Since subsets of       *)
(* Euclidean space are paracompact, there's a locally finite refinement.     *)
(* ------------------------------------------------------------------------- *)

let PARACOMPACT_SPACE_EUCLIDEAN = `paracompact_space(euclidean:(real^N)topology)`;;

let PARACOMPACT_SPACE_EUCLIDEAN_SUBTOPOLOGY = `!s:real^N->bool. paracompact_space(subtopology euclidean s)`;;

let PARACOMPACT = `!s c. (!t:real^N->bool. t IN c ==> open t) /\ s SUBSET UNIONS c
         ==> ?c'. s SUBSET UNIONS c' /\
                  (!u. u IN c'
                       ==> open u /\ ?t. t IN c /\ u SUBSET t) /\
                  (!x. x IN s
                       ==> ?v. open v /\ x IN v /\
                               FINITE {u | u IN c' /\ ~(u INTER v = {})})`;;

let SUBORDINATE_PARTITION_OF_UNITY = `!c s:real^N->bool.
        s SUBSET UNIONS c /\ (!u. u IN c ==> open u)
        ==> ?f:(real^N->bool)->real^N->real.
                (!u. u IN c
                     ==> (lift o f u) continuous_on s /\
                         !x. x IN s ==> &0 <= f u x) /\
                (!x u. u IN c /\ x IN s /\ ~(x IN u)
                       ==> f u x = &0) /\
                (!x. x IN s ==> sum c (\u. f u x) = &1) /\
                (!x. x IN s
                     ==> ?n. open n /\ x IN n /\
                             FINITE {u | u IN c /\
                                     ~(!x. x IN n
                                           ==> f u x = &0)})`;;
