(* ========================================================================= *)
(* Paths, connectedness, homotopy, simple connectedness & contractibility.   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Multivariate/homology.ml";;
needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Paths and arcs.                                                           *)
(* ------------------------------------------------------------------------- *)

let path = new_definition
 `!g:real^1->real^N. path g <=> g continuous_on interval[vec 0,vec 1]`;;

let pathstart = new_definition
 `pathstart (g:real^1->real^N) = g(vec 0)`;;

let pathfinish = new_definition
 `pathfinish (g:real^1->real^N) = g(vec 1)`;;

let path_image = new_definition
 `path_image (g:real^1->real^N) = IMAGE g (interval[vec 0,vec 1])`;;

let reversepath = new_definition
 `reversepath (g:real^1->real^N) = \x. g(vec 1 - x)`;;

let joinpaths = new_definition
 `(g1 ++ g2) = \x. if drop x <= &1 / &2 then g1(&2 % x)
                   else g2(&2 % x - vec 1)`;;

let simple_path = new_definition
 `simple_path (g:real^1->real^N) <=>
        path g /\
        !x y. x IN interval[vec 0,vec 1] /\
              y IN interval[vec 0,vec 1] /\
              g x = g y
              ==> x = y \/ x = vec 0 /\ y = vec 1 \/ x = vec 1 /\ y = vec 0`;;

let arc = new_definition
 `arc (g:real^1->real^N) <=>
        path g /\
        !x y. x IN interval [vec 0,vec 1] /\
              y IN interval [vec 0,vec 1] /\
              g x = g y
              ==> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Relate to topological general case.                                       *)
(* ------------------------------------------------------------------------- *)

let PATH_IN_EUCLIDEAN = `!s:real^N->bool g.
        path_in (subtopology euclidean s) g <=>
        path (g o drop) /\ path_image (g o drop) SUBSET s`;;

let PATH_EUCLIDEAN = `!s g:real^1->real^N.
        path g /\ path_image g SUBSET s <=>
        path_in (subtopology euclidean s) (g o lift)`;;

let PATH_PATH_IN = `!g:real^1->real^N. path g <=> path_in euclidean (g o lift)`;;

(* ------------------------------------------------------------------------- *)
(* Invariance theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let PATH_EQ = `!p q. (!t. t IN interval[vec 0,vec 1] ==> p t = q t) /\ path p
         ==> path q`;;

let PATH_CONTINUOUS_IMAGE = `!f:real^M->real^N g.
     path g /\ f continuous_on path_image g ==> path(f o g)`;;

let PATH_TRANSLATION_EQ = `!a g:real^1->real^N. path((\x. a + x) o g) <=> path g`;;

add_translation_invariants [PATH_TRANSLATION_EQ];;

let PATH_LINEAR_IMAGE_EQ = `!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (path(f o g) <=> path g)`;;

add_linear_invariants [PATH_LINEAR_IMAGE_EQ];;

let PATHSTART_TRANSLATION = `!a g. pathstart((\x. a + x) o g) = a + pathstart g`;;

add_translation_invariants [PATHSTART_TRANSLATION];;

let PATHSTART_LINEAR_IMAGE_EQ = `!f g. linear f ==> pathstart(f o g) = f(pathstart g)`;;

add_linear_invariants [PATHSTART_LINEAR_IMAGE_EQ];;

let PATHFINISH_TRANSLATION = `!a g. pathfinish((\x. a + x) o g) = a + pathfinish g`;;

add_translation_invariants [PATHFINISH_TRANSLATION];;

let PATHFINISH_LINEAR_IMAGE = `!f g. linear f ==> pathfinish(f o g) = f(pathfinish g)`;;

add_linear_invariants [PATHFINISH_LINEAR_IMAGE];;

let PATH_IMAGE_TRANSLATION = `!a g. path_image((\x. a + x) o g) = IMAGE (\x. a + x) (path_image g)`;;

add_translation_invariants [PATH_IMAGE_TRANSLATION];;

let PATH_IMAGE_LINEAR_IMAGE = `!f g. linear f ==> path_image(f o g) = IMAGE f (path_image g)`;;

add_linear_invariants [PATH_IMAGE_LINEAR_IMAGE];;

let REVERSEPATH_TRANSLATION = `!a g. reversepath((\x. a + x) o g) = (\x. a + x) o reversepath g`;;

add_translation_invariants [REVERSEPATH_TRANSLATION];;

let REVERSEPATH_LINEAR_IMAGE = `!f g. linear f ==> reversepath(f o g) = f o reversepath g`;;

add_linear_invariants [REVERSEPATH_LINEAR_IMAGE];;

let JOINPATHS_TRANSLATION = `!a:real^N g1 g2. ((\x. a + x) o g1) ++ ((\x. a + x) o g2) =
                    (\x. a + x) o (g1 ++ g2)`;;

add_translation_invariants [JOINPATHS_TRANSLATION];;

let JOINPATHS_LINEAR_IMAGE = `!f g1 g2. linear f ==> (f o g1) ++ (f o g2) = f o (g1 ++ g2)`;;

add_linear_invariants [JOINPATHS_LINEAR_IMAGE];;

let SIMPLE_PATH_TRANSLATION_EQ = `!a g:real^1->real^N. simple_path((\x. a + x) o g) <=> simple_path g`;;

add_translation_invariants [SIMPLE_PATH_TRANSLATION_EQ];;

let SIMPLE_PATH_LINEAR_IMAGE_EQ = `!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (simple_path(f o g) <=> simple_path g)`;;

add_linear_invariants [SIMPLE_PATH_LINEAR_IMAGE_EQ];;

let ARC_TRANSLATION_EQ = `!a g:real^1->real^N. arc((\x. a + x) o g) <=> arc g`;;

add_translation_invariants [ARC_TRANSLATION_EQ];;

let ARC_LINEAR_IMAGE_EQ = `!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (arc(f o g) <=> arc g)`;;

add_linear_invariants [ARC_LINEAR_IMAGE_EQ];;

let SIMPLE_PATH_CONTINUOUS_IMAGE = `!f g. simple_path g /\
         f continuous_on path_image g /\
         (!x y.
              x IN path_image g /\ y IN path_image g /\ f x = f y ==> x = y)
         ==> simple_path(f o g)`;;

let ARC_CONTINUOUS_IMAGE = `!f g:real^1->real^N.
        arc g /\
        f continuous_on path_image g /\
        (!x y. x IN path_image g /\ y IN path_image g /\ f x = f y ==> x = y)
        ==> arc(f o g)`;;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about paths.                                                 *)
(* ------------------------------------------------------------------------- *)

let ARC_IMP_SIMPLE_PATH = `!g. arc g ==> simple_path g`;;

let ARC_IMP_PATH = `!g. arc g ==> path g`;;

let SIMPLE_PATH_IMP_PATH = `!g. simple_path g ==> path g`;;

let SIMPLE_PATH_CASES = `!g:real^1->real^N. simple_path g ==> arc g \/ pathfinish g = pathstart g`;;

let SIMPLE_PATH_IMP_ARC = `!g:real^1->real^N.
        simple_path g /\ ~(pathfinish g = pathstart g) ==> arc g`;;

let ARC_DISTINCT_ENDS = `!g:real^1->real^N. arc g ==> ~(pathfinish g = pathstart g)`;;

let ARC_SIMPLE_PATH = `!g:real^1->real^N.
        arc g <=> simple_path g /\ ~(pathfinish g = pathstart g)`;;

let SIMPLE_PATH_EQ_ARC = `!g. ~(pathstart g = pathfinish g) ==> (simple_path g <=> arc g)`;;

let PATH_IMAGE_NONEMPTY = `!g. ~(path_image g = {})`;;

let PATHSTART_IN_PATH_IMAGE = `!g. (pathstart g) IN path_image g`;;

let PATHFINISH_IN_PATH_IMAGE = `!g. (pathfinish g) IN path_image g`;;

let CONNECTED_PATH_IMAGE = `!g. path g ==> connected(path_image g)`;;

let COMPACT_PATH_IMAGE = `!g. path g ==> compact(path_image g)`;;

let BOUNDED_PATH_IMAGE = `!g. path g ==> bounded(path_image g)`;;

let CLOSED_PATH_IMAGE = `!g. path g ==> closed(path_image g)`;;

let CONNECTED_SIMPLE_PATH_IMAGE = `!g. simple_path g ==> connected(path_image g)`;;

let COMPACT_SIMPLE_PATH_IMAGE = `!g. simple_path g ==> compact(path_image g)`;;

let BOUNDED_SIMPLE_PATH_IMAGE = `!g. simple_path g ==> bounded(path_image g)`;;

let CLOSED_SIMPLE_PATH_IMAGE = `!g. simple_path g ==> closed(path_image g)`;;

let CONNECTED_ARC_IMAGE = `!g. arc g ==> connected(path_image g)`;;

let COMPACT_ARC_IMAGE = `!g. arc g ==> compact(path_image g)`;;

let BOUNDED_ARC_IMAGE = `!g. arc g ==> bounded(path_image g)`;;

let CLOSED_ARC_IMAGE = `!g. arc g ==> closed(path_image g)`;;

let PATHSTART_COMPOSE = `!f p. pathstart(f o p) = f(pathstart p)`;;

let PATHFINISH_COMPOSE = `!f p. pathfinish(f o p) = f(pathfinish p)`;;

let PATH_IMAGE_COMPOSE = `!f p. path_image (f o p) = IMAGE f (path_image p)`;;

let PATH_COMPOSE_JOIN = `!f p q. f o (p ++ q) = (f o p) ++ (f o q)`;;

let PATH_COMPOSE_REVERSEPATH = `!f p. f o reversepath p = reversepath(f o p)`;;

let JOIN_PATHS_EQ = `!p q:real^1->real^N.
   (!t. t IN interval[vec 0,vec 1] ==> p t = p' t) /\
   (!t. t IN interval[vec 0,vec 1] ==> q t = q' t)
   ==> !t. t IN interval[vec 0,vec 1] ==> (p ++ q) t = (p' ++ q') t`;;

let CARD_EQ_SIMPLE_PATH_IMAGE = `!g. simple_path g ==> path_image g =_c (:real)`;;

let INFINITE_SIMPLE_PATH_IMAGE = `!g. simple_path g ==> INFINITE(path_image g)`;;

let CARD_EQ_ARC_IMAGE = `!g. arc g ==> path_image g =_c (:real)`;;

let INFINITE_ARC_IMAGE = `!g. arc g ==> INFINITE(path_image g)`;;

(* ------------------------------------------------------------------------- *)
(* The operations on paths.                                                  *)
(* ------------------------------------------------------------------------- *)

let JOINPATHS = `!g1 g2. pathfinish g1 = pathstart g2
           ==> g1 ++ g2 = \x. if drop x < &1 / &2 then g1(&2 % x)
                              else g2 (&2 % x - vec 1)`;;

let REVERSEPATH_REVERSEPATH = `!g:real^1->real^N. reversepath(reversepath g) = g`;;

let PATHSTART_REVERSEPATH = `pathstart(reversepath g) = pathfinish g`;;

let PATHFINISH_REVERSEPATH = `pathfinish(reversepath g) = pathstart g`;;

let PATHSTART_JOIN = `!g1 g2. pathstart(g1 ++ g2) = pathstart g1`;;

let PATHFINISH_JOIN = `!g1 g2. pathfinish(g1 ++ g2) = pathfinish g2`;;

let PATH_IMAGE_REVERSEPATH = `!g:real^1->real^N. path_image(reversepath g) = path_image g`;;

let PATH_REVERSEPATH = `!g:real^1->real^N. path(reversepath g) <=> path g`;;

let PATH_JOIN = `!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (path(g1 ++ g2) <=> path g1 /\ path g2)`;;

let PATH_JOIN_IMP = `!g1 g2:real^1->real^N.
        path g1 /\ path g2 /\ pathfinish g1 = pathstart g2
        ==> path(g1 ++ g2)`;;

let PATH_IMAGE_JOIN_SUBSET = `!g1 g2:real^1->real^N.
        path_image(g1 ++ g2) SUBSET (path_image g1 UNION path_image g2)`;;

let SUBSET_PATH_IMAGE_JOIN = `!g1 g2:real^1->real^N s.
        path_image g1 SUBSET s /\ path_image g2 SUBSET s
        ==> path_image(g1 ++ g2) SUBSET s`;;

let PATH_IMAGE_JOIN = `!g1 g2. pathfinish g1 = pathstart g2
           ==> path_image(g1 ++ g2) = path_image g1 UNION path_image g2`;;

let NOT_IN_PATH_IMAGE_JOIN = `!g1 g2 x. ~(x IN path_image g1) /\ ~(x IN path_image g2)
             ==> ~(x IN path_image(g1 ++ g2))`;;

let ARC_REVERSEPATH = `!g. arc g ==> arc(reversepath g)`;;

let ARC_REVERSEPATH_EQ = `!g:real^1->real^N. arc(reversepath g) <=> arc g`;;

let SIMPLE_PATH_REVERSEPATH = `!g. simple_path g ==> simple_path (reversepath g)`;;

let SIMPLE_PATH_REVERSEPATH_EQ = `!g:real^1->real^N. simple_path(reversepath g) <=> simple_path g`;;

let SIMPLE_PATH_JOIN_LOOP = `!g1 g2:real^1->real^N.
        arc g1 /\ arc g2 /\
        pathfinish g1 = pathstart g2 /\
        pathfinish g2 = pathstart g1 /\
        (path_image g1 INTER path_image g2) SUBSET
            {pathstart g1,pathstart g2}
        ==> simple_path(g1 ++ g2)`;;

let ARC_JOIN = `!g1 g2:real^1->real^N.
        arc g1 /\ arc g2 /\
        pathfinish g1 = pathstart g2 /\
        (path_image g1 INTER path_image g2) SUBSET {pathstart g2}
        ==> arc(g1 ++ g2)`;;

let REVERSEPATH_JOINPATHS = `!g1 g2. pathfinish g1 = pathstart g2
           ==> reversepath(g1 ++ g2) = reversepath g2 ++ reversepath g1`;;

(* ------------------------------------------------------------------------- *)
(* Some reversed and "if and only if" versions of joining theorems.          *)
(* ------------------------------------------------------------------------- *)

let PATH_JOIN_PATH_ENDS = `!g1 g2:real^1->real^N.
        path g2 /\ path(g1 ++ g2) ==> pathfinish g1 = pathstart g2`;;

let PATH_JOIN_EQ = `!g1 g2:real^1->real^N.
        path g1 /\ path g2
        ==> (path(g1 ++ g2) <=> pathfinish g1 = pathstart g2)`;;

let SIMPLE_PATH_JOIN_IMP = `!g1 g2:real^1->real^N.
        simple_path(g1 ++ g2) /\ pathfinish g1 = pathstart g2
        ==> arc g1 /\ arc g2 /\
            path_image g1 INTER path_image g2 SUBSET
            {pathstart g1, pathstart g2}`;;

let SIMPLE_PATH_JOIN_LOOP_EQ = `!g1 g2:real^1->real^N.
        pathfinish g2 = pathstart g1 /\
        pathfinish g1 = pathstart g2
        ==> (simple_path(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 SUBSET
             {pathstart g1, pathstart g2})`;;

let SIMPLE_PATH_JOIN_LOOP_EQ_ALT = `!g1 g2:real^1->real^N.
        pathfinish g2 = pathstart g1 /\
        pathfinish g1 = pathstart g2
        ==> (simple_path(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 =
             {pathstart g1, pathstart g2})`;;

let ARC_JOIN_EQ = `!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (arc(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 SUBSET {pathstart g2})`;;

let ARC_JOIN_EQ_ALT = `!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (arc(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 = {pathstart g2})`;;

(* ------------------------------------------------------------------------- *)
(* Reassociating a joined path doesn't matter for various properties.        *)
(* ------------------------------------------------------------------------- *)

let PATH_ASSOC = `!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (path(p ++ (q ++ r)) <=> path((p ++ q) ++ r))`;;

let SIMPLE_PATH_ASSOC = `!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (simple_path(p ++ (q ++ r)) <=> simple_path((p ++ q) ++ r))`;;

let ARC_ASSOC = `!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (arc(p ++ (q ++ r)) <=> arc((p ++ q) ++ r))`;;

(* ------------------------------------------------------------------------- *)
(* In the case of a loop, neither does symmetry.                             *)
(* ------------------------------------------------------------------------- *)

let PATH_SYM = `!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> (path(p ++ q) <=> path(q ++ p))`;;

let SIMPLE_PATH_SYM = `!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> (simple_path(p ++ q) <=> simple_path(q ++ p))`;;

let PATH_IMAGE_SYM = `!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> path_image(p ++ q) = path_image(q ++ p)`;;

(* ------------------------------------------------------------------------- *)
(* Reparametrizing a closed curve to start at some chosen point.             *)
(* ------------------------------------------------------------------------- *)

let shiftpath = new_definition
  `shiftpath a (f:real^1->real^N) =
        \x. if drop(a + x) <= &1 then f(a + x)
            else f(a + x - vec 1)`;;

let SHIFTPATH_TRANSLATION = `!a t g. shiftpath t ((\x. a + x) o g) = (\x. a + x) o shiftpath t g`;;

add_translation_invariants [SHIFTPATH_TRANSLATION];;

let SHIFTPATH_LINEAR_IMAGE = `!f t g. linear f ==> shiftpath t (f o g) = f o shiftpath t g`;;

add_linear_invariants [SHIFTPATH_LINEAR_IMAGE];;

let PATHSTART_SHIFTPATH = `!a g. drop a <= &1 ==> pathstart(shiftpath a g) = g(a)`;;

let PATHFINISH_SHIFTPATH = `!a g. &0 <= drop a /\ pathfinish g = pathstart g
         ==> pathfinish(shiftpath a g) = g(a)`;;

let ENDPOINTS_SHIFTPATH = `!a g. pathfinish g = pathstart g /\ a IN interval[vec 0,vec 1]
         ==> pathfinish(shiftpath a g) = g a /\
             pathstart(shiftpath a g) = g a`;;

let CLOSED_SHIFTPATH = `!a g. pathfinish g = pathstart g /\ a IN interval[vec 0,vec 1]
         ==> pathfinish(shiftpath a g) = pathstart(shiftpath a g)`;;

let PATH_SHIFTPATH = `!g a. path g /\ pathfinish g:real^N = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> path(shiftpath a g)`;;

let SHIFTPATH_SHIFTPATH = `!g a x. a IN interval[vec 0,vec 1] /\ pathfinish g = pathstart g /\
           x IN interval[vec 0,vec 1]
           ==> shiftpath (vec 1 - a) (shiftpath a g) x = g x`;;

let PATH_IMAGE_SHIFTPATH = `!a g:real^1->real^N.
        a IN interval[vec 0,vec 1] /\ pathfinish g = pathstart g
        ==> path_image(shiftpath a g) = path_image g`;;

let SIMPLE_PATH_SHIFTPATH = `!g a. simple_path g /\ pathfinish g = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> simple_path(shiftpath a g)`;;

(* ------------------------------------------------------------------------- *)
(* Choosing a sub-path of an existing path.                                  *)
(* ------------------------------------------------------------------------- *)

let subpath = new_definition
 `subpath u v g = \x. g(u + drop(v - u) % x)`;;

let SUBPATH_SCALING_LEMMA = `!u v.
    IMAGE (\x. u + drop(v - u) % x) (interval[vec 0,vec 1]) = segment[u,v]`;;

let PATH_IMAGE_SUBPATH_GEN = `!u v g:real^1->real^N. path_image(subpath u v g) = IMAGE g (segment[u,v])`;;

let PATH_IMAGE_SUBPATH = `!u v g:real^1->real^N.
        drop u <= drop v
        ==> path_image(subpath u v g) = IMAGE g (interval[u,v])`;;

let PATH_IMAGE_SUBPATH_COMBINE = `!g:real^1->real^N u.
        path g /\ u IN interval[vec 0,vec 1]
        ==> path_image(subpath (vec 0) u g) UNION
            path_image(subpath u (vec 1) g) =
            path_image g`;;

let PATH_SUBPATH = `!u v g:real^1->real^N.
        path g /\ u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> path(subpath u v g)`;;

let PATHSTART_SUBPATH = `!u v g:real^1->real^N. pathstart(subpath u v g) = g(u)`;;

let PATHFINISH_SUBPATH = `!u v g:real^1->real^N. pathfinish(subpath u v g) = g(v)`;;

let SUBPATH_TRIVIAL = `!g. subpath (vec 0) (vec 1) g = g`;;

let SUBPATH_REVERSEPATH = `!g. subpath (vec 1) (vec 0) g = reversepath g`;;

let REVERSEPATH_SUBPATH = `!g u v. reversepath(subpath u v g) = subpath v u g`;;

let SUBPATH_TRANSLATION = `!a g:real^1->real^N u v.
        subpath u v ((\x. a + x) o g) = (\x. a + x) o subpath u v g`;;

add_translation_invariants [SUBPATH_TRANSLATION];;

let SUBPATH_LINEAR_IMAGE = `!f:real^M->real^N g u v.
    linear f ==> subpath u v (f o g) = f o subpath u v g`;;

add_linear_invariants [SUBPATH_LINEAR_IMAGE];;

let SIMPLE_PATH_SUBPATH_EQ = `!g u v. simple_path(subpath u v g) <=>
           path(subpath u v g) /\ ~(u = v) /\
           (!x y. x IN segment[u,v] /\ y IN segment[u,v] /\ g x = g y
                  ==> x = y \/ x = u /\ y = v \/ x = v /\ y = u)`;;

let ARC_SUBPATH_EQ = `!g u v. arc(subpath u v g) <=>
           path(subpath u v g) /\ ~(u = v) /\
           (!x y. x IN segment[u,v] /\ y IN segment[u,v] /\ g x = g y
                  ==> x = y)`;;

let SIMPLE_PATH_SUBPATH = `!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(u = v)
           ==> simple_path(subpath u v g)`;;

let ARC_SIMPLE_PATH_SUBPATH = `!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(g u = g v)
           ==> arc(subpath u v g)`;;

let ARC_SUBPATH_ARC = `!u v g. arc g /\
           u IN interval [vec 0,vec 1] /\ v IN interval [vec 0,vec 1] /\
           ~(u = v)
           ==> arc(subpath u v g)`;;

let ARC_SIMPLE_PATH_SUBPATH_INTERIOR = `!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(u = v) /\ abs(drop u - drop v) < &1
           ==> arc(subpath u v g)`;;

let PATH_IMAGE_SUBPATH_SUBSET = `!u v g:real^1->real^N.
        path g /\ u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> path_image(subpath u v g) SUBSET path_image g`;;

let JOIN_SUBPATHS_MIDDLE = `!p:real^1->real^N.
   subpath (vec 0) (lift(&1 / &2)) p ++ subpath (lift(&1 / &2)) (vec 1) p = p`;;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas about choosing sub-paths.                          *)
(* ------------------------------------------------------------------------- *)

let EXISTS_SUBPATH_OF_PATH = `!g a b:real^N.
        path g /\ a IN path_image g /\ b IN path_image g
        ==> ?h. path h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET path_image g`;;

let EXISTS_SUBPATH_OF_ARC_NOENDS = `!g a b:real^N.
        arc g /\ a IN path_image g /\ b IN path_image g /\
        {a,b} INTER {pathstart g,pathfinish g} = {}
        ==> ?h. path h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET
                (path_image g) DIFF {pathstart g,pathfinish g}`;;

let EXISTS_SUBARC_OF_ARC_NOENDS = `!g a b:real^N.
        arc g /\ a IN path_image g /\ b IN path_image g /\ ~(a = b) /\
        {a,b} INTER {pathstart g,pathfinish g} = {}
        ==> ?h. arc h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET
                (path_image g) DIFF {pathstart g,pathfinish g}`;;

let EXISTS_ARC_PSUBSET_SIMPLE_PATH = `!g:real^1->real^N.
        simple_path g /\ closed s /\ s PSUBSET path_image g
        ==> ?h. arc h /\
                s SUBSET path_image h /\
                path_image h SUBSET path_image g`;;

let EXISTS_DOUBLE_ARC_EXPLICIT = `!g:real^1->real^N a b.
        simple_path g /\ pathfinish g = pathstart g /\
        a IN interval[vec 0,vec 1] /\ b IN interval[vec 0,vec 1] /\
        drop a <= drop b /\ ~(g a = g b)
        ==> ?u d. arc u /\ arc d /\
                  pathstart u = g a /\ pathfinish u = g b /\
                  pathstart d = g b /\ pathfinish d = g a /\
                  path_image u =
                    IMAGE g (interval[a,b]) /\
                  path_image d =
                    IMAGE g (interval[vec 0,vec 1] DIFF interval(a,b)) /\
                  (path_image u) INTER (path_image d) = {g a,g b} /\
                  (path_image u) UNION (path_image d) = path_image g`;;

let EXISTS_DOUBLE_ARC = `!g:real^1->real^N a b.
        simple_path g /\ pathfinish g = pathstart g /\
        a IN path_image g /\ b IN path_image g /\ ~(a = b)
        ==> ?u d. arc u /\ arc d /\
                  pathstart u = a /\ pathfinish u = b /\
                  pathstart d = b /\ pathfinish d = a /\
                  (path_image u) INTER (path_image d) = {a,b} /\
                  (path_image u) UNION (path_image d) = path_image g`;;

let SUBPATH_TO_FRONTIER_EXPLICIT = `!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                (!x. &0 <= drop x /\ drop x < drop u ==> g x IN interior s) /\
                ~(g u IN interior s) /\
                (u = vec 0 \/ g u IN closure s)`;;

let SUBPATH_TO_FRONTIER_STRONG = `!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                 ~(pathfinish(subpath (vec 0) u g) IN interior s) /\
                (u = vec 0 \/
                 (!x. x IN interval[vec 0,vec 1] /\ ~(x = vec 1)
                      ==> (subpath (vec 0) u g x) IN interior s) /\
                 pathfinish(subpath (vec 0) u g) IN closure s)`;;

let SUBPATH_TO_FRONTIER = `!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                pathfinish(subpath (vec 0) u g) IN frontier s /\
                (path_image(subpath (vec 0) u g) DELETE
                 pathfinish(subpath (vec 0) u g))
                SUBSET interior s`;;

let EXISTS_PATH_SUBPATH_TO_FRONTIER = `!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?h. path h /\ pathstart h = pathstart g /\
                (path_image h) SUBSET (path_image g) /\
                (path_image h DELETE (pathfinish h)) SUBSET interior s /\
                pathfinish h IN frontier s`;;

let EXISTS_PATH_SUBPATH_TO_FRONTIER_CLOSED = `!g:real^1->real^N s.
        closed s /\ path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?h. path h /\ pathstart h = pathstart g /\
                (path_image h) SUBSET (path_image g) INTER s /\
                pathfinish h IN frontier s`;;

let PATH_COMBINE = `!u g:real^1->real^N.
        u IN interval[vec 0,vec 1]
        ==> (path g <=>
             path(subpath (vec 0) u g) /\ path(subpath u (vec 1) g))`;;

(* ------------------------------------------------------------------------- *)
(* Special case of straight-line paths.                                      *)
(* ------------------------------------------------------------------------- *)

let linepath = new_definition
 `linepath(a,b) = \x. (&1 - drop x) % a + drop x % b`;;

let LINEPATH_TRANSLATION = `!a b c. linepath(a + b,a + c) = (\x. a + x) o linepath(b,c)`;;

add_translation_invariants [LINEPATH_TRANSLATION];;

let LINEPATH_LINEAR_IMAGE = `!f. linear f ==> !b c. linepath(f b,f c) = f o linepath(b,c)`;;

add_linear_invariants [LINEPATH_LINEAR_IMAGE];;

let PATHSTART_LINEPATH = `!a b. pathstart(linepath(a,b)) = a`;;

let PATHFINISH_LINEPATH = `!a b. pathfinish(linepath(a,b)) = b`;;

let CONTINUOUS_LINEPATH_AT = `!a b x. linepath(a,b) continuous (at x)`;;

let CONTINUOUS_ON_LINEPATH = `!a b s. linepath(a,b) continuous_on s`;;

let PATH_LINEPATH = `!a b. path(linepath(a,b))`;;

let PATH_IMAGE_LINEPATH = `!a b. path_image(linepath (a,b)) = segment[a,b]`;;

let REVERSEPATH_LINEPATH = `!a b. reversepath(linepath(a,b)) = linepath(b,a)`;;

let ARC_LINEPATH = `!a b. ~(a = b) ==> arc(linepath(a,b))`;;

let SIMPLE_PATH_LINEPATH = `!a b. ~(a = b) ==> simple_path(linepath(a,b))`;;

let SIMPLE_PATH_LINEPATH_EQ = `!a b:real^N. simple_path(linepath(a,b)) <=> ~(a = b)`;;

let ARC_LINEPATH_EQ = `!a b. arc(linepath(a,b)) <=> ~(a = b)`;;

let LINEPATH_REFL = `!a. linepath(a,a) = \x. a`;;

let PATH_IMAGE_CONST = `!a:real^N. path_image (\x. a) = {a}`;;

let SHIFTPATH_TRIVIAL = `!t a. shiftpath t (linepath(a,a)) = linepath(a,a)`;;

let SUBPATH_REFL = `!g a. subpath a a g = linepath(g a,g a)`;;

let SEGMENT_TO_FRONTIER = `!s a b:real^N.
        a IN interior s /\ ~(b IN interior s)
        ==> ?c. c IN segment[a,b] /\ ~(c = a) /\ c IN frontier s /\
                segment(a,c) SUBSET interior s`;;

(* ------------------------------------------------------------------------- *)
(* Bounding a point away from a path.                                        *)
(* ------------------------------------------------------------------------- *)

let NOT_ON_PATH_BALL = `!g z:real^N.
        path g /\ ~(z IN path_image g)
        ==> ?e. &0 < e /\ ball(z,e) INTER (path_image g) = {}`;;

let NOT_ON_PATH_CBALL = `!g z:real^N.
        path g /\ ~(z IN path_image g)
        ==> ?e. &0 < e /\ cball(z,e) INTER (path_image g) = {}`;;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms of arc images.                                             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_ARC = `!g:real^1->real^N.
     arc g ==> ?h. homeomorphism (interval[vec 0,vec 1],path_image g) (g,h)`;;

let HOMEOMORPHIC_ARC_IMAGE_INTERVAL = `!g:real^1->real^N a b:real^1.
      arc g /\ drop a < drop b ==> (path_image g) homeomorphic interval[a,b]`;;

let HOMEOMORPHIC_ARC_IMAGES = `!g:real^1->real^M h:real^1->real^N.
        arc g /\ arc h ==> (path_image g) homeomorphic (path_image h)`;;

let HOMEOMORPHIC_ARC_IMAGE_SEGMENT = `!g:real^1->real^N a b:real^M.
        arc g /\ ~(a = b) ==> (path_image g) homeomorphic segment[a,b]`;;

let HOMEOMORPHIC_ARC_IMAGE_SEGMENT_EQ = `!s:real^N->bool a b:real^M.
        ~(a = b)
        ==> (s homeomorphic segment[a,b] <=>
             ?g. arc g /\ path_image g = s)`;;

let CONNECTED_SUBSET_PATH_IMAGE_ARC = `!s g:real^1->real^N.
        arc g /\ connected s /\
        s SUBSET path_image g /\ pathstart g IN s /\ pathfinish g IN s
        ==> s = path_image g`;;

let ARC_IMAGE_UNIQUE = `!g h:real^1->real^N.
        path g /\ arc h /\ path_image g SUBSET path_image h /\
        {pathstart g,pathfinish g} = {pathstart h,pathfinish h}
        ==> path_image g = path_image h`;;

let CONNECTED_SUBSET_ARC_PAIR = `!g h s:real^N->bool.
        arc g /\ arc h /\
        pathstart g = pathstart h /\ pathfinish g = pathfinish h /\
        path_image g INTER path_image h = {pathstart g,pathfinish g} /\
        connected s /\
        s SUBSET path_image g UNION path_image h /\
        pathstart g IN s /\ pathfinish g IN s
        ==> path_image g SUBSET s \/ path_image h SUBSET s`;;

let HOMEOMORPHIC_SIMPLE_PATH_IMAGES = `!g:real^1->real^M h:real^1->real^N.
        simple_path g /\ pathfinish g = pathstart g /\
        simple_path h /\ pathfinish h = pathstart h
        ==> (path_image g) homeomorphic (path_image h)`;;

let HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ = `!s:real^N->bool a:real^2 r.
        &0 < r
        ==> (s homeomorphic sphere(a,r) <=>
             ?g. simple_path g /\ pathfinish g = pathstart g /\
                 path_image g = s)`;;

let HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE = `!g:real^1->real^N a:real^2 r.
        simple_path g /\ pathfinish g = pathstart g /\ &0 < r
        ==> (path_image g) homeomorphic sphere(a,r)`;;

(* ------------------------------------------------------------------------- *)
(* Path component, considered as a "joinability" relation (from Tom Hales).  *)
(* ------------------------------------------------------------------------- *)

let path_component = new_definition
 `path_component s x y <=>
        ?g. path g /\ path_image g SUBSET s /\
            pathstart g = x /\ pathfinish g = y`;;

let path_components = new_definition
 `path_components s = {path_component s x | x | x IN s}`;;

let PATH_COMPONENT_OF_EUCLIDEAN = `!s:real^N->bool.
        path_component_of (subtopology euclidean s) = path_component s`;;

let PATH_COMPONENTS_OF_EUCLIDEAN = `!s:real^N->bool.
        path_components_of (subtopology euclidean s) = path_components s`;;

let PATH_COMPONENT_IN = `!s x y. path_component s x y ==> x IN s /\ y IN s`;;

let PATH_COMPONENT_REFL_EQ = `!s x:real^N. path_component s x x <=> x IN s`;;

let PATH_COMPONENT_REFL = `!s x:real^N. x IN s ==> path_component s x x`;;

let PATH_COMPONENT_SYM_EQ = `!s x y. path_component s x y <=> path_component s y x`;;

let PATH_COMPONENT_SYM = `!s x y:real^N. path_component s x y ==> path_component s y x`;;

let PATH_COMPONENT_TRANS = `!s x y:real^N.
      path_component s x y /\ path_component s y z ==> path_component s x z`;;

let PATH_COMPONENT_OF_SUBSET = `!s t x. s SUBSET t /\ path_component s x y ==> path_component t x y`;;

(* ------------------------------------------------------------------------- *)
(* Can also consider it as a set, as the name suggests.                      *)
(* ------------------------------------------------------------------------- *)

let PATH_COMPONENT_SET = `!s x. path_component s x =
            { y | ?g. path g /\ path_image g SUBSET s /\
                      pathstart g = x /\ pathfinish g = y }`;;

let PATH_COMPONENT_SUBSET = `!s x. (path_component s x) SUBSET s`;;

let PATH_COMPONENT_EQ_EMPTY = `!s x. path_component s x = {} <=> ~(x IN s)`;;

let PATH_COMPONENT_EMPTY = `!x. path_component {} x = {}`;;

let UNIONS_PATH_COMPONENT = `!s:real^N->bool. UNIONS {path_component s x |x| x IN s} = s`;;

let PATH_COMPONENT_TRANSLATION = `!a s x. path_component (IMAGE (\x. a + x) s) (a + x) =
                IMAGE (\x. a + x) (path_component s x)`;;

add_translation_invariants [PATH_COMPONENT_TRANSLATION];;

let PATH_COMPONENT_LINEAR_IMAGE = `!f s x. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> path_component (IMAGE f s) (f x) =
               IMAGE f (path_component s x)`;;

add_linear_invariants [PATH_COMPONENT_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Path connectedness of a space.                                            *)
(* ------------------------------------------------------------------------- *)

let path_connected = new_definition
 `path_connected s <=>
        !x y. x IN s /\ y IN s
              ==> ?g. path g /\ (path_image g) SUBSET s /\
                      pathstart g = x /\ pathfinish g = y`;;

let PATH_CONNECTED_IFF_PATH_COMPONENT = `!s. path_connected s <=> !x y. x IN s /\ y IN s ==> path_component s x y`;;

let PATH_CONNECTED_IN_EUCLIDEAN = `!s:real^N->bool. path_connected_in euclidean s <=> path_connected s`;;

let PATH_CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY = `!s:real^N->bool.
       path_connected_space(subtopology euclidean s) <=> path_connected s`;;

let PATH_CONNECTED_IMP_PATH_COMPONENT = `!s a b:real^N.
     path_connected s /\ a IN s /\ b IN s ==> path_component s a b`;;

let PATH_CONNECTED_COMPONENT_SET = `!s. path_connected s <=> !x. x IN s ==> path_component s x = s`;;

let PATH_COMPONENT_MONO = `!s t x. s SUBSET t ==> (path_component s x) SUBSET (path_component t x)`;;

let PATH_COMPONENT_MAXIMAL = `!s t x. x IN t /\ path_connected t /\ t SUBSET s
           ==> t SUBSET (path_component s x)`;;

let PATH_COMPONENT_EQ = `!s x y. y IN path_component s x
           ==> path_component s y = path_component s x`;;

let PATH_CONNECTED_PATH_IMAGE = `!p:real^1->real^N. path p ==> path_connected(path_image p)`;;

let PATH_COMPONENT_PATH_IMAGE_PATHSTART = `!p x:real^N.
        path p /\ x IN path_image p
        ==> path_component (path_image p) (pathstart p) x`;;

let PATH_CONNECTED_PATH_COMPONENT = `!s x:real^N. path_connected(path_component s x)`;;

let PATH_COMPONENT = `!s x y:real^N.
        path_component s x y <=>
        ?t. path_connected t /\ t SUBSET s /\ x IN t /\ y IN t`;;

let PATH_COMPONENT_PATH_COMPONENT = `!s x:real^N.
        path_component (path_component s x) x = path_component s x`;;

let PATH_CONNECTED_LINEPATH = `!s a b:real^N. segment[a,b] SUBSET s ==> path_component s a b`;;

let PATH_COMPONENT_DISJOINT = `!s a b. DISJOINT (path_component s a) (path_component s b) <=>
             ~(a IN path_component s b)`;;

let PATH_COMPONENT_EQ_EQ = `!s x y:real^N.
        path_component s x = path_component s y <=>
        ~(x IN s) /\ ~(y IN s) \/
        x IN s /\ y IN s /\ path_component s x y`;;

let PATH_COMPONENT_UNIQUE = `!s c x:real^N.
        x IN c /\ c SUBSET s /\ path_connected c /\
        (!c'. x IN c' /\ c' SUBSET s /\ path_connected c'
              ==> c' SUBSET c)
        ==> path_component s x = c`;;

let PATH_COMPONENT_INTERMEDIATE_SUBSET = `!t u a:real^N.
        path_component u a SUBSET t /\ t SUBSET u
        ==> path_component t a = path_component u a`;;

let COMPLEMENT_PATH_COMPONENT_UNIONS = `!s x:real^N.
     s DIFF path_component s x =
     UNIONS({path_component s y | y | y IN s} DELETE (path_component s x))`;;

(* ------------------------------------------------------------------------- *)
(* General "locally connected implies connected" type results.               *)
(* ------------------------------------------------------------------------- *)

let OPEN_GENERAL_COMPONENT = `!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x:real^N. open s ==> open(c s x)`;;

let OPEN_NON_GENERAL_COMPONENT = `!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x:real^N. open s ==> open(s DIFF c s x)`;;

let GENERAL_CONNECTED_OPEN = `!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x y:real^N. open s /\ connected s /\ x IN s /\ y IN s
                          ==> c s x y`;;

(* ------------------------------------------------------------------------- *)
(* Some useful lemmas about path-connectedness.                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_IMP_PATH_CONNECTED = `!s:real^N->bool. convex s ==> path_connected s`;;

let PATH_CONNECTED_UNIV = `path_connected(:real^N)`;;

let IS_INTERVAL_PATH_CONNECTED = `!s. is_interval s ==> path_connected s`;;

let PATH_CONNECTED_INTERVAL = `(!a b:real^N. path_connected(interval[a,b])) /\
   (!a b:real^N. path_connected(interval(a,b)))`;;

let PATH_COMPONENT_UNIV = `!x. path_component(:real^N) x = (:real^N)`;;

let PATH_CONNECTED_IMP_CONNECTED = `!s:real^N->bool. path_connected s ==> connected s`;;

let OPEN_PATH_COMPONENT = `!s x:real^N. open s ==> open(path_component s x)`;;

let OPEN_NON_PATH_COMPONENT = `!s x:real^N. open s ==> open(s DIFF path_component s x)`;;

let PATH_CONNECTED_CONTINUOUS_IMAGE = `!f:real^M->real^N s.
        f continuous_on s /\ path_connected s ==> path_connected (IMAGE f s)`;;

let HOMEOMORPHIC_PATH_CONNECTEDNESS = `!s t. s homeomorphic t ==> (path_connected s <=> path_connected t)`;;

let PATH_CONNECTED_LINEAR_IMAGE = `!f:real^M->real^N s.
     path_connected s /\ linear f ==> path_connected(IMAGE f s)`;;

let PATH_CONNECTED_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (path_connected (IMAGE f s) <=> path_connected s)`;;

add_linear_invariants [PATH_CONNECTED_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_PATH_CONNECTEDNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (path_connected(IMAGE f k) <=> path_connected k)`;;

let PATH_CONNECTED_EMPTY = `path_connected {}`;;

let PATH_CONNECTED_SING = `!a:real^N. path_connected {a}`;;

let PATH_CONNECTED_UNION = `!s t. path_connected s /\ path_connected t /\ ~(s INTER t = {})
         ==> path_connected (s UNION t)`;;

let PATH_CONNECTED_UNIONS = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> path_connected s) /\ ~(INTERS f = {})
        ==> path_connected(UNIONS f)`;;

let PATH_CONNECTED_TRANSLATION = `!a s. path_connected s ==> path_connected (IMAGE (\x:real^N. a + x) s)`;;

let PATH_CONNECTED_TRANSLATION_EQ = `!a s. path_connected (IMAGE (\x:real^N. a + x) s) <=> path_connected s`;;

add_translation_invariants [PATH_CONNECTED_TRANSLATION_EQ];;

let PATH_CONNECTED_PCROSS = `!s:real^M->bool t:real^N->bool.
        path_connected s /\ path_connected t
        ==> path_connected (s PCROSS t)`;;

let PATH_CONNECTED_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        path_connected(s PCROSS t) <=>
        s = {} \/ t = {} \/ path_connected s /\ path_connected t`;;

let PATH_COMPONENT_PCROSS = `!s t a:real^M b:real^N.
        path_component (s PCROSS t) (pastecart a b) =
        path_component s a PCROSS path_component t b`;;

let PATH_CONNECTED_SCALING = `!s:real^N->bool c.
        path_connected s ==> path_connected (IMAGE (\x. c % x) s)`;;

let PATH_CONNECTED_SCALING_EQ = `!s:real^N->bool c.
        path_connected (IMAGE (\x. c % x) s) <=> c = &0 \/ path_connected s`;;

let PATH_CONNECTED_AFFINITY_EQ = `!s m c:real^N.
        path_connected (IMAGE (\x. m % x + c) s) <=>
        m = &0 \/ path_connected s`;;

let PATH_CONNECTED_AFFINITY = `!s m c:real^N.
     path_connected s ==> path_connected (IMAGE (\x. m % x + c) s)`;;

let PATH_CONNECTED_NEGATIONS = `!s:real^N->bool.
        path_connected s ==> path_connected (IMAGE (--) s)`;;

let PATH_CONNECTED_SUMS = `!s t:real^N->bool.
        path_connected s /\ path_connected t
        ==> path_connected {x + y | x IN s /\ y IN t}`;;

let IS_INTERVAL_PATH_CONNECTED_1 = `!s:real^1->bool. is_interval s <=> path_connected s`;;

(* ------------------------------------------------------------------------- *)
(* Bounds on components of a continuous image.                               *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_PATH_COMPONENTS = `!f:real^M->real^N s.
        f continuous_on s
        ==> {path_component (IMAGE f s) y | y | y IN IMAGE f s}
            <=_c {path_component s x | x | x IN s}`;;

let CARD_LE_CONNECTED_COMPONENTS = `!f:real^M->real^N s.
        f continuous_on s
        ==> {connected_component (IMAGE f s) y | y | y IN IMAGE f s}
            <=_c {connected_component s x | x | x IN s}`;;

let CARD_LE_COMPONENTS = `!f:real^M->real^N s.
        f continuous_on s ==> components(IMAGE f s) <=_c components s`;;

(* ------------------------------------------------------------------------- *)
(* More stuff about segments.                                                *)
(* ------------------------------------------------------------------------- *)

let PATH_CONNECTED_SEGMENT = `(!a b. path_connected(segment[a,b])) /\
   (!a b. path_connected(segment(a,b)))`;;

let PATH_CONNECTED_SEMIOPEN_SEGMENT = `(!a b:real^N. path_connected(segment[a,b] DELETE a)) /\
   (!a b:real^N. path_connected(segment[a,b] DELETE b))`;;

let SUBSET_CONTINUOUS_IMAGE_SEGMENT_1 = `!f:real^N->real^1 a b.
        f continuous_on segment[a,b]
        ==> segment[f a,f b] SUBSET IMAGE f (segment[a,b])`;;

let CONTINUOUS_INJECTIVE_IMAGE_SEGMENT_1 = `!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\
        (!x y. x IN segment[a,b] /\ y IN segment[a,b] /\ f x = f y ==> x = y)
        ==> IMAGE f (segment[a,b]) = segment[f a,f b]`;;

let CONTINUOUS_INJECTIVE_IMAGE_OPEN_SEGMENT_1 = `!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\
        (!x y. x IN segment[a,b] /\ y IN segment[a,b] /\ f x = f y ==> x = y)
        ==> IMAGE f (segment(a,b)) = segment(f a,f b)`;;

let CONTINUOUS_IVT_LOCAL_EXTREMUM = `!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\ ~(a = b) /\ f(a) = f(b)
         ==> ?z. z IN segment(a,b) /\
                 ((!w. w IN segment[a,b] ==> drop(f w) <= drop(f z)) \/
                  (!w. w IN segment[a,b] ==> drop(f z) <= drop(f w)))`;;

let FRONTIER_UNIONS_SUBSET_CLOSURE = `!f:(real^N->bool)->bool.
        frontier(UNIONS f) SUBSET closure(UNIONS {frontier t | t IN f})`;;

let FRONTIER_UNIONS_SUBSET = `!f:(real^N->bool)->bool.
        FINITE f ==> frontier(UNIONS f) SUBSET UNIONS {frontier t | t IN f}`;;

let CLOSURE_CONVEX_INTER_AFFINE = `!s t:real^N->bool.
      convex s /\ affine t /\ ~(relative_interior s INTER t = {})
      ==> closure(s INTER t) = closure(s) INTER t`;;

let RELATIVE_FRONTIER_CONVEX_INTER_AFFINE = `!s t:real^N->bool.
        convex s /\ affine t /\ ~(interior s INTER t = {})
        ==> relative_frontier(s INTER t) = frontier s INTER t`;;

let RELATIVE_FRONTIER_CBALL_INTER_AFFINE = `!s a:real^N r.
        affine s /\ a IN s /\ ~(r = &0)
        ==> relative_frontier(cball(a,r) INTER s) = sphere(a,r) INTER s`;;

let CONNECTED_COMPONENT_1_GEN = `!s a b:real^N.
        dimindex(:N) = 1
        ==> (connected_component s a b <=> segment[a,b] SUBSET s)`;;

let CONNECTED_COMPONENT_1 = `!s a b:real^1. connected_component s a b <=> segment[a,b] SUBSET s`;;

let HOMEOMORPHIC_SEGMENTS = `(!a b:real^M c d:real^N.
        segment[a,b] homeomorphic segment[c,d] <=> (a = b <=> c = d)) /\
   (!a b:real^M c d:real^N.
        ~(segment[a,b] homeomorphic segment(c,d))) /\
   (!a b:real^M c d:real^N.
        ~(segment(a,b) homeomorphic segment[c,d])) /\
   (!a b:real^M c d:real^N.
        segment(a,b) homeomorphic segment(c,d) <=> (a = b <=> c = d))`;;

let HOMEOMORPHISM_SEGMENT = `!a b:real^N.
        ~(a = b)
        ==> ?h. homeomorphism (interval[vec 0:real^1,vec 1],segment[a,b])
                              ((\t. (&1 - drop t) % a + drop t % b),h)`;;

let CONNECTED_SUBSET_SEGMENT = `!s a b:real^N.
        connected s /\ s SUBSET segment[a,b] /\ a IN s /\ b IN s
        ==> s = segment[a,b]`;;

let DIAMETER_SEGMENT = `(!a b:real^N. diameter(segment[a,b]) = dist(a,b)) /\
   (!a b:real^N. diameter(segment(a,b)) = dist(a,b))`;;

(* ------------------------------------------------------------------------- *)
(* Removing points from arcs and simple paths, hence allowing us to          *)
(* distinguish simple closed curves and arcs topologically.                  *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_PATH_ENDLESS = `!c:real^1->real^N.
        simple_path c
        ==> path_image c DIFF {pathstart c,pathfinish c} =
            IMAGE c (interval(vec 0,vec 1))`;;

let PATH_CONNECTED_SIMPLE_PATH_ENDLESS = `!c:real^1->real^N.
        simple_path c
        ==> path_connected(path_image c DIFF {pathstart c,pathfinish c})`;;

let CONNECTED_SIMPLE_PATH_ENDLESS = `!c:real^1->real^N.
        simple_path c
        ==> connected(path_image c DIFF {pathstart c,pathfinish c})`;;

let NONEMPTY_SIMPLE_PATH_ENDLESS = `!c:real^1->real^N.
      simple_path c ==> ~(path_image c DIFF {pathstart c,pathfinish c} = {})`;;

let CONNECTED_ARC_IMAGE_DELETE = `!g a:real^N.
        arc g /\ a IN path_image g
        ==> (connected(path_image g DELETE a) <=>
             a IN {pathstart g,pathfinish g})`;;

let CONNECTED_SIMPLE_PATH_IMAGE_DELETE = `!g a:real^N.
        simple_path g /\ pathfinish g = pathstart g
        ==> connected(path_image g DELETE a)`;;

let HOMEOMORPHIC_SIMPLE_PATH_ARC = `!g:real^1->real^M h:real^1->real^N.
        arc g /\ simple_path h /\ (path_image g) homeomorphic (path_image h)
        ==> arc h`;;

let HOMEOMORPHIC_SIMPLE_PATH_ARC_EQ = `!g:real^1->real^M h:real^1->real^N.
        simple_path g /\ simple_path h /\
        (path_image g) homeomorphic (path_image h)
        ==> (arc g <=> arc h)`;;

let ARC_ENDS_UNIQUE = `!g h:real^1->real^N.
        arc g /\ simple_path h /\ path_image g = path_image h
        ==> {pathstart g, pathfinish g} = {pathstart h, pathfinish h}`;;

let ARC_HOMEOMORPHISM_ENDS = `!g h f f':real^N->real^N.
        homeomorphism (path_image g,path_image h) (f,f') /\ arc g /\ arc h
        ==> f(pathstart g) = pathstart h /\
            f(pathfinish g) = pathfinish h /\
            f'(pathstart h) = pathstart g /\
            f'(pathfinish h) = pathfinish g \/
            f(pathstart g) = pathfinish h /\
            f(pathfinish g) = pathstart h /\
            f'(pathstart h) = pathfinish g /\
            f'(pathfinish h) = pathstart g`;;

let HOMEOMORPHISM_ARC_IMAGES = `!g:real^1->real^M h:real^1->real^N.
        arc g /\ arc h
        ==> ?f f'. homeomorphism (path_image g,path_image h) (f,f') /\
                   f(pathstart g) = pathstart h /\
                   f(pathfinish g) = pathfinish h /\
                   f'(pathstart h) = pathstart g /\
                   f'(pathfinish h) = pathfinish g`;;

let COLLINEAR_SIMPLE_PATH_IMAGE = `!g:real^1->real^N.
        simple_path g /\ collinear(path_image g)
        ==> path_image g = segment[pathstart g,pathfinish g]`;;

(* ------------------------------------------------------------------------- *)
(* An injective function into R is a homeomorphism and so an open map.       *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_INTO_1D_EQ_HOMEOMORPHISM = `!f:real^N->real^1 s.
        f continuous_on s /\ path_connected s
        ==>  ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              ?g. homeomorphism (s,IMAGE f s) (f,g))`;;

let INJECTIVE_INTO_1D_IMP_OPEN_MAP = `!f:real^N->real^1 s t.
        f continuous_on s /\ path_connected s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open_in (subtopology euclidean s) t
        ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t)`;;

let HOMEOMORPHISM_INTO_1D = `!f:real^N->real^1 s t.
        path_connected s /\
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ?g. homeomorphism(s,t) (f,g)`;;

(* ------------------------------------------------------------------------- *)
(* Injective function on an interval is strictly increasing or decreasing.   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_INJECTIVE_IFF_MONOTONIC = `!f:real^1->real^1 s.
        f continuous_on s /\ is_interval s
        ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
             (!x y. x IN s /\ y IN s /\ drop x < drop y
                    ==> drop(f x) < drop(f y)) \/
             (!x y. x IN s /\ y IN s /\ drop x < drop y
                    ==> drop(f y) < drop(f x)))`;;

let CONTINUOUS_INJECTIVE_IMP_MONOTONIC = `!f s.
        f continuous_on s /\ is_interval s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> (!x y. x IN s /\ y IN s
                   ==> (drop(f x) < drop(f y) <=> drop x < drop y)) \/
            (!x y. x IN s /\ y IN s
                   ==> (drop(f x) < drop(f y) <=> drop y < drop x))`;;

let HOMEOMORPHISM_1D_IMP_MONOTONIC = `!f g s t.
        homeomorphism(s,t) (f,g) /\ is_interval s
        ==> (!x y. x IN s /\ y IN s
                   ==> (drop(f x) < drop(f y) <=> drop x < drop y)) /\
            (!x y. x IN t /\ y IN t
                   ==> (drop(g x) < drop(g y) <=> drop x < drop y)) \/
            (!x y. x IN s /\ y IN s
                   ==> (drop(f x) < drop(f y) <=> drop y < drop x)) /\
            (!x y. x IN t /\ y IN t
                   ==> (drop(g x) < drop(g y) <=> drop y < drop x))`;;

(* ------------------------------------------------------------------------- *)
(* Topological rendering of Darboux continuity, proof it implies continuity  *)
(* for a regulated function from R^1 (having left and right limits).         *)
(* ------------------------------------------------------------------------- *)

let CONVEXITY_PRESERVING = `!f:real^M->real^N s.
        (!c. c SUBSET s /\ convex c ==> convex(IMAGE f c)) <=>
        (!a b. segment[a,b] SUBSET s ==> convex(IMAGE f (segment[a,b])))`;;

let CONVEXITY_PRESERVING_ALT = `!f:real^M->real^N s.
        (!c. c SUBSET s /\ convex c ==> convex(IMAGE f c)) <=>
        (!a b. segment[a,b] SUBSET s
               ==> segment[f a,f b] SUBSET IMAGE f (segment[a,b]))`;;

let DARBOUX_AND_REGULATED_IMP_CONTINUOUS = `!f:real^1->real^N s.
      is_interval s /\
      (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c)) /\
      (!a. a IN s
           ==> (?l. (f --> l) (at a within s INTER {x | drop x <= drop a})) /\
               (?r. (f --> r) (at a within s INTER {x | drop a <= drop x})))
      ==> f continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Some handy facts about Lipschitz functions.                               *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_ON_UNION = `!(f:real^1->real^N) s t l.
        is_interval s /\ is_interval t /\ ~(s INTER t = {}) /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= l * norm(x - y)) /\
        (!x y. x IN t /\ y IN t ==> norm(f x - f y) <= l * norm(x - y))
        ==> !x y. x IN s UNION t /\ y IN s UNION t
                  ==> norm(f x - f y) <= l * norm(x - y)`;;

let LIPSCHITZ_ON_COMBINE = `!(f:real^1->real^N) a b c l.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b]
               ==> norm(f x - f y) <= l * norm(x - y)) /\
        (!x y. x IN interval[b,c] /\ y IN interval[b,c]
               ==> norm(f x - f y) <= l * norm(x - y))
        ==> !x y. x IN interval[a,c] /\ y IN interval[a,c]
                  ==> norm(f x - f y) <= l * norm(x - y)`;;

let LOCALLY_LIPSCHITZ_GEN = `!f:real^M->real^N s b.
        convex s /\
        (!x c. x IN s /\ b < c
               ==> eventually (\y. norm(f y - f x) <= c * norm(y - x))
                              (at x within s))
        ==> !x y. x IN s /\ y IN s ==> norm(f x - f y) <= b * norm(x - y)`;;

let LOCALLY_LIPSCHITZ = `!f:real^M->real^N s b.
        convex s /\
        (!x. x IN s
             ==> eventually (\y. norm(f y - f x) <= b * norm(y - x))
                            (at x within s))
        ==> !x y. x IN s /\ y IN s ==> norm(f x - f y) <= b * norm(x - y)`;;

(* ------------------------------------------------------------------------- *)
(* Some uncountability results for relevant sets.                            *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_SEGMENT = `(!a b:real^N. ~(a = b) ==> segment[a,b] =_c (:real)) /\
   (!a b:real^N. ~(a = b) ==> segment(a,b) =_c (:real))`;;

let UNCOUNTABLE_SEGMENT = `(!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment[a,b])) /\
   (!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment(a,b)))`;;

let CARD_EQ_PATH_CONNECTED = `!s a b:real^N.
        path_connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`;;

let UNCOUNTABLE_PATH_CONNECTED = `!s a b:real^N.
        path_connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`;;

let CARD_EQ_CONVEX = `!s a b:real^N.
        convex s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`;;

let UNCOUNTABLE_CONVEX = `!s a b:real^N.
        convex s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`;;

let CARD_EQ_NONEMPTY_INTERIOR = `!s:real^N->bool. ~(interior s = {}) ==> s =_c (:real)`;;

let UNCOUNTABLE_NONEMPTY_INTERIOR = `!s:real^N->bool. ~(interior s = {}) ==> ~(COUNTABLE s)`;;

let COUNTABLE_EMPTY_INTERIOR = `!s:real^N->bool. COUNTABLE s ==> interior s = {}`;;

let CONNECTED_FINITE_IFF_SING = `(!s:real^N->bool. connected s ==> (FINITE s <=> s = {} \/ ?a. s = {a}))`
and CONNECTED_FINITE_IFF_COUNTABLE = `(!s:real^N->bool. connected s ==> (FINITE s <=> COUNTABLE s))`
and CONNECTED_INFINITE_IFF_CARD_EQ = `(!s:real^N->bool. connected s ==> (INFINITE s <=> s =_c (:real)))`;;

let CONNECTED_FINITE_EQ_LOWDIM = `!s:real^N->bool. connected s ==> (FINITE s <=> aff_dim s <= &0)`;;

let CLOSED_AS_FRONTIER_OF_SUBSET = `!s:real^N->bool. closed s <=> ?t. t SUBSET s /\ s = frontier t`;;

let CLOSED_AS_FRONTIER = `!s:real^N->bool. closed s <=> ?t. s = frontier t`;;

let CARD_EQ_PERFECT_SET = `!s:real^N->bool.
        closed s /\ (!x. x IN s ==> x limit_point_of s) /\ ~(s = {})
        ==> s =_c (:real)`;;

let CARD_EQ_CLOSED = `!s:real^N->bool. closed s ==> s <=_c (:num) \/ s =_c (:real)`;;

let CONDENSATION_POINTS_EQ_EMPTY = `(!s:real^N->bool.
        {x | x condensation_point_of s} = {} <=> COUNTABLE s)`
and CARD_EQ_CONDENSATION_POINTS = `(!s:real^N->bool.
        {x | x condensation_point_of s} =_c (:real) <=> ~(COUNTABLE s))`;;

let UNCOUNTABLE_HAS_CONDENSATION_POINT = `!s:real^N->bool. ~COUNTABLE s ==> ?x. x condensation_point_of s`;;

(* ------------------------------------------------------------------------- *)
(* Density of sets with small complement, including irrationals.             *)
(* ------------------------------------------------------------------------- *)

let COSMALL_APPROXIMATION = `!s. ((:real) DIFF s) <_c (:real)
       ==> !x e. &0 < e ==> ?y. y IN s /\ abs(y - x) < e`;;

let COCOUNTABLE_APPROXIMATION = `!s. COUNTABLE((:real) DIFF s)
       ==> !x e. &0 < e ==> ?y. y IN s /\ abs(y - x) < e`;;

let OPEN_SET_COSMALL_COORDINATES = `!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> (:real) DIFF {x | P i x} <_c (:real))
       ==> !s:real^N->bool.
              open s /\ ~(s = {})
              ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i)`;;

let OPEN_SET_COCOUNTABLE_COORDINATES = `!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> COUNTABLE((:real) DIFF {x | P i x}))
       ==> !s:real^N->bool.
              open s /\ ~(s = {})
              ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i)`;;

let OPEN_SET_IRRATIONAL_COORDINATES = `!s:real^N->bool.
        open s /\ ~(s = {})
        ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> ~rational(x$i)`;;

let CLOSURE_COSMALL_COORDINATES = `!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> (:real) DIFF {x | P i x} <_c (:real))
       ==> closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> P i (x$i)} =
           (:real^N)`;;

let CLOSURE_COCOUNTABLE_COORDINATES = `!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> COUNTABLE((:real) DIFF {x | P i x}))
       ==> closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> P i (x$i)} =
           (:real^N)`;;

let CLOSURE_IRRATIONAL_COORDINATES = `closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> ~rational(x$i)} =
   (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Every path between distinct points contains an arc, and hence             *)
(* that path connection is equivalent to arcwise connection, for distinct    *)
(* points. The proof is based on Whyburn's "Topological Analysis".           *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_MONOTONE_IMAGE_INTERVAL = `!f:real^1->real^N.
       f continuous_on interval[vec 0,vec 1] /\
       (!y. connected {x | x IN interval[vec 0,vec 1] /\ f x = y}) /\
       ~(f(vec 1) = f(vec 0))
       ==> (IMAGE f (interval[vec 0,vec 1])) homeomorphic
           (interval[vec 0:real^1,vec 1])`;;

let PATH_CONTAINS_ARC = `!p:real^1->real^N a b.
        path p /\ pathstart p = a /\ pathfinish p = b /\ ~(a = b)
        ==> ?q. arc q /\ path_image q SUBSET path_image p /\
                pathstart q = a /\ pathfinish q = b`;;

let PATH_CONNECTED_ARCWISE = `!s:real^N->bool.
        path_connected s <=>
        !x y. x IN s /\ y IN s /\ ~(x = y)
              ==> ?g. arc g /\
                      path_image g SUBSET s /\
                      pathstart g = x /\
                      pathfinish g = y`;;

let ARC_CONNECTED_TRANS = `!g h:real^1->real^N.
        arc g /\ arc h /\
        pathfinish g = pathstart h /\ ~(pathstart g = pathfinish h)
        ==> ?i. arc i /\
                path_image i SUBSET (path_image g UNION path_image h) /\
                pathstart i = pathstart g /\
                pathfinish i = pathfinish h`;;

(* ------------------------------------------------------------------------- *)
(* Local connectedness and local path connectedness.                         *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONNECTED_SPACE_SUBTOPOLOGY_EUCLIDEAN = `!s:real^N->bool.
        locally_connected_space (subtopology euclidean s) <=>
        locally connected s`;;

let LOCALLY_CONNECTED = `(!s:real^N->bool.
        locally connected s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\
                      connected u /\
                      x IN u /\ u SUBSET v)`
and LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT = `(!s:real^N->bool.
        locally connected s <=>
        !t x. open_in (subtopology euclidean s) t /\ x IN t
              ==> open_in (subtopology euclidean s)
                          (connected_component t x))`;;

let LOCALLY_PATH_CONNECTED_SPACE_SUBTOPOLOGY_EUCLIDEAN = `!s:real^N->bool.
        locally_path_connected_space (subtopology euclidean s) <=>
        locally path_connected s`;;

let LOCALLY_PATH_CONNECTED = `(!s:real^N->bool.
        locally path_connected s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\
                      path_connected u /\
                      x IN u /\ u SUBSET v)`
and LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT = `(!s:real^N->bool.
        locally path_connected s <=>
        !t x. open_in (subtopology euclidean s) t /\ x IN t
              ==> open_in (subtopology euclidean s)
                          (path_component t x))`;;

let LOCALLY_CONNECTED_OPEN_COMPONENT = `!s:real^N->bool.
        locally connected s <=>
        !t c. open_in (subtopology euclidean s) t /\ c IN components t
              ==> open_in (subtopology euclidean s) c`;;

let LOCALLY_CONNECTED_IM_KLEINEN = `!s:real^N->bool.
      locally connected s <=>
      !v x. open_in (subtopology euclidean s) v /\ x IN v
            ==> ?u. open_in (subtopology euclidean s) u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?c. connected c /\ c SUBSET v /\ x IN c /\ y IN c`;;

let LOCALLY_PATH_CONNECTED_IM_KLEINEN = `!s:real^N->bool.
      locally path_connected s <=>
      !v x. open_in (subtopology euclidean s) v /\ x IN v
            ==> ?u. open_in (subtopology euclidean s) u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?p. path p /\ path_image p SUBSET v /\
                                pathstart p = x /\ pathfinish p = y`;;

let LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED = `!s:real^N->bool. locally path_connected s ==> locally connected s`;;

let LOCALLY_CONNECTED_COMPONENTS = `!s c:real^N->bool.
        locally connected s /\ c IN components s ==> locally connected c`;;

let LOCALLY_CONNECTED_CONNECTED_COMPONENT = `!s x:real^N.
        locally connected s
        ==> locally connected (connected_component s x)`;;

let LOCALLY_PATH_CONNECTED_COMPONENTS = `!s c:real^N->bool.
        locally path_connected s /\ c IN components s
        ==> locally path_connected c`;;

let LOCALLY_PATH_CONNECTED_CONNECTED_COMPONENT = `!s x:real^N.
        locally path_connected s
        ==> locally path_connected (connected_component s x)`;;

let OPEN_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool. open s ==> locally path_connected s`;;

let OPEN_IMP_LOCALLY_CONNECTED = `!s:real^N->bool. open s ==> locally connected s`;;

let LOCALLY_PATH_CONNECTED_UNIV = `locally path_connected (:real^N)`;;

let LOCALLY_CONNECTED_UNIV = `locally connected (:real^N)`;;

let OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED = `!s x:real^N.
        locally connected s
        ==> open_in (subtopology euclidean s) (connected_component s x)`;;

let OPEN_IN_COMPONENTS_LOCALLY_CONNECTED = `!s c:real^N->bool.
        locally connected s /\ c IN components s
        ==> open_in (subtopology euclidean s) c`;;

let OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED = `!s x:real^N.
        locally path_connected s
        ==> open_in (subtopology euclidean s) (path_component s x)`;;

let CLOSED_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED = `!s x:real^N.
        locally path_connected s
        ==> closed_in (subtopology euclidean s) (path_component s x)`;;

let CONVEX_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool. convex s ==> locally path_connected s`;;

let OPEN_IN_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool.
        open_in (subtopology euclidean (affine hull s)) s
        ==> locally path_connected s`;;

let OPEN_IN_CONNECTED_COMPONENTS = `!s c:real^N->bool.
        FINITE(components s) /\ c IN components s
        ==> open_in (subtopology euclidean s) c`;;

let FINITE_COMPONENTS_MEETING_COMPACT_SUBSET = `!k s:real^N->bool.
        compact k /\ locally connected s /\ k SUBSET s
        ==> FINITE {c | c IN components s /\ ~(c INTER k = {})}`;;

let FINITE_COMPONENTS = `!s:real^N->bool. compact s /\ locally connected s ==> FINITE(components s)`;;

let FINITE_LOCALLY_CONNECTED_CONNECTED_COMPONENTS = `!s:real^N->bool.
        compact s /\ locally connected s
        ==> FINITE {connected_component s x |x|  x IN s}`;;

let FINITE_LOCALLY_PATH_CONNECTED_PATH_COMPONENTS = `!s:real^N->bool.
        compact s /\ locally path_connected s
        ==> FINITE {path_component s x |x|  x IN s}`;;

let CONVEX_IMP_LOCALLY_CONNECTED = `!s:real^N->bool. convex s ==> locally connected s`;;

let HOMEOMORPHIC_LOCAL_CONNECTEDNESS = `!s t. s homeomorphic t ==> (locally connected s <=> locally connected t)`;;

let HOMEOMORPHISM_LOCAL_CONNECTEDNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (locally connected (IMAGE f k) <=> locally connected k)`;;

let HOMEOMORPHIC_LOCAL_PATH_CONNECTEDNESS = `!s t. s homeomorphic t
         ==> (locally path_connected s <=> locally path_connected t)`;;

let HOMEOMORPHISM_LOCAL_PATH_CONNECTEDNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (locally path_connected (IMAGE f k) <=> locally path_connected k)`;;

let LOCALLY_PATH_CONNECTED_TRANSLATION_EQ = `!a:real^N s. locally path_connected (IMAGE (\x. a + x) s) <=>
                locally path_connected s`;;

add_translation_invariants [LOCALLY_PATH_CONNECTED_TRANSLATION_EQ];;

let LOCALLY_CONNECTED_TRANSLATION_EQ = `!a:real^N s. locally connected (IMAGE (\x. a + x) s) <=>
                locally connected s`;;

add_translation_invariants [LOCALLY_CONNECTED_TRANSLATION_EQ];;

let LOCALLY_PATH_CONNECTED_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally path_connected (IMAGE f s) <=> locally path_connected s)`;;

add_linear_invariants [LOCALLY_PATH_CONNECTED_LINEAR_IMAGE_EQ];;

let LOCALLY_CONNECTED_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally connected (IMAGE f s) <=> locally connected s)`;;

add_linear_invariants [LOCALLY_CONNECTED_LINEAR_IMAGE_EQ];;

let LOCALLY_CONNECTED_QUOTIENT_IMAGE = `!f:real^M->real^N s.
      (!t. t SUBSET IMAGE f s
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                open_in (subtopology euclidean (IMAGE f s)) t)) /\
      locally connected s
      ==> locally connected (IMAGE f s)`;;

let LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE = `!f:real^M->real^N s.
      (!t. t SUBSET IMAGE f s
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                open_in (subtopology euclidean (IMAGE f s)) t)) /\
      locally path_connected s
      ==> locally path_connected (IMAGE f s)`;;


let LOCALLY_CONNECTED_CONTINUOUS_IMAGE_COMPACT = `!f:real^M->real^N s.
        locally connected s /\ compact s /\ f continuous_on s
        ==> locally connected (IMAGE f s)`;;

let LOCALLY_PATH_CONNECTED_CONTINUOUS_IMAGE_COMPACT = `!f:real^M->real^N s.
        locally path_connected s /\ compact s /\ f continuous_on s
        ==> locally path_connected (IMAGE f s)`;;

let LOCALLY_PATH_CONNECTED_PATH_IMAGE = `!p:real^1->real^N. path p ==> locally path_connected (path_image p)`;;

let LOCALLY_CONNECTED_PATH_IMAGE = `!p:real^1->real^N. path p ==> locally connected (path_image p)`;;

let LOCALLY_CONNECTED_LEFT_INVERTIBLE_IMAGE = `!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x) /\
        locally connected s
        ==> locally connected (IMAGE f s)`;;

let LOCALLY_CONNECTED_RIGHT_INVERTIBLE_IMAGE = `!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        IMAGE g (IMAGE f s) SUBSET s /\ (!x. x IN IMAGE f s ==> f(g x) = x) /\
        locally connected s
        ==> locally connected (IMAGE f s)`;;

let LOCALLY_PATH_CONNECTED_LEFT_INVERTIBLE_IMAGE = `!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x) /\
        locally path_connected s
        ==> locally path_connected (IMAGE f s)`;;

let LOCALLY_PATH_CONNECTED_RIGHT_INVERTIBLE_IMAGE = `!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        IMAGE g (IMAGE f s) SUBSET s /\ (!x. x IN IMAGE f s ==> f(g x) = x) /\
        locally path_connected s
        ==> locally path_connected (IMAGE f s)`;;

let LOCALLY_CONNECTED_PCROSS = `!s:real^M->bool t:real^N->bool.
        locally connected s /\ locally connected t
        ==> locally connected (s PCROSS t)`;;

let LOCALLY_PATH_CONNECTED_PCROSS = `!s:real^M->bool t:real^N->bool.
        locally path_connected s /\ locally path_connected t
        ==> locally path_connected (s PCROSS t)`;;

let LOCALLY_CONNECTED_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        locally connected (s PCROSS t) <=>
        s = {} \/ t = {} \/ locally connected s /\ locally connected t`;;

let LOCALLY_PATH_CONNECTED_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        locally path_connected (s PCROSS t) <=>
        s = {} \/ t = {} \/
        locally path_connected s /\ locally path_connected t`;;

let LOCALLY_CONNECTED_SUBREGION = `!s t c:real^N->bool.
        locally connected s /\ t SUBSET s /\
        connected c /\ open_in (subtopology euclidean t) c
        ==> ?c'. connected c' /\ open_in (subtopology euclidean s) c' /\
                 c = t INTER c'`;;

let CARD_EQ_OPEN_IN = `!u s:real^N->bool.
      locally connected u /\
      open_in (subtopology euclidean u) s /\
      (?x. x IN s /\ x limit_point_of u)
      ==> s =_c (:real)`;;

let CARD_EQ_OPEN_IN_AFFINE = `!u s:real^N->bool.
        affine u /\ ~(aff_dim u = &0) /\
        open_in (subtopology euclidean u) s /\ ~(s = {})
        ==> s =_c (:real)`;;

let SEPARATION_BY_CLOSED_INTERMEDIATES = `!u s:real^N->bool.
        ~connected(u DIFF s)
        ==> ?t. closed_in (subtopology euclidean u) t /\ t SUBSET s /\
                !c. closed_in (subtopology euclidean u) c /\
                    t SUBSET c /\ c SUBSET s
                    ==> ~connected(u DIFF c)`;;

let SEPARATION_BY_CLOSED_INTERMEDIATES_EQ = `!u s:real^N->bool.
        locally connected u
        ==> (~connected(u DIFF s) <=>
             ?t. closed_in (subtopology euclidean u) t /\ t SUBSET s /\
                 !c. closed_in (subtopology euclidean u) c /\
                     t SUBSET c /\ c SUBSET s
                     ==> ~connected(u DIFF c))`;;

let LOCALLY_CONNECTED_CLOSED_UNION_GEN = `!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        locally connected s /\ locally connected t
        ==> locally connected (s UNION t)`;;

let LOCALLY_CONNECTED_CLOSED_UNION = `!s t:real^N->bool.
        locally connected s /\ locally connected t /\ closed s /\ closed t
        ==> locally connected (s UNION t)`;;

let LOCALLY_CONNECTED_CLOSED_UNIONS = `!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> closed s /\ locally connected s)
        ==> locally connected (UNIONS f)`;;

let LOCALLY_CONNECTED_FROM_UNION_AND_INTER_GEN = `!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        locally connected (s UNION t) /\ locally connected (s INTER t)
        ==> locally connected s`;;

let LOCALLY_CONNECTED_FROM_UNION_AND_INTER = `!s t:real^N->bool.
        closed s /\ closed t /\
        locally connected (s UNION t) /\ locally connected (s INTER t)
        ==> locally connected s`;;

let LOCALLY_CONNECTED_CLOSURE_FROM_FRONTIER = `!s:real^N->bool.
        locally connected (frontier s) ==> locally connected (closure s)`;;

let PATH_CONNECTED_FROM_CLOSED_UNION_AND_INTER_LOCAL = `(!u s t:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        path_connected (s UNION t) /\
        path_connected (s INTER t)
        ==> path_connected s /\ path_connected t)`
and PATH_CONNECTED_FROM_OPEN_UNION_AND_INTER_LOCAL = `(!u s t:real^N->bool.
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t /\
        path_connected (s UNION t) /\
        path_connected (s INTER t)
        ==> path_connected s /\ path_connected t)`;;

let PATH_CONNECTED_FROM_CLOSED_UNION_AND_INTER = `!s t:real^N->bool.
        closed s /\
        closed t /\
        path_connected (s UNION t) /\
        path_connected (s INTER t)
        ==> path_connected s /\ path_connected t`;;

let PATH_CONNECTED_CLOSURE_FROM_FRONTIER = `!s:real^N->bool. path_connected(frontier s) ==> path_connected(closure s)`;;

let LOCALLY_PATH_CONNECTED_SUBREGION = `!s t c:real^N->bool.
        locally path_connected s /\ t SUBSET s /\
        path_connected c /\ open_in (subtopology euclidean t) c
        ==> ?c'. path_connected c' /\ open_in (subtopology euclidean s) c' /\
                 c = t INTER c'`;;

let LOCALLY_PATH_CONNECTED_FROM_UNION_AND_INTER_GEN = `!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        locally path_connected (s UNION t) /\ locally path_connected (s INTER t)
        ==> locally path_connected s`;;

let LOCALLY_PATH_CONNECTED_FROM_UNION_AND_INTER = `!s t:real^N->bool.
        closed s /\ closed t /\
        locally path_connected (s UNION t) /\
        locally path_connected (s INTER t)
        ==> locally path_connected s`;;

(* ------------------------------------------------------------------------- *)
(* Two uniform variants of local connectedness. ULC is an abbreviation for   *)
(* "uniformly locally connected"; FCCOVERABLE ("fine connected coverable")   *)
(* is more usually called "Property S" (Whyburn, Hocking & Young etc.)       *)
(* ------------------------------------------------------------------------- *)

(* Key bridge: submetric euclidean_metric s gives a metric on s where
   mtopology = subtopology euclidean s, mspace = s, mdist = dist *)

let SUBMETRIC_EUCLIDEAN_METRIC = `(!s:real^N->bool. mspace(submetric euclidean_metric s) = s) /\
   (!s:real^N->bool. mdist(submetric euclidean_metric s) = dist)`;;

let MTOPOLOGY_SUBMETRIC_EUCLIDEAN = `!s:real^N->bool.
     mtopology(submetric euclidean_metric s) = subtopology euclidean s`;;

(* Helper: connect mbounded/mdiameter through submetric euclidean_metric *)
let MBOUNDED_SUBMETRIC_EUCLIDEAN = `!s t:real^N->bool.
     t SUBSET s ==> (mbounded (submetric euclidean_metric s) t <=> bounded t)`;;

let MDIAMETER_SUBMETRIC_EUCLIDEAN = `!s t:real^N->bool.
     t SUBSET s
     ==> mdiameter (submetric euclidean_metric s) t = diameter t`;;

let CONNECTED_IN_SUBTOPOLOGY_EUCLIDEAN = `!s t:real^N->bool.
     connected_in (subtopology euclidean s) t <=> t SUBSET s /\ connected t`;;

let COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN = `!s t:real^N->bool.
     compact_in (subtopology euclidean s) t <=> t SUBSET s /\ compact t`;;

let CONNECTED_IN_SUBMETRIC_EUCLIDEAN = `!s t:real^N->bool.
     connected_in (mtopology(submetric euclidean_metric s)) t <=>
     t SUBSET s /\ connected t`;;

(* Helper bridges for compact/connected/locally_compact/locally_connected *)
let COMPACT_IN_SUBMETRIC_EUCLIDEAN_MSPACE = `!s:real^N->bool.
     compact_in (mtopology(submetric euclidean_metric s)) s <=> compact s`;;

let LOCALLY_CONNECTED_SPACE_SUBMETRIC_EUCLIDEAN = `!s:real^N->bool.
     locally_connected_space(mtopology(submetric euclidean_metric s)) <=>
     locally connected s`;;

let LOCALLY_COMPACT_SPACE_SUBMETRIC_EUCLIDEAN = `!s:real^N->bool.
     locally_compact_space(mtopology(submetric euclidean_metric s)) <=>
     locally compact s`;;

let CONNECTED_IN_SUBMETRIC_EUCLIDEAN_MSPACE = `!s:real^N->bool.
     connected_in (mtopology(submetric euclidean_metric s)) s <=>
     connected s`;;

(* Key bridge: fccoverable_in euclidean_metric s = Euclidean fccoverable_space *)
let FCCOVERABLE_IN_EUCLIDEAN_METRIC = `!s:real^N->bool.
     fccoverable_in euclidean_metric s <=>
     (!e. &0 < e ==> ?c. FINITE c /\ UNIONS c = s /\
                         !t. t IN c ==> connected t /\ bounded t /\
                                        diameter t <= e)`;;

(* Bridge: fccoverable_space on submetric euclidean_metric s = Euclidean form *)
let FCCOVERABLE_SPACE_SUBMETRIC_EUCLIDEAN = `!s:real^N->bool.
     fccoverable_space (submetric euclidean_metric s) <=>
     (!e. &0 < e ==> ?c. FINITE c /\ UNIONS c = s /\
                         !t. t IN c ==> connected t /\ bounded t /\
                                        diameter t <= e)`;;

(* Bridge: ulc_space on submetric euclidean_metric s *)
let ULC_SPACE_SUBMETRIC_EUCLIDEAN = `!s:real^N->bool.
     ulc_space (submetric euclidean_metric s) <=>
     (!e. &0 < e
          ==> ?d. &0 < d /\
                  !x y. x IN s /\ y IN s /\ dist(x,y) < d
                        ==> ?c. x IN c /\ y IN c /\ c SUBSET s /\
                                connected c /\ bounded c /\ diameter c <= e)`;;

(* FCCOVERABLE_IMP_LOCALLY_CONNECTED: derive from the metric version *)
let FCCOVERABLE_IMP_LOCALLY_CONNECTED = `!s:real^N->bool.
        (!e. &0 < e ==> ?c. FINITE c /\ UNIONS c = s /\
                            !t. t IN c ==> connected t /\ bounded t /\
                                           diameter t <= e)
        ==> locally connected s`;;

(* ULC_IMP_LOCALLY_CONNECTED: derive from the metric version *)
let ULC_IMP_LOCALLY_CONNECTED = `!s:real^N->bool.
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !x y. x IN s /\ y IN s /\ dist(x,y) < d
                           ==> ?c. x IN c /\ y IN c /\ c SUBSET s /\
                                   connected c /\
                                   bounded c /\ diameter c <= e)
        ==> locally connected s`;;

(* FCCOVERABLE_INTERMEDIATE_CLOSURE: derive from the metric version *)
let FCCOVERABLE_INTERMEDIATE_CLOSURE = `!s t:real^N->bool.
        s SUBSET t /\ t SUBSET closure s /\
        (!e. &0 < e ==> ?c. FINITE c /\ UNIONS c = s /\
                           !t. t IN c ==> connected t /\ bounded t /\
                                          diameter t <= e)
        ==> (!e. &0 < e ==> ?c. FINITE c /\ UNIONS c = t /\
                                !t. t IN c ==> connected t /\ bounded t /\
                                               diameter t <= e)`;;

(* COMPACT_LOCALLY_CONNECTED_IMP_ULC: derive from the metric version *)
let COMPACT_LOCALLY_CONNECTED_IMP_ULC = `!s:real^N->bool.
     compact s /\ locally connected s
     ==> (!e. &0 < e
              ==> ?d. &0 < d /\
                      !x y. x IN s /\ y IN s /\ dist(x,y) < d
                            ==> ?c. x IN c /\ y IN c /\ c SUBSET s /\
                                    connected c /\
                                    bounded c /\ diameter c <= e)`;;

(* COMPACT_LOCALLY_CONNECTED_IMP_ULC_ALT: derive from the above *)
let COMPACT_LOCALLY_CONNECTED_IMP_ULC_ALT = `!s:real^N->bool.
     compact s /\ locally connected s
     ==> !e. &0 < e
             ==> ?d. &0 < d /\ d < e /\
                     !x y. x IN s /\ y IN s /\ dist(x,y) < d
                           ==> ?c. connected c /\ x IN c /\ y IN c /\
                                   c SUBSET s INTER ball(x,e) INTER ball(y,e)`;;

(* BOUNDED_ULC_IMP_FCCOVERABLE: derive from the metric version *)
let BOUNDED_ULC_IMP_FCCOVERABLE = `!s:real^N->bool.
        bounded s /\
        (!e. &0 < e
            ==> ?d. &0 < d /\
                    !x y. x IN s /\ y IN s /\ dist(x,y) < d
                          ==> ?c. x IN c /\ y IN c /\ c SUBSET s /\
                                  connected c /\ bounded c /\ diameter c <= e)
        ==> (!e. &0 < e ==> ?c. FINITE c /\ UNIONS c = s /\
                           !t. t IN c ==> connected t /\ bounded t /\
                                          diameter t <= e)`;;

(* COMPACT_LOCALLY_CONNECTED_IMP_FCCOVERABLE: simple from above *)
let COMPACT_LOCALLY_CONNECTED_IMP_FCCOVERABLE = `!s:real^N->bool.
        compact s /\ locally connected s
        ==> !e. &0 < e ==> ?c. FINITE c /\ UNIONS c = s /\
                           !t. t IN c ==> connected t /\ bounded t /\
                                          diameter t <= e`;;

(* COMPACT_LOCALLY_CONNECTED_EQ_FCCCOVERABLE *)
let COMPACT_LOCALLY_CONNECTED_EQ_FCCCOVERABLE = `!s:real^N->bool.
       compact s /\ locally connected s <=>
       !e. &0 < e
           ==> ?c. FINITE c /\ UNIONS c = s /\
                   !t. t IN c ==> connected t /\ compact t /\ diameter t <= e`;;

(* ------------------------------------------------------------------------- *)
(* Localization of "property S"                                              *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_FCCOVERABLE = `!s u a:real^N.
      (!e. &0 < e
           ==> ?c. FINITE c /\ UNIONS c = s /\
                   !t. t IN c
                       ==> connected t /\ bounded t /\ diameter t <= e) /\
      open_in (subtopology euclidean s) u /\ a IN u
      ==> ?v. open_in (subtopology euclidean s) v /\ connected v /\
              a IN v /\ v SUBSET u /\
              !e. &0 < e
                  ==> ?c. FINITE c /\ UNIONS c = v /\
                          !t. t IN c
                              ==> connected t /\ bounded t /\ diameter t <= e`;;

let LOCALLY_FCCOVERABLE_ALT = `!s u a:real^N.
      locally compact s /\ locally connected s /\
      open_in (subtopology euclidean s) u /\ a IN u
      ==> ?v. open_in (subtopology euclidean s) v /\ connected v /\
              a IN v /\ v SUBSET u /\
              !e. &0 < e
                  ==> ?c. FINITE c /\ UNIONS c = v /\
                          !t. t IN c
                              ==> connected t /\ bounded t /\ diameter t <= e`;;

let LOCALLY_CONNECTED_CONTINUUM = `!s:real^N->bool.
        locally (\c. compact c /\ connected c /\ locally connected c) s <=>
        locally compact s /\ locally connected s`;;

let COMPACT_LOCALLY_CONNECTED_EQ_FCCCOVERABLE_ALT = `!s:real^N->bool.
        compact s /\ locally connected s <=>
        !e. &0 < e
            ==> ?c. FINITE c /\ UNIONS c = s /\
                    !t. t IN c
                        ==> connected t /\ compact t /\ locally connected t /\
                            diameter t <= e`;;

(* ------------------------------------------------------------------------- *)
(* Sufficient conditions for "semi-local connectedness"                      *)
(* ------------------------------------------------------------------------- *)

let SEMI_LOCALLY_CONNECTED = `!s:real^N->bool.
        connected s /\ locally compact s /\ locally connected s
        ==> !x v. open_in (subtopology euclidean s) v /\ x IN v
                  ==> ?u. open_in (subtopology euclidean s) u /\
                          x IN u /\ u SUBSET v /\
                          FINITE(components(s DIFF u))`;;

let SEMI_LOCALLY_CONNECTED_GEN = `!s:real^N->bool.
        FINITE(components s) /\ locally compact s /\ locally connected s
        ==> !x v. open_in (subtopology euclidean s) v /\ x IN v
                  ==> ?u. open_in (subtopology euclidean s) u /\
                          x IN u /\ u SUBSET v /\
                          FINITE(components(s DIFF u))`;;

let SEMI_LOCALLY_CONNECTED_COMPACT = `!s:real^N->bool.
        compact s /\ locally connected s
        ==> !x v. open_in (subtopology euclidean s) v /\ x IN v
                  ==> ?u. open_in (subtopology euclidean s) u /\
                          x IN u /\ u SUBSET v /\
                          FINITE(components(s DIFF u))`;;


(* ------------------------------------------------------------------------- *)
(* Euclidean specializations derived from general metric space theorems.      *)
(* These bridge theorems connect the metric space versions in metric.ml       *)
(* to the concrete Euclidean topology.                                        *)
(* ------------------------------------------------------------------------- *)

(* Euclidean version of FINITE_CONNECTED_COMPONENTS_COMPACT_LOCALLY_CONNECTED.
   Equivalent to the existing FINITE_COMPONENTS. *)
let FINITE_CONNECTED_COMPONENTS_COMPACT_LOCALLY_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        compact s /\ locally connected s
        ==> FINITE(components s)`;;

(* Euclidean: compact + connected + locally connected
   ==> path connected. *)
let COMPACT_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        compact s /\ connected s /\ locally connected s
        ==> path_connected s`;;

(* Euclidean: locally compact + connected + locally connected
   ==> path connected. *)
let LOCALLY_COMPACT_CONNECTED_IMP_PATH_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        locally compact s /\ connected s /\ locally connected s
        ==> path_connected s`;;

(* Euclidean: locally compact + locally connected
   ==> (path_connected <=> connected). *)
let LOCALLY_COMPACT_PATH_CONNECTED_EQ_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        locally compact s /\ locally connected s
        ==> (path_connected s <=> connected s)`;;

(* Euclidean: locally compact + locally connected
   ==> locally path connected. *)
let LOCALLY_COMPACT_LOCALLY_CONNECTED_IMP_LOCALLY_PATH_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        locally compact s /\ locally connected s
        ==> locally path_connected s`;;

(* Euclidean: locally compact
   ==> (locally path connected <=> locally connected). *)
let LOCALLY_COMPACT_LOCALLY_PATH_CONNECTED_EQ_LOCALLY_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        locally compact s
        ==> (locally path_connected s <=>
             locally connected s)`;;

(* In Euclidean R^N, complete subsets are locally compact.                   *)
(* Uses: complete => closed (in R^N) => locally compact.                     *)
let MCOMPLETE_IMP_LOCALLY_COMPACT_EUCLIDEAN = `!s:real^N->bool.
        mcomplete(submetric euclidean_metric s)
        ==> locally compact s`;;

(* In R^N, complete + connected + locally connected
   ==> path connected. *)
let MCOMPLETE_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        mcomplete(submetric euclidean_metric s) /\
        connected s /\ locally connected s
        ==> path_connected s`;;

(* In Euclidean R^N: complete + locally connected
   ==> locally path connected. *)
let MCOMPLETE_LOCALLY_CONNECTED_IMP_LOCALLY_PATH_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        mcomplete(submetric euclidean_metric s) /\
        locally connected s
        ==> locally path_connected s`;;

(* In Euclidean R^N: complete ==>
   (locally path connected <=> locally connected). *)
let MCOMPLETE_LOCALLY_PATH_CONNECTED_EQ_LOCALLY_CONNECTED_EUCLIDEAN =
  `!s:real^N->bool.
        mcomplete(submetric euclidean_metric s)
        ==> (locally path_connected s <=>
             locally connected s)`;;

(* G-delta ==> (locally path connected <=> locally connected).               *)
(* Optimal in R^N since gdelta <=> completely metrizable; the locally        *)
(* compact version follows since locally compact ==> gdelta.                 *)

let GDELTA_LOCALLY_PATH_CONNECTED_EQ_LOCALLY_CONNECTED = `!s:real^N->bool.
        gdelta s
        ==> (locally path_connected s <=>
             locally connected s)`;;

let GDELTA_LOCALLY_CONNECTED_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool.
        gdelta s /\ locally connected s
        ==> locally path_connected s`;;

(* Gdelta + connected + locally connected ==> path connected.               *)
(* Optimal Euclidean form of Menger's theorem                                *)
(* (gdelta is optimal since gdelta <==> completely metrizable in R^N).       *)

let GDELTA_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED = `!s:real^N->bool.
        gdelta s /\ connected s /\ locally connected s
        ==> path_connected s`;;

(* ------------------------------------------------------------------------- *)
(* Locally convex sets.                                                      *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONVEX = `!s:real^N->bool.
        locally convex s <=>
        !x. x IN s ==> ?u v. x IN u /\ u SUBSET v /\ v SUBSET s /\
                             open_in (subtopology euclidean s) u /\
                             convex v`;;

(* ------------------------------------------------------------------------- *)
(* Various sufficient conditions for continuity. These are mainly from the   *)
(* papers by Klee & Utz, Pervin & Levine, and Tanaka.                        *)
(* ------------------------------------------------------------------------- *)

let PROPER_MAP_TO_COMPACT = `!f:real^M->real^N s t.
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        compact t /\ IMAGE f s SUBSET t
        ==> f continuous_on s`;;

let CONTINUOUS_WITHIN_SEQUENTIALLY_COMPACT_MAP = `!f:real^M->real^N s x.
        (!c. c SUBSET s /\ compact c ==> compact(IMAGE f c)) /\ x IN s
        ==> (f continuous (at x within s) <=>
             !p y. (!n. p n IN s) /\ (p --> x) sequentially /\ (!n. f(p n) = y)
                   ==> f x = y)`;;

let COMPACT_CLOSED_POINTIMAGES_IMP_CONTINUOUS_ON = `!f:real^M->real^N s.
        (!c. c SUBSET s /\ compact c ==> compact(IMAGE f c)) /\
        (!y. closed_in (subtopology euclidean s) {x | x IN s /\ f x = y})
        ==> f continuous_on s`;;

let COMPACT_CONTINUOUS_IMAGE_EQ = `!f:real^M->real^N s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> (f continuous_on s <=>
             !t. compact t /\ t SUBSET s ==> compact(IMAGE f t))`;;

let CONTINUOUS_EQ_COMPACT_CONNECTED_PRESERVING_GEN = `!P f:real^M->real^N s.
     locally P s /\ (!c. P c ==> connected c)
     ==> (f continuous_on s <=>
          (!c. c SUBSET s /\ compact c ==> compact(IMAGE f c)) /\
          (!c. c SUBSET s /\ P c ==> connected(IMAGE f c)))`;;

let CONTINUOUS_EQ_COMPACT_CONNECTED_PRESERVING = `!f:real^M->real^N s.
        locally connected s
        ==> (f continuous_on s <=>
             (!c. c SUBSET s /\ compact c ==> compact(IMAGE f c)) /\
             (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c)))`;;

let CONTINUOUS_EQ_COMPACT_PATH_CONNECTED_PRESERVING = `!f:real^M->real^N s.
     locally path_connected s
     ==> (f continuous_on s <=>
          (!c. c SUBSET s /\ compact c ==> compact(IMAGE f c)) /\
          (!c. c SUBSET s /\ path_connected c ==> path_connected(IMAGE f c)))`;;

let CONNECTED_CLOSED_POINTIMAGES_IMP_CONTINUOUS_ON = `!f:real^N->real^1 s t.
        IMAGE f s SUBSET t /\
        locally connected s /\
        (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c)) /\
        (!y. closed_in (subtopology euclidean s) {x | x IN s /\ f x = y})
        ==> f continuous_on s`;;

let CONNECTED_CONNECTED_IMP_CLOSED_POINTIMAGES = `!f:real^M->real^N s.
        (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c)) /\
        (!y. connected {x | x IN s /\ f x = y})
        ==> !y. closed_in (subtopology euclidean s) {x | x IN s /\ f x = y}`;;

let CONNECTED_CONNECTED_POINTIMAGES_IMP_CONTINUOUS_ON = `!f:real^N->real^1 s t.
        IMAGE f s SUBSET t /\
        locally connected s /\
        (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c)) /\
        (!y. connected {x | x IN s /\ f x = y})
        ==> f continuous_on s`;;

let CLOSED_CLOSED_PREIMAGES_IMP_CONTINUOUS_ON = `!f:real^M->real^N s t.
        compact t /\
        (!y. closed_in (subtopology euclidean s) {x | x IN s /\ f x = y}) /\
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c))
        ==> f continuous_on s`;;

let CLOSED_CONNECTED_PREIMAGES_IMP_CONTINUOUS_ON = `!f:real^M->real^N s t.
        compact t /\
        (!y. connected {x | x IN s /\ f x = y}) /\
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
        (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c))
        ==> f continuous_on s`;;

let BICONNECTED_IMP_CONTINUOUS_ON = `!f:real^M->real^N s t.
        FINITE (components t) /\ locally compact t /\ locally connected t /\
        IMAGE f s = t /\
        (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c)) /\
        (!c. c SUBSET t /\ connected c ==> connected {x | x IN s /\ f x IN c})
        ==> f continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Topological characterizations of non-strict monotonicity.                 *)
(* ------------------------------------------------------------------------- *)

let MONOTONE_TOPOLOGICALLY_IMP = `!f s. (!c. connected c ==> connected {x | x IN s /\ f x IN c})
         ==> (!x y. x IN s /\ y IN s /\ drop x <= drop y
                     ==> drop(f x) <= drop(f y)) \/
              (!x y. x IN s /\ y IN s /\ drop x <= drop y
                     ==> drop(f y) <= drop(f x))`;;

let MONOTONE_TOPOLOGICALLY_EQ = `!f s. (!c. connected c ==> connected {x | x IN s /\ f x IN c}) <=>
         is_interval s /\
         ((!x y. x IN s /\ y IN s /\ drop x <= drop y
                 ==> drop(f x) <= drop(f y)) \/
          (!x y. x IN s /\ y IN s /\ drop x <= drop y
                 ==> drop(f y) <= drop(f x)))`;;

let MONOTONE_TOPOLOGICALLY = `!f s. is_interval s
         ==> ((!x y. x IN s /\ y IN s /\ drop x <= drop y
                     ==> drop(f x) <= drop(f y)) \/
              (!x y. x IN s /\ y IN s /\ drop x <= drop y
                     ==> drop(f y) <= drop(f x)) <=>
              !c. connected c ==> connected {x | x IN s /\ f x IN c})`;;

let MONOTONE_TOPOLOGICALLY_INTO_1D_EQ = `!f:real^N->real^1 s.
        f continuous_on s
        ==> ((!k. connected k ==> connected {x | x IN s /\ f x IN k}) <=>
             connected s /\ (!y. connected {x | x IN s /\ f x = y}))`;;

let MONOTONE_TOPOLOGICALLY_INTO_1D = `!f:real^N->real^1 s.
        connected s /\ f continuous_on s /\
        (!y. connected {x | x IN s /\ f x = y})
        ==> (!k. connected k ==> connected {x | x IN s /\ f x IN k})`;;

let MONOTONE_TOPOLOGICALLY_POINTS = `!f:real^1->real^1 s.
        is_interval s /\ f continuous_on s
        ==> ((!x y. x IN s /\ y IN s /\ drop x <= drop y
                    ==> drop(f x) <= drop(f y)) \/
             (!x y. x IN s /\ y IN s /\ drop x <= drop y
                    ==> drop(f y) <= drop(f x)) <=>
             !a. connected {x | x IN s /\ f x = a})`;;

let MONOTONE_TOPOLOGICALLY_POINTS_IMP = `!f s. f continuous_on s /\ is_interval s /\
         (!y. connected {x | x IN s /\ f x = y})
         ==> (!x y. x IN s /\ y IN s /\ drop x <= drop y
                    ==> drop(f x) <= drop(f y)) \/
             (!x y. x IN s /\ y IN s /\ drop x <= drop y
                    ==> drop(f y) <= drop(f x))`;;

let MONOTONE_IMP_HOMEOMORPHISM_1D = `!f s t.
        is_interval s /\ is_interval t /\ IMAGE f s = t /\
        ((!x y. x IN s /\ y IN s /\ drop x < drop y
                ==> drop(f x) < drop(f y)) \/
         (!x y. x IN s /\ y IN s /\ drop x < drop y
                ==> drop(f x) < drop(f y)))
        ==> ?g. homeomorphism(s,t) (f,g)`;;

let MONOTONE_CONNECTED_PREIMAGES_IMP_PROPER_MAP = `!f:real^M->real^N s t.
        IMAGE f s = t /\ locally compact s /\ locally connected t /\
        f continuous_on s /\
        (!y. compact {x | x IN s /\ f x = y}) /\
        (!c. c SUBSET t /\ connected c ==> connected {x | x IN s /\ f x IN c})
        ==> (!k. k SUBSET t /\ compact k
                 ==> compact {x | x IN s /\ f x IN k})`;;

let MONOTONE_INTO_1D_IMP_PROPER_MAP = `!f:real^N->real^1 s t.
      connected s /\ locally compact s /\
      f continuous_on s /\ IMAGE f s = t /\
      (!y. compact {x | x IN s /\ f x = y}) /\
      (!y. connected {x | x IN s /\ f x = y})
      ==> (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k})`;;

let MONOTONE_CONNECTED_PREIMAGES_IMP_PROPER_MAP_GEN = `!f:real^M->real^N s t.
        IMAGE f s = t /\ locally compact s /\ locally connected t /\
        (!c. c SUBSET s /\ compact c ==> compact(IMAGE f c)) /\
        (!y. compact {x | x IN s /\ f x = y}) /\
        (!c. c SUBSET t /\ connected c ==> connected {x | x IN s /\ f x IN c})
        ==> (!k. k SUBSET t /\ compact k
                 ==> compact {x | x IN s /\ f x IN k})`;;

(* ------------------------------------------------------------------------- *)
(* Sura-Bura's results about compact components of sets.                     *)
(* ------------------------------------------------------------------------- *)

let SURA_BURA_COMPACT = `!s c:real^N->bool.
        compact s /\ c IN components s
        ==> c = INTERS {t | c SUBSET t /\
                            open_in (subtopology euclidean s) t /\
                            closed_in (subtopology euclidean s) t}`;;

let SURA_BURA_CLOPEN_SUBSET = `!s c u:real^N->bool.
        locally compact s /\
        c IN components s /\ compact c /\
        open u /\ c SUBSET u
        ==> ?k. open_in (subtopology euclidean s) k /\ compact k /\
                c SUBSET k /\ k SUBSET u`;;

let SURA_BURA_CLOPEN_SUBSET_ALT = `!s c u:real^N->bool.
        locally compact s /\
        c IN components s /\ compact c /\
        open_in (subtopology euclidean s) u /\ c SUBSET u
        ==> ?k. open_in (subtopology euclidean s) k /\ compact k /\
                c SUBSET k /\ k SUBSET u`;;

let SURA_BURA = `!s c:real^N->bool.
        locally compact s /\ c IN components s /\ compact c
        ==> c = INTERS {k | c SUBSET k /\ compact k /\
                            open_in (subtopology euclidean s) k}`;;

let COMPONENT_CLOPEN_HAUSDIST_EXPLICIT = `!s c:real^N->bool e.
        &0 < e /\
        locally compact s /\
        c IN components s /\
        compact c
        ==> ?k. open_in (subtopology euclidean s) k /\
                compact k /\ c SUBSET k /\
                k SUBSET {x + d | x IN c /\ d IN ball(vec 0,e)}`;;

let COMPONENT_CLOPEN_HAUSDIST = `!s c:real^N->bool e.
        &0 < e /\
        locally compact s /\
        c IN components s /\
        compact c
        ==> ?k. open_in (subtopology euclidean s) k /\
                compact k /\ c SUBSET k /\ hausdist(c,k) < e`;;

let COMPONENT_INTERMEDIATE_CLOPEN = `!s t u:real^N->bool.
        t IN components s /\
        open_in (subtopology euclidean s) u /\
        t SUBSET u /\
        (dimindex(:N) = 1 \/ (?r:real^1->bool. s homeomorphic r) \/
         locally connected s \/
         (locally compact s /\ compact t))
        ==> ?c. closed_in (subtopology euclidean s) c /\
                open_in (subtopology euclidean s) c /\
                t SUBSET c /\ c SUBSET u`;;

let COMPONENTS_SUBSETS_CLOPEN_PARTITION = `!u s:real^N->bool.
        locally compact s /\
        FINITE u /\ ~(u = {}) /\ u SUBSET components s /\
        (!c. c IN u ==> compact c)
        ==> ?f. (!c. c IN u
                     ==> open_in (subtopology euclidean s) (f c) /\
                         closed_in (subtopology euclidean s) (f c) /\
                         c SUBSET f(c)) /\
                pairwise (\c c'. ~(f(c) = f(c'))) u /\
                pairwise (\c c'. DISJOINT (f c) (f c')) u /\
                UNIONS (IMAGE f u) = s`;;

(* ------------------------------------------------------------------------- *)
(* Relations between components and path components.                         *)
(* ------------------------------------------------------------------------- *)

let OPEN_CONNECTED_COMPONENT = `!s x:real^N. open s ==> open(connected_component s x)`;;

let IN_CLOSURE_CONNECTED_COMPONENT = `!x y:real^N.
        x IN s /\ open s
        ==> (x IN closure(connected_component s y) <=>
             x IN connected_component s y)`;;

let PATH_COMPONENT_SUBSET_CONNECTED_COMPONENT = `!s x:real^N. (path_component s x) SUBSET (connected_component s x)`;;

let PATH_COMPONENT_EQ_CONNECTED_COMPONENT = `!s x:real^N.
        locally path_connected s
        ==> (path_component s x = connected_component s x)`;;

let PATH_COMPONENT_IMP_CONNECTED_COMPONENT = `!s a b:real^N. path_component s a b ==> connected_component s a b`;;

let LOCALLY_PATH_CONNECTED_PATH_COMPONENT = `!s x:real^N.
        locally path_connected s
        ==> locally path_connected (path_component s x)`;;

let OPEN_PATH_CONNECTED_COMPONENT = `!s x:real^N. open s ==> path_component s x = connected_component s x`;;

let PATH_CONNECTED_EQ_CONNECTED_LPC = `!s. locally path_connected s ==> (path_connected s <=> connected s)`;;

let PATH_CONNECTED_EQ_CONNECTED = `!s. open s ==> (path_connected s <=> connected s)`;;

let CONNECTED_OPEN_PATH_CONNECTED = `!s:real^N->bool. open s /\ connected s ==> path_connected s`;;

let CONNECTED_OPEN_ARC_CONNECTED = `!s:real^N->bool.
      open s /\ connected s
      ==> !x y. x IN s /\ y IN s
                ==> x = y \/
                    ?g. arc g /\
                        path_image g SUBSET s /\
                        pathstart g = x /\
                        pathfinish g = y`;;

let OPEN_COMPONENTS = `!u:real^N->bool s. open u /\ s IN components u ==> open s`;;

let COMPONENTS_OPEN_UNIQUE = `!f:(real^N->bool)->bool s.
        (!c. c IN f ==> open c /\ connected c /\ ~(c = {})) /\
        pairwise DISJOINT f /\ UNIONS f = s
        ==> components s = f`;;

let COUNTABLE_OPEN_COMPONENTS = `!s:real^N->bool. open s ==> COUNTABLE(components s)`;;

let COUNTABLE_OPEN_CONNECTED_COMPONENTS = `!s t:real^N->bool.
        open s ==> COUNTABLE {connected_component s x | x IN t}`;;

let CONTINUOUS_ON_COMPONENTS = `!f:real^M->real^N s.
        locally connected s /\ (!c. c IN components s ==> f continuous_on c)
        ==> f continuous_on s`;;

let CONTINUOUS_ON_COMPONENTS_EQ = `!f s. locally connected s
         ==> (f continuous_on s <=>
              !c. c IN components s ==> f continuous_on c)`;;

let CONTINUOUS_ON_COMPONENTS_OPEN = `!f:real^M->real^N s.
        open s /\ (!c. c IN components s ==> f continuous_on c)
        ==> f continuous_on s`;;

let CONTINUOUS_ON_COMPONENTS_OPEN_EQ = `!f s. open s
         ==> (f continuous_on s <=>
              !c. c IN components s ==> f continuous_on c)`;;

let CLOSED_IN_UNION_COMPLEMENT_COMPONENTS = `!u s:real^N->bool c.
        locally connected u /\
        closed_in (subtopology euclidean u) s /\ c SUBSET components(u DIFF s)
        ==> closed_in (subtopology euclidean u) (s UNION UNIONS c)`;;

let CLOSED_UNION_COMPLEMENT_COMPONENTS = `!s c. closed s /\ c SUBSET components((:real^N) DIFF s)
         ==> closed(s UNION UNIONS c)`;;

let CLOSED_IN_UNION_COMPLEMENT_COMPONENT = `!u s c:real^N->bool.
        locally connected u /\
        closed_in (subtopology euclidean u) s /\
        c IN components(u DIFF s)
        ==> closed_in (subtopology euclidean u) (s UNION c)`;;

let CLOSED_UNION_COMPLEMENT_COMPONENT = `!s c. closed s /\ c IN components((:real^N) DIFF s) ==> closed(s UNION c)`;;

let NONSEPARATED_CLOSED_COMPLEMENT_COMPONENTS = `!u s:real^N->bool c.
        connected u /\ locally connected u /\
        closed_in (subtopology euclidean u) s /\ ~(s = {}) /\
        c SUBSET components(u DIFF s) /\ ~(c = {})
        ==> ~(s INTER closure(UNIONS c) = {})`;;

let COUNTABLE_CONNECTED_COMPONENTS = `!s:real^N->bool t.
    locally connected s ==> COUNTABLE {connected_component s x | x IN t}`;;

let COUNTABLE_PATH_COMPONENTS = `!s:real^N->bool t.
    locally path_connected s ==> COUNTABLE {path_component s x | x IN t}`;;

let COUNTABLE_COMPONENTS = `!s:real^N->bool. locally connected s ==> COUNTABLE(components s)`;;

let FRONTIER_MINIMAL_SEPARATING_CLOSED = `!s c. closed s /\ ~connected((:real^N) DIFF s) /\
         (!t. closed t /\ t PSUBSET s ==> connected((:real^N) DIFF t)) /\
         c IN components ((:real^N) DIFF s)
         ==> frontier c = s`;;

let FRONTIER_MINIMAL_SEPARATING_CLOSED_POINTWISE = `!s a b. closed s /\ ~(a IN s) /\
           ~connected_component ((:real^N) DIFF s) a b /\
           (!t. closed t /\ t PSUBSET s
                ==> connected_component((:real^N) DIFF t) a b)
           ==> frontier(connected_component ((:real^N) DIFF s) a) = s`;;

(* ------------------------------------------------------------------------- *)
(* "Boundary bumping theorems" and relatives.                                *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_COMPONENT_DIFF_NONSEPARATED = `!s t c:real^N->bool.
        compact s /\ connected s /\ t SUBSET s /\ ~(t = {}) /\
        c IN components(s DIFF t)
        ==> ~(closure(c) INTER closure(t) = {})`;;

let CONNECTED_COMPONENT_DIFF_NONSEPARATED_ALT = `!s t c:real^N->bool.
        compact s /\ connected s /\ t PSUBSET s /\ c IN components t
        ==> ~(closure(c) INTER closure(s DIFF t) = {})`;;

let CONNECTED_COMPONENT_DIFF_CLOSED_NONSEPARATED = `!s t c:real^N->bool.
        compact s /\ connected s /\ closed t /\ t SUBSET s /\ ~(t = {}) /\
        c IN components(s DIFF t)
        ==> ~(closure(c) INTER t = {})`;;

let NONSEPARATED_CLOSED_COMPLEMENT_COMPONENT = `!u s c:real^N->bool.
        (compact u \/ locally connected u) /\
        connected u /\
        closed_in (subtopology euclidean u) s /\ ~(s = {}) /\
        c IN components(u DIFF s)
        ==> ~(s INTER closure c = {})`;;

let CONNECTED_EQ_NONSEPARATED_CLOSED_COMPLEMENT_COMPONENT = `!u s:real^N->bool.
        (compact u \/ locally connected u) /\
        closed_in (subtopology euclidean u) s /\
        connected s /\
        ~(s = {})
        ==> (connected u <=>
             !c. c IN components(u DIFF s) ==> ~(s INTER closure c = {}))`;;

let CONNECTED_EQ_COMPONENT_DIFF_CLOSED_NONSEPARATED = `!s:real^N->bool t.
        compact s /\ closed t /\ connected t /\ t SUBSET s /\ ~(t = {})
        ==> (connected s <=>
             !c. c IN components (s DIFF t) ==> ~(closure c INTER t = {}))`;;

let CONNECTED_EQ_COMPONENT_DELETE_NONSEPARATED = `!s:real^N->bool a:real^N.
        (compact s \/ locally connected s \/ FINITE(components(s DELETE a))) /\
        a IN s
        ==> (connected s <=>
             !c. c IN components (s DELETE a) ==> a IN closure c)`;;

let CONNECTED_INSERT_COMPACT = `!s:real^N->bool a:real^N.
        compact(a INSERT s)
        ==> (connected(a INSERT s) <=>
             !c. c IN components s ==> a IN closure c)`;;

let BOUNDARY_BUMPING_THEOREM_EUCLIDEAN = `!s t c:real^N->bool.
        compact s /\ connected s /\ t PSUBSET s /\ c IN components t
        ==> ~(closure(c) INTER closure(t) INTER closure(s DIFF t) = {})`;;

let BOUNDARY_BUMPING_THEOREM_EUCLIDEAN_CLOSED = `!s t c:real^N->bool.
      compact s /\ connected s /\ closed t /\ t PSUBSET s /\ c IN components t
      ==> ~(c INTER closure t INTER closure(s DIFF t) = {})`;;

let BOUNDARY_BUMPING_THEOREM_EUCLIDEAN_ALT = `!s t c:real^N->bool.
      compact s /\ connected s /\ open_in (subtopology euclidean s) t /\
      t PSUBSET s /\ c IN components(closure t)
      ==> ~(c INTER (s DIFF t) = {})`;;

let BOUNDARY_BUMPING_THEOREM_EUCLIDEAN_OPEN = `!s t c:real^N->bool.
      (compact s \/ locally connected s) /\
      connected s /\
      open_in (subtopology euclidean s) t /\
      t PSUBSET s /\ c IN components t
      ==> ~(closure c INTER (s DIFF t) = {})`;;

let BOUNDARY_BUMPING_THEOREM_EUCLIDEAN_OPEN_ALT = `!s t c:real^N->bool.
      (compact s \/ locally connected s) /\
      connected s /\ open_in (subtopology euclidean s) t /\
      t PSUBSET s /\ c IN components t
      ==> ~(closure c INTER (closure t DIFF t) = {})`;;

let CONTINUUM_UNION_COMPONENTS_INTERMEDIATE_COMPLEMENT = `!s t u c:real^N->bool.
        compact s /\ connected s /\ compact t /\ s SUBSET t /\
        compact u /\ connected u /\ t SUBSET u /\
        c IN components(u DIFF t) /\ closure c DIFF c SUBSET s
        ==> compact(c UNION s) /\ connected(c UNION s)`;;

let CONTINUUM_UNION_COMPONENTS_COMPLEMENT = `!s u c:real^N->bool.
        compact s /\ connected s /\ compact u /\ connected u /\ s SUBSET u /\
        c IN components(u DIFF s) /\ closure c DIFF c SUBSET s
        ==> compact(c UNION s) /\ connected(c UNION s)`;;

(* ------------------------------------------------------------------------- *)
(* More compact component properties via the notion of "well-chained".       *)
(* ------------------------------------------------------------------------- *)

let WELLCHAINED_ELEMENTS_EUCLIDEAN = `!s:real^N->bool a b e.
        (?p n. p 0 = a /\ p n = b /\
               (!i. i <= n ==> p i IN s) /\
               (!i. i < n ==> dist(p i,p(SUC i)) < e)) <=>
        a IN s /\ b IN s /\
        (!c. c SUBSET s /\ a IN c /\
             (!x y. x IN c /\ y IN s /\ dist(x,y) < e ==> y IN c)
             ==> b IN c)`;;

let WELLCHAINED_SETS_EUCLIDEAN = `!s:real^N->bool e.
     (!a b. a IN s /\ b IN s
            ==> ?p n. p 0 = a /\ p n = b /\
                      (!i. i <= n ==> p i IN s) /\
                      (!i. i < n ==> dist(p i,p(SUC i)) < e)) <=>
     (!c. c SUBSET s /\ ~(c = {}) /\
          (!x y. x IN c /\ y IN s /\ dist(x,y) < e ==> y IN c)
          ==> c = s)`;;

let CONNECTED_IMP_WELLCHAINED = `!s e a b:real^N.
        connected s /\ &0 < e /\ a IN s /\ b IN s
        ==> ?p n. p 0 = a /\ p n = b /\
                  (!i. i <= n ==> p i IN s) /\
                  (!i. i < n ==> dist(p i,p(SUC i)) < e)`;;

let CONNECTED_COMPONENT_IMP_WELLCHAINED = `!s a b:real^N e.
        &0 < e /\ connected_component s a b
        ==> ?p n. p 0 = a /\ p n = b /\
                  (!i. i <= n ==> p i IN s) /\
                  (!i. i < n ==> dist(p i,p (SUC i)) < e)`;;

let CONNECTED_EQ_WELLCHAINED = `!s:real^N->bool.
        compact s
        ==> (connected s <=>
             !e. &0 < e
                 ==> !a b. a IN s /\ b IN s
                           ==> ?p n. p 0 = a /\ p n = b /\
                                     (!i. i <= n ==> p i IN s) /\
                                     (!i. i < n ==> dist(p i,p(SUC i)) < e))`;;

let CONNECTED_COMPONENT_EQ_WELLCHAINED = `!s a b:real^N.
        compact s
        ==> (connected_component s a b <=>
             a IN s /\ b IN s /\
             !e. &0 < e
                 ==> ?p n. p 0 = a /\ p n = b /\
                           (!i. i <= n ==> p i IN s) /\
                           (!i. i < n ==> dist(p i,p(SUC i)) < e))`;;

let WELLCHAINED_INTERS_EUCLIDEAN = `!s:num->(real^N->bool) d e.
        d < e /\
        (!m. compact (s m)) /\
        (!m. s(SUC m) SUBSET s m) /\
        (!m a b.
             a IN s m /\ b IN s m
             ==> ?p n. p 0 = a /\ p n = b /\
                        (!i. i <= n ==> p i IN s m) /\
                        (!i. i < n ==> dist(p i,p (SUC i)) < d))
        ==> !a b. a IN INTERS {s m | m IN (:num)} /\
                  b IN INTERS {s m | m IN (:num)}
                  ==> ?p n. p 0 = a /\ p n = b /\
                            (!i. i <= n ==> p i IN INTERS {s m | m IN (:num)}) /\
                            (!i. i < n ==> dist(p i,p (SUC i)) < e)`;;

let COMPACT_PARTITION_CONTAINING_CLOSED = `!s t t':real^N->bool.
        compact s /\ closed t /\ closed t' /\ t SUBSET s /\ t' SUBSET s /\
        (!c. c IN components s ==> c INTER t = {} \/ c INTER t' = {})
        ==> ?k k'. compact k /\ compact k' /\ t SUBSET k /\ t' SUBSET k' /\
                   DISJOINT k k' /\ k UNION k' = s`;;

let COMPACT_PARTITION_CONTAINING_POINTS = `!s a b:real^N.
        compact s /\ a IN s /\ b IN s /\ ~(connected_component s a b)
        ==> ?k k'. compact k /\ compact k' /\ a IN k /\ b IN k' /\
                   DISJOINT k k' /\ k UNION k' = s`;;

let CONNECTED_COMPONENT_LIMIT = `!s x y a b:real^N.
        compact s /\ (x --> a) sequentially /\ (y --> b) sequentially /\
        eventually (\n. connected_component s (x n) (y n)) sequentially
        ==> connected_component s a b`;;

let CLOSED_UNIONS_COMPONENTS_MEETING_CLOSED = `!s t:real^N->bool.
        compact s /\ closed t
        ==> closed (UNIONS {c | c IN components s /\ ~(c INTER t = {})})`;;

let ARBITRARILY_SMALL_CONTINUUM = `!s u a:real^N.
        connected s /\ locally compact s /\ open u /\ {a} PSUBSET s /\ a IN u
        ==> ?c. {a} PSUBSET c /\ c SUBSET s /\ c SUBSET u /\
                compact c /\ connected c`;;

let BOUNDARY_BUMPING_THEOREM_EUCLIDEAN_INTER = `!s u c:real^N->bool.
        connected s /\ locally compact s /\
        open u /\ ~(s SUBSET u) /\ compact(s INTER closure u) /\
        c IN components(s INTER closure u)
        ==> ~(c INTER frontier u = {})`;;

let BOUNDARY_BUMPING_THEOREM_EUCLIDEAN_INTER_ALT = `!s u c:real^N->bool.
        connected s /\ locally compact s /\
        open u /\ ~(s INTER u = {}) /\ ~(s SUBSET u) /\
        compact(s INTER closure u) /\
        c IN components(s INTER u)
        ==> ?x. x IN frontier u /\ x limit_point_of c`;;

(* ------------------------------------------------------------------------- *)
(* Equivalence of LC and LPC for locally connected sets.                     *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_COMPACT_CONNECTED_IMP_PATH_CONNECTED = `!s:real^N->bool.
        locally compact s /\ locally connected s /\ connected s
        ==> path_connected s`;;

let LOCALLY_COMPACT_PATH_CONNECTED_EQ_CONNECTED = `!s:real^N->bool.
        locally compact s /\ locally connected s
        ==> (path_connected s <=> connected s)`;;

let LOCALLY_COMPACT_LOCALLY_CONNECTED_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool.
        locally compact s /\ locally connected s
        ==> locally path_connected s`;;

let LOCALLY_COMPACT_LOCALLY_PATH_CONNECTED_EQ_LOCALLY_CONNECTED = `!s:real^N->bool.
     locally compact s ==> (locally path_connected s <=> locally connected s)`;;

let LOCALLY_PATH_CONNECTED_CLOSURE_FROM_FRONTIER = `!s:real^N->bool.
        locally connected (frontier s)
        ==> locally path_connected (closure s)`;;

(* ------------------------------------------------------------------------- *)
(* If two points are separated by a closed set, there's a minimal one.       *)
(* ------------------------------------------------------------------------- *)

let CLOSED_IRREDUCIBLE_SEPARATOR = `!s a b:real^N.
      closed s /\ ~connected_component ((:real^N) DIFF s) a b
      ==> ?t. t SUBSET s /\ closed t /\ ~(t = {}) /\
              ~connected_component ((:real^N) DIFF t) a b /\
              !u. u PSUBSET t ==> connected_component ((:real^N) DIFF u) a b`;;

(* ------------------------------------------------------------------------- *)
(* Lower bound on norms within segment between vectors.                      *)
(* Could have used these for connectedness results below, in fact.           *)
(* ------------------------------------------------------------------------- *)

let NORM_SEGMENT_LOWERBOUND = `!a b x:real^N r d.
        &0 < r /\
        norm(a) = r /\ norm(b) = r /\ x IN segment[a,b] /\
        a dot b = d * r pow 2
        ==> sqrt((&1 - abs d) / &2) * r <= norm(x)`;;

(* ------------------------------------------------------------------------- *)
(* Special case of orthogonality (could replace 2 by sqrt(2)).               *)
(* ------------------------------------------------------------------------- *)

let NORM_SEGMENT_ORTHOGONAL_LOWERBOUND = `!a b:real^N x r.
        r <= norm(a) /\ r <= norm(b) /\ orthogonal a b /\ x IN segment[a,b]
        ==> r / &2 <= norm(x)`;;

(* ------------------------------------------------------------------------- *)
(* Accessibility of frontier points.                                         *)
(* ------------------------------------------------------------------------- *)

let DENSE_ACCESSIBLE_FRONTIER_POINTS = `!s:real^N->bool v.
        open s /\ open_in (subtopology euclidean (frontier s)) v /\ ~(v = {})
        ==> ?g. arc g /\
                IMAGE g (interval [vec 0,vec 1] DELETE vec 1) SUBSET s /\
                pathstart g IN s /\ pathfinish g IN v`;;

let DENSE_ACCESSIBLE_FRONTIER_POINTS_CONNECTED = `!s:real^N->bool v x.
        open s /\ connected s /\ x IN s /\
        open_in (subtopology euclidean (frontier s)) v /\ ~(v = {})
        ==> ?g. arc g /\
                IMAGE g (interval [vec 0,vec 1] DELETE vec 1) SUBSET s /\
                pathstart g = x /\ pathfinish g IN v`;;

let DENSE_ACCESSIBLE_FRONTIER_POINT_PAIRS = `!s u v:real^N->bool.
         open s /\ connected s /\
         open_in (subtopology euclidean (frontier s)) u /\
         open_in (subtopology euclidean (frontier s)) v /\
         ~(u = {}) /\ ~(v = {}) /\ ~(u = v)
         ==> ?g. arc g /\
                 pathstart g IN u /\ pathfinish g IN v /\
                 IMAGE g (interval(vec 0,vec 1)) SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* Some simple positive connection theorems.                                 *)
(* ------------------------------------------------------------------------- *)

let PATH_CONNECTED_CONVEX_DIFF_CARD_LT = `!u s:real^N->bool.
    convex u /\ ~(collinear u) /\ s <_c (:real) ==> path_connected(u DIFF s)`;;

let CONNECTED_CONVEX_DIFF_CARD_LT = `!u s. convex u /\ ~collinear u /\ s <_c (:real) ==> connected(u DIFF s)`;;

let PATH_CONNECTED_CONVEX_DIFF_COUNTABLE = `!u s. convex u /\ ~collinear u /\ COUNTABLE s ==> path_connected(u DIFF s)`;;

let CONNECTED_CONVEX_DIFF_COUNTABLE = `!u s. convex u /\ ~collinear u /\ COUNTABLE s ==> connected(u DIFF s)`;;

let PATH_CONNECTED_PUNCTURED_CONVEX = `!s a:real^N. convex s /\ ~(aff_dim s = &1) ==> path_connected(s DELETE a)`;;

let CONNECTED_PUNCTURED_CONVEX = `!s a:real^N. convex s /\ ~(aff_dim s = &1) ==> connected(s DELETE a)`;;

let PATH_CONNECTED_COMPLEMENT_CARD_LT = `!s. 2 <= dimindex(:N) /\ s <_c (:real)
       ==> path_connected((:real^N) DIFF s)`;;

let PATH_CONNECTED_CONNECTED_DIFF = `!s t:real^N->bool.
        connected s /\ s SUBSET closure(s DIFF t) /\
        (!x. x IN s
             ==> ?u. x IN u /\ open_in (subtopology euclidean s) u /\
                     path_connected(u DIFF t))
        ==> path_connected(s DIFF t)`;;

let PATH_CONNECTED_OPEN_IN_DIFF_CARD_LT = `!s t:real^N->bool.
        connected s /\ open_in (subtopology euclidean (affine hull s)) s /\
        ~collinear s /\ t <_c (:real)
        ==> path_connected(s DIFF t)`;;

let CONNECTED_OPEN_IN_DIFF_CARD_LT = `!s t:real^N->bool.
        connected s /\ open_in (subtopology euclidean (affine hull s)) s /\
        ~collinear s /\ t <_c (:real)
        ==> connected(s DIFF t)`;;

let PATH_CONNECTED_OPEN_DIFF_CARD_LT = `!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ t <_c (:real)
        ==> path_connected(s DIFF t)`;;

let CONNECTED_OPEN_DIFF_CARD_LT = `!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ t <_c (:real)
        ==> connected(s DIFF t)`;;

let PATH_CONNECTED_OPEN_DIFF_COUNTABLE = `!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ COUNTABLE t
        ==> path_connected(s DIFF t)`;;

let CONNECTED_OPEN_DIFF_COUNTABLE = `!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ COUNTABLE t
        ==> connected(s DIFF t)`;;

let PATH_CONNECTED_OPEN_DELETE = `!s a:real^N. 2 <= dimindex(:N) /\ open s /\ connected s
                ==> path_connected(s DELETE a)`;;

let CONNECTED_OPEN_DELETE = `!s a:real^N. 2 <= dimindex(:N) /\ open s /\ connected s
                ==> connected(s DELETE a)`;;

let PATH_CONNECTED_PUNCTURED_UNIVERSE = `!a. 2 <= dimindex(:N) ==> path_connected((:real^N) DIFF {a})`;;

let CONNECTED_PUNCTURED_UNIVERSE = `!a. 2 <= dimindex(:N) ==> connected((:real^N) DIFF {a})`;;

let PATH_CONNECTED_PUNCTURED_BALL = `!a:real^N r. 2 <= dimindex(:N) ==> path_connected(ball(a,r) DELETE a)`;;

let CONNECTED_PUNCTURED_BALL = `!a:real^N r. 2 <= dimindex(:N) ==> connected(ball(a,r) DELETE a)`;;

let PATH_CONNECTED_PUNCTURED_CBALL = `!a:real^N r. 2 <= dimindex(:N) ==> path_connected(cball(a,r) DELETE a)`;;

let CONNECTED_PUNCTURED_CBALL = `!a:real^N r. 2 <= dimindex(:N) ==> connected(cball(a,r) DELETE a)`;;

let PATH_CONNECTED_SPHERE = `!a:real^N r. 2 <= dimindex(:N) ==> path_connected(sphere(a,r))`;;

let CONNECTED_SPHERE = `!a:real^N r. 2 <= dimindex(:N) ==> connected(sphere(a,r))`;;

let CONNECTED_SPHERE_EQ = `!a:real^N r. connected(sphere(a,r)) <=> 2 <= dimindex(:N) \/ r <= &0`;;

let PATH_CONNECTED_SPHERE_EQ = `!a:real^N r. path_connected(sphere(a,r)) <=> 2 <= dimindex(:N) \/ r <= &0`;;

let FINITE_SPHERE = `!a:real^N r. FINITE(sphere(a,r)) <=> r <= &0 \/ dimindex(:N) = 1`;;

let LIMIT_POINT_OF_SPHERE = `!a r x:real^N. x limit_point_of sphere(a,r) <=>
                  &0 < r /\ 2 <= dimindex(:N) /\ x IN sphere(a,r)`;;

let CARD_EQ_SPHERE = `!a:real^N r. 2 <= dimindex(:N) /\ &0 < r ==> sphere(a,r) =_c (:real)`;;

let HAS_SIZE_SPHERE_2 = `!a:real^N r. sphere(a,r) HAS_SIZE 2 <=> dimindex(:N) = 1 /\ &0 < r`;;

let LOCALLY_PATH_CONNECTED_SPHERE = `!(a:real^N) r. locally path_connected (sphere(a:real^N,r))`;;

let LOCALLY_CONNECTED_SPHERE = `!a:real^N r. locally connected(sphere(a,r))`;;

let FINITE_CIRCLE_INTERSECTION = `(!a b:real^2 r s.
        FINITE(sphere(a,r) INTER sphere(b,s)) <=>
        ~(a = b /\ r = s /\ &0 < r /\ &0 < s))`
and CARD_CIRCLE_INTERSECTION_LE = `(!a b:real^2 r s.
        ~(a = b /\ r = s /\ &0 < r /\ &0 < s)
        ==> CARD(sphere(a,r) INTER sphere(b,s)) <= 2)`;;

let INTER_SPHERE_EQ_EMPTY = `!a b:real^N r s.
        sphere(a,r) INTER sphere(b,s) = {} <=>
        if dimindex(:N) = 1 then
          r < &0 \/ s < &0 \/ ~(dist(a,b) = abs(r - s)) /\ ~(dist(a,b) = r + s)
        else
          r < &0 \/ s < &0 \/ dist(a,b) < abs(r - s) \/ r + s < dist(a,b)`;;

let HAS_SIZE_INTER_SPHERE_1 = `!a b:real^N r s.
        (sphere(a,r) INTER sphere(b,s)) HAS_SIZE 1 <=>
        &0 <= r /\ &0 <= s /\
        (a = b ==> r = &0 /\ s = &0) /\
        (dist(a,b) = r + s \/ dist(a,b) = abs(r - s))`;;

let PATH_CONNECTED_ANNULUS = `(!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 < norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 < norm(x - a) /\ norm(x - a) <= r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2})`;;

let CONNECTED_ANNULUS = `(!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 < norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 < norm(x - a) /\ norm(x - a) <= r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2})`;;

let PATH_CONNECTED_COMPLEMENT_BOUNDED_CONVEX = `!s. 2 <= dimindex(:N) /\ bounded s /\ convex s
       ==> path_connected((:real^N) DIFF s)`;;

let CONNECTED_COMPLEMENT_BOUNDED_CONVEX = `!s. 2 <= dimindex(:N) /\ bounded s /\ convex s
       ==> connected((:real^N) DIFF s)`;;

let CONNECTED_DIFF_BALL = `!s a:real^N r.
        2 <= dimindex(:N) /\ connected s /\ cball(a,r) SUBSET s
        ==> connected(s DIFF ball(a,r))`;;

let PATH_CONNECTED_DIFF_BALL = `!s a:real^N r.
        2 <= dimindex(:N) /\ path_connected s /\ cball(a,r) SUBSET s
        ==> path_connected(s DIFF ball(a,r))`;;

let CONNECTED_DELETE_INTERIOR_POINT = `!s a:real^N.
        2 <= dimindex(:N) /\ connected s /\ a IN interior s
        ==> connected(s DELETE a)`;;

let CONNECTED_DELETE_INTERIOR_POINT_EQ = `!s a:real^N.
        2 <= dimindex(:N) /\ a IN interior s
        ==> (connected (s DELETE a) <=> connected s)`;;

let CONNECTED_OPEN_DELETE_EQ = `!s a:real^N.
        2 <= dimindex(:N) /\ open s
        ==> (connected(s DELETE a) <=> connected s)`;;

let PATH_CONNECTED_DELETE_INTERIOR_POINT = `!s a:real^N.
        2 <= dimindex(:N) /\ path_connected s /\ a IN interior s
        ==> path_connected(s DELETE a)`;;

let CONNECTED_OPEN_DIFF_CBALL = `!s a:real^N r.
        2 <= dimindex (:N) /\ open s /\ connected s /\ cball(a,r) SUBSET s
        ==> connected(s DIFF cball(a,r))`;;

let PATH_CONNECTED_CONVEX_DIFF_LOWDIM = `!s t:real^N->bool.
        convex s /\ aff_dim t + &2 <= aff_dim s ==> path_connected(s DIFF t)`;;

let PATH_CONNECTED_OPEN_IN_DIFF_LOWDIM = `!s t:real^N->bool.
        connected s /\ open_in (subtopology euclidean (affine hull s)) s /\
        aff_dim t + &2 <= aff_dim s
        ==> path_connected(s DIFF t)`;;

let PATH_CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM = `!(s:real^N->bool) f.
        connected s /\ open_in (subtopology euclidean (affine hull s)) s /\
        FINITE f /\ (!t. t IN f ==> closed t /\ aff_dim t + &2 <= aff_dim s)
        ==> path_connected(s DIFF UNIONS f)`;;

let CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM = `!f s:real^N->bool.
        connected s /\ open_in (subtopology euclidean (affine hull s)) s /\
        FINITE f /\ (!t. t IN f ==> aff_dim t + &2 <= aff_dim s)
        ==> connected(s DIFF UNIONS f)`;;

let BOUNDED_FRONTIER_BOUNDED_OR_COBOUNDED = `!s. 2 <= dimindex(:N) /\ bounded(frontier s)
       ==> bounded(s) \/ bounded((:real^N) DIFF s)`;;

let BOUNDED_COMMON_FRONTIER_DOMAINS = `!s t c:real^N->bool.
        2 <= dimindex(:N) /\ bounded c /\
        open s /\ connected s /\
        open t /\ connected t /\
        ~(s = t) /\ frontier s = c /\ frontier t = c
        ==> bounded s \/ bounded t`;;

let INTERIOR_ARC_IMAGE = `!g:real^1->real^N.
        2 <= dimindex(:N) /\ arc g ==> interior(path_image g) = {}`;;

let INTERIOR_SIMPLE_PATH_IMAGE = `!g:real^1->real^N.
        2 <= dimindex(:N) /\ simple_path g ==> interior(path_image g) = {}`;;

let ENDPOINTS_NOT_IN_INTERIOR_SIMPLE_PATH_IMAGE = `!g:real^1->real^N.
     simple_path g
     ==> DISJOINT {pathstart g,pathfinish g} (interior(path_image g))`;;

(* ------------------------------------------------------------------------- *)
(* Existence of unbounded components.                                        *)
(* ------------------------------------------------------------------------- *)

let COBOUNDED_UNBOUNDED_COMPONENT = `!s. bounded((:real^N) DIFF s)
       ==> ?x. x IN s /\ ~bounded(connected_component s x)`;;

let COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT = `!s x y:real^N.
        2 <= dimindex(:N) /\ bounded((:real^N) DIFF s) /\
        ~bounded(connected_component s x) /\
        ~bounded(connected_component s y)
        ==> connected_component s x = connected_component s y`;;

let COBOUNDED_UNBOUNDED_COMPONENTS = `!s. bounded ((:real^N) DIFF s) ==> ?c. c IN components s /\ ~bounded c`;;

let COBOUNDED_UNIQUE_UNBOUNDED_COMPONENTS = `!s c c'.
        2 <= dimindex(:N) /\
        bounded ((:real^N) DIFF s) /\
        c IN components s /\ ~bounded c /\
        c' IN components s /\ ~bounded c'
        ==> c' = c`;;

let COBOUNDED_HAS_BOUNDED_COMPONENT = `!s. 2 <= dimindex(:N) /\ bounded((:real^N) DIFF s) /\ ~connected s
       ==> ?c. c IN components s /\ bounded c`;;

(* ------------------------------------------------------------------------- *)
(* Self-homeomorphisms shuffling points about in various ways.               *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_MOVING_POINT_EXISTS = `!s t a b:real^N.
        open_in (subtopology euclidean (affine hull s)) s /\
        s SUBSET t /\ t SUBSET affine hull s /\
        connected s /\ a IN s /\ b IN s
        ==> ?f g. homeomorphism (t,t) (f,g) /\ f a = b /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`;;

let HOMEOMORPHISM_MOVING_POINTS_EXISTS_GEN = `!s t x (y:A->real^N) k.
        &2 <= aff_dim s /\ open_in (subtopology euclidean (affine hull s)) s /\
        s SUBSET t /\ t SUBSET affine hull s /\ connected s /\
        FINITE k /\ (!i. i IN k ==> x i IN s /\ y i IN s) /\
        pairwise (\i j. ~(x i = x j) /\ ~(y i = y j)) k
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  (!i. i IN k ==> f(x i) = y i) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`;;

let HOMEOMORPHISM_MOVING_POINTS_EXISTS = `!s t x (y:A->real^N) k.
        2 <= dimindex(:N) /\ open s /\ connected s /\ s SUBSET t /\
        FINITE k /\ (!i. i IN k ==> x i IN s /\ y i IN s) /\
        pairwise (\i j. ~(x i = x j) /\ ~(y i = y j)) k
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  (!i. i IN k ==> f(x i) = y i) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`;;

let HOMEOMORPHISM_GROUPING_POINTS_EXISTS = `!u s t k:real^N->bool.
        open u /\ open s /\ connected s /\ ~(u = {}) /\
        FINITE k /\ k SUBSET s /\ u SUBSET s /\ s SUBSET t
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)} /\
                  !x. x IN k ==> (f x) IN u`;;

let HOMEOMORPHISM_GROUPING_POINTS_EXISTS_GEN = `!u s t k:real^N->bool.
        open_in (subtopology euclidean (affine hull s)) s /\
        s SUBSET t /\ t SUBSET affine hull s /\ connected s /\
        FINITE k /\ k SUBSET s /\
        open_in (subtopology euclidean s) u /\ ~(u = {})
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  (!x. x IN k ==> f(x) IN u) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`;;

let HOMEOMORPHISM_MOVING_DENSE_COUNTABLE_SUBSETS_EXISTS = `!s:real^M->bool t:real^N->bool.
        COUNTABLE s /\ closure s = affine hull s /\
        COUNTABLE t /\ closure t = affine hull t /\
        aff_dim s = aff_dim t
        ==> ?f g. homeomorphism (affine hull s,affine hull t) (f,g) /\
                  IMAGE f s = t`;;

(* ------------------------------------------------------------------------- *)
(* Boring but useful lemmas about the number of unbounded components.        *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_UNBOUNDED_COMPONENTS_COMPLEMENT_1 = `!s. bounded s /\ ~(s = {})
       ==> {c | c IN components((:real^1) DIFF s) /\ ~bounded c} HAS_SIZE 2`;;

let HAS_SIZE_UNBOUNDED_COMPONENTS_COMPLEMENT = `!s. bounded s
       ==> {c | c IN components((:real^N) DIFF s) /\ ~bounded c} HAS_SIZE
           (if s = {} \/ 2 <= dimindex(:N) then 1 else 2)`;;

(* ------------------------------------------------------------------------- *)
(* The "inside" and "outside" of a set, i.e. the points respectively in a    *)
(* bounded or unbounded connected component of the set's complement.         *)
(* ------------------------------------------------------------------------- *)

let inside = new_definition
 `inside s = {x | ~(x IN s) /\
                  bounded(connected_component ((:real^N) DIFF s) x)}`;;

let outside = new_definition
 `outside s = {x | ~(x IN s) /\
                   ~bounded(connected_component ((:real^N) DIFF s) x)}`;;

let INSIDE_TRANSLATION = `!a s. inside(IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (inside s)`;;

let OUTSIDE_TRANSLATION = `!a s. outside(IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (outside s)`;;

add_translation_invariants [INSIDE_TRANSLATION; OUTSIDE_TRANSLATION];;

let INSIDE_LINEAR_IMAGE = `!f s. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
         ==> inside(IMAGE f s) = IMAGE f (inside s)`;;

let OUTSIDE_LINEAR_IMAGE = `!f s. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
         ==> outside(IMAGE f s) = IMAGE f (outside s)`;;

add_linear_invariants [INSIDE_LINEAR_IMAGE; OUTSIDE_LINEAR_IMAGE];;

let OUTSIDE = `!s. outside s = {x | ~bounded(connected_component((:real^N) DIFF s) x)}`;;

let INSIDE_NO_OVERLAP = `!s. inside s INTER s = {}`;;

let OUTSIDE_NO_OVERLAP = `!s. outside s INTER s = {}`;;

let INSIDE_INTER_OUTSIDE = `!s. inside s INTER outside s = {}`;;

let INSIDE_UNION_OUTSIDE = `!s. inside s UNION outside s = (:real^N) DIFF s`;;

let INSIDE_EQ_OUTSIDE = `!s. inside s = outside s <=> s = (:real^N)`;;

let INSIDE_OUTSIDE = `!s. inside s = (:real^N) DIFF (s UNION outside s)`;;

let OUTSIDE_INSIDE = `!s. outside s = (:real^N) DIFF (s UNION inside s)`;;

let INSIDE_EMPTY_EQ_NO_BOUNDED_COMPONENT_COMPLEMENT = `!s. inside s = {} <=>
       !c. c IN components((:real^N) DIFF s) ==> ~bounded c`;;

let OUTSIDE_EMPTY_EQ_NO_BOUNDED_COMPONENT_COMPLEMENT = `!s. outside s = {} <=>
       !c. c IN components((:real^N) DIFF s) ==> bounded c`;;

let INSIDE_SELF_OUTSIDE_EVERSION = `!s t:real^N->bool.
        s UNION inside s SUBSET inside t <=>
        t UNION outside t SUBSET outside s`;;

let UNION_WITH_INSIDE = `!s. s UNION inside s = (:real^N) DIFF outside s`;;

let UNION_WITH_OUTSIDE = `!s. s UNION outside s = (:real^N) DIFF inside s`;;

let OUTSIDE_MONO = `!s t. s SUBSET t ==> outside t SUBSET outside s`;;

let INSIDE_MONO = `!s t. s SUBSET t ==> inside s DIFF t SUBSET inside t`;;

let INSIDE_MONO_ALT = `!s t:real^N->bool. s SUBSET t ==> inside s SUBSET t UNION inside t`;;

let COBOUNDED_OUTSIDE = `!s:real^N->bool. bounded s ==> bounded((:real^N) DIFF outside s)`;;

let UNBOUNDED_OUTSIDE = `!s:real^N->bool. bounded s ==> ~bounded(outside s)`;;

let BOUNDED_INSIDE = `!s:real^N->bool. bounded s ==> bounded(inside s)`;;

let CONNECTED_OUTSIDE = `!s:real^N->bool. 2 <= dimindex(:N) /\ bounded s ==> connected(outside s)`;;

let OUTSIDE_CONNECTED_COMPONENT_LT = `!s. outside s =
            {x | !B. ?y. B < norm(y) /\
                         connected_component((:real^N) DIFF s) x y}`;;

let OUTSIDE_CONNECTED_COMPONENT_LE = `!s. outside s =
            {x | !B. ?y. B <= norm(y) /\
                         connected_component((:real^N) DIFF s) x y}`;;

let NOT_OUTSIDE_CONNECTED_COMPONENT_LT = `!s. 2 <= dimindex(:N) /\ bounded s
       ==> (:real^N) DIFF (outside s) =
           {x | !B. ?y. B < norm(y) /\
                        ~(connected_component((:real^N) DIFF s) x y)}`;;

let NOT_OUTSIDE_CONNECTED_COMPONENT_LE = `!s. 2 <= dimindex(:N) /\ bounded s
       ==> (:real^N) DIFF (outside s) =
           {x | !B. ?y. B <= norm(y) /\
                        ~(connected_component((:real^N) DIFF s) x y)}`;;

let INSIDE_CONNECTED_COMPONENT_LT = `!s. 2 <= dimindex(:N) /\ bounded s
       ==> inside s =
            {x:real^N | ~(x IN s) /\
                        !B. ?y. B < norm(y) /\
                                ~(connected_component((:real^N) DIFF s) x y)}`;;

let INSIDE_CONNECTED_COMPONENT_LE = `!s. 2 <= dimindex(:N) /\ bounded s
       ==> inside s =
            {x:real^N | ~(x IN s) /\
                        !B. ?y. B <= norm(y) /\
                                ~(connected_component((:real^N) DIFF s) x y)}`;;

let OUTSIDE_UNION_OUTSIDE_UNION = `!c c1 c2:real^N->bool.
        c INTER outside(c1 UNION c2) = {}
        ==> outside(c1 UNION c2) SUBSET outside(c1 UNION c)`;;

let INSIDE_SUBSET = `!s t u. connected u /\ ~bounded u /\ t UNION u = (:real^N) DIFF s
           ==> inside s SUBSET t`;;

let INSIDE_UNIQUE = `!s t u. connected t /\ bounded t /\
           connected u /\ ~(bounded u) /\
           ~connected((:real^N) DIFF s) /\
           t UNION u = (:real^N) DIFF s
           ==> inside s = t`;;

let INSIDE_OUTSIDE_UNIQUE = `!s t u. connected t /\ bounded t /\
           connected u /\ ~(bounded u) /\
           ~connected((:real^N) DIFF s) /\
           t UNION u = (:real^N) DIFF s
           ==> inside s = t /\ outside s = u`;;

let INTERIOR_INSIDE_FRONTIER = `!s:real^N->bool. bounded s ==> interior s SUBSET inside(frontier s)`;;

let INSIDE_EMPTY = `inside {} = {}`;;

let OUTSIDE_EMPTY = `outside {} = (:real^N)`;;

let INSIDE_SAME_COMPONENT = `!s x y. connected_component((:real^N) DIFF s) x y /\ x IN inside s
           ==> y IN inside s`;;

let OUTSIDE_SAME_COMPONENT = `!s x y. connected_component((:real^N) DIFF s) x y /\ x IN outside s
           ==> y IN outside s`;;

let CONNECTED_COMPONENT_INSIDE = `!s a. connected_component (inside s) a =
         if a IN inside s then connected_component ((:real^N) DIFF s) a
         else {}`;;

let CONNECTED_COMPONENT_OUTSIDE = `!s a. connected_component (outside s) a =
         if a IN outside s then connected_component ((:real^N) DIFF s) a
         else {}`;;

let BOUNDED_COMPONENTS_INSIDE = `!c:real^N->bool. c IN components(inside s) ==> bounded c`;;

let UNBOUNDED_COMPONENTS_OUTSIDE = `!s c:real^N->bool. c IN components(outside s) ==> ~bounded c`;;

let INSIDE_WITH_INSIDE = `!s:real^N->bool. inside(s UNION inside s) = {}`;;

let OUTSIDE_WITH_OUTSIDE = `!s:real^N->bool. outside(s UNION outside s) = {}`;;

let OUTSIDE_CONVEX = `!s. convex s ==> outside s = (:real^N) DIFF s`;;

let INSIDE_CONVEX = `!s. convex s ==> inside s = {}`;;

let OUTSIDE_SUBSET_CONVEX = `!s t. convex t /\ s SUBSET t ==> (:real^N) DIFF t SUBSET outside s`;;

let INSIDE_SUBSET_CONVEX = `!s c:real^N->bool. convex c /\ s SUBSET c ==> inside s SUBSET c`;;

let INSIDE_SUBSET_CONVEX_HULL = `!s:real^N->bool. inside s SUBSET convex hull s`;;

let UNBOUNDED_DISJOINT_IN_OUTSIDE = `!s t x:real^N.
       connected t /\ ~bounded t /\ x IN t /\ DISJOINT s t ==> x IN outside s`;;

let INSIDE_SUBSET_INTERIOR_CONVEX = `!s c:real^N->bool. convex c /\ s SUBSET c ==> inside s SUBSET interior c`;;

let INSIDE_SUBSET_INTERIOR_CONVEX_HULL = `!s:real^N->bool. inside s SUBSET interior(convex hull s)`;;

let OUTSIDE_FRONTIER_MISSES_CLOSURE = `!s. bounded s ==> outside(frontier s) SUBSET (:real^N) DIFF closure s`;;

let OUTSIDE_FRONTIER_EQ_COMPLEMENT_CLOSURE = `!s. bounded s /\ convex s
       ==> outside(frontier s) = (:real^N) DIFF closure s`;;

let INSIDE_FRONTIER_EQ_INTERIOR = `!s:real^N->bool.
        bounded s /\ convex s ==> inside(frontier s) = interior s`;;

let INSIDE_SPHERE = `!a:real^N r. inside(sphere(a,r)) = ball(a,r)`;;

let OUTSIDE_SPHERE = `!a r. outside(sphere(a,r)) = (:real^N) DIFF cball(a,r)`;;

let OPEN_INSIDE = `!s:real^N->bool. closed s ==> open(inside s)`;;

let OPEN_OUTSIDE = `!s:real^N->bool. closed s ==> open(outside s)`;;

let CLOSURE_INSIDE_SUBSET = `!s:real^N->bool. closed s ==> closure(inside s) SUBSET s UNION inside s`;;

let FRONTIER_INSIDE_SUBSET = `!s:real^N->bool. closed s ==> frontier(inside s) SUBSET s`;;

let FRONTIER_WITH_INSIDE_SUBSET = `!s:real^N->bool. closed s ==> frontier(s UNION inside s) SUBSET s`;;

let CLOSURE_OUTSIDE_SUBSET = `!s:real^N->bool. closed s ==> closure(outside s) SUBSET s UNION outside s`;;

let FRONTIER_OUTSIDE_SUBSET = `!s:real^N->bool. closed s ==> frontier(outside s) SUBSET s`;;

let FRONTIER_WITH_OUTSIDE_SUBSET = `!s:real^N->bool. closed s ==> frontier(s UNION outside s) SUBSET s`;;

let CLOSED_WITH_INSIDE = `!s:real^N->bool. closed s ==> closed(s UNION inside s)`;;

let BOUNDED_WITH_INSIDE = `!s:real^N->bool. bounded s ==> bounded(s UNION inside s)`;;

let COMPACT_WITH_INSIDE = `!s:real^N->bool. compact s ==> compact(s UNION inside s)`;;

let INSIDE_COMPLEMENT_UNBOUNDED_CONNECTED_EMPTY = `!s. connected((:real^N) DIFF s) /\ ~bounded((:real^N) DIFF s)
       ==> inside s = {}`;;

let INSIDE_BOUNDED_COMPLEMENT_CONNECTED_EMPTY = `!s. connected((:real^N) DIFF s) /\ bounded s
       ==> inside s = {}`;;

let INSIDE_INSIDE = `!s t:real^N->bool.
        s SUBSET inside t ==> inside s DIFF t SUBSET inside t`;;

let INSIDE_INSIDE_SUBSET = `!s:real^N->bool. inside(inside s) SUBSET s`;;

let INSIDE_OUTSIDE_INTERSECT_CONNECTED = `!s t:real^N->bool.
        connected t /\ ~(inside s INTER t = {}) /\ ~(outside s INTER t = {})
        ==> ~(s INTER t = {})`;;

let OUTSIDE_BOUNDED_NONEMPTY = `!s:real^N->bool. bounded s ==> ~(outside s = {})`;;

let OUTSIDE_COMPACT_IN_OPEN = `!s t:real^N->bool.
        compact s /\ open t /\ s SUBSET t /\ ~(t = {})
        ==> ~(outside s INTER t = {})`;;

let INSIDE_INSIDE_COMPACT_CONNECTED = `!s t:real^N->bool.
        closed s /\ compact t /\ s SUBSET inside t /\ connected t
        ==> inside s SUBSET inside t`;;

let INSIDE_SELF_OUTSIDE_COMPACT_CONNECTED = `!s t:real^N->bool.
        closed s /\ compact t /\ s SUBSET inside t /\ connected t
        ==> t UNION outside t SUBSET outside s`;;

let INSIDE_OUTSIDE_COMPACT_CONNECTED = `!s t:real^N->bool.
        closed s /\ compact t /\ s SUBSET inside t /\ connected t
        ==> t SUBSET outside s`;;

let CONNECTED_WITH_INSIDE = `!s:real^N->bool. closed s /\ connected s ==> connected(s UNION inside s)`;;

let CONNECTED_WITH_OUTSIDE = `!s:real^N->bool. closed s /\ connected s ==> connected(s UNION outside s)`;;

let INSIDE_INSIDE_EQ_EMPTY = `!s:real^N->bool.
        closed s /\ connected s ==> inside(inside s) = {}`;;

let INSIDE_IN_COMPONENTS = `!s. (inside s) IN components((:real^N) DIFF s) <=>
       connected(inside s) /\ ~(inside s = {})`;;

let OUTSIDE_IN_COMPONENTS = `!s. (outside s) IN components((:real^N) DIFF s) <=>
       connected(outside s) /\ ~(outside s = {})`;;

let BOUNDED_UNIQUE_OUTSIDE = `!c s. 2 <= dimindex(:N) /\ bounded s
         ==> (c IN components ((:real^N) DIFF s) /\ ~bounded c <=>
              c = outside s)`;;

let EMPTY_INSIDE_PSUBSET_CONVEX_FRONTIER = `!s t:real^N->bool.
        convex s /\ t PSUBSET frontier s ==> inside t = {}`;;

(* ------------------------------------------------------------------------- *)
(* A Euclidean-centric formulation of homotopy.                              *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_EUCLIDEAN = `!P X Y (p:real^M->real^N) q.
    homotopic_with P (subtopology euclidean X,subtopology euclidean Y) p q <=>
        ?h:real^(1,M)finite_sum->real^N.
                h continuous_on (interval[vec 0,vec 1] PCROSS X) /\
                IMAGE h (interval[vec 0,vec 1] PCROSS X) SUBSET Y /\
                (!x. h(pastecart (vec 0) x) = p x) /\
                (!x. h(pastecart (vec 1) x) = q x) /\
                (!t. t IN interval[vec 0,vec 1] ==> P(\x. h(pastecart t x)))`;;

(* ------------------------------------------------------------------------- *)
(* We often want to just localize the ending function equality or whatever.  *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_EUCLIDEAN_ALT = `(!h k. (!x. x IN X ==> h x = k x) ==> (P h <=> P k))
   ==> (homotopic_with P
           (subtopology euclidean X,subtopology euclidean Y) p q <=>
        ?h:real^(1,M)finite_sum->real^N.
          h continuous_on (interval[vec 0,vec 1] PCROSS X) /\
          IMAGE h (interval[vec 0,vec 1] PCROSS X) SUBSET Y /\
          (!x. x IN X ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN X ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0,vec 1] ==> P(\x. h(pastecart t x))))`;;

(* ------------------------------------------------------------------------- *)
(* Trivial properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_RESTRICT = `!P s t s' t' f g:real^M->real^N.
        homotopic_with P
         (subtopology euclidean s,subtopology euclidean t) f g /\
        s' SUBSET s /\
        (!h. P h /\ IMAGE h s SUBSET t ==> IMAGE h s' SUBSET t')
        ==> homotopic_with P
             (subtopology euclidean s',subtopology euclidean t') f g`;;

let HOMOTOPIC_WITH_IMP_CONTINUOUS = `!P X Y (f:real^M->real^N) g.
      homotopic_with P (subtopology euclidean X,subtopology euclidean Y) f g
      ==> f continuous_on X /\ g continuous_on X`;;

let HOMOTOPIC_WITH_IMP_SUBSET = `!P X Y (f:real^M->real^N) g.
      homotopic_with P (subtopology euclidean X,subtopology euclidean Y) f g
      ==> IMAGE f X SUBSET Y /\ IMAGE g X SUBSET Y`;;

let HOMOTOPIC_WITH_MONO = `!P Q X Y f g:real^M->real^N.
        homotopic_with P
          (subtopology euclidean X,subtopology euclidean Y) f g /\
        (!h. h continuous_on X /\ IMAGE h X SUBSET Y /\ P h ==> Q h)
        ==> homotopic_with Q
             (subtopology euclidean X,subtopology euclidean Y) f g`;;

let HOMOTOPIC_WITH_SUBSET_LEFT = `!P X Y Z f g.
        homotopic_with P
         (subtopology euclidean X,subtopology euclidean Y) f g /\
        Z SUBSET X
        ==> homotopic_with P
             (subtopology euclidean Z,subtopology euclidean Y) f g`;;

let HOMOTOPIC_WITH_SUBSET_RIGHT = `!P X Y Z (f:real^M->real^N) g.
        homotopic_with P
         (subtopology euclidean X,subtopology euclidean Y) f g /\
        Y SUBSET Z
        ==> homotopic_with P
             (subtopology euclidean X,subtopology euclidean Z) f g`;;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT = `!p f:real^N->real^P g h:real^M->real^N W X Y.
      homotopic_with (\f. p(f o h))
       (subtopology euclidean X,subtopology euclidean Y) f g /\
      h continuous_on W /\ IMAGE h W SUBSET X
      ==> homotopic_with p
           (subtopology euclidean W,subtopology euclidean Y) (f o h) (g o h)`;;

let HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT = `!f:real^N->real^P g h:real^M->real^N W X Y.
        homotopic_with (\f. T)
         (subtopology euclidean X,subtopology euclidean Y) f g /\
        h continuous_on W /\ IMAGE h W SUBSET X
        ==> homotopic_with (\f. T)
            (subtopology euclidean W,subtopology euclidean Y) (f o h) (g o h)`;;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT = `!p f:real^M->real^N g h:real^N->real^P X Y Z.
      homotopic_with (\f. p(h o f))
       (subtopology euclidean X,subtopology euclidean Y) f g /\
      h continuous_on Y /\ IMAGE h Y SUBSET Z
      ==> homotopic_with p
           (subtopology euclidean X,subtopology euclidean Z) (h o f) (h o g)`;;

let HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT = `!f:real^M->real^N g h:real^N->real^P X Y Z.
        homotopic_with (\f. T)
         (subtopology euclidean X,subtopology euclidean Y) f g /\
        h continuous_on Y /\ IMAGE h Y SUBSET Z
        ==> homotopic_with (\f. T)
             (subtopology euclidean X,subtopology euclidean Z)
             (h o f) (h o g)`;;

let HOMOTOPIC_WITH_PCROSS = `!f:real^M->real^N f':real^P->real^Q g g' p p' q s s' t t'.
     homotopic_with p
       (subtopology euclidean s,subtopology euclidean t) f g /\
     homotopic_with p'
       (subtopology euclidean s',subtopology euclidean t') f' g' /\
     (!f g. p f /\ p' g ==> q(\x. pastecart (f(fstcart x)) (g(sndcart x))))
     ==> homotopic_with q
          (subtopology euclidean (s PCROSS s'),
           subtopology euclidean (t PCROSS t'))
          (\z. pastecart (f(fstcart z)) (f'(sndcart z)))
          (\z. pastecart (g(fstcart z)) (g'(sndcart z)))`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy with P is an equivalence relation (on continuous functions       *)
(* mapping X into Y that satisfy P, though this only affects reflexivity).   *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_COMPOSE = `!P Q R f f':real^M->real^N g g':real^N->real^P s t u.
           (!f g. f continuous_on s /\ IMAGE f s SUBSET t /\ P f /\
                  g continuous_on t /\ IMAGE g t SUBSET u /\ Q g
                  ==> R(g o f)) /\
           homotopic_with P
            (subtopology euclidean s,subtopology euclidean t) f f' /\
           homotopic_with Q
            (subtopology euclidean t,subtopology euclidean u) g g'
           ==> homotopic_with R
                (subtopology euclidean s,subtopology euclidean u)
                (g o f) (g' o f')`;;

let HOMOTOPIC_COMPOSE = `!f f':real^M->real^N g g':real^N->real^P s t u.
        homotopic_with (\x. T)
          (subtopology euclidean s,subtopology euclidean t) f f' /\
        homotopic_with (\x. T)
          (subtopology euclidean t,subtopology euclidean u) g g'
        ==> homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean u)
             (g o f) (g' o f')`;;

(* ------------------------------------------------------------------------- *)
(* Two characterizations of homotopic triviality, one of which               *)
(* implicitly incorporates path-connectedness.                               *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_TRIVIALITY = `!s:real^M->bool t:real^N->bool.
        (!f g. f continuous_on s /\ IMAGE f s SUBSET t /\
               g continuous_on s /\ IMAGE g s SUBSET t
               ==> homotopic_with (\x. T)
                    (subtopology euclidean s,subtopology euclidean t) f g) <=>
        (s = {} \/ path_connected t) /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET t
             ==> ?c. homotopic_with (\x. T)
                      (subtopology euclidean s,subtopology euclidean t)
                      f (\x. c))`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy on a union of closed-open sets.                                  *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_ON_CLOPEN_UNIONS = `!f:real^M->real^N g t u.
        (!s. s IN u
             ==> closed_in (subtopology euclidean (UNIONS u)) s /\
                 open_in (subtopology euclidean (UNIONS u)) s /\
                 homotopic_with (\x. T)
                  (subtopology euclidean s,subtopology euclidean t) f g)
        ==> homotopic_with (\x. T)
             (subtopology euclidean (UNIONS u),subtopology euclidean t) f g`;;

let INESSENTIAL_ON_CLOPEN_UNIONS = `!f:real^M->real^N t u.
        path_connected t /\
        (!s. s IN u
             ==> closed_in (subtopology euclidean (UNIONS u)) s /\
                 open_in (subtopology euclidean (UNIONS u)) s /\
                 ?a. homotopic_with (\x. T)
                      (subtopology euclidean s,subtopology euclidean t) f (\x. a))
        ==> ?a. homotopic_with (\x. T)
                 (subtopology euclidean (UNIONS u),subtopology euclidean t)
                 f (\x. a)`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy within the space of linear maps.                                 *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_REFLECTIONS_ALONG = `!P s t a b:real^N.
        ~(a = vec 0) /\ ~(b = vec 0) /\
        (!c. c IN segment[a,b]
             ==> P(reflect_along c) /\ IMAGE (reflect_along c) s SUBSET t)
        ==> homotopic_with P (subtopology euclidean s,subtopology euclidean t)
                             (reflect_along a) (reflect_along b)`;;

let HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS = `!f g:real^N->real^N.
        homotopic_with orthogonal_transformation
         (subtopology euclidean (sphere(vec 0,&1)),
          subtopology euclidean (sphere(vec 0,&1)))
         f g <=>
        orthogonal_transformation f /\ orthogonal_transformation g /\
        det(matrix f) = det(matrix g)`;;

let HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_GEN = `!P f g:real^N->real^N.
        (?r. &0 < r /\ P r)
        ==> (homotopic_with orthogonal_transformation
               (subtopology euclidean {x | P(norm x)},
                subtopology euclidean {x | P(norm x)})
               f g <=>
             orthogonal_transformation f /\ orthogonal_transformation g /\
             det(matrix f) = det(matrix g))`;;

let HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_ALT = `!f g:real^N->real^N.
        homotopic_with orthogonal_transformation
          (subtopology euclidean ((:real^N) DELETE vec 0),
           subtopology euclidean ((:real^N) DELETE vec 0))
          f g <=>
        orthogonal_transformation f /\ orthogonal_transformation g /\
        det(matrix f) = det(matrix g)`;;

let HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV = `!P f g:real^N->real^N.
        homotopic_with orthogonal_transformation
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
        orthogonal_transformation f /\ orthogonal_transformation g /\
        det(matrix f) = det(matrix g)`;;

let HOMOTOPIC_WITH_LINEAR_POSITIVE_DEFINITE_MAPS = `!f g. homotopic_with (\f. linear f /\ positive_definite(matrix f))
           (subtopology euclidean ((:real^N) DELETE vec 0),
            subtopology euclidean ((:real^N) DELETE vec 0)) f g <=>
           linear f /\ linear g /\
           positive_definite(matrix f) /\
           positive_definite(matrix g)`;;

let HOMOTOPIC_WITH_LINEAR_MAPS = `!f g:real^N->real^N.
     homotopic_with linear
       (subtopology euclidean ((:real^N) DELETE vec 0),
        subtopology euclidean ((:real^N) DELETE vec 0)) f g <=>
     linear f /\ linear g /\ &0 < det(matrix f) * det(matrix g)`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy of paths, maintaining the same endpoints.                        *)
(* ------------------------------------------------------------------------- *)

let homotopic_paths = new_definition
 `homotopic_paths s p q =
     homotopic_with
       (\r. pathstart r = pathstart p /\ pathfinish r = pathfinish p)
       (subtopology euclidean (interval[vec 0:real^1,vec 1]),
        subtopology euclidean s)
       p q`;;

let HOMOTOPIC_PATHS = `!s p q:real^1->real^N.
      homotopic_paths s p q <=>
      ?h. h continuous_on
          interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
          IMAGE h (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])
          SUBSET s /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0:real^1,vec 1]
               ==> pathstart(h o pastecart t) = pathstart p /\
                   pathfinish(h o pastecart t) = pathfinish p)`;;

let HOMOTOPIC_PATHS_IMP_PATHSTART = `!s p q. homotopic_paths s p q ==> pathstart p = pathstart q`;;

let HOMOTOPIC_PATHS_IMP_PATHFINISH = `!s p q. homotopic_paths s p q ==> pathfinish p = pathfinish q`;;

let HOMOTOPIC_PATHS_IMP_PATH = `!s p q. homotopic_paths s p q ==> path p /\ path q`;;

let HOMOTOPIC_PATHS_IMP_SUBSET = `!s p q.
     homotopic_paths s p q ==> path_image p SUBSET s /\ path_image q SUBSET s`;;

let HOMOTOPIC_PATHS_REFL = `!s p. homotopic_paths s p p <=>
           path p /\ path_image p SUBSET s`;;

let HOMOTOPIC_PATHS_SYM = `!s p q. homotopic_paths s p q <=> homotopic_paths s q p`;;

let HOMOTOPIC_PATHS_TRANS = `!s p q r.
        homotopic_paths s p q /\ homotopic_paths s q r
        ==> homotopic_paths s p r`;;

let HOMOTOPIC_PATHS_EQ = `!p:real^1->real^N q s.
        path p /\ path_image p SUBSET s /\
        (!t. t IN interval[vec 0,vec 1] ==> p(t) = q(t))
        ==> homotopic_paths s p q`;;

let HOMOTOPIC_PATHS_REPARAMETRIZE = `!p:real^1->real^N q.
        path p /\ path_image p SUBSET s /\
        (?f. f continuous_on interval[vec 0,vec 1] /\
             IMAGE f (interval[vec 0,vec 1]) SUBSET interval[vec 0,vec 1] /\
             f(vec 0) = vec 0 /\ f(vec 1) = vec 1 /\
             !t. t IN interval[vec 0,vec 1] ==> q(t) = p(f t))
        ==> homotopic_paths s p q`;;

let HOMOTOPIC_PATHS_SUBSET = `!s p q.
        homotopic_paths s p q /\ s SUBSET t
        ==> homotopic_paths t p q`;;

(* ------------------------------------------------------------------------- *)
(* A slightly ad-hoc but useful lemma in constructing homotopies.            *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_JOIN_LEMMA = `!p q:real^1->real^1->real^N.
  (\y. p (fstcart y) (sndcart y)) continuous_on
  (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
  (\y. q (fstcart y) (sndcart y)) continuous_on
  (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
  (!t. t IN interval[vec 0,vec 1] ==> pathfinish(p t) = pathstart(q t))
  ==> (\y. (p(fstcart y) ++ q(fstcart y)) (sndcart y)) continuous_on
      (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])`;;

(* ------------------------------------------------------------------------- *)
(* Congruence properties of homotopy w.r.t. path-combining operations.       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_REVERSEPATH = `!s p q:real^1->real^N.
     homotopic_paths s (reversepath p) (reversepath q) <=>
     homotopic_paths s p q`;;

let HOMOTOPIC_PATHS_JOIN = `!s p q p' q':real^1->real^N.
     homotopic_paths s p p' /\ homotopic_paths s q q' /\
     pathfinish p = pathstart q
     ==> homotopic_paths s (p ++ q) (p' ++ q')`;;

let HOMOTOPIC_PATHS_CONTINUOUS_IMAGE = `!f:real^1->real^M g h:real^M->real^N s t.
        homotopic_paths s f g /\
        h continuous_on s /\ IMAGE h s SUBSET t
        ==> homotopic_paths t (h o f) (h o g)`;;

(* ------------------------------------------------------------------------- *)
(* Group properties for homotopy of paths (so taking equivalence classes     *)
(* under homotopy would give the fundamental group).                         *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_RID = `!s p. path p /\ path_image p SUBSET s
         ==> homotopic_paths s (p ++ linepath(pathfinish p,pathfinish p)) p`;;

let HOMOTOPIC_PATHS_LID = `!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s (linepath(pathstart p,pathstart p) ++ p) p`;;

let HOMOTOPIC_PATHS_ASSOC = `!s p q r:real^1->real^N.
        path p /\ path_image p SUBSET s /\
        path q /\ path_image q SUBSET s /\
        path r /\ path_image r SUBSET s /\
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> homotopic_paths s (p ++ (q ++ r)) ((p ++ q) ++ r)`;;

let HOMOTOPIC_PATHS_RINV = `!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s
              (p ++ reversepath p) (linepath(pathstart p,pathstart p))`;;

let HOMOTOPIC_PATHS_LINV = `!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s
              (reversepath p ++ p) (linepath(pathfinish p,pathfinish p))`;;

let HOMOTOPIC_PATHS_LCANCEL = `!p q r s:real^N->bool.
        homotopic_paths s (p ++ q) (p ++ r) /\
        pathstart q = pathfinish p /\ pathstart r = pathfinish p
        ==> homotopic_paths s q r`;;

let HOMOTOPIC_PATHS_LCANCEL_EQ = `!p q r s:real^N->bool.
        pathstart q = pathfinish p /\ pathstart r = pathfinish p
        ==> (homotopic_paths s (p ++ q) (p ++ r) <=>
              path p /\ path_image p SUBSET s /\ homotopic_paths s q r)`;;

let HOMOTOPIC_PATHS_RCANCEL = `!p q r s:real^N->bool.
        homotopic_paths s (p ++ r) (q ++ r) /\
        pathfinish p = pathstart r /\ pathfinish q = pathstart r
        ==> homotopic_paths s p q`;;

let HOMOTOPIC_PATHS_RCANCEL_EQ = `!p q r s:real^N->bool.
        pathfinish p = pathstart r /\ pathfinish q = pathstart r
        ==> (homotopic_paths s (p ++ r) (q ++ r) <=>
             homotopic_paths s p q /\ path r /\ path_image r SUBSET s)`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy of loops without requiring preservation of endpoints.            *)
(* ------------------------------------------------------------------------- *)

let homotopic_loops = new_definition
 `homotopic_loops s p q =
     homotopic_with
       (\r. pathfinish r = pathstart r)
       (subtopology euclidean (interval[vec 0:real^1,vec 1]),
        subtopology euclidean s)
       p q`;;

let HOMOTOPIC_LOOPS = `!s p q:real^1->real^N.
      homotopic_loops s p q <=>
      ?h. h continuous_on
          interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
          IMAGE h (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])
          SUBSET s /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0:real^1,vec 1]
               ==> pathfinish(h o pastecart t) = pathstart(h o pastecart t))`;;

let HOMOTOPIC_LOOPS_IMP_LOOP = `!s p q. homotopic_loops s p q
           ==> pathfinish p = pathstart p /\
               pathfinish q = pathstart q`;;

let HOMOTOPIC_LOOPS_IMP_PATH = `!s p q. homotopic_loops s p q ==> path p /\ path q`;;

let HOMOTOPIC_LOOPS_IMP_SUBSET = `!s p q.
     homotopic_loops s p q ==> path_image p SUBSET s /\ path_image q SUBSET s`;;

let HOMOTOPIC_LOOPS_REFL = `!s p. homotopic_loops s p p <=>
           path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p`;;

let HOMOTOPIC_LOOPS_SYM = `!s p q. homotopic_loops s p q <=> homotopic_loops s q p`;;

let HOMOTOPIC_LOOPS_TRANS = `!s p q r.
        homotopic_loops s p q /\ homotopic_loops s q r
        ==> homotopic_loops s p r`;;

let HOMOTOPIC_LOOPS_SUBSET = `!s p q.
        homotopic_loops s p q /\ s SUBSET t
        ==> homotopic_loops t p q`;;

let HOMOTOPIC_LOOPS_EQ = `!p:real^1->real^N q s.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        (!t. t IN interval[vec 0,vec 1] ==> p(t) = q(t))
        ==> homotopic_loops s p q`;;

let HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE = `!f:real^1->real^M g h:real^M->real^N s t.
        homotopic_loops s f g /\
        h continuous_on s /\ IMAGE h s SUBSET t
        ==> homotopic_loops t (h o f) (h o g)`;;

let HOMOTOPIC_LOOPS_SHIFTPATH_SELF = `!p:real^1->real^N t s.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        t IN interval[vec 0,vec 1]
        ==> homotopic_loops s p (shiftpath t p)`;;

(* ------------------------------------------------------------------------- *)
(* Relations between the two variants of homotopy.                           *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS = `!s p q. homotopic_paths s p q /\
           pathfinish p = pathstart p /\
           pathfinish q = pathstart p
           ==> homotopic_loops s p q`;;

let HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL = `!s p a:real^N.
        homotopic_loops s p (linepath(a,a))
        ==> homotopic_paths s p (linepath(pathstart p,pathstart p))`;;

let HOMOTOPIC_LOOPS_CONJUGATE = `!p q s:real^N->bool.
        path p /\ path_image p SUBSET s /\
        path q /\ path_image q SUBSET s /\
        pathfinish p = pathstart q /\ pathfinish q = pathstart q
        ==> homotopic_loops s (p ++ q ++ reversepath p) q`;;

(* ------------------------------------------------------------------------- *)
(* Relating homotopy of trivial loops to path-connectedness.                 *)
(* ------------------------------------------------------------------------- *)

let PATH_COMPONENT_IMP_HOMOTOPIC_POINTS = `!s a b:real^N.
        path_component s a b
        ==> homotopic_loops s (linepath(a,a)) (linepath(b,b))`;;

let HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE = `!s p q:real^1->real^N t.
        homotopic_loops s p q /\ t IN interval[vec 0,vec 1]
        ==> path_component s (p t) (q t)`;;

let HOMOTOPIC_POINTS_EQ_PATH_COMPONENT = `!s a b:real^N.
        homotopic_loops s (linepath(a,a)) (linepath(b,b)) <=>
        path_component s a b`;;

let PATH_CONNECTED_EQ_HOMOTOPIC_POINTS = `!s:real^N->bool.
        path_connected s <=>
        !a b. a IN s /\ b IN s
              ==> homotopic_loops s (linepath(a,a)) (linepath(b,b))`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy of "nearby" function, paths and loops.                           *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_LINEAR = `!f g:real^M->real^N s t.
        f continuous_on s /\ g continuous_on s /\
        (!x. x IN s ==> segment[f x,g x] SUBSET t)
        ==> homotopic_with (\z. T)
             (subtopology euclidean s,subtopology euclidean t) f g`;;

let HOMOTOPIC_PATHS_LINEAR = `(!g s:real^N->bool h.
        path g /\ path h /\
        pathstart h = pathstart g /\ pathfinish h = pathfinish g /\
        (!t x. t IN interval[vec 0,vec 1] ==> segment[g t,h t] SUBSET s)
        ==> homotopic_paths s g h)`
and HOMOTOPIC_LOOPS_LINEAR = `(!g s:real^N->bool h.
        path g /\ path h /\
        pathfinish g = pathstart g /\ pathfinish h = pathstart h /\
        (!t x. t IN interval[vec 0,vec 1] ==> segment[g t,h t] SUBSET s)
        ==> homotopic_loops s g h)`;;

let HOMOTOPIC_PATHS_NEARBY_EXPLICIT = `(!g s:real^N->bool h.
        path g /\ path h /\
        pathstart h = pathstart g /\ pathfinish h = pathfinish g /\
        (!t x. t IN interval[vec 0,vec 1] /\ ~(x IN s)
               ==> norm(h t - g t) < norm(g t - x))
        ==> homotopic_paths s g h)`
and HOMOTOPIC_LOOPS_NEARBY_EXPLICIT = `(!g s:real^N->bool h.
        path g /\ path h /\
        pathfinish g = pathstart g /\ pathfinish h = pathstart h /\
        (!t x. t IN interval[vec 0,vec 1] /\ ~(x IN s)
               ==> norm(h t - g t) < norm(g t - x))
        ==> homotopic_loops s g h)`;;

let HOMOTOPIC_NEARBY_PATHS = `(!g s:real^N->bool.
        path g /\ open s /\ path_image g SUBSET s
        ==> ?e. &0 < e /\
                !h. path h /\
                    pathstart h = pathstart g /\
                    pathfinish h = pathfinish g /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < e)
                    ==> homotopic_paths s g h)`
and HOMOTOPIC_NEARBY_LOOPS = `(!g s:real^N->bool.
        path g /\ pathfinish g = pathstart g /\ open s /\ path_image g SUBSET s
        ==> ?e. &0 < e /\
                !h. path h /\
                    pathfinish h = pathstart h /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < e)
                    ==> homotopic_loops s g h)`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy of non-antipodal sphere maps.                                    *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_NON_MIDPOINT_SPHEREMAPS = `!f g:real^M->real^N s a r.
        f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
        g continuous_on s /\ IMAGE g s SUBSET sphere(a,r) /\
        (!x. x IN s ==> ~(midpoint(f x,g x) = a))
    ==> homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean (sphere(a,r))) f g`;;

let HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS = `!f g:real^M->real^N s r.
        f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,r) /\
        g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,r) /\
        (!x. x IN s ==> ~(f x = --g x))
    ==> homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean (sphere(vec 0,r))) f g`;;

(* ------------------------------------------------------------------------- *)
(* Retracts, in a general sense, preserve (co)homotopic triviality.          *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN = `!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f ==> P(k o f)) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f ==> Q(h o f)) /\
         (!h k. (!x. x IN u ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\ P f /\
               g continuous_on u /\ IMAGE g u SUBSET s /\ P g
               ==> homotopic_with P
                    (subtopology euclidean u,subtopology euclidean s)  f g)
        ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f /\
                   g continuous_on u /\ IMAGE g u SUBSET t /\ Q g
                   ==> homotopic_with Q
                        (subtopology euclidean u,subtopology euclidean t) f g)`;;

let HOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN = `!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f ==> P(k o f)) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f ==> Q(h o f)) /\
         (!h k. (!x. x IN u ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f
             ==> ?c. homotopic_with P
                      (subtopology euclidean u,subtopology euclidean s)
                      f (\x. c))
        ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f
                 ==> ?c. homotopic_with Q
                          (subtopology euclidean u,subtopology euclidean t)
                          f (\x. c))`;;

let COHOMOTOPICALLY_TRIVIAL_RETRACTION_GEN = `!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f ==> P(f o h)) /\
         (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f ==> Q(f o k)) /\
         (!h k. (!x. x IN t ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\ P f /\
               g continuous_on s /\ IMAGE g s SUBSET u /\ P g
               ==> homotopic_with P
                    (subtopology euclidean s,
                     subtopology euclidean u) f g)
        ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f /\
                   g continuous_on t /\ IMAGE g t SUBSET u /\ Q g
                   ==> homotopic_with Q
                       (subtopology euclidean t,subtopology euclidean u) f g)`;;

let COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN = `!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f ==> P(f o h)) /\
         (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f ==> Q(f o k)) /\
         (!h k. (!x. x IN t ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f
             ==> ?c. homotopic_with P
                      (subtopology euclidean s,subtopology euclidean u)
                      f (\x. c))
        ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f
                 ==> ?c. homotopic_with Q
                           (subtopology euclidean t,subtopology euclidean u)
                           f (\x. c))`;;

(* ------------------------------------------------------------------------- *)
(* Another useful lemma.                                                     *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_JOIN_SUBPATHS = `!g:real^1->real^N s.
       path g /\ path_image g SUBSET s /\
       u IN interval[vec 0,vec 1] /\
       v IN interval[vec 0,vec 1] /\
       w IN interval[vec 0,vec 1]
       ==> homotopic_paths s (subpath u v g ++ subpath v w g) (subpath u w g)`;;

let HOMOTOPIC_LOOPS_SHIFTPATH = `!s:real^N->bool p q u.
        homotopic_loops s p q /\ u IN interval[vec 0,vec 1]
        ==> homotopic_loops s (shiftpath u p) (shiftpath u q)`;;

let HOMOTOPIC_PATHS_LOOP_PARTS = `!s p q a:real^N.
        homotopic_loops s (p ++ reversepath q) (linepath(a,a)) /\ path q
        ==> homotopic_paths s p q`;;

let HOMOTOPIC_LOOPS_ADD_SYM = `!p q:real^1->real^N.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
        pathstart q = pathstart p
        ==> homotopic_loops s (p ++ q) (q ++ p)`;;

(* ------------------------------------------------------------------------- *)
(* Simply connected sets defined as "all loops are homotopic (as loops)".    *)
(* ------------------------------------------------------------------------- *)

let simply_connected = new_definition
 `simply_connected(s:real^N->bool) <=>
        !p q. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET s /\
              path q /\ pathfinish q = pathstart q /\ path_image q SUBSET s
              ==> homotopic_loops s p q`;;

let SIMPLY_CONNECTED_EMPTY = `simply_connected {}`;;

let SIMPLY_CONNECTED_IMP_PATH_CONNECTED = `!s:real^N->bool. simply_connected s ==> path_connected s`;;

let SIMPLY_CONNECTED_IMP_CONNECTED = `!s:real^N->bool. simply_connected s ==> connected s`;;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY = `!s:real^N->bool.
        simply_connected s <=>
        !p a. path p /\ path_image p SUBSET s /\
              pathfinish p = pathstart p /\ a IN s
              ==> homotopic_loops s p (linepath(a,a))`;;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME = `!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
            ==> ?a. a IN s /\ homotopic_loops s p (linepath(a,a))`;;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ALL = `!s:real^N->bool.
        simply_connected s <=>
        s = {} \/
        ?a. a IN s /\
            !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
                ==> homotopic_loops s p (linepath(a,a))`;;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH = `!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
            ==> homotopic_paths s p (linepath(pathstart p,pathstart p))`;;

let SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS = `!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p q. path p /\ path_image p SUBSET s /\
              path q /\ path_image q SUBSET s /\
              pathstart q = pathstart p /\ pathfinish q = pathfinish p
              ==> homotopic_paths s p q`;;

let SIMPLY_CONNECTED_RETRACTION_GEN = `!s:real^M->bool t:real^N->bool h k.
        h continuous_on s /\ IMAGE h s = t /\
        k continuous_on t /\ IMAGE k t SUBSET s /\
        (!y. y IN t ==> h(k y) = y) /\
        simply_connected s
        ==> simply_connected t`;;

let HOMEOMORPHIC_SIMPLY_CONNECTED = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ simply_connected s
        ==> simply_connected t`;;

let HOMEOMORPHIC_SIMPLY_CONNECTED_EQ = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t
        ==> (simply_connected s <=> simply_connected t)`;;

let SIMPLY_CONNECTED_TRANSLATION = `!a:real^N s. simply_connected (IMAGE (\x. a + x) s) <=> simply_connected s`;;

add_translation_invariants [SIMPLY_CONNECTED_TRANSLATION];;

let SIMPLY_CONNECTED_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (simply_connected (IMAGE f s) <=> simply_connected s)`;;

add_linear_invariants [SIMPLY_CONNECTED_INJECTIVE_LINEAR_IMAGE];;

let HOMEOMORPHISM_SIMPLE_CONNECTEDNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (simply_connected(IMAGE f k) <=> simply_connected k)`;;

let SIMPLY_CONNECTED_PCROSS = `!s:real^M->bool t:real^N->bool.
        simply_connected s /\ simply_connected t
        ==> simply_connected(s PCROSS t)`;;

let SIMPLY_CONNECTED_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        simply_connected(s PCROSS t) <=>
        s = {} \/ t = {} \/ simply_connected s /\ simply_connected t`;;

let SIMPLY_CONNECTED_NESTED_UNIONS = `!f:(real^N->bool)->bool.
        (!s. s IN f ==> open s /\ simply_connected s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> simply_connected(UNIONS f)`;;

(* ------------------------------------------------------------------------- *)
(* The (carrier of) the fundamental group: homotopy classes of loops at a.   *)
(* ------------------------------------------------------------------------- *)

let fundamental_group = new_definition
 `fundamental_group(s,a:real^N) =
    { homotopic_paths s p | p |  path p /\ path_image p SUBSET s /\
                                 pathstart p = a /\ pathfinish p = a}`;;

let FUNDAMENTAL_GROUP_EQ_EMPTY = `!s a:real^N. fundamental_group (s,a) = {} <=> ~(a IN s)`;;

let CARD_EQ_FUNDAMENTAL_GROUPS_BASEPOINTS = `!s a b:real^N.
        path_connected s /\ a IN s /\ b IN s
        ==> fundamental_group(s,a) =_c fundamental_group(s,b)`;;

let SIMPLY_CONNECTED_FUNDAMENTAL_GROUP = `!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !a. a IN s
            ==> fundamental_group(s,a) = {homotopic_paths s (linepath(a,a))}`;;

let FUNDAMENTAL_GROUP_SIMPLY_CONNECTED = `!s a:real^N.
     simply_connected s /\ a IN s
     ==> fundamental_group(s,a) = {homotopic_paths s (linepath(a,a))}`;;

(* ------------------------------------------------------------------------- *)
(* A mapping out of a sphere is nullhomotopic iff it extends to the ball.    *)
(* This even works out in the degenerate cases when the radius is <= 0, and  *)
(* we also don't need to explicitly assume continuity since it's already     *)
(* implicit in both sides of the equivalence.                                *)
(* ------------------------------------------------------------------------- *)

let NULLHOMOTOPIC_FROM_SPHERE_EXTENSION = `!f:real^M->real^N s a r.
        (?c. homotopic_with (\x. T)
              (subtopology euclidean (sphere(a,r)),
               subtopology euclidean s) f (\x. c)) <=>
        (?g. g continuous_on cball(a,r) /\ IMAGE g (cball(a,r)) SUBSET s /\
             !x. x IN sphere(a,r) ==> g x = f x)`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy equivalence.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("homotopy_equivalent",(12,"right"));;

let homotopy_equivalent = new_definition
 `(s:real^M->bool) homotopy_equivalent (t:real^N->bool) <=>
        ?f g. f continuous_on s /\ IMAGE f s SUBSET t /\
              g continuous_on t /\ IMAGE g t SUBSET s /\
              homotopic_with (\x. T)
               (subtopology euclidean s,subtopology euclidean s) (g o f) I /\
              homotopic_with (\x. T)
               (subtopology euclidean t,subtopology euclidean t) (f o g) I`;;

let HOMOTOPY_EQUIVALENT_SPACE_EUCLIDEAN = `!(s:real^M->bool) (t:real^N->bool).
     (subtopology euclidean s) homotopy_equivalent_space
     (subtopology euclidean t) <=>
     s homotopy_equivalent t`;;

let HOMOTOPY_EQUIVALENT = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t <=>
        ?f g h. f continuous_on s /\ IMAGE f s SUBSET t /\
                g continuous_on t /\ IMAGE g t SUBSET s /\
                h continuous_on t /\ IMAGE h t SUBSET s /\
                homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (g o f) I /\
                homotopic_with (\x. T)
                 (subtopology euclidean t,subtopology euclidean t) (f o h) I`;;

let HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> s homotopy_equivalent t`;;

let HOMOTOPY_EQUIVALENT_REFL = `!s:real^N->bool. s homotopy_equivalent s`;;

let HOMOTOPY_EQUIVALENT_SYM = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t <=> t homotopy_equivalent s`;;

let HOMOTOPY_EQUIVALENT_TRANS = `!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t /\ t homotopy_equivalent u
        ==> s homotopy_equivalent u`;;

let HOMOTOPY_EQUIVALENT_PCROSS = `!s:real^M->bool t:real^N->bool s':real^P->bool t':real^Q->bool.
         s homotopy_equivalent s' /\ t homotopy_equivalent t'
         ==> s PCROSS t homotopy_equivalent s' PCROSS t'`;;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_SELF = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (IMAGE f s) homotopy_equivalent s`;;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ = `!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((IMAGE f s) homotopy_equivalent t <=> s homotopy_equivalent t)`;;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ = `!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (s homotopy_equivalent (IMAGE f t) <=> s homotopy_equivalent t)`;;

add_linear_invariants
  [HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
   HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ];;

let HOMOTOPY_EQUIVALENT_TRANSLATION_SELF = `!a:real^N s. (IMAGE (\x. a + x) s) homotopy_equivalent s`;;

let HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ = `!a:real^N s t.
      (IMAGE (\x. a + x) s) homotopy_equivalent t <=> s homotopy_equivalent t`;;

let HOMOTOPY_EQUIVALENT_TRANSLATION_RIGHT_EQ = `!a:real^N s t.
      s homotopy_equivalent (IMAGE (\x. a + x) t) <=> s homotopy_equivalent t`;;

add_translation_invariants
  [HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ;
   HOMOTOPY_EQUIVALENT_TRANSLATION_RIGHT_EQ];;

let HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY = `!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
                    g continuous_on u /\ IMAGE g u SUBSET s
                    ==> homotopic_with (\x. T)
                         (subtopology euclidean u,subtopology euclidean s)
                         f g) <=>
             (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                    g continuous_on u /\ IMAGE g u SUBSET t
                    ==> homotopic_with (\x. T)
                         (subtopology euclidean u,subtopology euclidean t)
                         f g))`;;

let HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY = `!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
                    g continuous_on s /\ IMAGE g s SUBSET u
                    ==> homotopic_with (\x. T)
                         (subtopology euclidean s,subtopology euclidean u)
                         f g) <=>
             (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                    g continuous_on t /\ IMAGE g t SUBSET u
                    ==> homotopic_with (\x. T)
                         (subtopology euclidean t,subtopology euclidean u)
                         f g))`;;

let HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY_NULL = `!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f. f continuous_on u /\ IMAGE f u SUBSET s
                  ==> ?c. homotopic_with (\x. T)
                           (subtopology euclidean u,subtopology euclidean s)
                           f (\x. c)) <=>
             (!f. f continuous_on u /\ IMAGE f u SUBSET t
                  ==> ?c. homotopic_with (\x. T)
                           (subtopology euclidean u,subtopology euclidean t)
                           f (\x. c)))`;;

let HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL = `!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET u
                  ==> ?c. homotopic_with (\x. T)
                            (subtopology euclidean s,subtopology euclidean u)
                            f (\x. c)) <=>
             (!f. f continuous_on t /\ IMAGE f t SUBSET u
                  ==> ?c. homotopic_with (\x. T)
                           (subtopology euclidean t,subtopology euclidean u)
                           f (\x. c)))`;;

let HOMOTOPIC_WITH_IMP_PATH_COMPONENT = `!f g:real^M->real^N s t a.
        homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean t) f g /\
        a IN s
        ==> path_component t (f a) (g a)`;;

let HOMOTOPY_INVARIANT_CARD_COMPONENTS = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T)
         (subtopology euclidean t,subtopology euclidean t) (f o g) I
        ==> components t <=_c components s`;;

let HOMOTOPY_INVARIANT_CONNECTEDNESS = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T)
         (subtopology euclidean t,subtopology euclidean t) (f o g) I /\
        connected s
        ==> connected t`;;

let HOMOTOPY_EQUIVALENT_CONNECTEDNESS = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (connected s <=> connected t)`;;

let HOMOTOPY_EQUIVALENT_CARD_EQ_COMPONENTS = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> components s =_c components t`;;

let HOMEOMORPHIC_CARD_EQ_COMPONENTS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> components s =_c components t`;;

let HOMOTOPY_INVARIANT_CARD_PATH_COMPONENTS = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T)
         (subtopology euclidean t,subtopology euclidean t) (f o g) I
        ==> {path_component t x | x | x IN t}
            <=_c {path_component s x | x | x IN s}`;;

let HOMOTOPY_INVARIANT_PATH_CONNECTEDNESS = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T)
         (subtopology euclidean t,subtopology euclidean t) (f o g) I /\
        path_connected s
        ==> path_connected t`;;

let HOMOTOPY_EQUIVALENT_PATH_CONNECTEDNESS = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (path_connected s <=> path_connected t)`;;

let HOMOTOPY_EQUIVALENT_CARD_EQ_PATH_COMPONENTS = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t
        ==> {path_component s x | x | x IN s} =_c
            {path_component t x | x | x IN t}`;;

let HOMEOMORPHIC_CARD_EQ_PATH_COMPONENTS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t
        ==> {path_component s x | x | x IN s} =_c
            {path_component t x | x | x IN t}`;;

let FINITE_COMPONENTS_PUNCTURED_CONVEX = `!s a:real^N. convex s ==> FINITE(components(s DELETE a))`;;

(* ------------------------------------------------------------------------- *)
(* Contractible sets.                                                        *)
(* ------------------------------------------------------------------------- *)

let contractible = new_definition
 `contractible s <=>
    ?a. homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean s) (\x. x) (\x. a)`;;

let CONTRACTIBLE_SPACE_EUCLIDEAN = `!s:real^N->bool.
        contractible_space(subtopology euclidean s) <=> contractible s`;;

let CONTRACTIBLE_IMP_SIMPLY_CONNECTED = `!s:real^N->bool. contractible s ==> simply_connected s`;;

let CONTRACTIBLE_IMP_CONNECTED = `!s:real^N->bool. contractible s ==> connected s`;;

let CONTRACTIBLE_IMP_PATH_CONNECTED = `!s:real^N->bool. contractible s ==> path_connected s`;;

let NULLHOMOTOPIC_THROUGH_CONTRACTIBLE = `!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        contractible t
        ==> ?c. homotopic_with (\h. T)
                 (subtopology euclidean s,subtopology euclidean u)
                 (g o f) (\x. c)`;;

let NULLHOMOTOPIC_INTO_CONTRACTIBLE = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ contractible t
        ==> ?c. homotopic_with (\h. T)
                 (subtopology euclidean s,subtopology euclidean t) f (\x. c)`;;

let NULLHOMOTOPIC_FROM_CONTRACTIBLE = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ contractible s
        ==> ?c. homotopic_with (\h. T)
                 (subtopology euclidean s,subtopology euclidean t) f (\x. c)`;;

let HOMOTOPIC_THROUGH_CONTRACTIBLE = `!f1:real^M->real^N g1:real^N->real^P f2 g2 s t u.
        f1 continuous_on s /\ IMAGE f1 s SUBSET t /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET u /\
        f2 continuous_on s /\ IMAGE f2 s SUBSET t /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET u /\
        contractible t /\ path_connected u
        ==> homotopic_with (\h. T)
             (subtopology euclidean s,subtopology euclidean u)
             (g1 o f1) (g2 o f2)`;;

let HOMOTOPIC_INTO_CONTRACTIBLE = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on s /\ IMAGE g s SUBSET t /\
        contractible t
        ==> homotopic_with (\h. T)
             (subtopology euclidean s,subtopology euclidean t) f g`;;

let HOMOTOPIC_FROM_CONTRACTIBLE = `!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on s /\ IMAGE g s SUBSET t /\
        contractible s /\ path_connected t
        ==> homotopic_with (\h. T)
             (subtopology euclidean s,subtopology euclidean t) f g`;;

let HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS = `!s:real^M->bool t:real^N->bool.
        contractible s /\ contractible t /\ (s = {} <=> t = {})
        ==> s homotopy_equivalent t`;;

let STARLIKE_IMP_CONTRACTIBLE_GEN = `!P s.
        (!a t. a IN s /\ &0 <= t /\ t <= &1 ==> P(\x. (&1 - t) % x + t % a)) /\
        starlike s
        ==> ?a:real^N. homotopic_with P
            (subtopology euclidean s,subtopology euclidean s) (\x. x) (\x. a)`;;

let STARLIKE_IMP_CONTRACTIBLE = `!s:real^N->bool. starlike s ==> contractible s`;;

let CONTRACTIBLE_UNIV = `contractible(:real^N)`;;

let STARLIKE_IMP_SIMPLY_CONNECTED = `!s:real^N->bool. starlike s ==> simply_connected s`;;

let CONVEX_IMP_SIMPLY_CONNECTED = `!s:real^N->bool. convex s ==> simply_connected s`;;

let STARLIKE_IMP_PATH_CONNECTED = `!s:real^N->bool. starlike s ==> path_connected s`;;

let STARLIKE_IMP_CONNECTED = `!s:real^N->bool. starlike s ==> connected s`;;

let CONIC_IMP_PATH_CONNECTED = `!s:real^N->bool. conic s ==> path_connected s`;;

let CONIC_IMP_CONNECTED = `!s:real^N->bool. conic s ==> connected s`;;

let IS_INTERVAL_SIMPLY_CONNECTED_1 = `!s:real^1->bool. is_interval s <=> simply_connected s`;;

let CONTRACTIBLE_EMPTY = `contractible {}`;;

let CONIC_IMP_CONTRACTIBLE = `!s:real^N->bool. conic s ==> contractible s`;;

let CONIC_IMP_SIMPLY_CONNECTED = `!s:real^N->bool. conic s ==> simply_connected s`;;

let CONTRACTIBLE_CONVEX_TWEAK_BOUNDARY_POINTS = `!s t:real^N->bool.
        convex s /\ relative_interior s SUBSET t /\ t SUBSET closure s
        ==> contractible t`;;

let CONVEX_IMP_CONTRACTIBLE = `!s:real^N->bool. convex s ==> contractible s`;;

let CONTRACTIBLE_SING = `!a:real^N. contractible {a}`;;

let SIMPLY_CONNECTED_SING = `!a:real^N. simply_connected {a}`;;

let IS_INTERVAL_CONTRACTIBLE_1 = `!s:real^1->bool. is_interval s <=> contractible s`;;

let CONTRACTIBLE_PCROSS = `!s:real^M->bool t:real^N->bool.
        contractible s /\ contractible t ==> contractible(s PCROSS t)`;;

let CONTRACTIBLE_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        contractible(s PCROSS t) <=>
        s = {} \/ t = {} \/ contractible s /\ contractible t`;;

let HOMOTOPY_EQUIVALENT_EMPTY = `(!s. (s:real^M->bool) homotopy_equivalent ({}:real^N->bool) <=> s = {}) /\
   (!t. ({}:real^M->bool) homotopy_equivalent (t:real^N->bool) <=> t = {})`;;

let HOMOTOPY_EQUIVALENT_CONTRACTIBILITY = `!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (contractible s <=> contractible t)`;;

let HOMOTOPY_EQUIVALENT_SING = `!s:real^M->bool a:real^N.
        s homotopy_equivalent {a} <=> ~(s = {}) /\ contractible s`;;

let HOMEOMORPHIC_CONTRACTIBLE_EQ = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (contractible s <=> contractible t)`;;

let HOMEOMORPHIC_CONTRACTIBLE = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ contractible s ==> contractible t`;;

let CONTRACTIBLE_TRANSLATION = `!a:real^N s. contractible (IMAGE (\x. a + x) s) <=> contractible s`;;

add_translation_invariants [CONTRACTIBLE_TRANSLATION];;

let CONTRACTIBLE_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (contractible (IMAGE f s) <=> contractible s)`;;

add_linear_invariants [CONTRACTIBLE_INJECTIVE_LINEAR_IMAGE];;

let HOMEOMORPHISM_CONTRACTIBILITY = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (contractible(IMAGE f k) <=> contractible k)`;;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms between punctured spheres and affine sets.                 *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_PUNCTURED_AFFINE_SPHERE_AFFINE = `!a r b t:real^N->bool p:real^M->bool.
        &0 < r /\ b IN sphere(a,r) /\ affine t /\ a IN t /\ b IN t /\
        affine p /\ aff_dim t = aff_dim p + &1
        ==> ((sphere(a:real^N,r) INTER t) DELETE b) homeomorphic p`;;

let HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN = `!s:real^N->bool t:real^M->bool a.
        convex s /\ bounded s /\ a IN relative_frontier s /\
        affine t /\ aff_dim s = aff_dim t + &1
        ==> (relative_frontier s DELETE a) homeomorphic t`;;

let HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE = `!a r b:real^N t:real^M->bool.
    &0 < r /\ b IN sphere(a,r) /\ affine t /\ aff_dim(t) + &1 = &(dimindex(:N))
    ==> (sphere(a:real^N,r) DELETE b) homeomorphic t`;;

let HOMEOMORPHIC_PUNCTURED_SPHERE_HYPERPLANE = `!a r b c d.
        &0 < r /\ b IN sphere(a,r) /\ ~(c = vec 0)
        ==> (sphere(a:real^N,r) DELETE b) homeomorphic
             {x:real^N | c dot x = d}`;;

let HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV = `!a r b.
        &0 < r /\ b IN sphere(a,r) /\ dimindex(:N) = dimindex(:M) + 1
        ==> (sphere(a:real^N,r) DELETE b) homeomorphic (:real^M)`;;

let CONTRACTIBLE_PUNCTURED_SPHERE = `!a r b:real^N.
        &0 < r /\ b IN sphere(a,r) ==> contractible(sphere(a,r) DELETE b)`;;

let CONTRACTIBLE_PUNCTURED_SPHERE_GEN = `!s a:real^N.
        convex s /\ bounded s /\ a IN relative_frontier s
        ==> contractible(relative_frontier s DELETE a)`;;

let NULLHOMOTOPIC_NONSURJECTIVE_SPHERE_MAP_GEN = `!f s:real^N->bool.
        convex s /\ bounded s /\
        f continuous_on (relative_frontier s) /\
        IMAGE f (relative_frontier s) PSUBSET relative_frontier s
        ==> ?a. homotopic_with (\x. T)
                 (subtopology euclidean (relative_frontier s),
                  subtopology euclidean (relative_frontier s)) f (\x. a)`;;

let CONNECTED_PUNCTURED_SPHERE = `!a r b:real^N.
     connected(sphere(a,r) DELETE b) <=>
     (dimindex(:N) = 1 /\ &0 < r ==> b IN sphere(a,r))`;;

let CONNECTED_IN_SPHERE_DELETE_INTERIOR_POINT_EQ = `!a b r u s:real^N->bool.
        3 <= dimindex(:N) /\ open_in (subtopology euclidean (sphere(a,r))) u /\
        b IN u /\ u SUBSET s /\ s SUBSET sphere(a,r)
        ==> (connected(s DELETE b) <=> connected s)`;;

let CONNECTED_OPEN_IN_SPHERE_DELETE_EQ = `!a b r s:real^N->bool.
        3 <= dimindex(:N) /\ open_in (subtopology euclidean (sphere(a,r))) s
        ==> (connected(s DELETE b) <=> connected s)`;;

let FINITE_COMPONENTS_PUNCTURED_CONNECTED_SUBSET_SPHERE = `!r s a b:real^N.
        connected s /\ s SUBSET sphere(a,r) /\
        b IN (subtopology euclidean (sphere (a,r))) interior_of s
        ==> FINITE(components(s DELETE b))`;;

let CARD_EQ_COMPONENTS_IN_COMPACTIFICATION = `!f g (a:real^N) r s z.
        homeomorphism (sphere(a,r) DELETE z,(:real^M)) (f,g) /\
        s SUBSET sphere(a,r) /\ z IN sphere(a,r) /\ ~(z IN closure s)
        ==> components(sphere(a,r) DIFF s) =_c
            {1} +_c {c | c IN components((:real^M) DIFF IMAGE f s) /\
                         bounded c}`;;

let CONNECTED_COMPLEMENT_SUBSET_SIMPLE_PATH_IMAGE = `!g s:real^N->bool.
        simple_path g /\ pathfinish g = pathstart g /\ s SUBSET path_image g
        ==> (connected(path_image g DIFF s) <=> connected s)`;;

let CONNECTED_COMPLEMENT_SUBSET_CIRCLE = `!s a:real^N r.
        dimindex(:N) = 2 /\ s SUBSET sphere(a,r)
        ==> (connected(sphere(a,r) DIFF s) <=> connected s)`;;

(* ------------------------------------------------------------------------- *)
(* When dealing with AR, ANR and ANR later, it's useful to know that any set *)
(* at all is homeomorphic to a closed subset of a convex set, and if the     *)
(* set is locally compact we can take the convex set to be the universe.     *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_CLOSED_IN_CONVEX = `!s:real^M->bool.
        aff_dim s < &(dimindex(:N))
        ==> ?u t:real^N->bool.
                convex u /\
                ~(u = {}) /\
                closed_in (subtopology euclidean u) t /\
                s homeomorphic t`;;

let LOCALLY_COMPACT_HOMEOMORPHIC_CLOSED = `!s:real^M->bool.
        locally compact s /\ dimindex(:M) < dimindex(:N)
        ==> ?t:real^N->bool. closed t /\ s homeomorphic t`;;

(* ------------------------------------------------------------------------- *)
(* Simple connectedness of a union. This is essentially a stripped-down      *)
(* version of the Seifert - Van Kampen theorem.                              *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_UNION = `!s t:real^N->bool.
    open_in (subtopology euclidean (s UNION t)) s /\
    open_in (subtopology euclidean (s UNION t)) t /\
    simply_connected s /\ simply_connected t /\
    path_connected (s INTER t) /\ ~(s INTER t = {})
    ==> simply_connected (s UNION t)`;;

(* ------------------------------------------------------------------------- *)
(* Basic results about topological dimension.                                *)
(* ------------------------------------------------------------------------- *)

let dimension = new_definition
 `(dimension:(real^N->bool)->int) s =
        if s = {} then --(&1)
        else &(minimal n. (subtopology euclidean s) dimension_le &n)`;;

let DIMENSION_GE = `!s:real^N->bool. -- &1 <= dimension s`;;

let DIMENSION_LE_IMP_GE = `!s:real^N->bool n. dimension s <= n ==> -- &1 <= n`;;

let (HOMEOMORPHIC_DIMENSION,DIMENSION_LE_EQ, LOCALLY_DIMENSION_LE,
     DIMENSION_LE_AFF_DIM,DIMENSION_DIMENSION_LE) =
  let HOMEOMORPHIC_DIMENSION_LE' = `!s:real^M->bool t:real^N->bool n.
          s homeomorphic t
          ==> (subtopology euclidean s dimension_le n <=>
               subtopology euclidean t dimension_le n)` in
  let DIMENSION_LE_EQ' = `!s:real^N->bool n.
          (subtopology euclidean s) dimension_le n <=>
          -- &1 <= n /\
          !v a. open v /\ a IN v /\ a IN s
                ==> ?u. a IN u /\ u SUBSET v /\ open u /\
                        subtopology euclidean (s INTER frontier u)
                        dimension_le (n - &1)` in
  let LOCALLY_DIMENSION_LE' = `!s:real^N->bool n.
          (subtopology euclidean s) dimension_le n <=>
          -- &1 <= n /\
          locally (\u. (subtopology euclidean u) dimension_le n) s` in
  let DIMENSION_LE_AFF_DIM' = `!s:real^N->bool. (subtopology euclidean s) dimension_le aff_dim s` in
  let DIMENSION_DIMENSION_LE = `!s:real^N->bool n.
          dimension s <= n <=> (subtopology euclidean s) dimension_le n` in
  let HOMEOMORPHIC_DIMENSION = `!s:real^M->bool t:real^N->bool.
          s homeomorphic t ==> dimension s = dimension t` in
  let DIMENSION_LE_EQ = `!s:real^N->bool n.
          dimension s <= n <=>
          -- &1 <= n /\
          !v a. open v /\ a IN v /\ a IN s
                ==> ?u. a IN u /\ u SUBSET v /\ open u /\
                        dimension(s INTER frontier u) <= n - &1` in
  let LOCALLY_DIMENSION_LE = `!s:real^N->bool n.
          dimension s <= n <=>
          -- &1 <= n /\ locally (\u. dimension u <= n) s` in
  let DIMENSION_LE_AFF_DIM = `!s:real^N->bool. dimension s <= aff_dim s` in
 (HOMEOMORPHIC_DIMENSION,DIMENSION_LE_EQ, LOCALLY_DIMENSION_LE,
     DIMENSION_LE_AFF_DIM,DIMENSION_DIMENSION_LE);;

let DIMENSION_TRANSLATION = `!a:real^N s. dimension(IMAGE (\x. a + x) s) = dimension s`;;

add_translation_invariants [DIMENSION_TRANSLATION];;

let DIMENSION_LINEAR_IMAGE = `!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> dimension(IMAGE f s) = dimension s`;;

add_linear_invariants [DIMENSION_LINEAR_IMAGE];;

let DIMENSION_LE_DIMINDEX = `!s:real^N->bool. dimension s <= &(dimindex(:N))`;;

let DIMENSION_LE_MINUS1 = `!s:real^N->bool. dimension s <= -- &1 <=> s = {}`;;

let DIMENSION_EQ_MINUS1 = `!s:real^N->bool. dimension s = -- &1 <=> s = {}`;;

let DIMENSION_POS_LE = `!s:real^N->bool. &0 <= dimension s <=> ~(s = {})`;;

let DIMENSION_EMPTY = `dimension {} = -- &1`;;

let DIMENSION_SUBSET = `!s t:real^N->bool. s SUBSET t ==> dimension s <= dimension t`;;

let DIMENSION_LE_DISCRETE = `!s:real^N->bool.
        {x | x limit_point_of s} = {} ==> dimension s <= &0`;;

let DIMENSION_EQ_ZERO_DISCRETE = `!s:real^N->bool.
        ~(s = {}) /\ {x | x limit_point_of s} = {} ==> dimension s = &0`;;

let DIMENSION_EQ_DISCRETE = `!s:real^N->bool.
        {x | x limit_point_of s} = {}
        ==> dimension s = if s = {} then --(&1) else &0`;;

let DIMENSION_LE_EQ_ALT = `!s:real^N->bool n.
       dimension s <= n <=>
       -- &1 <= n /\
       !v a. open v /\ a IN v /\ a IN s
             ==> ?u. a IN u /\ u SUBSET v /\ open u /\
                     dimension(subtopology euclidean s frontier_of (s INTER u))
                     <= n - &1`;;

let DIMENSION_LE_EQ_LOCAL = `!s:real^N->bool n.
        dimension s <= n <=>
       -- &1 <= n /\
       !v a. open_in (subtopology euclidean s) v /\ a IN v
             ==> ?u. a IN u /\ u SUBSET v /\
                     open_in (subtopology euclidean s) u /\
                     dimension(subtopology euclidean s frontier_of u)
                     <= n - &1`;;

let DIMENSION_LE_EQ_GENERAL = `!t s:real^N->bool n.
        s SUBSET t
        ==> (dimension s <= n <=>
             -- &1 <= n /\
             !v a. open_in (subtopology euclidean t) v /\ a IN v /\ a IN s
                   ==> ?u. a IN u /\
                           u SUBSET v /\
                           open_in (subtopology euclidean t) u /\
                           dimension(s INTER
                                     subtopology euclidean t frontier_of u)
                           <= n - &1)`;;

let DIMENSION_LE_EQ_LOCALLY = `!s:real^N->bool n.
      dimension s <= n <=>
      --(&1) <= n /\
      locally (\u. open_in (subtopology euclidean s) u /\
                   dimension(subtopology euclidean s frontier_of u) <= n - &1)
              s`;;

let LOCALLY_OPEN_AND_DIMENSION_LE = `!s n. dimension s <= n <=>
         -- &1 <= n /\
         locally (\u. open_in (subtopology euclidean s) u /\
                      dimension u <= n) s`;;

let DIMENSION_EQ_ON_NBDS = `!s:real^N->bool n.
        ~(s = {}) /\
        (!x. x IN s
             ==> ?u v. x IN u /\ open_in (subtopology euclidean s) u /\
                       u SUBSET v /\ v SUBSET s /\ dimension v = n)
        ==> dimension s = n`;;

let LOCALLY_DIMENSION_EQ = `!s:real^N->bool n.
        ~(s = {}) /\ locally (\u. dimension u = n) s ==> dimension s = n`;;

let DIMENSION_EQ_ON_OPEN_SUBSETS = `!s:real^N->bool n.
        ~(s = {}) /\
        (!x. x IN s
             ==> ?u. x IN u /\ open_in (subtopology euclidean s) u /\
                     dimension u = n)
        ==> dimension s = n`;;

let DIMENSION_EQ_LOCALLY_CLOPEN = `!s:real^N->bool.
        dimension s <= &0 <=>
        locally (\u. closed_in (subtopology euclidean s) u /\
                     open_in (subtopology euclidean s) u) s`;;

let SMALL_INDUCTIVE_DIMENSION = `!s:real^N->bool n.
        dimension s <= n <=>
        -- &1 <= n /\
        !c a. a IN s /\ closed_in (subtopology euclidean s) c /\ ~(a IN c)
              ==> ?b. closed_in (subtopology euclidean s) b /\
                      dimension b <= n - &1 /\
                      ?u v. open_in (subtopology euclidean s) u /\
                            open_in (subtopology euclidean s) v /\
                            DISJOINT u v /\ u UNION v = s DIFF b /\
                            a IN u /\ c SUBSET v`;;

let SMALL_IMP_DIMENSION_LE_0 = `!s:real^N->bool. s <_c (:real) ==> dimension s <= &0`;;

let COUNTABLE_IMP_DIMENSION_LE_0 = `!s:real^N->bool. COUNTABLE s ==> dimension s <= &0`;;

let FINITE_IMP_DIMENSION_LE_0 = `!s:real^N->bool. FINITE s ==> dimension s <= &0`;;

let DIMENSION_SING = `!a:real^N. dimension {a} = &0`;;

let CONNECTED_DIMENSION_EQ_SING = `!s:real^N->bool. connected s ==> (dimension s = &0 <=> ?a. s = {a})`;;

let DIMENSION_SUBSET_EXISTS = `!s:real^N->bool n.
        -- &1 <= n /\ n <= dimension s
        ==> ?t. closed_in (subtopology euclidean s) t /\
                t SUBSET s /\
                dimension t = n`;;

let DIMENSION_UNION_LE_BASIC = `!s t:real^N->bool.
        dimension(s UNION t) <= dimension s + dimension t + &1`;;

let DIMENSION_ZERO_REDUCTION_THEOREM = `!s:real^N->bool v.
        dimension s <= &0 /\
        (!n:num. open_in (subtopology euclidean s) (v n))
        ==> ?u. (!n. open_in (subtopology euclidean s) (u n)) /\
                (!n. u n SUBSET v n) /\
                pairwise (\m n. DISJOINT (u m) (u n)) (:num) /\
                UNIONS {u n | n IN (:num)} = UNIONS {v n | n IN (:num)}`;;

let DIMENSION_ZERO_REDUCTION_THEOREM_2 = `!u s t:real^N->bool.
        dimension u <= &0 /\
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t
        ==> ?s' t'. open_in (subtopology euclidean u) s' /\
                    open_in (subtopology euclidean u) t' /\
                    s' SUBSET s /\ t' SUBSET t /\ DISJOINT s' t' /\
                    s' UNION t' = s UNION t`;;

let DIMENSION_ZERO_SEPARATION_THEOREM = `!u s t:real^N->bool.
        dimension u <= &0 /\
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        DISJOINT s t
        ==> ?s' t'. closed_in (subtopology euclidean u) s' /\
                    open_in (subtopology euclidean u) s' /\
                    closed_in (subtopology euclidean u) t' /\
                    open_in (subtopology euclidean u) t' /\
                    s SUBSET s' /\ t SUBSET t' /\ DISJOINT s' t' /\
                    s' UNION t' = u`;;

let DIMENSION_LE_CLOSED_IN_UNIONS,DIMENSION_DECOMPOSITION =
  let lemma = `!s:real^N->bool n.
          dimension s <= n /\ &0 <= n
          ==> ?t. (COUNTABLE UNION_OF
                   (\c. closed_in (subtopology euclidean s) c /\
                        dimension c <= n - &1)) t /\
                  dimension(s DIFF t) <= &0`
  and case0 = `!u:real^N->bool c.
          COUNTABLE c /\
          (!s. s IN c
               ==> closed_in (subtopology euclidean u) s /\ dimension s <= &0)
          ==> dimension(UNIONS c) <= &0` in
  let DIMENSION_LE_CLOSED_IN_UNIONS = `!u:real^N->bool c n.
       -- &1 <= n /\ COUNTABLE c /\
       (!s. s IN c
            ==> closed_in (subtopology euclidean u) s /\ dimension s <= n)
       ==> dimension(UNIONS c) <= n` in
  let DIMENSION_DECOMPOSITION = `!s:real^N->bool n.
          &0 <= n
          ==> (dimension s <= n <=>
               ?t u. t UNION u = s /\ DISJOINT t u /\
                     (fsigma relative_to s) t /\
                     dimension t <= n - &1 /\
                     dimension u <= &0)` in
  DIMENSION_LE_CLOSED_IN_UNIONS,DIMENSION_DECOMPOSITION;;

let DIMENSION_LE_UNIONS_RELATIVE = `!u:real^N->bool c n.
        -- &1 <= n /\
        COUNTABLE c /\
        (!s. s IN c ==> (fsigma relative_to u) s /\ dimension s <= n)
        ==> dimension(UNIONS c) <= n`;;

let DIMENSION_LE_UNIONS = `!c:(real^N->bool)->bool n.
        -- &1 <= n /\
        COUNTABLE c /\
        (!s. s IN c ==> fsigma s /\ dimension s <= n)
        ==> dimension(UNIONS c) <= n`;;

let DIMENSION_LE_UNION_RELATIVE = `!u s t:real^N->bool n.
        (fsigma relative_to u) s /\ (fsigma relative_to u) t /\
        dimension s <= n /\ dimension t <= n
        ==> dimension(s UNION t) <= n`;;

let DIMENSION_LE_UNION = `!s t:real^N->bool n.
        fsigma s /\ fsigma t /\ dimension s <= n /\ dimension t <= n
        ==> dimension(s UNION t) <= n`;;

let DIMENSION_LE_UNION_RELATIVE_GEN = `!u s t:real^N->bool n.
        ((fsigma relative_to u) s /\ (gdelta relative_to u) s /\ t SUBSET u \/
         (fsigma relative_to u) t /\ (gdelta relative_to u) t /\ s SUBSET u) /\
        dimension s <= n /\ dimension t <= n
        ==> dimension(s UNION t) <= n`;;

let DIMENSION_LE_UNION_GEN = `!s t:real^N->bool.
        (fsigma s /\ gdelta s \/ fsigma t /\ gdelta t) /\
        dimension s <= n /\ dimension t <= n
        ==> dimension(s UNION t) <= n`;;

let DIMENSION_LE_UNION_CLOSED_IN = `!u s t:real^N->bool n.
        (closed_in (subtopology euclidean u) s /\ t SUBSET u \/
         closed_in (subtopology euclidean u) t /\ s SUBSET u) /\
        dimension s <= n /\ dimension t <= n
        ==> dimension(s UNION t) <= n`;;

let DIMENSION_LE_UNIONS_ZERODIMENSIONAL = `!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> dimension s <= &0)
        ==> dimension(UNIONS f) <= &(CARD f) - &1`;;

let DIMENSION_LE_UNIONS_ZERODIMENSIONAL_EQ = `!s:real^N->bool n.
        dimension s <= n <=>
        ?f. FINITE f /\ &(CARD f) <= n + &1 /\
            (!d. d IN f ==> dimension d <= &0) /\
            UNIONS f = s`;;

let DIMENSION_INSERT = `!s a:real^N. dimension(a INSERT s) = if s = {} then &0 else dimension s`;;

let DIMENSION_DELETE = `!s a:real^N. dimension(s DELETE a) =
                if s DELETE a = {} then --(&1) else dimension s`;;

let DIMENSION_LE_EQ_GEN = `!s:real^N->bool n.
        dimension s <= n <=>
        if s = {} then -- &1 <= n else
        !v a. open v /\ a IN v
              ==> ?u. a IN u /\ u SUBSET v /\ open u /\
                      dimension (s INTER frontier u) <= n - &1`;;

let DIMENSION_PCROSS_LE = `!s:real^M->bool t:real^N->bool.
       ~(s = {} /\ t = {})
       ==> dimension(s PCROSS t) <= dimension s + dimension t`;;

let DIMENSION_PCROSS_EQ_0 = `!s:real^M->bool t:real^N->bool.
        dimension(s PCROSS t) = &0 <=> dimension s = &0 /\ dimension t = &0`;;

let DIMENSION_SEPARATION_THEOREM = `!t s:real^N->bool n c d.
        &0 <= n /\
        s SUBSET t /\ dimension s <= n /\
        closed_in (subtopology euclidean t) c /\
        closed_in (subtopology euclidean t) d /\
        DISJOINT c d
        ==> ?b. closed_in (subtopology euclidean t) b /\
                dimension(b INTER s) <= n - &1 /\
                ?u v. open_in (subtopology euclidean t) u /\
                      open_in (subtopology euclidean t) v /\
                      DISJOINT u v /\ u UNION v = t DIFF b /\
                      c SUBSET u /\ d SUBSET v`;;

let LARGE_INDUCTIVE_DIMENSION = `!s:real^N->bool n.
        dimension s <= n <=>
        if s = {} then -- &1 <= n else
        !c d. closed_in (subtopology euclidean s) c /\
              closed_in (subtopology euclidean s) d /\
              DISJOINT c d
              ==> ?b. closed_in (subtopology euclidean s) b /\
                      dimension b <= n - &1 /\
                      ?u v. open_in (subtopology euclidean s) u /\
                            open_in (subtopology euclidean s) v /\
                            DISJOINT u v /\ u UNION v = s DIFF b /\
                            c SUBSET u /\ d SUBSET v`;;

let TINY_INDUCTIVE_DIMENSION = `!s:real^N->bool n.
        locally compact s
        ==> (dimension s <= n <=>
             if s = {} then -- &1 <= n else
             &0 <= n /\
             !x y. x IN s /\ y IN s /\ ~(x = y)
                   ==> ?b. closed_in (subtopology euclidean s) b /\
                           dimension b <= n - &1 /\
                           ?u v. open_in (subtopology euclidean s) u /\
                                 open_in (subtopology euclidean s) v /\
                                 DISJOINT u v /\ u UNION v = s DIFF b /\
                                 x IN u /\ y IN v)`;;

let DIMENSION_LE_RATIONAL_COORDINATES = `!n. dimension {x:real^N | {i | i IN 1..dimindex(:N) /\ rational(x$i)}
                             HAS_SIZE n} <= &0`;;

let DIMENSION_EXACTLY_RATIONAL_COORDINATES = `!n. 1 <= n /\ n <= dimindex(:N)
       ==> dimension {x:real^N | {i | i IN 1..dimindex(:N) /\ rational(x$i)}
                                 HAS_SIZE n} = &0`;;

(* ------------------------------------------------------------------------- *)
(* Covering spaces and lifting results for them.                             *)
(* ------------------------------------------------------------------------- *)

let covering_space = new_definition
 `covering_space(c,(p:real^M->real^N)) s <=>
        p continuous_on c /\ IMAGE p c = s /\
        !x. x IN s
            ==> ?t. x IN t /\ open_in (subtopology euclidean s) t /\
                    ?v. UNIONS v = {x | x IN c /\ p(x) IN t} /\
                        (!u. u IN v ==> open_in (subtopology euclidean c) u) /\
                        pairwise DISJOINT v /\
                        (!u. u IN v ==> ?q. homeomorphism (u,t) (p,q))`;;

let COVERING_SPACE_IMP_CONTINUOUS = `!p:real^M->real^N c s. covering_space (c,p) s ==> p continuous_on c`;;

let COVERING_SPACE_IMP_SURJECTIVE = `!p:real^M->real^N c s. covering_space (c,p) s ==> IMAGE p c = s`;;

let HOMEOMORPHISM_IMP_COVERING_SPACE = `!f:real^M->real^N g s t.
        homeomorphism (s,t) (f,g) ==> covering_space (s,f) t`;;

let COVERING_SPACE_LOCAL_HOMEOMORPHISM = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !x. x IN c
                ==> ?t u. x IN t /\ open_in (subtopology euclidean c) t /\
                          p(x) IN u /\ open_in (subtopology euclidean s) u /\
                          ?q. homeomorphism (t,u) (p,q)`;;

let COVERING_SPACE_LOCAL_HOMEOMORPHISM_ALT = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !y. y IN s
                ==> ?x t u. p(x) = y /\
                            x IN t /\ open_in (subtopology euclidean c) t /\
                            y IN u /\ open_in (subtopology euclidean s) u /\
                            ?q. homeomorphism (t,u) (p,q)`;;

let COVERING_SPACE_OPEN_MAP = `!p:real^M->real^N c s t.
        covering_space (c,p) s /\
        open_in (subtopology euclidean c) t
        ==> open_in (subtopology euclidean s) (IMAGE p t)`;;

let COVERING_SPACE_QUOTIENT_MAP = `!p:real^M->real^N c s.
    covering_space (c,p) s
    ==> !u. u SUBSET s
            ==> (open_in (subtopology euclidean c) {x | x IN c /\ p x IN u} <=>
                 open_in (subtopology euclidean s) u)`;;

let COVERING_SPACE_LOCALIZED_HOMEOMORPHISM = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !w x. x IN w /\ open_in (subtopology euclidean c) w
                  ==> ?t u. x IN t /\ open_in (subtopology euclidean c) t /\
                            p(x) IN u /\ open_in (subtopology euclidean s) u /\
                            t SUBSET w /\
                            ?q. homeomorphism (t,u) (p,q)`;;

let COVERING_SPACE_LOCALIZED_HOMEOMORPHISM_ALT = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !w y. y IN w /\ open_in (subtopology euclidean s) w
                ==> ?x t u. p(x) = y /\
                            x IN t /\ open_in (subtopology euclidean c) t /\
                            y IN u /\ open_in (subtopology euclidean s) u /\
                            u SUBSET w /\
                            ?q. homeomorphism (t,u) (p,q)`;;

let COVERING_SPACE_LOCALLY_HOMEOMORPHIC = `!P Q p:real^M->real^N c s.
           covering_space (c,p) s /\
           (!q u v. ~(u = {}) /\ u SUBSET c /\ v SUBSET s /\
                    homeomorphism (u,v) (p,q) /\ P u
                    ==> Q v) /\
           locally P c
           ==> locally Q s`;;

let COVERING_SPACE_LOCALLY_HOMEOMORPHIC_EQ = `!P Q p:real^M->real^N c s.
           covering_space (c,p) s /\
           (!q u v. ~(u = {}) /\ u SUBSET c /\ v SUBSET s /\
                    homeomorphism (u,v) (p,q)
                    ==> (P u <=> Q v))
           ==> (locally P c <=> locally Q s)`;;

let COVERING_SPACE_LOCALLY = `!P Q p:real^M->real^N c s.
        covering_space (c,p) s /\ (!t. t SUBSET c /\ P t ==> Q(IMAGE p t)) /\
        locally P c
        ==> locally Q s`;;

let COVERING_SPACE_LOCALLY_EQ = `!P Q p:real^M->real^N c s.
        covering_space (c,p) s /\
        (!t. t SUBSET c /\ P t ==> Q(IMAGE p t)) /\
        (!q u. u SUBSET s /\ q continuous_on u /\ Q u ==> P(IMAGE q u))
        ==> (locally Q s <=> locally P c)`;;

let COVERING_SPACE_LOCALLY_COMPACT_EQ = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (locally compact s <=> locally compact c)`;;

let COVERING_SPACE_LOCALLY_CONNECTED_EQ = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (locally connected s <=> locally connected c)`;;

let COVERING_SPACE_LOCALLY_PATH_CONNECTED_EQ = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (locally path_connected s <=> locally path_connected c)`;;

let COVERING_SPACE_LOCALLY_COMPACT = `!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally compact c
        ==> locally compact s`;;

let COVERING_SPACE_LOCALLY_CONNECTED = `!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally connected c ==> locally connected s`;;

let COVERING_SPACE_LOCALLY_PATH_CONNECTED = `!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally path_connected c
        ==> locally path_connected s`;;

let COVERING_SPACE_LIFT_UNIQUE_GEN = `!p:real^M->real^N f:real^P->real^N g1 g2 c s t u a x.
        covering_space (c,p) s /\
        f continuous_on t /\ IMAGE f t SUBSET s /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g1 x)) /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g2 x)) /\
        u IN components t /\ a IN u /\ g1(a) = g2(a) /\ x IN u
        ==> g1(x) = g2(x)`;;

let COVERING_SPACE_LIFT_UNIQUE = `!p:real^M->real^N f:real^P->real^N g1 g2 c s t a x.
        covering_space (c,p) s /\
        f continuous_on t /\ IMAGE f t SUBSET s /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g1 x)) /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g2 x)) /\
        connected t /\ a IN t /\ g1(a) = g2(a) /\ x IN t
        ==> g1(x) = g2(x)`;;

let COVERING_SPACE_LIFT_UNIQUE_IDENTITY = `!p:real^M->real^N c f s a.
     covering_space (c,p) s /\
     path_connected c /\
     f continuous_on c /\ IMAGE f c SUBSET c /\
     (!x. x IN c ==> p(f x) = p x) /\
     a IN c /\ f(a) = a
     ==> !x. x IN c ==> f x = x`;;

let COVERING_SPACE_LIFT_HOMOTOPY = `!p:real^M->real^N c s (h:real^(1,P)finite_sum->real^N) f u.
        covering_space (c,p) s /\
        h continuous_on (interval[vec 0,vec 1] PCROSS u) /\
        IMAGE h (interval[vec 0,vec 1] PCROSS u) SUBSET s /\
        (!y. y IN u ==> h (pastecart (vec 0) y) = p(f y)) /\
        f continuous_on u /\ IMAGE f u SUBSET c
        ==> ?k. k continuous_on (interval[vec 0,vec 1] PCROSS u) /\
                IMAGE k (interval[vec 0,vec 1] PCROSS u) SUBSET c /\
                (!y. y IN u ==> k(pastecart (vec 0) y) = f y) /\
                (!z. z IN interval[vec 0,vec 1] PCROSS u ==> h z = p(k z))`;;

let COVERING_SPACE_LIFT_HOMOTOPIC_FUNCTION = `!p:real^M->real^N c s f f' g u:real^P->bool.
        covering_space (c,p) s /\
        g continuous_on u /\ IMAGE g u SUBSET c /\
        (!y. y IN u ==> p(g y) = f y) /\
        homotopic_with (\x. T)
         (subtopology euclidean u,subtopology euclidean s) f f'
        ==> ?g'. g' continuous_on u /\ IMAGE g' u SUBSET c /\
                 (!y. y IN u ==> p(g' y) = f' y)`;;

let COVERING_SPACE_LIFT_INESSENTIAL_FUNCTION = `!p:real^M->real^N c s f a u:real^P->bool.
        covering_space (c,p) s /\
        homotopic_with (\x. T)
         (subtopology euclidean u,subtopology euclidean s) f (\x. a)
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                (!y. y IN u ==> p(g y) = f y)`;;

let COVERING_SPACE_LIFT_HOMOTOPY_ALT = `!p:real^M->real^N c s (h:real^(P,1)finite_sum->real^N) f u.
        covering_space (c,p) s /\
        h continuous_on (u PCROSS interval[vec 0,vec 1]) /\
        IMAGE h (u PCROSS interval[vec 0,vec 1]) SUBSET s /\
        (!y. y IN u ==> h (pastecart y (vec 0)) = p(f y)) /\
        f continuous_on u /\ IMAGE f u SUBSET c
        ==> ?k. k continuous_on (u PCROSS interval[vec 0,vec 1]) /\
                IMAGE k (u PCROSS interval[vec 0,vec 1]) SUBSET c /\
                (!y. y IN u ==> k(pastecart y (vec 0)) = f y) /\
                (!z. z IN u PCROSS interval[vec 0,vec 1] ==> h z = p(k z))`;;

let COVERING_SPACE_LIFT_PATH_STRONG = `!p:real^M->real^N c s g a.
     covering_space (c,p) s /\
     path g /\ path_image g SUBSET s /\ pathstart g = p(a) /\ a IN c
     ==> ?h. path h /\ path_image h SUBSET c /\ pathstart h = a /\
             !t. t IN interval[vec 0,vec 1] ==> p(h t) = g t`;;

let COVERING_SPACE_LIFT_PATH = `!p:real^M->real^N c s g.
     covering_space (c,p) s /\ path g /\ path_image g SUBSET s
     ==> ?h. path h /\ path_image h SUBSET c /\
             !t. t IN interval[vec 0,vec 1] ==> p(h t) = g t`;;

let COVERING_SPACE_LIFT_HOMOTOPIC_PATHS = `!p:real^M->real^N c s g1 g2 h1 h2.
     covering_space (c,p) s /\
     path g1 /\ path_image g1 SUBSET s /\
     path g2 /\ path_image g2 SUBSET s /\
     homotopic_paths s g1 g2 /\
     path h1 /\ path_image h1 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h1 t) = g1 t) /\
     path h2 /\ path_image h2 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h2 t) = g2 t) /\
     pathstart h1 = pathstart h2
     ==> homotopic_paths c h1 h2`;;

let COVERING_SPACE_MONODROMY = `!p:real^M->real^N c s g1 g2 h1 h2.
     covering_space (c,p) s /\
     path g1 /\ path_image g1 SUBSET s /\
     path g2 /\ path_image g2 SUBSET s /\
     homotopic_paths s g1 g2 /\
     path h1 /\ path_image h1 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h1 t) = g1 t) /\
     path h2 /\ path_image h2 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h2 t) = g2 t) /\
     pathstart h1 = pathstart h2
     ==> pathfinish h1 = pathfinish h2`;;

let COVERING_SPACE_LIFT_HOMOTOPIC_PATH = `!p:real^M->real^N c s f f' g a b.
        covering_space (c,p) s /\
        homotopic_paths s f f' /\
        path g /\ path_image g SUBSET c /\
        pathstart g = a /\ pathfinish g = b /\
        (!t. t IN interval[vec 0,vec 1] ==> p(g t) = f t)
        ==> ?g'. path g' /\ path_image g' SUBSET c /\
                 pathstart g' = a /\ pathfinish g' = b /\
                 (!t. t IN interval[vec 0,vec 1] ==> p(g' t) = f' t)`;;

let COVERING_SPACE_INESSENTIAL_LOOP_LIFT_IS_LOOP = `!p:real^M->real^N c s g h a.
        covering_space (c,p) s /\
        path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g /\
        homotopic_paths s g (linepath(a,a)) /\
        path h /\ path_image h SUBSET c /\
        (!t. t IN interval[vec 0,vec 1] ==> p(h t) = g t)
        ==> pathfinish h = pathstart h`;;

let COVERING_SPACE_SIMPLY_CONNECTED_LOOP_LIFT_IS_LOOP = `!p:real^M->real^N c s g h.
        covering_space (c,p) s /\ simply_connected s /\
        path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g /\
        path h /\ path_image h SUBSET c /\
        (!t. t IN interval[vec 0,vec 1] ==> p(h t) = g t)
        ==> pathfinish h = pathstart h`;;

let COVERING_SPACE_HOMOTOPIC_PATHS_CANCEL = `!p:real^M->real^N c s g h.
        covering_space (c,p) s /\
        path g /\ path_image g SUBSET c /\
        path h /\ path_image h SUBSET c /\
        pathstart g = pathstart h /\
        homotopic_paths s (p o g) (p o h)
        ==> homotopic_paths c g h`;;

let COVERING_SPACE_HOMOTOPIC_PATHS_CANCEL_EQ = `!p:real^M->real^N c s g h.
        covering_space (c,p) s /\
        path g /\ path_image g SUBSET c /\
        path h /\ path_image h SUBSET c /\
        pathstart g = pathstart h
        ==> (homotopic_paths s (p o g) (p o h) <=> homotopic_paths c g h)`;;

(* ------------------------------------------------------------------------- *)
(* Lifting of general functions to covering space                            *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_LIFT_GENERAL = `!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        path_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a /\
        (!r. path r /\ path_image r SUBSET u /\
             pathstart r = z /\ pathfinish r = z
             ==> ?q. path q /\ path_image q SUBSET c /\
                     pathstart q = a /\ pathfinish q = a /\
                     homotopic_paths s (f o r) (p o q))
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`;;

let COVERING_SPACE_LIFT_STRONGER = `!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        path_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a /\
        (!r. path r /\ path_image r SUBSET u /\
             pathstart r = z /\ pathfinish r = z
             ==> ?b. homotopic_paths s (f o r) (linepath(b,b)))
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`;;

let COVERING_SPACE_LIFT_STRONG = `!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        simply_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`;;

let COVERING_SPACE_LIFT = `!p:real^M->real^N c s f:real^P->real^N u.
        covering_space (c,p) s /\
        simply_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                (!y. y IN u ==> p(g y) = f y)`;;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas about covering spaces.                             *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_COVERING_MAP_FIBRES = `!p:real^M->real^N c s a b.
        covering_space (c,p) s /\ path_connected s /\ a IN s /\ b IN s
        ==> {x | x IN c /\ p(x) = a} =_c {x | x IN c /\ p(x) = b}`;;

let COVERING_SPACE_INJECTIVE = `!p:real^M->real^N c s.
        covering_space (c,p) s /\ path_connected c /\ simply_connected s
        ==> (!x y. x IN c /\ y IN c /\ p x = p y ==> x = y)`;;

let COVERING_SPACE_HOMEOMORPHISM = `!p:real^M->real^N c s.
        covering_space (c,p) s /\ path_connected c /\ simply_connected s
        ==> ?q. homeomorphism (c,s) (p,q)`;;

(* ------------------------------------------------------------------------- *)
(* Results on finiteness of the number of sheets in a covering space.        *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_FIBRE_NO_LIMPT = `!p:real^M->real^N c s a b.
        covering_space (c,p) s /\ a IN c
        ==> ~(a limit_point_of {x | x IN c /\ p x = b})`;;

let COVERING_SPACE_COUNTABLE_SHEETS = `!p:real^M->real^N c s b.
        covering_space (c,p) s ==> COUNTABLE {x | x IN c /\ p x = b}`;;

let COVERING_SPACE_FINITE_EQ_COMPACT_FIBRE = `!p:real^M->real^N c s b.
        covering_space (c,p) s
        ==> (FINITE {x | x IN c /\ p x = b} <=>
             compact {x | x IN c /\ p x = b})`;;

let COVERING_SPACE_CLOSED_MAP = `!p:real^M->real^N c s t.
        covering_space (c,p) s /\
        (!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) /\
        closed_in (subtopology euclidean c) t
        ==> closed_in (subtopology euclidean s) (IMAGE p t)`;;

let COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP_STRONG = `!p:real^M->real^N c s.
        covering_space (c,p) s /\ (!b. b IN s ==> b limit_point_of s)
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!t. closed_in (subtopology euclidean c) t
                  ==> closed_in (subtopology euclidean s) (IMAGE p t)))`;;

let COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP = `!p:real^M->real^N c s.
        covering_space (c,p) s /\ connected s /\ ~(?a. s = {a})
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!t. closed_in (subtopology euclidean c) t
                  ==> closed_in (subtopology euclidean s) (IMAGE p t)))`;;

let COVERING_SPACE_FINITE_SHEETS_EQ_PROPER_MAP = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!k. k SUBSET s /\ compact k
                  ==> compact {x | x IN c /\ p(x) IN k}))`;;

(* ------------------------------------------------------------------------- *)
(* Special cases where one or both of the sets is compact.                   *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_FINITE_SHEETS = `!p:real^M->real^N c s b.
      covering_space (c,p) s /\ compact c ==> FINITE {x | x IN c /\ p x = b}`;;

let COVERING_SPACE_COMPACT = `!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (compact c <=>
             compact s /\ (!b. b IN s ==> FINITE {x | x IN c /\ p x = b}))`;;

(* ------------------------------------------------------------------------- *)
(* A proper (or closed) local homeomorphism is in fact a covering map.       *)
(* ------------------------------------------------------------------------- *)

let PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP = `!p:real^M->real^N c s.
        IMAGE p c = s /\
        (!k. k SUBSET s /\ compact k ==> compact {x | x IN c /\ p x IN k}) /\
        (!x. x IN c
             ==> ?t u q. x IN t /\
                         open_in (subtopology euclidean c) t /\
                         open_in (subtopology euclidean s) u /\
                         homeomorphism (t,u) (p,q))
        ==> covering_space (c,p) s`;;

let CLOSED_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP = `!p:real^M->real^N c s.
        (!x. connected_component c x = {x} ==> c = {x}) /\
        IMAGE p c = s /\
        (!k. closed_in (subtopology euclidean c) k
             ==> closed_in (subtopology euclidean s) (IMAGE p k)) /\
        (!x. x IN c
             ==> ?t u q. x IN t /\
                         open_in (subtopology euclidean c) t /\
                         open_in (subtopology euclidean s) u /\
                         homeomorphism (t,u) (p,q))
        ==> covering_space (c,p) s`;;

let PROPER_LOCAL_HOMEOMORPHISM_GLOBAL = `!f:real^M->real^N s t.
        path_connected s /\ simply_connected t /\ (s = {} ==> t = {}) /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        (!x. x IN s
             ==> ?u v q. x IN u /\
                         open_in (subtopology euclidean s) u /\
                         open_in (subtopology euclidean t) v /\
                         homeomorphism (u,v) (f,q))
        ==> ?g. homeomorphism (s,t) (f,g)`;;

let CLOSED_LOCAL_HOMEOMORPHISM_GLOBAL = `!f:real^M->real^N s t.
        path_connected s /\ simply_connected t /\ (s = {} ==> t = {}) /\
        (!c. closed_in (subtopology euclidean s) c
             ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
        (!x. x IN s
             ==> ?u v g. x IN u /\
                         open_in (subtopology euclidean s) u /\
                         open_in (subtopology euclidean t) v /\
                         homeomorphism (u,v) (f,g))
        ==> ?g. homeomorphism (s,t) (f,g)`;;

let PROPER_LOCALLY_INJECTIVE_OPEN_IMP_COVERING_MAP = `!p:real^M->real^N c s.
        p continuous_on c /\ IMAGE p c = s /\
        (!k. k SUBSET s /\ compact k ==> compact {x | x IN c /\ p x IN k}) /\
        (!u. open_in (subtopology euclidean c) u
             ==> open_in (subtopology euclidean s) (IMAGE p u)) /\
        (!x. x IN c
             ==> ?t. x IN t /\ open_in (subtopology euclidean c) t /\
                     (!y z. y IN t /\ z IN t /\ p y = p z ==> y = z))
        ==> covering_space (c,p) s`;;

let PROPER_LOCALLY_INJECTIVE_OPEN_IMP_COVERING_MAP_GEN = `!p:real^M->real^N c s.
        p continuous_on c /\ IMAGE p c = s /\
        (!k. k SUBSET s /\ compact k ==> compact {x | x IN c /\ p x IN k}) /\
        (!u. open_in (subtopology euclidean c) u
             ==> open_in (subtopology euclidean c)
                         {x | x IN c /\ p x IN IMAGE p u}) /\
        (!x. x IN c
             ==> ?t. x IN t /\ open_in (subtopology euclidean c) t /\
                     (!y z. y IN t /\ z IN t /\ p y = p z ==> y = z))
        ==> covering_space (c,p) s`;;

let PROPER_LOCALLY_INJECTIVE_OPEN_IMP_HOMEOMORPHISM = `!f:real^M->real^N s t.
        path_connected s /\ simply_connected t /\
        f continuous_on s /\ IMAGE f s = t /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        (!x. x IN s
             ==> ?u. x IN u /\ open_in (subtopology euclidean s) u /\
                     !y z. y IN u /\ z IN u /\ f y = f z ==> y = z)
        ==> ?g. homeomorphism (s,t) (f,g)`;;

let PROPER_LOCALLY_INJECTIVE_OPEN_IMP_HOMEOMORPHISM_GEN = `!f:real^M->real^N s t.
        path_connected s /\ simply_connected t /\
        f continuous_on s /\ IMAGE f s = t /\
        (!k. k SUBSET t /\ compact k ==> compact {x | x IN s /\ f x IN k}) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean s)
                         {x | x IN s /\ f x IN IMAGE f u}) /\
        (!x. x IN s
             ==> ?u. x IN u /\ open_in (subtopology euclidean s) u /\
                     !y z. y IN u /\ z IN u /\ f y = f z ==> y = z)
        ==> ?g. homeomorphism (s,t) (f,g)`;;

(* ------------------------------------------------------------------------- *)
(* A simply connected covering space is universal.                           *)
(* ------------------------------------------------------------------------- *)

let UNIVERSAL_COVERING_SPACE = `!c p:real^M->real^P c' p':real^N->real^P s.
        covering_space (c,p) s /\ covering_space (c',p') s /\
        locally path_connected c /\ simply_connected c /\ connected c'
        ==> ?q. covering_space (c,q) c' /\ !x. x IN c ==> p'(q x) = p x`;;

(* ------------------------------------------------------------------------- *)
(* Size of fundamental group of a covering space (this could be generalized  *)
(* with structural properties of the bijections of course).                  *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_FUNDAMENTAL_GROUP_COVERING_SPACE_ALT = `!p:real^M->real^N c s a.
        covering_space(c,p) s /\ path_connected c /\ a IN c
        ==> fundamental_group(s,p a) =_c
            {homotopic_paths c g |g| path g /\ path_image g SUBSET c /\
                                     pathstart g = a /\
                                     p(pathfinish g) = p a}`;;

let CARD_EQ_FUNDAMENTAL_GROUP_COVERING_SPACE = `!p:real^M->real^N c s a.
        covering_space(c,p) s /\ path_connected c /\ a IN c
        ==> fundamental_group(s,p a) =_c
            fundamental_group(c,a) *_c {a' | a' IN c /\ p a' = p a}`;;

let COVERING_SPACE_SELF_FINITE_FUNDAMENTAL_GROUP = `!p s a:real^N.
        covering_space (s,p) s /\ path_connected s /\
        a IN s /\ FINITE(fundamental_group(s,a))
        ==> ?q. homeomorphism (s,s) (p,q)`;;

(* ------------------------------------------------------------------------- *)
(* Invariance of dimension and domain in setting of R^n.                     *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_SUBSPACE_EUCLIDEAN_SPACE = `!(s:real^N->bool) n.
        subspace s
        ==> (subtopology euclidean s homeomorphic_space euclidean_space n <=>
             dim s = n)`;;

let HOMEOMORPHIC_SUBSPACE_EUCLIDEAN_SPACE_DIM = `!(s:real^N->bool).
       subspace s
       ==> subtopology euclidean s homeomorphic_space euclidean_space (dim s)`;;

let HOMEOMORPHIC_SUBSPACES_EQ = `!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> (s homeomorphic t <=> dim s = dim t)`;;

let HOMEOMORPHIC_AFFINE_EUCLIDEAN_SPACE = `!(s:real^N->bool) n.
        affine s
        ==> (subtopology euclidean s homeomorphic_space euclidean_space n <=>
             aff_dim s = &n)`;;

let HOMEOMORPHIC_AFFINE_SETS_EQ = `!s:real^M->bool t:real^N->bool.
        affine s /\ affine t ==> (s homeomorphic t <=> aff_dim s = aff_dim t)`;;

let INVARIANCE_OF_DOMAIN_SUBSPACES = `!f:real^M->real^N u v s.
        subspace u /\ subspace v /\ dim v <= dim u /\
        f continuous_on s /\ IMAGE f s SUBSET v /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean v) (IMAGE f s)`;;

let INVARIANCE_OF_DOMAIN = `!f:real^N->real^N s.
        f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> open(IMAGE f s)`;;

let INVARIANCE_OF_DIMENSION_SUBSPACES = `!f:real^M->real^N u v s.
      subspace u /\ subspace v /\
      ~(s = {}) /\ open_in (subtopology euclidean u) s /\
      f continuous_on s /\ IMAGE f s SUBSET v /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
      ==> dim u <= dim v`;;

let INVARIANCE_OF_DOMAIN_AFFINE_SETS = `!f:real^M->real^N u v s.
        affine u /\ affine v /\ aff_dim v <= aff_dim u /\
        f continuous_on s /\ IMAGE f s SUBSET v /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean v) (IMAGE f s)`;;

let INVARIANCE_OF_DIMENSION_AFFINE_SETS = `!f:real^M->real^N u v s.
      affine u /\ affine v /\
      ~(s = {}) /\ open_in (subtopology euclidean u) s /\
      f continuous_on s /\ IMAGE f s SUBSET v /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
      ==> aff_dim u <= aff_dim v`;;

let INVARIANCE_OF_DIMENSION = `!f:real^M->real^N s.
        f continuous_on s /\ open s /\ ~(s = {}) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)`;;

let CONTINUOUS_INJECTIVE_IMAGE_SUBSPACE_DIM_LE = `!f:real^M->real^N s t.
        subspace s /\ subspace t /\
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> dim(s) <= dim(t)`;;

let INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN = `!f:real^M->real^N s t.
        convex s /\ f continuous_on s /\ IMAGE f s SUBSET affine hull t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> aff_dim(s) <= aff_dim(t)`;;

let HOMEOMORPHIC_CONVEX_SETS = `!s:real^M->bool t:real^N->bool.
        convex s /\ convex t /\ s homeomorphic t ==> aff_dim s = aff_dim t`;;

let HOMEOMORPHIC_CONVEX_COMPACT_SETS_EQ = `!s:real^M->bool t:real^N->bool.
        convex s /\ compact s /\ convex t /\ compact t
        ==> (s homeomorphic t <=> aff_dim s = aff_dim t)`;;

let INVARIANCE_OF_DOMAIN_GEN = `!f:real^M->real^N s.
        dimindex(:N) <= dimindex(:M) /\ f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> open(IMAGE f s)`;;

let INJECTIVE_INTO_1D_IMP_OPEN_MAP_UNIV = `!f:real^N->real^1 s t.
        f continuous_on s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open t /\ t SUBSET s
        ==> open (IMAGE f t)`;;

let CONTINUOUS_ON_INVERSE_OPEN = `!f:real^M->real^N g s.
        dimindex(:N) <= dimindex(:M) /\
        f continuous_on s /\ open s /\
        (!x. x IN s ==> g(f x) = x)
        ==> g continuous_on IMAGE f s`;;

let CONTINUOUS_ON_INVERSE_INTO_1D = `!f:real^N->real^1 g s t.
        f continuous_on s /\
        (path_connected s \/
         connected s /\ (locally compact s \/ locally connected s) \/
         compact s \/
         open s) /\
        IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x)
        ==> g continuous_on t`;;

let INVARIANCE_OF_DOMAIN_HOMEOMORPHISM = `!f:real^M->real^N s.
        dimindex(:N) <= dimindex(:M) /\ f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ?g. homeomorphism (s,IMAGE f s) (f,g)`;;

let INVARIANCE_OF_DOMAIN_HOMEOMORPHIC = `!f:real^M->real^N s.
        dimindex(:N) <= dimindex(:M) /\ f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> s homeomorphic (IMAGE f s)`;;

let HOMEOMORPHIC_INTERVALS_EQ = `(!a b:real^M c d:real^N.
        interval[a,b] homeomorphic interval[c,d] <=>
        aff_dim(interval[a,b]) = aff_dim(interval[c,d])) /\
   (!a b:real^M c d:real^N.
        interval[a,b] homeomorphic interval(c,d) <=>
        interval[a,b] = {} /\ interval(c,d) = {}) /\
   (!a b:real^M c d:real^N.
        interval(a,b) homeomorphic interval[c,d] <=>
        interval(a,b) = {} /\ interval[c,d] = {}) /\
   (!a b:real^M c d:real^N.
        interval(a,b) homeomorphic interval(c,d) <=>
        interval(a,b) = {} /\ interval(c,d) = {} \/
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {}) /\
        dimindex(:M) = dimindex(:N))`;;

let CONTINUOUS_IMAGE_SUBSET_INTERIOR = `!f:real^M->real^N s.
        f continuous_on s /\ dimindex(:N) <= dimindex(:M) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f (interior s) SUBSET interior(IMAGE f s)`;;

let HOMEOMORPHIC_INTERIORS_SAME_DIMENSION = `!s:real^M->bool t:real^N->bool.
        dimindex(:M) = dimindex(:N) /\ s homeomorphic t
        ==> (interior s) homeomorphic (interior t)`;;

let HOMEOMORPHIC_INTERIORS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ (interior s = {} <=> interior t = {})
        ==> (interior s) homeomorphic (interior t)`;;

let HOMEOMORPHIC_FRONTIERS_SAME_DIMENSION = `!s:real^M->bool t:real^N->bool.
        dimindex(:M) = dimindex(:N) /\
        s homeomorphic t /\ closed s /\ closed t
        ==> (frontier s) homeomorphic (frontier t)`;;

let HOMEOMORPHIC_FRONTIERS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ closed s /\ closed t /\
        (interior s = {} <=> interior t = {})
        ==> (frontier s) homeomorphic (frontier t)`;;

let CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ aff_dim t <= aff_dim s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f (relative_interior s) SUBSET relative_interior(IMAGE f s)`;;

let HOMEOMORPHIC_RELATIVE_INTERIORS_SAME_DIMENSION = `!s:real^M->bool t:real^N->bool.
        aff_dim s = aff_dim t /\ s homeomorphic t
        ==> (relative_interior s) homeomorphic (relative_interior t)`;;

let HOMEOMORPHIC_RELATIVE_INTERIORS = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\
        (relative_interior s = {} <=> relative_interior t = {})
        ==> (relative_interior s) homeomorphic (relative_interior t)`;;

let HOMEOMORPHIC_RELATIVE_BOUNDARIES_SAME_DIMENSION = `!s:real^M->bool t:real^N->bool.
        aff_dim s = aff_dim t /\ s homeomorphic t
        ==> (s DIFF relative_interior s) homeomorphic
            (t DIFF relative_interior t)`;;

let HOMEOMORPHIC_RELATIVE_BOUNDARIES = `!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\
        (relative_interior s = {} <=> relative_interior t = {})
        ==> (s DIFF relative_interior s) homeomorphic
            (t DIFF relative_interior t)`;;

let UNIFORMLY_CONTINUOUS_HOMEOMORPHISM_UNIV_TRIVIAL = `!f g s:real^N->bool.
        homeomorphism (s,(:real^N)) (f,g) /\ f uniformly_continuous_on s
        ==> s = (:real^N)`;;

let INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET_GEN = `!f:real^M->real^N u s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        bounded u /\ convex u /\ affine t /\ aff_dim t < aff_dim u /\
        open_in (subtopology euclidean (relative_frontier u)) s
        ==> open_in (subtopology euclidean t) (IMAGE f s)`;;

let INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET = `!f:real^M->real^N a r s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        ~(r = &0) /\ affine t /\ aff_dim t < &(dimindex(:M)) /\
        open_in (subtopology euclidean (sphere(a,r))) s
        ==> open_in (subtopology euclidean t) (IMAGE f s)`;;

let NO_EMBEDDING_SPHERE_LOWDIM = `!f:real^M->real^N a r.
        &0 < r /\
        f continuous_on sphere(a,r) /\
        (!x y. x IN sphere(a,r) /\ y IN sphere(a,r) /\ f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)`;;

let EMPTY_INTERIOR_LOWDIM_GEN = `!s:real^N->bool t:real^M->bool.
        dimindex(:M) < dimindex(:N) /\ s homeomorphic t ==> interior s = {}`;;

let EMPTY_INTERIOR_LOWDIM_GEN_LE = `!s:real^N->bool t:real^M->bool.
        dimindex(:M) <= dimindex(:N) /\
        interior t = {} /\
        s homeomorphic t
        ==> interior s = {}`;;

let HOMEOMORPHIC_HYPERPLANES_EQ = `!a:real^M b c:real^N d.
        ~(a = vec 0) /\ ~(c = vec 0)
        ==> ({x | a dot x = b} homeomorphic {x | c dot x = d} <=>
             dimindex(:M) = dimindex(:N))`;;

let HOMEOMORPHIC_UNIV_UNIV = `(:real^M) homeomorphic (:real^N) <=> dimindex(:M) = dimindex(:N)`;;

let HOMEOMORPHIC_CBALLS_EQ = `!a:real^M b:real^N r s.
        cball(a,r) homeomorphic cball(b,s) <=>
        r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N)`;;

let HOMEOMORPHIC_BALLS_EQ = `!a:real^M b:real^N r s.
        ball(a,r) homeomorphic ball(b,s) <=>
        r <= &0 /\ s <= &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N)`;;

(* ------------------------------------------------------------------------- *)
(* General forms of the Jordan curve theorem in setting of R^n.              *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_COMPONENTS_COMPLEMENTS = `!s t:real^N->bool.
        closed s /\ closed t /\ s homeomorphic t
        ==> components((:real^N) DIFF s) =_c components((:real^N) DIFF t)`;;

let JORDAN_CURVE_THEOREM_GEN = `!s:real^N->bool.
        2 <= dimindex(:N) /\ s homeomorphic sphere(vec 0:real^N,&1)
        ==> ?ins out.
                 ~(ins = {}) /\ open ins /\ connected ins /\
                 ~(out = {}) /\ open out /\ connected out /\
                 bounded ins /\ ~bounded out /\
                 ins INTER out = {} /\
                 ins UNION out = (:real^N) DIFF s /\
                 frontier ins = s /\
                 frontier out = s`;;

let JORDAN_INSIDE_OUTSIDE_GEN = `!s:real^N->bool.
        2 <= dimindex(:N) /\ s homeomorphic sphere(vec 0:real^N,&1)
        ==> ~(inside s = {}) /\
            open(inside s) /\
            connected(inside s) /\
            ~(outside s = {}) /\
            open(outside s) /\
            connected(outside s) /\
            bounded(inside s) /\
            ~bounded(outside s) /\
            inside s INTER outside s = {} /\
            inside s UNION outside s = (:real^N) DIFF s /\
            frontier(inside s) = s /\
            frontier(outside s) = s`;;

let JORDAN_BROUWER_FRONTIER = `!s t a:real^N r.
     2 <= dimindex(:N) /\
     s homeomorphic sphere(a,r) /\ t IN components((:real^N) DIFF s)
     ==> frontier t = s`;;

let JORDAN_BROUWER_NONSEPARATION = `!s t a:real^N r.
        2 <= dimindex(:N) /\
        s homeomorphic sphere(a,r) /\ t PSUBSET s
        ==> connected((:real^N) DIFF t)`;;

let JORDAN_BROUWER_SEPARATION = `!s a:real^N r.
        &0 < r /\ s homeomorphic sphere(a,r) ==> ~connected((:real^N) DIFF s)`;;

let JORDAN_CURVE_THEOREM = `!c:real^1->real^2.
        simple_path c /\ pathfinish c = pathstart c
        ==> ?ins out.
                 ~(ins = {}) /\ open ins /\ connected ins /\
                 ~(out = {}) /\ open out /\ connected out /\
                 bounded ins /\ ~bounded out /\
                 ins INTER out = {} /\
                 ins UNION out = (:real^2) DIFF path_image c /\
                 frontier ins = path_image c /\
                 frontier out = path_image c`;;

let JORDAN_DISCONNECTED = `!c. simple_path c /\ pathfinish c = pathstart c
       ==> ~connected((:real^2) DIFF path_image c)`;;

let JORDAN_INSIDE_OUTSIDE = `!c:real^1->real^2.
        simple_path c /\ pathfinish c = pathstart c
        ==> ~(inside(path_image c) = {}) /\
            open(inside(path_image c)) /\
            connected(inside(path_image c)) /\
            ~(outside(path_image c) = {}) /\
            open(outside(path_image c)) /\
            connected(outside(path_image c)) /\
            bounded(inside(path_image c)) /\
            ~bounded(outside(path_image c)) /\
            inside(path_image c) INTER outside(path_image c) = {} /\
            inside(path_image c) UNION outside(path_image c) =
            (:real^2) DIFF path_image c /\
            frontier(inside(path_image c)) = path_image c /\
            frontier(outside(path_image c)) = path_image c`;;

let JORDAN_COMPONENTS = `!g. simple_path g /\ pathfinish g = pathstart g
       ==> components((:real^2) DIFF path_image g) =
           {inside(path_image g),outside(path_image g)}`;;

let HOMEOMORPHIC_SEPARATION_SPHERE_CARD_EQ = `!s t:real^N->bool a r.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\
      closed s /\ closed t /\ s homeomorphic t
      ==> (components(sphere(a,r) DIFF s) =_c components(sphere(a,r) DIFF t))`;;

let HOMEOMORPHIC_SEPARATION_SPHERE_HAS_SIZE_EQ = `!s t:real^N->bool a r n.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\ s homeomorphic t
      ==> (components(sphere(a,r) DIFF s) HAS_SIZE n <=>
           components(sphere(a,r) DIFF t) HAS_SIZE n)`;;

let HOMEOMORPHIC_SEPARATION_SPHERE = `!s t:real^N->bool a r.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\ s homeomorphic t
      ==> (connected (sphere(a,r) DIFF s) <=> connected(sphere(a,r) DIFF t))`;;

let HAS_SIZE_EQ_COMPONENTS_COMPLEMENTS = `!s (t:real^N->bool) n.
        (closed s /\ closed t \/ bounded s /\ bounded t) /\
        s homeomorphic t
        ==> (components((:real^N) DIFF s) HAS_SIZE n <=>
             components((:real^N) DIFF t) HAS_SIZE n)`;;

let HOMEOMORPHIC_SEPARATION = `!s t. bounded s /\ bounded t /\ s homeomorphic t
         ==> (connected((:real^N) DIFF s) <=> connected((:real^N) DIFF t))`;;
