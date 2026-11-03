(* ========================================================================= *)
(* Lebesgue measure, measurable functions (defined via the gauge integral).  *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Library/card.ml";;
needs "Library/permutations.ml";;
needs "Multivariate/integration.ml";;
needs "Multivariate/determinants.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Lebesgue measure in the case where the measure is finite. This is our     *)
(* default notion of "measurable", but we also define "lebesgue_measurable"  *)
(* further down. Note that in neither case do we assume the set is bounded.  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_measure",(12,"right"));;

let has_measure = new_definition
 `s has_measure m <=> ((\x. vec 1) has_integral (lift m)) s`;;

let measurable = new_definition
 `measurable s <=> ?m. s has_measure m`;;

let measure = new_definition
 `measure s = @m. s has_measure m`;;

let HAS_MEASURE_MEASURE = `!s. measurable s <=> s has_measure (measure s)`;;

let HAS_MEASURE_UNIQUE = `!s m1 m2. s has_measure m1 /\ s has_measure m2 ==> m1 = m2`;;

let MEASURE_UNIQUE = `!s m. s has_measure m ==> measure s = m`;;

let HAS_MEASURE_MEASURABLE_MEASURE = `!s m. s has_measure m <=> measurable s /\ measure s = m`;;

let HAS_MEASURE_IMP_MEASURABLE = `!s m. s has_measure m ==> measurable s`;;

let HAS_MEASURE = `!s m. s has_measure m <=>
              ((\x. if x IN s then vec 1 else vec 0) has_integral (lift m))
              (:real^N)`;;

let MEASURABLE = `!s. measurable s <=> (\x. vec 1:real^1) integrable_on s`;;

let MEASURABLE_INTEGRABLE = `measurable s <=>
     (\x. if x IN s then vec 1 else vec 0:real^1) integrable_on UNIV`;;

let MEASURE_INTEGRAL = `!s. measurable s ==> measure s = drop (integral s (\x. vec 1))`;;

let MEASURE_INTEGRAL_UNIV = `!s. measurable s
       ==> measure s =
           drop(integral UNIV (\x. if x IN s then vec 1 else vec 0))`;;

let INTEGRAL_MEASURE = `!s. measurable s ==> integral s (\x. vec 1) = lift(measure s)`;;

let INTEGRAL_MEASURE_UNIV = `!s. measurable s
       ==> integral UNIV (\x. if x IN s then vec 1 else vec 0) =
           lift(measure s)`;;

let INTEGRABLE_ON_INDICATOR = `!s t:real^N->bool. indicator s integrable_on t <=> measurable(s INTER t)`;;

let ABSOLUTELY_INTEGRABLE_ON_INDICATOR = `!s t:real^N->bool.
    indicator s absolutely_integrable_on t <=> measurable(s INTER t)`;;

let INTEGRAL_INDICATOR = `!s t:real^M->bool.
      measurable(s INTER t)
      ==> integral t (indicator s) = lift(measure(s INTER t))`;;

let HAS_MEASURE_INTERVAL = `(!a b:real^N. interval[a,b] has_measure content(interval[a,b])) /\
   (!a b:real^N. interval(a,b) has_measure content(interval[a,b]))`;;

let MEASURABLE_INTERVAL = `(!a b:real^N. measurable (interval[a,b])) /\
   (!a b:real^N. measurable (interval(a,b)))`;;

let MEASURE_INTERVAL = `(!a b:real^N. measure(interval[a,b]) = content(interval[a,b])) /\
   (!a b:real^N. measure(interval(a,b)) = content(interval[a,b]))`;;

let MEASURE_INTERVAL_1 = `(!a b:real^1. measure(interval[a,b]) =
                    if drop a <= drop b then drop b - drop a else &0) /\
   (!a b:real^1. measure(interval(a,b)) =
                    if drop a <= drop b then drop b - drop a else &0)`;;

let MEASURE_INTERVAL_1_ALT = `(!a b:real^1. measure(interval[a,b]) =
                    if drop a < drop b then drop b - drop a else &0) /\
   (!a b:real^1. measure(interval(a,b)) =
                    if drop a < drop b then drop b - drop a else &0)`;;

let MEASURE_INTERVAL_2 = `(!a b:real^2. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0) /\
   (!a b:real^2. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0)`;;

let MEASURE_INTERVAL_2_ALT = `(!a b:real^2. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0) /\
   (!a b:real^2. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0)`;;

let MEASURE_INTERVAL_3 = `(!a b:real^3. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0) /\
   (!a b:real^3. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0)`;;

let MEASURE_INTERVAL_3_ALT = `(!a b:real^3. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0) /\
   (!a b:real^3. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0)`;;

let MEASURE_INTERVAL_4 = `(!a b:real^4. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3 /\ a$4 <= b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0) /\
   (!a b:real^4. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3 /\ a$4 <= b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0)`;;

let MEASURE_INTERVAL_4_ALT = `(!a b:real^4. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3 /\ a$4 < b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0) /\
   (!a b:real^4. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3 /\ a$4 < b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0)`;;

let MEASURABLE_INTER = `!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s INTER t)`;;

let MEASURABLE_UNION = `!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s UNION t)`;;

let HAS_MEASURE_DISJOINT_UNION = `!s1 s2 m1 m2. s1 has_measure m1 /\ s2 has_measure m2 /\ DISJOINT s1 s2
                 ==> (s1 UNION s2) has_measure (m1 + m2)`;;

let MEASURE_DISJOINT_UNION = `!s t. measurable s /\ measurable t /\ DISJOINT s t
         ==> measure(s UNION t) = measure s + measure t`;;

let MEASURE_DISJOINT_UNION_EQ = `!s t u.
        measurable s /\ measurable t /\ s UNION t = u /\ DISJOINT s t
        ==> measure s + measure t = measure u`;;

let HAS_MEASURE_POS_LE = `!m s:real^N->bool. s has_measure m ==> &0 <= m`;;

let MEASURE_POS_LE = `!s. measurable s ==> &0 <= measure s`;;

let HAS_MEASURE_SUBSET = `!s1 s2:real^N->bool m1 m2.
        s1 has_measure m1 /\ s2 has_measure m2 /\ s1 SUBSET s2
        ==> m1 <= m2`;;

let MEASURE_SUBSET = `!s t. measurable s /\ measurable t /\ s SUBSET t
         ==> measure s <= measure t`;;

let HAS_MEASURE_0 = `!s:real^N->bool. s has_measure &0 <=> negligible s`;;

let MEASURE_EQ_0 = `!s. negligible s ==> measure s = &0`;;

let NEGLIGIBLE_IMP_MEASURABLE = `!s:real^N->bool. negligible s ==> measurable s`;;

let HAS_MEASURE_EMPTY = `{} has_measure &0`;;

let MEASURE_EMPTY = `measure {} = &0`;;

let MEASURABLE_EMPTY = `measurable {}`;;

let MEASURABLE_SING = `!a:real^N. measurable {a}`;;

let MEASURABLE_MEASURE_EQ_0 = `!s. measurable s ==> (measure s = &0 <=> negligible s)`;;

let NEGLIGIBLE_EQ_MEASURE_0 = `!s:real^N->bool.
        negligible s <=> measurable s /\ measure s = &0`;;

let MEASURE_SING = `!a:real^N. measure {a} = &0`;;

let MEASURABLE_MEASURE_POS_LT = `!s. measurable s ==> (&0 < measure s <=> ~negligible s)`;;

let NEGLIGIBLE_INTERVAL = `(!a b. negligible(interval[a,b]) <=> interval(a,b) = {}) /\
   (!a b. negligible(interval(a,b)) <=> interval(a,b) = {})`;;

let MEASURABLE_UNIONS = `!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> measurable s)
        ==> measurable (UNIONS f)`;;

let HAS_MEASURE_DIFF_SUBSET = `!s1 s2 m1 m2. s1 has_measure m1 /\ s2 has_measure m2 /\ s2 SUBSET s1
                 ==> (s1 DIFF s2) has_measure (m1 - m2)`;;

let MEASURABLE_DIFF = `!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s DIFF t)`;;

let MEASURE_DIFF_SUBSET = `!s t. measurable s /\ measurable t /\ t SUBSET s
         ==> measure(s DIFF t) = measure s - measure t`;;

let HAS_MEASURE_UNION_NEGLIGIBLE = `!s t:real^N->bool m.
        s has_measure m /\ negligible t ==> (s UNION t) has_measure m`;;

let HAS_MEASURE_DIFF_NEGLIGIBLE = `!s t:real^N->bool m.
        s has_measure m /\ negligible t ==> (s DIFF t) has_measure m`;;

let HAS_MEASURE_UNION_NEGLIGIBLE_EQ = `!s t:real^N->bool m.
     negligible t ==> ((s UNION t) has_measure m <=> s has_measure m)`;;

let HAS_MEASURE_DIFF_NEGLIGIBLE_EQ = `!s t:real^N->bool m.
     negligible t ==> ((s DIFF t) has_measure m <=> s has_measure m)`;;

let HAS_MEASURE_ALMOST = `!s s' t m. s has_measure m /\ negligible t /\ s UNION t = s' UNION t
              ==> s' has_measure m`;;

let HAS_MEASURE_ALMOST_EQ = `!s s' t. negligible t /\ s UNION t = s' UNION t
            ==> (s has_measure m <=> s' has_measure m)`;;

let MEASURABLE_ALMOST = `!s s' t. measurable s /\ negligible t /\ s UNION t = s' UNION t
            ==> measurable s'`;;

let HAS_MEASURE_NEGLIGIBLE_UNION = `!s1 s2:real^N->bool m1 m2.
        s1 has_measure m1 /\ s2 has_measure m2 /\ negligible(s1 INTER s2)
        ==> (s1 UNION s2) has_measure (m1 + m2)`;;

let MEASURE_NEGLIGIBLE_UNION = `!s t. measurable s /\ measurable t /\ negligible(s INTER t)
         ==> measure(s UNION t) = measure s + measure t`;;

let MEASURE_NEGLIGIBLE_UNION_EQ = `!s t u.
        measurable s /\ measurable t /\ s UNION t = u /\ negligible(s INTER t)
        ==> measure s + measure t = measure u`;;

let HAS_MEASURE_NEGLIGIBLE_SYMDIFF = `!s t:real^N->bool m.
        s has_measure m /\
        negligible((s DIFF t) UNION (t DIFF s))
        ==> t has_measure m`;;

let MEASURABLE_NEGLIGIBLE_SYMDIFF = `!s t:real^N->bool.
        measurable s /\ negligible((s DIFF t) UNION (t DIFF s))
        ==> measurable t`;;

let MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ = `!s t:real^N->bool.
        negligible(s DIFF t UNION t DIFF s)
        ==> (measurable s <=> measurable t)`;;

let MEASURE_NEGLIGIBLE_SYMDIFF = `!s t:real^N->bool.
        negligible(s DIFF t UNION t DIFF s) ==> measure s = measure t`;;

let NEGLIGIBLE_SYMDIFF_EQ = `!s t:real^N->bool.
        negligible (s DIFF t UNION t DIFF s)
        ==> (negligible s <=> negligible t)`;;

let NEGLIGIBLE_DELETE = `!a:real^N. negligible(s DELETE a) <=> negligible s`;;

let HAS_MEASURE_NEGLIGIBLE_UNIONS = `!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> negligible(s INTER t))
        ==> (UNIONS f) has_measure (sum f m)`;;

let MEASURE_NEGLIGIBLE_UNIONS = `!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> negligible(s INTER t))
        ==> measure(UNIONS f) = sum f m`;;

let HAS_MEASURE_DISJOINT_UNIONS = `!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> (UNIONS f) has_measure (sum f m)`;;

let MEASURE_DISJOINT_UNIONS = `!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> measure(UNIONS f) = sum f m`;;

let HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE = `!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`;;

let MEASURE_NEGLIGIBLE_UNIONS_IMAGE = `!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`;;

let HAS_MEASURE_DISJOINT_UNIONS_IMAGE = `!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`;;

let MEASURE_DISJOINT_UNIONS_IMAGE = `!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`;;

let HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG = `!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`;;

let MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG = `!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`;;

let HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = `!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`;;

let MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = `!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`;;

let MEASURE_UNION = `!s t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s UNION t) = measure(s) + measure(t) - measure(s INTER t)`;;

let MEASURE_UNION_LE = `!s t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s UNION t) <= measure s + measure t`;;

let MEASURE_UNIONS_LE = `!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> measurable s)
        ==> measure(UNIONS f) <= sum f (\s. measure s)`;;

let MEASURABLE_INSERT = `!x s:real^N->bool. measurable(x INSERT s) <=> measurable s`;;

let MEASURABLE_DELETE = `!x s:real^N->bool. measurable(s DELETE x) <=> measurable s`;;

let MEASURE_INSERT = `!x s:real^N->bool. measure(x INSERT s) = measure s`;;

let MEASURE_DELETE = `!x s:real^N->bool. measure(s DELETE x) = measure s`;;

let MEASURE_UNIONS_LE_IMAGE = `!f:A->bool s:A->(real^N->bool).
        FINITE f /\ (!a. a IN f ==> measurable(s a))
        ==> measure(UNIONS (IMAGE s f)) <= sum f (\a. measure(s a))`;;

let MEASURE_SUB_LE_MEASURE_DIFF = `!s t:real^N->bool.
      measurable s /\ measurable t
      ==> measure s - measure t <= measure(s DIFF t)`;;

let MEASURE_SUB_LE_MEASURE_SYMDIFF = `!s t:real^N->bool.
      measurable s /\ measurable t
      ==> abs(measure s - measure t) <= measure((s DIFF t) UNION (t DIFF s))`;;

let MEASURABLE_INNER_OUTER = `!s:real^N->bool.
        measurable s <=>
                !e. &0 < e
                    ==> ?t u. t SUBSET s /\ s SUBSET u /\
                              measurable t /\ measurable u /\
                              abs(measure t - measure u) < e`;;

let HAS_MEASURE_INNER_OUTER = `!s:real^N->bool m.
        s has_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ measurable t /\
                                    m - e < measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ measurable u /\
                                    measure u < m + e)`;;

let HAS_MEASURE_INNER_OUTER_LE = `!s:real^N->bool m.
        s has_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ measurable t /\
                                    m - e <= measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ measurable u /\
                                    measure u <= m + e)`;;

let NEGLIGIBLE_OUTER = `!s:real^N->bool.
      negligible s <=>
      !e. &0 < e ==> ?t. s SUBSET t /\ measurable t /\ measure t < e`;;

let NEGLIGIBLE_OUTER_LE = `!s:real^N->bool.
      negligible s <=>
      !e. &0 < e ==> ?t. s SUBSET t /\ measurable t /\ measure t <= e`;;

let HAS_MEASURE_LIMIT = `!s. s has_measure m <=>
        !e. &0 < e
            ==> ?B. &0 < B /\
                    !a b. ball(vec 0,B) SUBSET interval[a,b]
                          ==> ?z. (s INTER interval[a,b]) has_measure z /\
                                  abs(z - m) < e`;;

let MEASURE_LIMIT = `!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?B. &0 < B /\
                !a b. ball(vec 0,B) SUBSET interval[a,b]
                      ==> abs(measure(s INTER interval[a,b]) -
                              measure s) < e`;;

let INTEGRABLE_ON_CONST = `!c:real^N. (\x:real^M. c) integrable_on s <=> c = vec 0 \/ measurable s`;;

let ABSOLUTELY_INTEGRABLE_ON_CONST = `!c. (\x. c) absolutely_integrable_on s <=> c = vec 0 \/ measurable s`;;

let HAS_INTEGRAL_CONST_GEN = `!s c. measurable s
         ==> (((\x. c):real^M->real^N) has_integral (measure s % c)) s`;;

let INTEGRAL_CONST_GEN = `!s c. measurable s
         ==> integral s ((\x. c):real^M->real^N) = measure s % c`;;

let OPEN_NOT_NEGLIGIBLE = `!s:real^N->bool. open s /\ ~(s = {}) ==> ~(negligible s)`;;

let NOT_NEGLIGIBLE_UNIV = `~negligible(:real^N)`;;

let NEGLIGIBLE_EMPTY_INTERIOR = `!s:real^N->bool. negligible s ==> interior s = {}`;;

let HAS_INTEGRAL_NEGLIGIBLE_EQ_AE = `!f:real^M->real^N s t.
        negligible t /\
        (!x i. x IN s DIFF t /\ 1 <= i /\ i <= dimindex (:N) ==> &0 <= f x$i)
        ==> ((f has_integral vec 0) s <=>
             negligible {x | x IN s /\ ~(f x = vec 0)})`;;

(* ------------------------------------------------------------------------- *)
(* Properties of measure under simple affine transformations.                *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_AFFINITY = `!s m c y. s has_measure y
             ==> (IMAGE (\x:real^N. m % x + c) s)
                 has_measure abs(m) pow (dimindex(:N)) * y`;;

let STRETCH_GALOIS = `!x:real^N y:real^N m.
        (!k. 1 <= k /\ k <= dimindex(:N) ==>  ~(m k = &0))
        ==> ((y = (lambda k. m k * x$k)) <=> (lambda k. inv(m k) * y$k) = x)`;;

let HAS_MEASURE_STRETCH = `!s m y. s has_measure y
           ==> (IMAGE (\x:real^N. lambda k. m k * x$k) s :real^N->bool)
               has_measure abs(product (1..dimindex(:N)) m) * y`;;

let HAS_MEASURE_TRANSLATION = `!s m a. s has_measure m ==> (IMAGE (\x:real^N. a + x) s) has_measure m`;;

let NEGLIGIBLE_TRANSLATION = `!s a. negligible s ==> negligible (IMAGE (\x:real^N. a + x) s)`;;

let HAS_MEASURE_TRANSLATION_EQ = `!a s m. (IMAGE (\x:real^N. a + x) s) has_measure m <=> s has_measure m`;;

add_translation_invariants [HAS_MEASURE_TRANSLATION_EQ];;

let MEASURE_TRANSLATION = `!a s. measure(IMAGE (\x:real^N. a + x) s) = measure s`;;

add_translation_invariants [MEASURE_TRANSLATION];;

let NEGLIGIBLE_TRANSLATION_REV = `!s a. negligible (IMAGE (\x:real^N. a + x) s) ==> negligible s`;;

let NEGLIGIBLE_TRANSLATION_EQ = `!a s. negligible (IMAGE (\x:real^N. a + x) s) <=> negligible s`;;

add_translation_invariants [NEGLIGIBLE_TRANSLATION_EQ];;

let MEASURABLE_TRANSLATION_EQ = `!a:real^N s. measurable (IMAGE (\x. a + x) s) <=> measurable s`;;

add_translation_invariants [MEASURABLE_TRANSLATION_EQ];;

let MEASURABLE_TRANSLATION = `!s a:real^N. measurable s ==> measurable (IMAGE (\x. a + x) s)`;;

let HAS_MEASURE_SCALING = `!s m c. s has_measure m
           ==> (IMAGE (\x:real^N. c % x) s) has_measure
               (abs(c) pow dimindex(:N)) * m`;;

let HAS_MEASURE_SCALING_EQ = `!s m c. ~(c = &0)
           ==> (IMAGE (\x:real^N. c % x) s
                  has_measure (abs(c) pow dimindex(:N)) * m <=>
                s has_measure m)`;;

let MEASURABLE_SCALING = `!s c. measurable s ==> measurable (IMAGE (\x:real^N. c % x) s)`;;

let MEASURABLE_SCALING_EQ = `!s:real^N->bool c. measurable (IMAGE (\x. c % x) s) <=>
                      c = &0 \/ measurable s`;;

let MEASURABLE_AFFINITY_EQ = `!s m c:real^N.
        measurable (IMAGE (\x. m % x + c) s) <=> m = &0 \/ measurable s`;;

let MEASURABLE_AFFINITY = `!s m c:real^N. measurable s ==> measurable (IMAGE (\x. m % x + c) s)`;;

let MEASURE_SCALING = `!s c. measurable s
         ==> measure(IMAGE (\x:real^N. c % x) s) =
             (abs(c) pow dimindex(:N)) * measure s`;;

let MEASURE_AFFINITY = `!s m c:real^N.
        measurable s
        ==> measure(IMAGE (\x. m % x + c) s) =
            abs m pow dimindex (:N) * measure s`;;

let NEGLIGIBLE_SCALING = `!s c. negligible s ==> negligible (IMAGE (\x:real^N. c % x) s)`;;

let NEGLIGIBLE_SCALING_EQ = `!s:real^N->bool c.
        negligible (IMAGE (\x. c % x) s) <=> c = &0 \/ negligible s`;;

let NEGLIGIBLE_AFFINITY_EQ = `!s m c:real^N.
        negligible (IMAGE (\x. m % x + c) s) <=>
        m = &0 \/ negligible s`;;

let NEGLIGIBLE_AFFINITY = `!s m c:real^N.
     negligible s ==> negligible (IMAGE (\x. m % x + c) s)`;;

let NOT_MEASURABLE_UNIV = `~measurable(:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of countable unions and intersections of various kinds.     *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_NESTED_UNIONS = `!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(s n) <= B) /\
        (!n. s(n) SUBSET s(SUC n))
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n)))
                  --> lift(measure(UNIONS { s(n) | n IN (:num) })))
            sequentially`;;

let MEASURABLE_NESTED_UNIONS = `!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(s n) <= B) /\
        (!n. s(n) SUBSET s(SUC n))
        ==> measurable(UNIONS { s(n) | n IN (:num) })`;;

let HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS = `!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!m n. ~(m = n) ==> negligible(s m INTER s n)) /\
        (!n. sum (0..n) (\k. measure(s k)) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n))) sums
             lift(measure(UNIONS { s(n) | n IN (:num) }))) (from 0)`;;

let NEGLIGIBLE_COUNTABLE_UNIONS_GEN = `!f. COUNTABLE f /\ (!s:real^N->bool. s IN f ==> negligible s)
       ==> negligible(UNIONS f)`;;

let HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED = `!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        (!m n. ~(m = n) ==> negligible(s m INTER s n)) /\
        bounded(UNIONS { s(n) | n IN (:num) })
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n))) sums
             lift(measure(UNIONS { s(n) | n IN (:num) }))) (from 0)`;;

let MEASURABLE_COUNTABLE_UNIONS_BOUNDED = `!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        bounded(UNIONS { s(n) | n IN (:num) })
        ==> measurable(UNIONS { s(n) | n IN (:num) })`;;

let MEASURE_COUNTABLE_UNIONS_LE_STRONG = `!d:num->(real^N->bool) B.
        (!n. measurable(d n)) /\
        (!n. measure(UNIONS {d k | k <= n}) <= B)
        ==> measurable(UNIONS {d n | n IN (:num)}) /\
            measure(UNIONS {d n | n IN (:num)}) <= B`;;

let MEASURE_COUNTABLE_UNIONS_LE = `!d:num->(real^N->bool) B.
        (!n. measurable(d n)) /\
        (!n. sum(0..n) (\k. measure(d k)) <= B)
        ==> measurable(UNIONS {d n | n IN (:num)}) /\
            measure(UNIONS {d n | n IN (:num)}) <= B`;;

let MEASURABLE_COUNTABLE_UNIONS_STRONG = `!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(UNIONS {s k | k <= n}) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) })`;;

let MEASURABLE_COUNTABLE_UNIONS = `!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. sum (0..n) (\k. measure(s k)) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) })`;;

let MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN = `!D B. COUNTABLE D /\
         (!d:real^N->bool. d IN D ==> measurable d) /\
         (!D'. D' SUBSET D /\ FINITE D' ==> measure(UNIONS D') <= B)
         ==> measurable(UNIONS D) /\ measure(UNIONS D) <= B`;;

let MEASURE_COUNTABLE_UNIONS_LE_GEN = `!D B. COUNTABLE D /\
         (!d:real^N->bool. d IN D ==> measurable d) /\
         (!D'. D' SUBSET D /\ FINITE D' ==> sum D' (\d. measure d) <= B)
         ==> measurable(UNIONS D) /\ measure(UNIONS D) <= B`;;

let MEASURABLE_COUNTABLE_INTERS = `!s:num->real^N->bool.
        (!n. measurable(s n))
        ==> measurable(INTERS { s(n) | n IN (:num) })`;;

let MEASURABLE_COUNTABLE_INTERS_GEN = `!D. COUNTABLE D /\ ~(D = {}) /\
       (!d:real^N->bool. d IN D ==> measurable d)
       ==> measurable(INTERS D)`;;

let MEASURE_COUNTABLE_UNIONS_APPROACHABLE = `!D B e.
        COUNTABLE D /\
        (!d. d IN D ==> measurable d) /\
        (!D'. D' SUBSET D /\ FINITE D' ==> measure(UNIONS D') <= B) /\
        &0 < e
        ==> ?D'. D' SUBSET D /\ FINITE D' /\
                 measure(UNIONS D) - e < measure(UNIONS D':real^N->bool)`;;

let HAS_MEASURE_NESTED_INTERS = `!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        (!n. s(SUC n) SUBSET s(n))
        ==> measurable(INTERS {s n | n IN (:num)}) /\
            ((\n. lift(measure (s n))) -->
                  lift(measure (INTERS {s n | n IN (:num)}))) sequentially`;;

let INTEGRAL_ZERO_ON_SUBINTERVALS_IMP_ZERO_AE_ALT = `!f:real^M->real^N.
        (!a b. (f has_integral (vec 0)) (interval[a,b]))
        ==> negligible{x | ~(f x = vec 0)}`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of compact and bounded open sets.                           *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_COMPACT = `!s:real^N->bool. compact s ==> measurable s`;;

let MEASURABLE_OPEN = `!s:real^N->bool. bounded s /\ open s ==> measurable s`;;

let MEASURE_OPEN_POS_LT = `!s. open s /\ bounded s /\ ~(s = {}) ==> &0 < measure s`;;

let MEASURE_OPEN_POS_LT_EQ = `!s. open s /\ bounded s ==> (&0 < measure s <=> ~(s = {}))`;;

let MEASURABLE_CLOSURE = `!s. bounded s ==> measurable(closure s)`;;

let MEASURABLE_INTERIOR = `!s. bounded s ==> measurable(interior s)`;;

let MEASURABLE_FRONTIER = `!s:real^N->bool. bounded s ==> measurable(frontier s)`;;

let MEASURE_FRONTIER = `!s:real^N->bool.
        bounded s
        ==> measure(frontier s) = measure(closure s) - measure(interior s)`;;

let MEASURE_CLOSURE = `!s:real^N->bool.
        bounded s /\ negligible(frontier s)
        ==> measure(closure s) = measure s`;;

let MEASURE_INTERIOR = `!s:real^N->bool.
        bounded s /\ negligible(frontier s)
        ==> measure(interior s) = measure s`;;

let MEASURABLE_JORDAN = `!s:real^N->bool. bounded s /\ negligible(frontier s) ==> measurable s`;;

let HAS_MEASURE_ELEMENTARY = `!d s. d division_of s ==> s has_measure (sum d content)`;;

let MEASURABLE_ELEMENTARY = `!d s. d division_of s ==> measurable s`;;

let MEASURE_ELEMENTARY = `!d s. d division_of s ==> measure s = sum d content`;;

let MEASURABLE_INTER_INTERVAL = `!s a b:real^N. measurable s ==> measurable (s INTER interval[a,b])`;;

let MEASURABLE_INSIDE = `!s:real^N->bool. compact s ==> measurable(inside s)`;;

(* ------------------------------------------------------------------------- *)
(* We can split off part of a measurable set of chosen size.                 *)
(* ------------------------------------------------------------------------- *)

let PART_MEASURES = `!s:real^N->bool m.
        measurable s /\ &0 <= m /\ m <= measure s
        ==> ?t u. DISJOINT t u /\ t UNION u = s /\
                  measurable t /\ measure t = m /\
                  measurable u /\ measure u = measure s - m`;;

let HALF_MEASURES = `!s:real^N->bool.
        measurable s
        ==> ?t u. DISJOINT t u /\ t UNION u = s /\
                  measurable t /\ measure t = measure s / &2 /\
                  measurable u /\ measure u = measure s / &2`;;

let MULTIPART_MEASURES = `!s:real^N->bool n.
        measurable s /\ ~(n = 0)
        ==> ?f. FINITE f /\ CARD f <= n /\
                pairwise DISJOINT f /\ UNIONS f = s /\
                !t. t IN f
                    ==> t SUBSET s /\ measurable t /\
                         measure t = measure s / &n`;;

(* ------------------------------------------------------------------------- *)
(* A nice lemma for negligibility proofs.                                    *)
(* ------------------------------------------------------------------------- *)

let STARLIKE_NEGLIGIBLE_BOUNDED_MEASURABLE = `!s. measurable s /\ bounded s /\
       (!c x:real^N. &0 <= c /\ x IN s /\ (c % x) IN s ==> c = &1)
       ==> negligible s`;;

let STARLIKE_NEGLIGIBLE_LEMMA = `!s. compact s /\
       (!c x:real^N. &0 <= c /\ x IN s /\ (c % x) IN s ==> c = &1)
       ==> negligible s`;;

let STARLIKE_NEGLIGIBLE = `!s a. closed s /\
         (!c x:real^N. &0 <= c /\ (a + x) IN s /\ (a + c % x) IN s ==> c = &1)
         ==> negligible s`;;

let STARLIKE_NEGLIGIBLE_STRONG = `!s a. closed s /\
         (!c x:real^N. &0 <= c /\ c < &1 /\ (a + x) IN s
                       ==> ~((a + c % x) IN s))
         ==> negligible s`;;

(* ------------------------------------------------------------------------- *)
(* In particular.                                                            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_HYPERPLANE = `!a b. ~(a = vec 0 /\ b = &0) ==> negligible {x:real^N | a dot x = b}`;;

let NEGLIGIBLE_LOWDIM = `!s:real^N->bool. dim(s) < dimindex(:N) ==> negligible s`;;

let NEGLIGIBLE_AFFINE_HULL = `!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N) ==> negligible(affine hull s)`;;

let NEGLIGIBLE_AFFINE_HULL_1 = `!a:real^1. negligible (affine hull {a})`;;

let NEGLIGIBLE_AFFINE_HULL_2 = `!a b:real^2. negligible (affine hull {a,b})`;;

let NEGLIGIBLE_AFFINE_HULL_3 = `!a b c:real^3. negligible (affine hull {a,b,c})`;;

let NEGLIGIBLE_CONVEX_HULL = `!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N) ==> negligible(convex hull s)`;;

let NEGLIGIBLE_CONVEX_HULL_1 = `!a:real^1. negligible (convex hull {a})`;;

let NEGLIGIBLE_CONVEX_HULL_2 = `!a b:real^2. negligible (convex hull {a,b})`;;

let NEGLIGIBLE_CONVEX_HULL_3 = `!a b c:real^3. negligible (convex hull {a,b,c})`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of bounded convex sets.                                     *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_CONVEX_FRONTIER = `!s:real^N->bool. convex s ==> negligible(frontier s)`;;

let MEASURABLE_CONVEX = `!s:real^N->bool. convex s /\ bounded s ==> measurable s`;;

let NEGLIGIBLE_CONVEX_INTERIOR = `!s:real^N->bool. convex s ==> (negligible s <=> interior s = {})`;;

(* ------------------------------------------------------------------------- *)
(* Various special cases.                                                    *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_SPHERE = `!a:real^N r. negligible (sphere(a,r))`;;

let MEASURABLE_BALL = `!a r. measurable(ball(a,r))`;;

let MEASURABLE_CBALL = `!a r. measurable(cball(a,r))`;;

let MEASURE_BALL_POS = `!x:real^N e. &0 < measure(ball(x,e)) <=> &0 < e`;;

let MEASURE_CBALL_POS = `!x:real^N e. &0 < measure(cball(x,e)) <=> &0 < e`;;

let HAS_INTEGRAL_OPEN_INTERVAL = `!f a b y. (f has_integral y) (interval(a,b)) <=>
             (f has_integral y) (interval[a,b])`;;

let INTEGRABLE_ON_OPEN_INTERVAL = `!f a b. f integrable_on interval(a,b) <=>
           f integrable_on interval[a,b]`;;

let INTEGRAL_OPEN_INTERVAL = `!f a b. integral(interval(a,b)) f = integral(interval[a,b]) f`;;

let ABSOLUTELY_INTEGRABLE_ON_OPEN_INTERVAL = `!f:real^M->real^N a b.
        f absolutely_integrable_on interval(a,b) <=>
        f absolutely_integrable_on interval[a,b]`;;

let MEASURABLE_SEGMENT = `(!a b:real^N. measurable(segment[a,b])) /\
   (!a b:real^N. measurable(segment(a,b)))`;;

let MEASURE_SEGMENT_1 = `(!a b:real^1. measure(segment[a,b]) = norm(b - a)) /\
   (!a b:real^1. measure(segment(a,b)) = norm(b - a))`;;

let NEGLIGIBLE_SEGMENT = `(!a b:real^N. negligible(segment[a,b]) <=> 2 <= dimindex(:N) \/ a = b) /\
   (!a b:real^N. negligible(segment(a,b)) <=> 2 <= dimindex(:N) \/ a = b)`;;

let MEASURE_BALL_SCALING = `!a:real^N c r.
      &0 <= c
      ==> measure(ball(a,c * r)) = c pow dimindex(:N) * measure(ball(a,r))`;;

let MEASURE_CBALL_SCALING = `!a:real^N c r.
      &0 <= c
      ==> measure(cball(a,c * r)) = c pow dimindex(:N) * measure(cball(a,r))`;;

(* ------------------------------------------------------------------------- *)
(* Crude upper bounds for measure of balls.                                  *)
(* ------------------------------------------------------------------------- *)

let MEASURE_CBALL_BOUND = `!x:real^N d.
        &0 <= d ==> measure(cball(x,d)) <= (&2 * d) pow (dimindex(:N))`;;

let MEASURE_BALL_BOUND = `!x:real^N d.
        &0 <= d ==> measure(ball(x,d)) <= (&2 * d) pow (dimindex(:N))`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility of image under non-injective linear map.                    *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_LINEAR_SINGULAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ ~(!x y. f(x) = f(y) ==> x = y)
        ==> negligible(IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas used in the approximation results that follow.      *)
(* Proof of the covering lemma is an obvious multidimensional generalization *)
(* of Lemma 3, p65 of Swartz's "Introduction to Gauge Integrals".            *)
(* ------------------------------------------------------------------------- *)

let COVERING_LEMMA = `!a b:real^N s g.
        s SUBSET interval[a,b] /\ ~(interval(a,b) = {}) /\ gauge g
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(interior k = {}) /\
                                (?c d. k = interval[c,d])) /\
                (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                         ==> interior k1 INTER interior k2 = {}) /\
                (!k. k IN d ==> ?x. x IN (s INTER k) /\ k SUBSET g(x)) /\
                (!u v. interval[u,v] IN d
                       ==> ?n. !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> v$i - u$i = (b$i - a$i) / &2 pow n) /\
                s SUBSET UNIONS d`;;

let COUNTABLE_ELEMENTARY_DIVISION = `!d. COUNTABLE d /\ (!k. k IN d ==> ?a b:real^N. k = interval[a,b])
       ==> ?d'. COUNTABLE d' /\
                (!k. k IN d' ==> ~(k = {}) /\ ?a b. k = interval[a,b]) /\
                (!k l. k IN d' /\ l IN d' /\ ~(k = l)
                       ==> interior k INTER interior l = {}) /\
                UNIONS d' = UNIONS d`;;

let EXPAND_CLOSED_OPEN_INTERVAL = `!a b:real^N e.
        &0 < e
        ==> ?c d. interval[a,b] SUBSET interval(c,d) /\
                  measure(interval(c,d)) <= measure(interval[a,b]) + e`;;

(* ------------------------------------------------------------------------- *)
(* Outer and inner approximation of measurable set by well-behaved sets.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_OUTER_INTERVALS_BOUNDED = `!s a b:real^N e.
        measurable s /\ s SUBSET interval[a,b] /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(k = {}) /\
                                (?c d. k = interval[c,d])) /\
                (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                         ==> interior k1 INTER interior k2 = {}) /\
                (!u v. interval[u,v] IN d
                       ==> ?n. !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> v$i - u$i = (b$i - a$i) / &2 pow n) /\
                (!k. k IN d /\ ~(interval(a,b) = {}) ==> ~(interior k = {})) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`;;

let MEASURABLE_OUTER_CLOSED_INTERVALS = `!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> ~(k = {}) /\ (?a b. k = interval[a,b])) /\
                (!k l. k IN d /\ l IN d /\ ~(k = l)
                       ==> interior k INTER interior l = {}) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`;;

let MEASURABLE_OUTER_OPEN_INTERVALS = `!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> ~(k = {}) /\ (?a b. k = interval(a,b))) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`;;

let MEASURABLE_OUTER_OPEN = `!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?t. open t /\ s SUBSET t /\
                measurable t /\ measure t < measure s + e`;;

let MEASURABLE_INNER_COMPACT = `!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?t. compact t /\ t SUBSET s /\
                measurable t /\ measure s < measure t + e`;;

let OPEN_MEASURABLE_INNER_DIVISION = `!s:real^N->bool e.
        open s /\ measurable s /\ &0 < e
        ==> ?D. D division_of UNIONS D /\
                UNIONS D SUBSET s /\
                measure s < measure(UNIONS D) + e`;;

let OUTER_MEASURE = `!s:real^N->bool.
        bounded s
        ==> ?t. s SUBSET t /\ measurable t /\
                !t'. s SUBSET t' /\ measurable t' ==> negligible(t DIFF t')`;;

(* ------------------------------------------------------------------------- *)
(* Transformation of measure by linear maps.                                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_LINEAR_IMAGE_INTERVAL = `!f a b. linear f ==> measurable(IMAGE f (interval[a,b]))`;;

let HAS_MEASURE_LINEAR_SUFFICIENT = `!f:real^N->real^N m.
        linear f /\
        (!a b. IMAGE f (interval[a,b]) has_measure
               (m * measure(interval[a,b])))
        ==> !s. measurable s ==> (IMAGE f s) has_measure (m * measure s)`;;

let INDUCT_MATRIX_ROW_OPERATIONS = `!P:real^N^N->bool.
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!A m n. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. A$i$(swap(m,n) j))) /\
        (!A m n c. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                   1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                   ==> P(lambda i. if i = m then row m A + c % row n A
                                   else row i A))
        ==> !A. P A`;;

let INDUCT_MATRIX_ELEMENTARY = `!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n c. 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. if i = m /\ j = n then c
                                   else if i = j then &1 else &0))
        ==> !A. P A`;;

let INDUCT_MATRIX_ELEMENTARY_ALT = `!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. if i = m /\ j = n \/ i = j then &1 else &0))
        ==> !A. P A`;;

let INDUCT_LINEAR_ELEMENTARY = `!P. (!f g. linear f /\ linear g /\ P f /\ P g ==> P(f o g)) /\
       (!f i. linear f /\ 1 <= i /\ i <= dimindex(:N) /\ (!x. (f x)$i = &0)
              ==> P f) /\
       (!c. P(\x. lambda i. c i * x$i)) /\
       (!m n. 1 <= m /\ m <= dimindex(:N) /\
              1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
              ==> P(\x. lambda i. x$swap(m,n) i)) /\
       (!m n. 1 <= m /\ m <= dimindex(:N) /\
              1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
              ==> P(\x. lambda i. if i = m then x$m + x$n else x$i))
       ==> !f:real^N->real^N. linear f ==> P f`;;

let LAMBDA_SWAP_GALOIS = `!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N)
        ==> (x = (lambda i. y$swap(m,n) i) <=>
             (lambda i. x$swap(m,n) i) = y)`;;

let LAMBDA_ADD_GALOIS = `!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N) /\
        ~(m = n)
        ==> (x = (lambda i. if i = m then y$m + y$n else y$i) <=>
             (lambda i. if i = m then x$m - x$n else x$i) = y)`;;

let HAS_MEASURE_SHEAR_INTERVAL = `!a b:real^N m n.
        1 <= m /\ m <= dimindex(:N) /\
        1 <= n /\ n <= dimindex(:N) /\
        ~(m = n) /\ ~(interval[a,b] = {}) /\
        &0 <= a$n
        ==> (IMAGE (\x. (lambda i. if i = m then x$m + x$n else x$i))
                   (interval[a,b]):real^N->bool)
            has_measure measure (interval [a,b])`;;

let HAS_MEASURE_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ measurable s
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * measure s)`;;

let MEASURABLE_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ measurable s ==> measurable(IMAGE f s)`;;

let MEASURE_LINEAR_IMAGE = `!f:real^N->real^N s.
        linear f /\ measurable s
        ==> measure(IMAGE f s) = abs(det(matrix f)) * measure s`;;

let HAS_MEASURE_LINEAR_IMAGE_ALT = `!f:real^N->real^N s m.
        linear f /\ s has_measure m
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * m)`;;

let HAS_MEASURE_LINEAR_IMAGE_SAME = `!f s. linear f /\ measurable s /\ abs(det(matrix f)) = &1
         ==> (IMAGE f s) has_measure (measure s)`;;

let MEASURE_LINEAR_IMAGE_SAME = `!f:real^N->real^N s.
        linear f /\ measurable s /\ abs(det(matrix f)) = &1
        ==> measure(IMAGE f s) = measure s`;;

let MEASURABLE_LINEAR_IMAGE_EQ = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (measurable (IMAGE f s) <=> measurable s)`;;

add_linear_invariants [MEASURABLE_LINEAR_IMAGE_EQ];;

let NEGLIGIBLE_LINEAR_IMAGE = `!f:real^N->real^N s. linear f /\ negligible s ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_LINEAR_IMAGE_EQ = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (negligible (IMAGE f s) <=> negligible s)`;;

add_linear_invariants [NEGLIGIBLE_LINEAR_IMAGE_EQ];;

let MEASURABLE_NEGATIONS = `!s:real^N->bool. measurable(IMAGE (--) s) <=> measurable s`;;

let HAS_MEASURE_ORTHOGONAL_IMAGE = `!f:real^N->real^N s m.
        orthogonal_transformation f /\ s has_measure m
        ==> (IMAGE f s) has_measure m`;;

let HAS_MEASURE_ORTHOGONAL_IMAGE_EQ = `!f:real^N->real^N s m.
        orthogonal_transformation f
        ==> ((IMAGE f s) has_measure m <=> s has_measure m)`;;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] HAS_MEASURE_ORTHOGONAL_IMAGE_EQ];;

let MEASURE_ORTHOGONAL_IMAGE_EQ = `!f:real^N->real^N s.
        orthogonal_transformation f
        ==> measure(IMAGE f s) = measure s`;;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] MEASURE_ORTHOGONAL_IMAGE_EQ];;

let MEASURE_NEGATIONS = `!s:real^N->bool. measure(IMAGE (--) s) = measure s`;;

let HAS_MEASURE_ISOMETRY = `!f:real^M->real^N s m.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x. norm(f x) = norm x)
        ==> (IMAGE f s has_measure m <=> s has_measure m)`;;

let MEASURABLE_LINEAR_IMAGE_EQ_GEN = `!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> (measurable(IMAGE f s) <=> measurable s)`;;

let MEASURE_ISOMETRY = `!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x. norm(f x) = norm x)
        ==> measure (IMAGE f s) = measure s`;;

let MEASURABLE_CONVEX_EQ = `!s:real^N->bool.
        convex s ==> (measurable s <=> bounded s \/ interior s = {})`;;

(* ------------------------------------------------------------------------- *)
(* Measure of a standard simplex.                                            *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_IMAGE_STD_SIMPLEX = `!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))} =
           IMAGE (\x:real^N. lambda i. sum(1..inverse p(i)) (\j. x$j))
                 {x | (!i. 1 <= i /\ i <= dimindex (:N) ==> &0 <= x$i) /\
                      sum (1..dimindex (:N)) (\i. x$i) <= &1}`;;

let HAS_MEASURE_IMAGE_STD_SIMPLEX = `!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))}
           has_measure
           (measure (convex hull
             (vec 0 INSERT {basis i:real^N | 1 <= i /\ i <= dimindex(:N)})))`;;

let HAS_MEASURE_STD_SIMPLEX = `(convex hull (vec 0:real^N INSERT {basis i | 1 <= i /\ i <= dimindex(:N)}))
   has_measure inv(&(FACT(dimindex(:N))))`;;

(* ------------------------------------------------------------------------- *)
(* Hence the measure of a general simplex.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_SIMPLEX_0 = `!l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (vec 0 INSERT set_of_list l)) has_measure
            abs(det(vector l)) / &(FACT(dimindex(:N)))`;;

let HAS_MEASURE_SIMPLEX = `!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (set_of_list(CONS a l))) has_measure
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`;;

let MEASURABLE_CONVEX_HULL = `!s. bounded s ==> measurable(convex hull s)`;;

let MEASURABLE_SIMPLEX = `!l. measurable(convex hull (set_of_list l))`;;

let MEASURE_SIMPLEX = `!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> measure(convex hull (set_of_list(CONS a l))) =
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`;;

(* ------------------------------------------------------------------------- *)
(* Area of a triangle.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TRIANGLE = `!a b c:real^2.
        convex hull {a,b,c} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`;;

let MEASURABLE_TRIANGLE = `!a b c:real^N. measurable(convex hull {a,b,c})`;;

let MEASURE_TRIANGLE = `!a b c:real^2.
        measure(convex hull {a,b,c}) =
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`;;

(* ------------------------------------------------------------------------- *)
(* Volume of a tetrahedron.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TETRAHEDRON = `!a b c d:real^3.
        convex hull {a,b,c,d} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) /
           &6`;;

let MEASURABLE_TETRAHEDRON = `!a b c d:real^N. measurable(convex hull {a,b,c,d})`;;

let MEASURE_TETRAHEDRON = `!a b c d:real^3.
        measure(convex hull {a,b,c,d}) =
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) / &6`;;

(* ------------------------------------------------------------------------- *)
(* Measure is continuous with Hausdorff distance: several formulations.      *)
(* ------------------------------------------------------------------------- *)

let MEASURE_CONTINUOUS_WITH_HAUSDIST = `!s:real^N->bool e.
        bounded s /\ convex s /\ ~(s = {}) /\ &0 < e
        ==> ?d. &0 < d /\
                !t. bounded t /\ convex t /\ ~(t = {}) /\ hausdist(s,t) < d
                    ==> abs(measure(t) - measure(s)) < e`;;

let MEASURE_CONTINUOUS_WITH_HAUSDIST_EXPLICIT = `!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?d. &0 < d /\
                !t. convex t /\
                    (!y. y IN s ==> ?x. x IN t /\ dist(x,y) < d) /\
                    (!y. y IN t ==> ?x. x IN s /\ dist(x,y) < d)
                    ==> abs(measure(t) - measure(s)) < e`;;

let MEASURE_SEMICONTINUOUS_WITH_HAUSDIST_EXPLICIT = `!s:real^N->bool e.
        bounded s /\ negligible(frontier s) /\ &0 < e
        ==> ?d. &0 < d /\
                !s'. measurable s' /\
                     (!y. y IN s' ==> ?x. x IN s /\ dist(x,y) < d)
                     ==> measure(s') < measure(s) + e`;;

let MEASURE_SEMICONTINUOUS_WITH_HAUSDIST_BOUND = `!s s' r e a:real^N.
        bounded s /\ convex s /\ ball(a,r) SUBSET s /\ &0 < r /\
        bounded s' /\ measurable s' /\ hausdist(s,s') <= e * r /\ &0 < e
        ==> measure(s') <= measure(s) * (&1 + e) pow dimindex(:N)`;;

(* ------------------------------------------------------------------------- *)
(* Steinhaus's theorem. (Stromberg's proof as given on Wikipedia.)           *)
(* ------------------------------------------------------------------------- *)

let STEINHAUS = `!s:real^N->bool.
        measurable s /\ &0 < measure s
        ==> ?d. &0 < d /\ ball(vec 0,d) SUBSET {x - y | x IN s /\ y IN s}`;;

(* ------------------------------------------------------------------------- *)
(* A measurable set with cardinality less than c is negligible.              *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_NONNEGLIGIBLE_IMP_LARGE = `!s:real^N->bool. measurable s /\ &0 < measure s ==> s =_c (:real)`;;

let MEASURABLE_SMALL_IMP_NEGLIGIBLE = `!s:real^N->bool. measurable s /\ s <_c (:real) ==> negligible s`;;

(* ------------------------------------------------------------------------- *)
(* Austin's Lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let AUSTIN_LEMMA = `!D. FINITE D /\
       (!d. d IN D
            ==> ?k a b. d = interval[a:real^N,b] /\
                        (!i. 1 <= i /\ i <= dimindex(:N) ==> b$i - a$i = k))
       ==> ?D'. D' SUBSET D /\ pairwise DISJOINT D' /\
                measure(UNIONS D') >=
                measure(UNIONS D) / &3 pow (dimindex(:N))`;;

(* ------------------------------------------------------------------------- *)
(* Some differentiability-like properties of the indefinite integral.        *)
(* The first two proofs are minor variants of each other, but it was more    *)
(* work to derive one from the other.                                        *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_CCONTINUOUS_EXPLICIT = `!f:real^M->real^N.
    (!a b. f integrable_on interval[a,b])
    ==> ?k. negligible k /\
         !x e. ~(x IN k) /\ &0 < e
               ==> ?d. &0 < d /\
                       !h. &0 < h /\ h < d
                           ==> norm(inv(content(interval[x,x + h % vec 1])) %
                                    integral (interval[x,x + h % vec 1]) f -
                                    f(x)) < e`;;

let INTEGRABLE_CCONTINUOUS_EXPLICIT_SYMMETRIC = `!f:real^M->real^N.
    (!a b. f integrable_on interval[a,b])
    ==> ?k. negligible k /\
         !x e. ~(x IN k) /\ &0 < e
               ==> ?d. &0 < d /\
                       !h. &0 < h /\ h < d
                ==> norm(inv(content(interval[x - h % vec 1,x + h % vec 1])) %
                    integral (interval[x - h % vec 1,x + h % vec 1]) f -
                    f(x)) < e`;;

let HAS_VECTOR_DERIVATIVE_INDEFINITE_INTEGRAL = `!f:real^1->real^N a b.
        f integrable_on interval[a,b]
        ==> ?k. negligible k /\
                !x. x IN interval[a,b] DIFF k
                    ==> ((\x. integral(interval[a,x]) f) has_vector_derivative
                         f(x)) (at x within interval[a,b])`;;

let ABSOLUTELY_INTEGRABLE_LEBESGUE_POINTS = `!f:real^M->real^N.
    (!a b. f absolutely_integrable_on interval[a,b])
    ==> ?k. negligible k /\
            !x e. ~(x IN k) /\ &0 < e
                  ==> ?d. &0 < d /\
                          !h. &0 < h /\ h < d
                             ==> norm(inv(content(interval[x - h % vec 1,
                                                           x + h % vec 1])) %
                                      integral (interval[x - h % vec 1,
                                                         x + h % vec 1])
                                               (\t. lift(norm(f t - f x))))
                                 < e`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of a function on a set (not necessarily itself measurable). *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("measurable_on",(12,"right"));;

let measurable_on = new_definition
 `(f:real^M->real^N) measurable_on s <=>
        ?k g. negligible k /\
              (!n. (g n) continuous_on (:real^M)) /\
              (!x. ~(x IN k)
                   ==> ((\n. g n x) --> if x IN s then f(x) else vec 0)
                       sequentially)`;;

let MEASURABLE_ON_UNIV = `(\x.  if x IN s then f(x) else vec 0) measurable_on (:real^M) <=>
   f measurable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Lebesgue measurability (like "measurable" but allowing infinite measure)  *)
(* ------------------------------------------------------------------------- *)

let lebesgue_measurable = new_definition
 `lebesgue_measurable s <=> (indicator s) measurable_on (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Relation between measurability and integrability.                         *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE = `!f:real^M->real^N g s.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> f integrable_on s`;;

let MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE = `!f:real^M->real^N g s k.
        f measurable_on s /\ g integrable_on s /\ negligible k /\
        (!x. x IN s DIFF k ==> norm(f x) <= drop(g x))
        ==> f integrable_on s`;;

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE = `!f:real^M->real^N g s.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> f absolutely_integrable_on s`;;

let INTEGRAL_DROP_LE_MEASURABLE = `!f g s:real^N->bool.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> &0 <= drop(f x) /\ drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`;;

let INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE = `!f:real^M->real^N.
        (!a b. f integrable_on interval[a,b]) ==> f measurable_on (:real^M)`;;

let INTEGRABLE_IMP_MEASURABLE = `!f:real^M->real^N s.
        f integrable_on s ==> f measurable_on s`;;

let ABSOLUTELY_INTEGRABLE_MEASURABLE = `!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
        f measurable_on s /\ (\x. lift(norm(f x))) integrable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Composing continuous and measurable functions; a few variants.            *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_COMPOSE_CONTINUOUS = `!f:real^M->real^N g:real^N->real^P.
        f measurable_on (:real^M) /\ g continuous_on (:real^N)
        ==> (g o f) measurable_on (:real^M)`;;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_0 = `!f:real^M->real^N g:real^N->real^P s.
        f measurable_on s /\ g continuous_on (:real^N) /\ g(vec 0) = vec 0
        ==> (g o f) measurable_on s`;;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_OPEN_INTERVAL = `!f:real^M->real^N g:real^N->real^P a b.
        f measurable_on (:real^M) /\
        (!x. f(x) IN interval(a,b)) /\
        g continuous_on interval(a,b)
        ==> (g o f) measurable_on (:real^M)`;;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET = `!f:real^M->real^N g:real^N->real^P s.
        closed s /\
        f measurable_on (:real^M) /\
        (!x. f(x) IN s) /\
        g continuous_on s
        ==> (g o f) measurable_on (:real^M)`;;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET_0 = `!f:real^M->real^N g:real^N->real^P s t.
        closed s /\
        f measurable_on t /\
        (!x. f(x) IN s) /\
        g continuous_on s /\
        vec 0 IN s /\ g(vec 0) = vec 0
        ==> (g o f) measurable_on t`;;

(* ------------------------------------------------------------------------- *)
(* Basic closure properties of measurable functions.                         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_MEASURABLE_ON = `!f:real^M->real^N. f continuous_on (:real^M) ==> f measurable_on (:real^M)`;;

let MEASURABLE_ON_CONST = `!k:real^N. (\x. k) measurable_on (:real^M)`;;

let MEASURABLE_ON_0 = `!s. (\x. vec 0) measurable_on s`;;

let MEASURABLE_ON_CMUL = `!c f:real^M->real^N s.
        f measurable_on s ==> (\x. c % f x) measurable_on s`;;

let MEASURABLE_ON_CMUL_EQ = `!f:real^M->real^N s c.
        (\x. c % f x) measurable_on s <=> c = &0 \/ f measurable_on s`;;

let MEASURABLE_ON_NEG = `!f:real^M->real^N s.
     f measurable_on s ==> (\x. --(f x)) measurable_on s`;;

let MEASURABLE_ON_NEG_EQ = `!f:real^M->real^N s. (\x. --(f x)) measurable_on s <=> f measurable_on s`;;

let MEASURABLE_ON_NORM = `!f:real^M->real^N s.
        f measurable_on s ==> (\x. lift(norm(f x))) measurable_on s`;;

let MEASURABLE_ON_LIFT_ABS = `!f:real^N->real s.
        (\x. lift(f x)) measurable_on s
        ==> (\x. lift(abs(f x))) measurable_on s`;;

let MEASURABLE_ON_PASTECART = `!f:real^M->real^N g:real^M->real^P s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. pastecart (f x) (g x)) measurable_on s`;;

let MEASURABLE_ON_COMBINE = `!h:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P s.
        f measurable_on s /\ g measurable_on s /\
        (\x. h (fstcart x) (sndcart x)) continuous_on UNIV /\
        h (vec 0) (vec 0) = vec 0
        ==> (\x. h (f x) (g x)) measurable_on s`;;

let MEASURABLE_ON_ADD = `!f:real^M->real^N g:real^M->real^N s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. f x + g x) measurable_on s`;;

let MEASURABLE_ON_SUB = `!f:real^M->real^N g:real^M->real^N s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. f x - g x) measurable_on s`;;

let MEASURABLE_ON_MAX = `!f:real^M->real^N g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. (lambda i. max ((f x)$i) ((g x)$i)):real^N)
          measurable_on s`;;

let MEASURABLE_ON_MIN = `!f:real^M->real^N g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. (lambda i. min ((f x)$i) ((g x)$i)):real^N)
          measurable_on s`;;

let MEASURABLE_ON_DROP_MUL = `!f g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. drop(f x) % g x) measurable_on s`;;

let MEASURABLE_ON_LIFT_MUL = `!f g s. (\x. lift(f x)) measurable_on s /\
           (\x. lift(g x)) measurable_on s
           ==> (\x. lift(f x * g x)) measurable_on s`;;

let MEASURABLE_ON_MUL = `!f g s. (\x. lift(f x)) measurable_on s /\ g measurable_on s
           ==> (\x. f x % g x) measurable_on s`;;

let MEASURABLE_ON_VSUM = `!f:A->real^M->real^N s t.
        FINITE t /\ (!i. i IN t ==> (f i) measurable_on s)
        ==> (\x. vsum t (\i. f i x)) measurable_on s`;;

let MEASURABLE_ON_COMPONENTWISE = `!f:real^M->real^N s.
        f measurable_on s <=>
        (!i. 1 <= i /\ i <= dimindex (:N)
             ==> (\x. lift (f x$i)) measurable_on s)`;;

let MEASURABLE_ON_CONST_EQ = `!s:real^M->bool c:real^N.
        (\x. c) measurable_on s <=> c = vec 0 \/ lebesgue_measurable s`;;

let MEASURABLE_ON_LIFT_POW = `!f:real^M->real s n.
        (\x. lift(f x)) measurable_on s /\ (n = 0 ==> lebesgue_measurable s)
        ==> (\x. lift(f x pow n)) measurable_on s`;;

let MEASURABLE_ON_LIFT_PRODUCT = `!f:A->real^N->real s t.
         FINITE t /\ (t = {} ==> lebesgue_measurable s) /\
         (!i. i IN t ==> (\x. lift(f i x)) measurable_on s)
         ==> (\x. lift(product t (\i. f i x))) measurable_on s`;;

let MEASURABLE_ON_SPIKE = `!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> f measurable_on t ==> g measurable_on t`;;

let MEASURABLE_ON_SPIKE_SET = `!f:real^M->real^N s t.
        negligible (s DIFF t UNION t DIFF s)
        ==> f measurable_on s
            ==> f measurable_on t`;;

let MEASURABLE_ON_SPIKE_SET_EQ = `!f:real^M->real^N s t.
        negligible (s DIFF t UNION t DIFF s)
        ==> (f measurable_on s <=> f measurable_on t)`;;

let MEASURABLE_ON_EQ = `!f g:real^M->real^N s.
        (!x. x IN s ==> f x = g x) /\ f measurable_on s
        ==> g measurable_on s`;;

let MEASURABLE_ON_RESTRICT = `!f:real^M->real^N s.
        f measurable_on (:real^M) /\ lebesgue_measurable s
        ==> (\x. if x IN s then f(x) else vec 0) measurable_on (:real^M)`;;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = `!f s t. s SUBSET t /\ f measurable_on t /\
           lebesgue_measurable s
           ==> f measurable_on s`;;

let MEASURABLE_ON_OPEN_INTERVAL = `!f:real^M->real^N a b.
        f measurable_on interval(a,b) <=> f measurable_on interval[a,b]`;;

let MEASURABLE_ON_CASES = `!P f g:real^M->real^N s.
        lebesgue_measurable {x | P x} /\
        f measurable_on s /\ g measurable_on s
        ==> (\x. if P x then f x else g x) measurable_on s`;;

let MEASURABLE_ON_LIMIT = `!f:num->real^M->real^N g s k.
        (!n. (f n) measurable_on s) /\
        negligible k /\
        (!x. x IN s DIFF k ==> ((\n. f n x) --> g x) sequentially)
        ==> g measurable_on s`;;

let MEASURABLE_ON_BILINEAR = `!op:real^N->real^P->real^Q f g s:real^M->bool.
        bilinear op /\ f measurable_on s /\ g measurable_on s
        ==> (\x. op (f x) (g x)) measurable_on s`;;

let ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT = `!op:real^N->real^P->real^Q f g s:real^M->bool.
        bilinear op /\
        f measurable_on s /\ bounded (IMAGE f s) /\
        g absolutely_integrable_on s
        ==> (\x. op (f x) (g x)) absolutely_integrable_on s`;;

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE = `!f:real^M->real^N g s t.
        f measurable_on s /\  g integrable_on s /\ negligible t /\
        (!x. x IN s DIFF t ==> norm(f x) <= drop(g x))
        ==> f absolutely_integrable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Some handy lemmas about square integrable functions. These exist in       *)
(* far more generality in "Multivariate/lpspaces.ml"                         *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_SQUARE_INTEGRABLE_PRODUCT = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P s.
        bilinear bop /\
        f measurable_on s /\ (\x. lift(norm(f x) pow 2)) integrable_on s /\
        g measurable_on s /\ (\x. lift(norm(g x) pow 2)) integrable_on s
        ==> (\x. bop (f x) (g x)) absolutely_integrable_on s`;;

let SQUARE_INTEGRAL_SQUARE_INTEGRABLE_PRODUCT_LE = `!f:real^M->real^N g:real^M->real^P s.
        f measurable_on s /\ (\x. lift(norm(f x) pow 2)) integrable_on s /\
        g measurable_on s /\ (\x. lift(norm(g x) pow 2)) integrable_on s
        ==> drop(integral s (\x. lift(norm(f x) * norm(g x)))) pow 2 <=
            drop(integral s (\x. lift(norm(f x) pow 2))) *
            drop(integral s (\x. lift(norm(g x) pow 2)))`;;

(* ------------------------------------------------------------------------- *)
(* Natural closure properties of measurable functions; the intersection      *)
(* one is actually quite tedious since we end up reinventing cube roots      *)
(* before they actually get introduced in transcendentals.ml                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_EMPTY = `!f:real^M->real^N. f measurable_on {}`;;

let MEASURABLE_ON_INTER = `!f:real^M->real^N s t.
        f measurable_on s /\ f measurable_on t
        ==> f measurable_on (s INTER t)`;;

let MEASURABLE_ON_DIFF = `!f:real^M->real^N s t.
    f measurable_on s /\ f measurable_on t ==> f measurable_on (s DIFF t)`;;

let MEASURABLE_ON_UNION = `!f:real^M->real^N s t.
    f measurable_on s /\ f measurable_on t ==> f measurable_on (s UNION t)`;;

let MEASURABLE_ON_UNIONS = `!f:real^M->real^N k.
        FINITE k /\ (!s. s IN k ==> f measurable_on s)
        ==> f measurable_on (UNIONS k)`;;

let MEASURABLE_ON_COUNTABLE_UNIONS = `!f:real^M->real^N k.
        COUNTABLE k /\ (!s. s IN k ==> f measurable_on s)
        ==> f measurable_on (UNIONS k)`;;

(* ------------------------------------------------------------------------- *)
(* An existence theorem for "improper" integrals. Hake's theorem implies     *)
(* that if the integrals over subintervals have a limit then the integral    *)
(* exists. This is incomparable: we only need a priori to assume that        *)
(* the integrals are bounded, and we get absolute integrability, but we      *)
(* also need a (rather weak) bound assumption on the function.               *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_IMPROPER_SIMPLE = `!(f:real^M->real^N) a b.
        (!c d. interval[c,d] SUBSET interval(a,b)
               ==> f absolutely_integrable_on interval[c,d]) /\
        bounded { integral (interval[c,d]) (\x. lift(norm(f x))) |
                  interval[c,d] SUBSET interval(a,b)}
        ==> f absolutely_integrable_on interval[a,b]`;;

let ABSOLUTELY_INTEGRABLE_IMPROPER = `!f:real^M->real^N a b.
     (!c d. interval[c,d] SUBSET interval(a,b)
            ==> f integrable_on interval[c,d]) /\
     bounded { integral (interval[c,d]) f |
               interval[c,d] SUBSET interval(a,b)} /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> ?g. g absolutely_integrable_on interval[a,b] /\
                  ((!x. x IN interval[a,b] ==> (f x)$i <= drop(g x)) \/
                   (!x. x IN interval[a,b] ==> (f x)$i >= drop(g x))))
   ==> f absolutely_integrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility of a Lipschitz image of a negligible set.                   *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE = `!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ negligible s /\
        (!x. x IN s
             ==> ?t b. open t /\ x IN t /\
                       !y. y IN s INTER t
                           ==> norm(f y - f x) <= b * norm(y - x))
        ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE_LOWDIM = `!f:real^M->real^N s.
        dimindex(:M) < dimindex(:N) /\
        (!x. x IN s
             ==> ?t b. open t /\ x IN t /\
                       !y. y IN s INTER t
                           ==> norm(f y - f x) <= b * norm(y - x))
        ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_LIPSCHITZ_IMAGE_UNIV = `!f:real^N->real^N s B.
        negligible s /\ (!x y. norm(f x - f y) <= B * norm(x - y))
        ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE = `!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ negligible s /\ f differentiable_on s
        ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM = `!f:real^M->real^N s.
        dimindex(:M) < dimindex(:N) /\ f differentiable_on s
        ==> negligible(IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* Simplest case of Sard's theorem (we don't need continuity of derivative). *)
(* ------------------------------------------------------------------------- *)

let BABY_SARD = `!f:real^M->real^N f' s.
        dimindex(:M) <= dimindex(:N) /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within s) /\
                 rank(matrix(f' x)) < dimindex(:N))
        ==> negligible(IMAGE f s)`;;

let BABY_SARD_ALT = `!f:real^M->real^N s.
         dimindex(:M) <= dimindex(:N) /\
         (!x. x IN s
              ==> ?f'. (f has_derivative f') (at x within s) /\
                       rank(matrix f') < dimindex (:N))
         ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_INFINITE_PREIMAGES_MOSTLY_DIFFERENTIABLE_GEN = `!f:real^N->real^N s.
       (!y. compact {x | x IN s /\ f x = y}) /\
       negligible (IMAGE f {x | x IN s /\ ~(f differentiable (at x within s))})
       ==> negligible {y | INFINITE {x | x IN s /\ f x = y}}`;;

let NEGLIGIBLE_INFINITE_PREIMAGES_MOSTLY_DIFFERENTIABLE = `!f:real^N->real^N s.
       f continuous_on s /\ compact s /\
       negligible (IMAGE f {x | x IN s /\ ~(f differentiable (at x within s))})
       ==> negligible {y | INFINITE {x | x IN s /\ f x = y}}`;;

let NEGLIGIBLE_INFINITE_PREIMAGES_DIFFERENTIABLE = `!f:real^N->real^N s.
        compact s /\ f differentiable_on s
        ==> negligible {y | INFINITE {x | x IN s /\ f(x) = y}}`;;

(* ------------------------------------------------------------------------- *)
(* Also negligibility of BV low-dimensional image.                           *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_IMAGE_BOUNDED_VARIATION_INTERVAL = `!f:real^1->real^N s.
        2 <= dimindex(:N) /\ f has_bounded_variation_on s /\ is_interval s
        ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE_LOWDIM = `!f:real^1->real^N s.
        2 <= dimindex(:N) /\ f absolutely_continuous_on s /\ is_interval s
        ==> negligible(IMAGE f s)`;;

let NEGLIGIBLE_RECTIFIABLE_PATH_IMAGE = `!g:real^1->real^N.
        2 <= dimindex(:N) /\ rectifiable_path g ==> negligible(path_image g)`;;

let INTERIOR_RECTIFIABLE_PATH_IMAGE = `!g:real^1->real^N.
        2 <= dimindex(:N) /\ rectifiable_path g
        ==> interior(path_image g) = {}`;;

(* ------------------------------------------------------------------------- *)
(* Properties of Lebesgue measurable sets.                                   *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_INDICATOR = `!s t. indicator t measurable_on s <=> lebesgue_measurable(s INTER t)`;;

let MEASURABLE_ON_INDICATOR_SUBSET = `!s t:real^N->bool.
        t SUBSET s
        ==> (indicator t measurable_on s <=> lebesgue_measurable t)`;;

let MEASURABLE_IMP_LEBESGUE_MEASURABLE = `!s:real^N->bool. measurable s ==> lebesgue_measurable s`;;

let NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE = `!s:real^N->bool. negligible s ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_EMPTY = `lebesgue_measurable {}`;;

let LEBESGUE_MEASURABLE_UNIV = `lebesgue_measurable (:real^N)`;;

let LEBESGUE_MEASURABLE_COMPACT = `!s:real^N->bool. compact s ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_BALL = `!a:real^N r. lebesgue_measurable(ball(a,r))`;;

let LEBESGUE_MEASURABLE_CBALL = `!a:real^N r. lebesgue_measurable(cball(a,r))`;;

let LEBESGUE_MEASURABLE_INTERVAL = `(!a b:real^N. lebesgue_measurable(interval[a,b])) /\
   (!a b:real^N. lebesgue_measurable(interval(a,b)))`;;

let LEBESGUE_MEASURABLE_INTER = `!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s INTER t)`;;

let LEBESGUE_MEASURABLE_UNION = `!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s UNION t)`;;

let LEBESGUE_MEASURABLE_DIFF = `!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s DIFF t)`;;

let LEBESGUE_MEASURABLE_COMPL = `!s. lebesgue_measurable((:real^N) DIFF s) <=> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_ON_SUBINTERVALS = `!s. lebesgue_measurable s <=>
       !a b:real^N. lebesgue_measurable(s INTER interval[a,b])`;;

let LEBESGUE_MEASURABLE_CLOSED = `!s:real^N->bool. closed s ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_OPEN = `!s:real^N->bool. open s ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_OPEN_IN = `!s t:real^N->bool.
        open_in (subtopology euclidean s) t /\ lebesgue_measurable s
        ==> lebesgue_measurable t`;;

let LEBESGUE_MEASURABLE_CLOSED_IN = `!s t:real^N->bool.
        closed_in (subtopology euclidean s) t /\ lebesgue_measurable s
        ==> lebesgue_measurable t`;;

let LEBESGUE_MEASURABLE_UNIONS = `!f. FINITE f /\ (!s. s IN f ==> lebesgue_measurable s)
       ==> lebesgue_measurable (UNIONS f)`;;

let LEBESGUE_MEASURABLE_COUNTABLE_UNIONS = `!f:(real^N->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (UNIONS f)`;;

let LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT = `!s:num->real^N->bool.
        (!n. lebesgue_measurable(s n))
        ==> lebesgue_measurable(UNIONS {s n | n IN (:num)})`;;

let LEBESGUE_MEASURABLE_COUNTABLE_INTERS = `!f:(real^N->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (INTERS f)`;;

let LEBESGUE_MEASURABLE_COUNTABLE_INTERS_EXPLICIT = `!s:num->real^N->bool.
        (!n. lebesgue_measurable(s n))
        ==> lebesgue_measurable(INTERS {s n | n IN (:num)})`;;

let LEBESGUE_MEASURABLE_INTERS = `!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (INTERS f)`;;

let GDELTA_IMP_LEBESGUE_MEASURABLE = `!s:real^N->bool. gdelta s ==> lebesgue_measurable s`;;

let FSIGMA_IMP_LEBESGUE_MEASURABLE = `!s:real^N->bool. fsigma s ==> lebesgue_measurable s`;;

let BOREL_IMP_LEBESGUE_MEASURABLE = `!s:real^N->bool. borel s ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_IFF_MEASURABLE = `!s:real^N->bool. bounded s ==> (lebesgue_measurable s <=> measurable s)`;;

let LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS = `!s:real^N->bool.
        lebesgue_measurable s <=>
        (!a b. measurable(s INTER interval[a,b]))`;;

let LEBESGUE_MEASURABLE_MEASURABLE_ON_COUNTABLE_SUBINTERVALS = `!s:real^N->bool.
        lebesgue_measurable s <=>
        (!n. measurable(s INTER interval[--vec n,vec n]))`;;

let MEASURABLE_ON_MEASURABLE_SUBSET = `!f s t. s SUBSET t /\ f measurable_on t /\ measurable s
           ==> f measurable_on s`;;

let LEBESGUE_MEASURABLE_JORDAN = `!s:real^N->bool. negligible(frontier s) ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_CONVEX = `!s:real^N->bool. convex s ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_NEGLIGIBLE_SYMDIFF = `!s t:real^N->bool.
        lebesgue_measurable s /\ negligible((s DIFF t) UNION (t DIFF s))
        ==> lebesgue_measurable t`;;

let LEBESGUE_MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ = `!s t:real^N->bool.
        negligible(s DIFF t UNION t DIFF s)
        ==> (lebesgue_measurable s <=> lebesgue_measurable t)`;;

let LEBESGUE_MEASURABLE_INSERT = `!s a:real^N. lebesgue_measurable(a INSERT s) <=> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_DELETE = `!s a:real^N. lebesgue_measurable(s DELETE a) <=> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_SING = `!a:real^N. lebesgue_measurable {a}`;;

let ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_INTER = `!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ lebesgue_measurable t
        ==> f absolutely_integrable_on (s INTER t)`;;

let ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET = `!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ t SUBSET s /\ lebesgue_measurable t
        ==> f absolutely_integrable_on t`;;

(* ------------------------------------------------------------------------- *)
(* Invariance theorems for Lebesgue measurability.                           *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_TRANSLATION = `!f:real^M->real^N s a.
          f measurable_on (IMAGE (\x. a + x) s)
          ==> (\x. f(a + x)) measurable_on s`;;

let MEASURABLE_ON_TRANSLATION_EQ = `!f:real^M->real^N s a.
        (\x. f(a + x)) measurable_on s <=>
        f measurable_on (IMAGE (\x. a + x) s)`;;

let NEGLIGIBLE_LINEAR_IMAGE_GEN = `!f:real^M->real^N s.
        linear f /\ negligible s /\ dimindex(:M) <= dimindex(:N)
        ==> negligible (IMAGE f s)`;;

let MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN = `!f:real^M->real^N h:real^N->real^P s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((h o f) measurable_on s <=> h measurable_on (IMAGE f s))`;;

let MEASURABLE_ON_LINEAR_IMAGE_EQ = `!f:real^N->real^N h:real^N->real^P s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((h o f) measurable_on s <=> h measurable_on (IMAGE f s))`;;

let LEBESGUE_MEASURABLE_TRANSLATION = `!a:real^N s.
     lebesgue_measurable (IMAGE (\x. a + x) s) <=>
     lebesgue_measurable s`;;

add_translation_invariants [LEBESGUE_MEASURABLE_TRANSLATION];;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ = `!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
         ==> (lebesgue_measurable (IMAGE f s) <=>
              lebesgue_measurable s)`;;

add_linear_invariants [LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ];;

let MEASURABLE_ON_REFLECT = `!f:real^M->real^N s.
        (\x. f(--x)) measurable_on s <=> f measurable_on (IMAGE (--) s)`;;

(* ------------------------------------------------------------------------- *)
(* Various common equivalent forms of function measurability.                *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k < a})`
and MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        ?g. (!n. (g n) measurable_on (:real^M)) /\
            (!n. FINITE(IMAGE (g n) (:real^M))) /\
            (!x. ((\n. g n x) --> f x) sequentially))`;;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k >= a}`;;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k > a}`;;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k <= a}`;;

let MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a b. lebesgue_measurable {x | f(x) IN interval(a,b)})`
and MEASURABLE_ON_PREIMAGE_OPEN = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. open t ==> lebesgue_measurable {x | f(x) IN t})`;;

let MEASURABLE_ON_PREIMAGE_CLOSED = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. closed t ==> lebesgue_measurable {x | f(x) IN t}`;;

let MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL = `!f:real^M->real^N.
         f measurable_on (:real^M) <=>
         !a b. lebesgue_measurable {x | f(x) IN interval[a,b]}`;;

let MEASURABLE_ON_PREIMAGE_BOREL = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. borel t ==> lebesgue_measurable {x | f x IN t}`;;

let LEBESGUE_MEASURABLE_PREIMAGE_OPEN = `!f:real^M->real^N t.
        f measurable_on (:real^M) /\ open t
        ==> lebesgue_measurable {x | f(x) IN t}`;;

let LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = `!f:real^M->real^N t.
        f measurable_on (:real^M) /\ closed t
        ==> lebesgue_measurable {x | f(x) IN t}`;;

let LEBESGUE_MEASURABLE_PREIMAGE_BOREL = `!f:real^M->real^N t.
        f measurable_on (:real^M) /\ borel t
        ==> lebesgue_measurable {x | f(x) IN t}`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LE = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k <= (a:real^N)$k}`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GE = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k >= (a:real^N)$k}`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LT = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k < (a:real^N)$k}`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GT = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k > (a:real^N)$k}`;;

let MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT_INCREASING = `!f:real^N->real^1.
        f measurable_on (:real^N) /\ (!x. &0 <= drop(f x)) <=>
        ?g. (!n x. &0 <= drop(g n x) /\ drop(g n x) <= drop(f x)) /\
            (!n x. drop(g n x) <= drop(g(SUC n) x)) /\
            (!n. (g n) measurable_on (:real^N)) /\
            (!n. FINITE(IMAGE (g n) (:real^N))) /\
            (!x. ((\n. g n x) --> f x) sequentially)`;;

(* ------------------------------------------------------------------------- *)
(* Some "iff" variants of integrability on subsets.                          *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET_EQ = `(!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
        f measurable_on s /\
        !t. t SUBSET s /\ lebesgue_measurable t ==> f integrable_on t)`
and ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT_EQ = `(!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
        f measurable_on s /\
        !g. g measurable_on s /\ bounded(IMAGE g s)
            ==> (\x. drop(g x) % f x) integrable_on s)`;;

let ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT_EQ_ALT = `!f:real^M->real^N s.
        lebesgue_measurable s
        ==> (f absolutely_integrable_on s <=>
             !g. g measurable_on s /\ bounded(IMAGE g s)
                 ==> (\x. drop(g x) % f x) integrable_on s)`;;

let ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET_EQ_ALT = `!f:real^M->real^N s.
        lebesgue_measurable s
        ==> (f absolutely_integrable_on s <=>
             !t. t SUBSET s /\ lebesgue_measurable t ==> f integrable_on t)`;;

(* ------------------------------------------------------------------------- *)
(* More connections with measure where Lebesgue measurability is useful.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_LEBESGUE_MEASURABLE_SUBSET = `!s t:real^N->bool.
        lebesgue_measurable s /\ measurable t /\ s SUBSET t
        ==> measurable s`;;

let MEASURABLE_LEBESGUE_MEASURABLE_INTER_MEASURABLE = `!s t:real^N->bool.
        lebesgue_measurable s /\ measurable t ==> measurable(s INTER t)`;;

let MEASURABLE_MEASURABLE_INTER_LEBESGUE_MEASURABLE = `!s t:real^N->bool.
        measurable s /\ lebesgue_measurable t ==> measurable(s INTER t)`;;

let LEBESGUE_MEASURABLE_MEASURABLE_INTER_EQ = `!s:real^N->bool.
        lebesgue_measurable s <=>
        !t. measurable t ==> measurable(s INTER t)`;;

let MEASURABLE_INTER_HALFSPACE_LE = `!s a i. measurable s ==> measurable(s INTER {x:real^N | x$i <= a})`;;

let MEASURABLE_INTER_HALFSPACE_GE = `!s a i. measurable s ==> measurable(s INTER {x:real^N | x$i >= a})`;;

let MEASURABLE_MEASURABLE_DIFF_LEBESGUE_MEASURABLE = `!s t. measurable s /\ lebesgue_measurable t ==> measurable(s DIFF t)`;;

let MEASURABLE_OPEN_IN = `!s t:real^N->bool.
        open_in (subtopology euclidean s) t /\ measurable s
        ==> measurable t`;;

let MEASURABLE_CLOSED_IN = `!s t:real^N->bool.
        closed_in (subtopology euclidean s) t /\ measurable s
        ==> measurable t`;;

let MEASURABLE_ON_REAL_SGN = `!f:real^N->real s.
        (\x. lift(f x)) measurable_on s
        ==> (\x. lift(real_sgn(f x))) measurable_on s`;;

let LEBESGUE_MEASURABLE_INNER_COMPACT = `!s:real^N->bool.
        lebesgue_measurable s /\ ~negligible s
        ==> ?k. k SUBSET s /\ compact k /\ &0 < measure k`;;

let CHOOSE_LARGE_MEASURABLE_SUBSET = `!s:real^N->bool B.
        lebesgue_measurable s /\ ~measurable s
        ==> ?t. t SUBSET s /\ measurable t /\ B <= measure t`;;

let CHOOSE_LARGE_COMPACT_SUBSET = `!s:real^N->bool B.
        lebesgue_measurable s /\ ~measurable s
        ==> ?t. t SUBSET s /\ compact t /\ B <= measure t`;;

let CHOOSE_LARGE_COMPACT_SUBSET_ALT = `!(s:real^N->bool) B.
        lebesgue_measurable s /\ B < measure s
        ==> ?t. compact t /\ t SUBSET s /\ B < measure t`;;

let OUTER_LEBESGUE_MEASURE = `!s:real^N->bool.
     ?t. s SUBSET t /\ lebesgue_measurable t /\
         !t'. s SUBSET t' /\ lebesgue_measurable t' ==> negligible(t DIFF t')`;;

let OUTER_MEASURE_GEN = `!s u:real^N->bool.
        s SUBSET u /\ measurable u
        ==> ?t. s SUBSET t /\ measurable t /\
                !t'. s SUBSET t' /\ lebesgue_measurable t'
                     ==> negligible(t DIFF t')`;;

let OUTER_MEASURE_EQ = `!s:real^N->bool.
        (?t. s SUBSET t /\ measurable t) <=>
        (?t. s SUBSET t /\ measurable t /\
             !t'. s SUBSET t' /\ lebesgue_measurable t'
                  ==> negligible(t DIFF t'))`;;

(* ------------------------------------------------------------------------- *)
(* Continuity of measure with respect to parameters determining region.      *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_MEASURE_IN_PORTION = `!(f:real^M->real^N->real) s t.
        measurable s /\
        (!a. a IN t ==> lebesgue_measurable {x | f a x <= &0}) /\
        (!a. a IN t ==> negligible {x | f a x = &0}) /\
        (!x. x IN s ==> (\a. lift(f a x)) continuous_on t)
        ==> (\a. lift(measure {x | x IN s /\ f a x <= &0}))
            continuous_on t`;;

let CONTINUOUS_ON_MEASURE_IN_HALFSPACE = `!s b. measurable s
         ==> (\a. lift(measure {x | x IN s /\ a dot x <= b}))
             continuous_on ((:real^N) DELETE vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Negigibility of set with uncountably many disjoint translates.            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_DISJOINT_TRANSLATES = `!s:real^N->bool k z.
        lebesgue_measurable s /\ z limit_point_of k /\
        pairwise (\a b. DISJOINT (IMAGE (\x. a + x) s) (IMAGE (\x. b + x) s)) k
        ==> negligible s`;;

(* ------------------------------------------------------------------------- *)
(* Sometimes convenient to restrict the sets in "preimage" characterization  *)
(* of measurable functions to choose points from a dense set.                *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE_DENSE = `!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k <= a})`;;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE_DENSE = `!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k >= a})`;;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT_DENSE = `!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k < a})`;;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT_DENSE = `!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k > a})`;;

let MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL_DENSE = `!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a b. a IN t /\ b IN t
                   ==> lebesgue_measurable {x | f(x) IN interval[a,b]})`;;

let MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL_DENSE = `!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a b. a IN t /\ b IN t
                   ==> lebesgue_measurable {x | f(x) IN interval(a,b)})`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LE_DENSE = `!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k <= (a:real^N)$k})`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GE_DENSE = `!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k >= (a:real^N)$k})`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LT_DENSE = `!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k < (a:real^N)$k})`;;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GT_DENSE = `!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k > (a:real^N)$k})`;;

(* ------------------------------------------------------------------------- *)
(* Localized variants of function measurability equivalents.                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !t. closed t ==> lebesgue_measurable {x | x IN s /\ f x IN t}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_INTERVAL = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a b. lebesgue_measurable {x | x IN s /\ f x IN interval[a,b]}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !t. open t ==> lebesgue_measurable {x | x IN s /\ f x IN t}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k >= a}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k > a}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k <= a}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k < a}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_INTERVAL = `(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a b. lebesgue_measurable {x | x IN s /\ f x IN interval(a,b)}))`
and MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_BOREL = `(!f:real^M->real^N s.
        lebesgue_measurable s
        ==> (f measurable_on s <=>
             !t. borel t ==> lebesgue_measurable {x | x IN s /\ f x IN t}))`;;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_OPEN = `!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ open t
        ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`;;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = `!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ closed t
        ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`;;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_EQ = `!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. open t ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`;;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_EQ = `!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. closed t ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`;;

let MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !t. closed t ==> measurable {x | x IN s /\ f x IN t}))`
and MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED_INTERVAL = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a b. measurable {x | x IN s /\ f x IN interval[a,b]}))`
and MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !t. open t ==> measurable {x | x IN s /\ f x IN t}))`
and MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k >= a}))`
and MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k > a}))`
and MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k <= a}))`
and MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k < a}))`
and MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN_INTERVAL = `(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a b. measurable {x | x IN s /\ f x IN interval(a,b)}))`;;

let MEASURABLE_MEASURABLE_PREIMAGE_OPEN = `!f:real^M->real^N s t.
        f measurable_on s /\ measurable s /\ open t
        ==> measurable {x | x IN s /\ f(x) IN t}`;;

let MEASURABLE_MEASURABLE_PREIMAGE_CLOSED = `!f:real^M->real^N s t.
        f measurable_on s /\ measurable s /\ closed t
        ==> measurable {x | x IN s /\ f(x) IN t}`;;

let MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN_EQ = `!f:real^M->real^N s.
        f measurable_on s /\ measurable s <=>
        !t. open t ==> measurable {x | x IN s /\ f(x) IN t}`;;

let MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED_EQ = `!f:real^M->real^N s.
        f measurable_on s /\ measurable s <=>
        !t. closed t ==> measurable {x | x IN s /\ f(x) IN t}`;;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_BOREL = `!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ borel t
        ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`;;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_BOREL_EQ = `!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. borel t ==> lebesgue_measurable {x | x IN s /\ f x IN t}`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of analytic sets and related results.                       *)
(* ------------------------------------------------------------------------- *)

let SUSLIN_LEBESGUE_MEASURABLE = `suslin lebesgue_measurable:(real^N->bool)->bool = lebesgue_measurable`;;

let ANALYTIC_IMP_LEBESGUE_MEASURABLE = `!s:real^N->bool. analytic s ==> lebesgue_measurable s`;;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_ANALYTIC = `!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ analytic t
        ==> lebesgue_measurable {x | x IN s /\ f x IN t}`;;

let LEBESGUE_MEASURABLE_PREIMAGE_ANALYTIC = `!f:real^M->real^N t.
        f measurable_on (:real^M) /\ analytic t
        ==> lebesgue_measurable {x | f x IN t}`;;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_ANALYTIC_EQ = `!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. analytic t ==> lebesgue_measurable {x | x IN s /\ f x IN t}`;;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_ANALYTIC = `!f:real^M->real^N s.
        lebesgue_measurable s
        ==> (f measurable_on s <=>
             !t. analytic t ==> lebesgue_measurable {x | x IN s /\ f x IN t})`;;

let MEASURABLE_ON_PREIMAGE_ANALYTIC = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. analytic t ==> lebesgue_measurable {x | f x IN t}`;;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas about measurability and absolute integrals.        *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_LIFT_INV = `!f:real^N->real s.
        (\x. lift(f x)) measurable_on s /\ negligible {x | x IN s /\ f x = &0}
        ==> (\x. lift(inv(f x))) measurable_on s`;;

let MEASURABLE_ON_LIFT_DIV = `!f:real^N->real g s.
        (\x. lift(f x)) measurable_on s /\ (\x. lift(g x)) measurable_on s /\
        negligible {x | x IN s /\ g x = &0}
        ==> (\x. lift(f x / g x)) measurable_on s`;;

let ABSOLUTELY_INTEGRABLE_UNION = `!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ f absolutely_integrable_on t
        ==> f absolutely_integrable_on (s UNION t)`;;

let ABSOLUTELY_INTEGRABLE_DIFF = `!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ f absolutely_integrable_on t
        ==> f absolutely_integrable_on (s DIFF t)`;;

let ABSOLUTELY_INTEGRABLE_INTER = `!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ f absolutely_integrable_on t
        ==> f absolutely_integrable_on (s INTER t)`;;

let INTEGRAL_COUNTABLE_UNIONS_ALT = `!f:real^M->real^N s.
        f absolutely_integrable_on (UNIONS {s m | m IN (:num)}) /\
        (!m. lebesgue_measurable(s m))
        ==> (!n. f absolutely_integrable_on UNIONS {s m | m IN 0..n}) /\
            ((\n. integral (UNIONS {s m | m IN 0..n}) f)
             --> integral (UNIONS {s m | m IN (:num)}) f) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Regularity properties and Steinhaus, this time for Lebesgue measure.      *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_OUTER_OPEN = `!s:real^N->bool e.
        lebesgue_measurable s /\ &0 < e
        ==> ?t. open t /\
                s SUBSET t /\
                measurable(t DIFF s) /\
                measure(t DIFF s) < e`;;

let LEBESGUE_MEASURABLE_INNER_CLOSED = `!s:real^N->bool e.
        lebesgue_measurable s /\ &0 < e
        ==> ?t. closed t /\
                t SUBSET s /\
                measurable(s DIFF t) /\
                measure(s DIFF t) < e`;;

let STEINHAUS_LEBESGUE = `!s:real^N->bool.
        lebesgue_measurable s /\ ~negligible s
        ==> ?d. &0 < d /\ ball(vec 0,d) SUBSET {x - y | x IN s /\ y IN s}`;;

let LEBESGUE_MEASURABLE_REGULAR_OUTER = `!s:real^N->bool.
        lebesgue_measurable s
        ==> ?k c. negligible k /\ (!n. open(c n)) /\
                  s = INTERS {c n | n IN (:num)} DIFF k`;;

let LEBESGUE_MEASURABLE_REGULAR_INNER = `!s:real^N->bool.
        lebesgue_measurable s
        ==> ?k c. negligible k /\ (!n. compact(c n)) /\
                  s = UNIONS {c n | n IN (:num)} UNION k`;;

let LEBESGUE_MEASURABLE_SMALL_IMP_NEGLIGIBLE = `!s:real^N->bool. lebesgue_measurable s /\ s <_c (:real) ==> negligible s`;;

(* ------------------------------------------------------------------------- *)
(* A Lebesgue measurable set is almost an F_sigma or G_delta.                *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_ALMOST_FSIGMA = `!s:real^N->bool.
        lebesgue_measurable s
        ==> ?c t. fsigma c /\ negligible t /\ c UNION t = s /\ DISJOINT c t`;;

let LEBESGUE_MEASURABLE_ALMOST_GDELTA = `!s:real^N->bool.
        lebesgue_measurable s
        ==> ?c t. gdelta c /\ negligible t /\ s UNION t = c /\ DISJOINT t s`;;

(* ------------------------------------------------------------------------- *)
(* Existence of nonmeasurable subsets of any set of positive measure.        *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_IFF_LEBESGUE_MEASURABLE_SUBSETS = `!s:real^N->bool. negligible s <=> !t. t SUBSET s ==> lebesgue_measurable t`;;

let NEGLIGIBLE_IFF_MEASURABLE_SUBSETS = `!s:real^N->bool. negligible s <=> !t. t SUBSET s ==> measurable t`;;

let NON_MEASURABLE_SET = `?s:real^N->bool. ~lebesgue_measurable s`;;

(* ------------------------------------------------------------------------- *)
(* Preserving Lebesgue measurability vs. preserving negligibility.           *)
(* ------------------------------------------------------------------------- *)

let PRESERVES_LEBESGUE_MEASURABLE_IMP_PRESERVES_NEGLIGIBLE = `!f s:real^N->bool.
        (!t. negligible t /\ t SUBSET s ==> lebesgue_measurable(IMAGE f t))
        ==> (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t))`;;

let PRESERVES_NEGLIGIBLE_IMAGE = `!f:real^M->real^N s.
      (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t)) <=>
      (!t. negligible t /\ t SUBSET s ==> lebesgue_measurable(IMAGE f t))`;;

let PRESERVES_NEGLIGIBLE_IMAGE_UNIV = `!f:real^M->real^N.
        (!t. negligible t ==> negligible(IMAGE f t)) <=>
        (!t. negligible t  ==> lebesgue_measurable(IMAGE f t))`;;

let LEBESGUE_MEASURABLE_CONTINUOUS_IMAGE = `!f:real^M->real^N s.
        f continuous_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t))
        ==> !t. lebesgue_measurable t /\ t SUBSET s
                ==> lebesgue_measurable(IMAGE f t)`;;

let PRESERVES_LEBESGUE_MEASURABLE_IFF_PRESERVES_NEGLIGIBLE = `!f:real^M->real^N s.
        f continuous_on s
        ==> ((!t. lebesgue_measurable t /\ t SUBSET s
                  ==> lebesgue_measurable (IMAGE f t)) <=>
             (!t. negligible t /\ t SUBSET s ==> negligible (IMAGE f t)))`;;

let PRESERVES_LEBESGUE_MEASURABLE_IFF_PRESERVES_NEGLIGIBLE_ALT = `!f:real^M->real^N.
        f continuous_on s
        ==> ((!t. lebesgue_measurable t /\ t SUBSET s
                  ==> lebesgue_measurable (IMAGE f t)) <=>
             (!t. negligible t /\ t SUBSET s
                  ==> lebesgue_measurable(IMAGE f t)))`;;

let LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE = `!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\
        f differentiable_on s /\ lebesgue_measurable s
        ==> lebesgue_measurable(IMAGE f s)`;;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN = `!f:real^M->real^N s.
        linear f /\ lebesgue_measurable s /\ dimindex(:M) <= dimindex(:N)
        ==> lebesgue_measurable(IMAGE f s)`;;

let MEASURABLE_LINEAR_IMAGE_GEN = `!f:real^M->real^N s.
        linear f /\ measurable s /\ dimindex(:M) <= dimindex(:N)
        ==> measurable(IMAGE f s)`;;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ_GEN = `!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> (lebesgue_measurable(IMAGE f s) <=> lebesgue_measurable s)`;;

(* ------------------------------------------------------------------------- *)
(* Lebesgue-Lebesgue measurability (preimage of measurable is measurable).   *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_LEBESGUE_MEASURABLE = `!f:real^M->real^N.
        (!t. lebesgue_measurable t ==> lebesgue_measurable {x | f x IN t}) <=>
        f measurable_on (:real^M) /\
        (!t. negligible t ==> lebesgue_measurable {x | f x IN t})`;;

let DOUBLE_LEBESGUE_MEASURABLE_ON = `!f:real^M->real^N s t.
        lebesgue_measurable s /\ lebesgue_measurable t /\ IMAGE f s SUBSET t
        ==> ((!u. lebesgue_measurable u /\ u SUBSET t
                  ==> lebesgue_measurable {x | x IN s /\ f x IN u}) <=>
             f measurable_on s /\
             (!u. negligible u /\ u SUBSET t
                  ==> lebesgue_measurable {x | x IN s /\ f x IN u}))`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of continuous functions.                                    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = `!f:real^M->real^N s.
        f continuous_on s /\ lebesgue_measurable s
        ==> f measurable_on s`;;

let CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET = `!f:real^M->real^N s.
        f continuous_on s /\ closed s ==> f measurable_on s`;;

let CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = `!f:real^M->real^N s m.
        f continuous_on (s DIFF m) /\ lebesgue_measurable s /\ negligible m
        ==> f measurable_on s`;;

let MEASURABLE_CONTINUOUS_COMPOSE = `!f:real^N->real^P g:real^M->real^N.
        f measurable_on UNIV /\
        g continuous_on UNIV /\
        (!k. negligible k ==> negligible {x | g x IN k})
        ==> (f o g) measurable_on UNIV`;;

let MEASURABLE_ON_COMPOSE_REV = `!f:real^N->real^P g:real^M->real^N s t.
      lebesgue_measurable s /\ IMAGE g s = t /\
      (!k. lebesgue_measurable k /\ k SUBSET s
           ==> lebesgue_measurable (IMAGE g k)) /\
      (f o g) measurable_on s
      ==> f measurable_on t`;;

let MEASURABLE_ON_CONTINUOUS_COMPOSE_REV = `!f:real^N->real^P g:real^M->real^N s t.
      lebesgue_measurable s /\ IMAGE g s = t /\
      (!k. negligible k /\ k SUBSET s
           ==> lebesgue_measurable (IMAGE g k)) /\
      g continuous_on s /\
      (f o g) measurable_on s
      ==> f measurable_on t`;;

let MEASURABLE_ON_COMPOSE_GEN = `!f:real^N->real^P g:real^M->real^N s t.
      lebesgue_measurable t /\ IMAGE g s SUBSET t /\
      (!k. lebesgue_measurable k /\ k SUBSET t
           ==> lebesgue_measurable {x | x IN s /\ g x IN k}) /\
      f measurable_on t
      ==> (f o g) measurable_on s`;;

let MEASURABLE_ON_COMPOSE_ALT = `!f:real^N->real^P g:real^M->real^N s t.
      lebesgue_measurable s /\ lebesgue_measurable t /\ IMAGE g s SUBSET t /\
      (!k. negligible k /\ k SUBSET t
           ==> lebesgue_measurable {x | x IN s /\ g x IN k}) /\
      g measurable_on s /\
      f measurable_on t
      ==> (f o g) measurable_on s`;;

let MEASURABLE_ON_CONTINUOUS_COMPOSE = `!f:real^N->real^P g:real^M->real^N s t.
      lebesgue_measurable s /\ lebesgue_measurable t /\ IMAGE g s SUBSET t /\
      f measurable_on t /\ g continuous_on s /\
      (!k. negligible k /\ k SUBSET t
           ==> lebesgue_measurable {x | x IN s /\ g x IN k})
      ==> (f o g) measurable_on s`;;

let MEASURABLE_ON_DIFFERENTIABLE_IMAGE = `!f:real^N->real^P g:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\
        lebesgue_measurable s /\ g differentiable_on s /\
        (f o g) measurable_on s
        ==> f measurable_on (IMAGE g s)`;;

let BOREL_MEASURABLE_IMP_MEASURABLE_ON = `!f:real^M->real^N s.
       f borel_measurable_on s /\ lebesgue_measurable s ==> f measurable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Connections between measurability and Baire-ness.                         *)
(* ------------------------------------------------------------------------- *)

let BAIRE_IMP_MEASURABLE_ON = `!(f:real^M->real^N) s.
        baire n s f /\ lebesgue_measurable s ==> f measurable_on s`;;

let BAIRE_IMP_MEASURABLE_ON_UNIV = `!(f:real^M->real^N) s.
        baire n (:real^M) f ==> f measurable_on (:real^M)`;;

let MEASURABLE_EQ_ALMOST_BAIRE1 = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        ?s. negligible((:real^M) DIFF s) /\ baire 1 s f`;;

let MEASURABLE_EQ_ALMOST_BAIRE2 = `!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        ?g. baire 2 (:real^M) g /\ negligible {x | ~(g x = f x)}`;;

(* ------------------------------------------------------------------------- *)
(* Versions of the Lebesgue density theorem, both integral and measure       *)
(* forms. Later we have cosmetically nicer ones using real limits.           *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_DENSITY_THEOREM_INTEGRAL_NORM_CBALL = `!f:real^M->real^N.
        (!a b. f absolutely_integrable_on interval[a,b])
        ==> ?k. negligible k /\
                !x. ~(x IN k)
                    ==> ((\e. inv(measure(cball(x,drop e))) %
                              integral (cball(x,drop e))
                                       (\y. lift(norm(f y - f x))))
                        --> vec 0)
                        (at (vec 0) within {t | &0 < drop t})`;;

let LEBESGUE_DENSITY_THEOREM_INTEGRAL_NORM_BALL = `!f:real^M->real^N.
        (!a b. f absolutely_integrable_on interval[a,b])
        ==> ?k. negligible k /\
                !x. ~(x IN k)
                    ==> ((\e. inv(measure(ball(x,drop e))) %
                              integral (ball(x,drop e))
                                       (\y. lift(norm(f y - f x))))
                        --> vec 0)
                        (at (vec 0) within {t | &0 < drop t})`;;

let LEBESGUE_DENSITY_THEOREM_INTEGRAL_CBALL = `!f:real^M->real^N s.
        (!a b. f absolutely_integrable_on (s INTER interval[a,b]))
        ==> ?k. negligible k /\
                !x. ~(x IN k)
                    ==> ((\e. inv(measure(cball(x,drop e))) %
                              integral (s INTER cball(x,drop e)) f)
                         --> (if x IN s then f x else vec 0))
                        (at (vec 0) within {t | &0 < drop t})`;;

let LEBESGUE_DENSITY_THEOREM_INTEGRAL_BALL = `!f:real^M->real^N s.
        (!a b. f absolutely_integrable_on (s INTER interval[a,b]))
        ==> ?k. negligible k /\
                !x. ~(x IN k)
                    ==> ((\e. inv(measure(ball(x,drop e))) %
                              integral (s INTER ball(x,drop e)) f)
                         --> (if x IN s then f x else vec 0))
                        (at (vec 0) within {t | &0 < drop t})`;;

let LEBESGUE_DENSITY_THEOREM_LIFT_CBALL = `!s:real^N->bool.
      lebesgue_measurable s
      ==> ?k. negligible k /\
              !x. ~(x IN k)
                  ==> ((\e. lift(measure(s INTER cball(x,drop e)) /
                                 measure(cball(x,drop e))))
                       --> (if x IN s then vec 1 else vec 0))
                      (at (vec 0) within {t | &0 < drop t})`;;

let LEBESGUE_DENSITY_THEOREM_LIFT_BALL = `!s:real^N->bool.
      lebesgue_measurable s
      ==> ?k. negligible k /\
              !x. ~(x IN k)
                  ==> ((\e. lift(measure(s INTER ball(x,drop e)) /
                                 measure(ball(x,drop e))))
                       --> (if x IN s then vec 1 else vec 0))
                      (at (vec 0) within {t | &0 < drop t})`;;

(* ------------------------------------------------------------------------- *)
(* More refined form of "derivative is zero at a maximum or minimum"         *)
(* where we only need the derivative to hold w.r.t. a Lebesgue measurable    *)
(* set based at a point of density 1 (actually this could be further         *)
(* sharpened to density > 1/2, but it hardly seems worth it).                *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIAL_ZERO_MAXMIN_DENSITY = `!f f' s a:real^N.
        (f has_derivative f') (at a within s) /\
        (eventually (\x. drop(f a) <= drop(f x)) (at a within s) \/
         eventually (\x. drop(f x) <= drop(f a)) (at a within s)) /\
        lebesgue_measurable s /\
        ((\e. lift(measure(s INTER ball(a,drop e)) / measure(ball(a,drop e))))
         --> vec 1)
        (at (vec 0) within {t | &0 < drop t})
        ==> f' = \v. vec 0`;;

let DIFFERENTIAL_ZERO_LEVELSET_DENSITY = `!f:real^M->real^N f' s a c.
        (f has_derivative f') (at a within s) /\
        eventually (\x. f x = c) (at a within s) /\
        lebesgue_measurable s /\
        ((\e. lift
              (measure (s INTER ball (a,drop e)) /
               measure (ball (a,drop e)))) -->
         vec 1)
        (at (vec 0) within {t | &0 < drop t})
        ==> f' = \h. vec 0`;;

let NEGLIGIBLE_POINTS_OF_AMBIGUOUS_DERIVATIVE = `!f:real^M->real^N s.
        lebesgue_measurable s
        ==> negligible
             {x | x IN s /\ ?y z. (f has_derivative y) (at x within s) /\
                                  (f has_derivative z) (at x within s) /\
                                  ~(y = z)}`;;

(* ------------------------------------------------------------------------- *)
(* Can only have countably many disjoint sets of positive measure.           *)
(* ------------------------------------------------------------------------- *)

let PAIRWISE_DISJOINT_LEBESGUE_MEASURABLE_IMP_COUNTABLE = `!f:(real^N->bool)->bool.
        pairwise (\s t. negligible (s INTER t)) f /\
        (!s. s IN f ==> lebesgue_measurable s /\ ~negligible s)
        ==> COUNTABLE f`;;

(* ------------------------------------------------------------------------- *)
(* Various Vitali-type covering lemmas.                                      *)
(* ------------------------------------------------------------------------- *)

let WIENER_COVERING_LEMMA_BALLS = `!k a:A->real^N r s.
        FINITE k /\ s SUBSET UNIONS(IMAGE (\i. ball(a i,r i)) k)
        ==> ?c. c SUBSET k /\
                pairwise (\i j. DISJOINT (ball(a i,r i)) (ball(a j,r j))) c /\
                s SUBSET UNIONS(IMAGE (\i. ball(a i,&3 * r i)) c)`;;

let WIENER_COVERING_LEMMA_CBALLS = `!k a:A->real^N r s.
       FINITE k /\ s SUBSET UNIONS(IMAGE (\i. cball(a i,r i)) k)
       ==> ?c. c SUBSET k /\
               pairwise (\i j. DISJOINT (cball(a i,r i)) (cball(a j,r j))) c /\
               s SUBSET UNIONS(IMAGE (\i. cball(a i,&3 * r i)) c)`;;

let VITALI_COVERING_LEMMA_CBALLS_BALLS = `!a:A->real^N r k B.
      (!i. i IN k ==> &0 < r i /\ r i <= B)
      ==> ?c. COUNTABLE c /\
              c SUBSET k /\
              pairwise (\i j. DISJOINT (cball(a i,r i)) (cball(a j,r j))) c /\
              !i. i IN k
                  ==> ?j. j IN c /\
                          ~DISJOINT (cball(a i,r i)) (cball(a j,r j)) /\
                          cball(a i,r i) SUBSET ball(a j,&5 * r j)`;;

let VITALI_COVERING_LEMMA_CBALLS = `!s a:A->real^N r k B.
      s SUBSET UNIONS (IMAGE (\i. cball(a i,r i)) k) /\
      (!i. i IN k ==> &0 < r i /\ r i <= B)
      ==> ?c. COUNTABLE c /\
              c SUBSET k /\
              pairwise (\i j. DISJOINT (cball(a i,r i)) (cball(a j,r j))) c /\
              s SUBSET UNIONS (IMAGE (\i. cball(a i,&5 * r i)) c)`;;

let VITALI_COVERING_LEMMA_BALLS = `!s a:A->real^N r k B.
      s SUBSET UNIONS (IMAGE (\i. ball(a i,r i)) k) /\
      (!i. i IN k ==> &0 < r i /\ r i <= B)
      ==> ?c. COUNTABLE c /\
              c SUBSET k /\
              pairwise (\i j. DISJOINT (ball(a i,r i)) (ball(a j,r j))) c /\
              s SUBSET UNIONS (IMAGE (\i. ball(a i,&5 * r i)) c)`;;

let VITALI_COVERING_THEOREM_CBALLS = `!k a:A->real^N r s.
      (!i. i IN k ==> &0 < r i) /\
      (!x d. x IN s /\ &0 < d
             ==> ?i. i IN k /\ x IN cball(a i,r i) /\ r i < d)
      ==> ?c. COUNTABLE c /\ c SUBSET k /\
              pairwise (\i j. DISJOINT (cball(a i,r i)) (cball(a j,r j))) c /\
              negligible(s DIFF UNIONS {cball(a i,r i) | i IN c})`;;

let VITALI_COVERING_THEOREM_BALLS = `!k a:A->real^N r s.
      (!x d. x IN s /\ &0 < d
             ==> ?i. i IN k /\ x IN ball(a i,r i) /\ r i < d)
      ==> ?c. COUNTABLE c /\ c SUBSET k /\
              pairwise (\i j. DISJOINT (ball(a i,r i)) (ball(a j,r j))) c /\
              negligible(s DIFF UNIONS {ball(a i,r i) | i IN c})`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility is a local property (we actually use the topological        *)
(* notion, which looks iconoclastic but is perfectly sensible). More         *)
(* interestingly, it is equivalent, to localized zero density.               *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_NEGLIGIBLE_ALT = `!s:real^N->bool.
    negligible s <=>
    !x. x IN s
        ==> ?u. open_in (subtopology euclidean s) u /\ x IN u /\ negligible u`;;

let LOCALLY_NEGLIGIBLE = `!s:real^N->bool. locally negligible s <=> negligible s`;;

let LOCALLY_LEBESGUE_MEASURABLE_ALT = `!s:real^N->bool.
    lebesgue_measurable s <=>
    !x. x IN s
        ==> ?u. open_in (subtopology euclidean s) u /\
                x IN u /\ lebesgue_measurable u`;;

let LOCALLY_LEBESGUE_MEASURABLE = `!s:real^N->bool. locally lebesgue_measurable s <=> lebesgue_measurable s`;;

let NEGLIGIBLE_EQ_ZERO_DENSITY_ALT = `!s:real^N->bool.
        negligible s <=>
        !x e. x IN s /\ &0 < e
              ==> ?d u. &0 < d /\ d <= e /\
                        s INTER ball(x,d) SUBSET u /\
                        measurable u /\ measure u < e * measure(ball(x,d))`;;

let NEGLIGIBLE_EQ_ZERO_DENSITY = `!s:real^N->bool.
        negligible s <=>
        !x r e. x IN s /\ &0 < e /\ &0 < r
                ==> ?d u. &0 < d /\ d <= r /\
                          s INTER ball(x,d) SUBSET u /\
                          measurable u /\ measure u < e * measure(ball(x,d))`;;

(* ------------------------------------------------------------------------- *)
(* A handy but by no means optimal measurability lemma.                      *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_POINTS_OF_CONVERGENCE = `!f:real^M->real^N->real^P g s.
       lebesgue_measurable s /\
       (!y. (\x. f x y) continuous_on s) /\
       g continuous_on s
       ==> lebesgue_measurable {x | x IN s /\ ?l. (f x --> l) (at (g x))}`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of the set of points of differentiability and of the        *)
(* partial derivatives and vector derivatives. These proofs are both         *)
(* similar and have some technicalities to handle the extra generality       *)
(* of "within s" (we show that the set of points where this makes the        *)
(* limit ill-defined is negligible). In the unrestricted case, the same      *)
(* idea works and shows the set of points of differentiability is Borel.     *)
(* ------------------------------------------------------------------------- *)

let BOREL_POINTS_OF_DIFFERENTIABILITY = `!f:real^M->real^N. borel {x | f differentiable at x}`;;

let LEBESGUE_MEASURABLE_POINTS_OF_DIFFERENTIABILITY_WITHIN = `!f:real^M->real^N s.
     lebesgue_measurable s
     ==> lebesgue_measurable {x | x IN s /\ f differentiable (at x within s)}`;;

let LEBESGUE_MEASURABLE_POINTS_OF_DIFFERENTIABILITY_AT = `!f:real^M->real^N.
        lebesgue_measurable {x | f differentiable (at x)}`;;

let MEASURABLE_ON_PARTIAL_DERIVATIVES = `!f:real^M->real^N f' s i j.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:M)
        ==> (\x. lift(matrix(f' x)$i$j)) measurable_on s`;;

let MEASURABLE_ON_VECTOR_DERIVATIVE_GEN = `!f:real^1->real^N f' s.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_vector_derivative f'(x)) (at x within s))
        ==> f' measurable_on s`;;

let MEASURABLE_ON_VECTOR_DERIVATIVE = `!f:real^1->real^N f' s k.
        negligible k /\ lebesgue_measurable s /\
        (!x. x IN (s DIFF k) ==> (f has_vector_derivative f'(x)) (at x))
        ==> f' measurable_on s`;;

let MEASURABLE_ON_DET_JACOBIAN = `!f:real^N->real^N f' s.
         lebesgue_measurable s /\
         (!x. x IN s ==> (f has_derivative f' x) (at x within s))
         ==> (\x. lift(det(matrix(f' x)))) measurable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Luzin's theorem (Talvila and Loeb's proof from Marius Junge's notes).     *)
(* ------------------------------------------------------------------------- *)

let LUZIN = `!f:real^M->real^N s e.
        measurable s /\ f measurable_on s /\ &0 < e
        ==> ?k. compact k /\ k SUBSET s /\
                measure(s DIFF k) < e /\ f continuous_on k`;;

let LUZIN_EQ = `(!f:real^M->real^N s.
        measurable s
        ==> (f measurable_on s <=>
             !e. &0 < e
                 ==> ?k. compact k /\ k SUBSET s /\
                         measure(s DIFF k) < e /\ f continuous_on k))`
and LUZIN_EQ_ALT = `(!f:real^M->real^N s.
        measurable s
        ==> (f measurable_on s <=>
             !e. &0 < e
                 ==> ?k g. compact k /\ k SUBSET s /\
                           measure(s DIFF k) < e /\
                           g continuous_on (:real^M) /\
                           (!x. x IN k ==> g x = f x)))`;;

let LUZIN_SIGMA = `!f:real^M->real^N s.
       lebesgue_measurable s /\ f measurable_on s
       ==> ?u. COUNTABLE u /\ pairwise DISJOINT u /\
               (!k. k IN u ==> compact k /\ k SUBSET s /\ f continuous_on k) /\
               negligible(s DIFF UNIONS u)`;;

let LUZIN_SIGMA_EXPLICIT = `!f:real^M->real^N s.
        lebesgue_measurable s /\ f measurable_on s
        ==> ?k. (!n. compact(k n)) /\
                (!n. k n SUBSET s) /\
                (!n. f continuous_on k n) /\
                pairwise (\m n. DISJOINT (k m) (k n)) (:num) /\
                negligible(s DIFF UNIONS {k n | n IN (:num)})`;;

let LUZIN_SIGMA_NESTED = `!f:real^M->real^N s.
        lebesgue_measurable s /\ f measurable_on s
        ==> ?k. (!n. compact(k n)) /\
                (!n. k n SUBSET s) /\
                (!n. f continuous_on k n) /\
                (!n. k n SUBSET k(SUC n)) /\
                negligible(s DIFF UNIONS {k n | n IN (:num)})`;;

let PRESERVES_LEBESGUE_MEASURABLE_IFF_PRESERVES_NEGLIGIBLE_GEN = `!f:real^M->real^N s.
        f measurable_on s
        ==> ((!t. lebesgue_measurable t /\ t SUBSET s
                  ==> lebesgue_measurable (IMAGE f t)) <=>
             (!t. negligible t /\ t SUBSET s ==> negligible (IMAGE f t)))`;;

(* ------------------------------------------------------------------------- *)
(* Several variants of measurability of the Banach indicatrix.               *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_PREIMAGE_CARD_LE = `!f:real^M->real^N s n.
        f measurable_on s /\ lebesgue_measurable s /\
        (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))
        ==> lebesgue_measurable
              {y | FINITE {x | x IN s /\ f x = y} /\
                   CARD {x | x IN s /\ f x = y} <= n}`;;

let LEBESGUE_MEASURABLE_PREIMAGE_HAS_SIZE = `!f:real^M->real^N s n.
        f measurable_on s /\ lebesgue_measurable s /\
        (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))
        ==> lebesgue_measurable {y | {x | x IN s /\ f x = y} HAS_SIZE n}`;;

let LEBESGUE_MEASURABLE_PREIMAGE_FINITE = `!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s /\
        (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))
        ==> lebesgue_measurable {y | FINITE {x | x IN s /\ f x = y}}`;;

let LEBESGUE_MEASURABLE_PREIMAGE_INFINITE = `!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s /\
        (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))
        ==> lebesgue_measurable {y | INFINITE {x | x IN s /\ f x = y}}`;;

let MEASURABLE_ON_BANACH_INDICATRIX = `!f:real^M->real^N s c.
        f measurable_on s /\ lebesgue_measurable s /\
        (!t. t SUBSET s /\ negligible t ==> negligible (IMAGE f t))
        ==> (\y. if FINITE {x | x IN s /\ f x = y}
                 then lift(&(CARD{x | x IN s /\ f x = y}))
                 else c) measurable_on (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* A measurable subset on which a function is injective, the simple version  *)
(* first and then some approximate variants with a "better" subsets.         *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_DOMAIN_OF_INJECTIVITY = `!f:real^M->real^N s.
        f measurable_on s
        ==> ?t. lebesgue_measurable t /\ t SUBSET s /\
                IMAGE f t = IMAGE f s /\
                !x y. x IN t /\ y IN t /\ f x = f y ==> x = y`;;

let BOREL_DOMAIN_OF_INJECTIVITY = `!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s /\
        (!n. n SUBSET s /\ negligible n ==> negligible(IMAGE f n))
        ==> ?t. borel t /\ t SUBSET s /\
                negligible(IMAGE f s DIFF IMAGE f t) /\
                !x y. x IN t /\ y IN t /\ f x = f y ==> x = y`;;

let GDELTA_DOMAIN_OF_INJECTIVITY_MEASURABLE = `!f:real^M->real^N s u e.
        f measurable_on s /\ lebesgue_measurable s /\ &0 < e /\
        IMAGE f s SUBSET u /\ measurable u /\
        (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))
        ==> ?t. t SUBSET s /\ gdelta t /\ bounded t /\ measurable t /\
                measurable(IMAGE f t) /\
                measure(IMAGE f s DIFF IMAGE f t) < e /\
                (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Relations between image measure sizes and preimage cardinality. These     *)
(* are natural generalizations (from continuous functions on intervals) of   *)
(* two of the "Theorems of Banach" in Saks, "Theory of the Integral" IX.7.   *)
(* ------------------------------------------------------------------------- *)

let LUZIN_NPROPERTY_IMP_COUNTABLE_PREIMAGES = `!f:real^M->real^N s.
        lebesgue_measurable s /\ f measurable_on s /\
        (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))
        ==> negligible {y | ~COUNTABLE {x | x IN s /\ f x = y}}`;;

let BANACH_SPROPERTY_IMP_LUZIN_NPROPERTY_OUTER = `!f:real^M->real^N s.
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t. t SUBSET s /\ measurable t /\ measure t < d
                         ==> ?u. IMAGE f t SUBSET u /\
                                 measurable u /\ measure u < e)
        ==> (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))`;;

let BANACH_SPROPERTY_IMP_LUZIN_NPROPERTY = `!f:real^M->real^N s.
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t. t SUBSET s /\ measurable t /\ measure t < d
                         ==> measurable (IMAGE f t) /\ measure (IMAGE f t) < e)
        ==> (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))`;;

let BANACH_SPROPERTY_OUTER = `!f:real^M->real^N s.
        f measurable_on s /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t. t SUBSET s /\ measurable t /\ measure t < d
                         ==> ?u. IMAGE f t SUBSET u /\
                                 measurable u /\ measure u < e)
        ==> (!e. &0 < e
                 ==> ?d. &0 < d /\
                         !t. t SUBSET s /\ measurable t /\ measure t < d
                             ==> measurable (IMAGE f t) /\
                                 measure (IMAGE f t) < e)`;;

let BANACH_SPROPERTY_IMP_PRESERVES_MEASURABLE = `!f:real^M->real^N s.
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t. t SUBSET s /\ measurable t /\ measure t < d
                         ==> measurable (IMAGE f t) /\ measure (IMAGE f t) < e)
        ==> (!t. t SUBSET s /\ measurable t ==> measurable(IMAGE f t))`;;

let BANACH_SPROPERTY_IMP_FINITE_PREIMAGES = `!f:real^M->real^N s.
        f measurable_on s /\ measurable s /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t. t SUBSET s /\ measurable t /\ measure t < d
                         ==> measurable (IMAGE f t) /\
                             measure (IMAGE f t) < e)
        ==> negligible {y | INFINITE {x | x IN s /\ f x = y}}`;;

let ABSOLUTELY_CONTINUOUS_MEASURE_IMAGE = `!f:real^M->real^N s u.
        f measurable_on s /\ IMAGE f s SUBSET u /\ measurable u /\
        (!t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t)) /\
        negligible {y | INFINITE {x | x IN s /\ f x = y}}
        ==> (!e. &0 < e
                 ==> ?d. &0 < d /\
                         !t. t SUBSET s /\ measurable t /\ measure t < d
                             ==> measurable (IMAGE f t) /\
                                 measure (IMAGE f t) < e)`;;

let ABSOLUTELY_CONTINUOUS_MEASURE_DIFFERENTIABLE_IMAGE_GEN = `!f:real^N->real^N s.
      compact s /\
      f continuous_on s /\
      negligible (IMAGE f {x | x IN s /\ ~(f differentiable (at x within s))})
      ==> !e. &0 < e
              ==> ?d. &0 < d /\
                      !t. t SUBSET s /\ measurable t /\ measure t < d
                          ==> measurable(IMAGE f t) /\
                              measure(IMAGE f t) < e`;;

let ABSOLUTELY_CONTINUOUS_MEASURE_DIFFERENTIABLE_IMAGE = `!f:real^N->real^N s.
        compact s /\ f differentiable_on s
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !t. t SUBSET s /\ measurable t /\ measure t < d
                            ==> measurable(IMAGE f t) /\
                                measure(IMAGE f t) < e`;;

(* ------------------------------------------------------------------------- *)
(* More refined measurability bounds for Lipschitz or differentiable images. *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_LOCALLY_LIPSCHITZ_IMAGE = `!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ lebesgue_measurable s /\
        (!x. x IN s
             ==> ?t b. open t /\ x IN t /\
                       !y. y IN s INTER t
                           ==> norm(f y - f x) <= b * norm(y - x))
        ==> lebesgue_measurable(IMAGE f s)`;;

let MEASURABLE_LOCALLY_LIPSCHITZ_IMAGE = `(!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\
        measurable s /\
        (!x. x IN s
             ==> ?t. open t /\
                     x IN t /\
                     (!y. y IN s INTER t
                          ==> norm(f y - f x) <= B * norm(y - x)))
        ==> measurable(IMAGE f s))`
and MEASURE_LOCALLY_LIPSCHITZ_IMAGE = `(!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\
        measurable s /\
        (!x. x IN s
             ==> ?t. open t /\
                     x IN t /\
                     (!y. y IN s INTER t
                          ==> norm(f y - f x) <= B * norm(y - x)))
        ==> measure(IMAGE f s) <= B pow dimindex(:N) * measure s)`;;

let LEBESGUE_MEASURABLE_LIPSCHITZ_IMAGE = `!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ lebesgue_measurable s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> lebesgue_measurable(IMAGE f s)`;;

let MEASURABLE_LIPSCHITZ_IMAGE = `!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ measurable s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> measurable(IMAGE f s)`;;

let MEASURE_LIPSCHITZ_IMAGE = `!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ measurable s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> measure(IMAGE f s) <= B pow dimindex(:N) * measure s`;;

let MEASURABLE_BOUNDED_DIFFERENTIABLE_IMAGE = `(!f:real^N->real^N f' s B.
      measurable s /\
      (!x. x IN s
           ==> (f has_derivative f' x) (at x within s) /\
               abs(det(matrix(f' x))) <= B)
      ==> measurable(IMAGE f s))`
and MEASURE_BOUNDED_DIFFERENTIABLE_IMAGE = `(!f:real^N->real^N f' s B.
      measurable s /\
      (!x. x IN s
           ==> (f has_derivative f' x) (at x within s) /\
               abs(det(matrix(f' x))) <= B)
      ==> measure(IMAGE f s) <= B * measure s)`;;

let MEASURABLE_DIFFERENTIABLE_IMAGE = `(!f:real^N->real^N f' s.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        (\x. lift(abs(det(matrix(f' x))))) integrable_on s
        ==> measurable(IMAGE f s))`
and MEASURE_DIFFERENTIABLE_IMAGE = `(!f:real^N->real^N f' s b.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        (\x. lift(abs(det(matrix(f' x))))) integrable_on s /\
        drop(integral s (\x. lift(abs(det(matrix(f' x)))))) <= b
        ==> measure(IMAGE f s) <= b)`;;

let NEGLIGIBLE_DIFFERENTIABLE_PREIMAGE = `!f:real^M->real^N f' s t.
        dimindex(:M) = dimindex(:N) /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s) /\
                        rank(matrix(f' x)) = dimindex(:N)) /\
        negligible t
        ==> negligible {x | x IN s /\ f x IN t}`;;

(* ------------------------------------------------------------------------- *)
(* A one-way version of change-of-variables not assuming injectivity.        *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_ON_IMAGE,INTEGRAL_ON_IMAGE_DROP_UBOUND_LE =
  let lemma = `!a:real. {x | x IN s /\ f x <= a} =
              UNIONS {{x | x IN s /\ f x = b} |b| b IN IMAGE f s /\ b <= a}` in
  let version0 = `!f:real^N->real^1 g:real^N->real^N g' s b.
          lebesgue_measurable s /\
          f measurable_on (IMAGE g s) /\
          (!x. x IN s ==> &0 <= drop(f(g x))) /\
          (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
          (!t. t SUBSET IMAGE g s /\ lebesgue_measurable t
               ==> lebesgue_measurable {x | x IN s /\ g x IN t}) /\
          (\x. abs(det(matrix(g' x))) % f(g x)) integrable_on s /\
          drop (integral s (\x. abs(det(matrix (g' x))) % f(g x))) <= b
          ==> f integrable_on (IMAGE g s) /\
              drop(integral (IMAGE g s) f) <= b` in
  let version1 = `!f:real^N->real^1 g:real^N->real^N g' s b.
          (!x. x IN s ==> &0 <= drop(f(g x))) /\
          (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
          (\x. abs(det(matrix(g' x))) % f(g x)) integrable_on s /\
          drop(integral s (\x. abs(det(matrix (g' x))) % f(g x))) <= b
          ==> f integrable_on (IMAGE g s) /\
              drop(integral (IMAGE g s) f) <= b` in
  let version2 = `!f:real^N->real^1 g:real^N->real^N g' s.
          (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
          (\x. abs(det(matrix(g' x))) % f(g x)) absolutely_integrable_on s
          ==> f absolutely_integrable_on (IMAGE g s)` in
  let ABSOLUTELY_INTEGRABLE_ON_IMAGE = `!f:real^M->real^N g:real^M->real^M g' s.
          (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
          (\x. abs(det(matrix(g' x))) % f(g x)) absolutely_integrable_on s
          ==> f absolutely_integrable_on (IMAGE g s)` in
  let INTEGRAL_ON_IMAGE_DROP_UBOUND_LE = `!f:real^N->real^1 g:real^N->real^N g' s b.
          (!x. x IN s ==> &0 <= drop(f(g x))) /\
          (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
          (\x. abs(det(matrix(g' x))) % f(g x)) integrable_on s /\
          drop(integral s (\x. abs(det(matrix (g' x))) % f(g x))) <= b
          ==> drop(integral (IMAGE g s) f) <= b` in
  ABSOLUTELY_INTEGRABLE_ON_IMAGE,INTEGRAL_ON_IMAGE_DROP_UBOUND_LE;;

(* ------------------------------------------------------------------------- *)
(* The classic change-of-variables theorem. We have two versions with quite  *)
(* general hypotheses, the first that the transforming function has a        *)
(* continuous inverse, the second that the base set is Lebesgue measurable.  *)
(* I am not sure if one can eliminate both of these hypotheses, but anyway   *)
(* it's hard to imagine a useful application to a non-measurable set.        *)
(* ------------------------------------------------------------------------- *)

let HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_INVERTIBLE = `!f:real^M->real^N g:real^M->real^M h g' s b.
      (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
      (!x. x IN s ==> h(g x) = x) /\ h continuous_on IMAGE g s
      ==> ((\x. abs(det(matrix(g' x))) % f(g x))
           absolutely_integrable_on s /\
           integral s (\x. abs(det(matrix(g' x))) % f(g x)) = b <=>
           f absolutely_integrable_on (IMAGE g s) /\
           integral (IMAGE g s) f = b)`;;

let HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES = `!f:real^M->real^N g:real^M->real^M g' s b.
      lebesgue_measurable s /\
      (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
      (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
      ==> ((\x. abs(det(matrix(g' x))) % f(g x)) absolutely_integrable_on s /\
           integral s (\x. abs(det(matrix(g' x))) % f(g x)) = b <=>
           f absolutely_integrable_on (IMAGE g s) /\
           integral (IMAGE g s) f = b)`;;

let ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES = `!f:real^M->real^N g:real^M->real^M g' s.
      lebesgue_measurable s /\
      (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
      (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
      ==> (f absolutely_integrable_on (IMAGE g s) <=>
           (\x. abs(det(matrix(g' x))) % f(g x)) absolutely_integrable_on s)`;;

let INTEGRAL_CHANGE_OF_VARIABLES = `!f:real^M->real^N g:real^M->real^M g' s.
      lebesgue_measurable s /\
      (!x. x IN s ==> (g has_derivative g' x) (at x within s)) /\
      (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\
       (f absolutely_integrable_on (IMAGE g s) \/
        (\x. abs(det(matrix(g' x))) % f(g x)) absolutely_integrable_on s)
      ==> integral (IMAGE g s) f =
          integral s (\x. abs(det(matrix(g' x))) % f(g x))`;;

let HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_1 = `!f:real^1->real^N g:real^1->real^1 g' s b.
        lebesgue_measurable s /\
         (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\
         (!x. x IN s
              ==> (g has_vector_derivative lift (g' (drop x)))
                  (at x within s))
         ==> ((\x. abs (g' (drop x)) % f (g x)) absolutely_integrable_on s /\
              integral s (\x. abs (g' (drop x)) % f (g x)) = b <=>
              f absolutely_integrable_on IMAGE g s /\
              integral (IMAGE g s) f = b)`;;

let ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_1 = `!f:real^1->real^N g:real^1->real^1 g' s.
        lebesgue_measurable s /\
        (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\
        (!x. x IN s
             ==> (g has_vector_derivative lift (g' (drop x)))
                 (at x within s))
        ==> (f absolutely_integrable_on IMAGE g s <=>
             (\x. abs(g'(drop x)) % f(g x)) absolutely_integrable_on s)`;;

(* ------------------------------------------------------------------------- *)
(* Change of variable for measure.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_DIFFERENTIABLE_IMAGE = `!f:real^N->real^N f' s m.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> (IMAGE f s has_measure m <=>
             ((\x. lift(abs(det(matrix(f' x))))) has_integral (lift m)) s)`;;

let MEASURABLE_DIFFERENTIABLE_IMAGE_EQ = `!f:real^N->real^N f' s.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> (measurable (IMAGE f s) <=>
             (\x. lift(abs(det(matrix(f' x))))) integrable_on s)`;;

let MEASURABLE_DIFFERENTIABLE_IMAGE_ALT = `!f:real^N->real^N f' s.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> (measurable (IMAGE f s) <=>
             (\x. lift(abs(det(matrix(f' x))))) absolutely_integrable_on s)`;;

let MEASURE_DIFFERENTIABLE_IMAGE_EQ = `!f:real^N->real^N f' s.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        (\x. lift(abs(det(matrix(f' x))))) integrable_on s
        ==> measure (IMAGE f s) =
            drop(integral s (\x. lift(abs(det(matrix(f' x))))))`;;

(* ------------------------------------------------------------------------- *)
(* Change of variables for integrals again: special case of linear function. *)
(* ------------------------------------------------------------------------- *)

let HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_LINEAR = `!f:real^M->real^N g:real^M->real^M s b.
      linear g
      ==> ((\x. abs(det(matrix g)) % f(g x)) absolutely_integrable_on s /\
           integral s (\x. abs(det(matrix g)) % f(g x)) = b <=>
           f absolutely_integrable_on (IMAGE g s) /\
           integral (IMAGE g s) f = b)`;;

let ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_LINEAR = `!f:real^M->real^N g:real^M->real^M s.
      linear g
      ==> ((\x. abs(det(matrix g)) % f(g x)) absolutely_integrable_on s <=>
           f absolutely_integrable_on (IMAGE g s))`;;

let ABSOLUTELY_INTEGRABLE_ON_LINEAR_IMAGE = `!f:real^M->real^N g:real^M->real^M s.
      linear g
      ==> (f absolutely_integrable_on (IMAGE g s) <=>
           (f o g) absolutely_integrable_on s \/ det(matrix g) = &0)`;;

let INTEGRAL_CHANGE_OF_VARIABLES_LINEAR = `!f:real^M->real^N g:real^M->real^M s.
        linear g /\
        (f absolutely_integrable_on (IMAGE g s) \/
         (f o g) absolutely_integrable_on s)
        ==> integral (IMAGE g s) f = abs(det(matrix g)) % integral s (f o g)`;;

(* ------------------------------------------------------------------------- *)
(* Approximation of L_1 functions by bounded continuous ones.                *)
(* Note that 100/fourier.ml has some generalizations to L_p spaces.          *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS = `!f:real^M->real^N s e.
        lebesgue_measurable s /\ f absolutely_integrable_on s /\ &0 < e
        ==> ?g. g absolutely_integrable_on s /\
                g continuous_on (:real^M) /\
                bounded (IMAGE g (:real^M)) /\
                norm(integral s (\x. lift(norm(f x - g x)))) < e`;;

(* ------------------------------------------------------------------------- *)
(* A kind of continuity of the (absolute) integral under translation.        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_ABSOLUTELY_INTEGRABLE_TRANSLATION_NORM = `!f:real^M->real^N.
        f absolutely_integrable_on (:real^M)
        ==> ((\a. integral (:real^M) (\x. lift(norm(f(a + x) - f x))))
             --> vec 0) (at (vec 0))`;;

let CONTINUOUS_ON_ABSOLUTELY_INTEGRABLE_TRANSLATION_NORM_GEN = `!f:real^M->real^N s t.
       f absolutely_integrable_on s /\ lebesgue_measurable t /\ t SUBSET s
       ==> ((\a. integral t (\x. lift(norm(f(a + x) - f x)))) --> vec 0)
           (at (vec 0) within {a | IMAGE (\x. a + x) t SUBSET s})`;;

let CONTINUOUS_ON_ABSOLUTELY_INTEGRABLE_TRANSLATION_GEN = `!f:real^M->real^N s t.
       f absolutely_integrable_on s /\ lebesgue_measurable t
       ==> (\a. integral t (\x. f(a + x))) continuous_on
           {a | IMAGE (\x. a + x) t SUBSET s}`;;

let CONTINUOUS_ON_ABSOLUTELY_INTEGRABLE_TRANSLATION = `!f:real^M->real^N.
       f absolutely_integrable_on (:real^M)
       ==> (\a. integral (:real^M) (\x. f(a + x))) continuous_on (:real^M)`;;

let CONTINUOUS_MEASURE_TRANSLATION_SYMDIFF = `!s:real^N->bool.
        measurable s
        ==> ((\a. lift(measure(((IMAGE (\x. a + x) s) DIFF s) UNION
                               (s DIFF IMAGE (\x. a + x) s)))) --> vec 0)
            (at (vec 0))`;;

let CONTINUOUS_MEASURE_TRANSLATION_DIFF = `!s:real^N->bool.
        measurable s
        ==> ((\a. lift(measure((IMAGE (\x. a + x) s) DIFF s))) --> vec 0)
            (at (vec 0))`;;

let CONTINUOUS_MEASURE_DIFFERENTIABLE_IMAGE_TRANSLATION = `!f:real^N->real^N s k.
        open s /\ f differentiable_on s /\ compact k
        ==> (\a. lift(measure(IMAGE f (IMAGE (\x. a + x) k))))
            continuous_on {a | IMAGE (\x. a + x) k SUBSET s}`;;

(* ------------------------------------------------------------------------- *)
(* A kind of mean-value theorem for integrals w.r.t. arbitrarily small       *)
(* subintervals, similar to the one in Saint-Raymond's "Local Inversion..."  *)
(* ------------------------------------------------------------------------- *)

let SUBINTERVAL_MEAN_VALUE_THEOREM = `!f:real^N->real^1 a b n.
        ~(interval[a,b] = {}) /\ ~(n = 0) /\
        f absolutely_integrable_on interval[a,b]
        ==> ?c d. c + inv(&n) % (b - a) = d /\
                  interval[c,d] SUBSET interval[a,b] /\
                  measure(interval[a,b]) % integral (interval[c,d]) f =
                  measure(interval[c,d]) % integral (interval[a,b]) f`;;

let SUBINTERVAL_MEAN_VALUE_THEOREM_SEQ = `!f:real^N->real^1 a b.
      ~(interval[a,b] = {}) /\ f absolutely_integrable_on interval[a,b]
      ==> ?c d. (!n. ?m. ~(m = 0) /\ c n + inv(&m) % (b - a) = d n) /\
                (!n. ~(interval[c n,d n] = {})) /\
                ((\n. d n - c n) --> vec 0) sequentially /\
                (!n. interval[c n,d n] SUBSET interval[a,b]) /\
                (!n. interval[c(SUC n),d(SUC n)] SUBSET interval[c n,d n]) /\
                (!n. measure(interval[a,b]) % integral (interval[c n,d n]) f =
                     measure(interval[c n,d n]) % integral (interval[a,b]) f)`;;

let SUBINTERVAL_MEAN_VALUE_THEOREM_ALT = `!f:real^N->real^1 a b.
        ~(interval[a,b] = {}) /\ f absolutely_integrable_on interval[a,b]
        ==> ?x. x IN interval[a,b] /\
                !e. &0 < e
                    ==> ?c d n.
                          ~(n = 0) /\ c + inv(&n) % (b - a) = d /\
                          x IN interval[c,d] /\
                          interval[c,d] SUBSET interval[a,b] /\
                          diameter(interval[c,d]) < e /\
                          measure(interval[a,b]) % integral (interval[c,d]) f =
                          measure(interval[c,d]) % integral (interval[a,b]) f`;;

(* ------------------------------------------------------------------------- *)
(* A kind of intermediate value result for a function where all points are   *)
(* a weak kind of Lebesgue point (inspired by Saint-Raymond's paper).        *)
(* ------------------------------------------------------------------------- *)

let WEAK_LEBESGUE_POINTS_IMP_IVT = `!f:real^N->real^1 a b s.
        open s /\ connected s /\ ~(interval(a,b) = {}) /\
        locally ((absolutely_integrable_on) f) s /\
        (!c x. x IN s /\
               (!n. ?u v. &0 < u /\
                          c n = IMAGE (\x. u % x + v) (interval[a,b])) /\
               eventually (\n. x IN c n) sequentially /\
               ((\n. lift(diameter(c n))) --> vec 0) sequentially
               ==> ((\n. inv(measure(c n)) % integral (c n) f) --> f x)
                   sequentially)
        ==> connected(IMAGE f s)`;;

(* ------------------------------------------------------------------------- *)
(* More from Saint Raymond's paper "Local Inversion for Differentiable       *)
(* Functions and the Darboux Property". The earlier parts are back in        *)
(* Multivariate/derivatives.ml but this part of the reasoning needs measure. *)
(* ------------------------------------------------------------------------- *)

let MEASURE_DIFFERENTIABLE_IMAGE_APPROX_GEN = `!f:real^N->real^N s c a.
        open s /\ f differentiable_on s /\
        (!v. v SUBSET s /\ open v ==> open(IMAGE f v)) /\
        a IN s /\ ~(det(jacobian f (at a)) = &0) /\
        ((\n. lift(diameter (c n))) --> vec 0) sequentially /\
        (!n. a IN closure(c n)) /\
        (?A. convex A /\ bounded A /\ ~(interior A = {}) /\
             !n. ?t z. &0 < t /\ IMAGE (\x. t % x + z) A = c n)
        ==> eventually (\n. measurable(IMAGE f (c n))) sequentially /\
            ((\n. lift(measure(IMAGE f (c n)) / measure(c n)))
             --> lift(abs(det(jacobian f (at a))))) sequentially`;;

let MEASURE_DIFFERENTIABLE_IMAGE_APPROX = `!f:real^N->real^N f' s c a.
        open s /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\
                 ~(det(matrix (f' x)) = &0)) /\
        ((\n. lift(diameter (c n))) --> vec 0) sequentially /\
        (!n. a IN closure(c n)) /\
        (?A. convex A /\ bounded A /\ ~(interior A = {}) /\
             !n. ?t z. &0 < t /\ IMAGE (\x. t % x + z) A = c n)
        ==> eventually (\n. measurable(IMAGE f (c n))) sequentially /\
            ((\n. lift(measure(IMAGE f (c n)) / measure(c n)))
             --> lift(abs(det(matrix(f' a))))) sequentially`;;

let CONNECTED_JACOBIAN_RANGE = `!f:real^N->real^N f' s.
        open s /\ connected s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0))
        ==> connected (IMAGE (\x. lift(det(matrix(f' x)))) s)`;;

let CONNECTED_JACOBIAN_RANGE_ALT = `!f:real^N->real^N f' s t a b.
       open s /\ connected s /\ convex t /\ t SUBSET s /\ ~(interior t = {}) /\
       (!x. x IN s
            ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0)) /\
       a IN t /\ b IN t
       ==> segment(lift(det(matrix(f' a))),lift(det(matrix(f' b))))
           SUBSET IMAGE (\x. lift(det(matrix(f' x)))) (interior t)`;;

let CONNECTED_JACOBIAN_RANGE_SUBSET = `!f:real^N->real^N f' s t.
       open s /\ connected s /\ convex t /\ t SUBSET s /\ ~(interior t = {}) /\
       (!x. x IN s
            ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0))
       ==> connected (IMAGE (\x. lift(det(matrix(f' x)))) t)`;;

let CONNECTED_JACOBIAN_GRAPH = `!f:real^N->real^N f' s.
        open s /\ connected s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0))
        ==> connected {pastecart x (lift(det(matrix(f' x)))) | x IN s}`;;

(* ------------------------------------------------------------------------- *)
(* A derivative-free formulation of (absolute) integration by parts.         *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTE_INTEGRATION_BY_PARTS = `!(bop:real^M->real^N->real^P) (f:real^1->real^M) g f' g' a b.
        bilinear bop /\ drop a <= drop b /\
        f' absolutely_integrable_on interval[a,b] /\
        g' absolutely_integrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> (f' has_integral f(x)) (interval[a,x])) /\
        (!x. x IN interval[a,b] ==> (g' has_integral g(x)) (interval[a,x]))
        ==> (\x. bop (f x) (g' x)) absolutely_integrable_on interval[a,b] /\
            (\x. bop (f' x) (g x)) absolutely_integrable_on interval[a,b] /\
            integral (interval[a,b]) (\x. bop (f x) (g' x)) +
            integral (interval[a,b]) (\x. bop (f' x) (g x)) =
            bop (f b) (g b) - bop (f a) (g a)`;;

(* ------------------------------------------------------------------------- *)
(* Measurability of inverse function (including sections / selections).      *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_LEBESGUE_MEASURABLE_INVERSE_FUNCTION_GEN = `!f:real^M->real^N s.
        f measurable_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t))
        ==> (!t. lebesgue_measurable t
                 ==> lebesgue_measurable(IMAGE f (s INTER t)))`;;

let DOUBLE_LEBESGUE_MEASURABLE_INVERSE_FUNCTION = `!f:real^M->real^N g s.
        f measurable_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t)) /\
        (!x. x IN s ==> g(f x) = x)
        ==> !t. lebesgue_measurable t
                ==> lebesgue_measurable {y | y IN IMAGE f s /\ g y IN t}`;;

let LEBESGUE_MEASURABLE_MEASURABLE_IMAGE = `(!f:real^M->real^N s.
        f measurable_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t)) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> lebesgue_measurable(IMAGE f s))`
and MEASURABLE_ON_INVERSE_FUNCTION = `(!f:real^M->real^N g s.
        f measurable_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t)) /\
        (!x. x IN s ==> g(f x) = x)
        ==> g measurable_on (IMAGE f s))`;;

let DOUBLE_LEBESGUE_MEASURABLE_LEFT_INVERSE = `!f:real^M->real^N s.
      f measurable_on s /\
      (!t. negligible t /\ t SUBSET s ==> negligible (IMAGE f t)) /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
      ==> ?g. (!x. x IN s ==> g(f x) = x) /\
              (!t. lebesgue_measurable t
                   ==> lebesgue_measurable {y | y IN IMAGE f s /\ g y IN t})`;;

let MEASURABLE_ON_LEFT_INVERSE = `!f:real^M->real^N s.
        f measurable_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible (IMAGE f t)) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ?g. (!x. x IN s ==> g(f x) = x) /\ g measurable_on IMAGE f s`;;

let DOUBLE_LEBESGUE_MEASURABLE_RIGHT_INVERSE = `!f:real^M->real^N s.
       f measurable_on s /\
       (!t. negligible t /\ t SUBSET s ==> negligible (IMAGE f t))
       ==> ?g. (!y. y IN IMAGE f s ==> g y IN s /\ f(g y) = y) /\
               (!t. lebesgue_measurable t
                    ==> lebesgue_measurable {y | y IN IMAGE f s /\ g y IN t})`;;

let MEASURABLE_ON_RIGHT_INVERSE = `!f:real^M->real^N s.
        f measurable_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible (IMAGE f t))
        ==> ?g. (!y. y IN IMAGE f s ==> g y IN s /\ f(g y) = y) /\
                g measurable_on IMAGE f s`;;

(* ------------------------------------------------------------------------- *)
(* Egorov's thoerem.                                                         *)
(* ------------------------------------------------------------------------- *)

let EGOROV = `!f:num->real^M->real^N g s t.
        measurable s /\ negligible t /\ (!n. f n measurable_on s) /\
        (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially)
        ==> !d. &0 < d
                ==> ?k. k SUBSET s /\ measurable k /\ measure k < d /\
                        !e. &0 < e
                            ==> ?N. !n x. N <= n /\ x IN s DIFF k
                                          ==> dist(f n x,g x) < e`;;

(* ------------------------------------------------------------------------- *)
(* The Lebesgue differentiation theorem.                                     *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_DIFFERENTIATION_THEOREM_COMPACT = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> negligible {x | x IN interval[a,b] /\ ~(f differentiable at x)}`;;

let LEBESGUE_DIFFERENTIATION_THEOREM = `!f:real^1->real^N s.
        is_interval s /\ f has_bounded_variation_on s
        ==> negligible {x | x IN s /\ ~(f differentiable at x)}`;;

let LEBESGUE_DIFFERENTIATION_THEOREM_ALT = `!f:real^1->real^N s.
        is_interval s /\ f has_bounded_variation_on s
        ==> ?t. t SUBSET s /\ negligible t /\
                !x. x IN s DIFF t ==> f differentiable at x`;;

let LEBESGUE_DIFFERENTIATION_THEOREM_GEN = `!f:real^1->real^N s.
        COUNTABLE(components s) /\ f has_bounded_variation_on s
        ==> negligible {x | x IN s /\ ~(f differentiable at x)}`;;

let LEBESGUE_DIFFERENTIATION_THEOREM_INCREASING = `!f s.
      is_interval s /\
      (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f x) <= drop(f y))
      ==> negligible {x | x IN s /\ ~(f differentiable at x)}`;;

let LEBESGUE_DIFFERENTIATION_THEOREM_DECREASING = `!f s.
      is_interval s /\
      (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f y) <= drop(f x))
      ==> negligible {x | x IN s /\ ~(f differentiable at x)}`;;

(* ------------------------------------------------------------------------- *)
(* Forms of absolute continuity of the indefinite (absolute) integral.       *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_CONTINUOUS_INTEGRAL = `!f:real^M->real^N s e.
        f absolutely_integrable_on s /\ &0 < e
        ==> ?d. &0 < d /\
                !t. t SUBSET s /\ measurable t /\ measure t < d
                    ==> norm(integral t f) < e`;;

let ABSOLUTELY_SETCONTINUOUS_INDEFINITE_INTEGRAL = `!f:real^M->real^N s.
        f absolutely_integrable_on s /\ lebesgue_measurable s
        ==> (\k. integral k f) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_RIGHT = `!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\x. integral(interval[a,x]) f)
            absolutely_continuous_on interval[a,b]`;;

let ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_LEFT = `!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\x. integral(interval[x,b]) f)
            absolutely_continuous_on interval[a,b]`;;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS = `!f:real^1->real^N f' s a b.
      negligible s /\ drop a <= drop b /\
      f absolutely_continuous_on interval[a,b] /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
      ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`;;

let ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_EQ = `!f:real^1->real^N a b.
      f absolutely_integrable_on interval[a,b] <=>
      f integrable_on interval[a,b] /\
      (\t. integral(interval[a,t]) f) has_bounded_variation_on interval[a,b]`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE = `!f:real^1->real^N f' s a b.
      f absolutely_continuous_on interval[a,b] /\
      negligible s /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
      ==> f' absolutely_integrable_on interval[a,b]`;;

let ABSOLUTE_INTEGRAL_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ = `!f:real^1->real^N f' a b.
      f' absolutely_integrable_on interval[a,b] /\
      (!x. x IN interval[a,b]
           ==> (f' has_integral (f x - f a)) (interval[a,x])) <=>
      f absolutely_continuous_on interval[a,b] /\
      ?s. negligible s /\
          !x. x IN interval [a,b] DIFF s
              ==> (f has_vector_derivative f' x) (at x within interval[a,b])`;;

let ABSOLUTE_INTEGRAL_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ_ALT = `!f:real^1->real^N f' a b.
      f' absolutely_integrable_on interval[a,b] /\
      (!x. x IN interval[a,b]
           ==> (f' has_integral (f x - f a)) (interval[a,x])) <=>
      f absolutely_continuous_on interval[a,b] /\
      ?s. negligible s /\
          !x. x IN interval [a,b] DIFF s
              ==> (f has_vector_derivative f' x) (at x)`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ = `!f':real^1->real^N a b.
     f' absolutely_integrable_on interval[a,b] <=>
     ?f s. f absolutely_continuous_on interval[a,b] /\
           negligible s /\
           !x. x IN interval [a,b] DIFF s
               ==> (f has_vector_derivative f' x) (at x within interval[a,b])`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ_ALT = `!f':real^1->real^N a b.
     f' absolutely_integrable_on interval[a,b] <=>
     ?f s. f absolutely_continuous_on interval[a,b] /\
           negligible s /\
           !x. x IN interval [a,b] DIFF s
               ==> (f has_vector_derivative f' x) (at x)`;;

let ABSOLUTE_INTEGRATION_BY_PARTS_SUM = `!(bop:real^M->real^N->real^P) (f:real^1->real^M) g f' g' a b.
        bilinear bop /\ drop a <= drop b /\
        (f' absolutely_integrable_on interval[a,b] /\
         !x. x IN interval[a,b]
             ==> (f' has_integral f(x) - f(a)) (interval[a,x])) /\
        (g' absolutely_integrable_on interval[a,b] /\
         !x. x IN interval[a,b]
             ==> (g' has_integral g(x) - g(a)) (interval[a,x]))
        ==> (\x. bop (f x) (g' x) + bop (f' x) (g x))
            absolutely_integrable_on interval[a,b] /\
            !x. x IN interval[a,b]
                ==> ((\x. bop (f x) (g' x) + bop (f' x) (g x))
                     has_integral (bop (f x) (g x) - bop (f a) (g a)))
                    (interval[a,x])`;;

(* ------------------------------------------------------------------------- *)
(* Characterizing absolutely continuous functions as Lebesgue integrals.     *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_INCREASING_DERIVATIVE = `!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> ?s f'. negligible s /\
                   (!x. x IN interval[a,b] DIFF s
                        ==> (f has_vector_derivative f' x) (at x)) /\
                   f' absolutely_integrable_on interval[a,b] /\
                   (!x. x IN interval[a,b]
                        ==> drop(integral(interval[a,x]) f')
                            <= drop(f x) - drop(f a))`;;

let ABSOLUTELY_INTEGRABLE_INCREASING_DERIVATIVE_ALT = `!f:real^1->real^1 f' a b s.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        negligible s /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f' x) (at x))
        ==> f' absolutely_integrable_on interval[a,b] /\
            (!x. x IN interval[a,b]
                 ==> drop(integral(interval[a,x]) f')
                     <= drop(f x) - drop(f a))`;;

let ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_DERIVATIVE = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> ?f' s. negligible s /\
                   (!x. x IN interval[a,b] DIFF s
                        ==> (f has_vector_derivative f' x) (at x)) /\
                   f' absolutely_integrable_on interval[a,b]`;;

let ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_EQ = `!f:real^1->real^N a b.
        f absolutely_continuous_on interval[a,b] <=>
        ?f'. f' absolutely_integrable_on interval[a,b] /\
             !x. x IN interval[a,b]
                 ==> (f' has_integral (f x - f a)) (interval[a,x])`;;

(* ------------------------------------------------------------------------- *)
(* Variation in terms of integral in a more general setting.                 *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTE_INTEGRAL_NORM_DERIVATIVE_LE_VARIATION = `!f:real^1->real^N a b.
      f has_bounded_variation_on interval[a,b]
      ==> ?s f'. negligible s /\
                 (!x. x IN interval[a,b] DIFF s
                      ==> (f has_vector_derivative f' x) (at x)) /\
                 f' absolutely_integrable_on interval[a,b] /\
                 !c. c IN interval[a,b]
                     ==> drop(integral (interval[a,c]) (\x. lift(norm(f' x))))
                         <= vector_variation (interval[a,c]) f`;;

let ABSOLUTE_INTEGRAL_NORM_DERIVATIVE_LE_VARIATION_ALT = `!f:real^1->real^N f' a b s.
        f has_bounded_variation_on interval[a,b] /\
        negligible s /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f' x) (at x within interval[a,b]))
        ==> f' absolutely_integrable_on interval[a,b] /\
            !c. c IN interval[a,b]
                ==> drop(integral (interval[a,c]) (\x. lift(norm(f' x))))
                    <= vector_variation (interval[a,c]) f`;;

let VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE_GEN = `!f:real^1->real^N f' a b s.
        f absolutely_continuous_on interval[a,b] /\
        negligible s /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f' x) (at x within interval[a,b]))
        ==> f' absolutely_integrable_on interval[a,b] /\
            vector_variation (interval[a,b]) f =
            drop(integral (interval[a,b]) (\x. lift(norm(f' x))))`;;

let ABSOLUTELY_CONTINUOUS_VECTOR_VARIATION = `!f:real^1->real^N a b.
       f has_bounded_variation_on interval[a,b] /\
       (\x. lift(vector_variation (interval [a,x]) f))
                absolutely_continuous_on interval[a,b] <=>
       f absolutely_continuous_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Converses to a couple of theorems above: equality holds only if the       *)
(* function concerned is absolutely continuous.                              *)
(* ------------------------------------------------------------------------- *)

let INCREASING_FTC_AE_IMP_ABSOLUTELY_CONTINUOUS = `!f f' a b s.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        negligible s /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f' x) (at x)) /\
        integral (interval[a,b]) f' = f(b) - f(a)
        ==> f absolutely_continuous_on interval[a,b]`;;

let VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE_REV = `!f:real^1->real^N f' a b s.
        f has_bounded_variation_on interval[a,b] /\
        negligible s /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f' x) (at x within interval[a,b])) /\
        vector_variation (interval[a,b]) f =
        drop(integral (interval[a,b]) (\x. lift(norm(f' x))))
        ==> f absolutely_continuous_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Banach-Zarecki and related results.                                       *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE,
    LEBESGUE_MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE,
    ABSOLUTELY_CONTINUOUS_IMP_BANACH_SPROPERTY =
  let lemma1 = `!f:real^1->real^1 s e.
          f absolutely_continuous_on s /\ is_interval s /\ closed s /\ &0 < e
          ==> ?r. &0 < r /\
                  !t. t SUBSET s /\ measurable t /\ measure t < r
                      ==> ?u. IMAGE f t SUBSET u /\
                              measurable u /\ measure u < e` in
  let lemma2 = `!f:real^1->real^1 s e.
          f absolutely_continuous_on s /\ is_interval s /\ &0 < e
          ==> ?r. &0 < r /\
                  !t. t SUBSET s /\ measurable t /\ measure t < r
                      ==> ?u. IMAGE f t SUBSET u /\
                              measurable u /\ measure u < e` in
  let lemma3 = `!f:real^1->real^N s e.
          f absolutely_continuous_on s /\ is_interval s /\ &0 < e
          ==> ?r. &0 < r /\
                  !t. t SUBSET s /\ measurable t /\ measure t < r
                      ==> ?u. IMAGE f t SUBSET u /\
                              measurable u /\ measure u < e` in
  let NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE = `!f:real^1->real^N s t.
          f absolutely_continuous_on s /\ is_interval s /\
          negligible t /\ t SUBSET s
          ==> negligible(IMAGE f t)` in
  let LEBESGUE_MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE = `!f:real^1->real^N s t.
          f absolutely_continuous_on s /\ is_interval s /\
          lebesgue_measurable t /\ t SUBSET s
          ==> lebesgue_measurable(IMAGE f t)` in
  let ABSOLUTELY_CONTINUOUS_IMP_BANACH_SPROPERTY = `!f:real^1->real^N s e.
          f absolutely_continuous_on s /\ is_interval s /\ &0 < e
          ==> ?d. &0 < d /\
                  !t. t SUBSET s /\ measurable t /\ measure t < d
                      ==> measurable(IMAGE f t) /\ measure(IMAGE f t) < e` in
  NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE,
  LEBESGUE_MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE,
  ABSOLUTELY_CONTINUOUS_IMP_BANACH_SPROPERTY;;

let MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE = `!f:real^1->real^N s t.
        f absolutely_continuous_on s /\ is_interval s /\
        measurable t /\ t SUBSET s
        ==> measurable(IMAGE f t)`;;

let BANACH_ZARECKI = `!f:real^1->real^1 a b.
        f absolutely_continuous_on interval[a,b] <=>
        f continuous_on interval[a,b] /\
        f has_bounded_variation_on interval[a,b] /\
        !t. t SUBSET interval[a,b] /\ negligible t ==> negligible(IMAGE f t)`;;

let BANACH_ZARECKI_GEN = `!f:real^1->real^1 s.
        is_interval s /\ bounded s
        ==> (f absolutely_continuous_on s <=>
             f continuous_on s /\
             f has_bounded_variation_on s /\
             !t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))`;;

let ABSOLUTELY_CONTINUOUS_DIFFERENTIABLE_BV_GEN = `!f:real^1->real^N s t.
        is_interval s /\ bounded s /\
        f continuous_on s /\ f has_bounded_variation_on s /\
        COUNTABLE t /\
        (!x. x IN s DIFF t ==> f differentiable (at x within s))
        ==> f absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_DIFFERENTIABLE_BV = `!f:real^1->real^N a b.
        f differentiable_on interval[a,b] /\
        f has_bounded_variation_on interval[a,b]
        ==> f absolutely_continuous_on interval[a,b]`;;

let ABSOLUTELY_CONTINUOUS_ON_COMPOSE = `!f:real^1->real^N g s t.
        is_interval s /\ bounded s /\
        is_interval t /\ bounded t /\
        f absolutely_continuous_on t /\
        g absolutely_continuous_on s /\
        IMAGE g s SUBSET t
        ==> ((f o g) absolutely_continuous_on s <=>
             (f o g) has_bounded_variation_on s)`;;

(* ------------------------------------------------------------------------- *)
(* Converse of baby-Sard and handy corollaries, following Serrin-Varburg.    *)
(* ------------------------------------------------------------------------- *)

let CONVERSE_SARD = `!(f:real^M->real^N) f' s.
        dimindex(:M) = dimindex(:N) /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        negligible(IMAGE f s)
        ==> negligible {x | x IN s /\ rank(matrix(f' x)) = dimindex(:N)}`;;

let CONVERSE_SARD_1 = `!(f:real^1->real^1) f' s.
        (!x. x IN s ==> (f has_vector_derivative f'(x)) (at x within s)) /\
        negligible(IMAGE f s)
        ==> negligible {x | x IN s /\ ~(f'(x) = vec 0)}`;;

let DIFF_CHAIN_WITHIN_EQUAL_AE = `!(f:real^1->real^1) (g:real^1->real^1) f' g' h' s t u v w.
        IMAGE f s SUBSET t /\ negligible u /\ negligible v /\ negligible w /\
        (!n. n SUBSET t /\ negligible n ==> negligible(IMAGE g n)) /\
        (!x. x IN s DIFF u
             ==> (f has_vector_derivative f' x) (at x within s)) /\
        (!y. y IN t DIFF v
             ==> (g has_vector_derivative g' y) (at y within t)) /\
        (!x. x IN s DIFF w
             ==> ((g o f) has_vector_derivative h' x) (at x within s))
        ==> negligible {x | x IN s /\ ~(h' x = drop(f' x) % g'(f x))}`;;

let DIFF_CHAIN_AT_EQUAL_AE = `!(f:real^1->real^1) (g:real^1->real^1) f' g' h' s t u v w.
        IMAGE f s SUBSET t /\ negligible u /\ negligible v /\ negligible w /\
        (!n. n SUBSET t /\ negligible n ==> negligible(IMAGE g n)) /\
        (!x. x IN s DIFF u  ==> (f has_vector_derivative f' x) (at x)) /\
        (!y. y IN t DIFF v ==> (g has_vector_derivative g' y) (at y)) /\
        (!x. x IN s DIFF w ==> ((g o f) has_vector_derivative h' x) (at x))
        ==> negligible {x | x IN s /\ ~(h' x = drop(f' x) % g'(f x))}`;;

let DIFF_CHAIN_WITHIN_AE = `!(f:real^1->real^1) (g:real^1->real^1) f' g' s t u v.
        IMAGE f s SUBSET t /\ negligible u /\ negligible v /\
        (!x. x IN s DIFF u
             ==> (f has_vector_derivative f' x) (at x within s)) /\
        (!y. y IN t DIFF v
             ==> (g has_vector_derivative g' y) (at y within t)) /\
        negligible {x | x IN s /\ f' x = vec 0}
        ==> negligible
             {x | x IN s /\
                  ~(((g o f) has_vector_derivative drop(f' x) % g'(f x))
                    (at x within s))}`;;

let ABSOLUTE_INTEGRAL_SUBSTITUTION = `!(f:real^1->real^N) g g' a b s.
        drop a <= drop b /\
        f absolutely_integrable_on interval[g a,g b] /\
        g absolutely_continuous_on interval[a,b] /\
        negligible s /\
        (!x. x IN interval[a,b] DIFF s
             ==> (g has_vector_derivative g' x) (at x within interval[a,b])) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(g x) <= drop(g y))
        ==> (\x. drop(g' x) % f(g x)) absolutely_integrable_on interval[a,b] /\
            integral (interval[a,b]) (\x. drop(g' x) % f(g x)) =
            integral (interval[g a,g b]) f`;;

(* ------------------------------------------------------------------------- *)
(* Indefinite integral of any gauge integrable function at least has the     *)
(* Luzin N property. Proof (with easy gap fixed up) from Bartle's "A Modern  *)
(* Theory of Integration" Th 14.20, apparently following Dongfu and Shipan:  *)
(* "Henstock integrals and Lusin's condition (N)" in Real Analysis Exchange. *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_IMAGE_INDEFINITE_INTEGRAL = `!f:real^1->real^1 s a b.
        f integrable_on interval[a,b] /\
        negligible s /\ s SUBSET interval[a,b]
        ==> negligible (IMAGE (\c. integral(interval[a,c]) f) s)`;;

(* ------------------------------------------------------------------------- *)
(* More refined ways of deducing increasing/decreasing/constant status       *)
(* from the sign of a derivative that may not hold on a set of exceptions.   *)
(* ------------------------------------------------------------------------- *)

let POSITIVE_AE_DERIVATIVE_IMP_NONDECREASING = `!f f' a b s.
      f continuous_on interval[a,b] /\
      interior(IMAGE f s) = {} /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f' x) (at x) /\ &0 < drop(f' x))
      ==> !x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                ==> drop(f x) <= drop(f y)`;;

let POSITIVE_AE_DERIVATIVE_IMP_INCREASING_LT_GEN = `!f:real^1->real^1 f' a b s.
      f continuous_on interval[a,b] /\
      interior s = {} /\ interior(IMAGE f s) = {} /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f' x) (at x) /\ &0 < drop(f' x))
      ==> !x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                ==> drop(f x) < drop(f y)`;;

let POSITIVE_AE_DERIVATIVE_IMP_INCREASING_LT = `!f:real^1->real^1 f' a b s.
      f absolutely_continuous_on interval[a,b] /\ negligible s /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f' x) (at x) /\ &0 < drop(f' x))
      ==> !x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                ==> drop(f x) < drop(f y)`;;

let POSITIVE_AE_DERIVATIVE_IMP_INCREASING_LE_GEN = `!f:real^1->real^1 f' a b s.
      f continuous_on interval[a,b] /\ negligible(IMAGE f s) /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f' x) (at x) /\ &0 <= drop(f' x))
      ==> !x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                ==> drop(f x) <= drop(f y)`;;

let POSITIVE_AE_DERIVATIVE_IMP_INCREASING_LE = `!f:real^1->real^1 f' a b s.
      f absolutely_continuous_on interval[a,b] /\ negligible s /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f' x) (at x) /\ &0 <= drop(f' x))
      ==> !x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                ==> drop(f x) <= drop(f y)`;;

let ZERO_AE_DERIVATIVE_IMP_CONSTANT_GEN = `!f:real^1->real^1 a b s.
      f continuous_on interval[a,b] /\
      negligible(IMAGE f s) /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative (vec 0)) (at x))
      ==> !x. x IN interval[a,b] ==> f x = f a`;;

let ZERO_AE_DERIVATIVE_IMP_CONSTANT = `!f:real^1->real^1 a b s.
      f absolutely_continuous_on interval[a,b] /\ negligible s /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative (vec 0)) (at x))
      ==> !x. x IN interval[a,b] ==> f x = f a`;;

(* ------------------------------------------------------------------------- *)
(* Convergence in measure implies convergence AE of a subsequence.           *)
(* ------------------------------------------------------------------------- *)

let CONVERGENCE_IN_MEASURE = `!f:num->real^M->real^N g s.
        (!n. f n measurable_on s) /\
        (!e. &0 < e
             ==> eventually
                  (\n. ?t. {x | x IN s /\ dist(f n x,g x) >= e} SUBSET t /\
                           measurable t /\ measure t < e)
                  sequentially)
        ==> ?r t. (!m n:num. m < n ==> r m < r n) /\
                  negligible t /\ t SUBSET s /\
                  !x. x IN s DIFF t
                      ==> ((\n. f (r n) x) --> g x) sequentially`;;

let CONVERGENCE_IN_MEASURE_UNIQUE = `!f:num->real^M->real^N g h s.
        (!n. f n measurable_on s) /\
        (!e. &0 < e
             ==> eventually
                  (\n. ?t. {x | x IN s /\ dist(f n x,g x) >= e} SUBSET t /\
                           measurable t /\ measure t < e)
                  sequentially) /\
        (!e. &0 < e
             ==> eventually
                  (\n. ?t. {x | x IN s /\ dist(f n x,h x) >= e} SUBSET t /\
                           measurable t /\ measure t < e)
                  sequentially)
        ==> negligible {x | x IN s /\ ~(g x = h x)}`;;

(* ------------------------------------------------------------------------- *)
(* Basic path notions for AC paths; these can be useful for working          *)
(* with rectifiable paths where we want to explicitly pick an AC             *)
(* parametrization, e.g. by ARC_LENGTH_REPARAMETRIZATION                     *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_CONTINUOUS_IMP_PATH = `!g:real^1->real^N.
    g absolutely_continuous_on interval[vec 0,vec 1] ==> path g`;;

let ABSOLUTELY_CONTINUOUS_IMP_RECTIFIABLE_PATH = `!g:real^1->real^N.
    g absolutely_continuous_on interval[vec 0,vec 1] ==> rectifiable_path g`;;

let ABSOLUTELY_INTEGRABLE_VECTOR_DERIVATIVE_ABSOLUTELY_CONTINUOUS = `!g:real^1->real^N.
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> (\t. vector_derivative g (at t))
        absolutely_integrable_on interval[vec 0,vec 1]`;;

let ABSOLUTELY_CONTINUOUS_REVERSEPATH = `!g:real^1->real^N.
    g absolutely_continuous_on interval[vec 0,vec 1]
    ==> (reversepath g) absolutely_continuous_on interval[vec 0,vec 1]`;;

let ABSOLUTELY_CONTINUOUS_JOINPATHS = `!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2 /\
        g1 absolutely_continuous_on interval[vec 0,vec 1] /\
        g2 absolutely_continuous_on interval[vec 0,vec 1]
        ==> (g1 ++ g2) absolutely_continuous_on interval[vec 0,vec 1]`;;

(* ------------------------------------------------------------------------- *)
(* Fubini-type results for measure.                                          *)
(* ------------------------------------------------------------------------- *)

let FUBINI_MEASURE = `!s:real^(M,N)finite_sum->bool.
        measurable s
        ==> negligible {x | ~measurable {y | pastecart x y IN s}} /\
            ((\x. lift(measure {y | pastecart x y IN s}))
             has_integral lift(measure s)) UNIV`;;

let FUBINI_MEASURE_ALT = `!s:real^(M,N)finite_sum->bool.
        measurable s
        ==> negligible {y | ~measurable {x | pastecart x y IN s}} /\
            ((\y. lift(measure {x | pastecart x y IN s}))
             has_integral lift(measure s)) UNIV`;;

let FUBINI_LEBESGUE_MEASURABLE = `!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> negligible {x | ~lebesgue_measurable {y | pastecart x y IN s}}`;;

let FUBINI_LEBESGUE_MEASURABLE_ALT = `!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> negligible {y | ~lebesgue_measurable {x | pastecart x y IN s}}`;;

let FUBINI_NEGLIGIBLE = `!s. negligible s
       ==> negligible
            {x:real^M | ~negligible {y:real^N | pastecart x y IN s}}`;;

let FUBINI_NEGLIGIBLE_ALT = `!s. negligible s
       ==> negligible
            {y:real^N | ~negligible {x:real^M | pastecart x y IN s}}`;;

let NEGLIGIBLE_PCROSS = `!s:real^M->bool t:real^N->bool.
        negligible(s PCROSS t) <=> negligible s \/ negligible t`;;

let FUBINI_TONELLI_MEASURE = `!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (measurable s <=>
             negligible {x | ~measurable {y | pastecart x y IN s}} /\
             (\x. lift(measure {y | pastecart x y IN s})) integrable_on UNIV)`;;

let FUBINI_TONELLI_MEASURE_ALT = `!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (measurable s <=>
             negligible {y | ~measurable {x | pastecart x y IN s}} /\
             (\y. lift(measure {x | pastecart x y IN s})) integrable_on UNIV)`;;

let FUBINI_TONELLI_NEGLIGIBLE = `!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (negligible s <=>
             negligible {x | ~negligible {y | pastecart x y IN s}})`;;

let FUBINI_TONELLI_NEGLIGIBLE_ALT = `!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (negligible s <=>
             negligible {y | ~negligible {x | pastecart x y IN s}})`;;

let LEBESGUE_MEASURABLE_PCROSS = `!s:real^M->bool t:real^N->bool.
        lebesgue_measurable(s PCROSS t) <=>
        negligible s \/ negligible t \/
        (lebesgue_measurable s /\ lebesgue_measurable t)`;;

let MEASURABLE_PCROSS = `!s:real^M->bool t:real^N->bool.
        measurable(s PCROSS t) <=>
        negligible s \/ negligible t \/ (measurable s /\ measurable t)`;;

let HAS_MEASURE_PCROSS = `!s:real^M->bool t:real^N->bool a b.
        s has_measure a /\ t has_measure b
        ==> (s PCROSS t) has_measure (a * b)`;;

let MEASURE_PCROSS = `!s:real^M->bool t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s PCROSS t) = measure s * measure t`;;

(* ------------------------------------------------------------------------- *)
(* Relate the measurability of a function and of its ordinate set.           *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE = `!f:real^M->real^N k.
        f measurable_on (:real^M)
        ==> lebesgue_measurable {pastecart x (y:real^N) | y$k <= (f x)$k}`;;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT = `!f:real^M->real^N k.
        f measurable_on (:real^M)
        ==> lebesgue_measurable {pastecart x (y:real^N) | y$k < (f x)$k}`;;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE_EQ = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> lebesgue_measurable
                  {pastecart x (y:real^N) | y$k <= (f x)$k})`
and LEBESGUE_MEASURABLE_FUNCTION_ORTHANT_SET_LE_EQ = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        lebesgue_measurable
          {pastecart x (y:real^N) | !k. 1 <= k /\ k <= dimindex(:N)
                                        ==> y$k <= (f x)$k})`;;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT_EQ = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> lebesgue_measurable
                  {pastecart x (y:real^N) | y$k < (f x)$k})`
and LEBESGUE_MEASURABLE_FUNCTION_ORTHANT_SET_LT_EQ = `(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        lebesgue_measurable
          {pastecart x (y:real^N) | !k. 1 <= k /\ k <= dimindex(:N)
                                        ==> y$k < (f x)$k})`;;

let NEGLIGIBLE_MEASURABLE_FUNCTION_GRAPH = `!f:real^M->real^N.
        f measurable_on (:real^M) ==> negligible {pastecart x y | f x = y}`;;

(* ------------------------------------------------------------------------- *)
(* Hence relate integrals and "area under curve" for functions into R^+.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_IFF_LEBESGUE_MEASURABLE_UNDER_CURVE = `!f:real^N->real^1.
        (!x. &0 <= drop(f x))
        ==> (f measurable_on (:real^N) <=>
             lebesgue_measurable { pastecart x y | y IN interval[vec 0,f x]})`;;

let INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE = `!f:real^N->real^1.
        (!x. &0 <= drop(f x))
        ==> (f integrable_on (:real^N) <=>
             measurable { pastecart x y | y IN interval[vec 0,f x]})`;;

let HAS_INTEGRAL_MEASURE_UNDER_CURVE = `!f:real^N->real^1 m.
        (!x. &0 <= drop(f x))
        ==> ((f has_integral lift m) (:real^N) <=>
             { pastecart x y | y IN interval[vec 0,f x]} has_measure m)`;;

(* ------------------------------------------------------------------------- *)
(* Some miscellanous lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_COMPOSE_FSTCART = `!f:real^M->real^P.
        f measurable_on (:real^M)
        ==> (\z:real^(M,N)finite_sum. f(fstcart z)) measurable_on
            (:real^(M,N)finite_sum)`;;

let MEASURABLE_ON_COMPOSE_SNDCART = `!f:real^N->real^P.
        f measurable_on (:real^N)
        ==> (\z:real^(M,N)finite_sum. f(sndcart z)) measurable_on
            (:real^(M,N)finite_sum)`;;

let MEASURABLE_ON_COMPOSE_SUB = `!f:real^M->real^N.
        f measurable_on (:real^M)
        ==> (\z. f(fstcart z - sndcart z))
            measurable_on (:real^(M,M)finite_sum)`;;

(* ------------------------------------------------------------------------- *)
(* Fubini for absolute integrability.                                        *)
(* ------------------------------------------------------------------------- *)

let FUBINI_ABSOLUTELY_INTEGRABLE = `!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {x | ~((\y. f(pastecart x y))
                     absolutely_integrable_on (:real^N))} /\
            ((\x. integral (:real^N) (\y. f(pastecart x y))) has_integral
             integral (:real^(M,N)finite_sum) f) (:real^M)`;;

let FUBINI_ABSOLUTELY_INTEGRABLE_ALT = `!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {y | ~((\x. f(pastecart x y))
                     absolutely_integrable_on (:real^M))} /\
            ((\y. integral (:real^M) (\x. f(pastecart x y))) has_integral
             integral (:real^(M,N)finite_sum) f) (:real^N)`;;

let FUBINI_INTEGRAL = `!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on UNIV
        ==> integral UNIV f =
            integral UNIV (\x. integral UNIV (\y. f(pastecart x y)))`;;

let FUBINI_INTEGRAL_ALT = `!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on UNIV
        ==> integral UNIV f =
            integral UNIV (\y. integral UNIV (\x. f(pastecart x y)))`;;

let FUBINI_HAS_ABSOLUTE_INTEGRAL = `!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {x | ~((\y. f(pastecart x y))
                     absolutely_integrable_on (:real^N))} /\
            (\x. integral (:real^N) (\y. f(pastecart x y)))
            absolutely_integrable_on (:real^M) /\
            integral (:real^M)
              (\x. integral (:real^N) (\y. f(pastecart x y))) =
            integral (:real^(M,N)finite_sum) f`;;

let FUBINI_HAS_ABSOLUTE_INTEGRAL_ALT = `!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {y | ~((\x. f(pastecart x y))
                     absolutely_integrable_on (:real^M))} /\
            (\y. integral (:real^M) (\x. f(pastecart x y)))
            absolutely_integrable_on (:real^N) /\
            integral (:real^N)
              (\y. integral (:real^M) (\x. f(pastecart x y))) =
            integral (:real^(M,N)finite_sum) f`;;

let FUBINI_INTEGRAL_SWAP = `!f. f absolutely_integrable_on (:real^(M,N)finite_sum)
         ==> integral (:real^M)
                      (\x. integral (:real^N) (\y. f (pastecart x y))):real^P =
             integral (:real^N)
                      (\y. integral (:real^M) (\x. f (pastecart x y)))`;;

let FUBINI_HAS_INTEGRAL_SWAP = `!f. f absolutely_integrable_on (:real^(M,N)finite_sum)
       ==> ((\x. integral (:real^N) (\y. f (pastecart x y))) has_integral
            integral (:real^N)
                     (\y. integral (:real^M) (\x. f (pastecart x y))):real^P)
            (:real^M)`;;

let FUBINI_HAS_INTEGRAL_SWAP_ALT = `!f. f absolutely_integrable_on (:real^(M,N)finite_sum)
       ==> ((\y. integral (:real^M) (\x. f (pastecart x y))) has_integral
            integral (:real^M)
                      (\x. integral (:real^N) (\y. f (pastecart x y))):real^P)
            (:real^N)`;;

let FUBINI_INTEGRAL_INTERVAL = `!f:real^(M,N)finite_sum->real^P a b c d.
        f absolutely_integrable_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[a,b])
                     (\x. integral (interval[c,d])
                                   (\y. f(pastecart x y)))`;;

let FUBINI_INTEGRAL_INTERVAL_ALT = `!f:real^(M,N)finite_sum->real^P a b c d.
        f absolutely_integrable_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[c,d])
                     (\y. integral (interval[a,b])
                                   (\x. f(pastecart x y)))`;;

let INTEGRAL_PASTECART_CONTINUOUS = `!f:real^(M,N)finite_sum->real^P a b c d.
        f continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[a,b])
                     (\x. integral (interval[c,d])
                                   (\y. f(pastecart x y)))`;;

let INTEGRAL_SWAP_CONTINUOUS = `!f:real^M->real^N->real^P a b c d.
        (\z. f (fstcart z) (sndcart z))
        continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[a,b]) (\x. integral (interval[c,d]) (f x)) =
            integral (interval[c,d])
                     (\y. integral (interval[a,b]) (\x. f x y))`;;

let FUBINI_TONELLI = `!f:real^(M,N)finite_sum->real^P.
   f measurable_on (:real^(M,N)finite_sum)
   ==> (f absolutely_integrable_on (:real^(M,N)finite_sum) <=>
        negligible
          {x | ~((\y. f(pastecart x y)) absolutely_integrable_on (:real^N))} /\
        (\x. integral (:real^N) (\y. lift(norm(f(pastecart x y)))))
        integrable_on (:real^M))`;;

let FUBINI_TONELLI_ALT = `!f:real^(M,N)finite_sum->real^P.
   f measurable_on (:real^(M,N)finite_sum)
   ==> (f absolutely_integrable_on (:real^(M,N)finite_sum) <=>
        negligible
          {y | ~((\x. f(pastecart x y)) absolutely_integrable_on (:real^M))} /\
        (\y. integral (:real^M) (\x. lift(norm(f(pastecart x y)))))
        integrable_on (:real^N))`;;

let HAS_DOUBLE_INTEGRAL_PCROSS = `!bop:real^P->real^Q->real^R f:real^M->real^P g:real^N->real^Q s t.
        bilinear bop /\
        f absolutely_integrable_on s /\
        g absolutely_integrable_on t
        ==> ((\z. bop (f(fstcart z)) (g(sndcart z))) has_integral
             bop (integral s f) (integral t g))
            (s PCROSS t)`;;

(* ------------------------------------------------------------------------- *)
(* Some versions of Fubini where we stay in a fixed space R^n.               *)
(* ------------------------------------------------------------------------- *)

let FUBINI_NEGLIGIBLE_REPLACEMENTS = `!k s:real^N->bool.
    lebesgue_measurable s
    ==> (negligible s <=>
         negligible { lift a |
                      ~negligible { x:real^N |
                                (lambda i. if i = k then a else x$i) IN s}})`;;

let FUBINI_NEGLIGIBLE_REPLACEMENTS_ALT = `!k s:real^N->bool.
    lebesgue_measurable s
    ==> (negligible s <=>
         negligible { x:real^N |
                      ~negligible { lift a |
                                (lambda i. if i = k then a else x$i) IN s}})`;;

let FUBINI_NEGLIGIBLE_OFFSET = `!s v:real^N.
        lebesgue_measurable s
        ==> (negligible s <=>
             negligible { x | ~negligible {t | (x + drop t % v) IN s}})`;;

(* ------------------------------------------------------------------------- *)
(* Some basic results about convolution.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_CONVOLUTION_SYM = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P i x.
        ((\y. bop (f(x - y)) (g y)) has_integral i) UNIV <=>
        ((\y. bop (f y) (g(x - y))) has_integral i) UNIV`;;

let INTEGRABLE_CONVOLUTION_SYM = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P x.
        (\y. bop (f(x - y)) (g y)) integrable_on UNIV <=>
        (\y. bop (f y) (g(x - y))) integrable_on UNIV`;;

let INTEGRAL_CONVOLUTION_SYM = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P x.
        integral UNIV (\y. bop (f(x - y)) (g y)) =
        integral UNIV (\y. bop (f y) (g(x - y)))`;;

let ABSOLUTELY_INTEGRABLE_CONVOLUTION_SYM = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P x.
        (\y. bop (f(x - y)) (g y)) absolutely_integrable_on UNIV <=>
        (\y. bop (f y) (g(x - y))) absolutely_integrable_on UNIV`;;

let MEASURABLE_ON_CONVOLUTION = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P x.
        bilinear bop /\ f measurable_on (:real^M) /\ g measurable_on (:real^M)
        ==> (\y. bop (f(x - y)) (g y)) measurable_on (:real^M)`;;

let ABSOLUTELY_INTEGRABLE_CONVOLUTION_AE = `(!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P.
        bilinear bop /\
        f absolutely_integrable_on (:real^M) /\
        g absolutely_integrable_on (:real^M)
        ==> ?t. negligible t /\
                !x. ~(x IN t)
                    ==> (\y. bop (f(x - y)) (g y))
                        absolutely_integrable_on (:real^M))`
and HAS_DOUBLE_INTEGRAL_CONVOLUTION = `(!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P.
        bilinear bop /\
        f absolutely_integrable_on (:real^M) /\
        g absolutely_integrable_on (:real^M)
        ==> ((\x. integral (:real^M) (\y. bop (f(x - y)) (g y))) has_integral
             bop (integral (:real^M) f) (integral (:real^M) g)) (:real^M))`;;

let DOUBLE_INTEGRABLE_CONVOLUTION = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P.
        bilinear bop /\
        f absolutely_integrable_on (:real^M) /\
        g absolutely_integrable_on (:real^M)
        ==> (\x. integral (:real^M) (\y. bop (f(x - y)) (g y)))
            integrable_on (:real^M)`;;

let DOUBLE_INTEGRAL_CONVOLUTION = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P.
        bilinear bop /\
        f absolutely_integrable_on (:real^M) /\
        g absolutely_integrable_on (:real^M)
        ==> integral (:real^M)
                     (\x. integral (:real^M) (\y. bop (f(x - y)) (g y))) =
            bop (integral (:real^M) f) (integral (:real^M) g)`;;

let ABSOLUTELY_INTEGRABLE_CONVOLUTION_L2 = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P x.
        bilinear bop /\
        f measurable_on (:real^M) /\ g measurable_on (:real^M) /\
        (\x. lift(norm(f x) pow 2)) absolutely_integrable_on (:real^M) /\
        (\x. lift(norm(g x) pow 2)) absolutely_integrable_on (:real^M)
        ==> (\y. bop (f(x - y)) (g y)) absolutely_integrable_on (:real^M)`;;

let ABSOLUTELY_INTEGRABLE_CONVOLUTION_L1_LINF = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P x.
        bilinear bop /\
        f absolutely_integrable_on (:real^M) /\
        g measurable_on (:real^M) /\ bounded(IMAGE g (:real^M))
        ==> (\y. bop (f(x - y)) (g y)) absolutely_integrable_on (:real^M)`;;

let ABSOLUTELY_INTEGRABLE_CONVOLUTION_LINF_L1 = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P x.
        bilinear bop /\
        f measurable_on (:real^M) /\ bounded(IMAGE f (:real^M)) /\
        g absolutely_integrable_on (:real^M)
        ==> (\y. bop (f(x - y)) (g y)) absolutely_integrable_on (:real^M)`;;

let CONTINUOUS_ON_CONVOLUTION_L1_LINF = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P.
        bilinear bop /\
        f absolutely_integrable_on (:real^M) /\
        g measurable_on (:real^M) /\ bounded(IMAGE g (:real^M))
        ==> (\x. integral (:real^M) (\y. bop (f(x - y)) (g y)))
            continuous_on (:real^M)`;;

let CONTINUOUS_ON_CONVOLUTION_LINF_L1 = `!bop:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P.
        bilinear bop /\
        f measurable_on (:real^M) /\ bounded(IMAGE f (:real^M)) /\
        g absolutely_integrable_on (:real^M)
        ==> (\x. integral (:real^M) (\y. bop (f(x - y)) (g y)))
            continuous_on (:real^M)`;;

(* ------------------------------------------------------------------------- *)
(* Some Steinhaus variants with two different sets of positive measure.      *)
(* ------------------------------------------------------------------------- *)

let STEINHAUS_SUMS = `!s t:real^N->bool.
        lebesgue_measurable s /\ ~negligible s /\
        lebesgue_measurable t /\ ~negligible t
        ==> ~(interior {x + y | x IN s /\ y IN t} = {})`;;

let STEINHAUS_DIFFS = `!s t:real^N->bool.
        lebesgue_measurable s /\ ~negligible s /\
        lebesgue_measurable t /\ ~negligible t
        ==> ~(interior {x - y | x IN s /\ y IN t} = {})`;;

(* ------------------------------------------------------------------------- *)
(* More refined Ostrowski-style theorems about midpoint convexity.           *)
(* ------------------------------------------------------------------------- *)

let MIDPOINT_CONVEX_IMP_CONTINUOUS_OSTROWSKI = `!f:real^N->real s t B.
        convex s /\ open s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint (x,y)) <= (f x + f y) / &2) /\
        t SUBSET s /\ lebesgue_measurable t /\ ~negligible t /\
        (!x. x IN t ==> f x <= B)
        ==> (lift o f) continuous_on s`;;

let MIDPOINT_CONVEX_IMP_CONVEX_OSTROWSKI = `!f:real^N->real s t B.
        convex s /\ open s /\
        t SUBSET s /\ lebesgue_measurable t /\ ~negligible t /\
        (!x y. x IN s /\ y IN s ==> f(midpoint (x,y)) <= (f x + f y) / &2) /\
        (!x. x IN t ==> f x <= B)
        ==> f convex_on s`;;

let MEASURABLE_MIDPOINT_CONVEX_IMP_CONTINUOUS = `!f:real^N->real s.
        (lift o f) measurable_on s /\ open s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint (x,y)) <= (f x + f y) / &2)
        ==> (lift o f) continuous_on s`;;

let MEASURABLE_MIDPOINT_CONVEX_IMP_CONVEX_GEN = `!f:real^N->real s.
        (lift o f) measurable_on s /\ convex s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint (x,y)) <= (f x + f y) / &2)
        ==> !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1 /\
                      (segment[x,y] SUBSET frontier s ==> x = y)
                      ==> f (u % x + v % y) <= u * f x + v * f y`;;

let MEASURABLE_MIDPOINT_CONVEX_IMP_CONVEX_OPEN = `!f:real^N->real s.
        (lift o f) measurable_on s /\ convex s /\ open s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint (x,y)) <= (f x + f y) / &2)
        ==> f convex_on s`;;

let MEASURABLE_MIDPOINT_CONVEX_IMP_CONVEX_1D = `!f:real^1->real s.
        (lift o f) measurable_on s /\ convex s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint (x,y)) <= (f x + f y) / &2)
        ==> f convex_on s`;;

let MEASURABLE_MIDPOINT_CONVEX_IMP_CONVEX_CBALL = `!f:real^N->real a r.
        (lift o f) measurable_on cball(a,r) /\
        (!x y. x IN cball(a,r) /\ y IN cball(a,r)
               ==> f(midpoint (x,y)) <= (f x + f y) / &2)
        ==> f convex_on cball(a,r)`;;

let OSTROWSKI_THEOREM = `!f:real^M->real^N B s.
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!x. x IN s ==> norm(f x) <= B) /\
        measurable s /\ &0 < measure s
        ==> linear f`;;

let MEASURABLE_ADDITIVE_IMP_LINEAR = `!f:real^M->real^N.
        f measurable_on (:real^M) /\ (!x y. f(x + y) = f(x) + f(y))
        ==> linear f`;;

let CONTINUOUS_ADDITIVE_IMP_LINEAR = `!f:real^M->real^N.
        f continuous_on (:real^M) /\
        (!x y. f(x + y) = f(x) + f(y))
        ==> linear f`;;

(* ------------------------------------------------------------------------- *)
(* Rademacher's theorem (the "simple proof" from Nekvinda and Zajicek).      *)
(* ------------------------------------------------------------------------- *)

let RADEMACHER_UNIV = `!f:real^M->real^N.
        (?B. !x y. norm(f x - f y) <= B * norm(x - y))
        ==> negligible {x | ~(f differentiable at x)}`;;

let RADEMACHER = `!f:real^M->real^N s.
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> negligible {x | x IN s /\ ~(f differentiable (at x within s))}`;;

let RADEMACHER_OPEN = `!f:real^M->real^N s.
        open s /\
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> negligible {x | x IN s /\ ~(f differentiable (at x))}`;;

let RADEMACHER_GEN = `!f:real^M->real^N s.
        negligible(frontier s) /\
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> negligible {x | x IN s /\ ~(f differentiable (at x))}`;;

(* ------------------------------------------------------------------------- *)
(* Stepanov's theorem (Maly's proof, slightly generalized by localization).  *)
(* ------------------------------------------------------------------------- *)

let STEPANOV_GEN = `!f:real^M->real^N s.
        lebesgue_measurable s
        ==> negligible
            {x | x IN s /\
                 (?B. eventually (\y. norm(f x - f y) / norm(x - y) <= B)
                                 (at x within s)) /\
                 ~(f differentiable at x within s)}`;;

let STEPANOV = `!f:real^M->real^N s.
     open s
     ==> negligible
         {x | x IN s /\
              (?B. eventually
                      (\y. norm(f x - f y) / norm(x - y) <= B) (at x)) /\
              ~(f differentiable at x)}`;;

let STEPANOV_UNIV = `!f:real^M->real^N.
        negligible
         {x | (?B. eventually
                      (\y. norm(f x - f y) / norm(x - y) <= B) (at x)) /\
              ~(f differentiable at x)}`;;
