(* ========================================================================= *)
(* Kurzweil-Henstock gauge integration in many dimensions.                   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "Library/floor.ml";;
needs "Multivariate/derivatives.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Some useful lemmas about intervals.                                       *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_SUBSET_UNION_INTERVALS = `!s i j. (?a b:real^N. i = interval[a,b]) /\ (?c d. j = interval[c,d]) /\
           ~(interior j = {}) /\
           i SUBSET j UNION s /\
           interior(i) INTER interior(j) = {}
           ==> interior i SUBSET interior s`;;

let INTER_INTERIOR_UNIONS_INTERVALS = `!s f. FINITE f /\ open s /\
         (!t. t IN f ==> ?a b:real^N. t = interval[a,b]) /\
         (!t. t IN f ==> s INTER (interior t) = {})
         ==> s INTER interior(UNIONS f) = {}`;;

(* ------------------------------------------------------------------------- *)
(* This lemma about iterations comes up in a few places.                     *)
(* ------------------------------------------------------------------------- *)

let ITERATE_NONZERO_IMAGE_LEMMA = `!op s f g a.
      monoidal op /\ FINITE s /\
      g(a) = neutral op /\
      (!x y. x IN s /\ y IN s /\ f x = f y /\ ~(x = y) ==> g(f x) = neutral op)
      ==> iterate op {f x | x | x IN s /\ ~(f x = a)} g =
          iterate op s (g o f)`;;

(* ------------------------------------------------------------------------- *)
(* Bounds on intervals where they exist.                                     *)
(* ------------------------------------------------------------------------- *)

let interval_upperbound = new_definition
  `(interval_upperbound:(real^M->bool)->real^M) s =
        lambda i. sup {a | ?x. x IN s /\ (x$i = a)}`;;

let interval_lowerbound = new_definition
  `(interval_lowerbound:(real^M->bool)->real^M) s =
        lambda i. inf {a | ?x. x IN s /\ (x$i = a)}`;;

let INTERVAL_UPPERBOUND = `!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> interval_upperbound(interval[a,b]) = b`;;

let INTERVAL_LOWERBOUND = `!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> interval_lowerbound(interval[a,b]) = a`;;

let INTERVAL_UPPERBOUND_1 = `!a b. drop a <= drop b ==> interval_upperbound(interval[a,b]) = b`;;

let INTERVAL_LOWERBOUND_1 = `!a b. drop a <= drop b ==> interval_lowerbound(interval[a,b]) = a`;;

let INTERVAL_LOWERBOUND_NONEMPTY = `!a b:real^N.
    ~(interval[a,b] = {}) ==> interval_lowerbound(interval[a,b]) = a`;;

let INTERVAL_UPPERBOUND_NONEMPTY = `!a b:real^N.
    ~(interval[a,b] = {}) ==> interval_upperbound(interval[a,b]) = b`;;

(* ------------------------------------------------------------------------- *)
(* Content (length, area, volume...) of an interval.                         *)
(* ------------------------------------------------------------------------- *)

let content = new_definition
   `content(s:real^M->bool) =
       if s = {} then &0 else
       product(1..dimindex(:M))
              (\i. (interval_upperbound s)$i - (interval_lowerbound s)$i)`;;

let CONTENT_CLOSED_INTERVAL = `!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> content(interval[a,b]) =
                        product(1..dimindex(:N)) (\i. b$i - a$i)`;;

let CONTENT_1 = `!a b. drop a <= drop b ==> content(interval[a,b]) = drop b - drop a`;;

let CONTENT_UNIT = `content(interval[vec 0:real^N,vec 1]) = &1`;;

let CONTENT_UNIT_1 = `content(interval[vec 0:real^1,vec 1]) = &1`;;

let CONTENT_POS_LE = `!a b:real^N. &0 <= content(interval[a,b])`;;

let CONTENT_POS_LT = `!a b:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i)
        ==> &0 < content(interval[a,b])`;;

let CONTENT_POS_LT_1 = `!a b. drop a < drop b ==> &0 < content(interval[a,b])`;;

let CONTENT_EQ_0_GEN = `!s:real^N->bool.
     bounded s
     ==> (content s = &0 <=>
          ?i a. 1 <= i /\ i <= dimindex(:N) /\ !x. x IN s ==> x$i = a)`;;

let CONTENT_EQ_0 = `!a b:real^N.
        content(interval[a,b]) = &0 <=>
        ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i <= a$i`;;

let CONTENT_0_SUBSET_GEN = `!s t:real^N->bool.
      s SUBSET t /\ bounded t /\ content t = &0 ==> content s = &0`;;

let CONTENT_0_SUBSET = `!s a b:real^N.
        s SUBSET interval[a,b] /\ content(interval[a,b]) = &0
        ==> content s = &0`;;

let CONTENT_CLOSED_INTERVAL_CASES = `!a b:real^N.
        content(interval[a,b]) =
                if !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i
                then product(1..dimindex(:N)) (\i. b$i - a$i)
                else &0`;;

let CONTENT_EQ_0_INTERIOR = `!a b:real^N.
        content(interval[a,b]) = &0 <=> interior(interval[a,b]) = {}`;;

let CONTENT_EQ_0_1 = `!a b:real^1.
        content(interval[a,b]) = &0 <=> drop b <= drop a`;;

let CONTENT_POS_LT_EQ = `!a b:real^N.
        &0 < content(interval[a,b]) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i`;;

let CONTENT_EMPTY = `content {} = &0`;;

let CONTENT_SUBSET = `!a b c d:real^N.
        interval[a,b] SUBSET interval[c,d]
        ==> content(interval[a,b]) <= content(interval[c,d])`;;

let CONTENT_LT_NZ = `!a b. &0 < content(interval[a,b]) <=> ~(content(interval[a,b]) = &0)`;;

let INTERVAL_BOUNDS_NULL_1 = `!a b:real^1.
        content(interval[a,b]) = &0
        ==> interval_upperbound(interval[a,b]) =
            interval_lowerbound(interval[a,b])`;;

let INTERVAL_BOUNDS_EMPTY_1 = `interval_upperbound({}:real^1->bool) =
   interval_lowerbound({}:real^1->bool)`;;

let CONTENT_PASTECART = `!a b:real^M c d:real^N.
        content(interval[pastecart a c,pastecart b d]) =
        content(interval[a,b]) * content(interval[c,d])`;;

(* ------------------------------------------------------------------------- *)
(* The notion of a gauge --- simply an open set containing the point.        *)
(* ------------------------------------------------------------------------- *)

let gauge = new_definition
  `gauge d <=> !x. x IN d(x) /\ open(d(x))`;;

let GAUGE_BALL_DEPENDENT = `!e. (!x. &0 < e(x)) ==> gauge(\x. ball(x,e(x)))`;;

let GAUGE_BALL = `!e. &0 < e ==> gauge (\x. ball(x,e))`;;

let GAUGE_TRIVIAL = `gauge (\x. ball(x,&1))`;;

let GAUGE_INTER = `!d1 d2. gauge d1 /\ gauge d2 ==> gauge (\x. (d1 x) INTER (d2 x))`;;

let GAUGE_INTERS = `!s. FINITE s /\ (!d. d IN s ==> gauge (f d))
       ==> gauge(\x. INTERS {f d x | d IN s})`;;

let GAUGE_EXISTENCE_LEMMA = `(!x. ?d. p x ==> &0 < d /\ q d x) <=>
   (!x. ?d. &0 < d /\ (p x ==> q d x))`;;

(* ------------------------------------------------------------------------- *)
(* Divisions.                                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("division_of",(12,"right"));;

let division_of = new_definition
 `s division_of i <=>
        FINITE s /\
        (!k. k IN s
             ==> k SUBSET i /\ ~(k = {}) /\ ?a b. k = interval[a,b]) /\
        (!k1 k2. k1 IN s /\ k2 IN s /\ ~(k1 = k2)
                 ==> interior(k1) INTER interior(k2) = {}) /\
        (UNIONS s = i)`;;

let DIVISION_OF = `s division_of i <=>
        FINITE s /\
        (!k. k IN s ==> ~(k = {}) /\ ?a b. k = interval[a,b]) /\
        (!k1 k2. k1 IN s /\ k2 IN s /\ ~(k1 = k2)
                 ==> interior(k1) INTER interior(k2) = {}) /\
        UNIONS s = i`;;

let DIVISION_OF_FINITE = `!s i. s division_of i ==> FINITE s`;;

let DIVISION_OF_SELF = `!a b. ~(interval[a,b] = {}) ==> {interval[a,b]} division_of interval[a,b]`;;

let DIVISION_OF_TRIVIAL = `!s. s division_of {} <=> s = {}`;;

let EMPTY_DIVISION_OF = `!s. {} division_of s <=> s = {}`;;

let DIVISION_OF_SING = `!s a. s division_of interval[a,a] <=> s = {interval[a,a]}`;;

let ELEMENTARY_EMPTY = `?p. p division_of {}`;;

let ELEMENTARY_INTERVAL = `!a b. ?p. p division_of interval[a,b]`;;

let DIVISION_CONTAINS = `!s i. s division_of i ==> !x. x IN i ==> ?k. x IN k /\ k IN s`;;

let FORALL_IN_DIVISION = `!P d i. d division_of i
           ==> ((!x. x IN d ==> P x) <=>
               (!a b. interval[a,b] IN d ==> P(interval[a,b])))`;;

let FORALL_IN_DIVISION_NONEMPTY = `!P d i.
         d division_of i
         ==> ((!x. x IN d ==> P x) <=>
              (!a b. interval [a,b] IN d /\ ~(interval[a,b] = {})
                     ==> P (interval [a,b])))`;;

let DIVISION_OF_SUBSET = `!p q:(real^N->bool)->bool.
        p division_of (UNIONS p) /\ q SUBSET p ==> q division_of (UNIONS q)`;;

let DIVISION_OF_UNION_SELF = `!p s. p division_of s ==> p division_of (UNIONS p)`;;

let DIVISION_OF_CONTENT_0 = `!a b d. content(interval[a,b]) = &0 /\ d division_of interval[a,b]
           ==> !k. k IN d ==> content k = &0`;;

let DIVISION_INTER = `!s1 s2:real^N->bool p1 p2.
        p1 division_of s1 /\
        p2 division_of s2
        ==> {k1 INTER k2 | k1 IN p1 /\ k2 IN p2 /\ ~(k1 INTER k2 = {})}
            division_of (s1 INTER s2)`;;

let DIVISION_INTER_1 = `!d i a b:real^N.
        d division_of i /\ interval[a,b] SUBSET i
        ==> { interval[a,b] INTER k | k |
                 k IN d /\ ~(interval[a,b] INTER k = {}) }
            division_of interval[a,b]`;;

let ELEMENTARY_INTER = `!s t. (?p. p division_of s) /\ (?p. p division_of t)
         ==> ?p. p division_of (s INTER t)`;;

let ELEMENTARY_INTERS = `!f:(real^N->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s. s IN f ==> ?p. p division_of s)
        ==> ?p. p division_of (INTERS f)`;;

let DIVISION_DISJOINT_UNION = `!s1 s2:real^N->bool p1 p2.
        p1 division_of s1 /\
        p2 division_of s2 /\
        interior s1 INTER interior s2 = {}
        ==> (p1 UNION p2) division_of (s1 UNION s2)`;;

let PARTIAL_DIVISION_EXTEND_1 = `!a b c d:real^N.
        interval[c,d] SUBSET interval[a,b] /\ ~(interval[c,d] = {})
        ==> ?p. p division_of interval[a,b] /\
                interval[c,d] IN p`;;

let PARTIAL_DIVISION_EXTEND_INTERVAL = `!p a b:real^N.
        p division_of (UNIONS p) /\ (UNIONS p) SUBSET interval[a,b]
        ==> ?q. p SUBSET q /\ q division_of interval[a,b]`;;

let ELEMENTARY_BOUNDED = `!s. (?p. p division_of s) ==> bounded s`;;

let ELEMENTARY_SUBSET_INTERVAL = `!s. (?p. p division_of s) ==> ?a b. s SUBSET interval[a,b]`;;

let DIVISION_UNION_INTERVALS_EXISTS = `!a b c d:real^N.
        ~(interval[a,b] = {})
        ==> ?p. (interval[a,b] INSERT p) division_of
                (interval[a,b] UNION interval[c,d])`;;

let DIVISION_OF_UNIONS = `!f. FINITE f /\
       (!p. p IN f ==> p division_of (UNIONS p)) /\
       (!k1 k2. k1 IN UNIONS f /\ k2 IN UNIONS f /\ ~(k1 = k2)
                ==> interior k1 INTER interior k2 = {})
       ==> (UNIONS f) division_of UNIONS(UNIONS f)`;;

let ELEMENTARY_UNION_INTERVAL_STRONG = `!p a b:real^N.
        p division_of (UNIONS p)
        ==> ?q. p SUBSET q /\ q division_of (interval[a,b] UNION UNIONS p)`;;

let ELEMENTARY_UNION_INTERVAL = `!p a b:real^N.
        p division_of (UNIONS p)
        ==> ?q. q division_of (interval[a,b] UNION UNIONS p)`;;

let ELEMENTARY_UNIONS_INTERVALS = `!f. FINITE f /\
       (!s. s IN f ==> ?a b:real^N. s = interval[a,b])
       ==> (?p. p division_of (UNIONS f))`;;

let ELEMENTARY_UNION = `!s t:real^N->bool.
        (?p. p division_of s) /\ (?p. p division_of t)
        ==> (?p. p division_of (s UNION t))`;;

let PARTIAL_DIVISION_EXTEND = `!p q s t:real^N->bool.
        p division_of s /\ q division_of t /\ s SUBSET t
        ==> ?r. p SUBSET r /\ r division_of t`;;

let INTERVAL_SUBDIVISION = `!a b c:real^N.
        c IN interval[a,b]
        ==> IMAGE (\s. interval[(lambda i. if i IN s then c$i else a$i),
                                (lambda i. if i IN s then b$i else c$i)])
                  {s | s SUBSET 1..dimindex(:N)}
            division_of interval[a,b]`;;

let DIVISION_OF_NONTRIVIAL = `!s a b:real^N.
        s division_of interval[a,b] /\ ~(content(interval[a,b]) = &0)
        ==> {k | k IN s /\ ~(content k = &0)} division_of interval[a,b]`;;

let DIVISION_OF_AFFINITY = `!d s:real^N->bool m c.
    IMAGE (IMAGE (\x. m % x + c)) d division_of (IMAGE (\x. m % x + c) s) <=>
    if m = &0 then if s = {} then d = {}
                   else ~(d = {}) /\ !k. k IN d ==> ~(k = {})
    else d division_of s`;;

let DIVISION_OF_TRANSLATION = `!d s:real^N->bool.
        IMAGE (IMAGE (\x. a + x)) d division_of (IMAGE (\x. a + x) s) <=>
        d division_of s`;;

let DIVISION_OF_REFLECT = `!d s:real^N->bool.
        IMAGE (IMAGE (--)) d division_of IMAGE (--) s <=>
        d division_of s`;;

let ELEMENTARY_COMPACT = `!s. (?d. d division_of s) ==> compact s`;;

let OPEN_COUNTABLE_LIMIT_ELEMENTARY = `!s:real^N->bool.
        open s
        ==> ?f. (!n. ?d. d division_of f n) /\
                (!n. f n SUBSET f(SUC n)) /\
                UNIONS {f n | n IN (:num)} = s`;;

let DIVISION_1_SORT = `!d s:real^1->bool.
        d division_of s /\
        (!k. k IN d ==> ~(interior k = {}))
        ==> ?n t. IMAGE t (1..n) = d /\
                  !i j. i IN 1..n /\ j IN 1..n /\ i < j
                        ==> ~(t i = t j) /\
                            !x y.  x IN t i /\ y IN t j ==> drop x <= drop y`;;

(* ------------------------------------------------------------------------- *)
(* Tagged (partial) divisions.                                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("tagged_partial_division_of",(12,"right"));;
parse_as_infix("tagged_division_of",(12,"right"));;

let tagged_partial_division_of = new_definition
  `s tagged_partial_division_of i <=>
        FINITE s /\
        (!x k. (x,k) IN s
               ==> x IN k /\ k SUBSET i /\ ?a b. k = interval[a,b]) /\
        (!x1 k1 x2 k2. (x1,k1) IN s /\ (x2,k2) IN s /\ ~((x1,k1) = (x2,k2))
                       ==> (interior(k1) INTER interior(k2) = {}))`;;

let tagged_division_of = new_definition
  `s tagged_division_of i <=>
        s tagged_partial_division_of i /\ (UNIONS {k | ?x. (x,k) IN s} = i)`;;

let TAGGED_DIVISION_OF_FINITE = `!s i. s tagged_division_of i ==> FINITE s`;;

let TAGGED_DIVISION_OF = `s tagged_division_of i <=>
        FINITE s /\
        (!x k. (x,k) IN s
               ==> x IN k /\ k SUBSET i /\ ?a b. k = interval[a,b]) /\
        (!x1 k1 x2 k2. (x1,k1) IN s /\ (x2,k2) IN s /\ ~((x1,k1) = (x2,k2))
                       ==> (interior(k1) INTER interior(k2) = {})) /\
        (UNIONS {k | ?x. (x,k) IN s} = i)`;;

let DIVISION_OF_TAGGED_DIVISION = `!s i. s tagged_division_of i ==> (IMAGE SND s) division_of i`;;

let PARTIAL_DIVISION_OF_TAGGED_DIVISION = `!s i. s tagged_partial_division_of i
         ==> (IMAGE SND s) division_of UNIONS(IMAGE SND s)`;;

let TAGGED_PARTIAL_DIVISION_SUBSET = `!s t i. s tagged_partial_division_of i /\ t SUBSET s
           ==> t tagged_partial_division_of i`;;

let VSUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA = `!d:(real^M->bool)->real^N p i.
        p tagged_partial_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = vec 0)
        ==> vsum p (\(x,k). d k) = vsum (IMAGE SND p) d`;;

let VSUM_OVER_TAGGED_DIVISION_LEMMA = `!d:(real^M->bool)->real^N p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = vec 0)
        ==> vsum p (\(x,k). d k) = vsum (IMAGE SND p) d`;;

let SUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA = `!d:(real^N->bool)->real p i.
        p tagged_partial_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = &0)
        ==> sum p (\(x,k). d k) = sum (IMAGE SND p) d`;;

let SUM_OVER_TAGGED_DIVISION_LEMMA = `!d:(real^N->bool)->real p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = &0)
        ==> sum p (\(x,k). d k) = sum (IMAGE SND p) d`;;

let TAG_IN_INTERVAL = `!p i k. p tagged_division_of i /\ (x,k) IN p ==> x IN i`;;

let TAGGED_DIVISION_OF_EMPTY = `{} tagged_division_of {}`;;

let TAGGED_PARTIAL_DIVISION_OF_TRIVIAL = `!p. p tagged_partial_division_of {} <=> p = {}`;;

let TAGGED_DIVISION_OF_TRIVIAL = `!p. p tagged_division_of {} <=> p = {}`;;

let TAGGED_DIVISION_OF_SELF = `!x a b. x IN interval[a,b]
           ==> {(x,interval[a,b])} tagged_division_of interval[a,b]`;;

let TAGGED_DIVISION_UNION = `!s1 s2:real^N->bool p1 p2.
        p1 tagged_division_of s1 /\
        p2 tagged_division_of s2 /\
        interior s1 INTER interior s2 = {}
        ==> (p1 UNION p2) tagged_division_of (s1 UNION s2)`;;

let TAGGED_DIVISION_UNIONS = `!iset pfn. FINITE iset /\
              (!i:real^M->bool. i IN iset ==> pfn(i) tagged_division_of i) /\
              (!i1 i2. i1 IN iset /\ i2 IN iset /\ ~(i1 = i2)
                       ==> (interior(i1) INTER interior(i2) = {}))
              ==> UNIONS(IMAGE pfn iset) tagged_division_of (UNIONS iset)`;;

let TAGGED_PARTIAL_DIVISION_OF_UNION_SELF = `!p s. p tagged_partial_division_of s
         ==> p tagged_division_of (UNIONS(IMAGE SND p))`;;

let TAGGED_DIVISION_OF_UNION_SELF = `!p s. p tagged_division_of s
         ==> p tagged_division_of (UNIONS(IMAGE SND p))`;;

let TAGGED_DIVISION_UNION_IMAGE_SND = `!p s. p tagged_division_of s ==> s = UNIONS(IMAGE SND p)`;;

let TAGGED_DIVISION_OF_ALT = `!p s. p tagged_division_of s <=>
         p tagged_partial_division_of s /\
         (!x. x IN s ==> ?t k. (t,k) IN p /\ x IN k)`;;

let TAGGED_DIVISION_OF_ANOTHER = `!p s s'.
        p tagged_partial_division_of s' /\
        (!t k. (t,k) IN p ==> k SUBSET s) /\
        (!x. x IN s ==> ?t k. (t,k) IN p /\ x IN k)
        ==> p tagged_division_of s`;;

let TAGGED_PARTIAL_DIVISION_OF_SUBSET = `!p s t. p tagged_partial_division_of s /\ s SUBSET t
           ==> p tagged_partial_division_of t`;;

let TAGGED_DIVISION_OF_NONTRIVIAL = `!s a b:real^N.
        s tagged_division_of interval[a,b] /\ ~(content(interval[a,b]) = &0)
        ==> {(x,k) | (x,k) IN s /\ ~(content k = &0)}
            tagged_division_of interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Fine-ness of a partition w.r.t. a gauge.                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("fine",(12,"right"));;

let fine = new_definition
  `d fine s <=> !x k. (x,k) IN s ==> k SUBSET d(x)`;;

let FINE_INTER = `!p d1 d2. (\x. d1(x) INTER d2(x)) fine p <=> d1 fine p /\ d2 fine p`;;

let FINE_INTERS = `!f s p. (\x. INTERS {f d x | d IN s}) fine p <=>
           !d. d IN s ==> (f d) fine p`;;

let FINE_UNION = `!d p1 p2. d fine p1 /\ d fine p2 ==> d fine (p1 UNION p2)`;;

let FINE_UNIONS = `!d ps. (!p. p IN ps ==> d fine p) ==> d fine (UNIONS ps)`;;

let FINE_SUBSET = `!d p q. p SUBSET q /\ d fine q ==> d fine p`;;

(* ------------------------------------------------------------------------- *)
(* Gauge integral. Define on compact intervals first, then use a limit.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_integral_compact_interval",(12,"right"));;
parse_as_infix("has_integral",(12,"right"));;
parse_as_infix("integrable_on",(12,"right"));;

let has_integral_compact_interval = new_definition
  `(f has_integral_compact_interval y) i <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p. p tagged_division_of i /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) - y) < e`;;

let has_integral_def = new_definition
  `(f has_integral y) i <=>
        if ?a b. i = interval[a,b] then (f has_integral_compact_interval y) i
        else !e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball(vec 0,B) SUBSET interval[a,b]
                               ==> ?z. ((\x. if x IN i then f(x) else vec 0)
                                        has_integral_compact_interval z)
                                        (interval[a,b]) /\
                                       norm(z - y) < e`;;

let has_integral = `(f has_integral y) (interval[a,b]) <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p. p tagged_division_of interval[a,b] /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) - y) < e`;;

let has_integral_alt = `(f has_integral y) i <=>
        if ?a b. i = interval[a,b] then (f has_integral y) i
        else !e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball(vec 0,B) SUBSET interval[a,b]
                               ==> ?z. ((\x. if x IN i then f(x) else vec 0)
                                        has_integral z) (interval[a,b]) /\
                                       norm(z - y) < e`;;

let integrable_on = new_definition
 `f integrable_on i <=> ?y. (f has_integral y) i`;;

let integral = new_definition
 `integral i f = @y. (f has_integral y) i`;;

let INTEGRABLE_INTEGRAL = `!f i. f integrable_on i ==> (f has_integral (integral i f)) i`;;

let HAS_INTEGRAL_INTEGRABLE = `!f i s. (f has_integral i) s ==> f integrable_on s`;;

let HAS_INTEGRAL_INTEGRAL = `!f s. f integrable_on s <=> (f has_integral (integral s f)) s`;;

let VSUM_CONTENT_NULL = `!f:real^M->real^N a b p.
        content(interval[a,b]) = &0 /\
        p tagged_division_of interval[a,b]
        ==> vsum p (\(x,k). content k % f x) = vec 0`;;

(* ------------------------------------------------------------------------- *)
(* Some basic combining lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_UNIONS_EXISTS = `!d iset i:real^M->bool.
        FINITE iset /\
        (!i. i IN iset ==> ?p. p tagged_division_of i /\ d fine p) /\
        (!i1 i2. i1 IN iset /\ i2 IN iset /\ ~(i1 = i2)
                 ==> (interior(i1) INTER interior(i2) = {})) /\
        (UNIONS iset = i)
        ==> ?p. p tagged_division_of i /\ d fine p`;;

(* ------------------------------------------------------------------------- *)
(* The set we're concerned with must be closed.                              *)
(* ------------------------------------------------------------------------- *)

let DIVISION_OF_CLOSED = `!s i. s division_of i ==> closed i`;;

(* ------------------------------------------------------------------------- *)
(* General bisection principle for intervals; might be useful elsewhere.     *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_BISECTION_STEP = `!P. P {} /\
       (!s t. P s /\ P t /\ interior(s) INTER interior(t) = {}
              ==> P(s UNION t))
       ==> !a b:real^N.
                ~(P(interval[a,b]))
                ==> ?c d. ~(P(interval[c,d])) /\
                          !i. 1 <= i /\ i <= dimindex(:N)
                              ==> a$i <= c$i /\ c$i <= d$i /\ d$i <= b$i /\
                                  &2 * (d$i - c$i) <= b$i - a$i`;;

let INTERVAL_BISECTION = `!P. P {} /\
       (!s t. P s /\ P t /\ interior(s) INTER interior(t) = {}
              ==> P(s UNION t))
       ==> !a b:real^N.
                ~(P(interval[a,b]))
                ==> ?x. x IN interval[a,b] /\
                        !e. &0 < e
                            ==> ?c d. x IN interval[c,d] /\
                                      interval[c,d] SUBSET ball(x,e) /\
                                      interval[c,d] SUBSET interval[a,b] /\
                                      ~P(interval[c,d])`;;

(* ------------------------------------------------------------------------- *)
(* Cousin's lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let FINE_DIVISION_EXISTS = `!g a b:real^M.
        gauge g ==> ?p. p tagged_division_of (interval[a,b]) /\ g fine p`;;

(* ------------------------------------------------------------------------- *)
(* Basic theorems about integrals.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_UNIQUE = `!f:real^M->real^N i k1 k2.
        (f has_integral k1) i /\ (f has_integral k2) i ==> k1 = k2`;;

let INTEGRAL_UNIQUE = `!f y k.
      (f has_integral y) k ==> integral k f = y`;;

let HAS_INTEGRAL_INTEGRABLE_INTEGRAL = `!f:real^M->real^N i s.
        (f has_integral i) s <=> f integrable_on s /\ integral s f = i`;;

let INTEGRAL_EQ_HAS_INTEGRAL = `!s f y. f integrable_on s ==> (integral s f = y <=> (f has_integral y) s)`;;

let HAS_INTEGRAL_IS_0 = `!f:real^M->real^N s.
        (!x. x IN s ==> (f(x) = vec 0)) ==> (f has_integral vec 0) s`;;

let HAS_INTEGRAL_0 = `!s. ((\x. vec 0) has_integral vec 0) s`;;

let HAS_INTEGRAL_0_EQ = `!i s. ((\x. vec 0) has_integral i) s <=> i = vec 0`;;

let HAS_INTEGRAL_LINEAR = `!f:real^M->real^N y s h:real^N->real^P.
        (f has_integral y) s /\ linear h ==> ((h o f) has_integral h(y)) s`;;

let HAS_INTEGRAL_CMUL = `!(f:real^M->real^N) k s c.
        (f has_integral k) s
        ==> ((\x. c % f(x)) has_integral (c % k)) s`;;

let HAS_INTEGRAL_NEG = `!f k s. (f has_integral k) s ==> ((\x. --(f x)) has_integral (--k)) s`;;

let HAS_INTEGRAL_ADD = `!f:real^M->real^N g s.
        (f has_integral k) s /\ (g has_integral l) s
        ==> ((\x. f(x) + g(x)) has_integral (k + l)) s`;;

let HAS_INTEGRAL_SUB = `!f:real^M->real^N g s.
        (f has_integral k) s /\ (g has_integral l) s
        ==> ((\x. f(x) - g(x)) has_integral (k - l)) s`;;

let INTEGRAL_0 = `!s. integral s (\x. vec 0) = vec 0`;;

let INTEGRAL_ADD = `!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> integral s (\x. f x + g x) = integral s f + integral s g`;;

let INTEGRAL_CMUL = `!f:real^M->real^N c s.
        f integrable_on s ==> integral s (\x. c % f(x)) = c % integral s f`;;

let INTEGRAL_NEG = `!f:real^M->real^N s.
        f integrable_on s ==> integral s (\x. --f(x)) = --integral s f`;;

let INTEGRAL_SUB = `!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> integral s (\x. f x - g x) = integral s f - integral s g`;;

let INTEGRABLE_0 = `!s. (\x. vec 0) integrable_on s`;;

let INTEGRABLE_ADD = `!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> (\x. f x + g x) integrable_on s`;;

let INTEGRABLE_CMUL = `!f:real^M->real^N c s.
        f integrable_on s ==> (\x. c % f(x)) integrable_on s`;;

let INTEGRABLE_CMUL_EQ = `!f:real^M->real^N s c.
      (\x. c % f x) integrable_on s <=> c = &0 \/ f integrable_on s`;;

let INTEGRABLE_NEG = `!f:real^M->real^N s.
        f integrable_on s ==> (\x. --f(x)) integrable_on s`;;

let INTEGRABLE_NEG_EQ = `!f:real^M->real^N s. (\x. --f x) integrable_on s <=> f integrable_on s`;;

let INTEGRABLE_SUB = `!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> (\x. f x - g x) integrable_on s`;;

let INTEGRABLE_LINEAR = `!f h s. f integrable_on s /\ linear h ==> (h o f) integrable_on s`;;

let INTEGRAL_LINEAR = `!f:real^M->real^N s h:real^N->real^P.
        f integrable_on s /\ linear h
        ==> integral s (h o f) = h(integral s f)`;;

let HAS_INTEGRAL_VSUM = `!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> ((f a) has_integral (i a)) s)
        ==> ((\x. vsum t (\a. f a x)) has_integral (vsum t i)) s`;;

let INTEGRAL_VSUM = `!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) integrable_on s)
        ==> integral s (\x. vsum t (\a. f a x)) =
                vsum t (\a. integral s (f a))`;;

let INTEGRABLE_VSUM = `!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) integrable_on s)
        ==>  (\x. vsum t (\a. f a x)) integrable_on s`;;

let HAS_INTEGRAL_EQ = `!f:real^M->real^N g k s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        (f has_integral k) s
        ==> (g has_integral k) s`;;

let INTEGRABLE_EQ = `!f:real^M->real^N g s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        f integrable_on s
        ==> g integrable_on s`;;

let HAS_INTEGRAL_EQ_EQ = `!f:real^M->real^N g k s.
        (!x. x IN s ==> (f(x) = g(x)))
        ==> ((f has_integral k) s <=> (g has_integral k) s)`;;

let HAS_INTEGRAL_NULL = `!f:real^M->real^N a b.
    content(interval[a,b]) = &0 ==> (f has_integral vec 0) (interval[a,b])`;;

let HAS_INTEGRAL_NULL_EQ = `!f a b i. content(interval[a,b]) = &0
             ==> ((f has_integral i) (interval[a,b]) <=> i = vec 0)`;;

let INTEGRAL_NULL = `!f a b. content(interval[a,b]) = &0
           ==> integral(interval[a,b]) f = vec 0`;;

let INTEGRABLE_ON_NULL = `!f a b. content(interval[a,b]) = &0
           ==> f integrable_on interval[a,b]`;;

let HAS_INTEGRAL_EMPTY = `!f. (f has_integral vec 0) {}`;;

let HAS_INTEGRAL_EMPTY_EQ = `!f i. (f has_integral i) {} <=> i = vec 0`;;

let INTEGRABLE_ON_EMPTY = `!f. f integrable_on {}`;;

let INTEGRAL_EMPTY = `!f. integral {} f = vec 0`;;

let HAS_INTEGRAL_REFL = `!f a. (f has_integral vec 0) (interval[a,a])`;;

let INTEGRABLE_ON_REFL = `!f a. f integrable_on interval[a,a]`;;

let INTEGRAL_REFL = `!f a. integral (interval[a,a]) f = vec 0`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type criterion for integrability.                                  *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_CAUCHY = `!f:real^M->real^N a b.
    f integrable_on interval[a,b] <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p1 p2. p1 tagged_division_of interval[a,b] /\ d fine p1 /\
                            p2 tagged_division_of interval[a,b] /\ d fine p2
                            ==> norm(vsum p1 (\(x,k). content k % f x) -
                                     vsum p2 (\(x,k). content k % f x)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Additivity of integral on abutting intervals.                             *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_SPLIT = `!a b:real^N c k.
    1 <= k /\ k <= dimindex(:N)
    ==> interval[a,b] INTER {x | x$k <= c} =
        interval[a,(lambda i. if i = k then min (b$k) c else b$i)] /\
        interval[a,b] INTER {x | x$k >= c} =
        interval[(lambda i. if i = k then max (a$k) c else a$i),b]`;;

let CONTENT_SPLIT = `!a b:real^N k.
    1 <= k /\ k <= dimindex(:N)
    ==> content(interval[a,b]) =
        content(interval[a,b] INTER {x | x$k <= c}) +
        content(interval[a,b] INTER {x | x$k >= c})`;;

let DIVISION_SPLIT_LEFT_INJ = `(!d i k1 k2 k c.
        d division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        k1 IN d /\ k2 IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k <= c} = k2 INTER {x | x$k <= c}
        ==> content(k1 INTER {x:real^N | x$k <= c}) = &0)`
and DIVISION_SPLIT_RIGHT_INJ = `(!d i k1 k2 k c.
        d division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        k1 IN d /\ k2 IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k >= c} = k2 INTER {x | x$k >= c}
        ==> content(k1 INTER {x:real^N | x$k >= c}) = &0)`;;

let TAGGED_DIVISION_SPLIT_LEFT_INJ = `!d i x1 k1 x2 k2 k c.
        d tagged_division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        (x1,k1) IN d /\ (x2,k2) IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k <= c} = k2 INTER {x | x$k <= c}
        ==> content(k1 INTER {x:real^N | x$k <= c}) = &0`;;

let TAGGED_DIVISION_SPLIT_RIGHT_INJ = `!d i x1 k1 x2 k2 k c.
        d tagged_division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        (x1,k1) IN d /\ (x2,k2) IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k >= c} = k2 INTER {x | x$k >= c}
        ==> content(k1 INTER {x:real^N | x$k >= c}) = &0`;;

let DIVISION_SPLIT = `!p s:real^N->bool k c.
     p division_of s /\ 1 <= k /\ k <= dimindex(:N)
     ==> {l INTER {x | x$k <= c} |l| l IN p /\ ~(l INTER {x | x$k <= c} = {})}
         division_of (s INTER {x | x$k <= c}) /\
         {l INTER {x | x$k >= c} |l| l IN p /\ ~(l INTER {x | x$k >= c} = {})}
         division_of (s INTER {x | x$k >= c})`;;

let HAS_INTEGRAL_SPLIT = `!f:real^M->real^N k a b c.
      (f has_integral i) (interval[a,b] INTER {x | x$k <= c}) /\
      (f has_integral j) (interval[a,b] INTER {x | x$k >= c}) /\
      1 <= k /\ k <= dimindex(:M)
      ==> (f has_integral (i + j)) (interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* A sort of converse, integrability on subintervals.                        *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_UNION_INTERVAL = `!a b:real^N p1 p2 c k.
        1 <= k /\ k <= dimindex(:N) /\
        p1 tagged_division_of (interval[a,b] INTER {x | x$k <= c}) /\
        p2 tagged_division_of (interval[a,b] INTER {x | x$k >= c})
        ==> (p1 UNION p2) tagged_division_of (interval[a,b])`;;

let HAS_INTEGRAL_SEPARATE_SIDES = `!f:real^M->real^N i a b k.
        (f has_integral i) (interval[a,b]) /\
        1 <= k /\ k <= dimindex(:M)
        ==> !e. &0 < e
                ==> ?d. gauge d /\
                        !p1 p2. p1 tagged_division_of
                                     (interval[a,b] INTER {x | x$k <= c}) /\
                                d fine p1 /\
                                p2 tagged_division_of
                                     (interval[a,b] INTER {x | x$k >= c}) /\
                                d fine p2
                                ==> norm((vsum p1 (\(x,k). content k % f x) +
                                          vsum p2 (\(x,k). content k % f x)) -
                                         i) < e`;;

let INTEGRABLE_SPLIT = `!f:real^M->real^N a b.
        f integrable_on (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:M)
        ==> f integrable_on (interval[a,b] INTER {x | x$k <= c}) /\
            f integrable_on (interval[a,b] INTER {x | x$k >= c})`;;

(* ------------------------------------------------------------------------- *)
(* Generalized notion of additivity.                                         *)
(* ------------------------------------------------------------------------- *)

let operative = new_definition
 `operative op (f:(real^N->bool)->A) <=>
    (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = neutral(op)) /\
    (!a b c k. 1 <= k /\ k <= dimindex(:N)
               ==> f(interval[a,b]) =
                   op (f(interval[a,b] INTER {x | x$k <= c}))
                      (f(interval[a,b] INTER {x | x$k >= c})))`;;

let OPERATIVE_TRIVIAL = `!op f a b.
        operative op f /\ content(interval[a,b]) = &0
        ==> f(interval[a,b]) = neutral op`;;

let PROPERTY_EMPTY_INTERVAL = `!P. (!a b:real^N. content(interval[a,b]) = &0 ==> P(interval[a,b]))
       ==> P {}`;;

let OPERATIVE_EMPTY = `!op f:(real^N->bool)->A. operative op f ==> f {} = neutral op`;;

(* ------------------------------------------------------------------------- *)
(* Using additivity of lifted function to encode definedness.                *)
(* ------------------------------------------------------------------------- *)

let FORALL_OPTION = `(!x. P x) <=> P NONE /\ !x. P(SOME x)`;;

let EXISTS_OPTION = `(?x. P x) <=> P NONE \/ ?x. P(SOME x)`;;

let lifted = define
 `(lifted op NONE _ = NONE) /\
  (lifted op _ NONE = NONE) /\
  (lifted op (SOME x) (SOME y) = SOME(op x y))`;;

let NEUTRAL_LIFTED = `!op. monoidal op ==> neutral(lifted op) = SOME(neutral op)`;;

let MONOIDAL_LIFTED = `!op. monoidal op ==> monoidal(lifted op)`;;

let ITERATE_SOME = `!op. monoidal op
        ==> !f s. FINITE s
                  ==> iterate (lifted op) s (\x. SOME(f x)) =
                      SOME(iterate op s f)`;;

(* ------------------------------------------------------------------------- *)
(* Two key instances of additivity.                                          *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_CONTENT = `operative(+) content`;;

let OPERATIVE_INTEGRAL = `!f:real^M->real^N.
       operative(lifted(+))
         (\i. if f integrable_on i then SOME(integral i f) else NONE)`;;

(* ------------------------------------------------------------------------- *)
(* Points of division of a partition.                                        *)
(* ------------------------------------------------------------------------- *)

let division_points = new_definition
 `division_points (k:real^N->bool) (d:(real^N->bool)->bool) =
    {j,x | 1 <= j /\ j <= dimindex(:N) /\
           (interval_lowerbound k)$j < x /\ x < (interval_upperbound k)$j /\
           ?i. i IN d /\
               ((interval_lowerbound i)$j = x \/
                (interval_upperbound i)$j = x)}`;;

let DIVISION_POINTS_FINITE = `!d i:real^N->bool. d division_of i ==> FINITE(division_points i d)`;;

let DIVISION_POINTS_SUBSET = `!a b:real^N c d k.
        d division_of interval[a,b] /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i) /\
        1 <= k /\ k <= dimindex(:N) /\ a$k < c /\ c < b$k
        ==> division_points (interval[a,b] INTER {x | x$k <= c})
                            {l INTER {x | x$k <= c} | l |
                             l IN d /\ ~(l INTER {x | x$k <= c} = {})}
            SUBSET division_points (interval[a,b]) d /\
            division_points (interval[a,b] INTER {x | x$k >= c})
                            {l INTER {x | x$k >= c} | l |
                             l IN d /\ ~(l INTER {x | x$k >= c} = {})}
            SUBSET division_points (interval[a,b]) d`;;

let DIVISION_POINTS_PSUBSET = `!a b:real^N c d k.
        d division_of interval[a,b] /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i) /\
        1 <= k /\ k <= dimindex(:N) /\ a$k < c /\ c < b$k /\
        (?l. l IN d /\
             (interval_lowerbound l$k = c \/ interval_upperbound l$k = c))
        ==> division_points (interval[a,b] INTER {x | x$k <= c})
                            {l INTER {x | x$k <= c} | l |
                             l IN d /\ ~(l INTER {x | x$k <= c} = {})}
            PSUBSET division_points (interval[a,b]) d /\
            division_points (interval[a,b] INTER {x | x$k >= c})
                            {l INTER {x | x$k >= c} | l |
                             l IN d /\ ~(l INTER {x | x$k >= c} = {})}
            PSUBSET division_points (interval[a,b]) d`;;

(* ------------------------------------------------------------------------- *)
(* Preservation by divisions and tagged divisions.                           *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_DIVISION = `!op d a b f:(real^N->bool)->A.
    monoidal op /\ operative op f /\ d division_of interval[a,b]
    ==> iterate(op) d f = f(interval[a,b])`;;

let OPERATIVE_TAGGED_DIVISION = `!op d a b f:(real^N->bool)->A.
    monoidal op /\ operative op f /\ d tagged_division_of interval[a,b]
    ==> iterate(op) d (\(x,l). f l) = f(interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Additivity of content.                                                    *)
(* ------------------------------------------------------------------------- *)

let ADDITIVE_CONTENT_DIVISION = `!d a b:real^N.
    d division_of interval[a,b]
    ==> sum d content = content(interval[a,b])`;;

let ADDITIVE_CONTENT_TAGGED_DIVISION = `!d a b:real^N.
    d tagged_division_of interval[a,b]
    ==> sum d (\(x,l). content l) = content(interval[a,b])`;;

let SUBADDITIVE_CONTENT_DIVISION = `!d s a b:real^M.
        d division_of s /\ s SUBSET interval[a,b]
        ==> sum d content <= content(interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Finally, the integral of a constant!                                      *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_CONST = `!a b:real^M c:real^N.
    ((\x. c) has_integral (content(interval[a,b]) % c)) (interval[a,b])`;;

let INTEGRABLE_CONST = `!a b:real^M c:real^N. (\x. c) integrable_on interval[a,b]`;;

let INTEGRAL_CONST = `!a b c. integral (interval[a,b]) (\x. c) = content(interval[a,b]) % c`;;

let INTEGRAL_PASTECART_CONST = `!a b:real^M c d:real^N k:real^P.
     integral (interval[pastecart a c,pastecart b d]) (\x. k) =
     integral (interval[a,b])
              (\x. integral (interval[c,d]) (\y. k))`;;

(* ------------------------------------------------------------------------- *)
(* Bounds on the norm of Riemann sums and the integral itself.               *)
(* ------------------------------------------------------------------------- *)

let DSUM_BOUND = `!p a b:real^M c:real^N e.
       p division_of interval[a,b] /\ norm(c) <= e
       ==> norm(vsum p (\l. content l % c)) <= e * content(interval[a,b])`;;

let RSUM_BOUND = `!p a b f:real^M->real^N e.
       p tagged_division_of interval[a,b] /\
       (!x. x IN interval[a,b] ==> norm(f x) <= e)
       ==> norm(vsum p (\(x,k). content k % f x))
            <= e * content(interval[a,b])`;;

let RSUM_DIFF_BOUND = `!p a b f g:real^M->real^N.
       p tagged_division_of interval[a,b] /\
       (!x. x IN interval[a,b] ==> norm(f x - g x) <= e)
       ==> norm(vsum p (\(x,k). content k % f x) -
                vsum p (\(x,k). content k % g x))
           <= e * content(interval[a,b])`;;

let HAS_INTEGRAL_BOUND = `!f:real^M->real^N a b i B.
        &0 <= B /\
        (f has_integral i) (interval[a,b]) /\
        (!x. x IN interval[a,b] ==> norm(f x) <= B)
        ==> norm i <= B * content(interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Similar theorems about relationship among components.                     *)
(* ------------------------------------------------------------------------- *)

let RSUM_COMPONENT_LE = `!p a b f:real^M->real^N g:real^M->real^N.
       p tagged_division_of interval[a,b] /\ 1 <= i /\ i <= dimindex(:N) /\
       (!x. x IN interval[a,b] ==> (f x)$i <= (g x)$i)
       ==> vsum p (\(x,k). content k % f x)$i <=
           vsum p (\(x,k). content k % g x)$i`;;

let HAS_INTEGRAL_COMPONENT_LE = `!f:real^M->real^N g:real^M->real^N s i j k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> (f x)$k <= (g x)$k)
        ==> i$k <= j$k`;;

let INTEGRAL_COMPONENT_LE = `!f:real^M->real^N g:real^M->real^N s k.
        1 <= k /\ k <= dimindex(:N) /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> (f x)$k <= (g x)$k)
        ==> (integral s f)$k <= (integral s g)$k`;;

let HAS_INTEGRAL_DROP_LE = `!f:real^M->real^1 g:real^M->real^1 s i j.
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> drop(f x) <= drop(g x))
        ==> drop i <= drop j`;;

let INTEGRAL_DROP_LE = `!f:real^M->real^1 g:real^M->real^1 s.
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`;;

let HAS_INTEGRAL_COMPONENT_POS = `!f:real^M->real^N s i k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\
        (!x. x IN s ==> &0 <= (f x)$k)
        ==> &0 <= i$k`;;

let INTEGRAL_COMPONENT_POS = `!f:real^M->real^N s k.
        1 <= k /\ k <= dimindex(:N) /\
        f integrable_on s /\
        (!x. x IN s ==> &0 <= (f x)$k)
        ==> &0 <= (integral s f)$k`;;

let HAS_INTEGRAL_DROP_POS = `!f:real^M->real^1 s i.
        (f has_integral i) s /\
        (!x. x IN s ==> &0 <= drop(f x))
        ==> &0 <= drop i`;;

let INTEGRAL_DROP_POS = `!f:real^M->real^1 s.
        f integrable_on s /\
        (!x. x IN s ==> &0 <= drop(f x))
        ==> &0 <= drop(integral s f)`;;

let HAS_INTEGRAL_COMPONENT_NEG = `!f:real^M->real^N s i k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\
        (!x. x IN s ==> (f x)$k <= &0)
        ==> i$k <= &0`;;

let HAS_INTEGRAL_DROP_NEG = `!f:real^M->real^1 s i.
        (f has_integral i) s /\
        (!x. x IN s ==> drop(f x) <= &0)
        ==> drop i <= &0`;;

let HAS_INTEGRAL_COMPONENT_LBOUND = `!f:real^M->real^N a b i k.
        (f has_integral i) (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> B <= f(x)$k)
        ==> B * content(interval[a,b]) <= i$k`;;

let HAS_INTEGRAL_COMPONENT_UBOUND = `!f:real^M->real^N a b i k.
        (f has_integral i) (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f(x)$k <= B)
        ==> i$k <= B * content(interval[a,b])`;;

let INTEGRAL_COMPONENT_LBOUND = `!f:real^M->real^N a b k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> B <= f(x)$k)
        ==> B * content(interval[a,b]) <= (integral(interval[a,b]) f)$k`;;

let INTEGRAL_COMPONENT_UBOUND = `!f:real^M->real^N a b k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f(x)$k <= B)
        ==> (integral(interval[a,b]) f)$k <= B * content(interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Uniform limit of integrable functions is integrable.                      *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_UNIFORM_LIMIT = `!f a b. (!e. &0 < e
                ==> ?g. (!x. x IN interval[a,b] ==> norm(f x - g x) <= e) /\
                        g integrable_on interval[a,b] )
           ==> (f:real^M->real^N) integrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Negligible sets.                                                          *)
(* ------------------------------------------------------------------------- *)

let negligible = new_definition
 `negligible s <=> !a b. (indicator s has_integral (vec 0)) (interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility of hyperplane.                                              *)
(* ------------------------------------------------------------------------- *)

let VSUM_NONZERO_IMAGE_LEMMA = `!s f:A->B g:B->real^N a.
        FINITE s /\ g(a) = vec 0 /\
        (!x y. x IN s /\ y IN s /\ f x = f y /\ ~(x = y) ==> g(f x) = vec 0)
       ==> vsum {f x |x| x IN s /\ ~(f x = a)} g =
           vsum s (g o f)`;;

let INTERVAL_DOUBLESPLIT = `1 <= k /\ k <= dimindex(:N)
      ==> interval[a,b] INTER {x:real^N | abs(x$k - c) <= e} =
          interval[(lambda i. if i = k then max (a$k) (c - e) else a$i),
                   (lambda i. if i = k then min (b$k) (c + e) else b$i)]`;;

let DIVISION_DOUBLESPLIT = `!p a b:real^N k c e.
        p division_of interval[a,b] /\ 1 <= k /\ k <= dimindex(:N)
        ==> {l INTER {x | abs(x$k - c) <= e} |l|
                l IN p /\ ~(l INTER {x | abs(x$k - c) <= e} = {})}
            division_of (interval[a,b] INTER {x | abs(x$k - c) <= e})`;;

let CONTENT_DOUBLESPLIT = `!a b:real^N k c e.
        &0 < e /\ 1 <= k /\ k <= dimindex(:N)
        ==> ?d. &0 < d /\
                content(interval[a,b] INTER {x | abs(x$k - c) <= d}) < e`;;

let NEGLIGIBLE_STANDARD_HYPERPLANE = `!c k. negligible {x:real^N | x$k = c}`;;

(* ------------------------------------------------------------------------- *)
(* A technical lemma about "refinement" of division.                         *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_FINER = `!p a b:real^N d. p tagged_division_of interval[a,b] /\ gauge d
             ==> ?q. q tagged_division_of interval[a,b] /\ d fine q /\
                     !x k. (x,k) IN p /\ k SUBSET d(x) ==> (x,k) IN q`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main theorem about negligible sets.                             *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_NEGLIGIBLE = `!f:real^M->real^N s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> f x = vec 0)
        ==> (f has_integral (vec 0)) t`;;

let HAS_INTEGRAL_ON_NEGLIGIBLE = `!f:real^M->real^N s. negligible s ==> (f has_integral vec 0) s`;;

let INTEGRABLE_ON_NEGLIGIBLE = `!f:real^M->real^N s. negligible s ==> f integrable_on s`;;

let INTEGRAL_ON_NEGLIGIBLE = `!f:real^M->real^N s. negligible s ==> integral s f = vec 0`;;

let HAS_INTEGRAL_SPIKE = `!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_integral y) t
        ==> (g has_integral y) t`;;

let HAS_INTEGRAL_SPIKE_EQ = `!f:real^M->real^N g s t y.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_integral y) t <=> (g has_integral y) t)`;;

let INTEGRABLE_SPIKE = `!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f integrable_on t ==> g integrable_on  t`;;

let INTEGRABLE_SPIKE_EQ = `!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> (f integrable_on t <=> g integrable_on t)`;;

let INTEGRAL_SPIKE = `!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> integral t f = integral t g`;;

(* ------------------------------------------------------------------------- *)
(* Some other trivialities about negligible sets.                            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_SUBSET = `!s:real^N->bool t:real^N->bool.
        negligible s /\ t SUBSET s ==> negligible t`;;

let NEGLIGIBLE_DIFF = `!s t:real^N->bool. negligible s ==> negligible(s DIFF t)`;;

let NEGLIGIBLE_INTER = `!s t. negligible s \/ negligible t ==> negligible(s INTER t)`;;

let NEGLIGIBLE_UNION = `!s t:real^N->bool.
        negligible s /\ negligible t ==> negligible (s UNION t)`;;

let NEGLIGIBLE_UNION_EQ = `!s t:real^N->bool.
        negligible (s UNION t) <=> negligible s /\ negligible t`;;

let NEGLIGIBLE_SING = `!a:real^N. negligible {a}`;;

let NEGLIGIBLE_INSERT = `!a:real^N s. negligible(a INSERT s) <=> negligible s`;;

let NEGLIGIBLE_EMPTY = `negligible {}`;;

let NEGLIGIBLE_FINITE = `!s. FINITE s ==> negligible s`;;

let NEGLIGIBLE_UNIONS = `!s. FINITE s /\ (!t. t IN s ==> negligible t)
       ==> negligible(UNIONS s)`;;

let NEGLIGIBLE = `!s:real^N->bool. negligible s <=> !t. (indicator s has_integral vec 0) t`;;

(* ------------------------------------------------------------------------- *)
(* Finite or empty cases of the spike theorem are quite commonly needed.     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_SPIKE_FINITE = `!f:real^M->real^N g s t y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_integral y) t
        ==> (g has_integral y) t`;;

let HAS_INTEGRAL_SPIKE_FINITE_EQ = `!f:real^M->real^N g s y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_integral y) t <=> (g has_integral y) t)`;;

let INTEGRABLE_SPIKE_FINITE = `!f:real^M->real^N g s.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f integrable_on t
            ==> g integrable_on  t`;;

let INTEGRAL_EQ = `!f:real^M->real^N g s.
        (!x. x IN s ==> f x = g x) ==> integral s f = integral s g`;;

let INTEGRAL_EQ_0 = `!f:real^M->real^N s. (!x. x IN s ==> f x = vec 0) ==> integral s f = vec 0`;;

(* ------------------------------------------------------------------------- *)
(* In particular, the boundary of an interval is negligible.                 *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_FRONTIER_INTERVAL = `!a b:real^N. negligible(interval[a,b] DIFF interval(a,b))`;;

let HAS_INTEGRAL_SPIKE_INTERIOR = `!f:real^M->real^N g a b y.
        (!x. x IN interval(a,b) ==> g x = f x) /\
        (f has_integral y) (interval[a,b])
        ==> (g has_integral y) (interval[a,b])`;;

let HAS_INTEGRAL_SPIKE_INTERIOR_EQ = `!f:real^M->real^N g a b y.
        (!x. x IN interval(a,b) ==> g x = f x)
        ==> ((f has_integral y) (interval[a,b]) <=>
             (g has_integral y) (interval[a,b]))`;;

let INTEGRABLE_SPIKE_INTERIOR = `!f:real^M->real^N g a b.
        (!x. x IN interval(a,b) ==> g x = f x)
        ==> f integrable_on (interval[a,b])
            ==> g integrable_on  (interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Integrability of continuous functions.                                    *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_AND = `neutral(/\) = T`;;

let MONOIDAL_AND = `monoidal(/\)`;;

let ITERATE_AND = `!p s. FINITE s ==> (iterate(/\) s p <=> !x. x IN s ==> p x)`;;

let OPERATIVE_DIVISION_AND = `!P d a b. operative(/\) P /\ d division_of interval[a,b]
             ==> ((!i. i IN d ==> P i) <=> P(interval[a,b]))`;;

let OPERATIVE_APPROXIMABLE = `!f:real^M->real^N e.
        &0 <= e
        ==> operative(/\)
               (\i. ?g. (!x. x IN i ==> norm (f x - g x) <= e) /\
                        g integrable_on i)`;;

let APPROXIMABLE_ON_DIVISION = `!f:real^M->real^N d a b.
        &0 <= e /\
        (d division_of interval[a,b]) /\
        (!i. i IN d
             ==> ?g. (!x. x IN i ==> norm (f x - g x) <= e) /\
                     g integrable_on i)
        ==> ?g. (!x. x IN interval[a,b] ==> norm (f x - g x) <= e) /\
                g integrable_on interval[a,b]`;;

let INTEGRABLE_CONTINUOUS = `!f:real^M->real^N a b.
        f continuous_on interval[a,b] ==> f integrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Specialization of additivity to one dimension.                            *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_1_LT = `!op. monoidal op
        ==> !f. operative op f <=>
                (!a b. drop b <= drop a ==> f(interval[a,b]) = neutral op) /\
                (!a b c. drop a < drop c /\ drop c < drop b
                         ==> op (f(interval[a,c])) (f(interval[c,b])) =
                             f(interval[a,b]))`;;

let OPERATIVE_1_LE = `!op. monoidal op
        ==> !f. operative op f <=>
                (!a b. drop b <= drop a ==> f(interval[a,b]) = neutral op) /\
                (!a b c. drop a <= drop c /\ drop c <= drop b
                         ==> op (f(interval[a,c])) (f(interval[c,b])) =
                             f(interval[a,b]))`;;

(* ------------------------------------------------------------------------- *)
(* Additivity in R^1 for differences between function at endpoints.          *)
(* ------------------------------------------------------------------------- *)

let ADDITIVE_DIVISION_1 = `!f:real^1->real^N d a b.
        drop a <= drop b /\
        d division_of interval[a,b]
        ==> vsum d (\k. f(interval_upperbound k) - f(interval_lowerbound k)) =
            f b - f a`;;

let ADDITIVE_TAGGED_DIVISION_1 = `!f:real^1->real^N p a b.
        drop a <= drop b /\
        p tagged_division_of interval[a,b]
        ==> vsum p
             (\(x,k). f(interval_upperbound k) - f(interval_lowerbound k)) =
            f b - f a`;;

(* ------------------------------------------------------------------------- *)
(* A useful lemma allowing us to factor out the content size.                *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_FACTOR_CONTENT = `!f:real^M->real^N i a b.
      (f has_integral i) (interval[a,b]) <=>
      (!e. &0 < e
           ==> ?d. gauge d /\
                   (!p. p tagged_division_of interval[a,b] /\ d fine p
                        ==> norm (vsum p (\(x,k). content k % f x) - i)
                            <= e * content(interval[a,b])))`;;

(* ------------------------------------------------------------------------- *)
(* Attempt a systematic general set of "offset" results for components.      *)
(* ------------------------------------------------------------------------- *)

let GAUGE_MODIFY = `!f:real^M->real^N.
      (!s. open s ==> open {x | f(x) IN s})
      ==> !d. gauge d ==> gauge (\x y. d (f x) (f y))`;;

(* ------------------------------------------------------------------------- *)
(* Integrability on subintervals.                                            *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_INTEGRABLE = `!f. operative (/\) (\i. f integrable_on i)`;;

let INTEGRABLE_SUBINTERVAL = `!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        interval[c,d] SUBSET interval[a,b]
        ==> f integrable_on interval[c,d]`;;

(* ------------------------------------------------------------------------- *)
(* Combining adjacent intervals in 1 dimension.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE = `!f i:real^N j a b c.
        drop a <= drop c /\ drop c <= drop b /\
        (f has_integral i) (interval[a,c]) /\
        (f has_integral j) (interval[c,b])
        ==> (f has_integral (i + j)) (interval[a,b])`;;

let INTEGRAL_COMBINE = `!f:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b /\ f integrable_on (interval[a,b])
        ==> integral(interval[a,c]) f + integral(interval[c,b]) f =
            integral(interval[a,b]) f`;;

let INTEGRABLE_COMBINE = `!f a b c.
        drop a <= drop c /\ drop c <= drop b /\
        f integrable_on interval[a,c] /\
        f integrable_on interval[c,b]
        ==> f integrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Reduce integrability to "local" integrability.                            *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_ON_LITTLE_SUBINTERVALS = `!f:real^M->real^N a b.
        (!x. x IN interval[a,b]
             ==> ?d. &0 < d /\
                     !u v. x IN interval[u,v] /\
                           interval[u,v] SUBSET ball(x,d) /\
                           interval[u,v] SUBSET interval[a,b]
                           ==> f integrable_on interval[u,v])
        ==> f integrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Second FCT or existence of antiderivative.                                *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_HAS_VECTOR_DERIVATIVE_POINTWISE = `!f:real^1->real^N a b x.
        f integrable_on interval[a,b] /\ x IN interval[a,b] /\
        f continuous (at x within interval[a,b])
        ==> ((\u. integral (interval [a,u]) f) has_vector_derivative f x)
            (at x within interval [a,b])`;;

let INTEGRAL_HAS_VECTOR_DERIVATIVE = `!f:real^1->real^N a b.
     f continuous_on interval[a,b]
     ==> !x. x IN interval[a,b]
             ==> ((\u. integral (interval[a,u]) f) has_vector_derivative f(x))
                 (at x within interval[a,b])`;;

let ANTIDERIVATIVE_CONTINUOUS = `!f:real^1->real^N a b.
     f continuous_on interval[a,b]
     ==> ?g. !x. x IN interval[a,b]
                 ==> (g has_vector_derivative f(x))
                          (at x within interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Integrating characteristic function of an interval.                       *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_RESTRICT_OPEN_SUBINTERVAL = `!f:real^M->real^N a b c d i.
        (f has_integral i) (interval[c,d]) /\
        interval[c,d] SUBSET interval[a,b]
        ==> ((\x. if x IN interval(c,d) then f x else vec 0) has_integral i)
             (interval[a,b])`;;

let HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL = `!f:real^M->real^N a b c d i.
        (f has_integral i) (interval[c,d]) /\
        interval[c,d] SUBSET interval[a,b]
        ==> ((\x. if x IN interval[c,d] then f x else vec 0) has_integral i)
             (interval[a,b])`;;

let HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVALS_EQ = `!f:real^M->real^N a b c d i.
        interval[c,d] SUBSET interval[a,b]
        ==> (((\x. if x IN interval[c,d] then f x else vec 0) has_integral i)
              (interval[a,b]) <=>
             (f has_integral i) (interval[c,d]))`;;

(* ------------------------------------------------------------------------- *)
(* Hence we can apply the limit process uniformly to all integrals.          *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL = `!f:real^M->real^N i s.
     (f has_integral i) s <=>
        !e. &0 < e
            ==> ?B. &0 < B /\
                    !a b. ball(vec 0,B) SUBSET interval[a,b]
                          ==> ?z. ((\x. if x IN s then f(x) else vec 0)
                                   has_integral z) (interval[a,b]) /\
                                  norm(z - i) < e`;;

(* ------------------------------------------------------------------------- *)
(* Hence a general restriction property.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_RESTRICT = `!f:real^M->real^N s t i.
        s SUBSET t
        ==> (((\x. if x IN s then f x else vec 0) has_integral i) t <=>
             (f has_integral i) s)`;;

let INTEGRAL_RESTRICT = `!f:real^M->real^N s t.
        s SUBSET t
        ==> integral t (\x. if x IN s then f x else vec 0) =
            integral s f`;;

let INTEGRABLE_RESTRICT = `!f:real^M->real^N s t.
        s SUBSET t
        ==> ((\x. if x IN s then f x else vec 0) integrable_on t <=>
             f integrable_on s)`;;

let HAS_INTEGRAL_RESTRICT_UNIV = `!f:real^M->real^N s i.
        ((\x. if x IN s then f x else vec 0) has_integral i) (:real^M) <=>
         (f has_integral i) s`;;

let INTEGRAL_RESTRICT_UNIV = `!f:real^M->real^N s.
        integral (:real^M) (\x. if x IN s then f x else vec 0) =
        integral s f`;;

let INTEGRABLE_RESTRICT_UNIV = `!f s. (\x. if x IN s then f x else vec 0) integrable_on (:real^M) <=>
         f integrable_on s`;;

let HAS_INTEGRAL_RESTRICT_INTER = `!f:real^M->real^N s t.
        ((\x. if x IN s then f x else vec 0) has_integral i) t <=>
        (f has_integral i) (s INTER t)`;;

let INTEGRAL_RESTRICT_INTER = `!f:real^M->real^N s t.
        integral t (\x. if x IN s then f x else vec 0) =
        integral (s INTER t) f`;;

let INTEGRABLE_RESTRICT_INTER = `!f:real^M->real^N s t.
        (\x. if x IN s then f x else vec 0) integrable_on t <=>
        f integrable_on (s INTER t)`;;

let HAS_INTEGRAL_ON_SUPERSET = `!f s t.
        (!x. ~(x IN s) ==> f x = vec 0) /\ s SUBSET t /\ (f has_integral i) s
        ==> (f has_integral i) t`;;

let INTEGRABLE_ON_SUPERSET = `!f s t.
        (!x. ~(x IN s) ==> f x = vec 0) /\ s SUBSET t /\ f integrable_on s
        ==> f integrable_on t`;;

let NEGLIGIBLE_ON_INTERVALS = `!s. negligible s <=> !a b:real^N. negligible(s INTER interval[a,b])`;;

let NEGLIGIBLE_BOUNDED_SUBSETS = `!s:real^N->bool.
    negligible s <=> !t. bounded t /\ t SUBSET s ==> negligible t`;;

let NEGLIGIBLE_ON_COUNTABLE_INTERVALS = `!s:real^N->bool.
        negligible s <=>
        !n. negligible (s INTER interval[--vec n,vec n])`;;

let HAS_INTEGRAL_SPIKE_SET_EQ = `!f:real^M->real^N s t y.
        negligible(s DIFF t UNION t DIFF s)
        ==> ((f has_integral y) s <=> (f has_integral y) t)`;;

let HAS_INTEGRAL_SPIKE_SET = `!f:real^M->real^N s t y.
        negligible(s DIFF t UNION t DIFF s) /\
        (f has_integral y) s
        ==> (f has_integral y) t`;;

let INTEGRABLE_SPIKE_SET = `!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> f integrable_on s ==> f integrable_on t`;;

let INTEGRABLE_SPIKE_SET_EQ = `!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> (f integrable_on s <=> f integrable_on t)`;;

let INTEGRAL_SPIKE_SET = `!f:real^M->real^N g s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> integral s f = integral t f`;;

let HAS_INTEGRAL_INTERIOR = `!f:real^M->real^N y s.
        negligible(frontier s)
        ==> ((f has_integral y) (interior s) <=> (f has_integral y) s)`;;

let HAS_INTEGRAL_CLOSURE = `!f:real^M->real^N y s.
        negligible(frontier s)
        ==> ((f has_integral y) (closure s) <=> (f has_integral y) s)`;;

let INTEGRABLE_CASES = `!f g:real^M->real^N s.
        f integrable_on {x | x IN s /\ P x} /\
        g integrable_on {x | x IN s /\ ~P x}
        ==> (\x. if P x then f x else g x) integrable_on s`;;

(* ------------------------------------------------------------------------- *)
(* General "twiddling" for interval-to-interval function image.              *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_TWIDDLE = `!f:real^N->real^P (g:real^M->real^N) h r i a b.
      &0 < r /\
      (!x. h(g x) = x) /\ (!x. g(h x) = x) /\ (!x. g continuous at x) /\
      (!u v. ?w z. IMAGE g (interval[u,v]) = interval[w,z]) /\
      (!u v. ?w z. IMAGE h (interval[u,v]) = interval[w,z]) /\
      (!u v. content(IMAGE g (interval[u,v])) = r * content(interval[u,v])) /\
      (f has_integral i) (interval[a,b])
      ==> ((\x. f(g x)) has_integral (inv r) % i) (IMAGE h (interval[a,b]))`;;

let HAS_INTEGRAL_TWIDDLE_GEN = `!f:real^N->real^P (g:real^M->real^N) h r i s.
      &0 < r /\
      (!x. h(g x) = x) /\ (!x. g(h x) = x) /\ (!x. g continuous at x) /\
      (!b. &0 < b
           ==> ?b'. &0 < b' /\
                    ball(vec 0,b) SUBSET IMAGE g (ball(vec 0,b'))) /\
      (!u v. ?w z. IMAGE g (interval[u,v]) = interval[w,z]) /\
      (!u v. ?w z. IMAGE h (interval[u,v]) = interval[w,z]) /\
      (!u v. content(IMAGE g (interval[u,v])) = r * content(interval[u,v])) /\
      (f has_integral i) s
      ==> ((\x. f(g x)) has_integral (inv r) % i) (IMAGE h s)`;;

(* ------------------------------------------------------------------------- *)
(* Use this for various "trivial" change-of-variables results.               *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_TWIZZLE_INTERVAL = `!f:real^N->real^P p a b:real^M.
      (f has_integral y) (interval[(lambda i. a$(p i)),(lambda i. b$(p i))]) /\
      dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
      ==> ((\x. f(lambda i. x$p i)) has_integral y) (interval[a,b])`;;

let HAS_INTEGRAL_TWIZZLE = `!f:real^N->real^P s:real^M->bool y p.
        dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N) /\
        (f has_integral y) (IMAGE (\x. lambda i. x$p i) s)
        ==> ((\x. f(lambda i. x$p i)) has_integral y) s`;;

let HAS_INTEGRAL_TWIZZLE_EQ = `!f:real^N->real^P s:real^M->bool y p.
        dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
        ==> ((f has_integral y) (IMAGE (\x. lambda i. x$p i) s) <=>
             ((\x. f(lambda i. x$p i)) has_integral y) s)`;;

let INTEGRABLE_TWIZZLE_EQ = `!f:real^N->real^P s:real^M->bool p.
        dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
        ==> (f integrable_on IMAGE (\x. lambda i. x$p i) s <=>
             (\x. f(lambda i. x$p i)) integrable_on s)`;;

let INTEGRAL_TWIZZLE_EQ = `!f:real^N->real^P s:real^M->bool p.
        dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
        ==> integral (IMAGE (\x. lambda i. x$p i) s) f =
            integral s (\x. f(lambda i. x$p i))`;;

let HAS_INTEGRAL_PASTECART_SYM_ALT = `!f:real^(M,N)finite_sum->real^P s y.
        ((\z. f(pastecart (sndcart z) (fstcart z))) has_integral y) s <=>
        (f has_integral y) (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s)`;;

let HAS_INTEGRAL_PASTECART_SYM = `!f:real^(M,N)finite_sum->real^P s y.
        ((\z. f(pastecart (sndcart z) (fstcart z))) has_integral y)
        (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s) <=>
        (f has_integral y) s`;;

let INTEGRAL_PASTECART_SYM = `!f:real^(M,N)finite_sum->real^P s.
        integral
           (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s)
           (\z. f(pastecart (sndcart z) (fstcart z))) =
        integral s f`;;

let INTEGRABLE_PASTECART_SYM = `!f:real^(M,N)finite_sum->real^P s.
        (\z. f(pastecart (sndcart z) (fstcart z))) integrable_on
        (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s) <=>
        f integrable_on s`;;

let INTERVAL_IMAGE_AFFINITY_INTERVAL = `!a b m c. ?u v. IMAGE (\x. m % x + c) (interval[a,b]) = interval[u,v]`;;

let CONTENT_IMAGE_AFFINITY_INTERVAL = `!a b:real^N m c.
        content(IMAGE (\x. m % x + c) (interval[a,b])) =
        (abs m) pow (dimindex(:N)) * content(interval[a,b])`;;

let HAS_INTEGRAL_AFFINITY = `!f:real^M->real^N i s m c.
        (f has_integral i) s /\ ~(m = &0)
        ==> ((\x. f(m % x + c)) has_integral
             (inv(abs(m) pow dimindex(:M)) % i))
            (IMAGE (\x. inv m % x + --(inv(m) % c)) s)`;;

let INTEGRABLE_AFFINITY = `!f:real^M->real^N s m c.
        f integrable_on s /\ ~(m = &0)
        ==> (\x. f(m % x + c)) integrable_on
            (IMAGE (\x. inv m % x + --(inv(m) % c)) s)`;;

let CONTENT_IMAGE_STRETCH_INTERVAL = `!a b:real^N m.
        content(IMAGE (\x. lambda k. m k * x$k) (interval[a,b]):real^N->bool) =
        abs(product(1..dimindex(:N)) m) * content(interval[a,b])`;;

let HAS_INTEGRAL_STRETCH = `!f:real^M->real^N i m a b.
        (f has_integral i) (interval[a,b]) /\
        (!k. 1 <= k /\ k <= dimindex(:M) ==>  ~(m k = &0))
        ==> ((\x:real^M. f(lambda k. m k * x$k)) has_integral
             (inv(abs(product(1..dimindex(:M)) m)) % i))
            (IMAGE (\x. lambda k. inv(m k) * x$k) (interval[a,b]))`;;

let INTEGRABLE_STRETCH = `!f:real^M->real^N m a b.
        f integrable_on interval[a,b] /\
        (!k. 1 <= k /\ k <= dimindex(:M) ==>  ~(m k = &0))
        ==> (\x:real^M. f(lambda k. m k * x$k)) integrable_on
            (IMAGE (\x. lambda k. inv(m k) * x$k) (interval[a,b]))`;;

let HAS_INTEGRAL_REFLECT_LEMMA = `!f:real^M->real^N i a b.
     (f has_integral i) (interval[a,b])
     ==> ((\x. f(--x)) has_integral i) (interval[--b,--a])`;;

let HAS_INTEGRAL_REFLECT = `!f:real^M->real^N i a b.
     ((\x. f(--x)) has_integral i) (interval[--b,--a]) <=>
     (f has_integral i) (interval[a,b])`;;

let INTEGRABLE_REFLECT = `!f:real^M->real^N a b.
     (\x. f(--x)) integrable_on (interval[--b,--a]) <=>
     f integrable_on (interval[a,b])`;;

let INTEGRAL_REFLECT = `!f:real^M->real^N a b.
     integral (interval[--b,--a]) (\x. f(--x)) =
     integral (interval[a,b]) f`;;

let HAS_INTEGRAL_TRANSLATION = `!f:real^M->real^N i s a.
        ((\x. f(a + x)) has_integral i) s <=>
        (f has_integral i) (IMAGE (\x. a + x) s)`;;

let INTEGRAL_TRANSLATION = `!f:real^M->real^N s a.
       integral s (\x. f (a + x)) = integral (IMAGE (\x. a + x) s) f`;;

let INTEGRABLE_TRANSLATION = `!f:real^M->real^N s a.
        (\x. f(a + x)) integrable_on s <=>
        f integrable_on (IMAGE (\x. a + x) s)`;;

(* ------------------------------------------------------------------------- *)
(* Technical lemmas about how many non-trivial intervals of a division a     *)
(* point can be in (we sometimes need this for bounding sums).               *)
(* ------------------------------------------------------------------------- *)

let DIVISION_COMMON_POINT_BOUND = `!d s:real^N->bool x.
        d division_of s
        ==> CARD {k | k IN d /\ ~(content k = &0) /\ x IN k}
            <= 2 EXP (dimindex(:N))`;;

let TAGGED_PARTIAL_DIVISION_COMMON_POINT_BOUND = `!p s:real^N->bool y.
        p tagged_partial_division_of s
        ==> CARD {(x,k) | (x,k) IN p /\ y IN k /\ ~(content k = &0)}
            <= 2 EXP (dimindex(:N))`;;

let TAGGED_PARTIAL_DIVISION_COMMON_TAGS = `!p s:real^N->bool x.
        p tagged_partial_division_of s
        ==> CARD {(x,k) | k | (x,k) IN p /\ ~(content k = &0)}
            <= 2 EXP (dimindex(:N))`;;

(* ------------------------------------------------------------------------- *)
(* More lemmas that are useful later.                                        *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_DROP_POS_AE = `!f:real^M->real^1 s t i.
        (f has_integral i) s /\
        negligible t /\ (!x. x IN s DIFF t ==> &0 <= drop(f x))
        ==> &0 <= drop i`;;

let INTEGRAL_DROP_POS_AE = `!f:real^M->real^1 s t.
        f integrable_on s /\
        negligible t /\ (!x. x IN s DIFF t ==> &0 <= drop(f x))
        ==> &0 <= drop(integral s f)`;;

let HAS_INTEGRAL_SUBSET_COMPONENT_LE = `!f:real^M->real^N s t i j k.
        s SUBSET t /\ (f has_integral i) s /\ (f has_integral j) t /\
        1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN t ==> &0 <= f(x)$k)
        ==> i$k <= j$k`;;

let INTEGRAL_SUBSET_COMPONENT_LE = `!f:real^M->real^N s t k.
        s SUBSET t /\ f integrable_on s /\ f integrable_on t /\
        1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN t ==> &0 <= f(x)$k)
        ==> (integral s f)$k <= (integral t f)$k`;;

let HAS_INTEGRAL_SUBSET_DROP_LE = `!f:real^M->real^1 s t i j.
        s SUBSET t /\ (f has_integral i) s /\ (f has_integral j) t /\
        (!x. x IN t ==> &0 <= drop(f x))
        ==> drop i <= drop j`;;

let INTEGRAL_SUBSET_DROP_LE = `!f:real^M->real^1 s t.
        s SUBSET t /\ f integrable_on s /\ f integrable_on t /\
        (!x. x IN t ==> &0 <= drop(f(x)))
        ==> drop(integral s f) <= drop(integral t f)`;;

let INTEGRAL_SUBSET_DROP_LE_AE = `!f:real^M->real^1 s t u.
        s SUBSET t /\ f integrable_on s /\ f integrable_on t /\
        negligible u /\ (!x. x IN t DIFF u ==> &0 <= drop(f(x)))
        ==> drop(integral s f) <= drop(integral t f)`;;

let HAS_INTEGRAL_ALT = `!f:real^M->real^N s i.
        (f has_integral i) s <=>
            (!a b. (\x. if x IN s then f x else vec 0)
                   integrable_on interval[a,b]) /\
            (!e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball (vec 0,B) SUBSET interval[a,b]
                               ==> norm(integral(interval[a,b])
                                          (\x. if x IN s then f x else vec 0) -
                                        i) < e)`;;

let INTEGRABLE_ALT = `!f:real^M->real^N s.
        f integrable_on s <=>
          (!a b. (\x. if x IN s then f x else vec 0) integrable_on
                 interval[a,b]) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !a b c d.
                          ball(vec 0,B) SUBSET interval[a,b] /\
                          ball(vec 0,B) SUBSET interval[c,d]
                          ==> norm(integral (interval[a,b])
                                    (\x. if x IN s then f x else vec 0) -
                                   integral (interval[c,d])
                                    (\x. if x IN s then f x else vec 0)) < e)`;;

let INTEGRABLE_ALT_SUBSET = `!f:real^M->real^N s.
        f integrable_on s <=>
          (!a b. (\x. if x IN s then f x else vec 0) integrable_on
                 interval[a,b]) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !a b c d.
                          ball(vec 0,B) SUBSET interval[a,b] /\
                          interval[a,b] SUBSET interval[c,d]
                          ==> norm(integral (interval[a,b])
                                    (\x. if x IN s then f x else vec 0) -
                                   integral (interval[c,d])
                                    (\x. if x IN s then f x else vec 0)) < e)`;;

let INTEGRABLE_ON_SUBINTERVAL = `!f:real^M->real^N s a b.
        f integrable_on s /\ interval[a,b] SUBSET s
        ==> f integrable_on interval[a,b]`;;

let INTEGRAL_SPLIT = `!f:real^M->real^N a b t k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:M)
        ==> integral (interval[a,b]) f =
                integral(interval
                 [a,(lambda i. if i = k then min (b$k) t else b$i)]) f +
                integral(interval
                 [(lambda i. if i = k then max (a$k) t else a$i),b]) f`;;

let INTEGRAL_SPLIT_SIGNED = `!f:real^M->real^N a b t k.
        1 <= k /\ k <= dimindex(:M) /\ a$k <= t /\ a$k <= b$k /\
        f integrable_on
        interval[a,(lambda i. if i = k then max (b$k) t else b$i)]
        ==> integral (interval[a,b]) f =
                integral(interval
                 [a,(lambda i. if i = k then t else b$i)]) f +
                (if b$k < t then -- &1 else &1) %
                integral(interval
                 [(lambda i. if i = k then min (b$k) t else a$i),
                  (lambda i. if i = k then max (b$k) t else b$i)]) f`;;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION = `!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b]
        ==> integral(interval[a,d]) f =
                vsum {s | s SUBSET 1..dimindex(:M)}
                    (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                         integral
                          (interval[(lambda i. if i IN s
                                               then min (c$i) (d$i)
                                               else (a:real^M)$i),
                                    (lambda i. if i IN s
                                               then max (c$i) (d$i)
                                               else c$i)]) f)`;;

let INTEGRAL_INTERVALS_DIFF_INCLUSION_EXCLUSION = `!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b]
        ==> integral(interval[a,d]) f - integral(interval[a,c]) f =
                vsum {s | ~(s = {}) /\ s SUBSET 1..dimindex(:M)}
                    (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                         integral
                          (interval[(lambda i. if i IN s
                                               then min (c$i) (d$i)
                                               else (a:real^M)$i),
                                    (lambda i. if i IN s
                                               then max (c$i) (d$i)
                                               else c$i)]) f)`;;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_RIGHT = `!f:real^M->real^N a b c.
        f integrable_on interval[a,b] /\ c IN interval[a,b]
        ==> integral(interval[a,c]) f =
                vsum {s | s SUBSET 1..dimindex (:M)}
                     (\s. --(&1) pow CARD s %
                          integral
                           (interval[(lambda i. if i IN s then c$i else a$i),
                                     b])
                           f)`;;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_LEFT = `!f:real^M->real^N a b c.
        f integrable_on interval[a,b] /\ c IN interval[a,b]
        ==> integral(interval[c,b]) f =
                vsum {s | s SUBSET 1..dimindex (:M)}
                     (\s. --(&1) pow CARD s %
                          integral
                           (interval[a,(lambda i. if i IN s then c$i else b$i)])
                           f)`;;

let HAS_INTEGRAL_REFLECT_GEN = `!f:real^M->real^N i s.
     ((\x. f(--x)) has_integral i) s <=> (f has_integral i) (IMAGE (--) s)`;;

let INTEGRABLE_REFLECT_GEN = `!f:real^M->real^N s.
        (\x. f(--x)) integrable_on s <=> f integrable_on (IMAGE (--) s)`;;

let INTEGRAL_REFLECT_GEN = `!f:real^M->real^N s.
        integral s (\x. f(--x)) = integral (IMAGE (--) s) f`;;

(* ------------------------------------------------------------------------- *)
(* A straddling criterion for integrability.                                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_STRADDLE_INTERVAL = `!f:real^N->real^1 a b.
        (!e. &0 < e
             ==> ?g h i j. (g has_integral i) (interval[a,b]) /\
                           (h has_integral j) (interval[a,b]) /\
                           norm(i - j) < e /\
                           !x. x IN interval[a,b]
                               ==> drop(g x) <= drop(f x) /\
                                   drop(f x) <= drop(h x))
        ==> f integrable_on interval[a,b]`;;

let INTEGRABLE_STRADDLE = `!f:real^N->real^1 s.
        (!e. &0 < e
             ==> ?g h i j. (g has_integral i) s /\
                           (h has_integral j) s /\
                           norm(i - j) < e /\
                           !x. x IN s
                               ==> drop(g x) <= drop(f x) /\
                                   drop(f x) <= drop(h x))
        ==> f integrable_on s`;;

let HAS_INTEGRAL_STRADDLE_NULL = `!f g:real^N->real^1 s.
        (!x. x IN s ==> &0 <= drop(f x) /\ drop(f x) <= drop(g x)) /\
        (g has_integral (vec 0)) s
        ==> (f has_integral (vec 0)) s`;;

(* ------------------------------------------------------------------------- *)
(* Adding integrals over several sets.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_UNION = `!f:real^M->real^N i j s t.
        (f has_integral i) s /\ (f has_integral j) t /\ negligible(s INTER t)
        ==> (f has_integral (i + j)) (s UNION t)`;;

let INTEGRAL_UNION = `!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(s INTER t)
        ==> integral (s UNION t) f = integral s f + integral t f`;;

let INTEGRABLE_UNION = `!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(s INTER t)
        ==> f integrable_on (s UNION t)`;;

let INTEGRABLE_UNION_EQ = `!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t
        ==> (f integrable_on (s UNION t) <=> f integrable_on (s INTER t))`;;

let HAS_INTEGRAL_UNIONS_IMAGE = `!f:real^M->real^N k i t:A->bool.
        FINITE t /\
        (!s. s IN t ==> (f has_integral (i s)) (k s)) /\
        pairwise (\i j. negligible(k i INTER k j)) t
        ==> (f has_integral (vsum t i)) (UNIONS (IMAGE k t))`;;

let HAS_INTEGRAL_UNIONS = `!f:real^M->real^N i t.
        FINITE t /\
        (!s. s IN t ==> (f has_integral (i s)) s) /\
        (!s s'. s IN t /\ s' IN t /\ ~(s = s') ==> negligible(s INTER s'))
        ==> (f has_integral (vsum t i)) (UNIONS t)`;;

let INTEGRABLE_UNIONS_IMAGE = `!f:real^M->real^N k t:A->bool.
        FINITE t /\
        (!s. s IN t ==> f integrable_on k s) /\
        pairwise (\i j. negligible(k i INTER k j)) t
        ==> f integrable_on UNIONS (IMAGE k t)`;;

let INTEGRABLE_UNIONS = `!f:real^M->real^N u.
        FINITE u /\
        (!s. s IN u ==> f integrable_on s) /\
        pairwise (\s t. negligible(s INTER t)) u
        ==> f integrable_on UNIONS u`;;

let HAS_INTEGRAL_DIFF = `!f:real^M->real^N i j s t.
    (f has_integral i) s /\
    (f has_integral j) t /\
    negligible (t DIFF s)
    ==> (f has_integral (i - j)) (s DIFF t)`;;

let INTEGRAL_DIFF = `!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(t DIFF s)
        ==> integral (s DIFF t) f = integral s f - integral t f`;;

let INTEGRABLE_DIFF = `!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ t SUBSET s
        ==> f integrable_on (s DIFF t)`;;

let INTEGRABLE_ON_SUBINTERVAL_GEN = `!f:real^1->real^N s t.
        f integrable_on s /\ t SUBSET s /\ is_interval t
        ==> f integrable_on t`;;

let INTEGRABLE_ON_SUBSET = `!f:real^1->real^N s t.
        f integrable_on s /\ t SUBSET s /\ FINITE(components t)
        ==> f integrable_on t`;;

(* ------------------------------------------------------------------------- *)
(* In particular adding integrals over a division, maybe not of an interval. *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE_DIVISION = `!f:real^M->real^N s d i.
        d division_of s /\
        (!k. k IN d ==> (f has_integral (i k)) k)
        ==> (f has_integral (vsum d i)) s`;;

let INTEGRAL_COMBINE_DIVISION_BOTTOMUP = `!f:real^M->real^N d s.
        d division_of s /\ (!k. k IN d ==> f integrable_on k)
        ==> integral s f = vsum d (\i. integral i f)`;;

let HAS_INTEGRAL_COMBINE_DIVISION_TOPDOWN = `!f:real^M->real^N s d k.
        f integrable_on s /\ d division_of k /\ k SUBSET s
        ==> (f has_integral (vsum d (\i. integral i f))) k`;;

let INTEGRAL_COMBINE_DIVISION_TOPDOWN = `!f:real^M->real^N d s.
        f integrable_on s /\ d division_of s
        ==> integral s f = vsum d (\i. integral i f)`;;

let INTEGRABLE_COMBINE_DIVISION = `!f d s.
        d division_of s /\ (!i. i IN d ==> f integrable_on i)
        ==> f integrable_on s`;;

let INTEGRABLE_ON_SUBDIVISION = `!f:real^M->real^N s d i.
        d division_of i /\
        f integrable_on s /\ i SUBSET s
        ==> f integrable_on i`;;

(* ------------------------------------------------------------------------- *)
(* Also tagged divisions.                                                    *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE_TAGGED_DIVISION = `!f:real^M->real^N s p i.
        p tagged_division_of s /\
        (!x k. (x,k) IN p ==> (f has_integral (i k)) k)
        ==> (f has_integral (vsum p (\(x,k). i k))) s`;;

let INTEGRAL_COMBINE_TAGGED_DIVISION_BOTTOMUP = `!f:real^M->real^N p a b.
        p tagged_division_of interval[a,b] /\
        (!x k. (x,k) IN p ==> f integrable_on k)
        ==> integral (interval[a,b]) f = vsum p (\(x,k). integral k f)`;;

let HAS_INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN = `!f:real^M->real^N a b p.
        f integrable_on interval[a,b] /\ p tagged_division_of interval[a,b]
        ==> (f has_integral (vsum p (\(x,k). integral k f))) (interval[a,b])`;;

let INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN = `!f:real^M->real^N a b p.
        f integrable_on interval[a,b] /\ p tagged_division_of interval[a,b]
        ==> integral (interval[a,b]) f = vsum p (\(x,k). integral k f)`;;

(* ------------------------------------------------------------------------- *)
(* Henstock's lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

let HENSTOCK_LEMMA_PART1 = `!f:real^M->real^N a b d e.
        f integrable_on interval[a,b] /\
        &0 < e /\ gauge d /\
        (!p. p tagged_division_of interval[a,b] /\ d fine p
             ==> norm (vsum p (\(x,k). content k % f x) -
                       integral(interval[a,b]) f) < e)
        ==> !p. p tagged_partial_division_of interval[a,b] /\ d fine p
                            ==> norm(vsum p (\(x,k). content k % f x -
                                                     integral k f)) <= e`;;

let HENSTOCK_LEMMA_PART2 = `!f:real^M->real^N a b d e.
        f integrable_on interval[a,b] /\
        &0 < e /\ gauge d /\
        (!p. p tagged_division_of interval[a,b] /\ d fine p
             ==> norm (vsum p (\(x,k). content k % f x) -
                       integral(interval[a,b]) f) < e)
        ==> !p. p tagged_partial_division_of interval[a,b] /\ d fine p
                            ==> sum p (\(x,k). norm(content k % f x -
                                                    integral k f))
                                <= &2 * &(dimindex(:N)) * e`;;

let HENSTOCK_LEMMA = `!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> !e. &0 < e
                ==> ?d. gauge d /\
                        !p. p tagged_partial_division_of interval[a,b] /\
                            d fine p
                            ==> sum p (\(x,k). norm(content k % f x -
                                                    integral k f)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Monotone convergence (bounded interval first).                            *)
(* ------------------------------------------------------------------------- *)

let MONOTONE_CONVERGENCE_INTERVAL = `!f:num->real^N->real^1 g a b.
        (!k. (f k) integrable_on interval[a,b]) /\
        (!k x. x IN interval[a,b] ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN interval[a,b] ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral (interval[a,b]) (f k) | k IN (:num)}
        ==> g integrable_on interval[a,b] /\
            ((\k. integral (interval[a,b]) (f k))
             --> integral (interval[a,b]) g) sequentially`;;

let MONOTONE_CONVERGENCE_INCREASING = `!f:num->real^N->real^1 g s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`;;

let MONOTONE_CONVERGENCE_DECREASING = `!f:num->real^N->real^1 g s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`;;

let MONOTONE_CONVERGENCE_INCREASING_AE = `!f:num->real^N->real^1 g s t.
        (!k. (f k) integrable_on s) /\
        negligible t /\
        (!k x. x IN s DIFF t ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN s DIFF t ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`;;

let MONOTONE_CONVERGENCE_DECREASING_AE = `!f:num->real^N->real^1 g s t.
        (!k. (f k) integrable_on s) /\
        negligible t /\
        (!k x. x IN s DIFF t ==> drop(f (SUC k) x) <= drop(f k x)) /\
        (!x. x IN s DIFF t ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* More lemmas about existence and bounds between integrals.                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_NORM_BOUND_INTEGRAL = `!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> norm(integral s f) <= drop(integral s g)`;;

let INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT = `!f:real^M->real^N g:real^M->real^P s k.
        1 <= k /\ k <= dimindex(:P) /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= (g x)$k)
        ==> norm(integral s f) <= (integral s g)$k`;;

let HAS_INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT = `!f:real^M->real^N g:real^M->real^P s i j k.
        1 <= k /\ k <= dimindex(:P) /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> norm(f x) <= (g x)$k)
        ==> norm(i) <= j$k`;;

let INTEGRABLE_ON_ALL_INTERVALS_INTEGRABLE_BOUND = `!f:real^M->real^N g s.
        (!a b. (\x. if x IN s then f x else vec 0)
               integrable_on interval[a,b]) /\
        (!x. x IN s ==> norm(f x) <= drop(g x)) /\
        g integrable_on s
        ==> f integrable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Explicit limit statement for integrals over [0,inf].                      *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_LIM_AT_POSINFINITY = `!f l:real^N.
        (f has_integral l) {t | &0 <= drop t} <=>
        (!a. f integrable_on interval[vec 0,a]) /\
        ((\a. integral (interval[vec 0,lift a]) f) --> l) at_posinfinity`;;

let HAS_INTEGRAL_LIM_AT_POSINFINITY_GEN = `!f a l:real^N.
        (f has_integral l) {t | a <= drop t} <=>
        (!b. f integrable_on interval[lift a,lift b]) /\
        ((\b. integral (interval[lift a,lift b]) f) --> l) at_posinfinity`;;

let HAS_INTEGRAL_LIM_SEQUENTIALLY = `!f:real^1->real^N l.
           (f o lift --> vec 0) at_posinfinity /\
           (!n. f integrable_on interval[vec 0,vec n]) /\
           ((\n. integral (interval[vec 0,vec n]) f) --> l) sequentially
           ==> (f has_integral l) {t | &0 <= drop t}`;;

(* ------------------------------------------------------------------------- *)
(* Interval functions of bounded variation on a set.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_bounded_setvariation_on",(12,"right"));;

let set_variation = new_definition
 `set_variation s (f:(real^M->bool)->real^N) =
        sup { sum d (\k. norm(f k)) | ?t. d division_of t /\ t SUBSET s}`;;

let has_bounded_setvariation_on = new_definition
  `(f:(real^M->bool)->real^N) has_bounded_setvariation_on s <=>
        ?B. !d t. d division_of t /\ t SUBSET s
                  ==> sum d (\k. norm(f k)) <= B`;;

let SET_VARIATION_DEGENERATES = `!f:(real^M->bool)->real^N g s.
        ~(f has_bounded_setvariation_on s) /\
        ~(g has_bounded_setvariation_on s)
        ==> set_variation s f = set_variation s g`;;

let HAS_BOUNDED_SETVARIATION_ON = `!f:(real^M->bool)->real^N s.
        f  has_bounded_setvariation_on s <=>
        ?B. &0 < B /\ !d t. d division_of t /\ t SUBSET s
                            ==> sum d (\k. norm(f k)) <= B`;;

let HAS_BOUNDED_SET_VARIATION = `!f:(real^M->bool)->real^N s c.
        f has_bounded_setvariation_on s /\ set_variation s f <= c <=>
        !d t. d division_of t /\ t SUBSET s ==> sum d (\k. norm(f k)) <= c`;;

let HAS_BOUNDED_SETVARIATION_COMPARISON = `!f:(real^M->bool)->real^N g:(real^M->bool)->real^P s.
        f has_bounded_setvariation_on s /\
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> norm(g(interval[a,b])) <= norm(f(interval[a,b])))
        ==> g has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_EQ = `!f g:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b])) /\
        f has_bounded_setvariation_on s
        ==> g has_bounded_setvariation_on s`;;

let SET_VARIATION_EQ = `!f g:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b]))
        ==> set_variation s f = set_variation s g`;;

let HAS_BOUNDED_SETVARIATION_ON_COMPONENTWISE = `!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\k. lift(f k$i)) has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_LIFT_ABS = `!f:(real^N->bool)->real s.
        (\x. lift(abs(f x))) has_bounded_setvariation_on s <=>
        (\x. lift(f x)) has_bounded_setvariation_on s`;;

let SETVARIATION_EQUAL_LEMMA = `!mf:((real^M->bool)->real^N)->((real^M->bool)->real^N) ms ms'.
        (!s. ms'(ms s) = s /\ ms(ms' s) = s) /\
        (!f a b. ~(interval[a,b] = {})
                 ==> mf f (ms (interval[a,b])) = f (interval[a,b]) /\
                     ?a' b'. ~(interval[a',b'] = {}) /\
                             ms' (interval[a,b]) = interval[a',b']) /\
        (!t u. t SUBSET u ==> ms t SUBSET ms u /\ ms' t SUBSET ms' u) /\
        (!d t. d division_of t
               ==> (IMAGE ms d) division_of ms t /\
                   (IMAGE ms' d) division_of ms' t)
   ==> (!f s. (mf f) has_bounded_setvariation_on (ms s) <=>
              f has_bounded_setvariation_on s) /\
       (!f s. set_variation (ms s) (mf f) = set_variation s f)`;;

let HAS_BOUNDED_SETVARIATION_ON_ELEMENTARY = `!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> (f has_bounded_setvariation_on s <=>
             ?B. !d. d division_of s ==> sum d (\k. norm(f k)) <= B)`;;

let HAS_BOUNDED_SETVARIATION_ON_INTERVAL = `!f:(real^M->bool)->real^N a b.
        f has_bounded_setvariation_on interval[a,b] <=>
        ?B. !d. d division_of interval[a,b] ==> sum d (\k. norm(f k)) <= B`;;

let HAS_BOUNDED_SETVARIATION_ON_UNIV = `!f:(real^M->bool)->real^N.
        f has_bounded_setvariation_on (:real^M) <=>
        ?B. !d. d division_of UNIONS d ==> sum d (\k. norm(f k)) <= B`;;

let HAS_BOUNDED_SETVARIATION_ON_SUBSET = `!f:(real^M->bool)->real^N s t.
        f has_bounded_setvariation_on s /\ t SUBSET s
        ==> f has_bounded_setvariation_on t`;;

let HAS_BOUNDED_SETVARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS = `!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> bounded { f(interval[c,d]) | interval[c,d] SUBSET s}`;;

let HAS_BOUNDED_SETVARIATION_ON_NORM = `!f:(real^M->bool)->real^N s.
        (\x. lift(norm(f x))) has_bounded_setvariation_on s <=>
        f has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_COMPOSE_LINEAR = `!f:(real^M->bool)->real^N g:real^N->real^P s.
        f has_bounded_setvariation_on s /\ linear g
        ==> (g o f) has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_0 = `!s:real^N->bool. (\x. vec 0) has_bounded_setvariation_on s`;;

let SET_VARIATION_0 = `!s:real^N->bool. set_variation s (\x. vec 0) = &0`;;

let HAS_BOUNDED_SETVARIATION_ON_CMUL = `!f:(real^M->bool)->real^N c s.
        f has_bounded_setvariation_on s
        ==> (\x. c % f x) has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_NEG = `!f:(real^M->bool)->real^N s.
        (\x. --(f x)) has_bounded_setvariation_on s <=>
        f has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_ADD = `!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. f x + g x) has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_SUB = `!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. f x - g x) has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_MUL = `!f g:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. drop(f x) % g x) has_bounded_setvariation_on s`;;

let HAS_BOUNDED_SETVARIATION_ON_NULL = `!f:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s /\
               content(interval[a,b]) = &0
               ==> f(interval[a,b]) = vec 0) /\
        content s = &0 /\ bounded s
        ==> f has_bounded_setvariation_on s`;;

let SET_VARIATION_ON_EMPTY = `!f:(real^M->bool)->real^N. set_variation {} f = &0`;;

let SET_VARIATION_ELEMENTARY_LEMMA = `!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> ((!d t. d division_of t /\ t SUBSET s
                    ==> sum d (\k. norm(f k)) <= b) <=>
             (!d. d division_of s ==> sum d (\k. norm(f k)) <= b))`;;

let SET_VARIATION_ON_ELEMENTARY = `!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> set_variation s f =
             sup { sum d (\k. norm(f k)) | d division_of s}`;;

let SET_VARIATION_ON_INTERVAL = `!f:(real^M->bool)->real^N a b.
        set_variation (interval[a,b]) f =
        sup { sum d (\k. norm(f k)) | d division_of interval[a,b]}`;;

let SET_VARIATION_INTERVAL_LEMMA = `!f:(real^M->bool)->real^N s c.
        is_interval s
        ==> ((!d t. d division_of t /\ t SUBSET s
                    ==> sum d (\k. norm(f k)) <= c) <=>
             (!d a b. d division_of interval[a,b] /\ interval[a,b] SUBSET s
                      ==>  sum d (\k. norm(f k)) <= c))`;;

let HAS_BOUNDED_SETVARIATION_WORKS = `!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> (!d t. d division_of t /\ t SUBSET s
                   ==> sum d (\k. norm(f k)) <= set_variation s f) /\
            (!B. (!d t. d division_of t /\ t SUBSET s
                        ==> sum d (\k. norm (f k)) <= B)
                 ==> set_variation s f <= B)`;;

let HAS_BOUNDED_SETVARIATION_WORKS_ON_ELEMENTARY = `!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s /\ (?d. d division_of s)
        ==> (!d. d division_of s
                 ==> sum d (\k. norm(f k)) <= set_variation s f) /\
            (!B. (!d. d division_of s ==> sum d (\k. norm(f k)) <= B)
                 ==> set_variation s f <= B)`;;

let HAS_BOUNDED_SETVARIATION_WORKS_ON_INTERVAL = `!f:(real^M->bool)->real^N a b.
      f has_bounded_setvariation_on interval[a,b]
      ==> (!d. d division_of interval[a,b]
               ==> sum d (\k. norm(f k)) <= set_variation (interval[a,b]) f) /\
          (!B. (!d. d division_of interval[a,b]
                    ==> sum d (\k. norm(f k)) <= B)
               ==> set_variation (interval[a,b]) f <= B)`;;

let SET_VARIATION_UBOUND = `!f:(real^M->bool)->real^N s B.
        f has_bounded_setvariation_on s /\
        (!d t. d division_of t /\ t SUBSET s ==> sum d (\k. norm(f k)) <= B)
        ==> set_variation s f <= B`;;

let SET_VARIATION_UBOUND_ON_INTERVAL = `!f:(real^M->bool)->real^N a b B.
        f has_bounded_setvariation_on interval[a,b] /\
        (!d. d division_of interval[a,b] ==> sum d (\k. norm(f k)) <= B)
        ==> set_variation (interval[a,b]) f <= B`;;

let SET_VARIATION_LBOUND = `!f:(real^M->bool)->real^N s B.
        f has_bounded_setvariation_on s /\
        (?d t. d division_of t /\ t SUBSET s /\ B <= sum d (\k. norm(f k)))
        ==> B <= set_variation s f`;;

let SET_VARIATION_LBOUND_ON_INTERVAL = `!f:(real^M->bool)->real^N a b B.
        f has_bounded_setvariation_on interval[a,b] /\
        (?d. d division_of interval[a,b] /\ B <= sum d (\k. norm(f k)))
        ==> B <= set_variation (interval[a,b]) f`;;

let SET_VARIATION = `!f:(real^M->bool)->real^N s d t.
        f has_bounded_setvariation_on s /\ d division_of t /\ t SUBSET s
        ==> sum d (\k. norm(f k)) <= set_variation s f`;;

let SET_VARIATION_WORKS_ON_INTERVAL = `!f:(real^M->bool)->real^N a b d.
        f has_bounded_setvariation_on interval[a,b] /\
        d division_of interval[a,b]
        ==> sum d (\k. norm(f k)) <= set_variation (interval[a,b]) f`;;

let SET_VARIATION_POS_LE = `!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s ==> &0 <= set_variation s f`;;

let SET_VARIATION_CMUL = `!f:(real^M->bool)->real^N s c.
        f has_bounded_setvariation_on s
        ==> set_variation s (\x. c % f x) = abs c * set_variation s f`;;

let SET_VARIATION_COMPARISON = `!f:(real^M->bool)->real^N g:(real^M->bool)->real^P s.
        f has_bounded_setvariation_on s /\
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> norm(g(interval[a,b])) <= norm(f(interval[a,b])))
        ==> set_variation s g <= set_variation s f`;;

let SET_VARIATION_GE_FUNCTION = `!f:(real^M->bool)->real^N s a b.
        f has_bounded_setvariation_on s /\
        interval[a,b] SUBSET s /\ ~(interval[a,b] = {})
        ==> norm(f(interval[a,b])) <= set_variation s f`;;

let SET_VARIATION_ON_NULL = `!f:(real^M->bool)->real^N s.
        (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = vec 0) /\
        content s = &0 /\ bounded s
        ==> set_variation s f = &0`;;

let SET_VARIATION_TRIANGLE = `!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> set_variation s (\x. f x + g x)
             <= set_variation s f + set_variation s g`;;

let HAS_BOUNDED_SETVARIATION_ON_VSUM = `(!f:A->(real^M->bool)->real^N s k.
        FINITE k /\
        (!i. i IN k ==> f i has_bounded_setvariation_on s)
        ==> (\x. vsum k (\i. f i x)) has_bounded_setvariation_on s)`
and SET_VARIATION_SUM_LE = `(!f:A->(real^M->bool)->real^N s k.
        FINITE k /\
        (!i. i IN k ==> f i has_bounded_setvariation_on s)
        ==> set_variation s (\x. vsum k (\i. f i x))
            <= sum k (\i. set_variation s (f i)))`;;

let BOUNDED_SET_VARIATION_ON_PASTECART = `!f:(real^M->bool)->real^N g:(real^M->bool)->real^P s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. pastecart (f x) (g x)) has_bounded_setvariation_on s /\
            set_variation s (\x. pastecart (f x) (g x)) <=
                set_variation s f + set_variation s g`;;

let BOUNDED_SET_VARIATION_FROM_PASTECART = `!f:(real^M->bool)->real^N g:(real^M->bool)->real^P s.
      (\x. pastecart (f x) (g x)) has_bounded_setvariation_on s
      ==> (f has_bounded_setvariation_on s /\
           set_variation s f <= set_variation s (\x. pastecart (f x) (g x))) /\
          (g has_bounded_setvariation_on s /\
           set_variation s g <= set_variation s (\x. pastecart (f x) (g x)))`;;

let HAS_BOUNDED_SETVARIATION_ON_PASTECART = `!f:(real^M->bool)->real^N g:(real^M->bool)->real^P s.
        (\x. pastecart (f x) (g x)) has_bounded_setvariation_on s <=>
        f has_bounded_setvariation_on s /\ g has_bounded_setvariation_on s`;;

let OPERATIVE_LIFTED_SETVARIATION = `!f:(real^M->bool)->real^N.
        operative(+) f
        ==> operative (lifted(+))
                      (\i. if f has_bounded_setvariation_on i
                           then SOME(set_variation i f) else NONE)`;;

let OPERATIVE_HAS_BOUNDED_SETVARIATION_ON = `!f:(real^M->bool)->real^N.
        operative (+) f ==> operative (/\) ((has_bounded_setvariation_on) f)`;;

let HAS_BOUNDED_SETVARIATION_ON_DIVISION = `!f:(real^M->bool)->real^N a b d.
        operative (+) f /\ d division_of interval[a,b]
        ==> ((!k. k IN d ==> f has_bounded_setvariation_on k) <=>
             f has_bounded_setvariation_on interval[a,b])`;;

let SET_VARIATION_ON_DIVISION = `!f:(real^M->bool)->real^N a b d.
        operative (+) f /\ d division_of interval[a,b] /\
        f has_bounded_setvariation_on interval[a,b]
        ==> sum d (\k. set_variation k f) = set_variation (interval[a,b]) f`;;

let SET_VARIATION_MONOTONE = `!f:(real^M->bool)->real^N s t.
        f has_bounded_setvariation_on s /\ t SUBSET s
        ==> set_variation t f <= set_variation s f`;;

let HAS_BOUNDED_SETVARIATION_REFLECT2_EQ = `(!f:(real^M->bool)->real^N s.
        (\k. f(IMAGE (--) k)) has_bounded_setvariation_on (IMAGE (--) s) <=>
        f has_bounded_setvariation_on s)`
and SET_VARIATION_REFLECT2 = `(!f:(real^M->bool)->real^N s.
        set_variation (IMAGE (--) s) (\k. f(IMAGE (--) k)) =
        set_variation s f)`;;

let HAS_BOUNDED_SETVARIATION_TRANSLATION2_EQ = `(!a f:(real^M->bool)->real^N s.
          (\k. f(IMAGE (\x. a + x) k))
          has_bounded_setvariation_on (IMAGE (\x. --a + x) s) <=>
          f has_bounded_setvariation_on s)`
and SET_VARIATION_TRANSLATION2 = `(!a f:(real^M->bool)->real^N s.
          set_variation (IMAGE (\x. --a + x) s) (\k. f(IMAGE (\x. a + x) k)) =
          set_variation s f)`;;

let HAS_BOUNDED_SETVARIATION_TRANSLATION = `!f:(real^M->bool)->real^N s a.
        f has_bounded_setvariation_on s
        ==> (\k. f(IMAGE (\x. a + x) k))
            has_bounded_setvariation_on (IMAGE (\x. --a + x) s)`;;

(* ------------------------------------------------------------------------- *)
(* Absolute integrability (this is the same as Lebesgue integrability).      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("absolutely_integrable_on",(12,"right"));;

let absolutely_integrable_on = new_definition
 `f absolutely_integrable_on s <=>
        f integrable_on s /\ (\x. lift(norm(f x))) integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE = `!f s. f absolutely_integrable_on s ==> f integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE = `!f:real^M->real^N s.
     f absolutely_integrable_on s ==> (\x. lift (norm (f x))) integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV = `!f s. (\x. if x IN s then f x else vec 0)
              absolutely_integrable_on (:real^M) <=>
         f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_RESTRICT_INTER = `!f:real^M->real^N s t.
        (\x. if x IN s then f x else vec 0) absolutely_integrable_on t <=>
        f absolutely_integrable_on (s INTER t)`;;

let HAS_ABSOLUTE_INTEGRAL = `!(f:real^M->real^N) s y.
        f absolutely_integrable_on s /\ integral s f = y <=>
        f absolutely_integrable_on s /\ (f has_integral y) s`;;

let ABSOLUTELY_INTEGRABLE_LE = `!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> norm(integral s f) <= drop(integral s (\x. lift(norm(f x))))`;;

let ABSOLUTELY_INTEGRABLE_ON_NULL = `!f a b. content(interval[a,b]) = &0
           ==> f absolutely_integrable_on interval[a,b]`;;

let ABSOLUTELY_INTEGRABLE_ON_EMPTY = `!f:real^M->real^N. f absolutely_integrable_on {}`;;

let ABSOLUTELY_INTEGRABLE_0 = `!s. (\x. vec 0) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_CMUL = `!f s c. f absolutely_integrable_on s
           ==> (\x. c % f(x)) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_CMUL_EQ = `!f:real^M->real^N s c.
      (\x. c % f x) absolutely_integrable_on s <=>
      c = &0 \/ f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_NEG = `!f s. f absolutely_integrable_on s
         ==> (\x. --f(x)) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_NEG_EQ = `!f:real^M->real^N s.
        (\x. --f x) absolutely_integrable_on s <=>
        f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_NORM = `!f s. f absolutely_integrable_on s
         ==> (\x. lift(norm(f x))) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABS_1 = `!f s. f absolutely_integrable_on s
         ==> (\x. lift(abs(drop(f x)))) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL = `!f:real^M->real^N s a b.
        f absolutely_integrable_on s /\ interval[a,b] SUBSET s
        ==> f absolutely_integrable_on interval[a,b]`;;

let ABSOLUTELY_INTEGRABLE_COMBINE = `!f a b c.
        drop a <= drop c /\ drop c <= drop b /\
        f absolutely_integrable_on interval[a,c] /\
        f absolutely_integrable_on interval[c,b]
        ==> f absolutely_integrable_on interval[a,b]`;;

let ABSOLUTELY_INTEGRABLE_ON_NEGLIGIBLE = `!f:real^M->real^N s. negligible s ==> f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_SPIKE = `!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> f absolutely_integrable_on t ==> g absolutely_integrable_on t`;;

let ABSOLUTELY_INTEGRABLE_SPIKE_EQ = `!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> (f absolutely_integrable_on t <=> g absolutely_integrable_on t)`;;

let ABSOLUTELY_INTEGRABLE_SPIKE_SET_EQ = `!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> (f absolutely_integrable_on s <=> f absolutely_integrable_on t)`;;

let ABSOLUTELY_INTEGRABLE_SPIKE_SET = `!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> f absolutely_integrable_on s ==> f absolutely_integrable_on t`;;

let ABSOLUTELY_INTEGRABLE_EQ = `!f:real^M->real^N g s.
        (!x. x IN s ==> f x = g x) /\ f absolutely_integrable_on s
        ==> g absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ = `!f:real^N->real^P s:real^M->bool p.
        dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
        ==> (f absolutely_integrable_on IMAGE (\x. lambda i. x$p i) s <=>
             (\x. f(lambda i. x$p i)) absolutely_integrable_on s)`;;

let ABSOLUTELY_INTEGRABLE_AFFINITY = `!f:real^M->real^N s m c.
        f absolutely_integrable_on s /\ ~(m = &0)
        ==> (\x. f(m % x + c)) absolutely_integrable_on
            (IMAGE (\x. inv m % x + --(inv(m) % c)) s)`;;

let ABSOLUTELY_INTEGRABLE_TRANSLATION = `!f:real^M->real^N s a.
        (\x. f(a + x)) absolutely_integrable_on s <=>
        f absolutely_integrable_on (IMAGE (\x. a + x) s)`;;

let ABSOLUTELY_INTEGRABLE_REFLECT_GEN = `!f:real^M->real^N s.
        (\x. f(--x)) absolutely_integrable_on s <=>
        f absolutely_integrable_on (IMAGE (--) s)`;;

let ABSOLUTELY_INTEGRABLE_REFLECT = `!f:real^M->real^N a b.
     (\x. f(--x)) absolutely_integrable_on (interval[--b,--a]) <=>
     f absolutely_integrable_on (interval[a,b])`;;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION = `!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> (\k. integral k f) has_bounded_setvariation_on s`;;

let lemma = `!f:A->real^N g s e.
        sum s (\x. norm(f x - g x)) < e
        ==> FINITE s
            ==> abs(sum s (\x. norm(f x)) - sum s (\x. norm(g x))) < e`;;

let BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL = `!f:real^M->real^N a b.
        f integrable_on interval[a,b] /\
        (\k. integral k f) has_bounded_setvariation_on interval[a,b]
        ==> f absolutely_integrable_on interval[a,b]`;;

let BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE = `!f:real^M->real^N.
        f integrable_on UNIV /\
        (\k. integral k f) has_bounded_setvariation_on (:real^M)
        ==> f absolutely_integrable_on UNIV`;;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_UNIV_EQ = `!f:real^M->real^N.
        f absolutely_integrable_on (:real^M) <=>
        f integrable_on (:real^M) /\
        (\k. integral k f) has_bounded_setvariation_on (:real^M)`;;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_EQ = `!f:real^M->real^N a b.
        f absolutely_integrable_on interval[a,b] <=>
        f integrable_on interval[a,b] /\
        (\k. integral k f) has_bounded_setvariation_on interval[a,b]`;;

let ABSOLUTELY_INTEGRABLE_SET_VARIATION = `!f:real^M->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> set_variation (interval[a,b]) (\k. integral k f) =
                 drop(integral (interval[a,b]) (\x. lift(norm(f x))))`;;

let ABSOLUTELY_INTEGRABLE_CONST = `!a b c. (\x. c) absolutely_integrable_on interval[a,b]`;;

let ABSOLUTELY_INTEGRABLE_ADD = `!f:real^M->real^N g s.
        f absolutely_integrable_on s /\
        g absolutely_integrable_on s
        ==> (\x. f(x) + g(x)) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_SUB = `!f:real^M->real^N g s.
        f absolutely_integrable_on s /\
        g absolutely_integrable_on s
        ==> (\x. f(x) - g(x)) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_LINEAR = `!f:real^M->real^N h:real^N->real^P s.
        f absolutely_integrable_on s /\ linear h
        ==> (h o f) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_VSUM = `!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) absolutely_integrable_on s)
        ==>  (\x. vsum t (\a. f a x)) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABS = `!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_MAX = `!f:real^M->real^N g:real^M->real^N s.
        f absolutely_integrable_on s /\ g absolutely_integrable_on s
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N)
            absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_MAX_1 = `!f:real^M->real g:real^M->real s.
        (\x. lift(f x)) absolutely_integrable_on s /\
        (\x. lift(g x)) absolutely_integrable_on s
        ==> (\x. lift(max (f x) (g x))) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_MIN = `!f:real^M->real^N g:real^M->real^N s.
        f absolutely_integrable_on s /\ g absolutely_integrable_on s
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N)
            absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_MIN_1 = `!f:real^M->real g:real^M->real s.
        (\x. lift(f x)) absolutely_integrable_on s /\
        (\x. lift(g x)) absolutely_integrable_on s
        ==> (\x. lift(min (f x) (g x))) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABS_EQ = `!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
          f integrable_on s /\
          (\x. (lambda i. abs(f(x)$i)):real^N) integrable_on s`;;

let NONNEGATIVE_ABSOLUTELY_INTEGRABLE = `!f:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N)
               ==> &0 <= f(x)$i) /\
        f integrable_on s
        ==> f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND = `!f:real^M->real^N g s.
        (!x. x IN s ==> norm(f x) <= drop(g x)) /\
        f integrable_on s /\ g integrable_on s
        ==> f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_BOUND = `!f:real^M->real^N g:real^M->real^P s.
        (!x. x IN s ==> norm(f x) <= norm(g x)) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_INF_1 = `!fs s:real^N->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. lift(fs x i)) absolutely_integrable_on s)
        ==> (\x. lift(inf (IMAGE (fs x) k))) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_SUP_1 = `!fs s:real^N->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. lift(fs x i)) absolutely_integrable_on s)
        ==> (\x. lift(sup (IMAGE (fs x) k))) absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_CONTINUOUS = `!f:real^M->real^N a b.
        f continuous_on interval[a,b]
        ==> f absolutely_integrable_on interval[a,b]`;;

let INTEGRABLE_MIN_CONST_1 = `!f s t.
        &0 <= t /\ (!x. x IN s ==> &0 <= f x) /\
        (\x:real^N. lift(f x)) integrable_on s
        ==> (\x. lift(min (f x) t)) integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_UBOUND = `!f:real^M->real^N g:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> f(x)$i <= g(x)$i) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_LBOUND = `!f:real^M->real^N g:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> f(x)$i <= g(x)$i) /\
        f absolutely_integrable_on s /\ g integrable_on s
        ==> g absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_DROP_UBOUND = `!f:real^M->real^1 g:real^M->real^1 s.
        (!x. x IN s ==> drop(f(x)) <= drop(g(x))) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_DROP_LBOUND = `!f:real^M->real^1 g:real^M->real^1 s.
        (!x. x IN s ==> drop(f(x)) <= drop(g(x))) /\
        f absolutely_integrable_on s /\ g integrable_on s
        ==> g absolutely_integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_EQ_INTEGRABLE_POS = `!f:real^N->real^1 s.
        (!x. x IN s ==> &0 <= drop(f x))
        ==> (f absolutely_integrable_on s <=> f integrable_on s)`;;

let ABSOLUTELY_INTEGRABLE_PASTECART_SYM = `!f:real^(M,N)finite_sum->real^P s y.
        (\z. f(pastecart (sndcart z) (fstcart z))) absolutely_integrable_on
        (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s) <=>
        f absolutely_integrable_on s`;;

let HAS_INTEGRAL_PASTECART_SYM_UNIV = `(!f:real^(M,N)finite_sum->real^P s y.
        ((\z. f(pastecart (sndcart z) (fstcart z))) has_integral y) UNIV <=>
        (f has_integral y) UNIV)`
and INTEGRAL_PASTECART_SYM_UNIV = `(!f:real^(M,N)finite_sum->real^P s y.
        integral UNIV (\z. f(pastecart (sndcart z) (fstcart z))) =
        integral UNIV f)`
and INTEGRABLE_PASTECART_SYM_UNIV = `(!f:real^(M,N)finite_sum->real^P s y.
        (\z. f(pastecart (sndcart z) (fstcart z))) integrable_on UNIV <=>
        f integrable_on UNIV)`
and ABSOLUTELY_INTEGRABLE_PASTECART_SYM_UNIV = `(!f:real^(M,N)finite_sum->real^P s y.
     (\z. f(pastecart (sndcart z) (fstcart z)))
     absolutely_integrable_on UNIV <=>
       f absolutely_integrable_on UNIV)`;;

(* ------------------------------------------------------------------------- *)
(* Relating vector integrals to integrals of components.                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPONENTWISE = `!f:real^M->real^N s y.
        (f has_integral y) s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift((f x)$i)) has_integral (lift(y$i))) s`;;

let INTEGRABLE_COMPONENTWISE = `!f:real^M->real^N s.
        f integrable_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) integrable_on s`;;

let INTEGRABLE_LIFT_COMPONENT = `!(f:real^M->real^N) s.
        f integrable_on s /\
        1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift(f x$i)) integrable_on s`;;

let LIFT_INTEGRAL_COMPONENT = `!f:real^M->real^N.
        f integrable_on s
        ==> lift((integral s f)$k) = integral s (\x. lift((f x)$k))`;;

let INTEGRAL_COMPONENT = `!f:real^M->real^N.
        f integrable_on s
        ==> (integral s f)$k = drop(integral s (\x. lift((f x)$k)))`;;

let ABSOLUTELY_INTEGRABLE_COMPONENTWISE = `!f:real^M->real^N s.
     f absolutely_integrable_on s <=>
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\x. lift(f x$i)) absolutely_integrable_on s)`;;

let ABSOLUTELY_INTEGRABLE_LIFT_COMPONENT = `!(f:real^M->real^N) s.
        f absolutely_integrable_on s /\
        1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift(f x$i)) absolutely_integrable_on s`;;

(* ------------------------------------------------------------------------- *)
(* Dominated convergence.                                                    *)
(* ------------------------------------------------------------------------- *)

let DOMINATED_CONVERGENCE = `!f:num->real^M->real^N g h s.
        (!k. (f k) integrable_on s) /\ h integrable_on s /\
        (!k x. x IN s ==> norm(f k x) <= drop(h x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`;;

let DOMINATED_CONVERGENCE_INTEGRABLE = `!f:num->real^M->real^N g h s.
         (!k. f k absolutely_integrable_on s) /\
         h integrable_on s /\
         (!x. x IN s ==> norm(g x) <= drop(h x)) /\
         (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
         ==> g integrable_on s`;;

let DOMINATED_CONVERGENCE_ABSOLUTELY_INTEGRABLE = `!f:num->real^M->real^N g h s.
         (!k. f k absolutely_integrable_on s) /\
         h integrable_on s /\
         (!x. x IN s ==> norm(g x) <= drop(h x)) /\
         (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
         ==> g absolutely_integrable_on s`;;

let DOMINATED_CONVERGENCE_AE = `!f:num->real^M->real^N g h s t.
        (!k. (f k) integrable_on s) /\ h integrable_on s /\ negligible t /\
        (!k x. x IN s DIFF t ==> norm(f k x) <= drop(h x)) /\
        (!x. x IN s DIFF t ==> ((\k. f k x) --> g x) sequentially)
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`;;

let INTEGRAL_COUNTABLE_UNIONS = `!f:real^M->real^N s.
        (!n. f integrable_on (s n)) /\
        pairwise (\i j. negligible (s i INTER s j)) (:num) /\
        f absolutely_integrable_on (UNIONS {s n | n IN (:num)})
        ==> ((\n. vsum(0..n) (\i. integral (s i) f))
             --> integral (UNIONS {s n | n IN (:num)}) f) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* A few more properties of negligible sets.                                 *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_ON_UNIV = `!s. negligible s <=> (indicator s has_integral vec 0) (:real^N)`;;

let NEGLIGIBLE_COUNTABLE_UNIONS = `!s:num->real^N->bool.
        (!n. negligible(s n)) ==> negligible(UNIONS {s(n) | n IN (:num)})`;;

let HAS_INTEGRAL_NEGLIGIBLE_EQ = `!f:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> &0 <= f(x)$i)
        ==> ((f has_integral vec 0) s <=>
             negligible {x | x IN s /\ ~(f x = vec 0)})`;;

let INTEGRAL_ZERO_ON_SUBINTERVALS_IMP_ZERO_AE = `!f:real^M->real^N a b.
        (!x. x IN interval[a,b] ==> (f has_integral vec 0) (interval[a,x]))
        ==> negligible {x | x IN interval[a,b] /\ ~(f x = vec 0)}`;;

let NEGLIGIBLE_COUNTABLE = `!s:real^N->bool. COUNTABLE s ==> negligible s`;;

(* ------------------------------------------------------------------------- *)
(* More basic "almost everywhere" variants of other theorems.                *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPONENT_LE_AE = `!f:real^M->real^N g:real^M->real^N s i j k t.
        1 <= k /\ k <= dimindex(:N) /\ negligible t /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s DIFF t ==> (f x)$k <= (g x)$k)
        ==> i$k <= j$k`;;

let INTEGRAL_COMPONENT_LE_AE = `!f:real^M->real^N g:real^M->real^N s k t.
        1 <= k /\ k <= dimindex(:N) /\ negligible t /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s DIFF t ==> (f x)$k <= (g x)$k)
        ==> (integral s f)$k <= (integral s g)$k`;;

let HAS_INTEGRAL_DROP_LE_AE = `!f:real^M->real^1 g:real^M->real^1 s i j t.
        (f has_integral i) s /\ (g has_integral j) s /\
        negligible t /\ (!x. x IN s DIFF t ==> drop(f x) <= drop(g x))
        ==> drop i <= drop j`;;

let INTEGRAL_DROP_LE_AE = `!f:real^M->real^1 g:real^M->real^1 s t.
        f integrable_on s /\ g integrable_on s /\
        negligible t /\ (!x. x IN s DIFF t ==> drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`;;

let NONNEGATIVE_ABSOLUTELY_INTEGRABLE_AE = `!f:real^M->real^N s t.
        negligible t /\
        (!x i. x IN s DIFF t /\ 1 <= i /\ i <= dimindex(:N)
               ==> &0 <= f(x)$i) /\
        f integrable_on s
        ==> f absolutely_integrable_on s`;;

let INTEGRAL_NORM_BOUND_INTEGRAL_AE = `!f:real^M->real^N g s t.
        f integrable_on s /\ g integrable_on s /\
        negligible t /\ (!x. x IN s DIFF t ==> norm(f x) <= drop(g x))
        ==> norm(integral s f) <= drop(integral s g)`;;

(* ------------------------------------------------------------------------- *)
(* Beppo Levi theorem.                                                       *)
(* ------------------------------------------------------------------------- *)

let BEPPO_LEVI_INCREASING = `!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`;;

let BEPPO_LEVI_DECREASING = `!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`;;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING = `!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`;;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING = `!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`;;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING_AE = `!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k. ?t. negligible t /\
                 !x. x IN s DIFF t ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`;;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING_AE = `!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k. ?t. negligible t /\
                 !x. x IN s DIFF t ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Fatou's lemma and Lieb's extension.                                       *)
(* ------------------------------------------------------------------------- *)

let FATOU = `!f:num->real^N->real^1 g s t B.
        negligible t /\
        (!n. (f n) integrable_on s) /\
        (!n x. x IN s DIFF t ==> &0 <= drop(f n x)) /\
        (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially) /\
        (!n. drop(integral s (f n)) <= B)
        ==> g integrable_on s /\
            &0 <= drop(integral s g) /\ drop(integral s g) <= B`;;

let LIEB = `!f:num->real^M->real^N g s t.
     (!n. f n absolutely_integrable_on s) /\ g absolutely_integrable_on s /\
     negligible t /\ (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially)
     ==> ((\n. integral s (\x. lift(norm(f n x - g x))) -
               (integral s (\x. lift(norm(f n x))) -
                integral s (\x. lift(norm(g x)))))
          --> vec 0) sequentially`;;

let FATOU_STRONG = `!f:num->real^N->real^1 g s t B.
      negligible t /\
      (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially) /\
      eventually (\n. (f n) integrable_on s) sequentially /\
      eventually (\n. !x. x IN s DIFF t ==> &0 <= drop(f n x)) sequentially /\
      eventually (\n. drop(integral s (f n)) <= B) sequentially
        ==> g absolutely_integrable_on s /\
            &0 <= drop(integral s g) /\ drop(integral s g) <= B`;;

(* ------------------------------------------------------------------------- *)
(* Fundamental theorem of calculus, starting with strong forms.              *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_CALCULUS_BARTLE = `!f:real^1->real^N f' s a b.
      negligible s /\ drop a <= drop b /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f'(x)) (at x within interval[a,b])) /\
      (!e. &0 < e
           ==> ?g. gauge g /\
                   !p. p tagged_partial_division_of interval[a,b] /\
                       g fine p /\ IMAGE FST p SUBSET s
                       ==> norm (vsum p (\(x,k). f(interval_upperbound k) -
                                                 f(interval_lowerbound k)))
                           < e)
      ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`;;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG = `!f:real^1->real^N f' s a b.
        COUNTABLE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`;;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG = `!f:real^1->real^N f' s a b.
        COUNTABLE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF s
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`;;

let FUNDAMENTAL_THEOREM_OF_CALCULUS = `!f:real^1->real^N f' a b.
        drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`;;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR = `!f:real^1->real^N f' a b.
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b)
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`;;

let ANTIDERIVATIVE_INTEGRAL_CONTINUOUS = `!f:real^1->real^N a b.
     (f continuous_on interval[a,b])
     ==> ?g. !u v. u IN interval[a,b] /\ v IN interval[a,b] /\ drop u <= drop v
                   ==> (f has_integral (g(v) - g(u))) (interval[u,v])`;;

(* ------------------------------------------------------------------------- *)
(* This doesn't directly involve integration, but that gives an easy proof.  *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL = `!f:real^1->real^N a b k y.
        COUNTABLE k /\ f continuous_on interval[a,b] /\ f a = y /\
        (!x. x IN (interval[a,b] DIFF k)
             ==> (f has_derivative (\h. vec 0)) (at x within interval[a,b]))
        ==> !x. x IN interval[a,b] ==> f x = y`;;

(* ------------------------------------------------------------------------- *)
(* Generalize a bit to any convex set.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX = `!f:real^M->real^N s k c y.
      convex s /\ COUNTABLE k /\ f continuous_on s /\ c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_derivative (\h. vec 0)) (at x within s))
      ==> !x. x IN s ==> f x = y`;;

(* ------------------------------------------------------------------------- *)
(* Also to any open connected set with finite set of exceptions. Could       *)
(* generalize to locally convex set with limpt-free set of exceptions.       *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONNECTED = `!f:real^M->real^N s k c y.
      connected s /\ open s /\ COUNTABLE k /\ f continuous_on s /\
      c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_derivative (\h. vec 0)) (at x within s))
      ==> !x. x IN s ==> f x = y`;;

(* ------------------------------------------------------------------------- *)
(* Integration by parts.                                                     *)
(* ------------------------------------------------------------------------- *)

let INTEGRATION_BY_PARTS = `!(bop:real^M->real^N->real^P) f g f' g' a b c y.
        bilinear bop /\ drop a <= drop b /\ COUNTABLE c /\
        (\x. bop (f x) (g x)) continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF c
             ==> (f has_vector_derivative f'(x)) (at x) /\
                 (g has_vector_derivative g'(x)) (at x)) /\
        ((\x. bop (f x) (g' x)) has_integral
         ((bop (f b) (g b) - bop (f a) (g a)) - y))
            (interval[a,b])
        ==> ((\x. bop (f' x) (g x)) has_integral y) (interval[a,b])`;;

let INTEGRATION_BY_PARTS_SIMPLE = `!(bop:real^M->real^N->real^P) f g f' g' a b y.
        bilinear bop /\ drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]) /\
                 (g has_vector_derivative g'(x)) (at x within interval[a,b])) /\
        ((\x. bop (f x) (g' x)) has_integral
         ((bop (f b) (g b) - bop (f a) (g a)) - y))
            (interval[a,b])
        ==> ((\x. bop (f' x) (g x)) has_integral y) (interval[a,b])`;;

let INTEGRABLE_BY_PARTS = `!(bop:real^M->real^N->real^P) f g f' g' a b c.
        bilinear bop /\ COUNTABLE c /\
        (\x. bop (f x) (g x)) continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF c
             ==> (f has_vector_derivative f'(x)) (at x) /\
                 (g has_vector_derivative g'(x)) (at x)) /\
        (\x. bop (f x) (g' x)) integrable_on interval[a,b]
        ==> (\x. bop (f' x) (g x)) integrable_on interval[a,b]`;;

let INTEGRABLE_BY_PARTS_EQ = `!(bop:real^M->real^N->real^P) f g f' g' a b c.
        bilinear bop /\ COUNTABLE c /\
        (\x. bop (f x) (g x)) continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF c
             ==> (f has_vector_derivative f'(x)) (at x) /\
                 (g has_vector_derivative g'(x)) (at x))
        ==> ((\x. bop (f x) (g' x)) integrable_on interval[a,b] <=>
             (\x. bop (f' x) (g x)) integrable_on interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Equiintegrability. The definition here only really makes sense for an     *)
(* elementary set. We just use compact intervals in applications below.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("equiintegrable_on",(12,"right"));;

let equiintegrable_on = new_definition
  `fs equiintegrable_on i <=>
        (!f:real^M->real^N. f IN fs ==> f integrable_on i) /\
        (!e. &0 < e
             ==> ?d. gauge d /\
                    !f p. f IN fs /\ p tagged_division_of i /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) -
                                 integral i f) < e)`;;

let EQUIINTEGRABLE_ON_SING = `!f:real^M->real^N a b.
        {f} equiintegrable_on interval[a,b] <=>
        f integrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for the interval of integration.                 *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_ON_NULL = `!fs:(real^M->real^N)->bool a b.
     content(interval[a,b]) = &0 ==> fs equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_ON_SPLIT = `!fs:(real^M->real^N)->bool k a b c.
      fs equiintegrable_on (interval[a,b] INTER {x | x$k <= c}) /\
      fs equiintegrable_on (interval[a,b] INTER {x | x$k >= c}) /\
      1 <= k /\ k <= dimindex(:M)
      ==> fs equiintegrable_on (interval[a,b])`;;

let EQUIINTEGRABLE_DIVISION = `!fs:(real^M->real^N)->bool d a b.
        d division_of interval[a,b]
        ==> (fs equiintegrable_on interval[a,b] <=>
             !i. i IN d ==> fs equiintegrable_on i)`;;

(* ------------------------------------------------------------------------- *)
(* Main limit theorem for an equiintegrable sequence.                        *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_LIMIT = `!f g:real^M->real^N a b.
        {f n | n IN (:num)} equiintegrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> ((\n. f n x) --> g x) sequentially)
        ==> g integrable_on interval[a,b] /\
            ((\n. integral(interval[a,b]) (f n)) --> integral(interval[a,b]) g)
            sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for the set of equiintegrable functions.               *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_SUBSET = `!fs gs s.
   fs equiintegrable_on s /\ gs SUBSET fs ==> gs equiintegrable_on s`;;

let EQUIINTEGRABLE_UNION = `!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> (fs UNION gs) equiintegrable_on s`;;

let EQUIINTEGRABLE_EQ = `!fs gs:(real^M->real^N)->bool s.
        fs equiintegrable_on s /\
        (!g. g IN gs ==> ?f. f IN fs /\ (!x. x IN s ==> f x = g x))
        ==> gs equiintegrable_on s`;;

let EQUIINTEGRABLE_CMUL = `!fs:(real^M->real^N)->bool s k.
        fs equiintegrable_on s
        ==> {(\x. c % f x) | abs(c) <= k /\ f IN fs} equiintegrable_on s`;;

let EQUIINTEGRABLE_ADD = `!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> {(\x. f x + g x) | f IN fs /\ g IN gs} equiintegrable_on s`;;

let EQUIINTEGRABLE_NEG = `!fs:(real^M->real^N)->bool s.
        fs equiintegrable_on s
        ==> {(\x. --(f x)) | f IN fs} equiintegrable_on s`;;

let EQUIINTEGRABLE_SUB = `!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> {(\x. f x - g x) | f IN fs /\ g IN gs} equiintegrable_on s`;;

let EQUIINTEGRABLE_SUM = `!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {(\x. vsum t (\i. c i % f i x)) |
               FINITE t /\
               (!i:A. i IN t ==> &0 <= c i /\ (f i) IN fs) /\
               sum t c = &1}
            equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_UNIFORM_LIMIT = `!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {g | !e. &0 < e
                     ==> ?f. f IN fs /\
                             !x. x IN interval[a,b] ==> norm(g x - f x) < e}
            equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_REFLECT = `!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {(\x. f(--x)) | f IN fs} equiintegrable_on interval[--b,--a]`;;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas about minimizing a "flat" part of a sum over a      *)
(* division, followed by subinterval resictions for equiintegrable family.   *)
(* ------------------------------------------------------------------------- *)

let SUM_CONTENT_AREA_OVER_THIN_DIVISION = `!d a b:real^M s i c.
        d division_of s /\ s SUBSET interval[a,b] /\
        1 <= i /\ i <= dimindex(:M) /\ a$i <= c /\ c <= b$i /\
        (!k. k IN d ==> ~(k INTER {x | x$i = c} = {}))
        ==> (b$i - a$i) *
            sum d (\k. content k /
                       (interval_upperbound k$i - interval_lowerbound k$i))
            <= &2 * content(interval[a,b])`;;

let BOUNDED_EQUIINTEGRAL_OVER_THIN_TAGGED_PARTIAL_DIVISION = `!fs f:real^M->real^N a b e.
    fs equiintegrable_on interval[a,b] /\ f IN fs /\
    (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x)) /\
    &0 < e
    ==> ?d. gauge d /\
            !c i p h. c IN interval[a,b] /\ 1 <= i /\ i <= dimindex(:M) /\
                      p tagged_partial_division_of interval[a,b] /\
                      d fine p /\
                      h IN fs /\
                      (!x k. (x,k) IN p ==> ~(k INTER {x | x$i = c$i} = {}))
                      ==> sum p(\(x,k). norm(integral k h)) < e`;;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE = `!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i <= c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE = `!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i >= c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LT = `!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i < c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GT = `!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i > c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_OPEN_INTERVAL_RESTRICTIONS = `!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> { (\x. if x IN interval(c,d) then f x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`;;

let EQUIINTEGRABLE_CLOSED_INTERVAL_RESTRICTIONS = `!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> { (\x. if x IN interval[c,d] then f x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Continuity of the indefinite integral.                                    *)
(* ------------------------------------------------------------------------- *)

let INDEFINITE_INTEGRAL_CONTINUOUS = `!f:real^M->real^N a b c d e.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b] /\ &0 < e
        ==> ?k. &0 < k /\
                !c' d'. c' IN interval[a,b] /\
                        d' IN interval[a,b] /\
                        norm(c' - c) <= k /\ norm(d' - d) <= k
                        ==> norm(integral(interval[c',d']) f -
                                 integral(interval[c,d]) f) < e`;;

let INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT = `!f:real^M->real^N a b.
        f integrable_on interval[a,b]
         ==> (\x. integral (interval[a,x]) f) continuous_on interval[a,b]`;;

let INDEFINITE_INTEGRAL_CONTINUOUS_LEFT = `!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> (\x. integral(interval[x,b]) f) continuous_on interval[a,b]`;;

let INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS = `!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> (\y. integral (interval[fstcart y,sndcart y]) f)
            uniformly_continuous_on interval[pastecart a a,pastecart b b]`;;

let INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS_EXPLICIT = `!f:real^M->real^N a b e.
        f integrable_on interval[a,b] /\ &0 < e
        ==> ?k. &0 < k /\
                !c d c' d'. c IN interval[a,b] /\ d IN interval[a,b] /\
                            c' IN interval[a,b] /\ d' IN interval[a,b] /\
                            norm (c' - c) <= k /\ norm (d' - d) <= k
                            ==> norm(integral(interval[c',d']) f -
                                     integral(interval[c,d]) f) < e`;;

let BOUNDED_INTEGRALS_OVER_SUBINTERVALS = `!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> bounded { integral (interval[c,d]) f |
                      interval[c,d] SUBSET interval[a,b]}`;;

(* ------------------------------------------------------------------------- *)
(* Substitution.                                                             *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_SUBSTITUTION_STRONG = `!f:real^1->real^N g g' a b c d k.
        COUNTABLE k /\
        f integrable_on interval[c,d] /\
        g continuous_on interval[a,b] /\
        IMAGE g (interval[a,b]) SUBSET interval[c,d] /\
        (!x. x IN interval[a,b] DIFF k
                  ==> (g has_vector_derivative g'(x))
                       (at x within interval[a,b]) /\
                      f continuous
                        (at(g x)) within interval[c,d]) /\
        drop a <= drop b /\ drop c <= drop d /\ drop(g a) <= drop(g b)
        ==> ((\x. drop(g' x) % f(g x)) has_integral
             integral (interval[g a,g b]) f) (interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Second mean value theorem and corollaries.                                *)
(* ------------------------------------------------------------------------- *)

let SECOND_MEAN_VALUE_THEOREM_FULL = `!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\
        f integrable_on interval [a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (g(a) % integral (interval[a,c]) f +
                  g(b) % integral (interval[c,b]) f)) (interval[a,b])`;;

let SECOND_MEAN_VALUE_THEOREM = `!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\
        f integrable_on interval [a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                 g(a) % integral (interval[a,c]) f +
                 g(b) % integral (interval[c,b]) f`;;

let SECOND_MEAN_VALUE_THEOREM_GEN_FULL = `!f:real^1->real^1 g a b u v.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (u % integral (interval[a,c]) f +
                  v % integral (interval[c,b]) f)) (interval[a,b])`;;

let SECOND_MEAN_VALUE_THEOREM_GEN = `!f:real^1->real^1 g a b u v.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                u % integral (interval[a,c]) f +
                v % integral (interval[c,b]) f`;;

let SECOND_MEAN_VALUE_THEOREM_BONNET_FULL = `!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (g(b) % integral (interval[c,b]) f)) (interval[a,b])`;;

let SECOND_MEAN_VALUE_THEOREM_BONNET = `!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\ f integrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                g(b) % integral (interval[c,b]) f`;;

let INTEGRABLE_INCREASING_PRODUCT = `!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g(x) <= g(y))
        ==> (\x. g(x) % f(x)) integrable_on interval[a,b]`;;

let INTEGRABLE_INCREASING_PRODUCT_UNIV = `!f:real^1->real^N g B.
        f integrable_on (:real^1) /\
        (!x y. drop x <= drop y ==> g x <= g y) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x % f x) integrable_on (:real^1)`;;

let INTEGRABLE_INCREASING = `!f:real^1->real^N a b.
        (!x y i. x IN interval[a,b] /\ y IN interval[a,b] /\
                 drop x <= drop y /\ 1 <= i /\ i <= dimindex(:N)
                 ==> f(x)$i <= f(y)$i)
        ==> f integrable_on interval[a,b]`;;

let INTEGRABLE_INCREASING_1 = `!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> f integrable_on interval[a,b]`;;

let INTEGRABLE_DECREASING_PRODUCT = `!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g(y) <= g(x))
        ==> (\x. g(x) % f(x)) integrable_on interval[a,b]`;;

let INTEGRABLE_DECREASING_PRODUCT_UNIV = `!f:real^1->real^N g B.
        f integrable_on (:real^1) /\
        (!x y. drop x <= drop y ==> g y <= g x) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x % f x) integrable_on (:real^1)`;;

let INTEGRABLE_DECREASING = `!f:real^1->real^N a b.
        (!x y i. x IN interval[a,b] /\ y IN interval[a,b] /\
                 drop x <= drop y /\ 1 <= i /\ i <= dimindex(:N)
                 ==> f(y)$i <= f(x)$i)
        ==> f integrable_on interval[a,b]`;;

let INTEGRABLE_DECREASING_1 = `!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
        ==> f integrable_on interval[a,b]`;;

(* ------------------------------------------------------------------------- *)
(* Bounded variation and variation function, for real^1->real^N functions.   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_bounded_variation_on",(12,"right"));;

let has_bounded_variation_on = new_definition
 `(f:real^1->real^N) has_bounded_variation_on s <=>
        (\k. f(interval_upperbound k) - f(interval_lowerbound k))
        has_bounded_setvariation_on s`;;

let vector_variation = new_definition
 `vector_variation s (f:real^1->real^N) =
  set_variation s (\k. f(interval_upperbound k) - f(interval_lowerbound k))`;;

let VECTOR_VARIATION_DEGENERATES = `!f:real^1->real^N g s.
        ~(f has_bounded_variation_on s) /\
        ~(g has_bounded_variation_on s)
        ==> vector_variation s f = vector_variation s g`;;

let HAS_BOUNDED_VARIATION_ON_INTERVAL = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b] <=>
        ?B. !d. d division_of interval[a,b]
                ==> sum d (\k. norm(f(interval_upperbound k) -
                                    f(interval_lowerbound k))) <= B`;;

let VECTOR_VARIATION_ON_INTERVAL = `!f:real^1->real^N a b.
        vector_variation (interval[a,b]) f =
        sup {sum d (\k. norm(f(interval_upperbound k) -
                             f(interval_lowerbound k))) |
             d division_of interval[a,b]}`;;

let HAS_BOUNDED_VECTOR_VARIATION_ON_INTERVAL = `!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\
        vector_variation (interval[a,b]) f <= c <=>
        !d. d division_of interval[a,b]
                ==> sum d (\k. norm(f(interval_upperbound k) -
                                    f(interval_lowerbound k))) <= c`;;

let HAS_BOUNDED_VECTOR_VARIATION = `!f:real^1->real^N s c.
        f has_bounded_variation_on s /\ vector_variation s f <= c <=>
        !d t. d division_of t /\ t SUBSET s
              ==> sum d (\k. norm(f(interval_upperbound k) -
                                  f(interval_lowerbound k))) <= c`;;

let HAS_BOUNDED_VARIATION_WORKS = `!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> (!d t. d division_of t /\ t SUBSET s
                   ==> sum d (\k. norm(f(interval_upperbound k) -
                                       f(interval_lowerbound k))) <=
                       vector_variation s f) /\
            (!B. (!d t. d division_of t /\ t SUBSET s
                        ==> sum d (\k. norm(f(interval_upperbound k) -
                                       f(interval_lowerbound k))) <= B)
                   ==> vector_variation s f <= B)`;;

let HAS_BOUNDED_VARIATION_WORKS_ON_ELEMENTARY = `!f:real^1->real^N s.
        f has_bounded_variation_on s /\ (?d. d division_of s)
        ==> (!d. d division_of s
                 ==> sum d (\k. norm(f(interval_upperbound k) -
                                     f(interval_lowerbound k))) <=
                     vector_variation s f) /\
            (!B. (!d. d division_of s
                      ==> sum d (\k. norm(f(interval_upperbound k) -
                                     f(interval_lowerbound k))) <= B)
                  ==> vector_variation s f <= B)`;;

let HAS_BOUNDED_VARIATION_WORKS_ON_INTERVAL = `!f:real^1->real^N.
        f has_bounded_variation_on interval[a,b]
        ==> (!d. d division_of interval[a,b]
                 ==> sum d (\k. norm(f(interval_upperbound k) -
                                     f(interval_lowerbound k))) <=
                     vector_variation (interval[a,b]) f) /\
            (!B. (!d. d division_of interval[a,b]
                      ==> sum d (\k. norm(f(interval_upperbound k) -
                                     f(interval_lowerbound k))) <= B)
                  ==> vector_variation (interval[a,b]) f <= B)`;;

let HAS_BOUNDED_VECTOR_VARIATION_ON_INTERVAL_GEN = `!f:real^1->real^N s c.
        is_interval s
        ==> (f has_bounded_variation_on s /\ vector_variation s f <= c <=>
            !d a b. d division_of interval[a,b] /\ interval[a,b] SUBSET s
                    ==> sum d (\k. norm(f(interval_upperbound k) -
                                        f(interval_lowerbound k))) <= c)`;;

let HAS_BOUNDED_VECTOR_VARIATION_ON_SUBINTERVALS = `!f:real^1->real^N s c.
        is_interval s
        ==> (f has_bounded_variation_on s /\ vector_variation s f <= c <=>
             !a b. interval[a,b] SUBSET s
                   ==> f has_bounded_variation_on interval[a,b] /\
                       vector_variation (interval[a,b]) f <= c)`;;

let HAS_BOUNDED_VARIATION_ON_EQ = `!f g:real^1->real^N s.
        (!x. x IN s ==> f x = g x) /\ f has_bounded_variation_on s
        ==> g has_bounded_variation_on s`;;

let VECTOR_VARIATION_EQ = `!f g:real^1->real^N s.
        (!x. x IN s ==> f x = g x)
        ==> vector_variation s f = vector_variation s g`;;

let HAS_BOUNDED_VARIATION_ISOMETRIC = `!f g:real^1->real^N s.
        (!x y. dist(f x,f y) = dist(g x,g y))
        ==> (f has_bounded_variation_on s <=> g has_bounded_variation_on s)`;;

let HAS_BOUNDED_VARIATION_ISOMETRIC_COMPOSE = `!f:real^M->real^N g s.
        (!x y. dist(f x,f y) = dist(x,y))
        ==> ((f o g) has_bounded_variation_on s <=>
             g has_bounded_variation_on s)`;;

let VECTOR_VARIATION_ISOMETRIC = `!f g:real^1->real^N s.
        (!x y. dist(f x,f y) = dist(g x,g y))
        ==> vector_variation s f = vector_variation s g`;;

let VECTOR_VARIATION_ISOMETRIC_COMPOSE = `!f:real^M->real^N g s.
        (!x y. dist(f x,f y) = dist(x,y))
        ==> vector_variation s (f o g) = vector_variation s g`;;

let HAS_BOUNDED_VARIATION_ON_TRANSLATION = `!f:real^1->real^N s a.
   (\x. a + f x) has_bounded_variation_on s <=> f has_bounded_variation_on s`;;

let VECTOR_VARIATION_TRANSLATION = `!f:real^1->real^N s a.
        vector_variation s (\x. a + f x) = vector_variation s f`;;

let HAS_BOUNDED_VARIATION_ON_COMPONENTWISE = `!f:real^1->real^N s.
        f has_bounded_variation_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f x$i)) has_bounded_variation_on s`;;

let VARIATION_EQUAL_LEMMA = `!ms ms'.
        (!s. ms'(ms s) = s /\ ms(ms' s) = s) /\
        (!d t. d division_of t
               ==> (IMAGE (IMAGE ms) d) division_of IMAGE ms t /\
                   (IMAGE (IMAGE ms') d) division_of IMAGE ms' t) /\
        (!a b. ~(interval[a,b] = {})
               ==> IMAGE ms' (interval [a,b]) = interval[ms' a,ms' b] \/
                   IMAGE ms' (interval [a,b]) = interval[ms' b,ms' a])
   ==> (!f:real^1->real^N s.
            (\x. f(ms' x)) has_bounded_variation_on (IMAGE ms s) <=>
            f has_bounded_variation_on s) /\
       (!f:real^1->real^N s.
            vector_variation (IMAGE ms s) (\x. f(ms' x)) =
            vector_variation s f)`;;

let HAS_BOUNDED_VARIATION_COMPARISON = `!f:real^1->real^M g:real^1->real^N s.
        f has_bounded_variation_on s /\
        (!x y. x IN s /\ y IN s /\ drop x < drop y
               ==> dist(g x,g y) <= dist(f x,f y))
        ==> g has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_LIFT_ABS = `!f:real^1->real.
        (\x. lift(f x)) has_bounded_variation_on s
        ==> (\x. lift(abs(f x))) has_bounded_variation_on s`;;

let VECTOR_VARIATION_COMPARISON = `!f:real^1->real^M g:real^1->real^N s.
        f has_bounded_variation_on s /\
        (!x y. x IN s /\ y IN s /\ drop x < drop y
               ==> dist(g x,g y) <= dist(f x,f y))
        ==> vector_variation s g <= vector_variation s f`;;

let VECTOR_VARIATION_COMPONENT_LE = `!f:real^1->real^N s i.
        f has_bounded_variation_on s
        ==> vector_variation s (\x. lift(f x$i)) <= vector_variation s f`;;

let VECTOR_VARIATION_LIFT_ABS = `!f:real^1->real s.
        (\x. lift(f x)) has_bounded_variation_on s
        ==> vector_variation s (\x. lift(abs(f x)))
            <= vector_variation s (\x. lift(f x))`;;

let HAS_BOUNDED_VARIATION_ON_SUBSET = `!f:real^1->real^N s t.
        f has_bounded_variation_on s /\ t SUBSET s
        ==> f has_bounded_variation_on t`;;

let HAS_BOUNDED_VARIATION_ON_CONST = `!s c:real^N. (\x. c) has_bounded_variation_on s`;;

let VECTOR_VARIATION_CONST = `!s c:real^N. vector_variation s (\x. c) = &0`;;

let HAS_BOUNDED_VARIATION_ON_CMUL = `!f:real^1->real^N c s.
        f has_bounded_variation_on s
        ==> (\x. c % f x) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_CMUL_EQ = `!f:real^1->real^N c s.
        (\x. c % f x) has_bounded_variation_on s <=>
        c = &0 \/ f has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_VMUL_EQ = `!f s v:real^N.
        (\x. f(x) % v) has_bounded_variation_on s <=>
        v = vec 0 \/ (\x. lift(f x)) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_VMUL = `!f s v:real^N.
        (\x. lift(f x)) has_bounded_variation_on s
        ==> (\x. f(x) % v) has_bounded_variation_on s`;;

let VECTOR_VARIATION_CMUL = `!f:real^1->real^N s c.
        f has_bounded_variation_on s
        ==> vector_variation s (\x. c % f x) = abs c * vector_variation s f`;;

let VECTOR_VARIATION_VMUL = `!f s v:real^N.
        (\x. lift(f x)) has_bounded_variation_on s
        ==> vector_variation s (\x. f(x) % v) =
            norm(v) * vector_variation s (\x. lift(f x))`;;

let HAS_BOUNDED_VARIATION_ON_NEG = `!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> (\x. --f x) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_ADD = `!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> (\x. f x + g x) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_SUB = `!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> (\x. f x - g x) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_COMPOSE_LINEAR = `!f:real^1->real^M g:real^M->real^N s.
        f has_bounded_variation_on s /\ linear g
        ==> (g o f) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_NULL = `!f:real^1->real^N s.
        content s = &0 /\ bounded s ==> f has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_EMPTY = `!f:real^1->real^N. f has_bounded_variation_on {}`;;

let VECTOR_VARIATION_ON_NULL = `!f s. content s = &0 /\ bounded s ==> vector_variation s f = &0`;;

let VECTOR_VARIATION_ON_EMPTY = `!f:real^1->real^N. vector_variation {} f = &0`;;

let VECTOR_VARIATION_SING = `!f:real^1->real^N a. vector_variation {a} f = &0`;;

let HAS_BOUNDED_VARIATION_ON_NORM = `!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> (\x. lift(norm(f x))) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_MAX = `!f g s. f has_bounded_variation_on s /\ g has_bounded_variation_on s
           ==> (\x. lift(max (drop(f x)) (drop(g x))))
               has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_MIN = `!f g s. f has_bounded_variation_on s /\ g has_bounded_variation_on s
           ==> (\x. lift(min (drop(f x)) (drop(g x))))
               has_bounded_variation_on s`;;

let BOUNDED_VECTOR_VARIATION_ON_PASTECART = `!f:real^1->real^N g:real^1->real^P s.
        f has_bounded_variation_on s /\
        g has_bounded_variation_on s
        ==> (\x. pastecart (f x) (g x)) has_bounded_variation_on s /\
            vector_variation s (\x. pastecart (f x) (g x)) <=
                vector_variation s f + vector_variation s g`;;

let BOUNDED_VARIATION_FROM_PASTECART = `!f:real^1->real^N g:real^1->real^P s.
      (\x. pastecart (f x) (g x)) has_bounded_variation_on s
      ==> (f has_bounded_variation_on s /\
           vector_variation s f
           <= vector_variation s (\x. pastecart (f x) (g x))) /\
          (g has_bounded_variation_on s /\
           vector_variation s g
           <= vector_variation s (\x. pastecart (f x) (g x)))`;;

let HAS_BOUNDED_VARIATION_ON_PASTECART = `!f:real^1->real^N g:real^1->real^P s.
        (\x. pastecart (f x) (g x)) has_bounded_variation_on s <=>
        f has_bounded_variation_on s /\ g has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS = `!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> bounded { f(d) - f(c) | interval[c,d] SUBSET s /\
                                    ~(interval[c,d] = {})}`;;

let HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED = `!f:real^1->real^N s.
        f has_bounded_variation_on s /\ is_interval s ==> bounded (IMAGE f s)`;;

let HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_INTERVAL = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> bounded(IMAGE f (interval[a,b]))`;;

let HAS_BOUNDED_VARIATION_ON_BILINEAR = `!bop:real^M->real^N->real^P f g s.
        bilinear bop /\
        f has_bounded_variation_on s /\
        g has_bounded_variation_on s /\
        is_interval s
        ==> (\x. bop (f x) (g x)) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_MUL = `!f g:real^1->real^N s.
        f has_bounded_variation_on s /\
        g has_bounded_variation_on s /\
        is_interval s
        ==> (\x. drop(f x) % g x) has_bounded_variation_on s`;;

let VECTOR_VARIATION_POS_LE = `!f:real^1->real^N s.
        f has_bounded_variation_on s ==> &0 <= vector_variation s f`;;

let VECTOR_VARIATION_GE_NORM_FUNCTION = `!f:real^1->real^N s a b.
        f has_bounded_variation_on s /\ segment[a,b] SUBSET s
        ==> norm(f b - f a) <= vector_variation s f`;;

let VECTOR_VARIATION_GE_DROP_FUNCTION = `!f s a b.
        f has_bounded_variation_on s /\ segment[a,b] SUBSET s
        ==> drop(f b) - drop(f a) <= vector_variation s f`;;

let VECTOR_VARIATION_CONST_EQ = `!f:real^1->real^N s.
        is_interval s /\ f has_bounded_variation_on s
        ==> (vector_variation s f = &0 <=> ?c. !x. x IN s ==> f x = c)`;;

let VECTOR_VARIATION_MONOTONE = `!f s t. f has_bounded_variation_on s /\ t SUBSET s
           ==> vector_variation t f <= vector_variation s f`;;

let VECTOR_VARIATION_NEG = `!f:real^1->real^N s.
        vector_variation s (\x. --(f x)) = vector_variation s f`;;

let VECTOR_VARIATION_TRIANGLE = `!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> vector_variation s (\x. f x + g x)
              <= vector_variation s f + vector_variation s g`;;

let HAS_BOUNDED_VARIATION_ON_VSUM = `(!f:A->real^1->real^N s k.
        FINITE k /\
        (!i. i IN k ==> f i has_bounded_variation_on s)
        ==> (\x. vsum k (\i. f i x)) has_bounded_variation_on s)`
and VECTOR_VARIATION_SUM_LE = `(!f:A->real^1->real^N s k.
        FINITE k /\
        (!i. i IN k ==> f i has_bounded_variation_on s)
        ==> vector_variation s (\x. vsum k (\i. f i x))
            <= sum k (\i. vector_variation s (f i)))`;;

let OPERATIVE_FUNCTION_ENDPOINT_DIFF = `!f:real^1->real^N.
    operative (+) (\k. f (interval_upperbound k) - f (interval_lowerbound k))`;;

let OPERATIVE_REAL_FUNCTION_ENDPOINT_DIFF = `!f:real^1->real.
    operative (+) (\k. f (interval_upperbound k) - f (interval_lowerbound k))`;;

let OPERATIVE_HAS_BOUNDED_VARIATION_ON = `!f:real^1->real^N.
        operative (/\) ((has_bounded_variation_on) f)`;;

let OPERATIVE_LIFTED_VECTOR_VARIATION = `!f:real^1->real^N.
        operative (lifted(+))
                  (\i. if f has_bounded_variation_on i
                       then SOME(vector_variation i f) else NONE)`;;

let HAS_BOUNDED_VARIATION_ON_DIVISION = `!f:real^1->real^N a b d.
        d division_of interval[a,b]
        ==> ((!k. k IN d ==> f has_bounded_variation_on k) <=>
             f has_bounded_variation_on interval[a,b])`;;

let VECTOR_VARIATION_ON_DIVISION = `!f:real^1->real^N a b d.
        d division_of interval[a,b] /\
        f has_bounded_variation_on interval[a,b]
        ==> sum d (\k. vector_variation k f) =
            vector_variation (interval[a,b]) f`;;

let HAS_BOUNDED_VARIATION_ON_CLOSURE = `!f:real^1->real^N s.
        is_interval s /\ f has_bounded_variation_on s
        ==> f has_bounded_variation_on (closure s)`;;

let HAS_BOUNDED_VARIATION_ON_CLOSURE_EQ = `!f:real^1->real^N s.
        is_interval s
        ==> (f has_bounded_variation_on closure s <=>
             f has_bounded_variation_on s)`;;

let HAS_BOUNDED_VARIATION_ON_SING = `!f a. f has_bounded_variation_on {a}`;;

let VECTOR_VARIATION_LE_UNION = `!f:real^1->real^N s t.
        f has_bounded_variation_on (s UNION t) /\
        interior s INTER interior t = {}
        ==> vector_variation s f + vector_variation t f
            <= vector_variation (s UNION t) f`;;

let HAS_BOUNDED_VARIATION_ON_UNION = `(!f:real^1->real^N s t.
        is_interval s /\ is_interval t /\
        f has_bounded_variation_on s /\ f has_bounded_variation_on t
        ==> f has_bounded_variation_on (s UNION t))`
and VECTOR_VARIATION_UNION_LE = `(!f:real^1->real^N s t.
        is_interval s /\ is_interval t /\
        (s INTER t = {}
         ==> s INTER closure t = {} /\ t INTER closure s = {}) /\
        f has_bounded_variation_on s /\ f has_bounded_variation_on t
        ==> vector_variation (s UNION t) f <=
            vector_variation s f + vector_variation t f)`;;

let HAS_BOUNDED_VARIATION_ON_SPLIT = `!f:real^1->real^N s a.
        is_interval s
        ==> (f has_bounded_variation_on s <=>
             f has_bounded_variation_on {x | x IN s /\ drop x <= a} /\
             f has_bounded_variation_on {x | x IN s /\ a <= drop x})`;;

let VECTOR_VARIATION_SPLIT = `!f:real^1->real^N s a.
        is_interval s /\ f has_bounded_variation_on s
        ==> vector_variation {x | x IN s /\ drop x <= a} f +
            vector_variation {x | x IN s /\ a <= drop x} f =
            vector_variation s f`;;

let HAS_BOUNDED_VARIATION_ON_COMBINE = `!f:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b
        ==> (f has_bounded_variation_on interval[a,b] <=>
             f has_bounded_variation_on interval[a,c] /\
             f has_bounded_variation_on interval[c,b])`;;

let VECTOR_VARIATION_COMBINE = `!f:real^1->real^N a b c.
        drop a <= drop c /\
        drop c <= drop b /\
        f has_bounded_variation_on interval[a,b]
        ==> vector_variation (interval[a,c]) f +
            vector_variation (interval[c,b]) f =
            vector_variation (interval[a,b]) f`;;

let VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE_LEFT = `!f s a b.
        f has_bounded_variation_on s /\ is_interval s /\
        a IN s /\ b IN s /\ drop a <= drop b
        ==> vector_variation {x | x IN s /\ drop x <= drop a} f - drop(f a) <=
            vector_variation {x | x IN s /\ drop x <= drop b} f - drop(f b)`;;

let VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE_RIGHT = `!f s a b.
        f has_bounded_variation_on s /\ is_interval s /\
        a IN s /\ b IN s /\ drop a <= drop b
        ==> vector_variation {x | x IN s /\ drop b <= drop x} f - drop(f b) <=
            vector_variation {x | x IN s /\ drop a <= drop x} f - drop(f a)`;;

let VECTOR_VARIATION_SEGMENT_TRIANGLE = `!f:real^1->real^N s a b c.
        f has_bounded_variation_on s /\
        is_interval s /\ a IN s /\ b IN s /\ c IN s
        ==> vector_variation (segment[a,c]) f <=
            vector_variation (segment[a,b]) f +
            vector_variation (segment[b,c]) f`;;

let HAS_BOUNDED_VARIATION_ON_VECTOR_VARIATION = `(!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> (\x. lift(vector_variation (interval [a,x]) f))
            has_bounded_variation_on interval[a,b])`
and VECTOR_VARIATION_VECTOR_VARIATION = `(!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> vector_variation (interval[a,b])
                             (\x. lift(vector_variation (interval [a,x]) f)) =
            vector_variation (interval[a,b]) f)`;;

let VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE = `!f a b c d.
        f has_bounded_variation_on interval[a,b] /\
        interval[c,d] SUBSET interval[a,b] /\ ~(interval[c,d] = {})
        ==> vector_variation (interval[c,d]) f - drop(f d - f c) <=
            vector_variation (interval[a,b]) f - drop(f b - f a)`;;

let HAS_BOUNDED_VARIATION_NONTRIVIAL = `!f:real^1->real^N s.
        f has_bounded_variation_on s <=>
        ?B. !d t.
                  d division_of t /\ t SUBSET s /\
                  (!k. k IN d ==> ~(interior k = {}))
                  ==> sum d (\k. norm(f(interval_upperbound k) -
                                      f (interval_lowerbound k))) <= B`;;

let INCREASING_BOUNDED_VARIATION_GEN = `!f s.
      bounded(IMAGE f s) /\
      (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f x) <= drop(f y))
       ==> f has_bounded_variation_on s`;;

let DECREASING_BOUNDED_VARIATION_GEN = `!f s.
      bounded(IMAGE f s) /\
      (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f y) <= drop(f x))
       ==> f has_bounded_variation_on s`;;

let INCREASING_BOUNDED_VARIATION = `!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> f has_bounded_variation_on interval[a,b]`;;

let DECREASING_BOUNDED_VARIATION = `!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
         ==> f has_bounded_variation_on interval[a,b]`;;

let INCREASING_VECTOR_VARIATION = `!f a b.
        ~(interval[a,b] = {}) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> vector_variation (interval[a,b]) f = drop(f b) - drop(f a)`;;

let DECREASING_VECTOR_VARIATION = `!f a b.
        ~(interval[a,b] = {}) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
        ==> vector_variation (interval[a,b]) f = drop(f a) - drop(f b)`;;

let VECTOR_VARIATION_ID = `!a b. vector_variation (interval[a,b]) (\x. x) =
         if interval[a,b] = {} then &0 else drop b - drop a`;;

let HAS_BOUNDED_VARIATION_TRANSLATION2_EQ = `(!a f:real^1->real^N s.
        (\x. f(a + x)) has_bounded_variation_on (IMAGE (\x. --a + x) s) <=>
        f has_bounded_variation_on s)`
and VECTOR_VARIATION_TRANSLATION2 = `(!a f:real^1->real^N s.
        vector_variation (IMAGE (\x. --a + x) s) (\x. f(a + x)) =
        vector_variation s f)`;;

let HAS_BOUNDED_VARIATION_AFFINITY2_EQ = `(!m c f:real^1->real^N s.
        (\x. f (m % x + c)) has_bounded_variation_on
        IMAGE (\x. inv m % x + --(inv m % c)) s <=>
        m = &0 \/ f has_bounded_variation_on s)`
and VECTOR_VARIATION_AFFINITY2 = `(!m c f:real^1->real^N s.
        vector_variation (IMAGE (\x. inv m % x + --(inv m % c)) s)
                         (\x. f (m % x + c)) =
        if m = &0 then &0 else vector_variation s f)`;;

let HAS_BOUNDED_VARIATION_AFFINITY_EQ = `(!m c f:real^1->real^N s.
        (\x. f(m % x + c)) has_bounded_variation_on s <=>
        m = &0 \/ f has_bounded_variation_on (IMAGE (\x. m % x + c) s))`
and VECTOR_VARIATION_AFFINITY = `(!m c f:real^1->real^N s.
        vector_variation s (\x. f(m % x + c)) =
        if m = &0 then &0 else vector_variation (IMAGE (\x. m % x + c) s) f)`;;

let HAS_BOUNDED_VARIATION_TRANSLATION_EQ = `(!a f:real^1->real^N s.
        (\x. f(a + x)) has_bounded_variation_on s <=>
        f has_bounded_variation_on (IMAGE (\x. a + x) s))`
and VECTOR_VARIATION_TRANSLATION_ALT = `(!a f:real^1->real^N s.
        vector_variation s (\x. f(a + x)) =
        vector_variation (IMAGE (\x. a + x) s) f)`;;

let HAS_BOUNDED_VARIATION_TRANSLATION_EQ_INTERVAL = `(!a f:real^1->real^N u v.
        (\x. f(a + x)) has_bounded_variation_on interval[u,v] <=>
        f has_bounded_variation_on interval[a+u,a+v])`
and VECTOR_VARIATION_TRANSLATION_INTERVAL = `(!a f:real^1->real^N u v.
        vector_variation (interval[u,v]) (\x. f(a + x)) =
        vector_variation (interval[a+u,a+v]) f)`;;

let HAS_BOUNDED_VARIATION_TRANSLATION = `!f:real^1->real^N s a.
        f has_bounded_variation_on s
        ==> (\x. f(a + x)) has_bounded_variation_on (IMAGE (\x. --a + x) s)`;;

let HAS_BOUNDED_VARIATION_REFLECT2_EQ = `(!f:real^1->real^N s.
        (\x. f(--x)) has_bounded_variation_on (IMAGE (--) s) <=>
        f has_bounded_variation_on s)`
and VECTOR_VARIATION_REFLECT2 = `(!f:real^1->real^N s.
        vector_variation (IMAGE (--) s) (\x. f(--x)) =
        vector_variation s f)`;;

let HAS_BOUNDED_VARIATION_REFLECT_EQ = `(!f:real^1->real^N s.
        (\x. f(--x)) has_bounded_variation_on s <=>
        f has_bounded_variation_on (IMAGE (--) s))`
and VECTOR_VARIATION_REFLECT = `(!f:real^1->real^N s.
        vector_variation s (\x. f(--x)) =
        vector_variation (IMAGE (--) s) f)`;;

let HAS_BOUNDED_VARIATION_REFLECT_EQ_INTERVAL = `(!f:real^1->real^N u v.
        (\x. f(--x)) has_bounded_variation_on interval[u,v] <=>
        f has_bounded_variation_on interval[--v,--u])`
and VECTOR_VARIATION_REFLECT_INTERVAL = `(!f:real^1->real^N u v.
        vector_variation (interval[u,v]) (\x. f(--x)) =
        vector_variation (interval[--v,--u]) f)`;;

let HAS_BOUNDED_VARIATION_DARBOUX_GEN = `!f s. is_interval s /\ f has_bounded_variation_on s
         ==> ?g h. (!x y. x IN s /\ y IN s /\ drop x <= drop y
                          ==> drop(g x) <= drop(g y)) /\
                   (!x y. x IN s /\ y IN s /\ drop x <= drop y
                          ==> drop(h x) <= drop(h y)) /\
                   (!x. f x = g x - h x)`;;

let HAS_BOUNDED_VARIATION_DARBOUX = `!f a b.
     f has_bounded_variation_on interval[a,b] <=>
     ?g h. (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                  ==> drop(g x) <= drop(g y)) /\
           (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                  ==> drop(h x) <= drop(h y)) /\
           (!x. f x = g x - h x)`;;

let HAS_BOUNDED_VARIATION_DARBOUX_STRICT = `!f a b.
     f has_bounded_variation_on interval[a,b] <=>
     ?g h. (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                  ==> drop(g x) < drop(g y)) /\
           (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                  ==> drop(h x) < drop(h y)) /\
           (!x. f x = g x - h x)`;;

let HAS_BOUNDED_VARIATION_ON_REFLECT = `!f:real^1->real^N s.
        f has_bounded_variation_on IMAGE (--) s
        ==> (\x. f(--x)) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_REFLECT_INTERVAL = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[--b,--a]
        ==> (\x. f(--x)) has_bounded_variation_on interval[a,b]`;;

let HAS_BOUNDED_VARIATION_COMPOSE_INCREASING = `(!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        g has_bounded_variation_on interval[f a,f b]
        ==> (g o f) has_bounded_variation_on interval[a,b])`
and VECTOR_VARIATION_COMPOSE_INCREASING = `(!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        g has_bounded_variation_on interval[f a,f b]
        ==> vector_variation (interval[a,b]) (g o f)
            <= vector_variation (interval[f a,f b]) g)`;;

let HAS_BOUNDED_VARIATION_COMPOSE_DECREASING = `!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        g has_bounded_variation_on interval[f b,f a]
        ==> (g o f) has_bounded_variation_on interval[a,b]`;;

let VECTOR_VARIATION_COMPOSE_DECREASING = `!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        g has_bounded_variation_on interval[f b,f a]
        ==> vector_variation (interval[a,b]) (g o f)
            <= vector_variation (interval[f b,f a]) g`;;

let HAS_BOUNDED_VARIATION_COMPOSE_INCREASING_GEN = `(!f g:real^1->real^N s t.
        is_interval s /\ is_interval t /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        g has_bounded_variation_on t
        ==> (g o f) has_bounded_variation_on s)`
and VECTOR_VARIATION_COMPOSE_INCREASING_GEN = `(!f g:real^1->real^N s t.
        is_interval s /\ is_interval t /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        g has_bounded_variation_on t
        ==> vector_variation s (g o f) <= vector_variation t g)`;;

let HAS_BOUNDED_VARIATION_COMPOSE_HOMEOMORPHISM = `!f f' g:real^1->real^N s t.
        is_interval s /\ homeomorphism (s,t) (f,f') /\
        g has_bounded_variation_on t
        ==> (g o f) has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_COMPOSE_INJECTIVE = `!f g:real^1->real^N s.
        is_interval s /\ f continuous_on s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        g has_bounded_variation_on (IMAGE f s)
        ==> (g o f) has_bounded_variation_on s`;;

let VECTOR_VARIATION_COMPOSE_HOMEOMORPHISM = `!f f' g:real^1->real^N s t.
        is_interval s /\ homeomorphism (s,t) (f,f') /\
        g has_bounded_variation_on t
        ==> vector_variation s (g o f) = vector_variation t g`;;

let HAS_BOUNDED_VARIATION_ON_ID = `!s:real^1->bool. bounded s ==> (\x. x) has_bounded_variation_on s`;;

let LINEAR_IMP_HAS_BOUNDED_VARIATION = `!f:real^1->real^N.
        linear f /\ bounded s ==> f has_bounded_variation_on s`;;

let VECTOR_VARIATION_LINEAR = `!f:real^1->real^N a b.
        linear f /\ drop a <= drop b
        ==> vector_variation(interval[a,b]) f = dist(f a,f b)`;;

let HAS_BOUNDED_VARIATION_LIPSCHITZ_COMPOSE = `!f:real^M->real^N g s B.
        g has_bounded_variation_on s /\
        (!x y. x IN IMAGE g s /\ y IN IMAGE g s
               ==> norm(f x - f y) <= B * norm(x - y))
        ==> (f o g) has_bounded_variation_on s`;;

let LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION = `!f:real^1->real^N s B.
        bounded s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> f has_bounded_variation_on s`;;

let VECTOR_VARIATION_LIPSCHITZ = `!f:real^1->real^N a b l.
        drop a <= drop b /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b]
               ==> norm(f x - f y) <= l * norm(x - y))
        ==> vector_variation (interval[a,b]) f <= l * (drop b - drop a)`;;

let LIPSCHITZ_VECTOR_VARIATION = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> ((!x y. x IN interval[a,b] /\ y IN interval[a,b]
                    ==> abs(vector_variation (interval[a,x]) f -
                            vector_variation (interval[a,y]) f)
                        <= B * norm(x - y)) <=>
             (!x y. x IN interval[a,b] /\ y IN interval[a,b]
                    ==> norm(f x - f y) <= B * norm(x - y)))`;;

let HAS_BOUNDED_VECTOR_DERIVATIVE_IMP_HAS_BOUNDED_VARIATION_ON = `!f:real^1->real^N f' s.
        (!x. x IN s ==> (f has_vector_derivative f'(x)) (at x within s)) /\
        convex s /\ bounded s /\ bounded(IMAGE f' s)
        ==> f has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_LINEAR_IMAGE = `!f:real^1->real^1 g:real^1->real^N a b.
        linear f /\ g has_bounded_variation_on IMAGE f (interval[a,b])
        ==> (g o f) has_bounded_variation_on interval[a,b]`;;

let HAS_BOUNDED_VARIATION_ON_COMBINE_GEN = `!f:real^1->real^N s a.
        is_interval s
        ==> (f has_bounded_variation_on s <=>
             f has_bounded_variation_on {x | x IN s /\ drop x <= a} /\
             f has_bounded_variation_on {x | x IN s /\ drop x >= a})`;;

let HAS_BOUNDED_VARIATION_ON_INTERIOR = `!f:real^1->real^N s.
        f has_bounded_variation_on (interior s) /\
        (is_interval s \/ f continuous_on s)
        ==> f has_bounded_variation_on s`;;

let HAS_BOUNDED_VARIATION_ON_INTERIOR_EQ = `!f:real^1->real^N s.
        is_interval s \/ f continuous_on s
        ==> (f has_bounded_variation_on interior s <=>
             f has_bounded_variation_on s)`;;

let CONVEX_HAS_BOUNDED_VARIATION_EQ = `!f s. (drop o f) convex_on s /\ is_interval s
         ==> (f has_bounded_variation_on s <=> bounded(IMAGE f s))`;;

let CONVEX_HAS_BOUNDED_VARIATION = `!f a b.
        f convex_on interval[a,b]
        ==> (lift o f) has_bounded_variation_on interval[a,b]`;;

let HAS_BOUNDED_VECTOR_VARIATION_UNIFORM_LIM = `!f:num->real^1->real^N g s b.
        (!n. (f n) has_bounded_variation_on s) /\
        (!n. vector_variation s (f n) <= b) /\
        (!x. x IN s ==> ((\n. f n x) --> g x) sequentially)
        ==> g has_bounded_variation_on s /\ vector_variation s g <= b`;;

let INCREASING_LEFT_LIMIT_1 = `!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[a,c])`;;

let DECREASING_LEFT_LIMIT_1 = `!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[a,c])`;;

let INCREASING_RIGHT_LIMIT_1 = `!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[c,b])`;;

let DECREASING_RIGHT_LIMIT_1 = `!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[c,b])`;;

let HAS_BOUNDED_VECTOR_VARIATION_LEFT_LIMIT = `!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[a,c])`;;

let HAS_BOUNDED_VECTOR_VARIATION_RIGHT_LIMIT = `!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[c,b])`;;

let HAS_BOUNDED_VARIATION_RIGHT_LIMIT_GEN = `!f:real^1->real^N s a.
        f has_bounded_variation_on s /\ is_interval s
        ==> ?l. (f --> l) (at a within {x | x IN s /\ drop a <= drop x})`;;

let HAS_BOUNDED_VARIATION_LEFT_LIMIT_GEN = `!f:real^1->real^N s a.
        f has_bounded_variation_on s /\ is_interval s
        ==> ?l. (f --> l) (at a within {x | x IN s /\ drop x <= drop a})`;;

let INCREASING_LEFT_LIMIT_1_GEN = `!f s a B.
     is_interval s /\
     (!x. x IN s ==> drop(f x) <= B) /\
     (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f x) <= drop(f y))
      ==> ?l. (f --> l) (at a within {x | x IN s /\ drop x <= drop a})`;;

let DECREASING_LEFT_LIMIT_1_GEN = `!f s a B.
     is_interval s /\
     (!x. x IN s ==> B <= drop(f x)) /\
     (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f y) <= drop(f x))
      ==> ?l. (f --> l) (at a within {x | x IN s /\ drop x <= drop a})`;;

let INCREASING_RIGHT_LIMIT_1_GEN = `!f s a B.
     is_interval s /\
     (!x. x IN s ==> B <= drop(f x)) /\
     (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f x) <= drop(f y))
      ==> ?l. (f --> l) (at a within {x | x IN s /\ drop a <= drop x})`;;

let DECREASING_RIGHT_LIMIT_1_GEN = `!f s a B.
     is_interval s /\
     (!x. x IN s ==> drop(f x) <= B) /\
     (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f y) <= drop(f x))
      ==> ?l. (f --> l) (at a within {x | x IN s /\ drop a <= drop x})`;;

let VECTOR_VARIATION_CONTINUOUS_LEFT = `!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[a,c]) <=>
            f continuous (at c within interval[a,c]))`;;

let VECTOR_VARIATION_CONTINUOUS_RIGHT = `!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[c,b]) <=>
            f continuous (at c within interval[c,b]))`;;

let VECTOR_VARIATION_CONTINUOUS = `!f:real^1->real^N a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[a,b]) <=>
            f continuous (at c within interval[a,b]))`;;

let CONTINUOUS_ON_VECTOR_VARIATION = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b] /\
        f continuous_on interval[a,b]
        ==> (\x. lift (vector_variation (interval [a,x]) f)) continuous_on
            interval[a,b]`;;

let HAS_BOUNDED_VARIATION_DARBOUX_STRONG = `!f a b.
     f has_bounded_variation_on interval[a,b]
     ==> ?g h. (!x. f x = g x - h x) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x <= drop y
                      ==> drop(g x) <= drop(g y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x <= drop y
                      ==> drop(h x) <= drop(h y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x < drop y
                      ==> drop(g x) < drop(g y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x < drop y
                      ==> drop(h x) < drop(h y)) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[a,x])
                    ==> g continuous (at x within interval[a,x]) /\
                        h continuous (at x within interval[a,x])) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[x,b])
                    ==> g continuous (at x within interval[x,b]) /\
                        h continuous (at x within interval[x,b])) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[a,b])
                    ==> g continuous (at x within interval[a,b]) /\
                        h continuous (at x within interval[a,b]))`;;

let INCREASING_COUNTABLE_DISCONTINUITIES = `!f s. is_interval s /\
         (!x y. x IN s /\ y IN s /\ drop x <= drop y
                ==> drop(f x) <= drop(f y))
         ==> COUNTABLE {x | x IN s /\ ~(f continuous at x)}`;;

let DECREASING_COUNTABLE_DISCONTINUITIES = `!f s. is_interval s /\
         (!x y. x IN s /\ y IN s /\ drop x <= drop y
                ==> drop(f y) <= drop(f x))
         ==> COUNTABLE {x | x IN s /\ ~(f continuous at x)}`;;

let HAS_BOUNDED_VARIATION_COUNTABLE_DISCONTINUITIES = `!f:real^1->real^N s.
        f has_bounded_variation_on s /\ is_interval s
        ==> COUNTABLE {x | x IN s /\ ~(f continuous at x)}`;;

let HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE = `!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x)
        ==> (f has_bounded_variation_on interval[a,b] <=>
             (\x. vector_derivative f (at x))
             absolutely_integrable_on interval[a,b])`;;

let HAS_BOUNDED_VARIATION_INTEGRABLE_NORM_DERIVATIVE = `!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x)
        ==> (f has_bounded_variation_on interval[a,b] <=>
             (\x. lift(norm(vector_derivative f (at x))))
             integrable_on interval[a,b])`;;

let VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE = `!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x) /\
        f has_bounded_variation_on interval[a,b]
        ==> vector_variation (interval[a,b]) f =
                drop(integral (interval[a,b])
                        (\x. lift(norm(vector_derivative f (at x)))))`;;

let INTEGRABLE_BOUNDED_VARIATION_PRODUCT = `!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. drop(g x) % f x) integrable_on interval[a,b]`;;

let INTEGRABLE_BOUNDED_VARIATION_PRODUCT_ALT = `!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (lift o g) has_bounded_variation_on interval[a,b]
        ==> (\x. g x % f x) integrable_on interval[a,b]`;;

let INTEGRABLE_BOUNDED_VARIATION_BILINEAR_LMUL = `!op:real^M->real^N->real^P f g a b.
        bilinear op /\
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. op (g x) (f x)) integrable_on interval[a,b]`;;

let INTEGRABLE_BOUNDED_VARIATION_BILINEAR_RMUL = `!op:real^M->real^N->real^P f g a b.
        bilinear op /\
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. op (f x) (g x)) integrable_on interval[a,b]`;;

let INTEGRABLE_BOUNDED_VARIATION = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> f integrable_on interval[a,b]`;;

let HAS_BOUNDED_VARIATION_ON_INDEFINITE_INTEGRAL_RIGHT = `!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\c. integral (interval[a,c]) f) has_bounded_variation_on
            interval[a,b]`;;

let HAS_BOUNDED_VARIATION_ON_INDEFINITE_INTEGRAL_LEFT = `!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\c. integral (interval[c,b]) f) has_bounded_variation_on
            interval[a,b]`;;

let CONTINUOUS_BV_IMP_UNIFORMLY_CONTINUOUS = `!f:real^1->real^N s.
        is_interval s /\
        f continuous_on s /\ f has_bounded_variation_on s
        ==> f uniformly_continuous_on s`;;

let HAS_BOUNDED_VARIATION_ON_DARBOUX_IMP_CONTINUOUS = `!f:real^1->real^N s.
      is_interval s /\ f has_bounded_variation_on s /\
      (!c. c SUBSET s /\ connected c ==> connected(IMAGE f c))
      ==> f continuous_on s`;;

let VECTOR_VARIATION_ON_INTERIOR = `!f:real^1->real^N s.
        is_interval s /\
        f has_bounded_variation_on (interior s) /\
        f continuous_on s
        ==> vector_variation (interior s) f = vector_variation s f`;;

let VECTOR_VARIATION_ON_CLOSURE = `!f:real^1->real^N s.
        is_interval s /\
        f has_bounded_variation_on s /\
        f continuous_on closure s
        ==> vector_variation (closure s) f = vector_variation s f`;;

let HAS_BOUNDED_VARIATION_IMP_BAIRE1 = `!f:real^1->real^N s.
        f has_bounded_variation_on s /\ is_interval s ==> baire 1 s f`;;

let INCREASING_IMP_BAIRE1 = `!f s.
        is_interval s /\
        (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f x) <= drop(f y))
        ==> baire 1 s f`;;

let DECREASING_IMP_BAIRE1 = `!f s.
        is_interval s /\
        (!x y. x IN s /\ y IN s /\ drop x <= drop y ==> drop(f y) <= drop(f x))
        ==> baire 1 s f`;;

(* ------------------------------------------------------------------------- *)
(* We can factor a BV function through its variation. Moreover the           *)
(* factor is Lipschitz and continuous on its domain, though without          *)
(* continuity of the original function that domain may not be an interval.   *)
(* ------------------------------------------------------------------------- *)

let FACTOR_THROUGH_VARIATION = `!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> ?g. (!x. x IN interval[a,b]
                     ==> f(x) = g(lift(vector_variation(interval[a,x]) f))) /\
                g continuous_on
                 { lift(vector_variation(interval[a,u]) f) |u|
                   u IN interval[a,b]} /\
                (!x y. x IN { lift(vector_variation(interval[a,u]) f) |u|
                              u IN interval[a,b]} /\
                       y IN { lift(vector_variation(interval[a,u]) f) |u|
                              u IN interval[a,b]}
                       ==> dist(g x,g y) <= dist(x,y))`;;

let FACTOR_CONTINUOUS_THROUGH_VARIATION = `!f:real^1->real^N a b l.
        drop a <= drop b /\
        f continuous_on interval[a,b] /\
        f has_bounded_variation_on interval[a,b] /\
        vector_variation(interval[a,b]) f = drop l
        ==> ?g. (!x. x IN interval[a,b]
                     ==> f(x) = g(lift(vector_variation(interval[a,x]) f))) /\
                g continuous_on interval[vec 0,l] /\
                (!u v. u IN interval[vec 0,l] /\ v IN interval[vec 0,l]
                       ==> dist(g u,g v) <= dist(u,v)) /\
                g has_bounded_variation_on interval[vec 0,l] /\
                IMAGE (\x. lift(vector_variation(interval[a,x]) f))
                      (interval[a,b]) = interval[vec 0,l] /\
                IMAGE g (interval[vec 0,l]) = IMAGE f (interval[a,b]) /\
                (!x. x IN interval[vec 0,l]
                     ==> vector_variation (interval[vec 0,x]) g = drop x)`;;

(* ------------------------------------------------------------------------- *)
(* The Helly selection theorem.                                              *)
(* ------------------------------------------------------------------------- *)

let HELLY_SELECTION_INCREASING = `!f:num->real^1->real^1 s k.
      is_interval s /\
      (!n x. x IN s ==> norm(f n x) <= k) /\
      (!n x y. x IN s /\ y IN s /\ drop x <= drop y
               ==> drop(f n x) <= drop(f n y))
      ==> ?r g. (!m n. m < n ==> r m < r n) /\
                (!x. x IN s ==> ((\n. f (r n) x) --> g x) sequentially) /\
                (!x. x IN s ==> norm(g x) <= k) /\
                (!x y. x IN s /\ y IN s /\ drop x <= drop y
                       ==> drop(g x) <= drop(g y))`;;

let HELLY_SELECTION_THEOREM = `!f:num->real^1->real^N s c d.
        is_interval s /\
        (!n. f n has_bounded_variation_on s) /\
        (!n. vector_variation s (f n) <= c) /\
        (!n x. x IN s ==> norm(f n x) <= d)
        ==> ?r g. (!m n. m < n ==> r m < r n) /\
                  (!x. x IN s ==> ((\n. f (r n) x) --> g x) sequentially) /\
                  g has_bounded_variation_on s /\
                  vector_variation s g <= c`;;

(* ------------------------------------------------------------------------- *)
(* Differentiability properties of convex functions.                         *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_RIGHT_DIFFERENTIABLE = `!f s a.
        f convex_on s /\ a IN interior s
        ==> (lift o f) differentiable (at a within {x | drop a <= drop x})`;;

let CONVEX_ON_LEFT_DIFFERENTIABLE = `!f s a.
        f convex_on s /\ a IN interior s
        ==> (lift o f) differentiable (at a within {x | drop x <= drop a})`;;

let CONVEX_ON_DIRECTIONAL_DERIVATIVES = `!f s a.
        f convex_on s /\ a IN interior s
        ==> ?l r. ((lift o f) has_vector_derivative l)
                   (at a within {x | drop x <= drop a}) /\
                  ((lift o f) has_vector_derivative r)
                   (at a within {x | drop a <= drop x}) /\
                  drop l <= drop r`;;

let CONVEX_ON_DIRECTIONAL_DERIVATIVE_FUNCTIONS = `!f s. f convex_on s /\ is_interval s /\ open s
         ==> ?l r. (!x. x IN s ==> ((lift o f) has_vector_derivative l(x))
                                   (at x within {t | drop t <= drop x})) /\
                   (!x. x IN s ==> ((lift o f) has_vector_derivative r(x))
                                   (at x within {t | drop x <= drop t})) /\
                   (!x. x IN s ==> drop(l x) <= drop(r x)) /\
                   (!x y. x IN s /\ y IN s /\ drop x < drop y
                          ==> drop(r x) <= drop(l y))`;;

let CONVEX_ON_COUNTABLE_NONDIFFERENTIABLE = `!f s.
      f convex_on s /\ COUNTABLE(components s)
      ==> COUNTABLE {x:real^1 | x IN s /\ ~((lift o f) differentiable at x)}`;;

(* ------------------------------------------------------------------------- *)
(* Convex functions R^1->R^1 are indefinite integrals of increasing ones.    *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_INDEFINITE_INTEGRAL_INCREASING = `!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> (\x. drop(integral (interval[a,x]) f)) convex_on interval[a,b]`;;

let CONVEX_ON_IS_INDEFINITE_INTEGRAL = `!f s. (drop o f) convex_on s /\ is_interval s /\ open s
         ==> ?f'. (!x y. x IN s /\ y IN s /\ drop x <= drop y
                         ==> drop(f' x) <= drop(f' y)) /\
                  (!x y. x IN s /\ y IN s /\ drop x <= drop y
                         ==> (f' has_integral (f y - f x)) (interval[x,y]))`;;

(* ------------------------------------------------------------------------- *)
(* Absolute continuity, first a "set function" form.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("absolutely_setcontinuous_on",(12,"right"));;

let absolutely_setcontinuous_on = new_definition
 `(f:(real^M->bool)->real^N) absolutely_setcontinuous_on s <=>
        !e. &0 < e
            ==> ?r. &0 < r /\
                    !d t. d division_of t /\ t SUBSET s /\ sum d content < r
                          ==> sum d (\k. norm(f k)) < e`;;

let ABSOLUTELY_SETCONTINUOUS_COMPARISON = `!f:(real^M->bool)->real^N g:(real^M->bool)->real^P s.
        f absolutely_setcontinuous_on s /\
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> norm(g(interval[a,b])) <= norm(f(interval[a,b])))
        ==> g absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_EQ = `!f g:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b])) /\
        f absolutely_setcontinuous_on s
        ==> g absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_COMPONENTWISE = `!f:(real^M->bool)->real^N s.
        f absolutely_setcontinuous_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\k. lift(f k$i)) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_ALT = `!f:(real^M->bool)->real^N s.
         f absolutely_setcontinuous_on s <=>
         !e. &0 < e
             ==> ?r. &0 < r /\
                     !d t. d division_of t /\ t SUBSET s /\ sum d content < r
                           ==> norm(vsum d f) < e`;;

let ABSOLUTELY_SETCONTINUOUS_ON_LIFT_ABS = `!f:(real^N->bool)->real s.
        (\x. lift(abs(f x))) absolutely_setcontinuous_on s <=>
        (\x. lift(f x)) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_SUBSET = `!f:(real^M->bool)->real^N s t.
        f absolutely_setcontinuous_on s /\ t SUBSET s
        ==> f absolutely_setcontinuous_on t`;;

let ABSOLUTELY_SETCONTINUOUS_ON_NORM = `!f:(real^M->bool)->real^N s.
        (\x. lift(norm(f x))) absolutely_setcontinuous_on s <=>
        f absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_COMPOSE_LINEAR = `!f:(real^M->bool)->real^N g:real^N->real^P s.
        f absolutely_setcontinuous_on s /\ linear g
        ==> (g o f) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_0 = `!s:real^N->bool. (\x. vec 0) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_CMUL = `!f:(real^M->bool)->real^N c s.
        f absolutely_setcontinuous_on s
        ==> (\x. c % f x) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_NEG = `!f:(real^M->bool)->real^N s.
        (\x. --(f x)) absolutely_setcontinuous_on s <=>
        f absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_ADD = `!f:(real^M->bool)->real^N g s.
        f absolutely_setcontinuous_on s /\
        g absolutely_setcontinuous_on s
        ==> (\x. f x + g x) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_SUB = `!f:(real^M->bool)->real^N g s.
        f absolutely_setcontinuous_on s /\
        g absolutely_setcontinuous_on s
        ==> (\x. f x - g x) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_NULL = `!f:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s /\
               content(interval[a,b]) = &0
               ==> f(interval[a,b]) = vec 0) /\
        content s = &0 /\ bounded s
        ==> f absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_VSUM = `!f:A->(real^M->bool)->real^N s k.
        FINITE k /\
        (!i. i IN k ==> f i absolutely_setcontinuous_on s)
        ==> (\x. vsum k (\i. f i x)) absolutely_setcontinuous_on s`;;

let ABSOLUTELY_SETCONTINUOUS_ON_MUL = `!f g:(real^M->bool)->real^N s.
        f absolutely_setcontinuous_on s /\
        g absolutely_setcontinuous_on s
        ==> (\x. drop(f x) % g x) absolutely_setcontinuous_on s`;;

let OPERATIVE_ABSOLUTELY_SETCONTINUOUS_ON = `!f:(real^M->bool)->real^N.
        operative (+) f ==> operative (/\) ((absolutely_setcontinuous_on) f)`;;

let ABSOLUTELY_SETCONTINUOUS_ON_DIVISION = `!f:(real^M->bool)->real^N a b d.
        operative (+) f /\ d division_of interval[a,b]
        ==> ((!k. k IN d ==> f absolutely_setcontinuous_on k) <=>
             f absolutely_setcontinuous_on interval[a,b])`;;

let ABSOLUTELY_SETCONTINUOUS_ON_IMP_HAS_BOUNDED_SETVARIATION_ON = `!f:(real^M->bool)->real^N s.
        operative (+) f /\ f absolutely_setcontinuous_on s /\ bounded s
        ==> f has_bounded_setvariation_on s`;;

(* ------------------------------------------------------------------------- *)
(* Now the standard notion of absolute continuity for a function R^1->R^n.   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("absolutely_continuous_on",(12,"right"));;

let absolutely_continuous_on = new_definition
 `(f:real^1->real^N) absolutely_continuous_on s <=>
        (\k. f(interval_upperbound k) - f(interval_lowerbound k))
        absolutely_setcontinuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_EQ = `!f g:real^1->real^N s.
        (!x. x IN s ==> f x = g x) /\ f absolutely_continuous_on s
        ==> g absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ISOMETRIC = `!f g:real^1->real^N s.
        (!x y. dist(f x,f y) = dist(g x,g y))
        ==> (f absolutely_continuous_on s <=> g absolutely_continuous_on s)`;;

let ABSOLUTELY_CONTINUOUS_ISOMETRIC_COMPOSE = `!f:real^M->real^N g s.
        (!x y. dist(f x,f y) = dist(x,y))
        ==> ((f o g) absolutely_continuous_on s <=>
             g absolutely_continuous_on s)`;;

let ABSOLUTELY_CONTINUOUS_ON_TRANSLATION = `!f:real^1->real^N s a.
   (\x. a + f x) absolutely_continuous_on s <=> f absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_COMPONENTWISE = `!f:real^1->real^N s.
        f absolutely_continuous_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f x$i)) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_LIFT_COMPONENT = `!(f:real^1->real^N) s.
        f absolutely_continuous_on s /\
        1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift(f x$i)) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_COMPARISON = `!f:real^1->real^M g:real^1->real^N s.
        f absolutely_continuous_on s /\
        (!x y. x IN s /\ y IN s /\ drop x < drop y
               ==> dist(g x,g y) <= dist(f x,f y))
        ==> g absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_LIFT_ABS = `!f:real^1->real.
        (\x. lift(f x)) absolutely_continuous_on s
        ==> (\x. lift(abs(f x))) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_SUBSET = `!f:real^1->real^N s t.
        f absolutely_continuous_on s /\ t SUBSET s
        ==> f absolutely_continuous_on t`;;

let ABSOLUTELY_CONTINUOUS_ON_CONST = `!s c:real^N. (\x. c) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_CMUL = `!f:real^1->real^N c s.
        f absolutely_continuous_on s
        ==> (\x. c % f x) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_CMUL_EQ = `!f:real^1->real^N c s.
        (\x. c % f x) absolutely_continuous_on s <=>
        c = &0 \/ f absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_VMUL_EQ = `!f s v:real^N.
        (\x. f(x) % v) absolutely_continuous_on s <=>
        v = vec 0 \/ (\x. lift(f x)) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_VMUL = `!f s v:real^N.
        (\x. lift(f x)) absolutely_continuous_on s
        ==> (\x. f(x) % v) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_NEG = `!f:real^1->real^N s.
        f absolutely_continuous_on s
        ==> (\x. --f x) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_ADD = `!f g:real^1->real^N s.
        f absolutely_continuous_on s /\ g absolutely_continuous_on s
        ==> (\x. f x + g x) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_SUB = `!f g:real^1->real^N s.
        f absolutely_continuous_on s /\ g absolutely_continuous_on s
        ==> (\x. f x - g x) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_COMPOSE_LINEAR = `!f:real^1->real^M g:real^M->real^N s.
        f absolutely_continuous_on s /\ linear g
        ==> (g o f) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_NULL = `!f:real^1->real^N s.
        content s = &0 /\ bounded s ==> f absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_EMPTY = `!f:real^1->real^N. f absolutely_continuous_on {}`;;

let ABSOLUTELY_CONTINUOUS_ON_NORM = `!f:real^1->real^N s.
        f absolutely_continuous_on s
        ==> (\x. lift(norm(f x))) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_MAX = `!f g s. f absolutely_continuous_on s /\ g absolutely_continuous_on s
           ==> (\x. lift(max (drop(f x)) (drop(g x))))
               absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_MIN = `!f g s. f absolutely_continuous_on s /\ g absolutely_continuous_on s
           ==> (\x. lift(min (drop(f x)) (drop(g x))))
               absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_LIPSCHITZ_COMPOSE = `!f:real^M->real^N g s B.
        g absolutely_continuous_on s /\
        (!x y. x IN IMAGE g s /\ y IN IMAGE g s
               ==> norm(f x - f y) <= B * norm(x - y))
        ==> (f o g) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_ID = `!s:real^1->bool. (\x. x) absolutely_continuous_on s`;;

let LIPSCHITZ_IMP_ABSOLUTELY_CONTINUOUS = `!f:real^1->real^N s B.
        bounded s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> f absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_IMP_UNIFORMLY_CONTINUOUS = `!f:real^1->real^N s.
        f absolutely_continuous_on s /\ is_interval s
        ==> f uniformly_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_IMP_CONTINUOUS = `!f s. f absolutely_continuous_on s /\ is_interval s
         ==> f continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON = `!f:real^1->real^N s.
        f absolutely_continuous_on s /\ bounded s
        ==> f has_bounded_variation_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_BILINEAR = `!bop:real^M->real^N->real^P f g s.
        bilinear bop /\
        f absolutely_continuous_on s /\
        g absolutely_continuous_on s /\
        is_interval s /\ bounded s
        ==> (\x. bop (f x) (g x)) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_MUL = `!f g:real^1->real^N s.
        f absolutely_continuous_on s /\
        g absolutely_continuous_on s /\
        is_interval s /\ bounded s
        ==> (\x. drop(f x) % g x) absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_VSUM = `!f:A->real^1->real^N s k.
        FINITE k /\
        (!i. i IN k ==> f i absolutely_continuous_on s)
        ==> (\x. vsum k (\i. f i x)) absolutely_continuous_on s`;;

let OPERATIVE_ABSOLUTELY_CONTINUOUS_ON = `!f:real^1->real^N.
        operative (/\) ((absolutely_continuous_on) f)`;;

let ABSOLUTELY_CONTINUOUS_ON_DIVISION = `!f:real^1->real^N a b d.
        d division_of interval[a,b]
        ==> ((!k. k IN d ==> f absolutely_continuous_on k) <=>
             f absolutely_continuous_on interval[a,b])`;;

let ABSOLUTELY_CONTINUOUS_ON_COMBINE = `!f:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b
        ==> (f absolutely_continuous_on interval[a,b] <=>
             f absolutely_continuous_on interval[a,c] /\
             f absolutely_continuous_on interval[c,b])`;;

let ABSOLUTELY_CONTINUOUS_ON_SING = `!f a. f absolutely_continuous_on {a}`;;

let ABSOLUTELY_CONTINUOUS_ON_INTERIOR = `!f:real^1->real^N s.
        f absolutely_continuous_on (interior s) /\
        f continuous_on s
        ==> f absolutely_continuous_on s`;;

let ABSOLUTELY_CONTINUOUS_ON_INTERIOR_EQ = `!f:real^1->real^N s.
        f continuous_on s
        ==> (f absolutely_continuous_on interior s <=>
             f absolutely_continuous_on s)`;;

let ABSOLUTELY_CONTINUOUS_ON_CLOSURE = `!f:real^1->real^N s.
        is_interval s /\ f continuous_on closure s /\
        f absolutely_continuous_on interior s
        ==> f absolutely_continuous_on closure s`;;

let ABSOLUTELY_CONTINUOUS_ON_CLOSURE_EQ = `!f:real^1->real^N s.
        is_interval s /\ f continuous_on closure s
        ==> (f absolutely_continuous_on closure s <=>
             f absolutely_continuous_on s)`;;

let ABSOLUTELY_CONTINUOUS_EXTENDS_TO_CLOSURE = `!f:real^1->real^N s.
        f absolutely_continuous_on s /\ is_interval s
        ==> ?g. g absolutely_continuous_on (closure s) /\
                !x. x IN s ==> g x = f x`;;

(* ------------------------------------------------------------------------- *)
(* Rectifiable paths and path length defined using variation.                *)
(* ------------------------------------------------------------------------- *)

let rectifiable_path = new_definition
 `rectifiable_path (g:real^1->real^N) <=>
    path g /\ g has_bounded_variation_on interval[vec 0,vec 1]`;;

let path_length = new_definition
 `path_length (g:real^1->real^N) =
  vector_variation (interval[vec 0,vec 1]) g`;;

let RECTIFIABLE_PATH_LIPSCHITZ_IMAGE = `!f:real^M->real^N g.
        rectifiable_path g /\
        (?B. !x y. x IN path_image g /\ y IN path_image g
                   ==> norm(f x - f y) <= B * norm(x - y))
        ==> rectifiable_path(f o g)`;;

let RECTIFIABLE_PATH_TRANSLATION_EQ = `!a:real^N g. rectifiable_path((\x. a + x) o g) <=> rectifiable_path g`;;

add_translation_invariants [RECTIFIABLE_PATH_TRANSLATION_EQ];;

let RECTIFIABLE_PATH_LINEAR_IMAGE_EQ = `!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (rectifiable_path(f o g) <=> rectifiable_path g)`;;

add_linear_invariants [RECTIFIABLE_PATH_LINEAR_IMAGE_EQ];;

let PATH_LENGTH_TRANSLATION = `!a g:real^1->real^N. path_length((\x. a + x) o g) = path_length g`;;

add_translation_invariants [PATH_LENGTH_TRANSLATION];;

let PATH_LENGTH_ISOMETRIC_IMAGE = `!f:real^M->real^N g.
     (!x y. dist(f x,f y) = dist(x,y)) ==> path_length(f o g) = path_length g`;;

let PATH_LENGTH_LINEAR_IMAGE = `!f:real^M->real^N g.
        linear f /\ (!x. norm(f x) = norm x)
        ==> path_length(f o g) = path_length g`;;

add_linear_invariants [PATH_LENGTH_LINEAR_IMAGE];;

let RECTIFIABLE_PATH_EQ = `!p q:real^1->real^N.
        (!t. t IN interval[vec 0,vec 1] ==> p t = q t) /\ rectifiable_path p
        ==> rectifiable_path q`;;

let PATH_LENGTH_EQ = `!p q:real^1->real^N.
        (!t. t IN interval[vec 0,vec 1] ==> p t = q t)
        ==> path_length p = path_length q`;;

let PATH_LENGTH_SCALING = `!g:real^1->real^N c.
        rectifiable_path g
        ==> path_length ((\x. c % x) o g) = abs c * path_length g`;;

let BOUNDED_RECTIFIABLE_PATH_IMAGE = `!g:real^1->real^N. rectifiable_path g ==> bounded(path_image g)`;;

let RECTIFIABLE_PATH_IMP_PATH = `!g:real^1->real^N. rectifiable_path g ==> path g`;;

let RECTIFIABLE_PATH_LINEPATH = `!a b:real^N. rectifiable_path(linepath(a,b))`;;

let RECTIFIABLE_PATH_REVERSEPATH = `!g:real^1->real^N. rectifiable_path(reversepath g) <=> rectifiable_path g`;;

let PATH_LENGTH_REVERSEPATH = `!g:real^1->real^N. path_length(reversepath g) = path_length g`;;

let RECTIFIABLE_PATH_SUBPATH_EQ = `!g:real^1->real^N s t.
        rectifiable_path(subpath s t g) <=>
        path(subpath s t g) /\ g has_bounded_variation_on segment[s,t]`;;

let PATH_LENGTH_SUBPATH = `!g:real^1->real^N s t.
        path_length(subpath s t g) = vector_variation (segment[s,t]) g`;;

let RECTIFIABLE_PATH_SUBPATH = `!u v g:real^1->real^N.
        rectifiable_path g /\
        u IN interval[vec 0,vec 1] /\
        v IN interval[vec 0,vec 1]
        ==> rectifiable_path(subpath u v g)`;;

let RECTIFIABLE_PATH_JOIN = `!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (rectifiable_path(g1 ++ g2) <=>
             rectifiable_path g1 /\ rectifiable_path g2)`;;

let RECTIFIABLE_PATH_JOIN_IMP = `!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2 /\
        pathfinish g1 = pathstart g2
        ==> rectifiable_path(g1 ++ g2)`;;

let RECTIFIABLE_PATH_JOIN_EQ = `!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2
        ==> (rectifiable_path (g1 ++ g2) <=> pathfinish g1 = pathstart g2)`;;

let RECTIFIABLE_PATH_SYM = `!p q:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart p
        ==> (rectifiable_path(p ++ q) <=> rectifiable_path(q ++ p))`;;

let RECTIFIABLE_PATH_SHIFTPATH = `!g:real^1->real^N a.
           rectifiable_path g /\
           pathfinish g = pathstart g /\
           a IN interval[vec 0,vec 1]
           ==> rectifiable_path(shiftpath a g)`;;

let PATH_LENGTH_SHIFTPATH = `!g:real^1->real^N a.
           rectifiable_path g /\
           pathfinish g = pathstart g /\
           a IN interval[vec 0,vec 1]
           ==> path_length(shiftpath a g) = path_length g`;;

let PATH_LENGTH_POS_LE = `!g:real^1->real^N.
        rectifiable_path g ==> &0 <= path_length g`;;

let PATH_LENGTH_EQ_0 = `!g:real^1->real^N.
        rectifiable_path g
        ==> (path_length g = &0 <=>
             ?c. !t. t IN interval[vec 0,vec 1] ==> g t = c)`;;

let SIMPLE_PATH_LENGTH_POS_LT = `!g:real^1->real^N.
        rectifiable_path g /\ simple_path g ==> &0 < path_length g`;;

let PATH_LENGTH_JOIN = `!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2 /\
        pathfinish g1 = pathstart g2
        ==> path_length(g1 ++ g2) = path_length g1 + path_length g2`;;

let PATH_LENGTH_COMBINE = `!g:real^1->real^N t.
        rectifiable_path g /\ t IN interval[vec 0,vec 1]
        ==> path_length(subpath (vec 0) t g) +
            path_length(subpath t (vec 1) g) =
            path_length g`;;

let RECTIFIABLE_PATH_COMBINE = `!g:real^1->real^N t.
        t IN interval[vec 0,vec 1]
        ==> (rectifiable_path g <=>
             rectifiable_path(subpath (vec 0) t g) /\
             rectifiable_path(subpath t (vec 1) g))`;;

let LIPSCHITZ_IMP_RECTIFIABLE_PATH = `!g:real^1->real^N b.
        (!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1]
               ==> norm(g x - g y) <= b * norm(x - y))
        ==> rectifiable_path g`;;

let PATH_LENGTH_LIPSCHITZ = `!g:real^1->real^N b.
        (!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1]
               ==> norm(g x - g y) <= b * norm(x - y))
        ==> path_length g <= b`;;

let DIST_POINTS_LE_PATH_LENGTH = `!g:real^1->real^N a b.
        rectifiable_path g /\
        a IN interval[vec 0,vec 1] /\
        b IN interval[vec 0,vec 1]
        ==> dist (g a,g b) <= path_length g`;;

let DIST_ENDPOINTS_LE_PATH_LENGTH = `!g:real^1->real^N.
      rectifiable_path g ==> dist(pathstart g,pathfinish g) <= path_length g`;;

let PATH_LENGTH_EQ_LINE_SEGMENT = `!g:real^1->real^N.
        rectifiable_path g /\ path_length g = dist(pathstart g,pathfinish g)
        ==> path_image g = segment[pathstart g,pathfinish g]`;;

let PATH_LENGTH_SUBPATH_LE = `!g:real^1->real^N s t.
        rectifiable_path g /\
        s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1]
        ==> path_length (subpath s t g) <= path_length g`;;

let RECTIFIABLE_PATH_IMAGE_SUBSET_CBALL = `!g:real^1->real^N.
        rectifiable_path g
        ==> path_image g SUBSET cball(pathstart g,path_length g)`;;

let PATH_LENGTH_LINEPATH = `!a b:real^N. path_length(linepath(a,b)) = dist(a,b)`;;

let RECTIFIABLE_PATH_REPARAMETRIZATION = `!g:real^1->real^N h h'.
        rectifiable_path g /\
        homeomorphism (interval[vec 0,vec 1],interval[vec 0,vec 1]) (h,h')
        ==> rectifiable_path(g o h)`;;

let PATH_LENGTH_REPARAMETRIZATION = `!g:real^1->real^N h h'.
        rectifiable_path g /\
        homeomorphism (interval[vec 0,vec 1],interval[vec 0,vec 1]) (h,h')
        ==> path_length (g o h) = path_length g`;;

let ARC_LENGTH_UNIQUE = `!g h:real^1->real^N.
        rectifiable_path g /\ arc g /\ rectifiable_path h /\ arc h /\
        path_image g = path_image h
        ==> path_length g = path_length h`;;

let CONTINUOUS_ON_PATH_LENGTH_SUBPATH_RIGHT = `!g:real^1->real^N a.
        rectifiable_path g /\ a IN interval[vec 0,vec 1]
        ==> (\x. lift(path_length(subpath a x g)))
            continuous_on interval[vec 0,vec 1]`;;

let CONTINUOUS_ON_PATH_LENGTH_SUBPATH_LEFT = `!g:real^1->real^N a.
        rectifiable_path g /\ a IN interval[vec 0,vec 1]
        ==> (\x. lift(path_length(subpath x a g)))
            continuous_on interval[vec 0,vec 1]`;;

(* ------------------------------------------------------------------------- *)
(* Arc length reparametrization, and existence of shortest paths.            *)
(* ------------------------------------------------------------------------- *)

let ARC_LENGTH_REPARAMETRIZATION = `!g:real^1->real^N.
        rectifiable_path g
        ==> ?h. rectifiable_path h /\
                path_image h = path_image g /\
                pathstart h = pathstart g /\
                pathfinish h = pathfinish g /\
                path_length h = path_length g /\
                (arc g ==> arc h) /\
                (simple_path g ==> simple_path h) /\
                (!t. t IN interval[vec 0,vec 1]
                     ==> path_length(subpath (vec 0) t h) =
                         path_length g * drop t) /\
                (!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1]
                       ==> dist(h x,h y) <= path_length g * dist(x,y))`;;

let SHORTEST_PATH_EXISTS_GEN = `!P. (!h g. (!n. rectifiable_path(h n) /\
                   P (path_image(h n)) (pathstart(h n)) (pathfinish(h n))) /\
               (!e. &0 < e
                    ==> ?N. !n:num x. n >= N /\ x IN interval[vec 0,vec 1]
                                      ==> norm (h n x - g x) < e)
               ==> P(path_image g) (pathstart g) (pathfinish g)) /\
       (?t. bounded t /\
            !g. rectifiable_path g /\
                P (path_image g) (pathstart g) (pathfinish g)
                ==> ~DISJOINT t (convex hull (path_image g))) /\
       (?g. rectifiable_path g /\
            P (path_image g) (pathstart g) (pathfinish g))
       ==> ?g. rectifiable_path g /\
               P (path_image g) (pathstart g) (pathfinish g) /\
               !h. rectifiable_path h /\
                   P (path_image h) (pathstart h) (pathfinish h)
                   ==> path_length(g:real^1->real^N) <= path_length h`;;

let SHORTEST_PATH_EXISTS_STRADDLE = `!s t a b:real^N->bool.
        closed s /\ compact a /\ compact b /\
        (?g. rectifiable_path g /\
             t SUBSET path_image g /\ path_image g SUBSET s /\
             pathstart g IN a /\ pathfinish g IN b)
        ==> ?g. rectifiable_path g /\
                t SUBSET path_image g /\ path_image g SUBSET s /\
                pathstart g IN a /\ pathfinish g IN b /\
                !h. rectifiable_path h /\
                    t SUBSET path_image h /\ path_image h SUBSET s /\
                    pathstart h IN a /\ pathfinish h IN b
                    ==> path_length g <= path_length h`;;

let SHORTEST_PATH_EXISTS = `!s a b:real^N->bool.
        closed s /\ compact a /\ compact b /\
        (?g. rectifiable_path g /\ path_image g SUBSET s /\
             pathstart g IN a /\ pathfinish g IN b)
        ==> ?g. rectifiable_path g /\ path_image g SUBSET s /\
                pathstart g IN a /\ pathfinish g IN b /\
                !h. rectifiable_path h /\ path_image h SUBSET s /\
                    pathstart h IN a /\ pathfinish h IN b
                    ==> path_length g <= path_length h`;;

let SHORTEST_ARC_EXISTS = `!s a b:real^N.
        closed s /\ ~(a = b) /\
        (?g. rectifiable_path g /\ path_image g SUBSET s /\
             pathstart g = a /\ pathfinish g = b)
        ==> ?g. rectifiable_path g /\ arc g /\ path_image g SUBSET s /\
                pathstart g = a /\ pathfinish g = b /\
                !h. rectifiable_path h /\ path_image h SUBSET s /\
                    pathstart h = a /\ pathfinish h = b
                    ==> path_length g <= path_length h`;;

let ARC_LENGTH_MINIMAL = `!g h:real^1->real^N.
        rectifiable_path g /\ arc g /\ rectifiable_path h /\
        path_image g = path_image h
        ==> path_length g <= path_length h`;;

let SIMPLE_PATH_LENGTH_MINIMAL = `!g h:real^1->real^N.
        rectifiable_path g /\ simple_path g /\ rectifiable_path h /\
        path_image g = path_image h
        ==> path_length g <= path_length h`;;

let SIMPLE_PATH_LENGTH_UNIQUE = `!g h:real^1->real^N.
        rectifiable_path g /\ simple_path g /\
        rectifiable_path h /\ simple_path h /\
        path_image g = path_image h
        ==> path_length g = path_length h`;;

(* ------------------------------------------------------------------------- *)
(* Useful equivalent formulations where the path is differentiable.          *)
(* ------------------------------------------------------------------------- *)

let RECTIFIABLE_PATH_DIFFERENTIABLE = `!g:real^1->real^N s.
        COUNTABLE s /\ path g /\
        (!t. t IN interval[vec 0,vec 1] DIFF s ==> g differentiable at t)
        ==> (rectifiable_path g <=>
                (\t. vector_derivative g (at t))
                absolutely_integrable_on interval[vec 0,vec 1])`;;

let PATH_LENGTH_DIFFERENTIABLE = `!g:real^1->real^N s.
        COUNTABLE s /\ rectifiable_path g /\
        (!t. t IN interval[vec 0,vec 1] DIFF s ==> g differentiable at t)
        ==> path_length g =
                drop(integral (interval[vec 0,vec 1])
                              (\t. lift(norm(vector_derivative g (at t)))))`;;

(* ------------------------------------------------------------------------- *)
(* Solutions to differential equations: the Picard-Lindelof theorem.         *)
(* ------------------------------------------------------------------------- *)

let PICARD_LINDELOF_RIGHT = `!s (f:real^(1,N)finite_sum->real^N) t0 u0 r0 r1 B c.
     open s /\ f continuous_on s /\
     &0 < r0 /\ &0 < r1 /\ B * r0 < r1 /\ c * r0 < &1 /\
     interval[t0,t0 + lift r0] PCROSS cball(u0,r1) SUBSET s /\
     (!x. x IN s ==> norm(f x) <= B) /\
     (!t v w. t IN interval[t0,t0 + lift r0] /\
              v IN cball(u0,r1) /\ w IN cball(u0,r1)
              ==> norm(f(pastecart t v) - f(pastecart t w)) <= c * norm(v - w))
     ==> ?u. u t0 = u0 /\
             (!t. t IN interval[t0,t0 + lift r0]
                  ==> (u has_vector_derivative f(pastecart t (u t)))
                        (at t within interval[t0,t0 + lift r0])) /\
             (!v. (!t. t IN interval[t0,t0 + lift r0]
                  ==> pastecart t (v t) IN s) /\
                  v t0 = u0 /\
                  (!t. t IN interval[t0,t0 + lift r0]
                       ==> (v has_vector_derivative f(pastecart t (v t)))
                             (at t within interval[t0,t0 + lift r0]))
                  ==> (!t. t IN interval[t0,t0 + lift r0] ==> v t = u t))`;;
