(* ========================================================================= *)
(* Euler's partition theorem and other elementary partition theorems.        *)
(* ========================================================================= *)

loadt "Library/binary.ml";;

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let NSUM_BOUND_LEMMA = `!f a b n. nsum(a..b) f = n ==> !i. a <= i /\ i <= b ==> f(i) <= n`;;

let CARD_EQ_LEMMA = `!f:A->B g s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> g(y) IN s) /\
        (!x. x IN s ==> g(f x) = x) /\
        (!y. y IN t ==> f(g y) = y)
        ==> FINITE s /\ FINITE t /\ CARD s = CARD t`;;

(* ------------------------------------------------------------------------- *)
(* Breaking a number up into 2^something * odd_number.                       *)
(* ------------------------------------------------------------------------- *)

let index = define
 `index n = if n = 0 then 0 else if ODD n then 0 else SUC(index(n DIV 2))`;;

let oddpart = define
 `oddpart n = if n = 0 then 0 else if ODD n then n else oddpart(n DIV 2)`;;

let INDEX_ODDPART_WORK = `!n. n = 2 EXP (index n) * oddpart n /\ (ODD(oddpart n) <=> ~(n = 0))`;;

let INDEX_ODDPART_DECOMPOSITION = `!n. n = 2 EXP (index n) * oddpart n`;;

let ODD_ODDPART = `!n. ODD(oddpart n) <=> ~(n = 0)`;;

let ODDPART_LE = `!n. oddpart n <= n`;;

let INDEX_ODDPART_UNIQUE = `!i m i' m'. ODD m /\ ODD m'
               ==> (2 EXP i * m = 2 EXP i' * m' <=> i = i' /\ m = m')`;;

let INDEX_ODDPART = `!i m. ODD m ==> index(2 EXP i * m) = i /\ oddpart(2 EXP i * m) = m`;;

(* ------------------------------------------------------------------------- *)
(* Partitions.                                                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("partitions",(12,"right"));;

let partitions = new_definition
 `p partitions n <=> (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
                     nsum(1..n) (\i. p(i) * i) = n`;;

let PARTITIONS_BOUND = `!p n. p partitions n ==> !i. p(i) <= n`;;

let FINITE_PARTITIONS_LEMMA = `!m n. FINITE {p | (!i. p(i) <= n) /\ !i. m <= i ==> p(i) = 0}`;;

let FINITE_PARTITIONS = `!n. FINITE {p | p partitions n}`;;

let FINITE_SUBSET_PARTITIONS = `!P n. FINITE {p | p partitions n /\ P p}`;;

(* ------------------------------------------------------------------------- *)
(* Mappings between "odd only" and "all distinct" partitions.                *)
(* ------------------------------------------------------------------------- *)

let odd_of_distinct = new_definition
 `odd_of_distinct p =
    \i. if ODD i then nsum {j | p(2 EXP j * i) = 1} (\j. 2 EXP j) else 0`;;

let distinct_of_odd = new_definition
 `distinct_of_odd p = \i. if (index i) IN bitset (p(oddpart i)) then 1 else 0`;;

(* ------------------------------------------------------------------------- *)
(* The critical properties.                                                  *)
(* ------------------------------------------------------------------------- *)

let ODD_ODD_OF_DISTINCT = `!p i. ~(odd_of_distinct p i = 0) ==> ODD i`;;

let DISTINCT_DISTINCT_OF_ODD = `!p i. distinct_of_odd p i <= 1`;;

let SUPPORT_ODD_OF_DISTINCT = `!p. (!i. ~(p i = 0) ==> i <= n)
       ==> !i. ~(odd_of_distinct p i = 0) ==> 1 <= i /\ i <= n`;;

let SUPPORT_DISTINCT_OF_ODD = `!p. (!i. p(i) * i <= n) /\
       (!i. ~(p i = 0) ==> ODD i)
       ==> !i. ~(distinct_of_odd p i = 0) ==> 1 <= i /\ i <= n`;;

let ODD_OF_DISTINCT_OF_ODD = `!p. (!i. ~(p(i) = 0) ==> ODD i)
       ==> odd_of_distinct (distinct_of_odd p) = p`;;

let DISTINCT_OF_ODD_OF_DISTINCT = `!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\ (!i. p(i) <= 1)
       ==> distinct_of_odd (odd_of_distinct p) = p`;;

let NSUM_DISTINCT_OF_ODD = `!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
       (!i. p(i) * i <= n) /\
       (!i. ~(p(i) = 0) ==> ODD i)
       ==> nsum(1..n) (\i. distinct_of_odd p i * i) =
           nsum(1..n) (\i. p i * i)`;;

let DISTINCT_OF_ODD = `!p. p IN {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}
       ==> (distinct_of_odd p) IN {p | p partitions n /\ !i. p(i) <= 1}`;;

let ODD_OF_DISTINCT = `!p. p IN {p | p partitions n /\ !i. p(i) <= 1}
       ==> (odd_of_distinct p) IN
           {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}`;;

(* ------------------------------------------------------------------------- *)
(* Euler's partition theorem:                                                *)
(*                                                                           *)
(* The number of partitions into distinct numbers is equal to the number of  *)
(* partitions into odd numbers (and there are only finitely many of each).   *)
(* ------------------------------------------------------------------------- *)

let EULER_PARTITION_THEOREM = `FINITE {p | p partitions n /\ !i. p(i) <= 1} /\
   FINITE {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i} /\
   CARD {p | p partitions n /\ !i. p(i) <= 1} =
   CARD {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}`;;
