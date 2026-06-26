(* ========================================================================= *)
(* Taylor series for tan and cot, via partial fractions expansion of cot.    *)
(* ========================================================================= *)

needs "Library/analysis.ml";;
needs "Library/transc.ml";;
needs "Library/floor.ml";;
needs "Library/poly.ml";;
needs "Examples/machin.ml";;
needs "Library/iter.ml";;

(* ------------------------------------------------------------------------- *)
(* Compatibility stuff for some old proofs.                                  *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_1_POW2 = `!n. &1 <= &2 pow n`;;

let REAL_LT_1_POW2 = `!n. &1 < &2 pow n <=> ~(n = 0)`;;

let REAL_POW2_CLAUSES = `(!n. &0 <= &2 pow n) /\
   (!n. &0 < &2 pow n) /\
   (!n. &0 <= inv(&2 pow n)) /\
   (!n. &0 < inv(&2 pow n)) /\
   (!n. inv(&2 pow n) <= &1) /\
   (!n. &1 - inv(&2 pow n) <= &1) /\
   (!n. &1 <= &2 pow n) /\
   (!n. &1 < &2 pow n <=> ~(n = 0)) /\
   (!n. &0 <= &1 - inv(&2 pow n)) /\
   (!n. &0 <= &2 pow n - &1) /\
   (!n. &0 < &1 - inv(&2 pow n) <=> ~(n = 0))`;;

let REAL_INTEGER_CLOSURES = `(!n. ?p. abs(&n) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x + y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x - y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x * y) = &p) /\
   (!x r. (?n. abs(x) = &n) ==> ?p. abs(x pow r) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(--x) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(abs x) = &p)`;;

let PI_APPROX_25_BITS = time PI_APPROX_BINARY_RULE 25;;

(* ------------------------------------------------------------------------- *)
(* Convert a polynomial into a "canonical" list-based form.                  *)
(* ------------------------------------------------------------------------- *)

let POLYMERIZE_CONV =
  let pth = `a = poly [a] x`;;

(* ------------------------------------------------------------------------- *)
(* We need to reverse sums to prove the grisly lemma below.                  *)
(* ------------------------------------------------------------------------- *)

let SUM_PERMUTE_0 = `!n p. (!y. y < n ==> ?!x. x < n /\ (p(x) = y))
        ==> !f. sum(0,n)(\n. f(p n)) = sum(0,n) f`;;

let SUM_REVERSE_0 = `!n f. sum(0,n) f = sum(0,n) (\k. f((n - 1) - k))`;;

let SUM_REVERSE = `!n m f. sum(m,n) f = sum(m,n) (\k. f(((n + 2 * m) - 1) - k))`;;

(* ------------------------------------------------------------------------- *)
(* Following is lifted from fsincos taylor series.                           *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_SIN = `!x n. abs(sin x -
             sum(0,n) (\m. (if EVEN m then &0
                            else -- &1 pow ((m - 1) DIV 2) / &(FACT m)) *
                            x pow m))
         <= inv(&(FACT n)) * abs(x) pow n`;;

(* ------------------------------------------------------------------------- *)
(* The formulas marked with a star on p. 205 of Knopp's book.                *)
(* ------------------------------------------------------------------------- *)

let COT_HALF_TAN = `~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) - tan(pi * x / &2)))`;;

let COT_HALF_POS = `~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) + cot(pi * (x + &1) / &2)))`;;

let COT_HALF_NEG = `~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) + cot(pi * (x - &1) / &2)))`;;

(* ------------------------------------------------------------------------- *)
(* By induction, the formula marked with the dagger.                         *)
(* ------------------------------------------------------------------------- *)

let COT_HALF_MULTIPLE = `~(integer x)
   ==> !n. cot(pi * x) =
           sum(0,2 EXP n)
             (\k. cot(pi * (x + &k) / &2 pow n) +
                  cot(pi * (x - &k) / &2 pow n)) / &2 pow (n + 1)`;;

let COT_HALF_KNOPP = `~(integer x)
   ==> !n. cot(pi * x) =
           cot(pi * x / &2 pow n) / &2 pow n +
           sum(1,2 EXP n - 1)
             (\k. cot(pi * (x + &k) / &2 pow (n + 1)) +
                  cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1)`;;

(* ------------------------------------------------------------------------- *)
(* Bounds on the terms in this series.                                       *)
(* ------------------------------------------------------------------------- *)

let SIN_SUMDIFF_LEMMA = `!x y. sin(x + y) * sin(x - y) = (sin x + sin y) * (sin x - sin y)`;;

let SIN_ZERO_LEMMA = `!x. (sin(pi * x) = &0) <=> integer(x)`;;

let NOT_INTEGER_LEMMA = `~(x = &0) /\ abs(x) < &1 ==> ~(integer x)`;;

let NOT_INTEGER_DIV_POW2 = `~(integer x) ==> ~(integer(x / &2 pow n))`;;

let SIN_ABS_LEMMA = `!x. abs(x) < pi ==> (abs(sin x) = sin(abs x))`;;

let SIN_EQ_LEMMA = `!x y. &0 <= x /\ x < pi / &2 /\ &0 <= y /\ y < pi / &2
         ==> ((sin x = sin y) <=> (x = y))`;;

let KNOPP_TERM_EQUIVALENT = `~(integer x) /\ k < 2 EXP n
   ==> ((cot(pi * (x + &k) / &2 pow (n + 1)) +
         cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1) =
        cot(pi * x / &2 pow (n + 1)) / &2 pow n /
        (&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 /
              sin(pi * x / &2 pow (n + 1)) pow 2))`;;

let SIN_LINEAR_ABOVE = `!x. abs(x) < &1 ==> abs(sin x) <= &2 * abs(x)`;;

let SIN_LINEAR_BELOW = `!x. abs(x) < &2 ==> abs(sin x) >= abs(x) / &3`;;

let KNOPP_TERM_BOUND_LEMMA = `~(integer x) /\ k < 2 EXP n /\ &6 * abs(x) < &k
   ==> abs(a / (&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 /
                     sin(pi * x / &2 pow (n + 1)) pow 2))
       <= abs(a) / ((&k / (&6 * x)) pow 2 - &1)`;;

let KNOPP_TERM_BOUND = `~(integer x) /\ k < 2 EXP n /\ &6 * abs(x) < &k
   ==> abs((cot(pi * (x + &k) / &2 pow (n + 1)) +
            cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1))
       <= abs(cot(pi * x / &2 pow (n + 1)) / &2 pow n) *
          (&36 * x pow 2) / (&k pow 2 - &36 * x pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* Show that the series we're looking at do in fact converge...              *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_INVERSE_SQUARES_LEMMA = `(\n. inv(&(n + 1) * &(n + 2))) sums &1`;;

let SUMMABLE_INVERSE_SQUARES = `summable (\n. inv(&n pow 2))`;;

let SUMMABLE_INVERSE_POWERS = `!m. 2 <= m ==> summable (\n. inv(&(n + 1) pow m))`;;

let COT_TYPE_SERIES_CONVERGES = `!x. ~(integer x) ==> summable (\n. inv(&n pow 2 - x))`;;

(* ------------------------------------------------------------------------- *)
(* Now the rather tricky limiting argument gives the result.                 *)
(* ------------------------------------------------------------------------- *)

let SIN_X_RANGE = `!x. abs(sin(x) - x) <= abs(x) pow 2 / &2`;;

let SIN_X_X_RANGE = `!x. ~(x = &0) ==> abs(sin(x) / x - &1) <= abs(x) / &2`;;

let SIN_X_LIMIT = `((\x. sin(x) / x) tends_real_real &1)(&0)`;;

let COT_X_LIMIT = `((\x. x * cot(x)) tends_real_real &1)(&0)`;;

let COT_LIMIT_LEMMA = `!x. ~(x = &0)
       ==> (\n. (x / &2 pow n) * cot(x / &2 pow n)) tends_num_real &1`;;

let COT_LIMIT_LEMMA1 = `~(x = &0)
   ==> (\n. (pi / &2 pow (n + 1)) * cot(pi * x / &2 pow (n + 1)))
       tends_num_real (inv(x))`;;

let COT_X_BOUND_LEMMA_POS = `?M. !x. &0 < x /\ abs(x) <= &1 ==> abs(x * cot(x)) <= M`;;

let COT_X_BOUND_LEMMA = `?M. !x. ~(x = &0) /\ abs(x) <= &1 ==> abs(x * cot(x)) <= M`;;

let COT_PARTIAL_FRACTIONS = `~(integer x)
   ==> (\n. (&2 * x pow 2) / (x pow 2 - &n pow 2)) sums
       ((pi * x) * cot(pi * x) + &1)`;;

(* ------------------------------------------------------------------------- *)
(* Expansion of each term as a power series.                                 *)
(* ------------------------------------------------------------------------- *)

let COT_PARTIAL_FRACTIONS_SUBTERM = `abs(x) < &n
   ==> (\k. --(&2) * (x pow 2 / &n pow 2) pow (k + 1))
       sums ((&2 * x pow 2) / (x pow 2 - &n pow 2))`;;

(* ------------------------------------------------------------------------- *)
(* General theorem about swapping a double series of positive terms.         *)
(* ------------------------------------------------------------------------- *)

let SEQ_LE_CONST = `!a x l N. (!n. n >= N ==> x(n) <= a) /\ x tends_num_real l ==> l <= a`;;

let SEQ_GE_CONST = `!a x l N. (!n. n >= N ==> a <= x(n)) /\ x tends_num_real l ==> a <= l`;;

let SUM_SWAP_0 = `!m n. sum(0,m) (\i. sum(0,n) (\j. a i j)) =
         sum(0,n) (\j. sum(0,m) (\i. a i j))`;;

let SUM_SWAP = `!m1 m2 n1 n2.
        sum(m1,m2) (\i. sum(n1,n2) (\j. a i j)) =
        sum(n1,n2) (\j. sum(m1,m2) (\i. a i j))`;;

let SER_SWAPDOUBLE_POS = `!z a l. (!m n. &0 <= a m n) /\ (!m. (a m) sums (z m)) /\ z sums l
           ==> ?s. (!n. (\m. a m n) sums (s n)) /\ s sums l`;;

(* ------------------------------------------------------------------------- *)
(* Hence we get a power series for cot with nice convergence property.       *)
(* ------------------------------------------------------------------------- *)

let COT_PARTIAL_FRACTIONS_FROM1 = `~integer x
    ==> (\n. (&2 * x pow 2) / (x pow 2 - &(n + 1) pow 2)) sums
        (pi * x) * cot (pi * x) - &1`;;

let COT_ALT_POWSER = `!x. &0 < abs(x) /\ abs(x) < &1
       ==> ?s. (!n. (\m. &2 * (x pow 2 / &(m + 1) pow 2) pow (n + 1))
                    sums s n) /\
               s sums --((pi * x) * cot(pi * x) - &1)`;;

(* ------------------------------------------------------------------------- *)
(* General unpairing result.                                                 *)
(* ------------------------------------------------------------------------- *)

let SER_INSERTZEROS = `(\n. c(2 * n)) sums l
   ==> (\n. if ODD n then &0 else c(n)) sums l`;;

(* ------------------------------------------------------------------------- *)
(* Mangle this into a standard power series.                                 *)
(* ------------------------------------------------------------------------- *)

let COT_POWSER_SQUARED_FORM = `!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. &2 * (x / pi) pow (2 * (n + 1)) *
                suminf (\m. inv (&(m + 1) pow (2 * (n + 1)))))
           sums --(x * cot x - &1)`;;

let COT_POWSER_SQUAREDAGAIN = `!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1
                 else --(&2) *
                      suminf (\m. inv (&(m + 1) pow (2 * n))) /
                      pi pow (2 * n)) *
                x pow (2 * n))
           sums (x * cot(x))`;;

let COT_X_POWSER = `!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1 else if ODD n then &0 else
                 --(&2) * suminf (\m. inv (&(m + 1) pow n)) / pi pow n) *
                x pow n)
           sums (x * cot(x))`;;

(* ------------------------------------------------------------------------- *)
(* Hence use the double-angle formula to get a series for tangent.           *)
(* ------------------------------------------------------------------------- *)

let TAN_COT_DOUBLE = `!x. &0 < abs(x) /\ abs(x) < pi / &2
        ==> (tan(x) = cot(x) - &2 * cot(&2 * x))`;;

let TAN_POWSER_WEAK = `!x. &0 < abs(x) /\ abs(x) < pi / &2
       ==> (\n. (if EVEN n then &0 else
                 &2 * (&2 pow (n + 1) - &1) *
                 suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1)) *
                x pow n)
           sums (tan x)`;;

let TAN_POWSER = `!x. abs(x) < pi / &2
       ==> (\n. (if EVEN n then &0 else
                 &2 * (&2 pow (n + 1) - &1) *
                 suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1)) *
                x pow n)
           sums (tan x)`;;

(* ------------------------------------------------------------------------- *)
(* Add polynomials to differentiator's known functions, for next proofs.     *)
(* ------------------------------------------------------------------------- *)

let th = `(f diffl l)(x) ==>
    ((\x. poly p (f x)) diffl (l * poly (poly_diff p) (f x)))(x)`;;

(* ------------------------------------------------------------------------- *)
(* Define tangent polynomials and tangent numbers on this pattern.           *)
(* ------------------------------------------------------------------------- *)

let tanpoly = new_recursive_definition num_RECURSION
  `(tanpoly 0 = [&0; &1]) /\
   (!n. tanpoly (SUC n) = [&1; &0; &1] ** poly_diff(tanpoly n))`;;

let TANPOLYS_RULE =
  let pth1,pth2 = CONJ_PAIR tanpoly in
  let base = [pth1]
  and rule = GEN_REWRITE_RULE LAND_CONV [GSYM pth2] in
  let poly_diff_tm = `poly_diff`
  and poly_mul_tm = `( ** ) [&1; &0; &1]` in
  let rec tanpolys n =
    if n < 0 then []
    else if n = 0 then base else
    let thl = tanpolys (n - 1) in
    let th1 = AP_TERM poly_diff_tm (hd thl) in
    let th2 = TRANS th1 (POLY_DIFF_CONV (rand(concl th1))) in
    let th3 = AP_TERM poly_mul_tm th2 in
    let th4 = TRANS th3 (POLY_MUL_CONV (rand(concl th3))) in
    let th5 = rule th4 in
    let th6 = CONV_RULE (LAND_CONV(RAND_CONV NUM_SUC_CONV)) th5 in
    th6::thl in
  rev o tanpolys;;

let TANPOLY_CONV =
  let tanpoly_tm = `tanpoly` in
  fun tm ->
    let l,r = dest_comb tm in
    if l <> tanpoly_tm then failwith "TANPOLY_CONV"
    else last(TANPOLYS_RULE(dest_small_numeral r));;

let tannumber = new_definition
  `tannumber n = poly (tanpoly n) (&0)`;;

let TANNUMBERS_RULE,TANNUMBER_CONV =
  let POLY_0_THM = `(poly [] (&0) = &0) /\
     (poly (CONS h t) (&0) = h)`;;

let th = `(f diffl l)(x) /\ ~(cos(f x) = &0)
   ==> ((\x. poly (tanpoly n) (tan(f x))) diffl
        (l * poly (tanpoly(SUC n)) (tan(f x))))(x)`;;

let TAN_DERIV_POWSER = `!n x. abs(x) < pi / &2
         ==> (\m. ITER n diffs
                   (\i. if EVEN i
                        then &0
                        else &2 *
                             (&2 pow (i + 1) - &1) *
                             suminf (\m. inv (&(m + 1) pow (i + 1))) /
                             pi pow (i + 1)) m *
                  x pow m)
             sums (poly (tanpoly n) (tan x))`;;

let ITER_DIFFS_LEMMA = `!n c. ITER n diffs c 0 = &(FACT n) * c(n)`;;

let TANNUMBER_HARMONICSUMS = `!n. ODD n
       ==> (&2 * (&2 pow (n + 1) - &1) * &(FACT n) *
            suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1) =
            tannumber n)`;;

let HARMONICSUMS_TANNUMBER = `!n. EVEN n /\ ~(n = 0)
       ==> (suminf (\m. inv (&(m + 1) pow n)) / pi pow n =
            tannumber(n - 1) / (&2 * &(FACT(n - 1)) * (&2 pow n - &1)))`;;

(* ------------------------------------------------------------------------- *)
(* For uniformity, show that even tannumbers are zero.                       *)
(* ------------------------------------------------------------------------- *)

let ODD_POLY_DIFF = `(!x. poly p (--x) = poly p x)
   ==> (!x. poly (poly_diff p) (--x) = --(poly(poly_diff p) x))`;;

let EVEN_POLY_DIFF = `(!x. poly p (--x) = --(poly p x))
   ==> (!x. poly (poly_diff p) (--x) = poly(poly_diff p) x)`;;

let TANPOLY_ODD_EVEN = `!n x. (poly (tanpoly n) (--x) =
          if EVEN n then --(poly (tanpoly n) x) else poly (tanpoly n) x)`;;

let TANNUMBER_EVEN = `!n. EVEN n ==> (tannumber n = &0)`;;

(* ------------------------------------------------------------------------- *)
(* Hence get tidy series.                                                    *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_TAN_CONVERGES = `!x. abs(x) < pi / &2
       ==> (\n. tannumber n / &(FACT n) * x pow n) sums (tan x)`;;

let TAYLOR_X_COT_CONVERGES = `!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1 else
                 tannumber (n - 1) / ((&1 - &2 pow n) * &(FACT(n - 1)))) *
                x pow n)
           sums (x * cot(x))`;;

(* ------------------------------------------------------------------------- *)
(* Get a simple bound on the tannumbers.                                     *)
(* ------------------------------------------------------------------------- *)

let TANNUMBER_BOUND = `!n. abs(tannumber n) <= &4 * &(FACT n) * (&2 / pi) pow (n + 1)`;;

(* ------------------------------------------------------------------------- *)
(* Also get some harmonic sums.                                              *)
(* ------------------------------------------------------------------------- *)

let HARMONIC_SUMS = `!n. (\m. inv (&(m + 1) pow (2 * (n + 1))))
       sums (pi pow (2 * (n + 1)) *
             tannumber(2 * n + 1) /
             (&2 * (&2 pow (2 * (n + 1)) - &1) * &(FACT(2 * n + 1))))`;;

let mk_harmonic =
  let pth = `x * &1 / n = x / n`;;

(* ------------------------------------------------------------------------- *)
(* Isolate the most famous special case.                                     *)
(* ------------------------------------------------------------------------- *)

let EULER_HARMONIC_SUM = mk_harmonic 2;;

(* ------------------------------------------------------------------------- *)
(* Canonical Taylor series for tan and cot with truncation bounds.           *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_TAN_BOUND_GENERAL = `!x n. abs(x) <= &1
         ==> abs(tan x - sum (0,n) (\m. tannumber m / &(FACT m) * x pow m))
             <= &12 * (&2 / &3) pow (n + 1) * abs(x) pow n`;;

let TAYLOR_TAN_BOUND = `!x n k. abs(x) <= inv(&2 pow k)
           ==> abs(tan x -
                   sum (0,n) (\m. tannumber(m) / &(FACT(m)) * x pow m))
               <= &12 * (&2 / &3) pow (n + 1) * inv(&2 pow (k * n))`;;

let TAYLOR_TANX_BOUND = `!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs(tan x / x -
                   sum (0,n) (\m. tannumber(m+1) / &(FACT(m+1)) * x pow m))
               <= &12 * (&2 / &3) pow (n + 2) * inv(&2 pow (k * n))`;;

let TAYLOR_TANX_SQRT_BOUND = `!x n k. abs(x) <= inv(&2 pow k) /\ &0 < x
           ==> abs(tan (sqrt x) / sqrt(x) -
                   sum(0,n) (\m. tannumber(2 * m + 1) / &(FACT(2 * m + 1)) *
                                 x pow m))
               <= &12 * (&2 / &3) pow (2 * n + 2) *
                  inv(&2 pow (k DIV 2 * 2 * n))`;;

let TAYLOR_COT_BOUND_GENERAL = `!x n. abs(x) <= &1 /\ ~(x = &0)
         ==> abs((&1 / x - cot x) -
                 sum (0,n) (\m. (tannumber m /
                                 ((&2 pow (m+1) - &1) * &(FACT(m)))) *
                                x pow m))
             <= &4 * (abs(x) / &3) pow n`;;

let TAYLOR_COT_BOUND = `!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 / x - cot x) -
                   sum (0,n) (\m. (tannumber m /
                                   ((&2 pow (m+1) - &1) * &(FACT(m)))) *
                                  x pow m))
               <= &4 / &3 pow n * inv(&2 pow (k * n))`;;

let TAYLOR_COTX_BOUND = `!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 / x - cot x) / x -
                   sum (0,n) (\m. (tannumber(m+1) /
                                   ((&2 pow (m+2) - &1) * &(FACT(m+1)))) *
                                  x pow m))
               <= (&4 / &3) / &3 pow n * inv(&2 pow (k * n))`;;

let TAYLOR_COTXX_BOUND = `!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 - x * cot(x)) -
                   sum(0,n) (\m. (tannumber (m-1) /
                                  ((&2 pow m - &1) * &(FACT(m-1)))) *
                                 x pow m))
               <= &12 / &3 pow n * inv(&2 pow (k * n))`;;

let TAYLOR_COTXX_SQRT_BOUND = `!x n k. abs(x) <= inv(&2 pow k) /\ &0 < x
           ==> abs((&1 - sqrt(x) * cot(sqrt(x))) -
                   sum(0,n) (\m. (tannumber (2*m-1) /
                                  ((&2 pow (2*m) - &1) * &(FACT(2*m-1)))) *
                                 x pow m))
               <= &12 / &3 pow (2 * n) * inv(&2 pow (k DIV 2 * 2 * n))`;;
