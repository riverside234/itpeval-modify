(* ========================================================================= *)
(* Bernoulli numbers and polynomials; sum of kth powers.                     *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Library/analysis.ml";;
needs "Library/transc.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* A couple of basic lemmas about new-style sums.                            *)
(* ------------------------------------------------------------------------- *)

let SUM_DIFFS = `!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i + 1) - a(i)) = a(n + 1) - a(m)`;;

let DIFF_SUM = `!f f' a b.
        (!k. a <= k /\ k <= b ==> ((\x. f x k) diffl f'(k)) x)
        ==> ((\x. sum(a..b) (f x)) diffl (sum(a..b) f')) x`;;

(* ------------------------------------------------------------------------- *)
(* Bernoulli numbers.                                                        *)
(* ------------------------------------------------------------------------- *)

let bernoulli = define
 `(bernoulli 0 = &1) /\
  (!n. bernoulli(SUC n) =
       --sum(0..n) (\j. &(binom(n + 2,j)) * bernoulli j) / (&n + &2))`;;

(* ------------------------------------------------------------------------- *)
(* A slightly tidier-looking form of the recurrence.                         *)
(* ------------------------------------------------------------------------- *)

let BERNOULLI = `!n. sum(0..n) (\j. &(binom(n + 1,j)) * bernoulli j) =
       if n = 0 then &1 else &0`;;

(* ------------------------------------------------------------------------- *)
(* Bernoulli polynomials.                                                    *)
(* ------------------------------------------------------------------------- *)

let bernpoly = new_definition
 `bernpoly n x = sum(0..n) (\k. &(binom(n,k)) * bernoulli k * x pow (n - k))`;;

(* ------------------------------------------------------------------------- *)
(* The key derivative recurrence.                                            *)
(* ------------------------------------------------------------------------- *)

let DIFF_BERNPOLY = `!n x. ((bernpoly (SUC n)) diffl (&(SUC n) * bernpoly n x)) x`;;

(* ------------------------------------------------------------------------- *)
(* Hence the key stepping recurrence.                                        *)
(* ------------------------------------------------------------------------- *)

let INTEGRALS_EQ = `!f g. (!x. ((\x. f(x) - g(x)) diffl &0) x) /\ f(&0) = g(&0)
         ==> !x. f(x) = g(x)`;;

let RECURRENCE_BERNPOLY = `!n x. bernpoly n (x + &1) - bernpoly n x = &n * x pow (n - 1)`;;

(* ------------------------------------------------------------------------- *)
(* Hence we get the main result.                                             *)
(* ------------------------------------------------------------------------- *)

let SUM_OF_POWERS = `!n. sum(0..n) (\k. &k pow m) =
        (bernpoly(SUC m) (&n + &1) - bernpoly(SUC m) (&0)) / (&m + &1)`;;

(* ------------------------------------------------------------------------- *)
(* Now explicit computations of the various terms on specific instances.     *)
(* ------------------------------------------------------------------------- *)

let SUM_CONV =
  let pth = `sum(0..0) f = f 0 /\ sum(0..SUC n) f = sum(0..n) f + f(SUC n)`;;

let BERNPOLY_CONV =
  let conv_1 =
    REWR_CONV bernpoly THENC SUM_CONV THENC
    TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV
  and conv_3 =
    ONCE_DEPTH_CONV BINOM_CONV THENC REAL_POLY_CONV in
  fun tm ->
    let n = dest_small_numeral(lhand tm) in
    let conv_2 = GEN_REWRITE_CONV ONCE_DEPTH_CONV (BERNOULLIS n) in
    (conv_1 THENC conv_2 THENC conv_3) tm;;

let SOP_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow m) =
        (\p. (p(&n + &1) - p(&0)) / (&m + &1))
        (\x. bernpoly (SUC m) x)`,
    REWRITE_TAC[SUM_OF_POWERS]) in
  let conv_0 = REWR_CONV pth in
  REWR_CONV pth THENC
  RAND_CONV(ABS_CONV(LAND_CONV NUM_SUC_CONV THENC BERNPOLY_CONV)) THENC
  TOP_DEPTH_CONV BETA_CONV THENC
  REAL_POLY_CONV;;

let SOP_NUM_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow p) = &m ==> nsum(0..n) (\k. k EXP p) = m`,
    REWRITE_TAC[REAL_OF_NUM_POW; GSYM REAL_OF_NUM_SUM_NUMSEG;
                REAL_OF_NUM_EQ]) in
  let rule_1 = PART_MATCH (lhs o rand) pth in
  fun tm ->
    let th1 = rule_1 tm in
    let th2 = SOP_CONV(lhs(lhand(concl th1))) in
    MATCH_MP th1 th2;;

(* ------------------------------------------------------------------------- *)
(* The example Bernoulli bragged about.                                      *)
(* ------------------------------------------------------------------------- *)

time SOP_NUM_CONV `nsum(0..1000) (\k. k EXP 10)`;;

(* ------------------------------------------------------------------------- *)
(* The general formulas for moderate powers.                                 *)
(* ------------------------------------------------------------------------- *)

time SOP_CONV `sum(0..n) (\k. &k pow 0)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 1)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 2)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 3)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 4)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 5)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 6)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 7)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 8)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 9)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 10)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 11)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 12)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 13)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 14)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 15)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 16)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 17)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 18)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 19)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 20)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 21)`;;
