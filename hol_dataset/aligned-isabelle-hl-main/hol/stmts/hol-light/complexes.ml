(* ========================================================================= *)
(* The type "real^2" regarded as the complex numbers.                        *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

new_type_abbrev("complex",`:real^2`);;

let prioritize_complex() =
  overload_interface("--",`vector_neg:complex->complex`);
  overload_interface("+",`vector_add:complex->complex->complex`);
  overload_interface("-",`vector_sub:complex->complex->complex`);
  overload_interface("*",`complex_mul:complex->complex->complex`);
  overload_interface("/",`complex_div:complex->complex->complex`);
  overload_interface("pow",`complex_pow:complex->num->complex`);
  overload_interface("inv",`complex_inv:complex->complex`);;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Real and imaginary parts of a number.                                     *)
(* ------------------------------------------------------------------------- *)

let RE_DEF = new_definition
  `Re(z:complex) = z$1`;;

let IM_DEF = new_definition
  `Im(z:complex) = z$2`;;

(* ------------------------------------------------------------------------- *)
(* Real injection and imaginary unit.                                        *)
(* ------------------------------------------------------------------------- *)

let complex = new_definition
 `complex(x,y) = vector[x;y]:complex`;;

let CX_DEF = new_definition
 `Cx(a) = complex(a,&0)`;;

let ii = new_definition
  `ii = complex(&0,&1)`;;

(* ------------------------------------------------------------------------- *)
(* Complex multiplication.                                                   *)
(* ------------------------------------------------------------------------- *)

let complex_mul = new_definition
  `w * z = complex(Re(w) * Re(z) - Im(w) * Im(z),
                   Re(w) * Im(z) + Im(w) * Re(z))`;;

let complex_inv = new_definition
  `inv(z) = complex(Re(z) / (Re(z) pow 2 + Im(z) pow 2),
                    --(Im(z)) / (Re(z) pow 2 + Im(z) pow 2))`;;

let complex_div = new_definition
  `w / z = w * inv(z)`;;

let complex_pow = define
  `(x pow 0 = Cx(&1)) /\
   (!n. x pow (SUC n) = x * x pow n)`;;

(* ------------------------------------------------------------------------- *)
(* Various handy rewrites.                                                   *)
(* ------------------------------------------------------------------------- *)

let RE = `(Re(complex(x,y)) = x)`;;

let IM = `Im(complex(x,y)) = y`;;

let COMPLEX_EQ = `!w z. (w = z) <=> (Re(w) = Re(z)) /\ (Im(w) = Im(z))`;;

let COMPLEX = `!z. complex(Re(z),Im(z)) = z`;;

let COMPLEX_EQ_0 = `z = Cx(&0) <=> Re(z) pow 2 + Im(z) pow 2 = &0`;;

let FORALL_COMPLEX = `(!z. P z) <=> (!x y. P(complex(x,y)))`;;

let EXISTS_COMPLEX = `(?z. P z) <=> (?x y. P(complex(x,y)))`;;

(* ------------------------------------------------------------------------- *)
(* Pseudo-definitions of other general vector concepts over R^2.             *)
(* ------------------------------------------------------------------------- *)

let complex_neg = `--z = complex(--(Re(z)),--(Im(z)))`;;

let complex_add = `w + z = complex(Re(w) + Re(z),Im(w) + Im(z))`;;

let complex_sub = VECTOR_ARITH `(w:complex) - z = w + --z`;;

let complex_norm = `norm(z) = sqrt(Re(z) pow 2 + Im(z) pow 2)`;;

let COMPLEX_SQNORM = `norm(z) pow 2 = Re(z) pow 2 + Im(z) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Crude tactic to automate very simple algebraic equivalences.              *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_COMPLEX_ARITH_TAC =
  REWRITE_TAC[COMPLEX_EQ; RE; IM; CX_DEF;
              complex_add; complex_neg; complex_sub; complex_mul;
              complex_inv; complex_div] THEN
  CONV_TAC REAL_FIELD;;

let SIMPLE_COMPLEX_ARITH tm = prove(tm,SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Basic algebraic properties that can be proved automatically by this.      *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_ADD_SYM = `!x y. x + y = y + x`;;

let COMPLEX_ADD_ASSOC = `!x y z. x + y + z = (x + y) + z`;;

let COMPLEX_ADD_LID = `!x. Cx(&0) + x = x`;;

let COMPLEX_ADD_LINV = `!x. --x + x = Cx(&0)`;;

let COMPLEX_MUL_SYM = `!x y. x * y = y * x`;;

let COMPLEX_MUL_ASSOC = `!x y z. x * y * z = (x * y) * z`;;

let COMPLEX_MUL_LID = `!x. Cx(&1) * x = x`;;

let COMPLEX_ADD_LDISTRIB = `!x y z. x * (y + z) = x * y + x * z`;;

let COMPLEX_ADD_AC = `(m + n = n + m) /\ ((m + n) + p = m + n + p) /\ (m + n + p = n + m + p)`;;

let COMPLEX_MUL_AC = `(m * n = n * m) /\ ((m * n) * p = m * n * p) /\ (m * n * p = n * m * p)`;;

let COMPLEX_ADD_RID = `!x. x + Cx(&0) = x`;;

let COMPLEX_MUL_RID = `!x. x * Cx(&1) = x`;;

let COMPLEX_ADD_RINV = `!x. x + --x = Cx(&0)`;;

let COMPLEX_ADD_RDISTRIB = `!x y z. (x + y) * z = x * z + y * z`;;

let COMPLEX_EQ_ADD_LCANCEL = `!x y z. (x + y = x + z) <=> (y = z)`;;

let COMPLEX_EQ_ADD_RCANCEL = `!x y z. (x + z = y + z) <=> (x = y)`;;

let COMPLEX_MUL_RZERO = `!x. x * Cx(&0) = Cx(&0)`;;

let COMPLEX_MUL_LZERO = `!x. Cx(&0) * x = Cx(&0)`;;

let COMPLEX_NEG_NEG = `!x. --(--x) = x`;;

let COMPLEX_MUL_RNEG = `!x y. x * --y = --(x * y)`;;

let COMPLEX_MUL_LNEG = `!x y. --x * y = --(x * y)`;;

let COMPLEX_NEG_ADD = `!x y. --(x + y) = --x + --y`;;

let COMPLEX_NEG_0 = `--Cx(&0) = Cx(&0)`;;

let COMPLEX_EQ_ADD_LCANCEL_0 = `!x y. (x + y = x) <=> (y = Cx(&0))`;;

let COMPLEX_EQ_ADD_RCANCEL_0 = `!x y. (x + y = y) <=> (x = Cx(&0))`;;

let COMPLEX_LNEG_UNIQ = `!x y. (x + y = Cx(&0)) <=> (x = --y)`;;

let COMPLEX_RNEG_UNIQ = `!x y. (x + y = Cx(&0)) <=> (y = --x)`;;

let COMPLEX_NEG_LMUL = `!x y. --(x * y) = --x * y`;;

let COMPLEX_NEG_RMUL = `!x y. --(x * y) = x * --y`;;

let COMPLEX_NEG_MUL2 = `!x y. --x * --y = x * y`;;

let COMPLEX_SUB_ADD = `!x y. x - y + y = x`;;

let COMPLEX_SUB_ADD2 = `!x y. y + x - y = x`;;

let COMPLEX_SUB_REFL = `!x. x - x = Cx(&0)`;;

let COMPLEX_SUB_0 = `!x y. (x - y = Cx(&0)) <=> (x = y)`;;

let COMPLEX_NEG_EQ_0 = `!x. (--x = Cx(&0)) <=> (x = Cx(&0))`;;

let COMPLEX_NEG_SUB = `!x y. --(x - y) = y - x`;;

let COMPLEX_ADD_SUB = `!x y. (x + y) - x = y`;;

let COMPLEX_NEG_EQ = `!x y. (--x = y) <=> (x = --y)`;;

let COMPLEX_NEG_MINUS1 = `!x. --x = --Cx(&1) * x`;;

let COMPLEX_SUB_SUB = `!x y. x - y - x = --y`;;

let COMPLEX_ADD2_SUB2 = `!a b c d. (a + b) - (c + d) = a - c + b - d`;;

let COMPLEX_SUB_LZERO = `!x. Cx(&0) - x = --x`;;

let COMPLEX_SUB_RZERO = `!x. x - Cx(&0) = x`;;

let COMPLEX_SUB_LNEG = `!x y. --x - y = --(x + y)`;;

let COMPLEX_SUB_RNEG = `!x y. x - --y = x + y`;;

let COMPLEX_SUB_NEG2 = `!x y. --x - --y = y - x`;;

let COMPLEX_SUB_TRIANGLE = `!a b c. a - b + b - c = a - c`;;

let COMPLEX_EQ_SUB_LADD = `!x y z. (x = y - z) <=> (x + z = y)`;;

let COMPLEX_EQ_SUB_RADD = `!x y z. (x - y = z) <=> (x = z + y)`;;

let COMPLEX_SUB_SUB2 = `!x y. x - (x - y) = y`;;

let COMPLEX_ADD_SUB2 = `!x y. x - (x + y) = --y`;;

let COMPLEX_DIFFSQ = `!x y. (x + y) * (x - y) = x * x - y * y`;;

let COMPLEX_EQ_NEG2 = `!x y. (--x = --y) <=> (x = y)`;;

let COMPLEX_SUB_LDISTRIB = `!x y z. x * (y - z) = x * y - x * z`;;

let COMPLEX_SUB_RDISTRIB = `!x y z. (x - y) * z = x * z - y * z`;;

let COMPLEX_MUL_2 = `!x. Cx(&2) * x = x + x`;;

(* ------------------------------------------------------------------------- *)
(* Sometimes here we need to tweak non-zeroness assertions.                  *)
(* ------------------------------------------------------------------------- *)

let II_NZ = `~(ii = Cx(&0))`;;

let COMPLEX_MUL_LINV = `!z. ~(z = Cx(&0)) ==> (inv(z) * z = Cx(&1))`;;

let COMPLEX_ENTIRE = `!x y. (x * y = Cx(&0)) <=> (x = Cx(&0)) \/ (y = Cx(&0))`;;

let COMPLEX_MUL_RINV = `!z. ~(z = Cx(&0)) ==> (z * inv(z) = Cx(&1))`;;

let COMPLEX_DIV_REFL = `!x. ~(x = Cx(&0)) ==> (x / x = Cx(&1))`;;

let COMPLEX_VEC_0 = `vec 0 = Cx(&0)`;;

let COMPLEX_CMUL = `!c x. c % x = Cx(c) * x`;;

(* ------------------------------------------------------------------------- *)
(* More about powers.                                                        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POW_ADD = `!x m n. x pow (m + n) = x pow m * x pow n`;;

let COMPLEX_POW_POW = `!x m n. (x pow m) pow n = x pow (m * n)`;;

let COMPLEX_POW_1 = `!x. x pow 1 = x`;;

let COMPLEX_POW_2 = `!x. x pow 2 = x * x`;;

let COMPLEX_POW_NEG = `!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)`;;

let COMPLEX_POW_ONE = `!n. Cx(&1) pow n = Cx(&1)`;;

let COMPLEX_POW_MUL = `!x y n. (x * y) pow n = (x pow n) * (y pow n)`;;

let COMPLEX_POW_II_2 = `ii pow 2 = --Cx(&1)`;;

let COMPLEX_POW_EQ_0 = `!x n. (x pow n = Cx(&0)) <=> (x = Cx(&0)) /\ ~(n = 0)`;;

let COMPLEX_POW_ZERO = `!n. Cx(&0) pow n = if n = 0 then Cx(&1) else Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* Homomorphic embedding properties for Cx mapping.                          *)
(* ------------------------------------------------------------------------- *)

let CX_INJ = `!x y. (Cx(x) = Cx(y)) <=> (x = y)`;;

let CX_NEG = `!x. Cx(--x) = --(Cx(x))`;;

let CX_ADD = `!x y. Cx(x + y) = Cx(x) + Cx(y)`;;

let CX_SUB = `!x y. Cx(x - y) = Cx(x) - Cx(y)`;;

let CX_INV = `!x. Cx(inv x) = inv(Cx x)`;;

let CX_MUL = `!x y. Cx(x * y) = Cx(x) * Cx(y)`;;

let CX_POW = `!x n. Cx(x pow n) = Cx(x) pow n`;;

let CX_DIV = `!x y. Cx(x / y) = Cx(x) / Cx(y)`;;

let CX_ABS = `!x. Cx(abs x) = Cx(norm(Cx(x)))`;;

let COMPLEX_NORM_CX = `!x. norm(Cx(x)) = abs(x)`;;

let DIST_CX = `!x y. dist(Cx x,Cx y) = abs(x - y)`;;

(* ------------------------------------------------------------------------- *)
(* Some "linear" things hold for Re and Im too.                              *)
(* ------------------------------------------------------------------------- *)

let RE_CX = `!x. Re(Cx x) = x`;;

let RE_NEG = `!x. Re(--x) = --Re(x)`;;

let RE_ADD = `!x y. Re(x + y) = Re(x) + Re(y)`;;

let RE_SUB = `!x y. Re(x - y) = Re(x) - Re(y)`;;

let IM_CX = `!x. Im(Cx x) = &0`;;

let IM_NEG = `!x. Im(--x) = --Im(x)`;;

let IM_ADD = `!x y. Im(x + y) = Im(x) + Im(y)`;;

let IM_SUB = `!x y. Im(x - y) = Im(x) - Im(y)`;;

(* ------------------------------------------------------------------------- *)
(* An "expansion" theorem into the traditional notation.                     *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EXPAND = `!z. z = Cx(Re z) + ii * Cx(Im z)`;;

let COMPLEX_TRAD = `!x y. complex(x,y) = Cx(x) + ii * Cx(y)`;;

(* ------------------------------------------------------------------------- *)
(* Real and complex parts of ii and multiples.                               *)
(* ------------------------------------------------------------------------- *)

let RE_II = `Re ii = &0`;;

let IM_II = `Im ii = &1`;;

let RE_MUL_II = `!z. Re(z * ii) = --(Im z) /\ Re(ii * z) = --(Im z)`;;

let IM_MUL_II = `!z. Im(z * ii) = Re z /\ Im(ii * z) = Re z`;;

let COMPLEX_NORM_II = `norm ii = &1`;;

(* ------------------------------------------------------------------------- *)
(* Limited "multiplicative" theorems for Re and Im.                          *)
(* ------------------------------------------------------------------------- *)

let RE_CMUL = `!a z. Re(a % z) = a * Re z`;;

let IM_CMUL = `!a z. Im(a % z) = a * Im z`;;

let RE_MUL_CX = `!x z. Re(Cx(x) * z) = x * Re z /\
         Re(z * Cx(x)) = Re z * x`;;

let IM_MUL_CX = `!x z. Im(Cx(x) * z) = x * Im z /\
         Im(z * Cx(x)) = Im z * x`;;

let RE_DIV_CX = `!z x. Re(z / Cx(x)) = Re(z) / x`;;

let IM_DIV_CX = `!z x. Im(z / Cx(x)) = Im(z) / x`;;

(* ------------------------------------------------------------------------- *)
(* Syntax constructors etc. for complex constants.                           *)
(* ------------------------------------------------------------------------- *)

let is_complex_const =
  let cx_tm = `Cx` in
  fun tm ->
    is_comb tm &&
    let l,r = dest_comb tm in l = cx_tm && is_ratconst r;;

let dest_complex_const =
  let cx_tm = `Cx` in
  fun tm ->
    let l,r = dest_comb tm in
    if l = cx_tm then rat_of_term r
    else failwith "dest_complex_const";;

let mk_complex_const =
  let cx_tm = `Cx` in
  fun r ->
    mk_comb(cx_tm,term_of_rat r);;

(* ------------------------------------------------------------------------- *)
(* Conversions for arithmetic on complex constants.                          *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RAT_EQ_CONV =
  GEN_REWRITE_CONV I [CX_INJ] THENC REAL_RAT_EQ_CONV;;

let COMPLEX_RAT_MUL_CONV =
  GEN_REWRITE_CONV I [GSYM CX_MUL] THENC RAND_CONV REAL_RAT_MUL_CONV;;

let COMPLEX_RAT_ADD_CONV =
  GEN_REWRITE_CONV I [GSYM CX_ADD] THENC RAND_CONV REAL_RAT_ADD_CONV;;

let COMPLEX_RAT_POW_CONV =
  let x_tm = `x:real`
  and n_tm = `n:num` in
  let pth = SYM(SPECL [x_tm; n_tm] CX_POW) in
  fun tm ->
    let lop,r = dest_comb tm in
    let op,bod = dest_comb lop in
    let th1 = INST [rand bod,x_tm; r,n_tm] pth in
    let tm1,tm2 = dest_comb(concl th1) in
    if rand tm1 <> tm then failwith "COMPLEX_RAT_POW_CONV" else
    let tm3,tm4 = dest_comb tm2 in
    TRANS th1 (AP_TERM tm3 (REAL_RAT_REDUCE_CONV tm4));;

(* ------------------------------------------------------------------------- *)
(* Complex polynomial normalizer.                                            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLY_CLAUSES = `(!x y z. x + (y + z) = (x + y) + z) /\
   (!x y. x + y = y + x) /\
   (!x. Cx(&0) + x = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x y. x * y = y * x) /\
   (!x. Cx(&1) * x = x) /\
   (!x. Cx(&0) * x = Cx(&0)) /\
   (!x y z. x * (y + z) = x * y + x * z) /\
   (!x. x pow 0 = Cx(&1)) /\
   (!x n. x pow (SUC n) = x * x pow n)`
and COMPLEX_POLY_NEG_CLAUSES = `(!x. --x = Cx(-- &1) * x) /\
   (!x y. x - y = x + Cx(-- &1) * y)`;;

let COMPLEX_POLY_NEG_CONV,COMPLEX_POLY_ADD_CONV,COMPLEX_POLY_SUB_CONV,
    COMPLEX_POLY_MUL_CONV,COMPLEX_POLY_POW_CONV,COMPLEX_POLY_CONV =
  SEMIRING_NORMALIZERS_CONV COMPLEX_POLY_CLAUSES COMPLEX_POLY_NEG_CLAUSES
   (is_complex_const,
    COMPLEX_RAT_ADD_CONV,COMPLEX_RAT_MUL_CONV,COMPLEX_RAT_POW_CONV)
   (<);;

(* ------------------------------------------------------------------------- *)
(* Extend it to handle "inv" and division, by constants after normalization. *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RAT_INV_CONV =
  REWR_CONV(GSYM CX_INV) THENC RAND_CONV REAL_RAT_INV_CONV;;

let COMPLEX_POLY_CONV =
  let neg_tm = `(--):complex->complex`
  and inv_tm = `inv:complex->complex`
  and add_tm = `(+):complex->complex->complex`
  and sub_tm = `(-):complex->complex->complex`
  and mul_tm = `(*):complex->complex->complex`
  and div_tm = `(/):complex->complex->complex`
  and pow_tm = `(pow):complex->num->complex`
  and div_conv = REWR_CONV complex_div in
  let rec COMPLEX_POLY_CONV tm =
    if not(is_comb tm) || is_ratconst tm then REFL tm else
    let lop,r = dest_comb tm in
    if lop = neg_tm then
      let th1 = AP_TERM lop (COMPLEX_POLY_CONV r) in
      TRANS th1 (COMPLEX_POLY_NEG_CONV (rand(concl th1)))
    else if lop = inv_tm then
      let th1 = AP_TERM lop (COMPLEX_POLY_CONV r) in
      TRANS th1 (TRY_CONV COMPLEX_RAT_INV_CONV (rand(concl th1)))
    else if not(is_comb lop) then REFL tm else
    let op,l = dest_comb lop in
    if op = pow_tm then
      let th1 = AP_THM (AP_TERM op (COMPLEX_POLY_CONV l)) r in
      TRANS th1 (TRY_CONV COMPLEX_POLY_POW_CONV (rand(concl th1)))
    else if op = add_tm || op = mul_tm || op = sub_tm then
      let th1 = MK_COMB(AP_TERM op (COMPLEX_POLY_CONV l),
                        COMPLEX_POLY_CONV r) in
      let fn = if op = add_tm then COMPLEX_POLY_ADD_CONV
               else if op = mul_tm then COMPLEX_POLY_MUL_CONV
               else COMPLEX_POLY_SUB_CONV in
      TRANS th1 (fn (rand(concl th1)))
    else if op = div_tm then
      let th1 = div_conv tm in
      TRANS th1 (COMPLEX_POLY_CONV (rand(concl th1)))
    else REFL tm in
  COMPLEX_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Complex number version of usual ring procedure.                           *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RING,complex_ideal_cofactors =
  let COMPLEX_INTEGRAL =
   `(!x. Cx(&0) * x = Cx(&0)) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))`
  and COMPLEX_RABINOWITSCH =
   `!x y:complex. ~(x = y) <=> ?z. (x - y) * z = Cx(&1)`
  and COMPLEX_IIII =
   `ii * ii + Cx(&1) = Cx(&0)` in
  let ring,ideal =
    RING_AND_IDEAL_CONV
        (dest_complex_const,mk_complex_const,COMPLEX_RAT_EQ_CONV,
         `(--):complex->complex`,`(+):complex->complex->complex`,
         `(-):complex->complex->complex`,`(inv):complex->complex`,
         `(*):complex->complex->complex`,`(/):complex->complex->complex`,
         `(pow):complex->num->complex`,
         COMPLEX_INTEGRAL,COMPLEX_RABINOWITSCH,COMPLEX_POLY_CONV)
  and ii_tm = `ii` and iiii_tm = concl COMPLEX_IIII in
  (fun tm -> if free_in ii_tm tm then
             MP (ring (mk_imp(iiii_tm,tm))) COMPLEX_IIII
             else ring tm),
  ideal;;

(* ------------------------------------------------------------------------- *)
(* Most basic properties of inverses.                                        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_INV_0 = `inv(Cx(&0)) = Cx(&0)`;;

let COMPLEX_INV_1 = `inv(Cx(&1)) = Cx(&1)`;;

let COMPLEX_INV_MUL = `!w z. inv(w * z) = inv(w) * inv(z)`;;

let COMPLEX_POW_INV = `!x n. (inv x) pow n = inv(x pow n)`;;

let COMPLEX_INV_INV = `!x:complex. inv(inv x) = x`;;

let COMPLEX_INV_DIV = `!w z:complex. inv(w / z) = z / w`;;

let COMPLEX_EQ_INV2 = `!w z:complex. inv w = inv z <=> w = z`;;

let SGN_RE_COMPLEX_INV = `!z. real_sgn(Re(inv z)) = real_sgn(Re z)`;;

let RE_COMPLEX_INV_GT_0 = `!z. &0 < Re(inv z) <=> &0 < Re z`;;

let RE_COMPLEX_INV_GE_0 = `!z. &0 <= Re(inv z) <=> &0 <= Re z`;;

(* ------------------------------------------------------------------------- *)
(* And also field procedure.                                                 *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EQ_MUL_LCANCEL = `!x y z. (x * y = x * z) <=> (x = Cx(&0)) \/ (y = z)`;;

let COMPLEX_EQ_MUL_RCANCEL = `!x y z. (x * z = y * z) <=> (x = y) \/ (z = Cx(&0))`;;

let COMPLEX_FIELD =
  let norm_net =
    itlist (net_of_thm false o SPEC_ALL)
     [FORALL_SIMP; EXISTS_SIMP; complex_div; COMPLEX_INV_INV; COMPLEX_INV_MUL;
      COMPLEX_POW_ADD]
    (net_of_conv
      `inv((x:complex) pow n)`
      (REWR_CONV(GSYM COMPLEX_POW_INV) o check (is_numeral o rand o rand))
      empty_net)
  and easy_nz_conv =
    LAND_CONV
     (GEN_REWRITE_CONV TRY_CONV[MESON[COMPLEX_POW_EQ_0; REAL_OF_NUM_EQ; CX_INJ]
       `~(x pow n = Cx(&0)) <=>
        ~((x:complex) = Cx(&0)) \/
        (Cx(&n) = Cx(&0)) \/
        ~(x pow n = Cx(&0))`] THENC
      TOP_DEPTH_CONV(REWR_CONV CX_INJ THENC REAL_RAT_EQ_CONV)) THENC
    GEN_REWRITE_CONV TRY_CONV [TAUT `(T ==> p) <=> p`] in
  let prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    NUM_REDUCE_CONV THENC
    TOP_DEPTH_CONV(REWRITES_CONV norm_net) THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV `(/\)` CONDS_CELIM_CONV THENC
    PRENEX_CONV
  and setup_conv = NNF_CONV THENC WEAK_CNF_CONV THENC CONJ_CANON_CONV
  and is_inv =
    let inv_tm = `inv:complex->complex`
    and is_div = is_binop `(/):complex->complex->complex` in
    fun tm -> (is_div tm || (is_comb tm && rator tm = inv_tm)) &&
              not(is_ratconst(rand tm)) in
  let BASIC_COMPLEX_FIELD tm =
    let is_freeinv t = is_inv t && free_in t tm in
    let itms = setify(map rand (find_terms is_freeinv tm)) in
    let hyps = map
     (fun t -> CONV_RULE easy_nz_conv (SPEC t COMPLEX_MUL_RINV)) itms in
    let tm' = itlist (fun th t -> mk_imp(concl th,t)) hyps tm in
    let th1 = setup_conv tm' in
    let cjs = conjuncts(rand(concl th1)) in
    let ths = map COMPLEX_RING cjs in
    let th2 = EQ_MP (SYM th1) (end_itlist CONJ ths) in
    rev_itlist (C MP) hyps th2 in
  fun tm ->
    let th0 = prenex_conv tm in
    let tm0 = rand(concl th0) in
    let avs,bod = strip_forall tm0 in
    let th1 = setup_conv bod in
    let ths = map BASIC_COMPLEX_FIELD (conjuncts(rand(concl th1))) in
    EQ_MP (SYM th0) (GENL avs (EQ_MP (SYM th1) (end_itlist CONJ ths)));;

(* ------------------------------------------------------------------------- *)
(* More trivial lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DIV_1 = `!z. z / Cx(&1) = z`;;

let COMPLEX_DIV_LMUL = `!x y. ~(y = Cx(&0)) ==> y * x / y = x`;;

let COMPLEX_DIV_RMUL = `!x y. ~(y = Cx(&0)) ==> x / y * y = x`;;

let COMPLEX_INV_II = `inv ii = --ii`;;

let COMPLEX_INV_EQ_0 = `!x. inv x = Cx(&0) <=> x = Cx(&0)`;;

let COMPLEX_INV_NEG = `!x:complex. inv(--x) = --(inv x)`;;

let COMPLEX_NEG_INV = `!x:complex. --(inv x) = inv(--x)`;;

let COMPLEX_INV_EQ_1 = `!x. inv x = Cx(&1) <=> x = Cx(&1)`;;

let COMPLEX_DIV_EQ_0 = `!w z. w / z = Cx(&0) <=> w = Cx(&0) \/ z = Cx(&0)`;;

let COMPLEX_POW_DIV = `!x y n. (x / y) pow n = (x pow n) / (y pow n)`;;

let COMPLEX_DIV_POW = `!x:complex n k:num.
      ~(x= Cx(&0)) /\ k <= n /\ ~(k = 0)
      ==> x pow (n - k) = x pow n / x pow k`;;

let COMPLEX_DIV_POW2 = `!z m n. ~(z = Cx(&0))
           ==> z pow m / z pow n =
               if n <= m then z pow (m - n) else inv(z pow (n - m))`;;

(* ------------------------------------------------------------------------- *)
(* Norms (aka "moduli").                                                     *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_NORM_ZERO = `!z. (norm z = &0) <=> (z = Cx(&0))`;;

let COMPLEX_NORM_NUM = `!n. norm(Cx(&n)) = &n`;;

let COMPLEX_NORM_0 = `norm(Cx(&0)) = &0`;;

let COMPLEX_NORM_NZ = `!z. &0 < norm(z) <=> ~(z = Cx(&0))`;;

let COMPLEX_NORM_MUL = `!w z. norm(w * z) = norm(w) * norm(z)`;;

let COMPLEX_NORM_POW = `!z n. norm(z pow n) = norm(z) pow n`;;

let COMPLEX_NORM_INV = `!z. norm(inv z) = inv(norm z)`;;

let COMPLEX_NORM_DIV = `!w z. norm(w / z) = norm(w) / norm(z)`;;

let COMPLEX_NORM_TRIANGLE_SUB = `!w z. norm(w) <= norm(w + z) + norm(z)`;;

let COMPLEX_NORM_ABS_NORM = `!w z. abs(norm w - norm z) <= norm(w - z)`;;

let COMPLEX_POW_EQ_1 = `!z n. z pow n = Cx(&1) ==> norm(z) = &1 \/ n = 0`;;

(* ------------------------------------------------------------------------- *)
(* Complex conjugate.                                                        *)
(* ------------------------------------------------------------------------- *)

let cnj = new_definition
  `cnj(z) = complex(Re(z),--(Im(z)))`;;

(* ------------------------------------------------------------------------- *)
(* Conjugation is an automorphism.                                           *)
(* ------------------------------------------------------------------------- *)

let CNJ_INJ = `!w z. (cnj(w) = cnj(z)) <=> (w = z)`;;

let CNJ_CNJ = `!z. cnj(cnj z) = z`;;

let CNJ_CX = `!x. cnj(Cx x) = Cx x`;;

let COMPLEX_NORM_CNJ = `!z. norm(cnj z) = norm(z)`;;

let CNJ_NEG = `!z. cnj(--z) = --(cnj z)`;;

let CNJ_INV = `!z. cnj(inv z) = inv(cnj z)`;;

let CNJ_ADD = `!w z. cnj(w + z) = cnj(w) + cnj(z)`;;

let CNJ_SUB = `!w z. cnj(w - z) = cnj(w) - cnj(z)`;;

let CNJ_MUL = `!w z. cnj(w * z) = cnj(w) * cnj(z)`;;

let CNJ_DIV = `!w z. cnj(w / z) = cnj(w) / cnj(z)`;;

let CNJ_POW = `!z n. cnj(z pow n) = cnj(z) pow n`;;

let RE_CNJ = `!z. Re(cnj z) = Re z`;;

let IM_CNJ = `!z. Im(cnj z) = --Im z`;;

let CNJ_EQ_CX = `!x z. cnj z = Cx x <=> z = Cx x`;;

let CNJ_EQ_0 = `!z. cnj z = Cx(&0) <=> z = Cx(&0)`;;

let COMPLEX_ADD_CNJ = `(!z. z + cnj z = Cx(&2 * Re z)) /\ (!z. cnj z + z = Cx(&2 * Re z))`;;

let CNJ_II = `cnj ii = --ii`;;

let CX_RE_CNJ = `!z. Cx(Re z) = (z + cnj z) / Cx(&2)`;;

let CX_IM_CNJ = `!z. Cx(Im z) = --ii * (z - cnj z) / Cx(&2)`;;

let FORALL_CNJ = `(!z. P(cnj z)) <=> (!z. P z)`;;

let EXISTS_CNJ = `(?z. P(cnj z)) <=> (?z. P z)`;;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc theorems relating multiplication, inverse and conjugation *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_NORM_POW_2 = `!z. Cx(norm z) pow 2 = z * cnj z`;;

let COMPLEX_MUL_CNJ = `!z. cnj z * z = Cx(norm(z)) pow 2 /\ z * cnj z = Cx(norm(z)) pow 2`;;

let COMPLEX_INV_CNJ = `!z. inv z = cnj z / Cx(norm z) pow 2`;;

let COMPLEX_DIV_CNJ = `!a b. a / b = (a * cnj b) / Cx(norm b) pow 2`;;

let RE_COMPLEX_DIV_EQ_0 = `!a b. Re(a / b) = &0 <=> Re(a * cnj b) = &0`;;

let IM_COMPLEX_DIV_EQ_0 = `!a b. Im(a / b) = &0 <=> Im(a * cnj b) = &0`;;

let RE_COMPLEX_DIV_GT_0 = `!a b. &0 < Re(a / b) <=> &0 < Re(a * cnj b)`;;

let IM_COMPLEX_DIV_GT_0 = `!a b. &0 < Im(a / b) <=> &0 < Im(a * cnj b)`;;

let RE_COMPLEX_DIV_GE_0 = `!a b. &0 <= Re(a / b) <=> &0 <= Re(a * cnj b)`;;

let IM_COMPLEX_DIV_GE_0 = `!a b. &0 <= Im(a / b) <=> &0 <= Im(a * cnj b)`;;

let RE_COMPLEX_DIV_LE_0 = `!a b. Re(a / b) <= &0 <=> Re(a * cnj b) <= &0`;;

let IM_COMPLEX_DIV_LE_0 = `!a b. Im(a / b) <= &0 <=> Im(a * cnj b) <= &0`;;

let RE_COMPLEX_DIV_LT_0 = `!a b. Re(a / b) < &0 <=> Re(a * cnj b) < &0`;;

let IM_COMPLEX_DIV_LT_0 = `!a b. Im(a / b) < &0 <=> Im(a * cnj b) < &0`;;

let IM_COMPLEX_INV_GE_0 = `!z. &0 <= Im(inv z) <=> Im(z) <= &0`;;

let IM_COMPLEX_INV_LE_0 = `!z. Im(inv z) <= &0 <=> &0 <= Im(z)`;;

let IM_COMPLEX_INV_GT_0 = `!z. &0 < Im(inv z) <=> Im(z) < &0`;;

let IM_COMPLEX_INV_LT_0 = `!z. Im(inv z) < &0 <=> &0 < Im(z)`;;

let IM_COMPLEX_INV_EQ_0 = `!z. Im(inv z) = &0 <=> Im(z) = &0`;;

let REAL_SGN_RE_COMPLEX_DIV = `!w z. real_sgn(Re(w / z)) = real_sgn(Re(w * cnj z))`;;

let REAL_SGN_IM_COMPLEX_DIV = `!w z. real_sgn(Im(w / z)) = real_sgn(Im(w * cnj z))`;;

(* ------------------------------------------------------------------------- *)
(* Norm versus components for complex numbers.                               *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_NORM_GE_RE_IM = `!z. abs(Re(z)) <= norm(z) /\ abs(Im(z)) <= norm(z)`;;

let COMPLEX_NORM_LE_RE_IM = `!z. norm(z) <= abs(Re z) + abs(Im z)`;;

let COMPLEX_L1_LE_NORM = `!z. sqrt(&2) / &2 * (abs(Re z) + abs(Im z)) <= norm z`;;

(* ------------------------------------------------------------------------- *)
(* Complex square roots.                                                     *)
(* ------------------------------------------------------------------------- *)

let csqrt = new_definition
  `csqrt(z) = if Im(z) = &0 then
                if &0 <= Re(z) then complex(sqrt(Re(z)),&0)
                else complex(&0,sqrt(--Re(z)))
              else complex(sqrt((norm(z) + Re(z)) / &2),
                           (Im(z) / abs(Im(z))) *
                           sqrt((norm(z) - Re(z)) / &2))`;;


let CSQRT = `!z. csqrt(z) pow 2 = z`;;

let CX_SQRT = `!x. &0 <= x ==> Cx(sqrt x) = csqrt(Cx x)`;;

let CSQRT_CX = `!x. &0 <= x ==> csqrt(Cx x) = Cx(sqrt x)`;;

let CSQRT_0 = `csqrt(Cx(&0)) = Cx(&0)`;;

let CSQRT_1 = `csqrt(Cx(&1)) = Cx(&1)`;;

let CSQRT_PRINCIPAL = `!z. &0 < Re(csqrt(z)) \/ Re(csqrt(z)) = &0 /\ &0 <= Im(csqrt(z))`;;

let RE_CSQRT = `!z. &0 <= Re(csqrt z)`;;

let CSQRT_UNIQUE = `!s z. s pow 2 = z /\ (&0 < Re s \/ Re s = &0 /\ &0 <= Im s)
         ==> csqrt z = s`;;

let POW_2_CSQRT = `!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im(z) ==> csqrt(z pow 2) = z`;;

let CSQRT_EQ_0 = `!z. csqrt z = Cx(&0) <=> z = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* A few more complex-specific cases of vector notions.                      *)
(* ------------------------------------------------------------------------- *)

let DOT_COMPLEX_MUL_CNJ = `!w z. w dot z = Re(w * cnj z)`;;

let DOT_CNJ = `!w z. cnj w dot cnj z = w dot z`;;

let LINEAR_COMPLEX_MUL = `!c. linear (\x. c * x)`;;

let BILINEAR_COMPLEX_MUL = `bilinear( * )`;;

let LINEAR_CNJ = `linear cnj`;;

let ORTHOGONAL_TRANSFORMATION_CNJ = `orthogonal_transformation cnj`;;

let LINEAR_COMPLEX_LMUL = `!f:real^N->complex c. linear f ==> linear (\x. c * f x)`;;

let LINEAR_COMPLEX_RMUL = `!f:real^N->complex c. linear f ==> linear (\x. f x * c)`;;

let COMPLEX_CAUCHY_SCHWARZ_EQ = `!w z. (w dot z) pow 2 + ((ii * w) dot z) pow 2 =
          norm(w) pow 2 * norm(z) pow 2`;;

let COMPLEX_BASIS = `basis 1 = Cx(&1) /\ basis 2 = ii`;;

let COMPLEX_LINEAR = `!f:complex->complex.
        (?c. f = \z. c * z) <=>
        linear f /\
        (matrix f)$1$1 = (matrix f)$2$2 /\
        (matrix f)$1$2 = --((matrix f)$2$1)`;;

let COMPLEX_LINEAR_ALT = `!f:complex->complex.
        (?c. f = \z. c * z) <=> linear f /\ f(ii) = ii * f(Cx(&1))`;;

let ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL = `!c. orthogonal_transformation(\z. c * z) <=> norm c = &1`;;

let COMPLEX_ORTHOGONAL_ROTATION = `!f:complex->complex.
        orthogonal_transformation f /\ det(matrix f) = &1 <=>
        ?c. norm c = &1 /\ f = \z. c * z`;;

let COMPLEX_ORTHOGONAL_ROTOINVERSION = `!f:complex->complex.
        orthogonal_transformation f /\ det(matrix f) = -- &1 <=>
        ?c. norm c = &1 /\ f = \z. c * cnj z`;;

let COMPLEX_ORTHOGONAL_TRANSFORMATION = `!f:complex->complex.
        orthogonal_transformation f <=>
        ?c. norm c = &1 /\ ((f = \z. c * z) \/ (f = \z. c * cnj z))`;;
(* ------------------------------------------------------------------------- *)
(* Complex-specific theorems about sums.                                     *)
(* ------------------------------------------------------------------------- *)

let RE_VSUM = `!f s. FINITE s ==> Re(vsum s f) = sum s (\x. Re(f x))`;;

let IM_VSUM = `!f s. FINITE s ==> Im(vsum s f) = sum s (\x. Im(f x))`;;

let VSUM_COMPLEX_LMUL = `!c f s. FINITE(s) ==> vsum s (\x. c * f x) = c * vsum s f`;;

let VSUM_COMPLEX_RMUL = `!c f s. FINITE(s) ==> vsum s (\x. f x * c) = vsum s f * c`;;

let VSUM_CX = `!f:A->real s. vsum s (\a. Cx(f a)) = Cx(sum s f)`;;

let CNJ_VSUM = `!f s. FINITE s ==> cnj(vsum s f) = vsum s (\x. cnj(f x))`;;

let VSUM_CX_NUMSEG = `!f m n. vsum (m..n) (\a. Cx(f a)) = Cx(sum (m..n) f)`;;

let COMPLEX_SUB_POW = `!x y n.
        1 <= n ==> x pow n - y pow n =
                   (x - y) * vsum(0..n-1) (\i. x pow i * y pow (n - 1 - i))`;;

let COMPLEX_SUB_POW_R1 = `!x n. 1 <= n
         ==> x pow n - Cx(&1) = (x - Cx(&1)) * vsum(0..n-1) (\i. x pow i)`;;

let COMPLEX_SUB_POW_L1 = `!x n. 1 <= n
         ==> Cx(&1) - x pow n = (Cx(&1) - x) * vsum(0..n-1) (\i. x pow i)`;;

(* ------------------------------------------------------------------------- *)
(* The complex numbers that are real (zero imaginary part).                  *)
(* ------------------------------------------------------------------------- *)

let real = new_definition
 `real z <=> Im z = &0`;;

let REAL = `!z. real z <=> Cx(Re z) = z`;;

let REAL_CNJ = `!z. real z <=> cnj z = z`;;

let REAL_IMP_CNJ = `!z. real z ==> cnj z = z`;;

let REAL_EXISTS = `!z. real z <=> ?x. z = Cx x`;;

let FORALL_REAL = `(!z. real z ==> P z) <=> (!x. P(Cx x))`;;

let EXISTS_REAL = `(?z. real z /\ P z) <=> (?x. P(Cx x))`;;

let REAL_CX = `!x. real(Cx x)`;;

let REAL_MUL_CX = `!x z. real(Cx x * z) <=> x = &0 \/ real z`;;

let REAL_ADD = `!w z. real w /\ real z ==> real(w + z)`;;

let REAL_NEG = `!z. real z ==> real(--z)`;;

let REAL_SUB = `!w z. real w /\ real z ==> real(w - z)`;;

let REAL_MUL = `!w z. real w /\ real z ==> real(w * z)`;;

let REAL_POW = `!z n. real z ==> real(z pow n)`;;

let REAL_INV = `!z. real z ==> real(inv z)`;;

let REAL_INV_EQ = `!z. real(inv z) = real z`;;

let REAL_DIV = `!w z. real w /\ real z ==> real(w / z)`;;

let REAL_VSUM = `!f s. FINITE s /\ (!a. a IN s ==> real(f a)) ==> real(vsum s f)`;;

let REAL_MUL_CNJ = `(!z. real(z * cnj z)) /\ (!z. real(cnj z * z))`;;

let REAL_SEGMENT = `!a b x. x IN segment[a,b] /\ real a /\ real b ==> real x`;;

let IN_SEGMENT_CX = `!a b x. Cx(x) IN segment[Cx(a),Cx(b)] <=>
                a <= x /\ x <= b \/ b <= x /\ x <= a`;;

let IN_SEGMENT_CX_GEN = `!a b x.
        x IN segment[Cx a,Cx b] <=>
        Im(x) = &0 /\ (a <= Re x /\ Re x <= b \/ b <= Re x /\ Re x <= a)`;;

let RE_POS_SEGMENT = `!a b x. x IN segment[a,b] /\ &0 < Re a /\ &0 < Re b ==> &0 < Re x`;;

let CONVEX_REAL = `convex real`;;

let IMAGE_CX = `!s. IMAGE Cx s = {z | real z /\ Re(z) IN s}`;;

let SUBSPACE_REAL = `subspace real`;;

let DIM_REAL = `dim real = 1`;;

let INTERIOR_REAL = `interior real = {}`;;

(* ------------------------------------------------------------------------- *)
(* Useful bound-type theorems for real quantities.                           *)
(* ------------------------------------------------------------------------- *)

let REAL_NORM = `!z. real z ==> norm(z) = abs(Re z)`;;

let REAL_NORM_POS = `!z. real z /\ &0 <= Re z ==> norm(z) = Re(z)`;;

let COMPLEX_NORM_VSUM_SUM_RE = `!f s. FINITE s /\ (!x. x IN s ==> real(f x) /\ &0 <= Re(f x))
         ==> norm(vsum s f) = sum s (\x. Re(f x))`;;

let COMPLEX_NORM_VSUM_BOUND = `!s f:A->complex g:A->complex.
        FINITE s /\ (!x. x IN s ==> real(g x) /\ norm(f x) <= Re(g x))
        ==> norm(vsum s f) <= norm(vsum s g)`;;

let COMPLEX_NORM_VSUM_BOUND_SUBSET = `!f:A->complex g:A->complex s t.
        FINITE s /\ t SUBSET s /\
        (!x. x IN s ==> real(g x) /\ norm(f x) <= Re(g x))
        ==> norm(vsum t f) <= norm(vsum s g)`;;

(* ------------------------------------------------------------------------- *)
(* Geometric progression.                                                    *)
(* ------------------------------------------------------------------------- *)

let VSUM_GP_BASIC = `!x n. (Cx(&1) - x) * vsum(0..n) (\i. x pow i) = Cx(&1) - x pow (SUC n)`;;

let VSUM_GP_MULTIPLIED = `!x m n. m <= n
           ==> ((Cx(&1) - x) * vsum(m..n) (\i. x pow i) =
                x pow m - x pow (SUC n))`;;

let VSUM_GP = `!x m n.
        vsum(m..n) (\i. x pow i) =
                if n < m then Cx(&0)
                else if x = Cx(&1) then Cx(&((n + 1) - m))
                else (x pow m - x pow (SUC n)) / (Cx(&1) - x)`;;

let VSUM_GP_OFFSET = `!x m n. vsum(m..m+n) (\i. x pow i) =
                if x = Cx(&1) then Cx(&n) + Cx(&1)
                else x pow m * (Cx(&1) - x pow (SUC n)) / (Cx(&1) - x)`;;

(* ------------------------------------------------------------------------- *)
(* Basics about polynomial functions: extremal behaviour and root counts.    *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_SUB_POLYFUN = `!a x y n.
   1 <= n
   ==> vsum(0..n) (\i. a i * x pow i) - vsum(0..n) (\i. a i * y pow i) =
       (x - y) *
       vsum(0..n-1) (\j. vsum(j+1..n) (\i. a i * y pow (i - j - 1)) * x pow j)`;;

let COMPLEX_SUB_POLYFUN_ALT = `!a x y n.
    1 <= n
    ==> vsum(0..n) (\i. a i * x pow i) - vsum(0..n) (\i. a i * y pow i) =
        (x - y) *
        vsum(0..n-1) (\j. vsum(0..n-j-1) (\k. a(j+k+1) * y pow k) * x pow j)`;;

let COMPLEX_POLYFUN_LINEAR_FACTOR = `!a c n. ?b. !z. vsum(0..n) (\i. c(i) * z pow i) =
                   (z - a) * vsum(0..n-1) (\i. b(i) * z pow i) +
                    vsum(0..n) (\i. c(i) * a pow i)`;;

let COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT = `!a c n. vsum(0..n) (\i. c(i) * a pow i) = Cx(&0)
           ==> ?b. !z. vsum(0..n) (\i. c(i) * z pow i) =
                      (z - a) * vsum(0..n-1) (\i. b(i) * z pow i)`;;

let COMPLEX_POLYFUN_EXTREMAL_LEMMA = `!c n e. &0 < e
           ==> ?M. !z. M <= norm(z)
                       ==> norm(vsum(0..n) (\i. c(i) * z pow i))
                               <= e * norm(z) pow (n + 1)`;;

let COMPLEX_POLYFUN_EXTREMAL = `!c n. (!k. k IN 1..n ==> c(k) = Cx(&0)) \/
         !B. eventually (\z. norm(vsum(0..n) (\i. c(i) * z pow i)) >= B)
                        at_infinity`;;

let COMPLEX_POLYFUN_ROOTBOUND = `!n c. ~(!i. i IN 0..n ==> c(i) = Cx(&0))
         ==> FINITE {z | vsum(0..n) (\i. c(i) * z pow i) = Cx(&0)} /\
             CARD {z | vsum(0..n) (\i. c(i) * z pow i) = Cx(&0)} <= n`;;

let COMPLEX_POLYFUN_FINITE_ROOTS = `!n c. FINITE {x | vsum(0..n) (\i. c i * x pow i) = Cx(&0)} <=>
         ?i. i IN 0..n /\ ~(c i = Cx(&0))`;;

let COMPLEX_POLYFUN_EQ_0 = `!n c. (!z. vsum(0..n) (\i. c i * z pow i) = Cx(&0)) <=>
         (!i. i IN 0..n ==> c i = Cx(&0))`;;

let COMPLEX_POLYFUN_EQ_CONST = `!n c k. (!z. vsum(0..n) (\i. c i * z pow i) = k) <=>
           c 0 = k /\ (!i. i IN 1..n ==> c i = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* Complex products.                                                         *)
(* ------------------------------------------------------------------------- *)

let cproduct = new_definition
  `cproduct = iterate (( * ):complex->complex->complex)`;;

let NEUTRAL_COMPLEX_MUL = `neutral(( * ):complex->complex->complex) = Cx(&1)`;;

let MONOIDAL_COMPLEX_MUL = `monoidal(( * ):complex->complex->complex)`;;

let CPRODUCT_CLAUSES = `(!f. cproduct {} f = Cx(&1)) /\
   (!x f s. FINITE(s)
            ==> (cproduct (x INSERT s) f =
                 if x IN s then cproduct s f else f(x) * cproduct s f))`;;

let CPRODUCT_EQ_0 = `!f s. FINITE s ==> (cproduct s f = Cx(&0) <=> ?x. x IN s /\ f(x) = Cx(&0))`;;

let CPRODUCT_INV = `!f s. FINITE s ==> cproduct s (\x. inv(f x)) = inv(cproduct s f)`;;

let CPRODUCT_MUL = `!f g s. FINITE s
           ==> cproduct s (\x. f x * g x) = cproduct s f * cproduct s g`;;

let CPRODUCT_EQ_1 = `!f s. (!x:A. x IN s ==> (f(x) = Cx(&1))) ==> (cproduct s f = Cx(&1))`;;

let CPRODUCT_1 = `!s. cproduct s (\n. Cx(&1)) = Cx(&1)`;;

let CPRODUCT_POW = `!f s n. FINITE s
           ==> cproduct s (\x. f x pow n) = (cproduct s f) pow n`;;

let NORM_CPRODUCT = `!f s. FINITE s ==> norm(cproduct s f) = product s (\x. norm(f x))`;;

let CPRODUCT_EQ = `!f g s. (!x. x IN s ==> (f x = g x)) ==> cproduct s f = cproduct s g`;;

let CPRODUCT_SING = `!f x. cproduct {x} f = f(x)`;;

let CPRODUCT_CLAUSES_NUMSEG = `(!m. cproduct(m..0) f = if m = 0 then f(0) else Cx(&1)) /\
   (!m n. cproduct(m..SUC n) f = if m <= SUC n then cproduct(m..n) f * f(SUC n)
                                 else cproduct(m..n) f)`;;

let CPRODUCT_CLAUSES_RIGHT = `!f m n. 0 < n /\ m <= n ==> cproduct(m..n) f = cproduct(m..n-1) f * (f n)`;;

let CPRODUCT_CLAUSES_LEFT = `!f m n. m <= n ==> cproduct(m..n) f = f m * cproduct(m + 1..n) f`;;

let CPRODUCT_IMAGE = `!f g s. (!x y. x IN s /\ y IN s /\ f x = f y ==> (x = y))
           ==> (cproduct (IMAGE f s) g = cproduct s (g o f))`;;

let CPRODUCT_OFFSET = `!f m p. cproduct(m+p..n+p) f = cproduct(m..n) (\i. f(i + p))`;;

let CPRODUCT_CONST = `!c s. FINITE s ==> cproduct s (\x. c) = c pow (CARD s)`;;

let CPRODUCT_CONST_NUMSEG = `!c m n. cproduct (m..n) (\x. c) = c pow ((n + 1) - m)`;;

let CPRODUCT_PAIR = `!f m n. cproduct(2*m..2*n+1) f = cproduct(m..n) (\i. f(2*i) * f(2*i+1))`;;

let CPRODUCT_REFLECT = `!x m n. cproduct(m..n) x =
           if n < m then Cx(&1) else cproduct(0..n-m) (\i. x(n - i))`;;

let CNJ_CPRODUCT = `!f s. FINITE s ==> cnj(cproduct s f) = cproduct s (\i. cnj(f i))`;;

let CX_PRODUCT = `!f s. FINITE s ==> Cx(product s f) = cproduct s (\i. Cx(f i))`;;

let CPRODUCT_SUPERSET = `!f:A->complex u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> f(x) = Cx(&1))
        ==> cproduct v f = cproduct u f`;;

let CPRODUCT_UNION = `!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (cproduct (s UNION t) f = cproduct s f * cproduct t f)`;;

let th = `(!f g s.   (!x. x IN s ==> f(x) = g(x))
              ==> cproduct s (\i. f(i)) = cproduct s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> cproduct(a..b) (\i. f(i)) = cproduct(a..b) g) /\
   (!f g p.   (!x. p x ==> f x = g x)
              ==> cproduct {y | p y} (\i. f(i)) = cproduct {y | p y} g)`;;
