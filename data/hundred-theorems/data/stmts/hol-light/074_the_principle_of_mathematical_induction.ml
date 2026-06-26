(* ========================================================================= *)
(* The axiom of infinity; construction of the natural numbers.               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "compute.ml";;

(* ------------------------------------------------------------------------- *)
(* Declare a new type "ind" of individuals.                                  *)
(* ------------------------------------------------------------------------- *)

new_type ("ind",0);;

(* ------------------------------------------------------------------------- *)
(* We assert the axiom of infinity as in HOL88, but then we can forget it!   *)
(* ------------------------------------------------------------------------- *)

let ONE_ONE = new_definition
  `ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;

let ONTO = new_definition
  `ONTO(f:A->B) = !y. ?x. y = f x`;;

let INFINITY_AX = new_axiom
  `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`;;

(* ------------------------------------------------------------------------- *)
(* Actually introduce constants.                                             *)
(* ------------------------------------------------------------------------- *)

let IND_SUC_0_EXISTS = `?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))`;;

let IND_SUC_SPEC =
  let th1 = new_definition
   `IND_SUC = @f:ind->ind. ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\
                                (!x. ~(f x = z))` in
  let th2 = REWRITE_RULE[GSYM th1] (SELECT_RULE IND_SUC_0_EXISTS) in
  let th3 = new_definition
   `IND_0 = @z:ind. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
                    (!x. ~(IND_SUC x = z))` in
  REWRITE_RULE[GSYM th3] (SELECT_RULE th2);;

let IND_SUC_INJ,IND_SUC_0 = CONJ_PAIR IND_SUC_SPEC;;

(* ------------------------------------------------------------------------- *)
(* Carve out the natural numbers inductively.                                *)
(* ------------------------------------------------------------------------- *)

let NUM_REP_RULES,NUM_REP_INDUCT,NUM_REP_CASES =
  new_inductive_definition
   `NUM_REP IND_0 /\
    (!i. NUM_REP i ==> NUM_REP (IND_SUC i))`;;

let num_tydef = new_basic_type_definition
  "num" ("mk_num","dest_num")
    (CONJUNCT1 NUM_REP_RULES);;

let ZERO_DEF = new_definition
 `_0 = mk_num IND_0`;;

let SUC_DEF = new_definition
 `SUC n = mk_num(IND_SUC(dest_num n))`;;

(* ------------------------------------------------------------------------- *)
(* Distinctness and injectivity of constructors.                             *)
(* ------------------------------------------------------------------------- *)

let NOT_SUC = `!n. ~(SUC n = _0)`;;

let SUC_INJ = `!m n. SUC m = SUC n <=> m = n`;;

(* ------------------------------------------------------------------------- *)
(* Induction.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_INDUCTION = `!P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n`;;

(* ------------------------------------------------------------------------- *)
(* Recursion.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_Axiom = `!(e:A) f. ?!fn. (fn _0 = e) /\
                   (!n. fn (SUC n) = f (fn n) n)`;;

(* ------------------------------------------------------------------------- *)
(* The basic numeral tag; rewrite existing instances of "_0".                *)
(* ------------------------------------------------------------------------- *)

let NUMERAL =
  let num_ty = type_of(lhand(concl ZERO_DEF)) in
  let funn_ty = mk_fun_ty num_ty num_ty in
  let numeral_tm = mk_var("NUMERAL",funn_ty) in
  let n_tm = mk_var("n",num_ty) in
  new_definition(mk_eq(mk_comb(numeral_tm,n_tm),n_tm));;

let [NOT_SUC; num_INDUCTION; num_Axiom] =
  let th = `_0 = 0`;;

(* ------------------------------------------------------------------------- *)
(* Cases theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let num_CASES = `!m. (m = 0) \/ (?n. m = SUC n)`;;

(* ------------------------------------------------------------------------- *)
(* Augmenting inductive type store.                                          *)
(* ------------------------------------------------------------------------- *)

inductive_type_store :=
 ("num",(2,num_INDUCTION,num_RECURSION))::(!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* "Bitwise" binary representation of numerals.                              *)
(* ------------------------------------------------------------------------- *)

let BIT0_DEF =
  let funn_ty = type_of(rator(lhand(snd(dest_forall(concl NUMERAL))))) in
  let bit0_tm = mk_var("BIT0",funn_ty) in
  let def = new_definition
   (mk_eq(bit0_tm,`@fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC(fn n)))`))
  and th = BETA_RULE(ISPECL [`0`; `\m n:num. SUC(SUC m)`] num_RECURSION) in
  REWRITE_RULE[GSYM def] (SELECT_RULE th);;

let BIT1_DEF =
  let funn_ty = type_of(rator(lhand(lhand(concl BIT0_DEF)))) in
  let num_ty = snd(dest_fun_ty funn_ty) in
  let n_tm = mk_var("n",num_ty) in
  let bit1_tm = mk_var("BIT1",funn_ty) in
  new_definition(mk_eq(mk_comb(bit1_tm,n_tm),`SUC (BIT0 n)`));;

(* ------------------------------------------------------------------------- *)
(* Syntax operations on numerals.                                            *)
(* ------------------------------------------------------------------------- *)

let mk_numeral =
  let pow24 = pow2 24 and num_0 = num 0
  and zero_tm = mk_const("_0",[])
  and BIT0_tm = mk_const("BIT0",[])
  and BIT1_tm = mk_const("BIT1",[])
  and NUMERAL_tm = mk_const("NUMERAL",[]) in
  let rec stripzeros l = match l with false::t -> stripzeros t | _ -> l in
  let rec raw_list_of_num l n =
    if n =/ num_0 then stripzeros l else
    let h = Num.int_of_num(mod_num n pow24) in
    raw_list_of_num
     ((h land 8388608 <> 0)::(h land 4194304 <> 0)::(h land 2097152 <> 0)::
      (h land 1048576 <> 0)::(h land 524288 <> 0)::(h land 262144 <> 0)::
      (h land 131072 <> 0)::(h land 65536 <> 0)::(h land 32768 <> 0)::
      (h land 16384 <> 0)::(h land 8192 <> 0)::(h land 4096 <> 0)::
      (h land 2048 <> 0)::(h land 1024 <> 0)::(h land 512 <> 0)::
      (h land 256 <> 0)::(h land 128 <> 0)::(h land 64 <> 0)::
      (h land 32 <> 0)::(h land 16 <> 0)::(h land 8 <> 0)::(h land 4 <> 0)::
      (h land 2 <> 0)::(h land 1 <> 0)::l) (quo_num n pow24) in
  let rec numeral_of_list t l =
    match l with
      [] -> t
    | b::r -> numeral_of_list(mk_comb((if b then BIT1_tm else BIT0_tm),t)) r in
  let mk_raw_numeral n = numeral_of_list zero_tm (raw_list_of_num [] n) in
  fun n -> if n </ num_0 then failwith "mk_numeral: negative argument" else
           mk_comb(NUMERAL_tm,mk_raw_numeral n);;

let mk_small_numeral n = mk_numeral(num n);;

let dest_small_numeral t = Num.int_of_num(dest_numeral t);;

let is_numeral = can dest_numeral;;

(* ------------------------------------------------------------------------- *)
(* Derived principles of definition based on existence.                      *)
(*                                                                           *)
(* This is put here because we use numerals as tags to force different       *)
(* constants specified with equivalent theorems to have different underlying *)
(* definitions, ensuring that there are no provable equalities between them  *)
(* and so in some sense the constants are "underspecified" as the user might *)
(* want for some applications.                                               *)
(* ------------------------------------------------------------------------- *)

let the_specifications = ref [];;

let new_specification =
  let code c = mk_small_numeral (Char.code (c.[0])) in
  let mk_code name =
      end_itlist (curry mk_pair) (map code (explode name)) in
  let check_distinct l =
    try itlist (fun t res -> if mem t res then fail() else t::res) l []; true
    with Failure _ -> false in
  let specify name th =
    let ntm = mk_code name in
    let gv = genvar(type_of ntm) in
    let th0 = CONV_RULE(REWR_CONV SKOLEM_THM) (GEN gv th) in
    let th1 = CONV_RULE(RATOR_CONV (REWR_CONV EXISTS_THM) THENC
                        BETA_CONV) th0 in
    let l,r = dest_comb(concl th1) in
    let rn = mk_comb(r,ntm) in
    let ty = type_of rn in
    let th2 = new_definition(mk_eq(mk_var(name,ty),rn)) in
    GEN_REWRITE_RULE ONCE_DEPTH_CONV [GSYM th2]
     (SPEC ntm (CONV_RULE BETA_CONV th1)) in
  let rec specifies names th =
    match names with
      [] -> th
    | name::onames -> let th' = specify name th in
                      specifies onames th' in
  fun names th ->
    let asl,c = dest_thm th in
    if not (asl = []) then
      failwith "new_specification: Assumptions not allowed in theorem" else
    if not (frees c = []) then
      failwith ("new_specification: Free variables in predicate: " ^
        (String.concat ", " (map (fun (Var (name,_)) -> name) (frees c)))) else
    let avs = fst(strip_exists c) in
    if length names = 0 || length names > length avs then
      failwith "new_specification: Unsuitable number of constant names" else
    if not (check_distinct names) then
      failwith "new_specification: Constant names not distinct"
    else
      try let sth = snd(find (fun ((names',th'),sth') ->
                               names' = names && aconv (concl th') (concl th))
                             (!the_specifications)) in
          warn true ("Benign respecification"); sth
      with Failure _ ->
          let sth = specifies names th in
          the_specifications := ((names,th),sth)::(!the_specifications);
          sth;;
