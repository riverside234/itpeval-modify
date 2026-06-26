new_type ("R",0);;

let is_integral_context = new_definition
  `is_integral_context (zero:R) (oneR:R)
                       (add:R->R->R) (opp:R->R) (mul:R->R->R)
                       (le:R->R->bool) (lt:R->R->bool) (absR:R->R)
                       (sigma:(R->bool)->(R->R)->R) <=>
     (!x:R y:R. add x y = add y x) /\
     (!x:R y:R z:R. add (add x y) z = add x (add y z)) /\
     (!x:R. add x zero = x) /\
     (!x:R. add (opp x) x = zero) /\
     (!x:R y:R z:R. add x z = add y z ==> x = y) /\
     (!x:R y:R. mul x y = mul y x) /\
     (!x:R y:R z:R. mul (mul x y) z = mul x (mul y z)) /\
     (!x:R. mul x oneR = x) /\
     (!x:R y:R z:R. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x:R. opp (opp x) = x) /\
     (!x:R y:R z:R. le x y ==> le (add x z) (add y z)) /\
     (!x:R y:R z:R. le zero z ==> le x y ==> le (mul x z) (mul y z)) /\
     le zero oneR /\
     (!x:R y:R. le x y \/ le y x) /\
     (!x:R y:R. le x y \/ ~(le x y)) /\
     (!x:R y:R. le x y ==> le (opp y) (opp x)) /\
     (!x:R y:R. le x y ==> le y x ==> x = y) /\
     (!x:R y:R. lt x y ==> lt (opp y) (opp x)) /\
     (!x:R. le x x) /\
     (!x:R y:R z:R. le x y ==> le y z ==> le x z) /\
     (!x:R y:R. lt x y <=> (le x y /\ ~(x = y))) /\
     (!x:R. le zero x ==> absR x = x) /\
     (!x:R. le x zero ==> absR x = opp x) /\
     (!x:R. le zero (absR x)) /\
     (!x:R. absR (opp x) = absR x) /\
     (!x:R y:R. le (absR (add x y)) (add (absR x) (absR y))) /\
     (!D:R->bool f:R->R c:R. sigma D (\x. mul c (f x)) = mul c (sigma D f)) /\
     (!D:R->bool f:R->R g:R->R. (!x:R. D x ==> f x = g x) ==> sigma D f = sigma D g) /\
     (!D:R->bool. sigma D (\x:R. zero) = zero) /\
     (!D:R->bool f:R->R g:R->R. sigma D (\x. add (f x) (g x)) = add (sigma D f) (sigma D g)) /\
     (!D:R->bool E:R->bool f:R->R. (!x:R. D x ==> E x ==> F) ==> sigma (\x. D x \/ E x) f = add (sigma D f) (sigma E f)) /\
     (!D:R->bool f:R->R g:R->R. (!x:R. D x ==> le (f x) (g x)) ==> le (sigma D f) (sigma D g)) /\
     (!D:R->bool E:R->bool f:R->R. (!x:R. D x <=> E x) ==> sigma D f = sigma E f) /\
     (!D:R->bool f:R->R. le (absR (sigma D f)) (sigma D (\x:R. absR (f x))))`;;

let iic = new_definition `iic (le:R->R->bool) c x <=> le x c`;;
let ioi = new_definition `ioi (lt:R->R->bool) c x <=> lt c x`;;
let iio = new_definition `iio (lt:R->R->bool) c x <=> lt x c`;;

let unionD = new_definition `unionD (D:R->bool) (E:R->bool) x <=> D x \/ E x`;;
let interD = new_definition `interD (D:R->bool) (E:R->bool) x <=> D x /\ E x`;;

let preimage = new_definition `preimage (g:R->R) (D:R->bool) x <=> D (g x)`;;

let INTRO_INT_HYPS =
  REWRITE_TAC[is_integral_context] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> ASSUME_TAC th THEN MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

let ASSUM_MATCH_TAC pat ttac =
  ASSUM_LIST
    (fun asms ->
      let th =
        find
          (fun th ->
            try
              let (_,tinst,_) = term_match [] pat (concl th) in
              forall (fun (v,t) -> t = v) tinst
            with Failure _ -> false)
          asms in
      ttac th);;

let INT_CONTEXT_CONJ n ctx =
  List.nth (CONJUNCTS (REWRITE_RULE[is_integral_context] ctx)) n;;

let lt_irrefl = prove
 (`!zero oneR add opp mul le lt absR sigma x.
     is_integral_context zero oneR add opp mul le lt absR sigma ==> ~(lt x x)`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    MP_TAC (SPECL [`x:R`; `x:R`] (INT_CONTEXT_CONJ 20 ctx)) THEN
    MESON_TAC[]));;

let lt_trans_strict = prove
 (`!zero oneR add opp mul le lt absR sigma x y z.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> lt x y ==> lt y z ==> lt x z`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    let le_antisymm = INT_CONTEXT_CONJ 16 ctx in
    let le_trans = INT_CONTEXT_CONJ 19 ctx in
    let lt_def = INT_CONTEXT_CONJ 20 ctx in
    MESON_TAC[le_antisymm; le_trans; lt_def]));;

let preimage_union = prove
 (`!D E (g:R->R) x.
     preimage g (unionD D E) x <=> preimage g D x \/ preimage g E x`,
  REWRITE_TAC[preimage; unionD]);;

let preimage_inter = prove
 (`!D E (g:R->R) x.
     preimage g (interD D E) x <=> preimage g D x /\ preimage g E x`,
  REWRITE_TAC[preimage; interD]);;

let preimage_neg_Ioi = prove
 (`!zero oneR add opp mul le lt absR sigma c x.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (preimage opp (ioi lt c) x <=> lt x (opp c))`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    REWRITE_TAC[preimage; ioi] THEN
    MESON_TAC[INT_CONTEXT_CONJ 9 ctx; INT_CONTEXT_CONJ 17 ctx]));;

let preimage_neg_Iic = prove
 (`!zero oneR add opp mul le lt absR sigma c x.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (preimage opp (iic le c) x <=> iic le x (opp c))`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    REWRITE_TAC[preimage; iic] THEN
    MESON_TAC[INT_CONTEXT_CONJ 9 ctx; INT_CONTEXT_CONJ 15 ctx]));;

let preimage_comp = prove
 (`!D (g:R->R) (h:R->R) x.
     preimage g (preimage h D) x <=> preimage (\x. h (g x)) D x`,
  REWRITE_TAC[preimage]);;

let integral_neg = prove
 (`!(zero:R) (oneR:R) (add:R->R->R) (opp:R->R) (mul:R->R->R)
      (le:R->R->bool) (lt:R->R->bool) (absR:R->R)
      (sigma:(R->bool)->(R->R)->R) (D:R->bool) (phi:R->R).
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma D (\x. opp (phi x)) = opp (sigma D phi)`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    let add_opp = INT_CONTEXT_CONJ 3 ctx in
    let add_right_cancel = INT_CONTEXT_CONJ 4 ctx in
    let sigma_zero = INT_CONTEXT_CONJ 28 ctx in
    let sigma_add = INT_CONTEXT_CONJ 29 ctx in
    SUBGOAL_THEN
      `(add:R->R->R)
         ((sigma:(R->bool)->(R->R)->R) D
           (\x:R. (opp:R->R) ((phi:R->R) x)))
         (sigma D phi) =
       add (opp (sigma D phi)) (sigma D phi)`
      MP_TAC THENL
     [SUBGOAL_THEN
       `(add:R->R->R)
          ((sigma:(R->bool)->(R->R)->R) D
            (\x:R. (opp:R->R) ((phi:R->R) x)))
          (sigma D phi) = zero`
       SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM sigma_add] THEN
      REWRITE_TAC[add_opp; sigma_zero];
     REWRITE_TAC[add_opp]];
     DISCH_TAC THEN
     SUBGOAL_THEN
       `!x:R y:R.
          (add:R->R->R) x ((sigma:(R->bool)->(R->R)->R) D (phi:R->R)) =
          add y (sigma D phi) ==> x = y`
       (fun cancel ->
          MATCH_MP_TAC
            (ISPECL
              [`(sigma:(R->bool)->(R->R)->R) D
                  (\x:R. (opp:R->R) ((phi:R->R) x))`;
               `(opp:R->R) ((sigma:(R->bool)->(R->R)->R) D (phi:R->R))`]
              cancel))
       THENL [MP_TAC add_right_cancel THEN MESON_TAC[]; ASM_REWRITE_TAC[]]]));;

let integral_sub = prove
 (`!zero oneR add opp mul le lt absR sigma D f g.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma D (\x. add (f x) (opp (g x))) = add (sigma D f) (opp (sigma D g))`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    let neg_g =
      MATCH_MP
        (ISPECL
          [`zero:R`; `oneR:R`; `add:R->R->R`; `opp:R->R`;
           `mul:R->R->R`; `le:R->R->bool`; `lt:R->R->bool`;
           `absR:R->R`; `sigma:(R->bool)->(R->R)->R`;
           `D:R->bool`; `g:R->R`]
          integral_neg)
        ctx in
    REWRITE_TAC[INT_CONTEXT_CONJ 29 ctx; neg_g]));;

let sigma_empty = prove
 (`!zero oneR add opp mul le lt absR sigma f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma (\x. F) f = zero`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    MESON_TAC[INT_CONTEXT_CONJ 27 ctx; INT_CONTEXT_CONJ 28 ctx]));;

let sigma_bilinear = prove
 (`!zero oneR add opp mul le lt absR sigma D f g c d.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma D (\x. add (mul c (f x)) (mul d (g x))) =
         add (mul c (sigma D f)) (mul d (sigma D g))`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    REWRITE_TAC[INT_CONTEXT_CONJ 26 ctx; INT_CONTEXT_CONJ 29 ctx]));;

let sigma_le_monotone = prove
 (`!zero oneR add opp mul le lt absR sigma D f g.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (!x. D x ==> le (f x) (g x)) ==> le (sigma D f) (sigma D g)`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    MESON_TAC[INT_CONTEXT_CONJ 31 ctx]));;

let sigma_nonneg = prove
 (`!zero oneR add opp mul le lt absR sigma D f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (!x. D x ==> le zero (f x)) ==> le zero (sigma D f)`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    MESON_TAC[INT_CONTEXT_CONJ 28 ctx; INT_CONTEXT_CONJ 31 ctx]));;

let sigma_split = prove
 (`!zero oneR add opp mul le lt absR sigma D P f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (!x. D x ==> P x \/ ~(P x))
     ==> sigma D f =
         add (sigma (\x. D x /\ P x) f) (sigma (\x. D x /\ ~(P x)) f)`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    let sigma_union_disjoint = INT_CONTEXT_CONJ 30 ctx in
    let sigma_dom_congr = INT_CONTEXT_CONJ 32 ctx in
    DISCH_THEN (fun dec ->
      ASSUME_TAC dec THEN
      SUBGOAL_THEN
        `(sigma:(R->bool)->(R->R)->R) (D:R->bool) (f:R->R) =
         sigma (\x:R. D x /\ (P:R->bool) x \/ D x /\ ~(P x)) f`
        SUBST1_TAC THENL
       [MATCH_MP_TAC
          (BETA_RULE (ISPECL
            [`D:R->bool`;
             `\x:R. (D:R->bool) x /\ (P:R->bool) x \/ D x /\ ~(P x)`;
             `f:R->R`]
            sigma_dom_congr)) THEN
        ASM_MESON_TAC[];
        MATCH_MP_TAC
          (BETA_RULE (ISPECL
            [`\x:R. (D:R->bool) x /\ (P:R->bool) x`;
             `\x:R. (D:R->bool) x /\ ~((P:R->bool) x)`;
             `f:R->R`]
            sigma_union_disjoint)) THEN
        MESON_TAC[]])));;

let sigma_preimage_neg_Ioi = prove
 (`!zero oneR add opp mul le lt absR sigma f c.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma (preimage opp (ioi lt c)) f = sigma (iio lt (opp c)) f`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    let opp_involutive = INT_CONTEXT_CONJ 9 ctx in
    let lt_opp = INT_CONTEXT_CONJ 17 ctx in
    let sigma_dom_congr = INT_CONTEXT_CONJ 32 ctx in
    MATCH_MP_TAC
      (ISPECL
        [`preimage (opp:R->R) (ioi (lt:R->R->bool) (c:R))`;
         `iio (lt:R->R->bool) ((opp:R->R) (c:R))`;
         `f:R->R`]
        sigma_dom_congr) THEN
    X_GEN_TAC `x:R` THEN
    REWRITE_TAC[preimage; ioi; iio] THEN
    MESON_TAC[opp_involutive; lt_opp]));;

let sigma_abs_bound = prove
 (`!zero oneR add opp mul le lt absR sigma D f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> le (absR (sigma D f)) (sigma D (\x. absR (f x)))`,
  REPEAT GEN_TAC THEN DISCH_THEN (fun ctx ->
    MATCH_ACCEPT_TAC (ISPECL [`D:R->bool`; `f:R->R`] (INT_CONTEXT_CONJ 33 ctx))));;
