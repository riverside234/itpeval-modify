let is_group = new_definition
  `is_group (mul:A->A->A) (e:A) (ginv:A->A) <=>
     (!a b c. mul a (mul b c) = mul (mul a b) c) /\
     (!a. mul a e = a) /\
     (!a. mul e a = a) /\
     (!a. mul (ginv a) a = e) /\
     (!a. mul a (ginv a) = e)`;;


let INTRO_GROUP_HYPS =
  REWRITE_TAC[is_group] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))));;



let FUN_CONG = prove
  (`!f:A->B x y. x = y ==> f x = f y`,
   REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let GROUP_ASSOC = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b c:A. mul a (mul b c) = mul (mul a b) c`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let GROUP_ASSOC_SYM = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b c:A. mul (mul a b) c = mul a (mul b c)`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let GROUP_MUL_ONE = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul a e = a`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let GROUP_ONE_MUL = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul e a = a`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let GROUP_MUL_INV_L = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul (ginv a) a = e`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let GROUP_MUL_INV_R = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul a (ginv a) = e`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let GROUP_LEFT_CANCEL_NORMALIZE = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b:A. mul (ginv a) (mul a b) = b`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let GROUP_RIGHT_CANCEL_NORMALIZE = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b:A. mul (mul b a) (ginv a) = b`,
   REWRITE_TAC[is_group] THEN MESON_TAC[]);;

let MUL_LEFT_CANCEL = prove
  (`!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b c:A. mul a b = mul a c ==> b = c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mul:A->A->A`; `e:A`; `ginv:A->A`]
    GROUP_LEFT_CANCEL_NORMALIZE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun nth ->
    MP_TAC(SPECL [`a:A`; `b:A`] nth) THEN
    MP_TAC(SPECL [`a:A`; `c:A`] nth)) THEN
  ASM_MESON_TAC[]);;

let MUL_RIGHT_CANCEL = prove
  (`!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b c:A. mul b a = mul c a ==> b = c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mul:A->A->A`; `e:A`; `ginv:A->A`]
    GROUP_RIGHT_CANCEL_NORMALIZE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun nth ->
    MP_TAC(SPECL [`a:A`; `b:A`] nth) THEN
    MP_TAC(SPECL [`a:A`; `c:A`] nth)) THEN
  ASM_MESON_TAC[]);;

let INV_INV = prove
  (`!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==> !a:A. ginv (ginv a) = a`,
  MESON_TAC[MUL_RIGHT_CANCEL; GROUP_MUL_INV_L; GROUP_MUL_INV_R]);;

let GROUP_INV_MUL_PRODUCT = prove
  (`!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv
        ==> !a b:A. mul (mul (ginv b) (ginv a)) (mul a b) = e`,
   MESON_TAC[GROUP_ASSOC_SYM; GROUP_LEFT_CANCEL_NORMALIZE; GROUP_MUL_INV_L]);;

let INV_MUL = prove
  (`!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b:A. ginv (mul a b) = mul (ginv b) (ginv a)`,
  MESON_TAC[MUL_RIGHT_CANCEL; GROUP_MUL_INV_L; GROUP_INV_MUL_PRODUCT]);;

let INV_EQ_OF_MUL_EQ_ONE = prove
  (`!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b:A. mul a b = e ==> b = ginv a`,
  MESON_TAC[GROUP_ASSOC; GROUP_MUL_INV_L; GROUP_MUL_ONE; GROUP_ONE_MUL]);;




let is_group_comm = new_definition
  `is_group_comm (mul:A->A->A) (e:A) (ginv:A->A) <=>
     is_group mul e ginv /\ (!a b. mul a b = mul b a)`;;

let MUL_ROTATE' = prove
  (`!mul (e:A) ginv. is_group_comm mul e ginv ==>
    !a b c. mul a (mul b c) = mul b (mul c a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_group_comm; is_group] THEN
  MESON_TAC[]);;




let is_group_action = new_definition
  `is_group_action (mul:A->A->A) (e:A) (ginv:A->A) (act:A->B->B) <=>
     is_group mul e ginv /\
     (!x. act e x = x) /\
     (!(g:A) (h:A) (x:B). act (mul g h) x = act g (act h x))`;;

let INTRO_ACTION_HYPS =
  REWRITE_TAC[is_group_action] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC));;

let GROUP_ACTION_REFL_TAC () =
  ASM_REWRITE_TAC[is_group_action] THEN REFL_TAC;;

let ACT_INV = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !g x. act (ginv g) (act g x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_group_action; is_group] THEN
  MESON_TAC[]);;

let ACT_INV_SPEC = prove
  (`!mul (e:A) ginv (act:A->B->B) g x. is_group_action mul e ginv act ==>
    act (ginv g) (act g x) = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_MESON_TAC[ACT_INV]);;

let ACT_INV_R = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !g x. act g (act (ginv g) x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_group_action; is_group] THEN
  MESON_TAC[]);;

let ACT_INV_R_SPEC = prove
  (`!mul (e:A) ginv (act:A->B->B) g x. is_group_action mul e ginv act ==>
    act g (act (ginv g) x) = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_MESON_TAC[ACT_INV_R]);;

let ACT_INV_R_SYM = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !g x. x = act g (act (ginv g) x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(ISPECL
   [`mul:A->A->A`; `e:A`; `ginv:A->A`; `act:A->B->B`; `g:A`; `x:B`]
   ACT_INV_R_SPEC) THEN
  ASM_REWRITE_TAC[]);;



let is_orbit = new_definition
  `is_orbit (act:A->B->B) x y <=> ?g. act g x = y`;;

let is_stabilizer = new_definition
  `is_stabilizer (act:A->B->B) x g <=> act g x = x`;;

let ORBIT_REFL = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x. is_orbit act x x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_group_action; is_orbit] THEN
  MESON_TAC[]);;

let ORBIT_SYM = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y. is_orbit act x y ==> is_orbit act y x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[is_orbit] THEN
  ASM_MESON_TAC[ACT_INV]);;

let ORBIT_TRANS = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y z. is_orbit act x y ==> is_orbit act y z ==> is_orbit act x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_orbit; is_group_action] THEN
  MESON_TAC[]);;

let ORBIT_PARTITION = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y z. is_orbit act x y ==>
            (is_orbit act x z <=> is_orbit act y z)`,
  MESON_TAC[ORBIT_SYM; ORBIT_TRANS]);;

let STABILIZER_MUL = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x g h. is_stabilizer act x g ==> is_stabilizer act x h ==>
            is_stabilizer act x (mul g h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_group_action; is_stabilizer] THEN
  MESON_TAC[]);;

let STABILIZER_INV = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x g. is_stabilizer act x g ==> is_stabilizer act x (ginv g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[is_stabilizer] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `act (ginv g:A) (act g (x:B))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL
     [`mul:A->A->A`; `e:A`; `ginv:A->A`; `act:A->B->B`; `g:A`; `x:B`]
     ACT_INV_SPEC) THEN
    ASM_REWRITE_TAC[]]);;

let STABILIZER_ONE = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x. is_stabilizer act x e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_stabilizer; is_group_action] THEN
  MESON_TAC[]);;

let STABILIZER_CONJUGATE = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x g h. is_stabilizer act x h ==>
            is_stabilizer act (act g x) (mul (mul g h) (ginv g))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun hact ->
    ASSUME_TAC hact THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[is_stabilizer] THEN DISCH_TAC THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[is_group_action] hact) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `act (ginv g:A) (act g (x:B)) = x` SUBST1_TAC THENL
     [MATCH_MP_TAC(ISPECL
       [`mul:A->A->A`; `e:A`; `ginv:A->A`; `act:A->B->B`; `g:A`; `x:B`]
       ACT_INV_SPEC) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]));;

let CONJUGATE_MUL_CANCEL_LEFT = prove
  (`!mul:A->A->A (e:A) (ginv:A->A) g h.
        is_group mul e ginv
        ==> mul g (mul (mul (ginv g) h) g) = mul h g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[is_group]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mul (mul (mul g (ginv g:A)) h) g` THEN
  ASM_REWRITE_TAC[]);;

let CONJUGATE_MUL_CANCEL = prove
  (`!mul:A->A->A (e:A) (ginv:A->A) g h.
        is_group mul e ginv
        ==> mul (mul g (mul (mul (ginv g) h) g)) (ginv g) = h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`mul:A->A->A`; `e:A`; `ginv:A->A`; `g:A`; `h:A`]
   CONJUGATE_MUL_CANCEL_LEFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_group]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(mul (h:A) (mul (g:A) (ginv g))):A` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let STABILIZER_CONJUGATE_ORBIT_FWD = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y g h. act g x = y ==>
            is_stabilizer act y h ==>
            is_stabilizer act x (mul (mul (ginv g) h) g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun hact ->
    ASSUME_TAC hact THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun hxy ->
      ASSUME_TAC hxy THEN
      REWRITE_TAC[is_stabilizer] THEN
      DISCH_THEN(fun hstab ->
        ASSUME_TAC hstab THEN
        STRIP_ASSUME_TAC(REWRITE_RULE[is_group_action] hact) THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC hxy THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM hxy) THEN
        MATCH_MP_TAC(ISPECL
         [`mul:A->A->A`; `e:A`; `ginv:A->A`; `act:A->B->B`; `g:A`; `x:B`]
         ACT_INV_SPEC) THEN
        ASM_REWRITE_TAC[]))));;

let STABILIZER_CONJUGATE_ORBIT_REV = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y g h. act g x = y ==>
            is_stabilizer act x (mul (mul (ginv g) h) g) ==>
            is_stabilizer act y h`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun hact ->
    REPEAT GEN_TAC THEN DISCH_THEN(fun hxy ->
      DISCH_THEN(fun hstab ->
        let hgroup = CONJUNCT1 (REWRITE_RULE[is_group_action] hact) in
        let eq_conj =
          MATCH_MP
            (ISPECL
              [`mul:A->A->A`; `e:A`; `ginv:A->A`; `g:A`; `h:A`]
              CONJUGATE_MUL_CANCEL)
            hgroup in
        let stab_conj = MATCH_MP (SPECL [`mul:A->A->A`; `e:A`; `ginv:A->A`; `act:A->B->B`] STABILIZER_CONJUGATE) hact in
        let stab_step =
          MATCH_MP
            (ISPECL [`x:B`; `g:A`; `mul (mul (ginv g) h) g:A`] stab_conj)
            hstab in
        MATCH_ACCEPT_TAC (REWRITE_RULE[hxy; eq_conj] stab_step)))));;
let STABILIZER_CONJUGATE_ORBIT = prove
  (`!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y g h. act g x = y ==>
            (is_stabilizer act y h <=>
             is_stabilizer act x (mul (mul (ginv g) h) g))`,
  MESON_TAC[STABILIZER_CONJUGATE_ORBIT_FWD; STABILIZER_CONJUGATE_ORBIT_REV]);;
