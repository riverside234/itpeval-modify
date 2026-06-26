new_type ("R",0);;
new_type ("W",0);;

let subR = new_definition
  `subR (addR:R->R->R) (oppR:R->R) (x:R) (y:R) = addR x (oppR y)`;;

let ev_false = new_definition
  `ev_false:W->bool = (\w. F)`;;

let ev_true = new_definition
  `ev_true:W->bool = (\w. T)`;;

let ev_inter = new_definition
  `ev_inter (A:W->bool) (B:W->bool) = (\w. A w /\ B w)`;;

let ev_union = new_definition
  `ev_union (A:W->bool) (B:W->bool) = (\w. A w \/ B w)`;;

let ev_compl = new_definition
  `ev_compl (A:W->bool) = (\w. ~(A w))`;;

let ev_diff = new_definition
  `ev_diff (A:W->bool) (B:W->bool) = (\w. A w /\ ~(B w))`;;

let disjoint = new_definition
  `disjoint (A:W->bool) (B:W->bool) <=> !w. ~(ev_inter A B w)`;;

let pairwise_disjoint = new_recursive_definition list_RECURSION
  `pairwise_disjoint ([]:(W->bool)list) = T /\
   pairwise_disjoint (CONS (A:W->bool) xs) =
     ((!B. MEM B xs ==> disjoint A B) /\ pairwise_disjoint xs)`;;

let bigUnion = new_recursive_definition list_RECURSION
  `bigUnion ([]:(W->bool)list) = ev_false /\
   bigUnion (CONS (A:W->bool) xs) = ev_union A (bigUnion xs)`;;

let fold_add = new_recursive_definition list_RECURSION
  `fold_add (addR:R->R->R) (zeroR:R) ([]:R list) = zeroR /\
   fold_add addR zeroR (CONS x xs) = addR x (fold_add addR zeroR xs)`;;

let NilL = new_definition
  `NilL:A list = []`;;

let ConsL = new_definition
  `ConsL (x:A) (xs:A list) = CONS x xs`;;

let InL = new_definition
  `InL (x:A) (xs:A list) <=> MEM x xs`;;

let mapL = new_definition
  `mapL (f:A->B) (xs:A list) = MAP f xs`;;

let fold_addL = new_definition
  `fold_addL (addR:R->R->R) (zeroR:R) (xs:R list) =
   fold_add addR zeroR xs`;;

let indep = new_definition
  `indep (prob:(W->bool)->R) (mulR:R->R->R) (A:W->bool) (B:W->bool) <=>
     prob (ev_inter A B) = mulR (prob A) (prob B)`;;

let is_prob_context = new_definition
  `!zeroR oneR addR mulR oppR prob cprob.
     is_prob_context zeroR oneR addR mulR oppR prob cprob <=>
     ~(oneR = zeroR) /\
	     (!x y. addR x y = addR y x) /\
	     (!x y z. addR (addR x y) z = addR x (addR y z)) /\
	     (!x y z. addR x z = addR y z ==> x = y) /\
	     (!x. addR x zeroR = x) /\
	     (!x. addR zeroR x = x) /\
	     (!x. addR x (oppR x) = zeroR) /\
	     (!x. addR (oppR x) x = zeroR) /\
     (!x y. mulR x y = mulR y x) /\
     (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
     (!x. mulR x oneR = x) /\
     (!x. mulR oneR x = x) /\
     (!x y z. mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
     (!x. mulR x zeroR = zeroR) /\
     (!x. mulR zeroR x = zeroR) /\
     (!x y. mulR x y = zeroR ==> x = zeroR \/ y = zeroR) /\
     (!A B. (!w. A w <=> B w) ==> prob A = prob B) /\
     (prob ev_false = zeroR) /\
     (prob ev_true  = oneR) /\
     (!A B. prob (ev_union A B) =
            addR (prob A) (addR (prob B) (oppR (prob (ev_inter A B))))) /\
     (!A. prob (ev_compl A) = addR oneR (oppR (prob A))) /\
     (!A B. prob (ev_inter A B) = mulR (cprob A B) (prob B)) /\
     (oppR zeroR = zeroR) /\
     (!x. oppR (oppR x) = x) /\
     (!x y. mulR x (oppR y) = oppR (mulR x y)) /\
	     (!x y. mulR (oppR x) y = oppR (mulR x y)) /\
	     (!A B. disjoint A B ==> prob (ev_union A B) = addR (prob A) (prob B)) /\
	     (!A xs. pairwise_disjoint (CONS A xs) ==> disjoint A (bigUnion xs)) /\
	     (!A B. indep prob mulR A B ==> indep prob mulR (ev_compl A) (ev_compl B)) /\
	     (!A B C.
	        prob (ev_union (ev_union A B) C) =
	        addR (prob A)
	          (addR (prob B)
	            (addR (prob C)
	              (oppR (addR (prob (ev_inter A B))
	                (addR (prob (ev_inter A C))
	                  (addR (prob (ev_inter B C))
	                    (oppR (prob (ev_inter (ev_inter A B) C))))))))))`;;

let INTRO_PROB_HYPS =
  REWRITE_TAC[is_prob_context] THEN REPEAT GEN_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC;;

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

let FUN_CONG = prove
 (`!f:A->B x y. x = y ==> f x = f y`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let add_right_cancel = prove
 (`!zeroR oneR addR mulR oppR prob cprob (x:R) (y:R) (z:R).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> addR x z = addR y z ==> x = y`,
  INTRO_PROB_HYPS THEN ASM_MESON_TAC[]);;

let add_move_right_raw = prove
 (`!zeroR addR oppR (x:R) (y:R) (z:R).
     (!a b c. addR (addR a b) c = addR a (addR b c))
     ==> (!a b c. addR a c = addR b c ==> a = b)
     ==> (!a. addR a zeroR = a)
     ==> (!a. addR (oppR a) a = zeroR)
     ==> addR x y = z
     ==> x = addR z (oppR y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (fun add_assoc ->
  DISCH_THEN (fun add_cancel ->
  DISCH_THEN (fun add_rzero ->
  DISCH_THEN (fun add_linv ->
  DISCH_TAC THEN
  MATCH_MP_TAC
    (SPECL [`x:R`; `addR z (oppR y):R`; `y:R`] add_cancel) THEN
  ASM_REWRITE_TAC[add_assoc; add_rzero; add_linv])))));;

let add_move_right = prove
 (`!zeroR oneR addR mulR oppR prob cprob (x:R) (y:R) (z:R).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> addR x y = z ==> x = addR z (oppR y)`,
  INTRO_PROB_HYPS THEN
  MP_TAC
    (ISPECL [`zeroR:R`; `addR:R->R->R`; `oppR:R->R`;
             `x:R`; `y:R`; `z:R`] add_move_right_raw) THEN
  ASM_REWRITE_TAC[]);;

let ev_diff_union_inter = prove
 (`!A B. !w. ev_union (ev_diff A B) (ev_inter A B) w <=> A w`,
  REWRITE_TAC[ev_union; ev_diff; ev_inter] THEN MESON_TAC[]);;

let ev_diff_inter_disjoint = prove
 (`!A B. disjoint (ev_diff A B) (ev_inter A B)`,
  REWRITE_TAC[disjoint; ev_diff; ev_inter] THEN MESON_TAC[]);;

let ev_diff_inter_compl = prove
 (`!A B. !w. ev_diff A B w <=> ev_inter A (ev_compl B) w`,
  REWRITE_TAC[ev_diff; ev_inter; ev_compl] THEN MESON_TAC[]);;

let ev_partition = prove
 (`!A B. !w.
     A w <=>
     ev_union (ev_inter A B) (ev_inter A (ev_compl B)) w`,
  REWRITE_TAC[ev_union; ev_inter; ev_compl] THEN MESON_TAC[]);;

let ev_partition_disjoint = prove
 (`!A B. disjoint (ev_inter A B) (ev_inter A (ev_compl B))`,
  REWRITE_TAC[disjoint; ev_inter; ev_compl] THEN MESON_TAC[]);;

let prob_ext_diff_compl_raw = prove
 (`!prob (A:W->bool) B.
     (!A B. (!w. A w <=> B w) ==> prob A = prob B)
     ==> prob (ev_diff A B) = prob (ev_inter A (ev_compl B))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[ev_diff_inter_compl]);;

let prob_ext_partition_raw = prove
 (`!prob (A:W->bool) B.
     (!A B. (!w. A w <=> B w) ==> prob A = prob B)
     ==> prob A =
         prob (ev_union (ev_inter A B) (ev_inter A (ev_compl B)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (fun th ->
     MP_TAC
      (ISPECL
        [`A:W->bool`;
         `ev_union (ev_inter (A:W->bool) B) (ev_inter A (ev_compl B))`]
        th)) THEN
  ANTS_TAC THENL
  [MATCH_ACCEPT_TAC (ISPECL [`A:W->bool`; `B:W->bool`] ev_partition);
   DISCH_THEN ACCEPT_TAC]);;

let prob_partition_union_raw = prove
 (`!addR prob (A:W->bool) B.
     (!A B. disjoint A B ==> prob (ev_union A B) = addR (prob A) (prob B))
     ==> prob (ev_union (ev_inter A B) (ev_inter A (ev_compl B))) =
         addR (prob (ev_inter A B)) (prob (ev_inter A (ev_compl B)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_ACCEPT_TAC (ISPECL [`A:W->bool`; `B:W->bool`] ev_partition_disjoint));;

let prob_partition_sum_raw = prove
 (`!(addR:R->R->R) (prob:(W->bool)->R) (A:W->bool) B.
     (!A B. (!w. A w <=> B w) ==> prob A = prob B)
     ==> (!A B. disjoint A B ==> prob (ev_union A B) = addR (prob A) (prob B))
     ==> prob A =
         addR (prob (ev_inter A B)) (prob (ev_inter A (ev_compl B)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `prob (ev_union (ev_inter (A:W->bool) B)
                   (ev_inter A (ev_compl B))):R` THEN
  CONJ_TAC THENL
  [MP_TAC
     (ISPECL [`prob:(W->bool)->R`; `A:W->bool`; `B:W->bool`]
       prob_ext_partition_raw) THEN
   ASM_REWRITE_TAC[];
   MP_TAC
     (ISPECL [`addR:R->R->R`; `prob:(W->bool)->R`;
              `A:W->bool`; `B:W->bool`]
       prob_partition_union_raw) THEN
   ASM_REWRITE_TAC[]]);;

let prob_inter_comm_raw = prove
 (`!prob (A:W->bool) B.
     (!A B. (!w. A w <=> B w) ==> prob A = prob B)
     ==> prob (ev_inter A B) = prob (ev_inter B A)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[ev_inter] THEN MESON_TAC[]);;

let add_swap_eq_raw = prove
 (`!(addR:R->R->R) (a:R) (b:R) (c:R).
     (!x y. addR x y = addR y x)
     ==> a = addR b c
     ==> addR c b = a`,
  MESON_TAC[]);;

let add_sub_right_from_sum_raw = prove
 (`!zeroR addR oppR (x:R) (y:R) (z:R).
     (!a b c. addR (addR a b) c = addR a (addR b c))
     ==> (!a b c. addR a c = addR b c ==> a = b)
     ==> (!a. addR a zeroR = a)
     ==> (!a. addR (oppR a) a = zeroR)
     ==> (!a b. addR a b = addR b a)
     ==> z = addR y x
     ==> x = addR z (oppR y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (fun h_assoc ->
  DISCH_THEN (fun h_cancel ->
  DISCH_THEN (fun h_rzero ->
  DISCH_THEN (fun h_linv ->
  DISCH_THEN (fun h_comm ->
  DISCH_TAC THEN
  MP_TAC
    (ISPECL [`zeroR:R`; `addR:R->R->R`; `oppR:R->R`;
             `x:R`; `y:R`; `z:R`] add_move_right_raw) THEN
  REWRITE_TAC[h_assoc; h_cancel; h_rzero; h_linv] THEN
  ANTS_TAC THENL
  [ASM_MESON_TAC[h_comm]; DISCH_THEN ACCEPT_TAC]))))));;

let indep_compl_right_alg_raw = prove
 (`!oneR addR mulR oppR (x:R) (y:R).
     (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c))
     ==> (!a. mulR a oneR = a)
     ==> (!a b. mulR a (oppR b) = oppR (mulR a b))
     ==> addR x (oppR (mulR x y)) = mulR x (addR oneR (oppR y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

let indep_compl_right_alg_sym_raw = prove
 (`!oneR addR mulR oppR (x:R) (y:R).
     (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c))
     ==> (!a. mulR a oneR = a)
     ==> (!a b. mulR a (oppR b) = oppR (mulR a b))
     ==> mulR x (addR oneR (oppR y)) = addR x (oppR (mulR x y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

let indep_compl_right_raw = prove
 (`!oneR addR mulR oppR prob (A:W->bool) B.
     (!A B. (!w. A w <=> B w) ==> prob A = prob B)
     ==> (!A. prob (ev_compl A) = addR oneR (oppR (prob A)))
     ==> (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c))
     ==> (!a. mulR a oneR = a)
     ==> (!a b. mulR a (oppR b) = oppR (mulR a b))
     ==> prob (ev_diff A B) =
         addR (prob A) (oppR (prob (ev_inter A B)))
     ==> prob (ev_inter A B) = mulR (prob A) (prob B)
     ==> prob (ev_inter A (ev_compl B)) =
         mulR (prob A) (prob (ev_compl B))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (fun h_prob_ext ->
  DISCH_THEN (fun h_prob_compl ->
  DISCH_THEN (fun h_dist ->
  DISCH_THEN (fun h_mul_one ->
  DISCH_THEN (fun h_opp_mul ->
  DISCH_THEN (fun h_diff ->
  DISCH_THEN (fun h_indep ->
  let h_ext =
    MP
      (ISPECL
        [`ev_diff (A:W->bool) B`;
         `ev_inter (A:W->bool) (ev_compl B)`] h_prob_ext)
      (ISPECL [`A:W->bool`; `B:W->bool`] ev_diff_inter_compl) in
  ASSUME_TAC (TRANS (SYM h_ext) h_diff) THEN
  ASM_REWRITE_TAC[h_prob_compl; h_indep] THEN
  ASM_REWRITE_TAC[h_dist; h_mul_one; h_opp_mul]))))))));;

let fold_add_zero = prove
 (`!addR zeroR (xs:R list).
     (!x. addR x zeroR = x)
     ==> (!x. MEM x xs ==> x = zeroR)
     ==> fold_add addR zeroR xs = zeroR`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`xs:R list`,`xs:R list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[fold_add; MEM] THEN
  ASM_MESON_TAC[]);;

let fold_add_map_zero = prove
 (`!addR zeroR (f:A->R) (xs:A list).
     (!x. addR x zeroR = x)
     ==> (!a. MEM a xs ==> f a = zeroR)
     ==> fold_add addR zeroR (MAP f xs) = zeroR`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; fold_add; MEM] THEN
  ASM_MESON_TAC[]);;

let fold_addL_map_zero_raw = prove
 (`!addR zeroR prob (xs:(W->bool) list).
     (!x. addR x zeroR = x)
     ==> (!A. InL A xs ==> prob A = zeroR)
     ==> fold_addL addR zeroR (mapL prob xs) = zeroR`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[InL; mapL; fold_addL] THEN
  MATCH_MP_TAC fold_add_map_zero THEN
  ASM_REWRITE_TAC[]);;

let fold_addL_map_zero = prove
 (`!zeroR oneR addR mulR oppR prob cprob (xs:(W->bool) list).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> (!A. InL A xs ==> prob A = zeroR)
     ==> fold_addL addR zeroR (mapL prob xs) = zeroR`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_prob_context]) THEN
  DISCH_TAC THEN
  MP_TAC
    (ISPECL [`addR:R->R->R`; `zeroR:R`; `prob:(W->bool)->R`;
             `xs:(W->bool) list`] fold_addL_map_zero_raw) THEN
  ASM_REWRITE_TAC[]);;

let prob_bigUnion_disjoint_cons_raw = prove
 (`!(addR:R->R->R) (prob:(W->bool)->R) (h:W->bool)
     (t:(W->bool) list) (s:R).
     (!A B. disjoint A B ==> prob (ev_union A B) = addR (prob A) (prob B))
     ==> disjoint h (bigUnion t)
     ==> prob (bigUnion t) = s
     ==> prob (ev_union h (bigUnion t)) = addR (prob h) s`,
  MESON_TAC[]);;

let prob_bigUnion_disjoint_cons_ih_raw = prove
 (`!(addR:R->R->R) (zeroR:R) (prob:(W->bool)->R)
     (h:W->bool) (t:(W->bool) list).
     (!A B. disjoint A B ==> prob (ev_union A B) = addR (prob A) (prob B))
     ==> disjoint h (bigUnion t)
     ==> (pairwise_disjoint t ==>
          prob (bigUnion t) = fold_addL addR zeroR (mapL prob t))
     ==> pairwise_disjoint t
     ==> prob (ev_union h (bigUnion t)) =
         addR (prob h) (fold_add addR zeroR (MAP prob t))`,
  REWRITE_TAC[fold_addL; mapL] THEN
  MESON_TAC[prob_bigUnion_disjoint_cons_raw]);;

let prob_disjoint_union_context = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> disjoint A B
     ==> prob (ev_union A B) = addR (prob A) (prob B)`,
  INTRO_PROB_HYPS THEN ASM_MESON_TAC[]);;

let pairwise_cons_bigUnion_disjoint_context = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (xs:(W->bool) list).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> pairwise_disjoint (CONS A xs)
     ==> disjoint A (bigUnion xs)`,
  INTRO_PROB_HYPS THEN ASM_MESON_TAC[]);;

let prob_bigUnion_disjoint_cons_context = prove
 (`!zeroR oneR addR mulR oppR prob cprob
     (h:W->bool) (t:(W->bool) list).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> disjoint h (bigUnion t)
     ==> (pairwise_disjoint t ==>
          prob (bigUnion t) = fold_addL addR zeroR (mapL prob t))
     ==> pairwise_disjoint t
     ==> prob (ev_union h (bigUnion t)) =
         addR (prob h) (fold_add addR zeroR (MAP prob t))`,
  REWRITE_TAC[fold_addL; mapL] THEN
  MESON_TAC[prob_disjoint_union_context]);;

let prob_bigUnion_disjoint_cons_step_context = prove
 (`!zeroR oneR addR mulR oppR prob cprob
     (h:W->bool) (t:(W->bool) list).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> (!B. MEM B t ==> disjoint h B)
     ==> pairwise_disjoint t
     ==> (pairwise_disjoint t ==>
          prob (bigUnion t) = fold_addL addR zeroR (mapL prob t))
     ==> prob (ev_union h (bigUnion t)) =
         addR (prob h) (fold_add addR zeroR (MAP prob t))`,
  REWRITE_TAC[fold_addL; mapL] THEN
  MESON_TAC[pairwise_cons_bigUnion_disjoint_context;
            prob_disjoint_union_context; pairwise_disjoint]);;





let prob_union_comm = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> prob (ev_union A B) = prob (ev_union B A)`,
  INTRO_PROB_HYPS THEN
  ASSUM_MATCH_TAC
    `!A B. (!w. A w <=> B w) ==> prob A = prob B`
    MATCH_MP_TAC THEN
  REWRITE_TAC[ev_union] THEN MESON_TAC[]);;

let prob_union_idem = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> prob (ev_union A A) = prob A`,
  INTRO_PROB_HYPS THEN
  ASSUM_MATCH_TAC
    `!A B. (!w. A w <=> B w) ==> prob A = prob B`
    MATCH_MP_TAC THEN
  REWRITE_TAC[ev_union] THEN MESON_TAC[]);;

let prob_diff = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> prob (ev_diff A B) =
         subR addR oppR (prob A) (prob (ev_inter A B))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[subR] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_prob_context]) THEN
  MP_TAC
    (ISPECL [`prob:(W->bool)->R`; `A:W->bool`; `B:W->bool`]
      prob_ext_diff_compl_raw) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL [`addR:R->R->R`; `prob:(W->bool)->R`;
             `A:W->bool`; `B:W->bool`]
      prob_partition_sum_raw) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`zeroR:R`; `addR:R->R->R`; `oppR:R->R`;
       `prob (ev_inter (A:W->bool) (ev_compl B)):R`;
       `prob (ev_inter A B):R`; `prob (A:W->bool):R`]
      add_sub_right_from_sum_raw) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

let bayes_symm = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> mulR (cprob A B) (prob B) = mulR (cprob B A) (prob A)`,
  INTRO_PROB_HYPS THEN
  MP_TAC
    (ISPECL [`prob:(W->bool)->R`; `A:W->bool`; `B:W->bool`]
      prob_inter_comm_raw) THEN
  ASM_REWRITE_TAC[]);;

let law_total_prob = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> prob A =
         addR (mulR (cprob A B) (prob B))
              (mulR (cprob A (ev_compl B)) (prob (ev_compl B)))`,
  INTRO_PROB_HYPS THEN
  MP_TAC
    (ISPECL [`addR:R->R->R`; `prob:(W->bool)->R`;
             `A:W->bool`; `B:W->bool`]
      prob_partition_sum_raw) THEN
  ASM_REWRITE_TAC[]);;

let prob_union_indep = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> indep prob mulR A B
     ==> prob (ev_union A B) =
         addR (prob A) (addR (prob B) (oppR (mulR (prob A) (prob B))))`,
  INTRO_PROB_HYPS THEN REWRITE_TAC[indep] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let indep_compl_right = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> indep prob mulR A B
     ==> indep prob mulR A (ev_compl B)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_prob_context]) THEN
  REWRITE_TAC[indep] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
       `oppR:R->R`; `prob:(W->bool)->R`; `cprob:(W->bool)->(W->bool)->R`;
       `A:W->bool`; `B:W->bool`] prob_diff) THEN
  ASM_REWRITE_TAC[subR] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL [`oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
             `oppR:R->R`; `prob:(W->bool)->R`; `A:W->bool`; `B:W->bool`]
      indep_compl_right_raw) THEN
  ASM_REWRITE_TAC[]);;

let indep_symm = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> indep prob mulR A B ==> indep prob mulR B A`,
  INTRO_PROB_HYPS THEN REWRITE_TAC[indep] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL [`prob:(W->bool)->R`; `B:W->bool`; `A:W->bool`]
      prob_inter_comm_raw) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

let indep_compl_left = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> indep prob mulR A B ==> indep prob mulR (ev_compl A) B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
       `oppR:R->R`; `prob:(W->bool)->R`; `cprob:(W->bool)->(W->bool)->R`;
       `A:W->bool`; `B:W->bool`] indep_symm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
       `oppR:R->R`; `prob:(W->bool)->R`; `cprob:(W->bool)->(W->bool)->R`;
       `B:W->bool`; `A:W->bool`] indep_compl_right) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
       `oppR:R->R`; `prob:(W->bool)->R`; `cprob:(W->bool)->(W->bool)->R`;
       `B:W->bool`; `ev_compl (A:W->bool)`] indep_symm) THEN
  ASM_REWRITE_TAC[]);;

let indep_compl_both = prove
 (`!zeroR oneR addR mulR oppR prob cprob (A:W->bool) (B:W->bool).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> indep prob mulR A B
     ==> indep prob mulR (ev_compl A) (ev_compl B)`,
  INTRO_PROB_HYPS THEN DISCH_TAC THEN
  ASSUM_MATCH_TAC
    `!A B. indep prob mulR A B ==> indep prob mulR (ev_compl A) (ev_compl B)`
    (fun th -> MATCH_MP_TAC (ISPECL [`A:W->bool`; `B:W->bool`] th)) THEN
  ASM_REWRITE_TAC[]);;

let inclusion_exclusion_three = prove
 (`!zeroR oneR addR mulR oppR prob cprob A B C.
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> prob (ev_union (ev_union A B) C) =
         addR (prob A)
           (addR (prob B)
             (addR (prob C)
               (oppR (addR (prob (ev_inter A B))
                 (addR (prob (ev_inter A C))
                   (addR (prob (ev_inter B C))
                     (oppR (prob (ev_inter (ev_inter A B) C)))))))))`,
  INTRO_PROB_HYPS THEN
  ASSUM_MATCH_TAC
    `!A B C.
       prob (ev_union (ev_union A B) C) =
       addR (prob A)
         (addR (prob B)
           (addR (prob C)
             (oppR (addR (prob (ev_inter A B))
               (addR (prob (ev_inter A C))
                 (addR (prob (ev_inter B C))
                   (oppR (prob (ev_inter (ev_inter A B) C)))))))))`
    (fun th -> MATCH_ACCEPT_TAC
       (ISPECL [`A:W->bool`; `B:W->bool`; `C:W->bool`] th)));;

let prob_bigUnion_disjoint = prove
 (`!zeroR oneR addR mulR oppR prob cprob (xs:(W->bool) list).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> pairwise_disjoint xs
     ==> prob (bigUnion xs) = fold_addL addR zeroR (mapL prob xs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[is_prob_context]) THEN
  SPEC_TAC(`xs:(W->bool) list`,`xs:(W->bool) list`) THEN
  LIST_INDUCT_TAC THENL
  [(REWRITE_TAC[bigUnion; mapL; fold_addL; fold_add; MAP; pairwise_disjoint] THEN
    ASM_REWRITE_TAC[]);
   (REWRITE_TAC[bigUnion; mapL; fold_addL; fold_add; MAP; pairwise_disjoint] THEN
    STRIP_TAC THEN
    MP_TAC
    (ISPECL
      [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
       `oppR:R->R`; `prob:(W->bool)->R`; `cprob:(W->bool)->(W->bool)->R`;
       `h:W->bool`; `t:(W->bool) list`]
      prob_bigUnion_disjoint_cons_step_context) THEN
    ASM_REWRITE_TAC[]) ]);;

let prob_bigUnion_disjoint_zero = prove
 (`!zeroR oneR addR mulR oppR prob cprob (xs:(W->bool) list).
     is_prob_context zeroR oneR addR mulR oppR prob cprob
     ==> pairwise_disjoint xs
     ==> (!A. InL A xs ==> prob A = zeroR)
     ==> prob (bigUnion xs) = zeroR`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
       `oppR:R->R`; `prob:(W->bool)->R`; `cprob:(W->bool)->(W->bool)->R`;
       `xs:(W->bool) list`] prob_bigUnion_disjoint) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (ISPECL
      [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
       `oppR:R->R`; `prob:(W->bool)->R`; `cprob:(W->bool)->(W->bool)->R`;
       `xs:(W->bool) list`] fold_addL_map_zero) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;
