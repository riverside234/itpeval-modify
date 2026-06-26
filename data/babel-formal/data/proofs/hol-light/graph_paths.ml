let path_RULES,path_INDUCT,path_CASES = new_inductive_definition
  `(!E:A->A->bool v. path E v v) /\
   (!E:A->A->bool u v w. path E u v /\ E v w ==> path E u w)`;;

let undirected = new_definition
  `undirected (E:A->A->bool) <=> !x y. E x y ==> E y x`;;

let erev = new_definition
  `erev (E:A->A->bool) x y <=> E y x`;;

let path_refl = prove
  (`!E:A->A->bool v. path E v v`,
   MESON_TAC[path_RULES]);;

let path_append_right = prove
  (`!E:A->A->bool v w. path E v w ==> !u. path E u v ==> path E u w`,
   MATCH_MP_TAC path_INDUCT THEN MESON_TAC[path_RULES]);;

let path_trans = prove
  (`!E:A->A->bool u v w. path E u v ==> path E v w ==> path E u w`,
   MESON_TAC[path_append_right]);;

let trans = path_trans;;

let edge_path = prove
  (`!E:A->A->bool u v. E u v ==> path E u v`,
   MESON_TAC[path_RULES]);;

let concat_edge_right = prove
  (`!E:A->A->bool u v w. path E u v ==> E v w ==> path E u w`,
   MESON_TAC[path_RULES]);;

let concat = path_trans;;

let concat_edge_left = prove
  (`!E:A->A->bool u v w. E u v ==> path E v w ==> path E u w`,
   MESON_TAC[edge_path; path_trans]);;

let concat3 = prove
  (`!E:A->A->bool u v w t.
      path E u v ==> path E v w ==> path E w t ==> path E u t`,
   MESON_TAC[path_trans]);;

let reverse_edge_Erev = prove
  (`!E:A->A->bool v w. E v w ==> path (erev E) w v`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC edge_path THEN ASM_REWRITE_TAC[erev]);;

let reverse_step_Erev = prove
  (`!E:A->A->bool u v w.
      path (erev E) v u ==> E v w ==> path (erev E) w u`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
   MP_TAC (SPECL
     [`erev (E:A->A->bool)`; `w:A`; `v:A`; `u:A`] path_trans) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC reverse_edge_Erev THEN ASM_REWRITE_TAC[]);;

let reverse_in_Erev = prove
  (`!E:A->A->bool u v. path E u v ==> path (erev E) v u`,
   MATCH_MP_TAC path_INDUCT THEN CONJ_TAC THENL
    [MESON_TAC[path_RULES];
     MESON_TAC[reverse_step_Erev]]);;

let path_mono = prove
  (`!(E:A->A->bool) (G:A->A->bool) u v.
      (!x y. E x y ==> G x y) ==> path E u v ==> path G u v`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   MP_TAC (SPEC
     `\(H:A->A->bool) (x:A) (y:A).
        H = (E:A->A->bool) ==> path (G:A->A->bool) x y`
     path_INDUCT) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MESON_TAC[path_RULES];
       ASM_MESON_TAC[path_RULES]];
     DISCH_THEN (MP_TAC o SPECL [`E:A->A->bool`; `u:A`; `v:A`]) THEN
     ASM_REWRITE_TAC[]]);;

let reverse_path = prove
  (`!E:A->A->bool u v. undirected E ==> path E u v ==> path E v u`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
   MP_TAC (SPECL [`E:A->A->bool`; `u:A`; `v:A`] reverse_in_Erev) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC (SPECL [`erev (E:A->A->bool)`; `E:A->A->bool`; `v:A`; `u:A`] path_mono) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC[undirected; erev]);;

let cycle_refl = prove
  (`!E:A->A->bool v w. path E v w ==> path E w v ==> path E v v`,
   MESON_TAC[path_trans]);;
