let is_lattice_like = new_definition
  `is_lattice_like (le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A) <=>
     (!x. le_rel x x) /\
     (!x y z. le_rel x y /\ le_rel y z ==> le_rel x z) /\
     (!x y. le_rel x y /\ le_rel y x ==> x = y) /\
     (!a b. le_rel (inf_op a b) a) /\
     (!a b. le_rel (inf_op a b) b) /\
     (!c a b. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)) /\
     (!a b. le_rel a (sup_op a b)) /\
     (!a b. le_rel b (sup_op a b)) /\
     (!a b c. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c)`;;

let INTRO_LATTICE_HYPS =
  REWRITE_TAC[is_lattice_like] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

let inf_comm = prove
  (`!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. inf_op a b = inf_op b a`,
   INTRO_LATTICE_HYPS THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC
     (SPECL [`inf_op (a:A) (b:A) : A`; `inf_op (b:A) (a:A) : A`]
            (ASSUME `!x:A y:A. le_rel x y /\ le_rel y x ==> x = y`)) THEN
   CONJ_TAC THENL
   [
     MATCH_MP_TAC
       (SPECL [`inf_op (a:A) (b:A) : A`; `b:A`; `a:A`]
              (ASSUME `!c:A a:A b:A. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)`)) THEN
     ASM_MESON_TAC[]
   ;
     MATCH_MP_TAC
       (SPECL [`inf_op (b:A) (a:A) : A`; `a:A`; `b:A`]
              (ASSUME `!c:A a:A b:A. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)`)) THEN
     ASM_MESON_TAC[] ]);;

let sup_comm = prove
  (`!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. sup_op a b = sup_op b a`,
   INTRO_LATTICE_HYPS THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC
     (SPECL [`sup_op (a:A) (b:A) : A`; `sup_op (b:A) (a:A) : A`]
            (ASSUME `!x:A y:A. le_rel x y /\ le_rel y x ==> x = y`)) THEN
   CONJ_TAC THENL
   [
     MATCH_MP_TAC
       (SPECL [`a:A`; `b:A`; `sup_op (b:A) (a:A) : A`]
              (ASSUME `!a:A b:A c:A. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c`)) THEN
     ASM_MESON_TAC[]
   ;
     MATCH_MP_TAC
       (SPECL [`b:A`; `a:A`; `sup_op (a:A) (b:A) : A`]
              (ASSUME `!a:A b:A c:A. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c`)) THEN
     ASM_MESON_TAC[] ]);;

let inf_assoc = prove
  (`!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==>
      !a b c:A. inf_op (inf_op a b) c = inf_op a (inf_op b c)`,
   INTRO_LATTICE_HYPS THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC
     (SPECL [`inf_op (inf_op (a:A) (b:A) : A) (c:A) : A`;
             `inf_op (a:A) (inf_op (b:A) (c:A) : A) : A`]
            (ASSUME `!x:A y:A. le_rel x y /\ le_rel y x ==> x = y`)) THEN
   CONJ_TAC THENL
   [
     MATCH_MP_TAC (ASSUME `!c:A a:A b:A. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)`) THEN
     CONJ_TAC THENL
     [
       MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
       ASM_MESON_TAC[]
     ;
       MATCH_MP_TAC (ASSUME `!c:A a:A b:A. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)`) THEN
       CONJ_TAC THENL
       [
         MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
         ASM_MESON_TAC[]
       ; ASM_MESON_TAC[] ] ]
   ;
     MATCH_MP_TAC (ASSUME `!c:A a:A b:A. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)`) THEN
     CONJ_TAC THENL
     [
       MATCH_MP_TAC (ASSUME `!c:A a:A b:A. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)`) THEN
       CONJ_TAC THENL
       [ ASM_MESON_TAC[]
       ; MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
         ASM_MESON_TAC[] ]
     ;
       MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
       ASM_MESON_TAC[] ] ]);;

let sup_assoc = prove
  (`!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==>
      !a b c:A. sup_op (sup_op a b) c = sup_op a (sup_op b c)`,
   INTRO_LATTICE_HYPS THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC
     (SPECL [`sup_op (sup_op (a:A) (b:A) : A) (c:A) : A`;
             `sup_op (a:A) (sup_op (b:A) (c:A) : A) : A`]
            (ASSUME `!x:A y:A. le_rel x y /\ le_rel y x ==> x = y`)) THEN
   CONJ_TAC THENL
   [
     MATCH_MP_TAC (ASSUME `!a:A b:A c:A. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c`) THEN
     CONJ_TAC THENL
     [
       MATCH_MP_TAC (ASSUME `!a:A b:A c:A. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c`) THEN
       CONJ_TAC THENL
       [ ASM_MESON_TAC[]
       ; MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
         ASM_MESON_TAC[] ]
     ;
       MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
       ASM_MESON_TAC[] ]
   ;
     MATCH_MP_TAC (ASSUME `!a:A b:A c:A. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c`) THEN
     CONJ_TAC THENL
     [
       MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
       ASM_MESON_TAC[]
     ;
       MATCH_MP_TAC (ASSUME `!a:A b:A c:A. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c`) THEN
       CONJ_TAC THENL
       [ MATCH_MP_TAC (ASSUME `!x:A y:A z:A. le_rel x y /\ le_rel y z ==> le_rel x z`) THEN
         ASM_MESON_TAC[]
       ; ASM_MESON_TAC[] ] ] ]);;

let inf_absorption = prove
  (`!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. inf_op a (sup_op a b) = a`,
   INTRO_LATTICE_HYPS THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC
     (SPECL [`inf_op (a:A) (sup_op (a:A) (b:A) : A) : A`; `a:A`]
            (ASSUME `!x:A y:A. le_rel x y /\ le_rel y x ==> x = y`)) THEN
   CONJ_TAC THENL
   [ ASM_MESON_TAC[]
   ; MATCH_MP_TAC (ASSUME `!c:A a:A b:A. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)`) THEN
     ASM_MESON_TAC[] ]);;

let sup_absorption = prove
  (`!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. sup_op a (inf_op a b) = a`,
   INTRO_LATTICE_HYPS THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC
     (SPECL [`sup_op (a:A) (inf_op (a:A) (b:A) : A) : A`; `a:A`]
            (ASSUME `!x:A y:A. le_rel x y /\ le_rel y x ==> x = y`)) THEN
   CONJ_TAC THENL
   [ MATCH_MP_TAC (ASSUME `!a:A b:A c:A. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c`) THEN
     ASM_MESON_TAC[]
   ; ASM_MESON_TAC[] ]);;
