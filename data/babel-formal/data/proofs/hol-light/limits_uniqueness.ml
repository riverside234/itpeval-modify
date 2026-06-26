let limit = new_definition
  `limit zero lt absV le sub natLe u l <=>
     !eps. lt zero eps ==>
       ?N. !n. natLe N n ==> le (absV (sub (u n) l)) eps`;;

let abs_sub_triangle = prove
 (`!(absV:A->A) (le:A->A->bool) (add:A->A->A) (sub:A->A->A) (x:A) (y:A) (z:A).
      (!u v w. sub u w = add (sub u v) (sub v w)) /\
      (!u v. le (absV (add u v)) (add (absV u) (absV v))) /\
      (!u v w. le u v ==> le v w ==> le u w) ==>
      le (absV (sub x z)) (add (absV (sub x y)) (absV (sub y z)))`,
  REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(sub:A->A->A) x z = add (sub x y) (sub y z)` SUBST1_TAC THENL
  [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let limit_unique = prove
 (`!zero add absV le lt sub natLe natMax u l m.
      (!x y. natLe x (natMax x y)) /\
      (!x y. natLe y (natMax x y)) /\
      (!x y z. sub x z = add (sub x y) (sub y z)) /\
      (!x y. absV (sub x y) = absV (sub y x)) /\
      (!x y z. le x y ==> le y z ==> le x z) /\
      (!a b c d. le a b ==> le c d ==> le (add a c) (add b d)) /\
      (!x y. le (absV (add x y)) (add (absV x) (absV y))) /\
      (!x y. sub x y = zero ==> x = y) /\
      (!x. (!eps. lt zero eps ==> le (absV x) (add eps eps)) ==> x = zero) /\
      limit zero lt absV le sub natLe u l ==>
      limit zero lt absV le sub natLe u m ==>
      l = m`,
  REWRITE_TAC[limit] THEN MESON_TAC[]);;
