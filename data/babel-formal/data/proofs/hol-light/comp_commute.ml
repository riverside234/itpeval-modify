let myComp = new_definition
  `myComp (g:B->C) (f:A->B) = (\x:A. g (f x))`;;

let myId = new_definition
  `myId = (\x:A. x)`;;

let comp_assoc = prove
  (`!h g f. myComp h (myComp g f) = myComp (myComp h g) f`,
   REWRITE_TAC[myComp]);;

let comp_id_l = prove
  (`!f:A->B. myComp myId f = f`,
   REWRITE_TAC[myComp; myId; FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC[]);;

let comp_id_r = prove
  (`!f:A->B. myComp f myId = f`,
   REWRITE_TAC[myComp; myId; FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC[]);;

let commute = new_definition
  `commute (f:A->A) (g:A->A) <=> myComp f g = myComp g f`;;

let commute_symm = prove
  (`!f g. commute f g ==> commute g f`,
   REWRITE_TAC[commute] THEN MESON_TAC[]);;

let commute_with_id_l = prove
  (`!f:A->A. commute f myId`,
   REWRITE_TAC[commute] THEN
   REWRITE_TAC[comp_id_l; comp_id_r]);;

let commute_with_id_r = prove
  (`!f:A->A. commute myId f`,
   REWRITE_TAC[commute] THEN
   REWRITE_TAC[comp_id_l; comp_id_r]);;

let commute_refl = prove
  (`!f:A->A. commute f f`,
   REWRITE_TAC[commute]);;

let commute_congr = prove
  (`!f1 f2 g1 g2:A->A.
      f1 = f2 ==> g1 = g2 ==> commute f1 g1 ==> commute f2 g2`,
   REWRITE_TAC[commute] THEN MESON_TAC[]);;

let commute_transport_left_id = prove
  (`!f g:A->A. commute f g ==> commute (myComp myId f) g`,
   REWRITE_TAC[commute] THEN
   REWRITE_TAC[comp_id_l]);;

let commute_transport_right_id = prove
  (`!f g:A->A. commute f g ==> commute f (myComp myId g)`,
   REWRITE_TAC[commute] THEN
   REWRITE_TAC[comp_id_l]);;
