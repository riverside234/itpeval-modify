let field_like = new_definition
  `field_like (zero_F:'a) (one_F:'a) (add_F:'a->'a->'a) (mul_F:'a->'a->'a)
              (opp_F:'a->'a) (inv_F:'a->'a) <=>
     (!x:'a y:'a. add_F x y = add_F y x) /\
     (!x:'a y:'a z:'a. add_F (add_F x y) z = add_F x (add_F y z)) /\
     (!x:'a. add_F x zero_F = x) /\
     (!x:'a. add_F (opp_F x) x = zero_F) /\
     (!x:'a y:'a. mul_F x y = mul_F y x) /\
     (!x:'a y:'a z:'a. mul_F (mul_F x y) z = mul_F x (mul_F y z)) /\
     (!x:'a. mul_F one_F x = x) /\
     (!x:'a. ~(x = zero_F) ==> mul_F (inv_F x) x = one_F) /\
     (!x:'a y:'a z:'a. mul_F x (add_F y z) = add_F (mul_F x y) (mul_F x z)) /\
     ~(zero_F = one_F) /\
     (!x:'a. ~(x = zero_F) ==> ~(inv_F x = zero_F))`;;

let tower = new_definition
  `tower (solv:'a->bool) (mp:'a->'a) (splt:'a->bool) <=>
     (!p:'a q:'a. solv p ==> solv (mp q) ==> solv q) /\
     (!p:'a. solv p ==> solv (mp p)) /\
     (!p:'a. splt p ==> solv p)`;;

let zero_add = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==> !x:'f. add_F zero_F x = x`,
   REWRITE_TAC[field_like] THEN MESON_TAC[]);;

let mul_one_r = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==> !x. mul_F x one_F = x`,
   REWRITE_TAC[field_like] THEN MESON_TAC[]);;

let mul_inv_r = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x. ~(x = zero_F) ==> mul_F x (inv_F x) = one_F`,
   REPEAT GEN_TAC THEN REWRITE_TAC[field_like] THEN
   DISCH_THEN(fun hfield ->
     let [_; _; _; _;
          hmul_comm; _; _; hmul_inv_l;
          _; _; _] = CONJUNCTS hfield in
     GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC
      `(mul_F:'f->'f->'f) ((inv_F:'f->'f) (x:'f)) (x:'f)` THEN
     CONJ_TAC THENL
      [MATCH_ACCEPT_TAC
        (SPECL [`x:'f`; `(inv_F:'f->'f) (x:'f)`] hmul_comm);
       MATCH_MP_TAC (SPEC `x:'f` hmul_inv_l) THEN
       ASM_REWRITE_TAC[]]));;

let add_cancel_l = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. add_F x y = add_F x z ==> y = z`,
   REPEAT GEN_TAC THEN REWRITE_TAC[field_like] THEN
   DISCH_THEN(fun hfield ->
     let [add_comm; add_assoc; add_zero; add_inv_l; _; _; _; _; _; _; _] =
       CONJUNCTS hfield in
     REPEAT GEN_TAC THEN DISCH_THEN(fun heq ->
       let assoc_y =
         SYM
          (SPECL
            [`(opp_F:'f->'f) (x:'f)`; `x:'f`; `y:'f`]
            add_assoc) in
       let inv_y =
         BETA_RULE
           (AP_TERM `\t:'f. (add_F:'f->'f->'f) t (y:'f)`
             (SPEC `x:'f` add_inv_l)) in
       let zero_y =
         TRANS (SPECL [`(zero_F:'f)`; `y:'f`] add_comm)
               (SPEC `y:'f` add_zero) in
       let cancel_y = TRANS assoc_y (TRANS inv_y zero_y) in
       let assoc_z =
         SYM
          (SPECL
            [`(opp_F:'f->'f) (x:'f)`; `x:'f`; `z:'f`]
            add_assoc) in
       let inv_z =
         BETA_RULE
           (AP_TERM `\t:'f. (add_F:'f->'f->'f) t (z:'f)`
             (SPEC `x:'f` add_inv_l)) in
       let zero_z =
         TRANS (SPECL [`(zero_F:'f)`; `z:'f`] add_comm)
               (SPEC `z:'f` add_zero) in
       let cancel_z = TRANS assoc_z (TRANS inv_z zero_z) in
       let cong =
         BETA_RULE
           (AP_TERM
             `\t:'f.
                (add_F:'f->'f->'f)
                  ((opp_F:'f->'f) (x:'f)) t`
             heq) in
       MATCH_ACCEPT_TAC (TRANS (TRANS (SYM cancel_y) cong) cancel_z))));;

let add_cancel_r = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. add_F y x = add_F z x ==> y = z`,
   REPEAT GEN_TAC THEN DISCH_THEN(fun hfield ->
     let [add_comm; _; _; _; _; _; _; _; _; _; _] =
       CONJUNCTS (REWRITE_RULE[field_like] hfield) in
     REPEAT GEN_TAC THEN DISCH_THEN(fun heq ->
       let heq' =
         TRANS (SPECL [`x:'f`; `y:'f`] add_comm)
               (TRANS heq (SPECL [`z:'f`; `x:'f`] add_comm)) in
       let cancel_l =
         MATCH_MP
           (SPECL
             [`(zero_F:'f)`;
              `(one_F:'f)`;
              `(add_F:'f->'f->'f)`;
              `(mul_F:'f->'f->'f)`;
              `(opp_F:'f->'f)`;
              `(inv_F:'f->'f)`]
             add_cancel_l)
           hfield in
       MATCH_ACCEPT_TAC
         (MATCH_MP (SPECL [`x:'f`; `y:'f`; `z:'f`] cancel_l) heq'))));;

let mul_cancel_l = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. ~(x = zero_F) ==> mul_F x y = mul_F x z ==> y = z`,
   REPEAT GEN_TAC THEN DISCH_THEN(fun hfield ->
     let [_; _; _; _; _; mul_assoc; mul_one_l; mul_inv_l; _; _; _] =
       CONJUNCTS (REWRITE_RULE[field_like] hfield) in
     REPEAT GEN_TAC THEN DISCH_THEN(fun hx ->
	       DISCH_THEN(fun heq ->
	         let eq_inv = MATCH_MP (SPEC `x:'f` mul_inv_l) hx in
	         let th1 = SYM (SPEC `y:'f` mul_one_l) in
	         let th2 =
	           BETA_RULE
	             (AP_TERM `\t:'f. (mul_F:'f->'f->'f) t (y:'f)` (SYM eq_inv)) in
         let th3 =
           SPECL
             [`(inv_F:'f->'f) (x:'f)`; `x:'f`; `y:'f`]
             mul_assoc in
	         let th4 =
	           BETA_RULE
	             (AP_TERM
	               `\t:'f. (mul_F:'f->'f->'f) ((inv_F:'f->'f) (x:'f)) t`
	               heq) in
         let th5 =
           SYM
            (SPECL
              [`(inv_F:'f->'f) (x:'f)`; `x:'f`; `z:'f`]
              mul_assoc) in
	         let th6 =
	           BETA_RULE
	             (AP_TERM `\t:'f. (mul_F:'f->'f->'f) t (z:'f)` eq_inv) in
         let th7 = SPEC `z:'f` mul_one_l in
         MATCH_ACCEPT_TAC
          (TRANS th1
            (TRANS th2
              (TRANS th3
                (TRANS th4 (TRANS th5 (TRANS th6 th7))))))))));;

let mul_cancel_r = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. ~(x = zero_F) ==> mul_F y x = mul_F z x ==> y = z`,
   REPEAT GEN_TAC THEN DISCH_THEN(fun hfield ->
     let [_; _; _; _; mul_comm; _; _; _; _; _; _] =
       CONJUNCTS (REWRITE_RULE[field_like] hfield) in
     REPEAT GEN_TAC THEN DISCH_THEN(fun hx ->
       DISCH_THEN(fun heq ->
         let heq' =
           TRANS (SPECL [`x:'f`; `y:'f`] mul_comm)
                 (TRANS heq (SPECL [`z:'f`; `x:'f`] mul_comm)) in
         let cancel_l =
           MATCH_MP
             (SPECL
               [`(zero_F:'f)`;
                `(one_F:'f)`;
                `(add_F:'f->'f->'f)`;
                `(mul_F:'f->'f->'f)`;
                `(opp_F:'f->'f)`;
                `(inv_F:'f->'f)`]
               mul_cancel_l)
             hfield in
         MATCH_ACCEPT_TAC
           (MATCH_MP
             (MATCH_MP (SPECL [`x:'f`; `y:'f`; `z:'f`] cancel_l) hx)
             heq')))));;

let inv_unique = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y. ~(x = zero_F) ==> mul_F x y = one_F ==> y = inv_F x`,
   REPEAT GEN_TAC THEN DISCH_THEN(fun hfield ->
     let [_; _; _; _; _; mul_assoc; mul_one_l; mul_inv_l; _; _; _] =
       CONJUNCTS (REWRITE_RULE[field_like] hfield) in
     let mul_one_r_th =
       MATCH_MP
         (SPECL
           [`(zero_F:'f)`;
            `(one_F:'f)`;
            `(add_F:'f->'f->'f)`;
            `(mul_F:'f->'f->'f)`;
            `(opp_F:'f->'f)`;
            `(inv_F:'f->'f)`]
           mul_one_r)
         hfield in
     REPEAT GEN_TAC THEN DISCH_THEN(fun hx ->
	       DISCH_THEN(fun heq ->
	         let eq_inv = MATCH_MP (SPEC `x:'f` mul_inv_l) hx in
	         let th1 = SYM (SPEC `y:'f` mul_one_l) in
	         let th2 =
	           BETA_RULE
	             (AP_TERM `\t:'f. (mul_F:'f->'f->'f) t (y:'f)` (SYM eq_inv)) in
         let th3 =
           SPECL
             [`(inv_F:'f->'f) (x:'f)`; `x:'f`; `y:'f`]
             mul_assoc in
	         let th4 =
	           BETA_RULE
	             (AP_TERM
	               `\t:'f. (mul_F:'f->'f->'f) ((inv_F:'f->'f) (x:'f)) t`
	               heq) in
         let th5 = SPEC `(inv_F:'f->'f) (x:'f)` mul_one_r_th in
         MATCH_ACCEPT_TAC (TRANS th1 (TRANS th2 (TRANS th3 (TRANS th4 th5))))))));;

let inv_involutive = prove
  (`!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x. ~(x = zero_F) ==> inv_F (inv_F x) = x`,
   REPEAT GEN_TAC THEN DISCH_THEN(fun hfield ->
     let [_; _; _; _; _; _; _; mul_inv_l; _; _; inv_nonzero] =
       CONJUNCTS (REWRITE_RULE[field_like] hfield) in
     let inv_unique_th =
       MATCH_MP
         (SPECL
           [`(zero_F:'f)`;
            `(one_F:'f)`;
            `(add_F:'f->'f->'f)`;
            `(mul_F:'f->'f->'f)`;
            `(opp_F:'f->'f)`;
            `(inv_F:'f->'f)`]
           inv_unique)
         hfield in
     GEN_TAC THEN DISCH_THEN(fun hx ->
       let hx_inv = MATCH_MP (SPEC `x:'f` inv_nonzero) hx in
       let eq_inv = MATCH_MP (SPEC `x:'f` mul_inv_l) hx in
       let eq =
         MATCH_MP
           (MATCH_MP
             (SPECL [`(inv_F:'f->'f) (x:'f)`; `x:'f`] inv_unique_th)
             hx_inv)
           eq_inv in
       MATCH_ACCEPT_TAC (SYM eq))));;

let gal_isSolvable_tower = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv q`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_double_tower = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a r:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv (mp r) ==> solv r`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_triple_tower = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a r:'a s:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv (mp r) ==> solv (mp s) ==> solv s`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_quadruple_tower = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a r:'a s:'a t:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv (mp r) ==> solv (mp s) ==> solv (mp t) ==> solv t`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_map_poly = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp p)`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_of_split = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> splt p ==> solv p`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_split_tower = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool q:'a.
      tower solv mp splt ==> splt q ==> solv q`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_two_step_map = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp (mp p))`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_three_step_map = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp (mp (mp p)))`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_map_poly_comp = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp (mp p))`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_mutual_split = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a.
      tower solv mp splt ==> splt p ==> splt q ==> solv p /\ solv q`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_map_after_split = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> splt p ==> solv (mp p)`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;

let gal_isSolvable_tower_split = prove
  (`!solv:'a->bool mp:'a->'a splt:'a->bool q:'a r:'a.
      tower solv mp splt ==> splt q ==> solv (mp r) ==> solv r`,
   REWRITE_TAC[tower] THEN MESON_TAC[]);;
