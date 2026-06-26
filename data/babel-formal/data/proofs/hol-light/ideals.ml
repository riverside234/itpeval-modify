let cring = new_definition
  `cring (zero:'r) (oneR:'r) (add:'r->'r->'r) (mul:'r->'r->'r) (opp:'r->'r) <=>
     (!x y. add x y = add y x) /\
     (!x y z. add (add x y) z = add x (add y z)) /\
     (!x. add x zero = x) /\
     (!x. add x (opp x) = zero) /\
     (!x y. mul x y = mul y x) /\
     (!x y z. mul (mul x y) z = mul x (mul y z)) /\
     (!x. mul x oneR = x) /\
     (!a x y. mul a (add x y) = add (mul a x) (mul a y)) /\
     (!x y. opp (add x y) = add (opp x) (opp y))`;;

let IsIdeal = new_definition
  `IsIdeal (zero:'r) (add:'r->'r->'r) (mul:'r->'r->'r) (opp:'r->'r)
           (ideal:'r->bool) <=>
     ideal zero /\
     (!x y. ideal x /\ ideal y ==> ideal (add x y)) /\
     (!x. ideal x ==> ideal (opp x)) /\
     (!a x. ideal x ==> ideal (mul a x))`;;

let inter = new_definition
  `inter (fam:'i->'r->bool) = (\x:'r. !i. fam i x)`;;

let add_rearrange = prove
  (`!zeroR:'r oneR:'r (add:'r->'r->'r) (mul:'r->'r->'r) (opp:'r->'r).
      cring zeroR oneR add mul opp ==>
      !a:'r b c d. add (add a b) (add c d) = add (add a c) (add b d)`,
   REWRITE_TAC[cring] THEN MESON_TAC[]);;

let ideal_sum = new_definition
  `ideal_sum (add:'r->'r->'r) (ideal1:'r->bool) (ideal2:'r->bool) =
     (\x:'r. ?a b. ideal1 a /\ ideal2 b /\ x = add a b)`;;

let inter_isIdeal = prove
  (`!zeroR oneR add mul opp (fam:'i->'r->bool).
      cring zeroR oneR add mul opp ==>
      (!i. IsIdeal zeroR add mul opp (fam i)) ==>
      IsIdeal zeroR add mul opp (inter fam)`,
   REWRITE_TAC[cring; IsIdeal; inter] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[]);;

let sum_isIdeal = prove
  (`!zeroR oneR add mul opp (ideal1:'r->bool) (ideal2:'r->bool).
      cring zeroR oneR add mul opp ==>
      IsIdeal zeroR add mul opp ideal1 ==>
      IsIdeal zeroR add mul opp ideal2 ==>
      IsIdeal zeroR add mul opp (ideal_sum add ideal1 ideal2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun hring ->
    DISCH_THEN(fun hideal1 ->
      DISCH_THEN(fun hideal2 ->
        ASSUME_TAC hring THEN ASSUME_TAC hideal1 THEN ASSUME_TAC hideal2 THEN
        STRIP_ASSUME_TAC(REWRITE_RULE[cring] hring) THEN
        STRIP_ASSUME_TAC(REWRITE_RULE[IsIdeal] hideal1) THEN
        STRIP_ASSUME_TAC(REWRITE_RULE[IsIdeal] hideal2) THEN
        REWRITE_TAC[IsIdeal; ideal_sum] THEN
        REPEAT CONJ_TAC THENL
         [EXISTS_TAC `zeroR:'r` THEN EXISTS_TAC `zeroR:'r` THEN
          ASM_REWRITE_TAC[];
          REPEAT GEN_TAC THEN
          DISCH_THEN(CONJUNCTS_THEN2
            (X_CHOOSE_THEN `a1:'r`
              (X_CHOOSE_THEN `b1:'r`
                (CONJUNCTS_THEN2 ASSUME_TAC
                  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))))
            (X_CHOOSE_THEN `a2:'r`
              (X_CHOOSE_THEN `b2:'r`
                (CONJUNCTS_THEN2 ASSUME_TAC
                  (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))))) THEN
          EXISTS_TAC `(add:'r->'r->'r) (a1:'r) (a2:'r)` THEN
          EXISTS_TAC `(add:'r->'r->'r) (b1:'r) (b2:'r)` THEN
          REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC[];
            ASM_MESON_TAC[];
            MATCH_ACCEPT_TAC
              (SPECL [`a1:'r`; `b1:'r`; `a2:'r`; `b2:'r`]
                (MATCH_MP
                  (SPECL
                    [`zeroR:'r`;
                     `oneR:'r`;
                     `add:'r->'r->'r`;
                     `mul:'r->'r->'r`;
                     `opp:'r->'r`]
                    add_rearrange)
                  hring))];
          GEN_TAC THEN
          DISCH_THEN(X_CHOOSE_THEN `a1:'r`
            (X_CHOOSE_THEN `b1:'r`
              (CONJUNCTS_THEN2 ASSUME_TAC
                (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
          EXISTS_TAC `(opp:'r->'r) (a1:'r)` THEN
          EXISTS_TAC `(opp:'r->'r) (b1:'r)` THEN
          REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC[];
            ASM_MESON_TAC[];
            ASM_REWRITE_TAC[]];
          REPEAT GEN_TAC THEN
          DISCH_THEN(X_CHOOSE_THEN `a1:'r`
            (X_CHOOSE_THEN `b1:'r`
              (CONJUNCTS_THEN2 ASSUME_TAC
                (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
          EXISTS_TAC `(mul:'r->'r->'r) (a:'r) (a1:'r)` THEN
          EXISTS_TAC `(mul:'r->'r->'r) (a:'r) (b1:'r)` THEN
          REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC[];
            ASM_MESON_TAC[];
            ASM_REWRITE_TAC[]]]))));;
