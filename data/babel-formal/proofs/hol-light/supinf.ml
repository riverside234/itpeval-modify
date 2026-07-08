let is_supinf_context = new_definition
  `is_supinf_context (zero_nat:N) (Succ:N->N)
		                     (NatAltle:N->N->bool)
		                     (zero:R) (oneR:R) (add:R->R->R) (mul:R->R->R)
		                     (opp:R->R) (invR:R->R)
		                     (Rle:R->R->bool) (Rlt:R->R->bool) (Rabs:R->R)
		                     (ofNat:N->R) <=>
	     (!n. NatAltle n n) /\
	     (!n m. NatAltle n m ==> NatAltle n (Succ m)) /\
	     (!n. NatAltle n (Succ n)) /\
	     (!x y. add x y = add y x) /\
	     (!x y z. add (add x y) z = add x (add y z)) /\
	     (!x. add x zero = x) /\
	     (!x. add (opp x) x = zero) /\
	     (!x y. mul x y = mul y x) /\
	     (!x y z. mul (mul x y) z = mul x (mul y z)) /\
	     (!x. mul x oneR = x) /\
     (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x. add x (opp zero) = x) /\
     (!x. Rle x x) /\
     (!x y z. Rle x y /\ Rle y z ==> Rle x z) /\
     (!x y. Rle x y /\ Rle y x ==> x = y) /\
     (!x y. Rlt x y <=> (Rle x y /\ ~(x = y))) /\
     (!x. Rle (add x (opp zero)) (Rabs x)) /\
     (!x. Rlt zero x ==> Rlt zero (invR x)) /\
     (!x y z. Rle y z ==> Rle (add x y) (add x z)) /\
     (!x. Rlt zero x ==> invR (invR x) = x) /\
	     (!n. Rlt zero (ofNat (Succ n))) /\
	     (!m n. NatAltle m n ==> Rle (ofNat m) (ofNat n)) /\
	     (ofNat zero_nat = zero) /\
	     (!n. ofNat (Succ n) = add (ofNat n) oneR) /\
	     (!x y. Rlt x y \/ x = y \/ Rlt y x) /\
	     (!a b. Rlt zero a /\ Rlt zero b /\ Rle a b ==> Rle (invR b) (invR a)) /\
	     (!x y. Rlt x y ==> ?eps. Rlt zero eps /\ Rlt (add x eps) y) /\
		     (!x. ?n. Rle x (ofNat n)) /\
	     (!A. (?ub. !a. A a ==> Rle ub a) ==>
	          ?sup. (!a. A a ==> Rle a sup) /\
	                (!y. (!a. A a ==> Rle a y) ==> Rle sup y))`;;

let sub = new_definition
  `sub (add:R->R->R) (opp:R->R) x y = add x (opp y)`;;

let up_bounds = new_definition
  `up_bounds (Rle:R->R->bool) (A:R->bool) x <=>
     !a. A a ==> Rle a x`;;

let is_maximum = new_definition
  `is_maximum (Rle:R->R->bool) (A:R->bool) x <=>
     A x /\ up_bounds Rle A x`;;

let low_bounds = new_definition
  `low_bounds (Rle:R->R->bool) (A:R->bool) x <=>
     !a. A a ==> Rle x a`;;

let is_inf = new_definition
  `is_inf (Rle:R->R->bool) (A:R->bool) x <=>
     is_maximum Rle (low_bounds Rle A) x`;;

let limit = new_definition
  `limit (zero:R) (Rlt:R->R->bool) (Rabs:R->R) (Rle:R->R->bool)
         (subf:R->R->R) (NatAltle:N->N->bool) u l <=>
     !eps. Rlt zero eps ==> ?N. !n. NatAltle N n ==> Rle (Rabs (subf (u n) l)) eps`;;

let INTRO_SUPINF_HYPS =
  REWRITE_TAC[is_supinf_context] THEN REPEAT GEN_TAC THEN
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

let supinf_order_core = prove
 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat.
     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
     ==> (!x. Rle x x) /\
         (!x y z. Rle x y /\ Rle y z ==> Rle x z) /\
         (!x y. Rle x y /\ Rle y x ==> x = y) /\
         (!x y. Rlt x y <=> Rle x y /\ ~(x = y)) /\
         (!x y. Rlt x y \/ x = y \/ Rlt y x) /\
         (!x y. Rlt x y ==> ?eps. Rlt zero eps /\ Rlt (add x eps) y)`,
  REWRITE_TAC[is_supinf_context] THEN MESON_TAC[]);;

let inf_lt_core = prove
 (`!Rle Rlt (A:R->bool) x y.
     (!x. Rle x x) /\
     (!x y. Rle x y /\ Rle y x ==> x = y) /\
     (!x y. Rlt x y <=> Rle x y /\ ~(x = y)) /\
     (!x y. Rlt x y \/ x = y \/ Rlt y x)
     ==> is_inf Rle A x ==> Rlt x y ==> ?a. A a /\ Rlt a y`,
  REWRITE_TAC[is_inf; is_maximum; up_bounds; low_bounds] THEN MESON_TAC[]);;

let not_lt_of_le_core = prove
 (`!Rle Rlt (x:A) y.
     (!u v. Rle u v /\ Rle v u ==> u = v) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v))
     ==> Rlt x y ==> ~(Rle y x)`,
  MESON_TAC[]);;

let lt_of_not_le_core = prove
 (`!Rle Rlt (x:A) y.
     (!u. Rle u u) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v)) /\
     (!u v. Rlt u v \/ u = v \/ Rlt v u)
     ==> ~(Rle y x) ==> Rlt x y`,
  MESON_TAC[]);;

let le_of_le_add_eps_core = prove
 (`!zero (add:A->A->A) Rle Rlt x y.
     (!u. Rle u u) /\
     (!u v. Rle u v /\ Rle v u ==> u = v) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v)) /\
     (!u v. Rlt u v \/ u = v \/ Rlt v u) /\
     (!u v. Rlt u v ==> ?eps. Rlt zero eps /\ Rlt (add u eps) v)
     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
     ==> Rle y x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `(Rle:A->A->bool) y x` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Rlt:A->A->bool) x y` ASSUME_TAC THENL
  [ASM_MESON_TAC[lt_of_not_le_core];
   SUBGOAL_THEN `?eps:A. (Rlt:A->A->bool) zero eps /\ Rlt (add x eps) y` MP_TAC THENL
   [ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `eps:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(Rle:A->A->bool) y (add x eps)` ASSUME_TAC THENL
    [ASM_MESON_TAC[];
     ASM_MESON_TAC[not_lt_of_le_core]]]]);;

let le_of_le_add_eps_r_core = prove
 (`!(zero:R) (add:R->R->R) Rle Rlt x y.
     (!u. Rle u u) /\
     (!u v. Rle u v /\ Rle v u ==> u = v) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v)) /\
     (!u v. Rlt u v \/ u = v \/ Rlt v u) /\
     (!u v. Rlt u v ==> ?eps. Rlt zero eps /\ Rlt (add u eps) v)
     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
     ==> Rle y x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `(Rle:R->R->bool) y x` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Rlt:R->R->bool) x y` ASSUME_TAC THENL
  [ASM_MESON_TAC[lt_of_not_le_core];
   SUBGOAL_THEN `?eps:R. (Rlt:R->R->bool) zero eps /\ Rlt (add x eps) y` MP_TAC THENL
   [ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `eps:R` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(Rle:R->R->bool) y (add x eps)` ASSUME_TAC THENL
    [ASM_MESON_TAC[];
     ASM_MESON_TAC[not_lt_of_le_core]]]]);;

let le_of_le_add_eps_r_core_imp = prove
 (`!(zero:R) (add:R->R->R) Rle Rlt x y.
     (!u. Rle u u)
     ==> (!u v. Rle u v /\ Rle v u ==> u = v)
     ==> (!u v. Rlt u v <=> Rle u v /\ ~(u = v))
     ==> (!u v. Rlt u v \/ u = v \/ Rlt v u)
     ==> (!u v. Rlt u v ==> ?eps. Rlt zero eps /\ Rlt (add u eps) v)
     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
     ==> Rle y x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun h_refl ->
  DISCH_THEN(fun h_antisym ->
  DISCH_THEN(fun h_lt ->
  DISCH_THEN(fun h_total ->
  DISCH_THEN(fun h_dense ->
  DISCH_THEN(fun h_bound ->
    ACCEPT_TAC
      (MATCH_MP
        (MATCH_MP
          (SPECL [`zero:R`; `add:R->R->R`; `Rle:R->R->bool`;
                  `Rlt:R->R->bool`; `x:R`; `y:R`]
             le_of_le_add_eps_r_core)
          (CONJ h_refl (CONJ h_antisym (CONJ h_lt (CONJ h_total h_dense)))))
        h_bound))))))));;

let add_sub_cancel_r = prove
 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat a b.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> add a (sub add opp b a) = b`,
  REWRITE_TAC[is_supinf_context; sub] THEN MESON_TAC[]);;

let rabs_pos = prove
	 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat t.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> Rle t (Rabs t)`,
  REWRITE_TAC[is_supinf_context] THEN MESON_TAC[]);;

let unique_max = prove
	 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat (A:R->bool) x y.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> is_maximum Rle A x ==> is_maximum Rle A y ==> x = y`,
  REWRITE_TAC[is_supinf_context; is_maximum; up_bounds] THEN MESON_TAC[]);;

let inf_lt = prove
	 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat (A:R->bool) x y.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> is_inf Rle A x ==> Rlt x y ==> ?a. A a /\ Rlt a y`,
  REWRITE_TAC[is_supinf_context] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL [`Rle:R->R->bool`; `Rlt:R->R->bool`; `A:R->bool`; `x:R`; `y:R`]
       inf_lt_core) THEN
  ASM_REWRITE_TAC[]);;

let le_of_le_add_eps = prove
	 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat x y.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
	     ==> Rle y x`,
  REWRITE_TAC[is_supinf_context] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC le_of_le_add_eps_core THEN
  ASM_REWRITE_TAC[]);;

let le_lim_eps_core = prove
 (`!(zero:R) (add:R->R->R) Rle Rlt Rabs subf NatAltle (u:N->R) x y eps.
     (!n. NatAltle n n) /\
     (!a b c. Rle a b /\ Rle b c ==> Rle a c) /\
     (!a b c. Rle b c ==> Rle (add a b) (add a c)) /\
     (!t. Rle t (Rabs t)) /\
     (!a b. add a (subf b a) = b) /\
     (!eps. Rlt zero eps ==> ?N. !n. NatAltle N n ==> Rle (Rabs (subf (u n) x)) eps) /\
     (!n. Rle y (u n)) /\
     Rlt zero eps
     ==> Rle y (add x eps)`,
  MESON_TAC[]);;

let le_lim_eps_core_imp = prove
 (`!(zero:R) (add:R->R->R) Rle Rlt Rabs subf NatAltle (u:N->R) x y eps.
     (!n. NatAltle n n)
     ==> (!a b c. Rle a b /\ Rle b c ==> Rle a c)
     ==> (!a b c. Rle b c ==> Rle (add a b) (add a c))
     ==> (!t. Rle t (Rabs t))
     ==> (!a b. add a (subf b a) = b)
     ==> (!eps. Rlt zero eps ==> ?N. !n. NatAltle N n ==> Rle (Rabs (subf (u n) x)) eps)
     ==> (!n. Rle y (u n))
     ==> Rlt zero eps
     ==> Rle y (add x eps)`,
  MESON_TAC[le_lim_eps_core]);;

let le_lim_core = prove
 (`!(zero:R) (add:R->R->R) Rle Rlt Rabs subf NatAltle (u:N->R) x y.
     (!n. NatAltle n n) /\
     (!a. Rle a a) /\
     (!a b c. Rle a b /\ Rle b c ==> Rle a c) /\
     (!a b. Rle a b /\ Rle b a ==> a = b) /\
     (!a b. Rlt a b <=> Rle a b /\ ~(a = b)) /\
     (!a b. Rlt a b \/ a = b \/ Rlt b a) /\
     (!a b c. Rle b c ==> Rle (add a b) (add a c)) /\
     (!a b. Rlt a b ==> ?eps. Rlt zero eps /\ Rlt (add a eps) b) /\
     (!t. Rle t (Rabs t)) /\
     (!a b. add a (subf b a) = b)
     ==> limit zero Rlt Rabs Rle subf NatAltle u x
     ==> (!n. Rle y (u n))
     ==> Rle y x`,
  REWRITE_TAC[limit] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun hctx ->
  DISCH_THEN(fun hlim ->
  DISCH_THEN(fun hbound ->
    let [h_nrefl; h_refl; h_trans; h_antisym; h_lt; h_total;
         h_add_mono; h_dense; h_abs; h_sub] = CONJUNCTS hctx in
    let h_eps =
      GEN `eps:R`
        (DISCH `(Rlt:R->R->bool) zero eps`
          (MATCH_MP
            (MATCH_MP
              (MATCH_MP
                (MATCH_MP
                  (MATCH_MP
                    (MATCH_MP
                      (MATCH_MP
                        (MATCH_MP
                          (SPECL [`zero:R`; `add:R->R->R`; `Rle:R->R->bool`;
                                  `Rlt:R->R->bool`; `Rabs:R->R`;
                                  `subf:R->R->R`; `NatAltle:N->N->bool`;
                                  `u:N->R`; `x:R`; `y:R`; `eps:R`]
                             le_lim_eps_core_imp)
                          h_nrefl)
                        h_trans)
                      h_add_mono)
                    h_abs)
                  h_sub)
                hlim)
              hbound)
            (ASSUME `(Rlt:R->R->bool) zero eps`))) in
    ACCEPT_TAC
      (MATCH_MP
        (MATCH_MP
          (MATCH_MP
            (MATCH_MP
              (MATCH_MP
                (MATCH_MP
                  (SPECL [`zero:R`; `add:R->R->R`; `Rle:R->R->bool`;
                          `Rlt:R->R->bool`; `x:R`; `y:R`]
                     le_of_le_add_eps_r_core_imp)
                  h_refl)
                h_antisym)
              h_lt)
            h_total)
          h_dense)
        h_eps)))));;

let le_lim = prove
	 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat (u:N->R) x y.
		     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
		     ==> limit zero Rlt Rabs Rle (sub add opp) NatAltle u x
		     ==> (!n. Rle y (u n))
		     ==> Rle y x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun hctx ->
  DISCH_THEN(fun hlim ->
  DISCH_THEN(fun hbound ->
    let [h_nrefl; _; _; _; _; _; _; _; _; _; _; h_add_opp_zero;
         h_refl; h_trans; h_antisym; h_lt; h_abs0; _; h_add_mono; _;
         _; _; _; _; h_total; _; h_dense; _; _] =
      CONJUNCTS (REWRITE_RULE[is_supinf_context] hctx) in
    let h_abs =
      GEN `t:R`
        (REWRITE_RULE [SPEC `t:R` h_add_opp_zero] (SPEC `t:R` h_abs0)) in
    let h_sub =
      GEN `a:R`
        (GEN `b:R`
          (MATCH_MP
            (SPEC_ALL add_sub_cancel_r)
            hctx)) in
    let h_core_ctx =
      CONJ h_nrefl
        (CONJ h_refl
          (CONJ h_trans
            (CONJ h_antisym
              (CONJ h_lt
                (CONJ h_total
                  (CONJ h_add_mono
                    (CONJ h_dense
                      (CONJ h_abs h_sub)))))))) in
    ACCEPT_TAC
      (MATCH_MP
        (MATCH_MP
          (MATCH_MP
            (SPECL [`zero:R`; `add:R->R->R`; `Rle:R->R->bool`;
                    `Rlt:R->R->bool`; `Rabs:R->R`; `(sub add opp):R->R->R`;
                    `NatAltle:N->N->bool`; `u:N->R`; `x:R`; `y:R`]
               le_lim_core)
            h_core_ctx)
          hlim)
        hbound)))));;

let inv_succ_pos = prove
	 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat n.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> Rlt zero (invR (ofNat (Succ n)))`,
  REWRITE_TAC[is_supinf_context] THEN MESON_TAC[]);;

let limit_inv_succ = prove
	 (`!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat eps.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> Rlt zero eps
	     ==> ?N. !n. NatAltle N n ==> Rle (invR (ofNat (Succ n))) eps`,
  REWRITE_TAC[is_supinf_context] THEN MESON_TAC[]);;
