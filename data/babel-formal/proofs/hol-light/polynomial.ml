let mynat_INDUCT,mynat_RECURSION = define_type
 "mynat = Nat_O | Nat_S mynat";;

let mynat_add = new_recursive_definition mynat_RECURSION
 `(mynat_add Nat_O m = m) /\
  (mynat_add (Nat_S n) m = Nat_S (mynat_add n m))`;;

let mynat_add_O_left = prove
 (`!m. mynat_add Nat_O m = m`,
  REWRITE_TAC[mynat_add]);;

let mynat_add_S_left = prove
 (`!n m. mynat_add (Nat_S n) m = Nat_S (mynat_add n m)`,
  REWRITE_TAC[mynat_add]);;

let mynat_le_RULES,mynat_le_INDUCT,mynat_le_CASES = new_inductive_definition
 `(!n. mynat_le n n) /\
  (!n m. mynat_le n m ==> mynat_le n (Nat_S m))`;;

let mynat_zero_le = prove
 (`!n. mynat_le Nat_O n`,
  MATCH_MP_TAC (BETA_RULE (SPEC `\(n:mynat). mynat_le Nat_O n` mynat_INDUCT)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mynat_le_RULES];
    ASM_MESON_TAC[mynat_le_RULES]]);;

let mynat_add_zero_r = prove
 (`!n. mynat_add n Nat_O = n`,
  MATCH_MP_TAC
   (BETA_RULE (SPEC `\(n:mynat). mynat_add n Nat_O = n` mynat_INDUCT)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mynat_add];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mynat_add]]);;

let mynat_succ_le_succ = prove
 (`!n m. mynat_le n m ==> mynat_le (Nat_S n) (Nat_S m)`,
  MATCH_MP_TAC
   (BETA_RULE
     (SPEC `\(n:mynat) (m:mynat). mynat_le (Nat_S n) (Nat_S m)`
           mynat_le_INDUCT)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mynat_le_RULES];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[mynat_le_RULES]]);;

let mynat_add_S_r = prove
 (`!m n. mynat_add m (Nat_S n) = Nat_S (mynat_add m n)`,
  MATCH_MP_TAC
   (BETA_RULE
     (SPEC `\(m:mynat). !n. mynat_add m (Nat_S n) = Nat_S (mynat_add m n)`
           mynat_INDUCT)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mynat_add];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mynat_add]]);;

let mynat_add_comm = prove
 (`!n m. mynat_add n m = mynat_add m n`,
  MATCH_MP_TAC
   (BETA_RULE
     (SPEC `\(n:mynat). !m. mynat_add n m = mynat_add m n`
           mynat_INDUCT)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mynat_add; mynat_add_zero_r];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mynat_add; mynat_add_S_r]]);;

let mynat_le_add_left = prove
 (`!n m. mynat_le n (mynat_add m n)`,
  GEN_TAC THEN
  MATCH_MP_TAC
   (BETA_RULE
     (SPEC `\(m:mynat). mynat_le n (mynat_add m n)` mynat_INDUCT)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mynat_add; mynat_le_RULES];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mynat_add] THEN
    ASM_MESON_TAC[mynat_le_RULES]]);;

let mylist_INDUCT,mylist_RECURSION = define_type
 "mylist = NilL | ConsL A mylist";;

let InL_RULES,InL_INDUCT,InL_CASES = new_inductive_definition
 `(!x xs. InL x (ConsL x xs)) /\
  (!x y xs. InL x xs ==> InL x (ConsL y xs))`;;

let NoDupL_RULES,NoDupL_INDUCT,NoDupL_CASES = new_inductive_definition
 `NoDupL NilL /\
  (!x xs. ~(InL x xs) /\ NoDupL xs ==> NoDupL (ConsL x xs))`;;

let InL_cons_intro = prove
 (`!x y (xs:A mylist). InL x xs ==> InL x (ConsL y xs)`,
  MESON_TAC[InL_RULES]);;

let NoDupL_cons_tail = prove
 (`!x (xs:A mylist). NoDupL (ConsL x xs) ==> NoDupL xs`,
  MESON_TAC[NoDupL_CASES; distinctness "mylist"; injectivity "mylist"]);;

let NoDupL_cons_notin = prove
 (`!x (xs:A mylist). NoDupL (ConsL x xs) ==> ~(InL x xs)`,
  MESON_TAC[NoDupL_CASES; distinctness "mylist"; injectivity "mylist"]);;

let lengthL = new_recursive_definition mylist_RECURSION
 `(lengthL NilL = Nat_O) /\
  (lengthL (ConsL x xs) = Nat_S (lengthL xs))`;;

let X = new_definition
 `X (monomial:mynat->R->P) (oneR:R) = monomial (Nat_S Nat_O) oneR`;;

let C = new_definition
 `C (monomial:mynat->R->P) (c:R) = monomial Nat_O c`;;

let x_minus_def = new_definition
 `X_minus (monomial:mynat->R->P) (addP:P->P->P) (oppR:R->R)
          (oneR:R) (a:R) =
    addP (X monomial oneR) (C monomial (oppR a))`;;

let is_root = new_definition
 `is_root (eval:P->R->R) (zeroR:R) (a:R) (p:P) <=> eval p a = zeroR`;;

let poly_of_roots = new_recursive_definition mylist_RECURSION
 `(poly_of_roots (monomial:mynat->R->P) (addP:P->P->P) (oppR:R->R)
                 (oneR:R) (mulP:P->P->P) (oneP:P) NilL = oneP) /\
  (poly_of_roots monomial addP oppR oneR mulP oneP (ConsL a xs) =
     mulP (X_minus monomial addP oppR oneR a)
          (poly_of_roots monomial addP oppR oneR mulP oneP xs))`;;

let is_ring = new_definition
 `is_ring (zr:A) (un:A) (add:A->A->A) (mul:A->A->A) (opp:A->A) <=>
    ~(un = zr) /\
    (!x y. add x y = add y x) /\
    (!x y z. add (add x y) z = add x (add y z)) /\
    (!x. add x zr = x) /\
    (!x. add x (opp x) = zr) /\
    (!x y. mul x y = mul y x) /\
    (!x y z. mul (mul x y) z = mul x (mul y z)) /\
    (!x. mul x un = x) /\
    (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
    (!x. mul x zr = zr) /\
    (!x y. mul x y = zr ==> x = zr \/ y = zr)`;;

let is_poly_context = new_definition
 `is_poly_context
      (zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R) (oppR:R->R)
      (zeroP:P) (oneP:P) (addP:P->P->P) (mulP:P->P->P) (oppP:P->P)
      (degree:P->mynat) (monomial:mynat->R->P) (eval:P->R->R) <=>
    is_ring zeroR oneR addR mulR oppR /\
    is_ring zeroP oneP addP mulP oppP /\
    C monomial zeroR = zeroP /\
    C monomial oneR = oneP /\
    degree zeroP = Nat_O /\
    (!p q x. eval (addP p q) x = addR (eval p x) (eval q x)) /\
    (!p q x. eval (mulP p q) x = mulR (eval p x) (eval q x)) /\
    (!c x. eval (C monomial c) x = c) /\
    (!x. eval (X monomial oneR) x = x) /\
    (!c. ~(c = zeroR) ==> degree (C monomial c) = Nat_O) /\
    (!p. degree p = Nat_O <=> ?c. p = C monomial c) /\
    (!a. degree (X_minus monomial addP oppR oneR a) = Nat_S Nat_O) /\
    (!p q. ~(p = zeroP) /\ ~(q = zeroP)
           ==> degree (mulP p q) = mynat_add (degree p) (degree q)) /\
    (!p a. ?q r. p = addP (mulP q (X_minus monomial addP oppR oneR a)) r /\
                  degree r = Nat_O)`;;

let ring_add_comm = prove
 (`!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> add x y = add y x`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_add_assoc = prove
 (`!zr un add mul opp (x:A) y z.
     is_ring zr un add mul opp ==> add (add x y) z = add x (add y z)`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_add_zero = prove
 (`!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add x zr = x`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_add_opp = prove
 (`!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add x (opp x) = zr`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let poly_context_poly_ring = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_ring zeroP oneP addP mulP oppP`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_oneP_nonzero = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(oneP = zeroP)`,
  REWRITE_TAC[is_poly_context; is_ring] THEN MESON_TAC[]);;

let poly_context_oneP_degree = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree oneP = Nat_O`,
  REWRITE_TAC[is_poly_context; is_ring; C] THEN MESON_TAC[]);;

let poly_context_zeroP_degree = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree zeroP = Nat_O`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_x_minus_degree = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree (X_minus monomial addP oppR oneR a) = Nat_S Nat_O`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_mul_degree = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(p = zeroP) /\ ~(q = zeroP)
     ==> degree (mulP p q) = mynat_add (degree p) (degree q)`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let ring_mul_comm = prove
 (`!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> mul x y = mul y x`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_mul_assoc = prove
 (`!zr un add mul opp (x:A) y z.
     is_ring zr un add mul opp ==> mul (mul x y) z = mul x (mul y z)`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_mul_reassoc_comm = prove
 (`!zr un add mul opp (x:A) y z.
     is_ring zr un add mul opp ==> mul (mul x y) z = mul x (mul z y)`,
  MESON_TAC[ring_mul_assoc; ring_mul_comm]);;

let ring_mul_one = prove
 (`!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> mul x un = x`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_mul_zero = prove
 (`!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> mul x zr = zr`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_no_zero_div = prove
 (`!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> mul x y = zr ==> x = zr \/ y = zr`,
  REWRITE_TAC[is_ring] THEN MESON_TAC[]);;

let ring_mul_zero_left = prove
 (`!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> mul zr x = zr`,
  MESON_TAC[ring_mul_comm; ring_mul_zero]);;

let sub_eq_zero_l = prove
 (`!zeroR oneR addR mulR oppR (a:R) b.
     is_ring zeroR oneR addR mulR oppR
     ==> addR a (oppR b) = zeroR ==> a = b`,
  MESON_TAC[ring_add_comm; ring_add_assoc; ring_add_zero; ring_add_opp]);;

let eval_x_minus_self = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (X_minus monomial addP oppR oneR a) a = zeroR`,
  REWRITE_TAC[is_poly_context; X; C; x_minus_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[ring_add_opp]);;

let eval_x_minus = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R) b.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (X_minus monomial addP oppR oneR a) b = addR b (oppR a)`,
  REWRITE_TAC[is_poly_context; X; C; x_minus_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let poly_context_division = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ?q r. p = addP (mulP q (X_minus monomial addP oppR oneR a)) r /\
               degree r = Nat_O`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_C_zero = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> C monomial zeroR = zeroP`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_eval_C = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (c:R) x.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (C monomial c) x = c`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_degree_zero = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> (degree p = Nat_O <=> ?c. p = C monomial c)`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_base_ring = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_ring zeroR oneR addR mulR oppR`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_eval_add = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q x.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (addP p q) x = addR (eval p x) (eval q x)`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let poly_context_eval_mul = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q x.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (mulP p q) x = mulR (eval p x) (eval q x)`,
  REWRITE_TAC[is_poly_context] THEN MESON_TAC[]);;

let ring_add_zero_left = prove
 (`!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add zr x = x`,
  MESON_TAC[ring_add_comm; ring_add_zero]);;

let ring_add_zero_left_eq = prove
 (`!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add zr x = zr ==> x = zr`,
  MESON_TAC[ring_add_zero_left]);;

let poly_context_add_zero = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (x:P).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> addP x zeroP = x`,
  MESON_TAC[poly_context_poly_ring; ring_add_zero]);;

let ring_add_mul_zero_cancel = prove
 (`!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> add (mul x zr) y = zr ==> y = zr`,
  MESON_TAC[ring_mul_zero; ring_add_zero_left_eq]);;

let constant_root_zero_lemma = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree p = Nat_O ==> is_root eval zeroR a p ==> p = zeroP`,
  MESON_TAC[poly_context_degree_zero; poly_context_eval_C;
            poly_context_C_zero; is_root]);;

let root_factor_remainder_root = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q r (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
	     ==> p = addP (mulP q (X_minus monomial addP oppR oneR a)) r
	     ==> is_root eval zeroR a p
	     ==> is_root eval zeroR a r`,
  REWRITE_TAC[is_root] THEN
  MESON_TAC[poly_context_eval_add; poly_context_eval_mul; eval_x_minus_self;
            poly_context_base_ring; ring_add_mul_zero_cancel]);;

let root_factor_remainder_zero = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q r (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> p = addP (mulP q (X_minus monomial addP oppR oneR a)) r
     ==> degree r = Nat_O
     ==> is_root eval zeroR a p
     ==> r = zeroP`,
  MESON_TAC[root_factor_remainder_root; constant_root_zero_lemma]);;

let root_factor = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_root eval zeroR a p
     ==> ?q. p = mulP q (X_minus monomial addP oppR oneR a)`,
  MESON_TAC[poly_context_division; root_factor_remainder_zero;
            poly_context_add_zero]);;

let root_transfer = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q (a:R) b.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> p = mulP q (X_minus monomial addP oppR oneR a)
     ==> ~(b = a)
     ==> is_root eval zeroR b p
     ==> is_root eval zeroR b q`,
  REWRITE_TAC[is_root] THEN
  MESON_TAC[poly_context_eval_mul; eval_x_minus; poly_context_base_ring;
            ring_no_zero_div; sub_eq_zero_l]);;

let x_minus_nonzero = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(X_minus monomial addP oppR oneR a = zeroP)`,
  MESON_TAC[poly_context_x_minus_degree; poly_context_zeroP_degree;
            distinctness "mynat"]);;

let constant_root_zero = constant_root_zero_lemma;;

let root_of_product = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_root eval zeroR a (mulP p q)
     ==> is_root eval zeroR a p \/ is_root eval zeroR a q`,
  REWRITE_TAC[is_poly_context; is_ring; is_root] THEN MESON_TAC[]);;

let root_scale_constant = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (c:R) a.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(c = zeroR)
     ==> (is_root eval zeroR a p <=>
          is_root eval zeroR a (mulP (C monomial c) p))`,
  REWRITE_TAC[is_poly_context; is_ring; is_root; C] THEN MESON_TAC[]);;

let poly_of_roots_nonzero = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(poly_of_roots monomial addP oppR oneR mulP oneP xs = zeroP)`,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPEC_TAC(`xs:R mylist`,`xs:R mylist`) THEN
  MATCH_MP_TAC
   (BETA_RULE
     (ISPEC `\(xs:R mylist).
               ~(poly_of_roots monomial addP oppR oneR mulP oneP xs = zeroP)`
           mylist_INDUCT)) THEN
  ASM_REWRITE_TAC[poly_of_roots] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[poly_context_oneP_nonzero];
    ASM_MESON_TAC[poly_context_poly_ring; ring_no_zero_div;
                  x_minus_nonzero]]);;

let poly_context_x_roots_mul_degree = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R) (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
         degree monomial eval
     ==> degree (mulP (X_minus monomial addP oppR oneR a)
                   (poly_of_roots monomial addP oppR oneR mulP oneP xs)) =
         mynat_add (degree (X_minus monomial addP oppR oneR a))
                   (degree (poly_of_roots monomial addP oppR oneR mulP oneP xs))`,
  MESON_TAC[poly_context_mul_degree; x_minus_nonzero;
            poly_of_roots_nonzero]);;

let deg_poly_of_roots = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree (poly_of_roots monomial addP oppR oneR mulP oneP xs) =
         lengthL xs`,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPEC_TAC(`xs:R mylist`,`xs:R mylist`) THEN
  MATCH_MP_TAC
   (BETA_RULE
     (ISPEC `\(xs:R mylist).
               degree (poly_of_roots monomial addP oppR oneR mulP oneP xs) =
               lengthL xs`
           mylist_INDUCT)) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[poly_of_roots; lengthL] THEN
    ASM_MESON_TAC[poly_context_oneP_degree];
    X_GEN_TAC `a:R` THEN
    X_GEN_TAC `xs:R mylist` THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC[poly_of_roots; lengthL] THEN
    ASM_MESON_TAC[poly_context_x_roots_mul_degree;
                  poly_context_x_minus_degree;
                  mynat_add_S_left; mynat_add_O_left] ]);;

let root_factor_list = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> NoDupL xs
     ==> (!a. InL a xs ==> is_root eval zeroR a p)
     ==> ?q. p = mulP q (poly_of_roots monomial addP oppR oneR mulP oneP xs)`,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SPEC_TAC(`p:P`,`p:P`) THEN
  SPEC_TAC(`xs:R mylist`,`xs:R mylist`) THEN
  MATCH_MP_TAC
   (BETA_RULE
     (ISPEC `\(xs:R mylist).
               !p:P.
                 NoDupL xs
                 ==> (!a. InL a xs ==> is_root eval zeroR a p)
                 ==> ?q. p = mulP q
                            (poly_of_roots monomial addP oppR oneR mulP oneP xs)`
           mylist_INDUCT)) THEN
  ASM_REWRITE_TAC[poly_of_roots] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `p:P` THEN
    ASM_MESON_TAC[poly_context_poly_ring; ring_mul_one];
    X_GEN_TAC `a:R` THEN
    X_GEN_TAC `xs:R mylist` THEN
    DISCH_THEN(LABEL_TAC "IH") THEN
    X_GEN_TAC `p:P` THEN
    DISCH_THEN(LABEL_TAC "ND") THEN
    DISCH_THEN(LABEL_TAC "ROOTS") THEN
    MP_TAC
     (ISPECL
       [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
        `oppR:R->R`; `zeroP:P`; `oneP:P`; `addP:P->P->P`;
        `mulP:P->P->P`; `oppP:P->P`; `degree:P->mynat`;
        `monomial:mynat->R->P`; `eval:P->R->R`; `p:P`; `a:R`]
       root_factor) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [USE_THEN "ROOTS" MATCH_MP_TAC THEN REWRITE_TAC[InL_RULES];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `q0:P`) THEN
    USE_THEN "IH" (MP_TAC o SPEC `q0:P`) THEN
    ANTS_TAC THENL
     [USE_THEN "ND" MP_TAC THEN MESON_TAC[NoDupL_cons_tail];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `b:R` THEN DISCH_TAC THEN
      ASM_MESON_TAC[NoDupL_cons_notin; InL_cons_intro; root_transfer];
      DISCH_THEN(X_CHOOSE_TAC `q:P`) THEN
      EXISTS_TAC `q:P` THEN
      ASM_MESON_TAC[poly_context_poly_ring; ring_mul_reassoc_comm]]]);;

let degree_factorisation = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (xs:R mylist) q.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> p = mulP q (poly_of_roots monomial addP oppR oneR mulP oneP xs)
     ==> ~(q = zeroP)
     ==> degree p = mynat_add (degree q) (lengthL xs)`,
  MESON_TAC[poly_context_mul_degree; poly_of_roots_nonzero;
            deg_poly_of_roots]);;

let roots_le_degree = prove
 (`!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> NoDupL xs
     ==> (!a. InL a xs ==> is_root eval zeroR a p)
     ==> ~(p = zeroP)
     ==> mynat_le (lengthL xs) (degree p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
           `oppR:R->R`; `zeroP:P`; `oneP:P`; `addP:P->P->P`;
           `mulP:P->P->P`; `oppP:P->P`; `degree:P->mynat`;
           `monomial:mynat->R->P`; `eval:P->R->R`; `p:P`;
           `xs:R mylist`] root_factor_list) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:P`) THEN
  SUBGOAL_THEN `~(q:P = zeroP)` ASSUME_TAC THENL
   [ASM_MESON_TAC[poly_context_poly_ring; ring_mul_zero_left];
    MP_TAC
     (SPECL [`zeroR:R`; `oneR:R`; `addR:R->R->R`; `mulR:R->R->R`;
             `oppR:R->R`; `zeroP:P`; `oneP:P`; `addP:P->P->P`;
             `mulP:P->P->P`; `oppP:P->P`; `degree:P->mynat`;
             `monomial:mynat->R->P`; `eval:P->R->R`; `p:P`;
             `xs:R mylist`; `q:P`] degree_factorisation) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mynat_le_add_left]]);;
