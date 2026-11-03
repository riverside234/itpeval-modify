(* ========================================================================= *)
(* Conversion to prenex form.                                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Quantifier-free formulas.                                                 *)
(* ------------------------------------------------------------------------- *)

let qfree = new_recursive_definition form_RECURSION
  `(qfree False <=> T) /\
   (qfree (Atom n l) <=> T) /\
   (qfree (p --> q) <=> qfree p /\ qfree q) /\
   (qfree (!!x p) <=> F)`;;

let QFREE = `(qfree False <=> T) /\
   (qfree True <=> T) /\
   (!a l. qfree (Atom a l) <=> T) /\
   (!p. qfree (Not p) <=> qfree p) /\
   (!p q. qfree (p || q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p && q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p --> q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p <-> q) <=> qfree p /\ qfree q) /\
   (!x p. qfree (!! x p) <=> F) /\
   (!x p. qfree (?? x p) <=> F)`;;

let QFREE_FORMSUBST = `!p v. qfree (formsubst v p) <=> qfree p`;;

let QFREE_BV_EMPTY = `!p. qfree(p) <=> (BV(p) = EMPTY)`;;

(* ------------------------------------------------------------------------- *)
(* Prenex and prenex universal formulas.                                     *)
(* ------------------------------------------------------------------------- *)

let prenex_RULES,prenex_INDUCT,prenex_CASES = new_inductive_definition
  `(!p. qfree p ==> prenex p) /\
   (!x p. prenex p ==> prenex (!!x p)) /\
   (!x p. prenex p ==> prenex (??x p))`;;

let universal_RULES,universal_INDUCT,universal_CASES =
  new_inductive_definition
  `(!p. qfree p ==> universal p) /\
   (!x p. universal p ==> universal (!!x p))`;;

let prenex_INDUCT_NOT = `!P. (!p. qfree p ==> P p) /\
       (!x p. P p ==> P (!! x p)) /\
       (!x p. P p ==> P (Not p))
       ==> !a. prenex a ==> P a`;;

let PRENEX = `(prenex False <=> T) /\
   (prenex True <=> T) /\
   (!a l. prenex (Atom a l) <=> T) /\
   (!p. prenex (Not p) <=> qfree p \/ (?q x. (Not p = ??x q) /\ prenex q)) /\
   (!p q. prenex (p || q) <=> qfree p /\ qfree q) /\
   (!p q. prenex (p && q) <=> qfree p /\ qfree q) /\
   (!p q. prenex (p --> q) <=> qfree p /\ qfree q \/
                             (?r x. (p --> q = ??x r) /\ prenex r)) /\
   (!p q. prenex (p <-> q) <=> qfree p /\ qfree q) /\
   (!x p. prenex (!! x p) <=> prenex p) /\
   (!x p. prenex (?? x p) <=> prenex p)`;;

let FORMSUBST_STRUCTURE_LEMMA = `!p i. ((formsubst i p = False) <=> (p = False)) /\
         ((?a l. formsubst i p = Atom a l) <=> (?a l. p = Atom a l)) /\
         ((?q r. formsubst i p = q --> r) <=> (?q r. p = q --> r)) /\
         ((?x q. formsubst i p = !!x q) <=> (?x q. p = !!x q))`;;

let FORMSUBST_STRUCTURE_NOT = `!p i. (?q. formsubst i p = Not q) <=> (?q. p = Not q)`;;

let FORMSUBST_STRUCTURE_EXISTS = `!p i. (?x q. formsubst i p = ??x q) <=> (?x q. p = ??x q)`;;

let PRENEX_FORMSUBST_LEMMA = `!p. prenex p ==> !i q. (p = formsubst i q) ==> prenex q`;;

let PRENEX_FORMSUBST = `!p i. prenex(formsubst i p) = prenex p`;;

(* ------------------------------------------------------------------------- *)
(* It's more convenient to argue by non-structural induction here.           *)
(* ------------------------------------------------------------------------- *)

let size = new_recursive_definition form_RECURSION
  `(size False = 1) /\
   (size (Atom p l) = 1) /\
   (size (q --> r) = size q + size r) /\
   (size (!!x q) = 1 + size q)`;;

let SIZE = `(size False = 1) /\
   (size True = 2) /\
   (!a l. size (Atom a l) = 1) /\
   (!p. size (Not p) = 1 + size p) /\
   (!p q. size (p || q) = size p + 2 * size q) /\
   (!p q. size (p && q) = size p + 2 * size q + 4) /\
   (!p q. size (p --> q) = size p + size q) /\
   (!p q. size (p <-> q) = 3 * size p + 3 * size q + 4) /\
   (!x p.size (!! x p) = 1 + size p) /\
   (!x p. size (?? x p) = 3 + size p)`;;

let SIZE_FORMSUBST = `!p i. size (formsubst i p) = size p`;;

(* ------------------------------------------------------------------------- *)
(* Constructive prenexing procedure.                                         *)
(* ------------------------------------------------------------------------- *)

let PPAT_DEF = new_definition
  `PPAT A B C r =
     if ?x p. r = !!x p then
                    A (@x. ?p. r = !!x p)
                      (@p. r = !!(@x. ?p. r = !!x p) p)
                  else if ?x p. r = ??x p then
                    B (@x. ?p. r = ??x p)
                      (@p. r = ??(@x. ?p. r = ??x p) p)
                  else C r`;;

let PRENEX_DISTINCT = `!x y p q. ((!!x p = !!y q) <=> (x = y) /\ (p = q)) /\
             ((??x p = ??y q) <=> (x = y) /\ (p = q)) /\
             ~(!!x p = ??y q)`;;

let PPAT = `!A B C. (!x p. PPAT A B C (!!x p) = A x p :A) /\
           (!x p. PPAT A B C (??x p) = B x p) /\
           !r. ~(?x p. r = !!x p) /\ ~(?x p. r = ??x p)
               ==> (PPAT A B C  r = C r)`;;

let SIZE_REC = `!H. (!f g x. (!z. size z < size x ==> (f z = g z)) ==> (H f x = H g x))
       ==> (?f. !x. f x = H f x)`;;

let PRENEX_RIGHT_EXISTENCE = `?Prenex_right.
        (!p x q. Prenex_right p (!!x q) =
                   let y = VARIANT(FV(p) UNION FV(!!x q)) in
                   !!y (Prenex_right p (formsubst (valmod (x,V y) V) q))) /\
        (!p x q. Prenex_right p (??x q) =
                   let y = VARIANT(FV(p) UNION FV(??x q)) in
                   ??y (Prenex_right p (formsubst (valmod (x,V y) V) q))) /\
        (!p q. qfree q ==> (Prenex_right p q = p --> q))`;;

let PRENEX_RIGHT = new_specification ["Prenex_right"] PRENEX_RIGHT_EXISTENCE;;

let PRENEX_LEFT_EXISTENCE = `?Prenex_left.
        (!p x q. Prenex_left (!!x q) p =
                   let y = VARIANT(FV(!!x q) UNION FV(p)) in
                   ??y (Prenex_left (formsubst (valmod (x,V y) V) q) p)) /\
        (!p x q. Prenex_left (??x q) p =
                   let y = VARIANT(FV(??x q) UNION FV(p)) in
                   !!y (Prenex_left (formsubst (valmod (x,V y) V) q) p)) /\
        (!p q. qfree q ==> (Prenex_left q p = Prenex_right q p))`;;

let PRENEX_LEFT = new_specification ["Prenex_left"] PRENEX_LEFT_EXISTENCE;;

let Prenex_DEF = new_recursive_definition form_RECURSION
  `(Prenex False = False) /\
   (Prenex (Atom a l) = Atom a l) /\
   (Prenex (p --> q) = Prenex_left (Prenex p) (Prenex q)) /\
   (Prenex (!!x p) = !!x (Prenex p))`;;

(* ------------------------------------------------------------------------- *)
(* Proof that it does indeed prenex.                                         *)
(* ------------------------------------------------------------------------- *)

let PRENEX_RIGHT_FORALL = `~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> !!x q) <=>
        holds M v (!! (VARIANT (FV(p) UNION FV(!!x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q)))`;;

let PRENEX_RIGHT_EXISTS = `~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> ??x q) <=>
        holds M v (?? (VARIANT (FV(p) UNION FV(??x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q)))`;;

let PRENEX_DUALITY_LEMMAS = `(holds M v (??x p --> q) <=> holds M v (Not q --> !!x (Not p))) /\
   (holds M v (!!x p --> q) <=> holds M v (Not q --> ??x (Not p)))`;;

let PRENEX_LEFT_FORALL = `~(Dom M :A->bool = EMPTY)
   ==> (holds M v (!!x p --> q) <=>
        holds M v (?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q)))`;;

let PRENEX_LEFT_EXISTS = `~(Dom M :A->bool = EMPTY)
   ==> (holds M v (??x p --> q) <=>
        holds M v (!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q)))`;;

(* ------------------------------------------------------------------------- *)
(* Extras about free variables.                                              *)
(* ------------------------------------------------------------------------- *)

let PRENEX_RIGHT_FORALL_FV = `FV(p --> !!x q) = FV(!! (VARIANT (FV(p) UNION FV(!!x q)))
                           (p --> formsubst (valmod
                              (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q))`;;

let PRENEX_RIGHT_EXISTS_FV = `FV(p --> ??x q) =
   FV(?? (VARIANT (FV(p) UNION FV(??x q)))
           (p --> formsubst (valmod
                   (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q))`;;

let PRENEX_LEFT_FORALL_FV = `FV(!!x p --> q) =
   FV(?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q))`;;

let PRENEX_LEFT_EXISTS_FV = `FV(??x p --> q) =
   FV(!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q))`;;

(* ------------------------------------------------------------------------- *)
(* And extras about the language.                                            *)
(* ------------------------------------------------------------------------- *)

let PRENEX_RIGHT_FORALL_LANGUAGE = `language {(p --> !!x q)} = language {(!! (VARIANT (FV(p) UNION FV(!!x q)))
                           (p --> formsubst (valmod
                              (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q))}`;;

let PRENEX_RIGHT_EXISTS_LANGUAGE = `language {(p --> ??x q)} =
   language {(?? (VARIANT (FV(p) UNION FV(??x q)))
           (p --> formsubst (valmod
                   (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q))}`;;

let PRENEX_LEFT_FORALL_LANGUAGE = `language {(!!x p --> q)} =
   language {(?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q))}`;;

let PRENEX_LEFT_EXISTS_LANGUAGE = `language {(??x p --> q)} =
   language {(!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q))}`;;

(* ------------------------------------------------------------------------- *)
(* Proofs that things work properly.                                         *)
(* ------------------------------------------------------------------------- *)

let PRENEX_LEMMA_FORALL = `P /\
   (FV r1 = FV r2) /\
   (language {r1} = language {r2}) /\
   (!M v. ~(Dom M :A->bool = EMPTY) ==> (holds M v p <=> holds M v q))
   ==> P /\
       (FV(!!z r1) = FV(!!z r2)) /\
       (language {(!!z r1)} = language {(!!z r2)}) /\
       !M v. ~(Dom M :A->bool = EMPTY)
               ==> (holds M v (!!x p) <=> holds M v (!!x q))`;;

let PRENEX_LEMMA_EXISTS = `P /\
   (FV r1 = FV r2) /\
   (language {r1} = language {r2}) /\
   (!M v. ~(Dom M :A->bool = EMPTY) ==> (holds M v p <=> holds M v q))
   ==> P /\
       (FV(??z r1) = FV(??z r2)) /\
       (language {(??z r1)} = language {(??z r2)}) /\
       !M v. ~(Dom M :A->bool = EMPTY)
               ==> (holds M v (??x p) <=> holds M v (??x q))`;;

let PRENEX_RIGHT_THM = `!p q. qfree p /\ prenex q
         ==> prenex (Prenex_right p q) /\
             (FV(Prenex_right p q) = FV(p --> q)) /\
             (language {(Prenex_right p q)} = language {(p --> q)}) /\
             (!M v. ~(Dom M :A->bool = EMPTY)
                    ==> (holds M v (Prenex_right p q) <=>
                         holds M v (p --> q)))`;;

let PRENEX_LEFT_THM = `!p q. prenex p /\ prenex q
         ==> prenex (Prenex_left p q) /\
             (FV(Prenex_left p q) = FV(p --> q)) /\
             (language {(Prenex_left p q)} = language {(p --> q)}) /\
             (!M v. ~(Dom M :A->bool = EMPTY)
                    ==> (holds M v (Prenex_left p q) <=> holds M v (p --> q)))`;;

let PRENEX_THM = `!p. prenex(Prenex p) /\
       (FV(Prenex p) = FV(p)) /\
       (language {(Prenex p)} = language {p}) /\
       !M v. ~(Dom M = EMPTY)
             ==> (holds M (v:num->A) (Prenex p) <=> holds M v p)`;;
