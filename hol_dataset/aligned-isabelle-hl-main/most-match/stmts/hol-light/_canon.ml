(* ========================================================================= *)
(* Canonical models in FOL and their use to derive classic metatheorems.     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Domain of a canonical model for given language.                           *)
(* ------------------------------------------------------------------------- *)

let terms_RULES,terms_INDUCT,terms_CASES = new_inductive_definition
  `(!x. terms fns (V x)) /\
   (!f l. (f,LENGTH l) IN fns /\ ALL (terms fns) l
          ==> terms fns (Fn f l))`;;

(* ------------------------------------------------------------------------- *)
(* A few obvious lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)

let STUPID_CANONDOM_LEMMA = `!t. t IN terms(FST L) ==> functions_term t SUBSET (FST L)`;;

let FINITE_SUBSET_INSTANCE = `!t'. FINITE(t')
        ==> t' SUBSET { formsubst v p | P(v) /\ p IN s}
            ==> ?t. FINITE(t) /\ t SUBSET s /\
                    t' SUBSET {formsubst v p | P(v) /\ p IN t}`;;

let FINITE_SUBSET_SKOLEM = `!s u. FINITE(u)
        ==> u SUBSET { SKOLEM p | p IN s}
            ==> ?t. FINITE(t) /\ t SUBSET s /\
                    (u = {SKOLEM p | p IN t})`;;

let VALUATION_EXISTS = `!M. ~(Dom(M) = EMPTY) ==> ?v:num->A. valuation(M) v`;;

let HOLDS_ITLIST_EXISTS = `!M xs v. holds M v (ITLIST ?? xs p) <=>
            ?as. (LENGTH as = LENGTH xs) /\
                 ALL (Dom M) as /\
                 holds M
                   (ITLIST valmod (REVERSE (MAP2 (\x a:A. (x,a)) xs as)) v)
                   p`;;

(* ------------------------------------------------------------------------- *)
(* Canonical model based on the language of a set of formulas.               *)
(* ------------------------------------------------------------------------- *)

let canonical = new_definition
  `canonical (L:(num#num->bool)#(num#num->bool)) M <=>
       (Dom M = terms (FST L)) /\
       (!f. Fun(M) f = Fn f)`;;

(* ------------------------------------------------------------------------- *)
(* Mappings between models and propositional valuations.                     *)
(* ------------------------------------------------------------------------- *)

let prop_of_model = new_definition
  `prop_of_model M v (Atom p l) <=> holds M v (Atom p l)`;;

let canon_of_prop = new_definition
  `canon_of_prop (L:((num#num)->bool)#((num#num)->bool)) (d:form->bool) =
   terms(FST L),Fn,\p l. d(Atom p l)`;;

let PHOLDS_PROP_OF_MODEL = `!p. qfree(p) ==> (pholds (prop_of_model M v) p <=> holds M v p)`;;

let PROP_OF_CANON_OF_PROP = `!p l. prop_of_model (canon_of_prop L d) V (Atom p l) = d (Atom p l)`;;

let HOLDS_CANON_OF_PROP = `!p. qfree p ==> (holds (canon_of_prop L d) V p <=> pholds d p)`;;

let HOLDS_CANON_OF_PROP_GENERAL = `qfree p ==> (holds (canon_of_prop L d) v p <=> pholds d (formsubst v p))`;;

let CANONICAL_CANON_OF_PROP = `!d. canonical L (canon_of_prop L d)`;;

let INTERPRETATION_CANON_OF_PROP = `!L d. interpretation L (canon_of_prop L d)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalence theorems for tautologies.                                     *)
(* ------------------------------------------------------------------------- *)

let PROP_VALID_IMP_FOL_VALID = `!p. qfree(p) /\ (!d. pholds d p) ==> !M v. holds M v p`;;

let FOL_VALID_IMP_PROP_VALID = `!p. qfree(p) /\
       (!C (v:num->term). canonical(language {p}) C ==> holds C v p)
       ==> !d. pholds d p`;;

(* ------------------------------------------------------------------------- *)
(* Same thing for satisfiability.                                            *)
(* ------------------------------------------------------------------------- *)

let SATISFIES_PSATISFIES = `(!p. p IN s ==> qfree p) /\ M satisfies s /\ valuation(M) v
   ==> (prop_of_model M v) psatisfies s`;;

let PSATISFIES_INSTANCES = `(!p. p IN s ==> qfree p) /\
   d psatisfies {formsubst v p | (!x. v x IN terms(FST L)) /\ p IN s}
   ==> (canon_of_prop L d) satisfies s`;;

let SATISFIES_INSTANCES = `!M:(A->bool)#(num->A list->A)#(num->A list->bool) s t.
        interpretation(language t) M
        ==> (M satisfies
             {formsubst i p | p IN s /\
                              (!x. i x IN terms(FST(language t)))} <=>
             M satisfies s)`;;

(* ------------------------------------------------------------------------- *)
(* So we have compactness in a strong form.                                  *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CANON_QFREE = `(!p. p IN s ==> qfree p) /\
   (!t. FINITE t /\ t SUBSET s ==> ?M. interpretation(language ss) M /\
                                       ~(Dom(M):A->bool = EMPTY) /\
                                       M satisfies t)
   ==> ?C. interpretation (language ss) C /\
           canonical (language ss) C /\
           C satisfies s`;;

(* ------------------------------------------------------------------------- *)
(* Tedious lemma about sublanguage.                                          *)
(* ------------------------------------------------------------------------- *)

let INTERPRETATION_RESTRICTLANGUAGE = `!M s t. t SUBSET s /\ interpretation(language s) M
         ==> interpretation(language t) M`;;

let INTERPRETATION_EXTENDLANGUAGE = `!M s t.
        interpretation (language t) M /\
        ~(Dom M :A->bool = EMPTY) /\
        M satisfies t
        ==> ?M'. (Dom M' = Dom M) /\
                 (Pred M' = Pred M) /\
                 interpretation(language s) M' /\
                 M' satisfies t`;;

(* ------------------------------------------------------------------------- *)
(* Generalize to any formulas, via Skolemization.                            *)
(* ------------------------------------------------------------------------- *)

let COMPACT_LS = `(!t. FINITE t /\ t SUBSET s ==> ?M. interpretation(language s) M /\
                                       ~(Dom(M):A->bool = EMPTY) /\
                                       M satisfies t)
   ==> ?C. interpretation (language s) C /\
           ~(Dom(C):term->bool = EMPTY) /\
           C satisfies s`;;

(* ------------------------------------------------------------------------- *)
(* Split away the compactness argument.                                      *)
(* ------------------------------------------------------------------------- *)

let CANON = `!M:(A->bool)#(num->A list->A)#(num->A list->bool) s.
        interpretation (language s) M /\
        ~(Dom(M) = EMPTY) /\
        (!p. p IN s ==> qfree p) /\ M satisfies s
        ==> ?C. interpretation (language s) C /\
                ~(Dom C :term->bool = EMPTY) /\
                C satisfies s`;;

(* ------------------------------------------------------------------------- *)
(* Conventional form of the LS theorem.                                      *)
(* ------------------------------------------------------------------------- *)

let term_of_num = new_definition
  `term_of_num n = (@t. num_of_term t = n)`;;

let TERM_OF_NUM = `term_of_num(num_of_term t) = t`;;

let LOWMOD = new_definition
  `LOWMOD M = {num_of_term t | t IN Dom(M)},
              (\g zs. num_of_term (Fun(M) g (MAP term_of_num zs))),
              (\p zs. Pred(M) p (MAP term_of_num zs))`;;

let LOWMOD_DOM_EMPTY = `(Dom(LOWMOD M) = EMPTY) <=> (Dom(M) = EMPTY)`;;

let LOWMOD_TERMVAL = `!v. valuation (LOWMOD M) v
       ==> !t. termval (LOWMOD M) v t =
               num_of_term (termval M (term_of_num o v) t)`;;

let LOWMOD_HOLDS = `!p v. valuation (LOWMOD M) v
         ==> (holds (LOWMOD M) v p <=> holds M (term_of_num o v) p)`;;

let LOWMOD_INTERPRETATION = `!L M. interpretation L (LOWMOD M) = interpretation L M`;;

let LS = `!M:(A->bool)#(num->A list->A)#(num->A list->bool) s.
        interpretation (language s) M /\
        ~(Dom(M) = EMPTY) /\
        (!p. p IN s ==> qfree p) /\ M satisfies s
        ==> ?N. interpretation (language s) N /\
                ~(Dom N :num->bool = EMPTY) /\
                N satisfies s`;;

(* ------------------------------------------------------------------------- *)
(* Now the Uniformity Lemma.                                                 *)
(* ------------------------------------------------------------------------- *)

let UNIFORMITY = `qfree p /\ (!C v. ~(Dom C = EMPTY) /\
                     valuation(C) v ==> holds C (v:num->term) (ITLIST ?? xs p))
   ==> ?is. (!i x. MEM i is ==> terms(FST(language {p})) (i x)) /\
            !d. pholds(d) (ITLIST (||) (MAP (\i. formsubst i p) is) False)`;;
