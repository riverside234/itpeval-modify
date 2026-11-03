(* ========================================================================= *)
(* Conversion to Skolem normal form.                                         *)
(* ========================================================================= *)

let HOLDS_EXISTS_LEMMA = `!p t x M v preds:num#num->bool.
        interpretation (functions_term t,preds) M /\
        valuation(M) (v:num->A) /\
        holds M v (formsubst (valmod (x,t) V) p)
        ==> holds M v (??x p)`;;

(* ------------------------------------------------------------------------- *)
(* One-step Skolemization of ??x p using new function f.                     *)
(* ------------------------------------------------------------------------- *)

let Skolem1_DEF = new_definition
  `Skolem1 f x p =
     formsubst (valmod (x,Fn f (MAP V (list_of_set(FV(??x p))))) V) p`;;

let HOLDS_SKOLEM1 = `!f x p.
     prenex(??x p) /\
     ~((f,CARD(FV(??x p))) IN functions_form(??x p))
     ==> prenex(Skolem1 f x p) /\
         (FV(Skolem1 f x p) = FV(??x p)) /\
         size(Skolem1 f x p) < size(??x p) /\
         (predicates_form (Skolem1 f x p) = predicates_form(??x p)) /\
         (functions_form(??x p) SUBSET functions_form (Skolem1 f x p)) /\
         (functions_form (Skolem1 f x p) SUBSET ((f,CARD(FV(??x p))) INSERT
                                  functions_form(??x p))) /\
         (!M. interpretation (language {p}) M /\
              ~(Dom(M) = EMPTY) /\
              (!v:num->A. valuation(M) v ==> holds M v (??x p))
              ==> ?M'. (Dom(M') = Dom(M)) /\
                       (Pred(M') = Pred(M)) /\
                       (!g zs. ~(g = f) \/ ~(LENGTH zs = CARD(FV(??x p)))
                               ==> (Fun(M') g zs = Fun(M) g zs)) /\
                       interpretation (language {(Skolem1 f x p)}) M' /\
                       (!v. valuation(M') v ==> holds M' v (Skolem1 f x p))) /\
         (!N. interpretation (language {(Skolem1 f x p)}) N /\
              ~(Dom(N) = EMPTY)
              ==> !v:num->A. valuation(N) (v:num->A) /\
                             holds N v (Skolem1 f x p) ==> holds N v (??x p))`;;

(* ------------------------------------------------------------------------- *)
(* Multiple Skolemization of a prenex formula.                               *)
(* ------------------------------------------------------------------------- *)

let Skolems_EXISTENCE = `!J. ?Skolems. !r.
    Skolems r = \k. PPAT (\x q. !!x (Skolems q k))
                         (\x q. Skolems (Skolem1 (NUMPAIR J k) x q) (SUC k))
                         (\p. p) r`;;

let Skolems_SPECIFICATION = `?Skolems. !J r k.
        Skolems J r k =
          PPAT (\x q. !!x (Skolems J q k))
               (\x q. Skolems J (Skolem1 (NUMPAIR J k) x q) (SUC k))
               (\p. p) r`;;

let Skolems_DEF = new_specification ["Skolems"] Skolems_SPECIFICATION;;

let HOLDS_SKOLEMS_INDUCTION = `!n J k p.
           (size(p) = n) /\
           prenex(p) /\
           (!l m. (NUMPAIR J l,m) IN functions_form p ==> l < k)
           ==> universal((Skolems J p k)) /\
               (FV((Skolems J p k)) = FV(p)) /\
               (predicates_form (Skolems J p k) = predicates_form p) /\
                functions_form p SUBSET functions_form (Skolems J p k) /\
                functions_form (Skolems J p k) SUBSET
                 {NUMPAIR j l,m | j,l,m | (j = J) /\ k <= l} UNION
                 functions_form p /\
                (!M. interpretation (language {p}) M /\
                     ~(Dom M = EMPTY) /\
                     (!v:num->A. valuation M v ==> holds M v p)
                     ==> ?M'. (Dom M' = Dom M) /\
                              (Pred M' = Pred M) /\
                              (!g zs. ~(Fun(M') g zs = Fun(M) g zs)
                                    ==> ?l. k <= l /\ (g = NUMPAIR J l)) /\
                              interpretation (language {(Skolems J p k)}) M' /\
                              (!v. valuation M' v
                                   ==> holds M' v (Skolems J p k))) /\
               (!N. interpretation (language {(Skolems J p k)}) N /\
                ~(Dom(N) = EMPTY)
                ==> !v:num->A. valuation(N) v /\ holds N v (Skolems J p k)
                               ==> holds N v p)`;;

let HOLDS_SKOLEMS_PRENEX = `!p.
    prenex(p)
    ==> !K. (!l m. ~(NUMPAIR K l,m IN functions_form p))
            ==> universal(Skolems K p 0) /\
                (FV(Skolems K p 0) = FV(p)) /\
                (predicates_form (Skolems K p 0) = predicates_form p) /\
                functions_form p SUBSET functions_form (Skolems K p 0) /\
                functions_form (Skolems K p 0) SUBSET
                 {NUMPAIR k l,m | k,l,m | k = K} UNION functions_form p /\
                (!M. interpretation (language {p}) M /\
                     ~(Dom M = EMPTY) /\
                     (!v:num->A. valuation M v ==> holds M v p)
                     ==> ?M'. (Dom M' = Dom M) /\
                              (Pred M' = Pred M) /\
                              (!g zs. ~(Fun M' g zs = Fun M g zs)
                                      ==> (?l. g =
                                              NUMPAIR K l)) /\
                              interpretation (language {(Skolems K p 0)}) M' /\
                              (!v. valuation M' v
                                   ==> holds M' v (Skolems K p 0))) /\
                (!N. interpretation (language {(Skolems K p 0)}) N /\
                     ~(Dom N = EMPTY)
                     ==> !v:num->A. valuation(N) v /\ holds N v (Skolems K p 0)
                                    ==> holds N v p)`;;

(* ------------------------------------------------------------------------- *)
(* Now Skolemize an arbitrary (non-prenex) formula.                          *)
(* ------------------------------------------------------------------------- *)

let Skopre_DEF = new_definition
  `Skopre K p = Skolems K (Prenex p) 0`;;

let SKOPRE = `!p K.
      (!l m. ~(NUMPAIR K l,m IN functions_form p))
       ==> universal(Skopre K p) /\
           (FV(Skopre K p) = FV(p)) /\
           (predicates_form (Skopre K p) = predicates_form p) /\
           functions_form p SUBSET functions_form (Skopre K p) /\
           functions_form (Skopre K p) SUBSET
            {NUMPAIR k l,m | k,l,m | k = K} UNION functions_form p /\
           (!M. interpretation (language {p}) M /\
                ~(Dom M = EMPTY) /\
                (!v:num->A. valuation M v ==> holds M v p)
                ==> ?M'. (Dom M' = Dom M) /\
                         (Pred M' = Pred M) /\
                         (!g zs. ~(Fun M' g zs = Fun M g zs)
                                 ==> (?l. g =
                                         NUMPAIR K l)) /\
                         interpretation (language {(Skopre K p)}) M' /\
                         (!v. valuation M' v ==> holds M' v (Skopre K p))) /\
           (!N. interpretation (language {(Skopre K p)}) N /\
                ~(Dom(N) = EMPTY)
                ==> !v:num->A. valuation(N) v /\ holds N v (Skopre K p)
                               ==> holds N v p)`;;

(* ------------------------------------------------------------------------- *)
(* Bumping up function indices to leave room for Skolem functions.           *)
(* ------------------------------------------------------------------------- *)

let bumpmod = new_definition
  `bumpmod(M) = Dom(M),(\k zs. Fun(M) (NUMSND k) zs),Pred(M)`;;

let bumpterm = new_recursive_definition term_RECURSION
  `(bumpterm (V x) = V x) /\
   (bumpterm (Fn k l) = Fn (NUMPAIR 0 k) (MAP bumpterm l))`;;

let bumpform = new_recursive_definition form_RECURSION
  `(bumpform False = False) /\
   (bumpform (Atom p l) = Atom p (MAP bumpterm l)) /\
   (bumpform (q --> r) = bumpform q --> bumpform r) /\
   (bumpform (!!x r) = !!x (bumpform r))`;;

let BUMPTERM = `!M v t. termval M v t = termval (bumpmod M) v (bumpterm t)`;;

let BUMPFORM = `!M p v. holds M v p = holds (bumpmod M) v (bumpform p)`;;

let FUNCTIONS_FORM_BUMPFORM = `!p f m.
        f,m IN functions_form(bumpform p)
        ==> ?k. (f = NUMPAIR 0 k) /\ k,m IN functions_form p`;;

let BUMPFORM_INTERPRETATION = `interpretation (language {p}) M
   ==> interpretation (language {(bumpform p)}) (bumpmod M)`;;

let unbumpterm = new_recursive_definition term_RECURSION
  `(unbumpterm (V x) = V x) /\
   (unbumpterm (Fn k l) = Fn (NUMSND k) (MAP unbumpterm l))`;;

let unbumpform = new_recursive_definition form_RECURSION
  `(unbumpform False = False) /\
   (unbumpform (Atom p l) = Atom p (MAP unbumpterm l)) /\
   (unbumpform (q --> r) = unbumpform q --> unbumpform r) /\
   (unbumpform (!!x r) = !!x (unbumpform r))`;;

let UNBUMPTERM = `!t. unbumpterm(bumpterm t) = t`;;

let UNBUMPFORM = `!p. unbumpform (bumpform p) = p`;;

let unbumpmod = new_definition
  `unbumpmod(M) = Dom(M),(\k zs. Fun(M) (NUMPAIR 0 k) zs),Pred(M)`;;

let UNBUMPMOD_TERM = `!M v t. termval M v (bumpterm t) = termval (unbumpmod M) v t`;;

let UNBUMPMOD = `!M p (v:num->A). holds M v (bumpform p) = holds (unbumpmod M) v p`;;

(* ------------------------------------------------------------------------- *)
(* Mapping terms and formulas into terms for unique Skolem functions.        *)
(* ------------------------------------------------------------------------- *)

let NUMLIST = new_recursive_definition list_RECURSION
  `(NUMLIST [] = 0) /\
   (NUMLIST (CONS h t) = NUMPAIR h (NUMLIST t) + 1)`;;

let NUMLIST_INJ = `!l1 l2. (NUMLIST l1 = NUMLIST l2) = (l1 = l2)`;;

let num_of_term = new_nested_recursive_definition term_RECURSION
  `(!x. num_of_term (V x) = NUMPAIR 0 x) /\
   (!f l. num_of_term (Fn f l) =
            NUMPAIR 1 (NUMPAIR f (NUMLIST(MAP num_of_term l))))`;;

let NUM_OF_TERM_INJ = `!s t. (num_of_term s = num_of_term t) = (s = t)`;;

let num_of_form = new_recursive_definition form_RECURSION
  `(num_of_form False = NUMPAIR 0 0) /\
   (num_of_form (Atom p l) =
        NUMPAIR 1 (NUMPAIR p (NUMLIST(MAP num_of_term l)))) /\
   (num_of_form (q --> r) =
        NUMPAIR 2 (NUMPAIR (num_of_form q) (num_of_form r))) /\
   (num_of_form (!!x q) = NUMPAIR 3 (NUMPAIR x (num_of_form q)))`;;

let NUMLIST_NUM_OF_TERM = `!l1 l2. (NUMLIST (MAP num_of_term l1) = NUMLIST (MAP num_of_term l2)) =
           (l1 = l2)`;;

let NUM_OF_FORM_INJ = `!q r. (num_of_form q = num_of_form r) = (q = r)`;;

let form_of_num = new_definition
  `form_of_num x = @p. num_of_form p = x`;;

let FORM_OF_NUM = `form_of_num(num_of_form p) = p`;;

(* ------------------------------------------------------------------------- *)
(* Skolemization function.                                                   *)
(* ------------------------------------------------------------------------- *)

let SKOLEMIZE = new_definition
  `SKOLEMIZE p = Skopre (num_of_form(bumpform p) + 1) (bumpform p)`;;

let SKOLEMIZE_WORKS = `!p. universal(SKOLEMIZE p) /\
       (FV(SKOLEMIZE p) = FV(bumpform p)) /\
       (predicates_form (SKOLEMIZE p) = predicates_form (bumpform p)) /\
       functions_form (bumpform p) SUBSET functions_form (SKOLEMIZE p) /\
       functions_form (SKOLEMIZE p) SUBSET
        {NUMPAIR k l,m | k,l,m | k = num_of_form(bumpform p) + 1} UNION
        functions_form (bumpform p) /\
       (!M. interpretation (language {(bumpform p)}) M /\
            ~(Dom M = EMPTY) /\
            (!v:num->A. valuation M v ==> holds M v (bumpform p))
            ==> ?M'. (Dom M' = Dom M) /\
                     (Pred M' = Pred M) /\
                     (!g zs. ~(Fun M' g zs = Fun M g zs)
                             ==> (?l. g =
                                     NUMPAIR (num_of_form(bumpform p) + 1)
                                             l)) /\
                     interpretation (language {(SKOLEMIZE p)}) M' /\
                     (!v. valuation M' v ==> holds M' v (SKOLEMIZE p))) /\
       (!N. interpretation (language {(SKOLEMIZE p)}) N /\
            ~(Dom(N) = EMPTY)
            ==> !v:num->A. valuation(N) v /\ holds N v (SKOLEMIZE p)
                           ==> holds N v (bumpform p))`;;

let FUNCTIONS_FORM_SKOLEMIZE = `!p f m.
        f,m IN functions_form(SKOLEMIZE p)
        ==> (?k. (f = NUMPAIR 0 k) /\ k,m IN functions_form p) \/
            (?l. (f = NUMPAIR (num_of_form (bumpform p) + 1) l))`;;

(* ------------------------------------------------------------------------- *)
(* Construction of Skolem model for a formula.                               *)
(* ------------------------------------------------------------------------- *)

let SKOMOD1 = new_definition
  `SKOMOD1 p M =
     if (!v. valuation M v ==> holds M v p)
     then @M'. (Dom M' = Dom (bumpmod M)) /\
               (Pred M' = Pred (bumpmod M)) /\
               (!g zs.
                    ~(Fun M' g zs = Fun (bumpmod M) g zs)
                    ==> (?l. g =
                             NUMPAIR (num_of_form (bumpform p) + 1) l)) /\
               interpretation (language {(SKOLEMIZE p)}) M' /\
               (!v:num->A. valuation M' v
                           ==> holds M' v (SKOLEMIZE p))
     else (Dom M,(\g zs. @a:A. a IN Dom(M)),Pred M)`;;

let SKOMOD1_WORKS = `!M p.
      interpretation (language {p}) M /\
      ~(Dom M = EMPTY)
      ==> (Dom (SKOMOD1 p M) = Dom (bumpmod M)) /\
          (Pred (SKOMOD1 p M) = Pred (bumpmod M)) /\
          interpretation (language {(SKOLEMIZE p)}) (SKOMOD1 p M) /\
          ((!v:num->A. valuation M v ==> holds M v p)
           ==> (!g zs.
                    ~(Fun (SKOMOD1 p M) g zs = Fun (bumpmod M) g zs)
                    ==> (?l. g =
                             NUMPAIR (num_of_form (bumpform p) + 1) l)) /\
               (!v:num->A. valuation (SKOMOD1 p M) v
                 ==> holds (SKOMOD1 p M) v (SKOLEMIZE p)))`;;

let SKOMOD = new_definition
  `SKOMOD M =
     (Dom M,
      (\g zs. if NUMFST g = 0 then Fun M (NUMSND g) zs
              else Fun (SKOMOD1 (unbumpform(form_of_num (PRE(NUMFST g)))) M)
                       g zs),
      Pred M)`;;

let SKOMOD_INTERPRETATION = `interpretation (language {p}) M /\
   ~(Dom M :A->bool = EMPTY)
   ==> interpretation (language {(SKOLEMIZE p)}) (SKOMOD M)`;;

let SKOMOD_WORKS = `interpretation(language {p}) M /\
   ~(Dom M = EMPTY)
   ==> ((!v:num->A. valuation(M) v ==> holds M v p) <=>
        (!v:num->A. valuation(SKOMOD M) v
                    ==> holds (SKOMOD M) v (SKOLEMIZE p)))`;;

let SKOLEMIZE_SATISFIABLE = `(?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language s) M /\
        M satisfies s) <=>
   (?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language {SKOLEMIZE p | p IN s}) M /\
        M satisfies {SKOLEMIZE p | p IN s})`;;

(* ------------------------------------------------------------------------- *)
(* Skolemization right down to quantifier-free formula.                      *)
(* ------------------------------------------------------------------------- *)

let specialize = new_recursive_definition form_RECURSION
  `(specialize False = False) /\
   (specialize (Atom p l) = Atom p l) /\
   (specialize (q --> r) = q --> r) /\
   (specialize (!!x r) = specialize r)`;;

let SPECIALIZE_SATISFIES = `!M s. ~(Dom M:A->bool = EMPTY)
         ==> (M satisfies s <=> M satisfies {specialize p | p IN s})`;;

let SPECIALIZE_QFREE = `!p. universal p ==> qfree(specialize p)`;;

let SPECIALIZE_LANGUAGE = `!s. language {specialize p | p IN s} = language s`;;

let SKOLEM = new_definition
  `SKOLEM p = specialize(SKOLEMIZE p)`;;

let SKOLEM_QFREE = `!p. qfree(SKOLEM p)`;;

let SKOLEM_SATISFIABLE = `(?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language s) M /\
        M satisfies s) =
   (?M. ~(Dom M :A->bool = EMPTY) /\
        interpretation (language {SKOLEM p | p IN s}) M /\
        M satisfies {SKOLEM p | p IN s})`;;
