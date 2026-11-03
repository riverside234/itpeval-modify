(* ========================================================================= *)
(* Formalization of semantics and basic model theory of first order logic.   *)
(* ========================================================================= *)

let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  check((=) s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;

let LIST_UNION = new_recursive_definition list_RECURSION
  `(LIST_UNION [] = {}) /\
   (LIST_UNION (CONS h t) = h UNION (LIST_UNION t))`;;

let LIST_UNION_FINITE = `!l. ALL FINITE l ==> FINITE(LIST_UNION l)`;;

let IN_LIST_UNION = `!x l. x IN (LIST_UNION l) <=> EX (\s. x IN s) l`;;

let LIST_UNION_APPEND = `!l1 l2. LIST_UNION(APPEND l1 l2) = (LIST_UNION l1) UNION (LIST_UNION l2)`;;

(* ------------------------------------------------------------------------- *)
(* Nested type of terms.                                                     *)
(* ------------------------------------------------------------------------- *)

let term_raw_INDUCT,term_raw_RECURSION = define_type
  "term = V num | Fn num (term list)";;

(* ------------------------------------------------------------------------- *)
(* Manually extract "nested" version of induction and recursion.             *)
(* One day, this will be automated; it's really pretty trivial.              *)
(* ------------------------------------------------------------------------- *)

let term_INDUCT = `!P. (!v. P(V v)) /\ (!s l. ALL P l ==> P(Fn s l)) ==> !t. P t`;;

let term_RECURSION = `!f h. ?fn:term->Z.
        (!v. fn(V v) = f v) /\
        (!s l. fn(Fn s l) = h s l (MAP fn l))`;;

(* ------------------------------------------------------------------------- *)
(* General Skolemizing hack to allow fixed initial parameters in nested      *)
(* recursive defs. Note that (prima facie) variable ones aren't justified.   *)
(* ------------------------------------------------------------------------- *)

let new_nested_recursive_definition ax tm =
  let expat = lhand(snd(strip_forall(hd(conjuncts tm)))) in
  let ev,allargs = strip_comb expat in
  let pargs = butlast allargs in
  let tm' = mk_exists(ev,list_mk_forall(pargs,tm)) in
  let rawprover = prove_recursive_functions_exist ax in
  let eth = prove(tm',
                  REWRITE_TAC[GSYM SKOLEM_THM] THEN
                  REPEAT GEN_TAC THEN
                  W(ACCEPT_TAC o rawprover o snd o dest_exists o snd)) in
  SPECL pargs (new_specification [fst(dest_var ev)] eth);;

(* ------------------------------------------------------------------------- *)
(* Standard consequences.                                                    *)
(* ------------------------------------------------------------------------- *)

let term_INJ = prove_constructors_injective term_RECURSION;;

let term_DISTINCT = prove_constructors_distinct term_RECURSION;;

let term_CASES = prove_cases_thm term_INDUCT;;

(* ------------------------------------------------------------------------- *)
(* Definition of formulas.                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(13,"right"));;

let form_INDUCTION,form_RECURSION =
  define_type "form = False
                    | Atom num (term list)
                    | --> form form
                    | !! num form";;

let form_INJ = prove_constructors_injective form_RECURSION;;

let form_DISTINCT = prove_constructors_distinct form_RECURSION;;

let form_CASES = prove_cases_thm form_INDUCTION;;

(* ------------------------------------------------------------------------- *)
(* Definitions of other connectives.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("&&",(16,"right"));;
parse_as_infix("||",(14,"right"));;
parse_as_infix("<->",(12,"right"));;

let Not_DEF = new_definition
  `Not p = p --> False`;;

let True_DEF = new_definition
  `True = Not False`;;

let Or_DEF = new_definition
  `p || q = (p --> q) --> q`;;

let And_DEF = new_definition
  `p && q = Not (Not p || Not q)`;;

let Iff_DEF = new_definition
  `(p <-> q) = (p --> q) && (q --> p)`;;

let Exists_DEF = new_definition
  `?? x p = Not(!!x (Not p))`;;

(* ------------------------------------------------------------------------- *)
(* The language of a term, formula and set of formulas.                      *)
(* ------------------------------------------------------------------------- *)

let functions_term = new_recursive_definition term_RECURSION
  `(!v. functions_term (V v) = {}) /\
   (!f l. functions_term (Fn f l) =
        (f,LENGTH l) INSERT (LIST_UNION (MAP functions_term l)))`;;

let functions_form = new_recursive_definition form_RECURSION
  `(functions_form False = {}) /\
   (functions_form (Atom a l) = LIST_UNION (MAP functions_term l)) /\
   (functions_form (p --> q) = (functions_form p) UNION (functions_form q)) /\
   (functions_form (!! x p) = functions_form p)`;;

let predicates_form = new_recursive_definition form_RECURSION
  `(predicates_form False = {}) /\
   (predicates_form (Atom a l) = {(a,LENGTH l)}) /\
   (predicates_form (p --> q) =
        (predicates_form p) UNION (predicates_form q)) /\
   (predicates_form (!! x p) = predicates_form p)`;;

let functions = new_definition
  `functions fms = UNIONS {functions_form f | f IN fms}`;;

let predicates = new_definition
  `predicates fms = UNIONS {predicates_form f | f IN fms}`;;

let language = new_definition
  `language fms = functions fms, predicates fms`;;

let FUNCTIONS_SING = `functions {p} = functions_form p`;;

let LANGUAGE_1 = `language {p} = functions_form p,predicates_form p`;;

(* ------------------------------------------------------------------------- *)
(* Selecting the bits of an interpretation: domain, functions and relations. *)
(* ------------------------------------------------------------------------- *)

let Dom_DEF = new_definition
  `Dom (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = D`;;

let Fun_DEF = new_definition
  `Fun (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = Funs`;;

let Pred_DEF = new_definition
  `Pred (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = Preds`;;

let MODEL_EQ = `(M = M') <=> (Dom M = Dom M') /\ (Fun M = Fun M') /\ (Pred M = Pred M')`;;

let MODEL_DECOMP = `M = Dom M,Fun M,Pred M`;;

(* ------------------------------------------------------------------------- *)
(* Free variables and bound variables.                                       *)
(* ------------------------------------------------------------------------- *)

let FVT = new_recursive_definition term_RECURSION
  `(!x. FVT (V x) = {x}) /\
   (!f l. FVT (Fn f l) = LIST_UNION (MAP FVT l))`;;

let FV = new_recursive_definition form_RECURSION
  `(FV False = {}) /\
   (!a l. FV (Atom a l) = LIST_UNION (MAP FVT l)) /\
   (!p q. FV (p --> q) = FV p UNION FV q) /\
   (!x p. FV (!! x p) = FV p DELETE x)`;;

let BV = new_recursive_definition form_RECURSION
  `(BV False = {}) /\
   (!a l. BV (Atom a l) = {}) /\
   (!p q. BV (p --> q) = BV p UNION BV q) /\
   (!x p. BV (!! x p) = x INSERT BV p)`;;

let FVT_FINITE = `!t. FINITE(FVT t)`;;

let FV_FINITE = `!p. FINITE(FV p)`;;

let BV_FINITE = `!p. FINITE(BV p)`;;

let FV_EXISTS = `FV(??x p) = FV(p) DELETE x`;;

(* ------------------------------------------------------------------------- *)
(* Modifier for a valuation.                                                 *)
(* ------------------------------------------------------------------------- *)

let valmod = new_definition
  `valmod (x,a) v = \y. if y = x then a else v y`;;

let VALMOD_CLAUSES = `(!v a k. valmod (k,a) v k = a) /\
   (!v a k x. ~(x = k) ==> (valmod (k,a) v x = v x))`;;

let VALMOD_TRIV = `!v x. valmod (x,v x) v = v`;;

let VALMOD_VALMOD = `!v a x b. valmod (x,a) (valmod (x,b) v) = valmod (x,a) v`;;

(* ------------------------------------------------------------------------- *)
(* Acceptability of a valuation.                                             *)
(* ------------------------------------------------------------------------- *)

let valuation = new_definition
  `valuation(M) v <=> !x:num. v(x) IN Dom(M)`;;

let VALUATION_VALMOD = `!M a v. valuation(M) v /\ a IN Dom(M) ==> valuation(M) (valmod (x,a) v)`;;

let VALUATION_IS_VALMOD = `!v x. valmod(x,v x) v = v`;;

(* ------------------------------------------------------------------------- *)
(* Interpretation of terms and formulas w.r.t. interpretation and valuation. *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("satisfies",(10,"right"));;

let termval = new_nested_recursive_definition term_RECURSION
  `(!x. termval M v (V x) = v(x)) /\
   (!f l. termval M v (Fn f l) = Fun(M) f (MAP (termval M v) l))`;;

let holds = new_recursive_definition form_RECURSION
  `(holds M v False <=> F) /\
   (!a l. holds M v (Atom a l) <=> Pred(M) a (MAP (termval M v) l)) /\
   (!p q. holds M v (p --> q) <=> holds M v p ==> holds M v q) /\
   (!x p. holds M v (!! x p) <=>
                !a. a IN Dom(M) ==> holds M (valmod (x,a) v) p)`;;

let hold = new_definition
  `hold M v fms <=> !p. p IN fms ==> holds M v p`;;

let satisfies = new_definition
  `M satisfies fms <=> !v p. valuation(M) v /\ p IN fms ==> holds M v p`;;

let SATISFIES_1 = `M satisfies {p} <=> !v. valuation(M) v ==> holds M v p`;;

(* ------------------------------------------------------------------------- *)
(* Clauses for derived constructs.                                           *)
(* ------------------------------------------------------------------------- *)

let HOLDS = `(holds M v False <=> F) /\
   (holds M v True <=> T) /\
   (!a l. holds M v (Atom a l) <=> Pred(M) a (MAP (termval M v) l)) /\
   (!p. holds M v (Not p) <=> ~(holds M v p)) /\
   (!p q. holds M v (p || q) <=> holds M v p \/ holds M v q) /\
   (!p q. holds M v (p && q) <=> holds M v p /\ holds M v q) /\
   (!p q. holds M v (p --> q) <=> holds M v p ==> holds M v q) /\
   (!p q. holds M v (p <-> q) <=> (holds M v p = holds M v q)) /\
   (!x p. holds M v (!! x p) <=>
                !a. a IN Dom(M) ==> holds M (valmod (x,a) v) p) /\
   (!x p. holds M v (?? x p) <=>
                ?a. a IN Dom(M) /\ holds M (valmod (x,a) v) p)`;;

(* ------------------------------------------------------------------------- *)
(* Prove that only values given to free variables by the valuation matter.   *)
(* ------------------------------------------------------------------------- *)

let TERMVAL_VALUATION = `!M t (v:num->A) v'.
        (!x. x IN (FVT t) ==> (v'(x) = v(x)))
             ==> (termval M v' t = termval M v t)`;;

let HOLDS_VALUATION = `!M p (v:num->A) v'.
      (!x. x IN (FV p) ==> (v'(x) = v(x)))
             ==> (holds M v' p <=> holds M v p)`;;

(* ------------------------------------------------------------------------- *)
(* Note that these are delicate given the fixed type of interpretations.     *)
(* ------------------------------------------------------------------------- *)

let satisfiable = new_definition
  `satisfiable (U:A->bool) fms <=>
   ?M:(A->bool)#(num->A list->A)#(num->A list->bool).
        ~(Dom M = {}) /\ M satisfies fms`;;

let valid = new_definition
  `valid (U:A->bool) fms <=>
   !M:(A->bool)#(num->A list->A)#(num->A list->bool).
        M satisfies fms`;;

let entails = new_definition
  `entails (U:A->bool) A p <=>
   !(M:(A->bool)#(num->A list->A)#(num->A list->bool)) v.
        hold M v A ==> holds M v p`;;

let equivalent = new_definition
  `equivalent (U:A->bool) p q <=>
   !(M:(A->bool)#(num->A list->A)#(num->A list->bool)) v.
        holds M v p <=> holds M v q`;;

(* ------------------------------------------------------------------------- *)
(* Quality of being an interpretation for a language.                        *)
(* ------------------------------------------------------------------------- *)

let interpretation = new_definition
  `interpretation (fns:(num#num)->bool,preds:(num#num)->bool) M <=>
     !f l. (f,LENGTH l) IN fns /\ ALL (\x. x IN Dom(M)) l
           ==> (Fun(M) f l) IN Dom(M)`;;


let INTERPRETATION_TERMVAL = `!any:num#num->bool M v t.
        interpretation (functions_term t,any) M /\
        valuation(M) v
        ==> termval M v t IN Dom(M)`;;

let INTERPRETATION_SUBLANGUAGE = `!M funs1 funs2 preds1 preds2.
        funs2 SUBSET funs1
        ==> interpretation (funs1,preds1) M
            ==> interpretation (funs2,preds2) M`;;

(* ------------------------------------------------------------------------- *)
(* Substitution in terms.                                                    *)
(* ------------------------------------------------------------------------- *)

let termsubst = new_nested_recursive_definition term_RECURSION
 `(!x. termsubst v (V x) = v(x)) /\
  (!f l. termsubst v (Fn f l) = Fn f (MAP (termsubst v) l))`;;

let TERMSUBST_TERMVAL = `!M. (Fun(M) = Fn) ==> !v t. termsubst v t = termval M v t`;;

let TERMVAL_TRIV = `!M. (Fun(M) = Fn) ==> !t. termval M V t = t`;;

let TERMVAL_TERMSUBST = `!M v i t. termval M v (termsubst i t) = termval M (termval M v o i) t`;;

let TERMSUBST_TERMSUBST = `!i j t. termsubst j (termsubst i t) = termsubst (termsubst j o i) t`;;

let TERMSUBST_TRIV = `!t. termsubst V t = t`;;

let TERMSUBST_VALUATION = `!t v v'. (!x. x IN (FVT t) ==> (v'(x) = v(x)))
            ==> (termsubst v' t = termsubst v t)`;;

let TERMSUBST_FVT = `!t i. FVT(termsubst i t) = {x | ?y. y IN FVT(t) /\ x IN FVT(i y)}`;;

(* ------------------------------------------------------------------------- *)
(* Choice of a new variable.                                                 *)
(* ------------------------------------------------------------------------- *)

let MAX_SYM = `!x y. MAX x y = MAX y x`;;

let MAX_ASSOC = `!x y z. MAX x (MAX y z) = MAX (MAX x y) z`;;

let SETMAX = new_definition
  `SETMAX s = ITSET MAX s 0`;;

let VARIANT = new_definition
  `VARIANT s = SETMAX s + 1`;;

let SETMAX_LEMMA = `(SETMAX {} = 0) /\
   (!x s. FINITE s ==>
           (SETMAX (x INSERT s) = if x IN s then SETMAX s
                                  else MAX x (SETMAX s)))`;;

let SETMAX_MEMBER = `!s. FINITE s ==> !x. x IN s ==> x <= SETMAX s`;;

let SETMAX_THM = `(SETMAX {} = 0) /\
   (!x s. FINITE s ==>
           (SETMAX (x INSERT s) = MAX x (SETMAX s)))`;;

let SETMAX_UNION = `!s t. FINITE(s UNION t)
         ==> (SETMAX(s UNION t) = MAX (SETMAX s) (SETMAX t))`;;

let VARIANT_FINITE = `!s:num->bool. FINITE(s) ==> ~(VARIANT(s) IN s)`;;

let VARIANT_THM = `!p. ~(VARIANT(FV p) IN FV(p))`;;

(* ------------------------------------------------------------------------- *)
(* Substitution in formulas.                                                 *)
(* ------------------------------------------------------------------------- *)

let formsubst = new_recursive_definition form_RECURSION
  `(formsubst v False = False) /\
   (formsubst v (Atom p l) = Atom p (MAP (termsubst v) l)) /\
   (formsubst v (q --> r) = (formsubst v q --> formsubst v r)) /\
   (formsubst v (!!x q) =
        let v' = valmod (x,V x) v in
        let z = if ?y. y IN FV(!!x q) /\ x IN FVT(v'(y))
                then VARIANT(FV(formsubst v' q)) else x in
        !!z (formsubst (valmod (x,V(z)) v) q))`;;

let FORMSUBST_TRIV = `!p. formsubst V p = p`;;

let FORMSUBST_VALUATION = `!p v v'. (!x. x IN (FV p) ==> (v'(x) = v(x)))
            ==> (formsubst v' p = formsubst v p)`;;

let FORMSUBST_FV = `!p i. FV(formsubst i p) = {x | ?y. y IN FV(p) /\ x IN FVT(i y)}`;;

(* ------------------------------------------------------------------------- *)
(* Important lemmas about substitution and renaming.                         *)
(* ------------------------------------------------------------------------- *)

let HOLDS_FORMSUBST = `!p i v. holds M (v:num->A) (formsubst i p) <=>
           holds M (termval M v o i) p`;;

let HOLDS_FORMSUBST1 = `!x t p v. holds M (v:num->A) (formsubst (valmod (x,t) V) p) <=>
             holds M (valmod (x,termval M v t) v) p`;;

let HOLDS_RENAME = `!x y p v. holds M (v:num->A) (formsubst (valmod (x,V y) V) p) <=>
             holds M (valmod (x,v(y)) v) p`;;

let HOLDS_ALPHA_FORALL = `!x y p v. ~(y IN FV(!!x p))
             ==> (holds M v (!!y (formsubst (valmod (x,V y) V) p)) <=>
                  holds M (v:num->A) (!!x p))`;;

let HOLDS_ALPHA_EXISTS = `!x y p v. ~(y IN FV(??x p))
              ==> (holds M v (??y (formsubst (valmod (x,V y) V) p)) <=>
                   holds M (v:num->A) (??x p))`;;

let FORMSUBST_RENAME = `!p x y. FV(formsubst (valmod (x,V y) V) p) DELETE y =
           (FV(p) DELETE x) DELETE y`;;

(* ------------------------------------------------------------------------- *)
(* Analogous theorems for the logical language.                              *)
(* ------------------------------------------------------------------------- *)

let TERMSUBST_FUNCTIONS_TERM = `!t i. functions_term(termsubst i t) =
         functions_term t UNION
         {x | ?y. y IN FVT(t) /\ x IN functions_term(i y)}`;;

let FORMSUBST_FUNCTIONS_FORM = `!p i. functions_form(formsubst i p) =
         functions_form p UNION
         {x | ?y. y IN FV(p) /\ x IN functions_term(i y)}`;;

let FORMSUBST_FUNCTIONS_FORM_1 = `!x t p. x IN FV(p)
           ==> (functions_form(formsubst (valmod (x,t) V) p) =
                functions_form p UNION functions_term t)`;;

(* ------------------------------------------------------------------------- *)
(* And of course we never change the predicates.                             *)
(* ------------------------------------------------------------------------- *)

let FORMSUBST_PREDICATES = `!p i. predicates_form(formsubst i p) = predicates_form p`;;

(* ------------------------------------------------------------------------- *)
(* Special case of renaming preserves language.                              *)
(* ------------------------------------------------------------------------- *)

let FORMSUBST_LANGUAGE_RENAME = `language {(formsubst (valmod (x,V y) V) p)} = language {p}`;;

(* ------------------------------------------------------------------------- *)
(* Invariance under change of language.                                      *)
(* ------------------------------------------------------------------------- *)

let TERMVAL_FUNCTIONS = `!M t. (!f zs. (f,LENGTH zs) IN functions_term t
                 ==> (Fun(M) f zs = Fun(M') f zs))
         ==> !v:num->A. termval M v t = termval M' v t`;;

let HOLDS_FUNCTIONS = `!M M' p. (Dom(M) = Dom(M')) /\
            (!P zs. Pred(M) P zs = Pred(M') P zs) /\
            (!f zs. (f,LENGTH zs) IN functions_form p
                    ==> (Fun(M) f zs = Fun(M') f zs))
            ==> !v:num->A. holds M v p <=> holds M' v p`;;

let HOLDS_PREDICATES = `!M M' p. (Dom(M) = Dom(M')) /\
            (!f zs. Fun(M) f zs = Fun(M') f zs) /\
            (!P zs. (P,LENGTH zs) IN predicates_form p
                    ==> (Pred(M) P zs = Pred(M') P zs))
            ==> !v:num->A. holds M v p <=> holds M' v p`;;

(* ------------------------------------------------------------------------- *)
(* Triviality of universal closure.                                          *)
(* ------------------------------------------------------------------------- *)

let HOLDS_UCLOSE = `!M x p. (!v:num->A. valuation(M) v ==> holds M v (!!x p)) <=>
           (Dom M = EMPTY) \/ !v. valuation(M) v ==> holds M v p`;;

(* ------------------------------------------------------------------------- *)
(* Sort of trivial upward LS theorem without equality.                       *)
(* ------------------------------------------------------------------------- *)

let MODEL_DUPLICATE = `!M fns preds D.
        interpretation(fns,preds) M /\
        (Dom(M) SUBSET D) /\
        ~(Dom(M):A->bool = {})
        ==> ?M'. interpretation(fns,preds) M' /\
                 (Dom(M') = D) /\
                 !s. functions s SUBSET fns /\
                     predicates s SUBSET preds
                     ==> (M' satisfies s <=> M satisfies s)`;;
