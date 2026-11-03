(* ========================================================================= *)
(* Propositional logic as subsystem of FOL, leading to compactness.          *)
(* ========================================================================= *)

let pholds = new_recursive_definition form_RECURSION
  `(pholds v False <=> F) /\
   (pholds v (Atom p l) <=> v (Atom p l)) /\
   (pholds v (q --> r) <=> pholds v q ==> pholds v r) /\
   (pholds v (!!x q) <=> v (!!x q))`;;

let PHOLDS = `(pholds v False <=> F) /\
   (pholds v True <=> T) /\
   (pholds v (Atom p l) <=> v (Atom p l)) /\
   (pholds v (Not q) <=> ~(pholds v q)) /\
   (pholds v (q || r) <=> pholds v q \/ pholds v r) /\
   (pholds v (q && r) <=> pholds v q /\ pholds v r) /\
   (pholds v (q --> r) <=> pholds v q ==> pholds v r) /\
   (pholds v (q <-> r) <=> (pholds v q = pholds v r))`;;

(* ------------------------------------------------------------------------- *)
(* Propositional satisfaction.                                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("psatisfies",(10,"right"));;

let psatisfies = new_definition
  `v psatisfies s <=> !p. p IN s ==> pholds v p`;;

let psatisfiable = new_definition
  `psatisfiable s <=> ?v. !p. p IN s ==> pholds v p`;;

let PSATISFIABLE_MONO = `!A B. psatisfiable A /\ B SUBSET A ==> psatisfiable B`;;

(* ------------------------------------------------------------------------- *)
(* Extensibility of finitely satisfiable set.                                *)
(* ------------------------------------------------------------------------- *)

let finsat = new_definition
  `finsat A <=> !B. B SUBSET A /\ FINITE(B) ==> psatisfiable B`;;

let FINSAT_MONO = `!A B. finsat A /\ B SUBSET A ==> finsat B`;;

let SATISFIABLE_MONO = `!A B. psatisfiable A /\ B SUBSET A ==> psatisfiable B`;;

let FINSAT_SATISFIABLE = `psatisfiable B ==> finsat B`;;

let FINSAT_MAX = `!A. finsat(A) ==> ?B. A SUBSET B /\ finsat(B) /\
                         !C. B SUBSET C /\ finsat(C) ==> (C = B)`;;

(* ------------------------------------------------------------------------- *)
(* Compactness.                                                              *)
(* ------------------------------------------------------------------------- *)

let FINSAT_EXTEND = `finsat(B) ==> finsat(p INSERT B) \/ finsat(Not p INSERT B)`;;

let FINSAT_MAX_COMPLETE = `finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. p IN B \/ Not(p) IN B`;;

let FINSAT_MAX_COMPLETE_STRONG = `finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. Not(p) IN B <=> ~(p IN B)`;;

let FINSAT_DEDUCTION = `finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p. p IN B <=> ?A. FINITE(A) /\ A SUBSET B /\
                        !v. (!q. q IN A ==> pholds v q) ==> pholds v p`;;

let FINSAT_MAX_CONSISTENT = `finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> ~(False IN B)`;;

let FINSAT_MAX_HOMO = `finsat(B) /\ (!C. B SUBSET C /\ finsat(C) ==> (C = B))
   ==> !p q. (p --> q) IN B <=> p IN B ==> q IN B`;;

let COMPACT_PROP = `(!B. FINITE(B) /\ B SUBSET A
        ==> ?d. !r. r IN B ==> pholds(d) r)
   ==> ?d. !r. r IN A ==> pholds(d) r`;;

(* ------------------------------------------------------------------------- *)
(* Important variant used in proving Uniformity for FOL.                     *)
(* ------------------------------------------------------------------------- *)

let COMPACT_PROP_ALT = `!A. (!d. ?p. p IN A /\ pholds d p)
       ==> ?B. FINITE(B) /\ B SUBSET A /\ (!d. ?p. p IN B /\ pholds d p)`;;

let FINITE_DISJ_LEMMA = `!A. FINITE(A) ==> ?ps. ALL (\p. p IN A) ps /\
                          !d. pholds(d) (ITLIST (||) ps False) <=>
                              ?p. p IN A /\ pholds d p`;;

let COMPACT_DISJ = `!A. (!d. ?p. p IN A /\ pholds d p)
       ==> ?ps. ALL (\p. p IN A) ps /\
                !d. pholds(d) (ITLIST (||) ps False)`;;
