(* ========================================================================= *)
(* Formalization of general topological and metric spaces in HOL Light       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2017                       *)
(*                (c) Copyright, Marco Maggesi 2014-2017                     *)
(*             (c) Copyright, Andrea Gabrielli  2016-2017                    *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "Multivariate/misc.ml";;
needs "Library/iter.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Instrument classical tactics to attach label to inductive hypothesis.     *)
(* ------------------------------------------------------------------------- *)

let LABEL_INDUCT_TAC =
  let IND_TAC = MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC in
  fun (asl,w as gl) ->
    let s = fst (dest_var (fst (dest_forall w)))  in
    (IND_TAC THENL
     [ALL_TAC; GEN_TAC THEN DISCH_THEN (LABEL_TAC("ind_"^s))])
    gl;;

let LABEL_ABBREV_TAC tm =
  let cvs,t = dest_eq tm in
  let v,vs = strip_comb cvs in
  let s = name_of v in
  let rs = list_mk_abs(vs,t) in
  let eq = mk_eq(rs,v) in
  let th1 = itlist (fun v th -> CONV_RULE(LAND_CONV BETA_CONV) (AP_THM th v))
                   (rev vs) (ASSUME eq) in
  let th2 = SIMPLE_CHOOSE v (SIMPLE_EXISTS v (GENL vs th1)) in
  let th3 = PROVE_HYP (EXISTS(mk_exists(v,eq),rs) (REFL rs)) th2 in
  fun (asl,w as gl) ->
    let avoids = itlist (union o frees o concl o snd) asl (frees w) in
    if mem v avoids then failwith "LABEL_ABBREV_TAC: variable already used" else
    CHOOSE_THEN
     (fun th -> RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE[th]) THEN
                PURE_ONCE_REWRITE_TAC[th] THEN
                LABEL_TAC s th)
     th3 gl;;

(* ------------------------------------------------------------------------- *)
(* Further tactics for structuring the proof flow.                           *)
(* ------------------------------------------------------------------------- *)

let CUT_TAC : term -> tactic =
  let th = MESON [] `(p ==> q) /\ p ==> q`
  and ptm = `p:bool` in
  fun tm -> MATCH_MP_TAC (INST [tm,ptm] th) THEN CONJ_TAC;;

let CLAIM_TAC s tm = SUBGOAL_THEN tm (DESTRUCT_TAC s);;

let CONJ_LIST = end_itlist CONJ;;

(* ------------------------------------------------------------------------- *)
(* General notion of a topology.                                             *)
(* ------------------------------------------------------------------------- *)

let istopology = new_definition
 `istopology L <=>
        {} IN L /\
        (!s t. s IN L /\ t IN L ==> (s INTER t) IN L) /\
        (!k. k SUBSET L ==> (UNIONS k) IN L)`;;

let topology_tybij_th = `?t:(A->bool)->bool. istopology t`;;

let topology_tybij =
  new_type_definition "topology" ("topology","open_in") topology_tybij_th;;

let ISTOPOLOGY_OPEN_IN = `istopology(open_in top)`;;

let TOPOLOGY_EQ = `!top1 top2. top1 = top2 <=> !s. open_in top1 s <=> open_in top2 s`;;

(* ------------------------------------------------------------------------- *)
(* Infer the "universe" from union of all sets in the topology.              *)
(* ------------------------------------------------------------------------- *)

let topspace = new_definition
 `topspace top = UNIONS {s | open_in top s}`;;

(* ------------------------------------------------------------------------- *)
(* Main properties of open sets.                                             *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_CLAUSES = `!top:(A)topology.
        open_in top {} /\
        (!s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)) /\
        (!k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k))`;;

let OPEN_IN_SUBSET = `!top s. open_in top s ==> s SUBSET (topspace top)`;;

let OPEN_IN_EMPTY = `!top. open_in top {}`;;

let OPEN_IN_INTER = `!top s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)`;;

let OPEN_IN_UNIONS = `!top k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k)`;;

let OPEN_IN_UNION = `!top s t. open_in top s /\ open_in top t ==> open_in top (s UNION t)`;;

let OPEN_IN_TOPSPACE = `!top. open_in top (topspace top)`;;

let OPEN_IN_INTERS = `!top s:(A->bool)->bool.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> open_in top t)
        ==> open_in top (INTERS s)`;;

let OPEN_IN_SUBOPEN = `!top s:A->bool.
        open_in top s <=>
        !x. x IN s ==> ?t. open_in top t /\ x IN t /\ t SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let closed_in = new_definition
 `closed_in top s <=>
        s SUBSET (topspace top) /\ open_in top (topspace top DIFF s)`;;

let CLOSED_IN_SUBSET = `!top s. closed_in top s ==> s SUBSET (topspace top)`;;

let CLOSED_IN_EMPTY = `!top. closed_in top {}`;;

let CLOSED_IN_TOPSPACE = `!top. closed_in top (topspace top)`;;

let CLOSED_IN_UNION = `!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s UNION t)`;;

let CLOSED_IN_INTERS = `!top k:(A->bool)->bool.
        ~(k = {}) /\ (!s. s IN k ==> closed_in top s)
        ==> closed_in top (INTERS k)`;;

let CLOSED_IN_INTER = `!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)`;;

let OPEN_IN_CLOSED_IN_EQ = `!top s. open_in top s <=>
           s SUBSET topspace top /\ closed_in top (topspace top DIFF s)`;;

let OPEN_IN_CLOSED_IN = `!s. s SUBSET topspace top
       ==> (open_in top s <=> closed_in top (topspace top DIFF s))`;;

let CLOPEN_IN_COMPLEMENT = `!top s:A->bool.
        closed_in top s /\ open_in top s <=>
        s SUBSET topspace top /\
        closed_in top (topspace top DIFF s) /\
        open_in top (topspace top DIFF s)`;;

let OPEN_IN_DIFF = `!top s t:A->bool.
      open_in top s /\ closed_in top t ==> open_in top (s DIFF t)`;;

let CLOSED_IN_DIFF = `!top s t:A->bool.
        closed_in top s /\ open_in top t ==> closed_in top (s DIFF t)`;;

let FORALL_OPEN_IN = `!top. (!s. open_in top s ==> P s) <=>
         (!s. closed_in top s ==> P(topspace top DIFF s))`;;

let FORALL_CLOSED_IN = `!top. (!s. closed_in top s ==> P s) <=>
         (!s. open_in top s ==> P(topspace top DIFF s))`;;

let EXISTS_OPEN_IN = `!top. (?s. open_in top s /\ P s) <=>
         (?s. closed_in top s /\ P(topspace top DIFF s))`;;

let EXISTS_CLOSED_IN = `!top. (?s. closed_in top s /\ P s) <=>
         (?s. open_in top s /\ P(topspace top DIFF s))`;;

let TOPOLOGY_FINER_CLOSED_IN = `!top top':A topology.
        topspace top' = topspace top
        ==> ((!s. open_in top s ==> open_in top' s) <=>
             (!s. closed_in top s ==> closed_in top' s))`;;

let CLOSED_IN_UNIONS = `!top s. FINITE s /\ (!t. t IN s ==> closed_in top t)
           ==> closed_in top (UNIONS s)`;;

let TOPOLOGY_EQ_ALT = `!top1 top2:A topology.
        top1 = top2 <=> !s. closed_in top1 s <=> closed_in top2 s`;;

let CARD_EQ_OPEN_CLOSED_IN_SETS = `!top:A topology. {s | open_in top s} =_c {s | closed_in top s}`;;

(* ------------------------------------------------------------------------- *)
(* The discrete topology.                                                    *)
(* ------------------------------------------------------------------------- *)

let discrete_topology = new_definition
 `discrete_topology u = topology {s:A->bool | s SUBSET u}`;;

let discrete_space = new_definition
 `discrete_space (top:A topology) <=> discrete_topology(topspace top) = top`;;

let OPEN_IN_DISCRETE_TOPOLOGY = `!u s:A->bool. open_in (discrete_topology u) s <=> s SUBSET u`;;

let TOPSPACE_DISCRETE_TOPOLOGY = `!u:A->bool. topspace(discrete_topology u) = u`;;

let CLOSED_IN_DISCRETE_TOPOLOGY = `!u s:A->bool. closed_in (discrete_topology u) s <=> s SUBSET u`;;

let DISCRETE_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. discrete_space(discrete_topology u)`;;

let DISCRETE_SPACE = `!top:A topology. discrete_space top <=> ?u. discrete_topology u = top`;;

let FORALL_DISCRETE_SPACES = `(!top:A topology. discrete_space top ==> P (topspace top) top) <=>
   (!u:A->bool. P u (discrete_topology u))`;;

let DISCRETE_TOPOLOGY_UNIQUE = `!top u:A->bool.
        discrete_topology u = top <=>
        topspace top = u /\ (!x. x IN u ==> open_in top {x})`;;

let DISCRETE_SPACE_UNIQUE = `!top:A topology.
        discrete_space top <=> !x. x IN topspace top ==> open_in top {x}`;;

let DISCRETE_TOPOLOGY_UNIQUE_ALT = `!top u:A->bool.
        discrete_topology u = top <=>
        topspace top SUBSET u /\ (!x. x IN u ==> open_in top {x})`;;

let SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_EMPTY = `!top:A topology. top = discrete_topology {} <=> topspace top = {}`;;

let DISCRETE_SPACE_TOPSPACE_EMPTY = `!top:A topology. topspace top = {} ==> discrete_space top`;;

let SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_SING = `!top a:A. top = discrete_topology {a} <=> topspace top = {a}`;;

let DISCRETE_SPACE_OPEN_EQ = `!top:A topology.
        discrete_space top <=> !s. open_in top s <=> s SUBSET topspace top`;;

let DISCRETE_SPACE_OPEN = `!top:A topology.
        discrete_space top <=> !s. s SUBSET topspace top ==> open_in top s`;;

let DISCRETE_SPACE_CLOSED_EQ = `!top:A topology.
        discrete_space top <=> !s. closed_in top s <=> s SUBSET topspace top`;;

let DISCRETE_SPACE_CLOSED = `!top:A topology.
        discrete_space top <=> !s. s SUBSET topspace top ==> closed_in top s`;;

let OPEN_IN_DISCRETE_SPACE = `!top (s:A->bool).
        discrete_space top ==> (open_in top s <=> s SUBSET topspace top)`;;

let CLOSED_IN_DISCRETE_SPACE = `!top (s:A->bool).
        discrete_space top ==> (closed_in top s <=> s SUBSET topspace top)`;;

(* ------------------------------------------------------------------------- *)
(* Subspace topology.                                                        *)
(* ------------------------------------------------------------------------- *)

let subtopology = new_definition
 `subtopology top u = topology {s INTER u | open_in top s}`;;

let ISTOPOLOGY_SUBTOPOLOGY = `!top u:A->bool. istopology {s INTER u | open_in top s}`;;

let ISTOPOLOGY_RELATIVE_TO = `!top u:A->bool.
        istopology top ==> istopology(top relative_to u)`;;

let OPEN_IN_SUBTOPOLOGY = `!top u s. open_in (subtopology top u) s <=>
                ?t. open_in top t /\ s = t INTER u`;;

let TOPOLOGY_FINER_SUBTOPOLOGY = `!top top' (u:A->bool).
        (!s. open_in top s ==> open_in top' s)
        ==> (!s. open_in (subtopology top u) s
                 ==> open_in (subtopology top' u) s)`;;

let OPEN_IN_SUBSET_TOPSPACE = `!top s t:A->bool.
        open_in top s /\ s SUBSET t ==> open_in (subtopology top t) s`;;

let OPEN_INTER_OPEN_IN_SUBTOPOLOGY = `!top s t:A->bool.
        open_in top s ==> open_in (subtopology top t) (s INTER t)`;;

let OPEN_IN_SUBTOPOLOGY_INTER_OPEN = `!top s t:A->bool.
        open_in top t ==> open_in (subtopology top s) (s INTER t)`;;

let OPEN_IN_RELATIVE_TO = `!top s:A->bool.
        (open_in top relative_to s) = open_in (subtopology top s)`;;

let OPEN_IN_SUBTOPOLOGY_ALT = `!top u s:A->bool.
       open_in (subtopology top u) s <=> s IN {u INTER t | open_in top t}`;;

let OPEN_IN_SUBSET_TRANS = `!top s t u:A->bool.
         open_in (subtopology top u) s /\ s SUBSET t /\ t SUBSET u
         ==> open_in (subtopology top t) s`;;

let OPEN_IN_OPEN_SUBTOPOLOGY = `!top s t:A->bool.
        open_in top s
        ==> (open_in (subtopology top s) t <=> open_in top t /\ t SUBSET s)`;;

let OPEN_IN_SUBTOPOLOGY_INTER_SUBSET = `!top s u v:A->bool.
        open_in (subtopology top u) (u INTER s) /\ v SUBSET u
        ==> open_in (subtopology top v) (v INTER s)`;;

let OPEN_IN_SUBTOPOLOGY_INTER_OPEN_IN = `!top s t u.
        open_in (subtopology top u) s /\ open_in top t
        ==> open_in (subtopology top u) (s INTER t)`;;

let TOPSPACE_SUBTOPOLOGY = `!top u. topspace(subtopology top u) = topspace top INTER u`;;

let TOPSPACE_SUBTOPOLOGY_SUBSET = `!top s:A->bool. s SUBSET topspace top ==> topspace(subtopology top s) = s`;;

let TOPSPACE_SUBTOPOLOGY_IS_SUBSET = `!top s:A->bool. topspace(subtopology top s) SUBSET s`;;

let OPEN_IN_TRANS = `!top s t u:A->bool.
        open_in (subtopology top t) s /\
        open_in (subtopology top u) t
        ==> open_in (subtopology top u) s`;;

let CLOSED_IN_SUBTOPOLOGY = `!top u s. closed_in (subtopology top u) s <=>
                ?t:A->bool. closed_in top t /\ s = t INTER u`;;

let CLOSED_IN_SUBSET_TOPSPACE = `!top s t:A->bool.
        closed_in top s /\ s SUBSET t ==> closed_in (subtopology top t) s`;;

let CLOSED_INTER_CLOSED_IN_SUBTOPOLOGY = `!top s t:A->bool.
        closed_in top s ==> closed_in (subtopology top t) (s INTER t)`;;

let CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED = `!top s t:A->bool.
        closed_in top t ==> closed_in (subtopology top s) (s INTER t)`;;

let CLOSED_IN_RELATIVE_TO = `!top s:A->bool.
        (closed_in top relative_to s) = closed_in (subtopology top s)`;;

let CLOSED_IN_SUBTOPOLOGY_ALT = `!top u s:A->bool.
       closed_in (subtopology top u) s <=> s IN {u INTER t | closed_in top t}`;;

let CLOSED_IN_SUBSET_TRANS = `!top s t u:A->bool.
         closed_in (subtopology top u) s /\ s SUBSET t /\ t SUBSET u
         ==> closed_in (subtopology top t) s`;;

let CLOSED_IN_CLOSED_SUBTOPOLOGY = `!top s t:A->bool.
      closed_in top s
      ==> (closed_in (subtopology top s) t <=> closed_in top t /\ t SUBSET s)`;;

let CLOSED_IN_SUBTOPOLOGY_INTER_SUBSET = `!top s u v:A->bool.
        closed_in (subtopology top u) (u INTER s) /\ v SUBSET u
        ==> closed_in (subtopology top v) (v INTER s)`;;

let CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED_IN = `!top s t u.
        closed_in (subtopology top u) s /\ closed_in top t
        ==> closed_in (subtopology top u) (s INTER t)`;;

let SUBTOPOLOGY_SUBTOPOLOGY = `!top s t:A->bool.
        subtopology (subtopology top s) t = subtopology top (s INTER t)`;;

let CLOSED_IN_TRANS = `!top s t u:A->bool.
        closed_in (subtopology top t) s /\
        closed_in (subtopology top u) t
        ==> closed_in (subtopology top u) s`;;

let OPEN_IN_TOPSPACE_EMPTY = `!top:A topology s. topspace top = {} ==> (open_in top s <=> s = {})`;;

let CLOSED_IN_TOPSPACE_EMPTY = `!top:A topology s. topspace top = {} ==> (closed_in top s <=> s = {})`;;

let OPEN_IN_SUBTOPOLOGY_EMPTY = `!top s. open_in (subtopology top {}) s <=> s = {}`;;

let CLOSED_IN_SUBTOPOLOGY_EMPTY = `!top s. closed_in (subtopology top {}) s <=> s = {}`;;

let OPEN_IN_SUBTOPOLOGY_REFL = `!top u:A->bool. open_in (subtopology top u) u <=> u SUBSET topspace top`;;

let CLOSED_IN_SUBTOPOLOGY_REFL = `!top u:A->bool. closed_in (subtopology top u) u <=> u SUBSET topspace top`;;

let SUBTOPOLOGY_SUPERSET = `!top s:A->bool. topspace top SUBSET s ==> subtopology top s = top`;;

let SUBTOPOLOGY_TOPSPACE = `!top. subtopology top (topspace top) = top`;;

let SUBTOPOLOGY_UNIV = `!top. subtopology top UNIV = top`;;

let SUBTOPOLOGY_RESTRICT = `!top s:A->bool.
        subtopology top s = subtopology top (topspace top INTER s)`;;

let OPEN_IN_IMP_SUBSET = `!top s t. open_in (subtopology top s) t ==> t SUBSET s`;;

let CLOSED_IN_IMP_SUBSET = `!top s t. closed_in (subtopology top s) t ==> t SUBSET s`;;

let OPEN_IN_TRANS_FULL = `!top s u.
        open_in (subtopology top u) s /\ open_in top u ==> open_in top s`;;

let CLOSED_IN_TRANS_FULL = `!top s u.
      closed_in (subtopology top u) s /\ closed_in top u ==> closed_in top s`;;

let OPEN_IN_SUBTOPOLOGY_DIFF_CLOSED = `!top s t:A->bool.
        s SUBSET topspace top /\ closed_in top t
        ==> open_in (subtopology top s) (s DIFF t)`;;

let CLOSED_IN_SUBTOPOLOGY_DIFF_OPEN = `!top s t:A->bool.
        s SUBSET topspace top /\ open_in top t
        ==> closed_in (subtopology top s) (s DIFF t)`;;

let OPEN_IN_SUBTOPOLOGY_UNION = `!top s t u:A->bool.
        open_in (subtopology top t) s /\ open_in (subtopology top u) s
        ==> open_in (subtopology top (t UNION u)) s`;;

let CLOSED_IN_SUBTOPOLOGY_UNION = `!top s t u:A->bool.
        closed_in (subtopology top t) s /\ closed_in (subtopology top u) s
        ==> closed_in (subtopology top (t UNION u)) s`;;

let SUBTOPOLOGY_DISCRETE_TOPOLOGY = `!u s:A->bool.
        subtopology (discrete_topology u) s = discrete_topology(u INTER s)`;;

let DISCRETE_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        discrete_space top ==> discrete_space(subtopology top s)`;;

(* ------------------------------------------------------------------------- *)
(* Topology bases.                                                           *)
(* ------------------------------------------------------------------------- *)

let ISTOPOLOGY_BASE_ALT = `!P:(A->bool)->bool.
        istopology (ARBITRARY UNION_OF P) <=>
        (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
               ==> (ARBITRARY UNION_OF P) (s INTER t))`;;

let ISTOPOLOGY_BASE_EQ = `!P:(A->bool)->bool.
        istopology (ARBITRARY UNION_OF P) <=>
        (!s t. P s /\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))`;;

let ISTOPOLOGY_BASE = `!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> istopology (ARBITRARY UNION_OF P)`;;

let MINIMAL_TOPOLOGY_BASE = `!top:A topology P.
        (!s. P s ==> open_in top s) /\
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> !s. open_in(topology(ARBITRARY UNION_OF P)) s ==> open_in top s`;;

let OPEN_IN_TOPOLOGY_BASE_UNIQUE = `!top:A topology B.
        open_in top = ARBITRARY UNION_OF B <=>
        (!v. v IN B ==> open_in top v) /\
        (!u x. open_in top u /\ x IN u
               ==> ?v. v IN B /\ x IN v /\ v SUBSET u)`;;

let TOPOLOGY_BASE_UNIQUE = `!top:A topology P.
        (!s. P s ==> open_in top s) /\
        (!u x. open_in top u /\ x IN u ==> ?b. P b /\ x IN b /\ b SUBSET u)
        ==> topology(ARBITRARY UNION_OF P) = top`;;

let TOPOLOGY_BASES_EQ = `!P Q.
        (!u x. P u /\ x IN u ==> ?v. Q v /\ x IN v /\ v SUBSET u) /\
        (!v x. Q v /\ x IN v ==> ?u. P u /\ x IN u /\ u SUBSET v)
        ==> topology (ARBITRARY UNION_OF P) =
            topology (ARBITRARY UNION_OF Q)`;;

let ISTOPOLOGY_SUBBASE = `!P s:A->bool.
     istopology (ARBITRARY UNION_OF (FINITE INTERSECTION_OF P relative_to s))`;;

let OPEN_IN_SUBBASE = `!B u s:A->bool.
        open_in (topology
           (ARBITRARY UNION_OF (FINITE INTERSECTION_OF B relative_to u))) s <=>
        (ARBITRARY UNION_OF (FINITE INTERSECTION_OF B relative_to u)) s`;;

let TOPSPACE_SUBBASE = `!B u:A->bool.
        topspace(topology
           (ARBITRARY UNION_OF (FINITE INTERSECTION_OF B relative_to u))) = u`;;

let MINIMAL_TOPOLOGY_SUBBASE = `!top:A topology u P.
        (!s. P s ==> open_in top s) /\ open_in top u
        ==> !s. open_in(topology(ARBITRARY UNION_OF
                       (FINITE INTERSECTION_OF P relative_to u))) s
                ==> open_in top s`;;

let ISTOPOLOGY_SUBBASE_UNIV = `!P:(A->bool)->bool.
       istopology (ARBITRARY UNION_OF (FINITE INTERSECTION_OF P))`;;

(* ------------------------------------------------------------------------- *)
(* Hereditary topological properties.                                        *)
(* ------------------------------------------------------------------------- *)

let hereditarily = new_definition
 `hereditarily P (top:A topology) <=>
        !s. s SUBSET topspace top ==> P(subtopology top s)`;;

let HEREDITARILY = `!P top:A topology.
        hereditarily P top <=> !s. P(subtopology top s)`;;

let HEREDITARILY_MONO = `!P Q:A topology->bool.
        (!top. P top ==> Q t)
        ==> (!top:A topology. hereditarily P top ==> hereditarily P top)`;;

let HEREDITARILY_INC = `!P:A topology->bool. hereditarily P top ==> P top`;;

let HEREDITARILY_SUBTOPOLOGY = `!P top s:A->bool.
        hereditarily P top ==> hereditarily P (subtopology top s)`;;

(* ------------------------------------------------------------------------- *)
(* Derived set (set of limit points).                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("derived_set_of",(21,"right"));;

let derived_set_of = new_definition
  `top derived_set_of s =
   {x:A | x IN topspace top /\
          (!t. x IN t /\ open_in top t
               ==> ?y. ~(y = x) /\ y IN s /\ y IN t)}`;;

let DERIVED_SET_OF_RESTRICT = `!top s:A->bool.
     top derived_set_of s = top derived_set_of (topspace top INTER s)`;;

let IN_DERIVED_SET_OF = `!top s x:A.
     x IN top derived_set_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. ~(y = x) /\ y IN s /\ y IN t)`;;

let DERIVED_SET_OF_SUBSET_TOPSPACE = `!top s:A->bool. top derived_set_of s SUBSET topspace top`;;

let DERIVED_SET_OF_SUBTOPOLOGY = `!top u s:A->bool.
        (subtopology top u) derived_set_of s =
        u INTER top derived_set_of (u INTER s)`;;

let DERIVED_SET_OF_SUBSET_SUBTOPOLOGY = `!top s t:A->bool. (subtopology top s) derived_set_of t SUBSET s`;;

let DERIVED_SET_OF_EMPTY = `!top:A topology. top derived_set_of {} = {}`;;

let DERIVED_SET_OF_MONO = `!top s t:A->bool.
        s SUBSET t ==> top derived_set_of s SUBSET top derived_set_of t`;;

let DERIVED_SET_OF_UNION = `!top s t:A->bool.
       top derived_set_of (s UNION t) =
       top derived_set_of s UNION top derived_set_of t`;;

let DERIVED_SET_OF_UNIONS = `!top (f:(A->bool)->bool).
        FINITE f
        ==> top derived_set_of (UNIONS f) =
            UNIONS {top derived_set_of s | s IN f}`;;

let DERIVED_SET_OF_TOPSPACE = `!top:A topology.
        top derived_set_of (topspace top) =
        {x | x IN topspace top /\ ~open_in top {x}}`;;

let DISCRETE_TOPOLOGY_UNIQUE_DERIVED_SET = `!top u:A->bool.
        discrete_topology u = top <=>
        topspace top = u /\ top derived_set_of u = {}`;;

let SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_EQ = `!top u:A->bool.
        subtopology top u = discrete_topology u <=>
        u SUBSET topspace top /\ u INTER top derived_set_of u = {}`;;

let SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY = `!top s:A->bool.
        s SUBSET topspace top /\ s INTER top derived_set_of s = {}
        ==> subtopology top s = discrete_topology s`;;

let SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_GEN = `!top s:A->bool.
        s INTER top derived_set_of s = {}
        ==> subtopology top s = discrete_topology(topspace top INTER s)`;;

let OPEN_IN_INTER_DERIVED_SET_OF_SUBSET = `!top s t:A->bool.
       open_in top s
       ==> s INTER top derived_set_of t SUBSET top derived_set_of (s INTER t)`;;

let OPEN_IN_INTER_DERIVED_SET_OF_EQ = `!top s t:A->bool.
        open_in top s
        ==> s INTER top derived_set_of t =
            s INTER top derived_set_of (s INTER t)`;;

(* ------------------------------------------------------------------------- *)
(* Closure with respect to a topological space.                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("closure_of",(21,"right"));;

let closure_of = new_definition
  `top closure_of s =
   {x:A | x IN topspace top /\
          (!t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t)}`;;

let CLOSURE_OF_RESTRICT = `!top s:A->bool. top closure_of s = top closure_of (topspace top INTER s)`;;

let IN_CLOSURE_OF = `!top s x:A.
     x IN top closure_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t)`;;

let CLOSURE_OF = `!top s:A->bool.
     top closure_of s =
     topspace top INTER (s UNION top derived_set_of s)`;;

let CLOSURE_OF_ALT = `!top s:A->bool.
        top closure_of s = topspace top INTER s UNION top derived_set_of s`;;

let DERIVED_SET_OF_SUBSET_CLOSURE_OF = `!top s:A->bool. top derived_set_of s SUBSET top closure_of s`;;

let CLOSURE_OF_SUBTOPOLOGY = `!top u s:A->bool.
      (subtopology top u) closure_of s = u INTER (top closure_of (u INTER s))`;;

let CLOSURE_OF_EMPTY = `!top. top closure_of {}:A->bool = {}`;;

let CLOSURE_OF_TOPSPACE = `!top:A topology. top closure_of topspace top = topspace top`;;

let CLOSURE_OF_UNIV = `!top. top closure_of (:A) = topspace top`;;

let CLOSURE_OF_SUBSET_TOPSPACE = `!top s:A->bool. top closure_of s SUBSET topspace top`;;

let CLOSURE_OF_SUBSET_SUBTOPOLOGY = `!top s t:A->bool. (subtopology top s) closure_of t SUBSET s`;;

let CLOSURE_OF_MONO = `!top s t:A->bool.
        s SUBSET t ==> top closure_of s SUBSET top closure_of t`;;

let CLOSURE_OF_SUBTOPOLOGY_SUBSET = `!top s u:A->bool.
        (subtopology top u) closure_of s SUBSET (top closure_of s)`;;

let CLOSURE_OF_SUBTOPOLOGY_MONO = `!top s t u:A->bool.
        t SUBSET u
        ==> (subtopology top t) closure_of s SUBSET
            (subtopology top u) closure_of s`;;

let CLOSURE_OF_UNION = `!top s t:A->bool.
       top closure_of (s UNION t) = top closure_of s UNION top closure_of t`;;

let CLOSURE_OF_UNIONS = `!top (f:(A->bool)->bool).
        FINITE f
        ==> top closure_of (UNIONS f) =  UNIONS {top closure_of s | s IN f}`;;

let CLOSURE_OF_SUBSET = `!top s:A->bool. s SUBSET topspace top ==> s SUBSET top closure_of s`;;

let CLOSURE_OF_SUBSET_INTER = `!top s:A->bool. topspace top INTER s SUBSET top closure_of s`;;

let CLOSURE_OF_SUBSET_EQ = `!top s:A->bool.
     s SUBSET topspace top /\ top closure_of s SUBSET s <=> closed_in top s`;;

let CLOSURE_OF_EQ = `!top s:A->bool. top closure_of s = s <=> closed_in top s`;;

let CLOSED_IN_CONTAINS_DERIVED_SET = `!top s:A->bool.
        closed_in top s <=>
        top derived_set_of s SUBSET s /\ s SUBSET topspace top`;;

let DERIVED_SET_SUBSET_GEN = `!top s:A->bool.
        top derived_set_of s SUBSET s <=>
        closed_in top (topspace top INTER s)`;;

let DERIVED_SET_SUBSET = `!top s:A->bool.
        s SUBSET topspace top
        ==> (top derived_set_of s SUBSET s <=> closed_in top s)`;;

let CLOSED_IN_DERIVED_SET = `!top s t:A->bool.
        closed_in (subtopology top t) s <=>
        s SUBSET topspace top /\ s SUBSET t /\
        !x. x IN top derived_set_of s /\ x IN t ==> x IN s`;;

let CLOSED_IN_INTER_CLOSURE_OF = `!top s t:A->bool.
        closed_in (subtopology top s) t <=> s INTER top closure_of t = t`;;

let CLOSURE_OF_CLOSED_IN = `!top s:A->bool. closed_in top s ==> top closure_of s = s`;;

let CLOSED_IN_CLOSURE_OF = `!top s:A->bool. closed_in top (top closure_of s)`;;

let CLOSURE_OF_CLOSURE_OF = `!top s:A->bool. top closure_of (top closure_of s) = top closure_of s`;;

let CLOSURE_OF_HULL = `!top s:A->bool.
        s SUBSET topspace top ==> top closure_of s = (closed_in top) hull s`;;

let CLOSURE_OF_MINIMAL = `!top s t:A->bool.
        s SUBSET t /\ closed_in top t ==> (top closure_of s) SUBSET t`;;

let CLOSURE_OF_MINIMAL_EQ = `!top s t:A->bool.
        s SUBSET topspace top /\ closed_in top t
        ==> ((top closure_of s) SUBSET t <=> s SUBSET t)`;;

let CLOSURE_OF_UNIQUE = `!top s t. s SUBSET t /\ closed_in top t /\
             (!t'. s SUBSET t' /\ closed_in top t' ==> t SUBSET t')
             ==> top closure_of s = t`;;

let FORALL_IN_CLOSURE_OF_GEN = `!top P s:A->bool.
         (!x. x IN s ==> P x) /\
         closed_in top {x | x IN top closure_of s /\ P x}
         ==> (!x. x IN top closure_of s ==> P x)`;;

let FORALL_IN_CLOSURE_OF = `!top P s:A->bool.
         (!x. x IN s ==> P x) /\
         closed_in top {x | x IN topspace top /\ P x}
         ==> (!x. x IN top closure_of s ==> P x)`;;

let FORALL_IN_CLOSURE_OF_UNIV = `!top P s:A->bool.
        (!x. x IN s ==> P x) /\ closed_in top {x | P x}
        ==> !x. x IN top closure_of s ==> P x`;;

let CLOSURE_OF_EQ_EMPTY_GEN = `!top s:A->bool.
        top closure_of s = {} <=> DISJOINT (topspace top) s`;;

let CLOSURE_OF_EQ_EMPTY = `!top s:A->bool.
        s SUBSET topspace top ==> (top closure_of s = {} <=> s = {})`;;

let OPEN_IN_INTER_CLOSURE_OF_SUBSET = `!top s t:A->bool.
        open_in top s
        ==> s INTER top closure_of t SUBSET top closure_of (s INTER t)`;;

let CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF = `!top s t:A->bool.
        open_in top s
        ==> top closure_of (s INTER top closure_of t) =
            top closure_of (s INTER t)`;;

let OPEN_IN_INTER_CLOSURE_OF_EQ = `!top s t:A->bool.
        open_in top s
        ==> s INTER top closure_of t = s INTER top closure_of (s INTER t)`;;

let OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY = `!top s t:A->bool.
        open_in top s ==> (s INTER top closure_of t = {} <=> s INTER t = {})`;;

let CLOSURE_OF_OPEN_IN_INTER_SUPERSET = `!top s t:A->bool.
        open_in top s /\ s SUBSET top closure_of t
        ==> top closure_of (s INTER t) = top closure_of s`;;

let CLOSURE_OF_OPEN_IN_SUBTOPOLOGY_INTER_CLOSURE_OF = `!top s t u:A->bool.
        open_in (subtopology top u) s /\ t SUBSET u
        ==> top closure_of (s INTER top closure_of t) =
            top closure_of (s INTER t)`;;

let CLOSURE_OF_SUBTOPOLOGY_OPEN = `!top u s:A->bool.
        open_in top u \/ s SUBSET u
        ==> (subtopology top u) closure_of s = u INTER top closure_of s`;;

let DISCRETE_TOPOLOGY_CLOSURE_OF = `!u s:A->bool. (discrete_topology u) closure_of s = u INTER s`;;

(* ------------------------------------------------------------------------- *)
(* Interior with respect to a topological space.                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("interior_of",(21,"right"));;

let interior_of = new_definition
 `top interior_of s = {x | ?t. open_in top t /\ x IN t /\ t SUBSET s}`;;

let INTERIOR_OF_RESTRICT = `!top s:A->bool.
        top interior_of s = top interior_of (topspace top INTER s)`;;

let INTERIOR_OF_EQ = `!top s:A->bool. (top interior_of s = s) <=> open_in top s`;;

let INTERIOR_OF_OPEN_IN = `!top s:a->bool. open_in top s ==> top interior_of s = s`;;

let INTERIOR_OF_EMPTY = `!top:A topology. top interior_of {} = {}`;;

let INTERIOR_OF_TOPSPACE = `!top:A topology. top interior_of (topspace top) = topspace top`;;

let OPEN_IN_INTERIOR_OF = `!top s:A->bool. open_in top (top interior_of s)`;;

let INTERIOR_OF_INTERIOR_OF = `!top s:A->bool. top interior_of top interior_of s = top interior_of s`;;

let INTERIOR_OF_SUBSET = `!top s:A->bool. top interior_of s SUBSET s`;;

let INTERIOR_OF_SUBSET_CLOSURE_OF = `!top s:A->bool. top interior_of s SUBSET top closure_of s`;;

let SUBSET_INTERIOR_OF_EQ = `!top s:A->bool. s SUBSET top interior_of s <=> open_in top s`;;

let INTERIOR_OF_MONO = `!top s t:A->bool.
        s SUBSET t ==> top interior_of s SUBSET top interior_of t`;;

let INTERIOR_OF_MAXIMAL = `!top s t:A->bool.
        t SUBSET s /\ open_in top t ==> t SUBSET top interior_of s`;;

let INTERIOR_OF_MAXIMAL_EQ = `!top s t:A->bool.
        open_in top t ==> (t SUBSET top interior_of s <=> t SUBSET s)`;;

let INTERIOR_OF_UNIQUE = `!top s t:A->bool.
        t SUBSET s /\ open_in top t /\
        (!t'. t' SUBSET s /\ open_in top t' ==> t' SUBSET t)
        ==> top interior_of s = t`;;

let INTERIOR_OF_SUBSET_TOPSPACE = `!top s:A->bool. top interior_of s SUBSET topspace top`;;

let INTERIOR_OF_SUBSET_SUBTOPOLOGY = `!top s t:A->bool. (subtopology top s) interior_of t SUBSET s`;;

let INTERIOR_OF_INTER = `!top s t:A->bool.
      top interior_of (s INTER t) = top interior_of s INTER top interior_of t`;;

let INTERIOR_OF_INTERS_SUBSET = `!top f:(A->bool)->bool.
        top interior_of (INTERS f) SUBSET
        INTERS {top interior_of s | s IN f}`;;

let UNION_INTERIOR_OF_SUBSET = `!top s t:A->bool.
        top interior_of s UNION top interior_of t
        SUBSET top interior_of (s UNION t)`;;

let INTERIOR_OF_EQ_EMPTY = `!top s:A->bool.
                top interior_of s = {} <=>
                !t. open_in top t /\ t SUBSET s ==> t = {}`;;

let INTERIOR_OF_EQ_EMPTY_ALT = `!top s:A->bool.
        top interior_of s = {} <=>
        !t. open_in top t /\ ~(t = {}) ==> ~(t DIFF s = {})`;;

let INTERIOR_OF_UNIONS_OPEN_IN_SUBSETS = `!top s:A->bool.
        UNIONS {t | open_in top t /\ t SUBSET s} = top interior_of s`;;

let INTERIOR_OF_COMPLEMENT = `!top s:A->bool.
        top interior_of (topspace top DIFF s) =
        topspace top DIFF top closure_of s`;;

let INTERIOR_OF_CLOSURE_OF = `!top s:A->bool.
        top interior_of s =
        topspace top DIFF top closure_of (topspace top DIFF s)`;;

let CLOSURE_OF_INTERIOR_OF = `!top s:A->bool.
        top closure_of s =
        topspace top DIFF top interior_of (topspace top DIFF s)`;;

let CLOSURE_OF_COMPLEMENT = `!top s:A->bool.
        top closure_of (topspace top DIFF s) =
        topspace top DIFF top interior_of s`;;

let INTERIOR_OF_EQ_EMPTY_COMPLEMENT = `!top s:A->bool.
        top interior_of s = {} <=>
        top closure_of (topspace top DIFF s) = topspace top`;;

let CLOSURE_OF_EQ_UNIV = `!top s:A->bool.
     top closure_of s = topspace top <=>
     top interior_of (topspace top DIFF s) = {}`;;

let INTERIOR_OF_SUBTOPOLOGY_SUBSET = `!top s u:A->bool.
        u INTER top interior_of s SUBSET (subtopology top u) interior_of s`;;

let INTERIOR_OF_SUBTOPOLOGY_SUBSETS = `!top s t u:A->bool.
        t SUBSET u
        ==> t INTER (subtopology top u) interior_of s SUBSET
            (subtopology top t) interior_of s`;;

let INTERIOR_OF_SUBTOPOLOGY_MONO = `!top s t u:A->bool.
        s SUBSET t /\ t SUBSET u
        ==> (subtopology top u) interior_of s SUBSET
            (subtopology top t) interior_of s`;;

let INTERIOR_OF_SUBTOPOLOGY_OPEN = `!top u s:A->bool.
        open_in top u
        ==> (subtopology top u) interior_of s = u INTER top interior_of s`;;

let DENSE_INTERSECTS_OPEN = `!top s:A->bool.
        top closure_of s = topspace top <=>
        !t. open_in top t /\ ~(t = {}) ==> ~(s INTER t = {})`;;

let INTERIOR_OF_CLOSED_IN_UNION_EMPTY_INTERIOR_OF = `!top s t:A->bool.
        closed_in top s /\ top interior_of t = {}
        ==> top interior_of (s UNION t) = top interior_of s`;;

let INTERIOR_OF_UNION_EQ_EMPTY = `!top s t:A->bool.
        closed_in top s \/ closed_in top t
        ==> (top interior_of (s UNION t) = {} <=>
             top interior_of s = {} /\ top interior_of t = {})`;;

let DISCRETE_TOPOLOGY_INTERIOR_OF = `!u s:A->bool. (discrete_topology u) interior_of s = u INTER s`;;

(* ------------------------------------------------------------------------- *)
(* Frontier with respect to topological space.                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("frontier_of",(21,"right"));;

let frontier_of = new_definition
 `top frontier_of s =  top closure_of s DIFF top interior_of s`;;

let FRONTIER_OF_CLOSURES = `!top s. top frontier_of s =
           top closure_of s INTER top closure_of (topspace top DIFF s)`;;

let INTERIOR_OF_UNION_FRONTIER_OF = `!top s:A->bool.
        top interior_of s UNION top frontier_of s = top closure_of s`;;

let FRONTIER_OF_RESTRICT = `!top s:A->bool. top frontier_of s = top frontier_of (topspace top INTER s)`;;

let CLOSED_IN_FRONTIER_OF = `!top s:A->bool. closed_in top (top frontier_of s)`;;

let FRONTIER_OF_SUBSET_TOPSPACE = `!top s:A->bool. top frontier_of s SUBSET topspace top`;;

let FRONTIER_OF_SUBSET_SUBTOPOLOGY = `!top s t:A->bool. (subtopology top s) frontier_of t SUBSET s`;;

let FRONTIER_OF_SUBTOPOLOGY_SUBSET = `!top s u:A->bool.
        u INTER (subtopology top u) frontier_of s SUBSET (top frontier_of s)`;;

let FRONTIER_OF_SUBTOPOLOGY_MONO = `!top s t u:A->bool.
        s SUBSET t /\ t SUBSET u
        ==> (subtopology top t) frontier_of s SUBSET
            (subtopology top u) frontier_of s`;;

let CLOPEN_IN_EQ_FRONTIER_OF = `!top s:A->bool.
        closed_in top s /\ open_in top s <=>
        s SUBSET topspace top /\ top frontier_of s = {}`;;

let FRONTIER_OF_EQ_EMPTY = `!top s:A->bool.
        s SUBSET topspace top
        ==> (top frontier_of s = {} <=> closed_in top s /\ open_in top s)`;;

let FRONTIER_OF_OPEN_IN = `!top s:A->bool.
        open_in top s ==> top frontier_of s = top closure_of s DIFF s`;;

let FRONTIER_OF_OPEN_IN_STRADDLE_INTER = `!top s u:A->bool.
        open_in top  u /\ ~(u INTER top frontier_of s = {})
        ==> ~(u INTER s = {}) /\ ~(u DIFF s = {})`;;

let FRONTIER_OF_SUBSET_CLOSED_IN = `!top s:A->bool. closed_in top s ==> (top frontier_of s) SUBSET s`;;

let FRONTIER_OF_EMPTY = `!top. top frontier_of {} = {}`;;

let FRONTIER_OF_TOPSPACE = `!top:A topology. top frontier_of topspace top = {}`;;

let FRONTIER_OF_SUBSET_EQ = `!top s:A->bool.
        s SUBSET topspace top
        ==> ((top frontier_of s) SUBSET s <=> closed_in top s)`;;

let FRONTIER_OF_COMPLEMENT = `!top s:A->bool. top frontier_of (topspace top DIFF s) = top frontier_of s`;;

let FRONTIER_OF_DISJOINT_EQ = `!top s. s SUBSET topspace top
        ==> ((top frontier_of s) INTER s = {} <=> open_in top s)`;;

let FRONTIER_OF_DISJOINT_EQ_ALT = `!top s:A->bool.
        s SUBSET (topspace top DIFF top frontier_of s) <=>
        open_in top s`;;

let FRONTIER_OF_INTER = `!top s t:A->bool.
        top frontier_of(s INTER t) =
        top closure_of (s INTER t) INTER
        (top frontier_of s UNION top frontier_of t)`;;

let FRONTIER_OF_INTER_SUBSET = `!top s t. top frontier_of(s INTER t) SUBSET
             top frontier_of(s) UNION top frontier_of(t)`;;

let FRONTIER_OF_INTER_CLOSED_IN = `!top s t:A->bool.
        closed_in top s /\ closed_in top t
        ==> top frontier_of(s INTER t) =
            top frontier_of s INTER t UNION s INTER top frontier_of t`;;

let FRONTIER_OF_UNION_SUBSET = `!top s t:A->bool.
      top frontier_of(s UNION t) SUBSET
      top frontier_of s UNION top frontier_of t`;;

let FRONTIER_OF_UNIONS_SUBSET = `!top f:(A->bool)->bool.
        FINITE f
        ==> top frontier_of (UNIONS f) SUBSET
            UNIONS {top frontier_of t | t IN f}`;;

let FRONTIER_OF_FRONTIER_OF_SUBSET = `!top s:A->bool.
    top frontier_of (top frontier_of s) SUBSET top frontier_of s`;;

let FRONTIER_OF_SUBTOPOLOGY_OPEN = `!top u s:A->bool.
        open_in top u
        ==> (subtopology top u) frontier_of s = u INTER top frontier_of s`;;

let DISCRETE_TOPOLOGY_FRONTIER_OF = `!u s:A->bool. (discrete_topology u) frontier_of s = {}`;;

let OPEN_IN_SUBSET_TOPSPACE_EQ = `!top u s:A->bool.
        DISJOINT s (top frontier_of u)
        ==> (open_in (subtopology top u) s <=>
             open_in top s /\ s SUBSET u)`;;

(* ------------------------------------------------------------------------- *)
(* Iteration of interior and closure.                                        *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_OF_CLOSURE_OF_IDEMP = `!top s:A->bool.
        top interior_of top closure_of top interior_of top closure_of s =
        top interior_of top closure_of s`;;

let CLOSURE_OF_INTERIOR_OF_IDEMP = `!top s:A->bool.
        top closure_of top interior_of top closure_of top interior_of s =
        top closure_of top interior_of s`;;

let INTERIOR_OF_FRONTIER_OF = `!top s:A->bool.
        top interior_of (top frontier_of s) =
        top interior_of (top closure_of s) DIFF
        top closure_of (top interior_of s)`;;

let THIN_FRONTIER_OF_SUBSET = `!top s:A->bool.
        top interior_of (top frontier_of s) = {} <=>
        top interior_of (top closure_of s) SUBSET
        top closure_of (top interior_of s)`;;

let THIN_FRONTIER_OF_CIC = `!top s:A->bool.
        top interior_of (top frontier_of s) = {} <=>
        top closure_of (top interior_of (top closure_of s)) =
        top closure_of (top interior_of s)`;;

let THIN_FRONTIER_OF_ICI = `!s:A->bool.
        top interior_of (top frontier_of s) = {} <=>
        top interior_of (top closure_of (top interior_of s)) =
        top interior_of (top closure_of  s)`;;

let INTERIOR_OF_FRONTIER_OF_EMPTY = `!top s:A->bool.
        open_in top s \/ closed_in top s
        ==> top interior_of (top frontier_of s) = {}`;;

let FRONTIER_OF_FRONTIER_OF = `!top s:A->bool.
        open_in top s \/ closed_in top s
        ==> top frontier_of (top frontier_of s) = top frontier_of s`;;

let FRONTIER_OF_FRONTIER_OF_FRONTIER_OF = `!top s:A->bool.
        top frontier_of top frontier_of top frontier_of s =
        top frontier_of top frontier_of s`;;

let REGULAR_CLOSURE_OF_INTERIOR_OF = `!top s:A->bool.
        s SUBSET top closure_of top interior_of s <=>
        s SUBSET topspace top /\
        top closure_of top interior_of s = top closure_of s`;;

let REGULAR_INTERIOR_OF_CLOSURE_OF = `!top s:A->bool.
        top interior_of top closure_of s SUBSET s <=>
        top interior_of top closure_of s = top interior_of s`;;

let REGULAR_CLOSED_IN = `!top s:A->bool.
        top closure_of top interior_of s = s <=>
        closed_in top s /\ s SUBSET top closure_of top interior_of s`;;

let REGULAR_OPEN_IN = `!top s:A->bool.
        top interior_of top closure_of s = s <=>
        open_in top s /\ top interior_of top closure_of s SUBSET s`;;

let REGULAR_CLOSURE_OF_IMP_THIN_FRONTIER_OF = `!top s:A->bool.
        s SUBSET top closure_of top interior_of s
        ==> top interior_of top frontier_of s = {}`;;

let REGULAR_INTERIOR_OF_IMP_THIN_FRONTIER_OF = `!top s:A->bool.
        top interior_of top closure_of s SUBSET s
        ==> top interior_of top frontier_of s = {}`;;

(* ------------------------------------------------------------------------- *)
(* Locally finite collections and their properties.                          *)
(* ------------------------------------------------------------------------- *)

let locally_finite_in = new_definition
 `locally_finite_in top U <=>
        (!u. u IN U ==> u SUBSET topspace top) /\
        (!x. x IN topspace top
             ==> ?v. open_in top v /\ x IN v /\
                     FINITE {u | u IN U /\ ~(u INTER v = {})})`;;

let FINITE_IMP_LOCALLY_FINITE_IN = `!(top:A topology) u.
        FINITE u /\ UNIONS u SUBSET topspace top ==> locally_finite_in top u`;;

let LOCALLY_FINITE_IN_SUBSET = `!(top:A topology) u v.
        locally_finite_in top u /\ v SUBSET u ==> locally_finite_in top v`;;

let LOCALLY_FINITE_IN_REFINEMENT = `!top u (f:(A->bool)->(A->bool)).
        locally_finite_in top u /\ (!s. s IN u ==> f s SUBSET s)
        ==> locally_finite_in top {f s | s IN u}`;;

let LOCALLY_FINITE_IN_SUBTOPOLOGY = `!top s (u:(A->bool)->bool).
        locally_finite_in top u /\ (!t. t IN u ==> t SUBSET s)
        ==> locally_finite_in (subtopology top s) u`;;

let LOCALLY_FINITE_IN_SUBTOPOLOGY_EQ = `!top s (u:(A->bool)->bool).
        closed_in top s
        ==> (locally_finite_in (subtopology top s) u <=>
             locally_finite_in top u /\ (!t. t IN u ==> t SUBSET s))`;;

let CLOSED_IN_LOCALLY_FINITE_UNIONS = `!top f:(A->bool)->bool.
        (!s. s IN f ==> closed_in top s) /\ locally_finite_in top f
        ==> closed_in top (UNIONS f)`;;

let LOCALLY_FINITE_IN_CLOSURES = `!top f:(A->bool)->bool.
        locally_finite_in top f
        ==> locally_finite_in top {top closure_of s | s IN f}`;;

let CLOSED_IN_UNIONS_LOCALLY_FINITE_CLOSURES = `!top f:(A->bool)->bool.
        locally_finite_in top f
        ==> closed_in top (UNIONS {top closure_of s | s IN f})`;;

let CLOSURE_OF_UNIONS_SUBSET = `!top (f:(A->bool)->bool).
        UNIONS {top closure_of s | s IN f} SUBSET top closure_of (UNIONS f)`;;

let CLOSURE_OF_LOCALLY_FINITE_UNIONS = `!top (f:(A->bool)->bool).
        locally_finite_in top f
        ==> top closure_of (UNIONS f) = UNIONS {top closure_of s | s IN f}`;;

(* ------------------------------------------------------------------------- *)
(* Continuous maps.                                                          *)
(* ------------------------------------------------------------------------- *)

let continuous_map = new_definition
  `!top top' f:A->B.
     continuous_map (top,top')  f <=>
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!u. open_in top' u
          ==> open_in top {x | x IN topspace top /\ f x IN u})`;;

let CONTINUOUS_MAP = `!top top' f.
        continuous_map (top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !u. open_in top' u
            ==> open_in top {x | x IN topspace top /\ f x IN u}`;;

let CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE = `!top top' f:A->B. continuous_map (top,top')  f
                     ==> IMAGE f (topspace top) SUBSET topspace top'`;;

let CONTINUOUS_MAP_ON_EMPTY = `!top top' (f:A->B). topspace top = {} ==> continuous_map(top,top') f`;;

let CONTINUOUS_MAP_INTO_EMPTY = `!top top' (f:A->B).
        topspace top' = {}
        ==> (continuous_map(top,top') f <=> topspace top = {})`;;

let CONTINUOUS_MAP_CLOSED_IN = `!top top' f:A->B.
         continuous_map (top,top') f <=>
         (!x. x IN topspace top ==> f x IN topspace top') /\
         (!c. closed_in top' c
              ==> closed_in top {x | x IN topspace top /\ f x IN c})`;;

let OPEN_IN_CONTINUOUS_MAP_PREIMAGE = `!f:A->B top top' u.
        continuous_map (top,top') f /\ open_in top' u
        ==> open_in top {x | x IN topspace top /\ f x IN u}`;;

let CLOSED_IN_CONTINUOUS_MAP_PREIMAGE = `!f:A->B top top' c.
        continuous_map (top,top') f /\ closed_in top' c
        ==> closed_in top {x | x IN topspace top /\ f x IN c}`;;

let OPEN_IN_CONTINUOUS_MAP_PREIMAGE_GEN = `!f:A->B top top' u v.
        continuous_map (top,top') f /\ open_in top u /\ open_in top' v
        ==> open_in top {x | x IN u /\ f x IN v}`;;

let CLOSED_IN_CONTINUOUS_MAP_PREIMAGE_GEN = `!f:A->B top top' u v.
        continuous_map (top,top') f /\ closed_in top u /\ closed_in top' v
        ==> closed_in top {x | x IN u /\ f x IN v}`;;

let CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET = `!top top' (f:A->B) s.
        continuous_map (top,top') f
        ==> IMAGE f (top closure_of s) SUBSET top' closure_of IMAGE f s`;;

let CONTINUOUS_MAP_EQ_IMAGE_CLOSURE_SUBSET = `(!top top' f:A->B.
        continuous_map (top,top') f <=>
        !s. IMAGE f (top closure_of s) SUBSET top' closure_of IMAGE f s)`
and CONTINUOUS_MAP_EQ_IMAGE_CLOSURE_SUBSET_ALT = `(!top top' f:A->B.
        continuous_map (top,top') f <=>
        !s. s SUBSET topspace top
            ==> IMAGE f (top closure_of s) SUBSET top' closure_of IMAGE f s)`
and CONTINUOUS_MAP_EQ_IMAGE_CLOSURE_SUBSET_GEN = `(!top top' f:A->B.
        continuous_map (top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !s. IMAGE f (top closure_of s) SUBSET top' closure_of IMAGE f s)`;;

let CONTINUOUS_MAP_CLOSURE_PREIMAGE_SUBSET = `!top top' (f:A->B) t.
        continuous_map (top,top') f
        ==> top closure_of {x | x IN topspace top /\ f x IN t}
            SUBSET {x | x IN topspace top /\ f x IN top' closure_of t}`;;

let CONTINUOUS_MAP_EQ_CLOSURE_PREIMAGE_SUBSET = `(!top top' f:A->B.
        continuous_map (top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !t. top closure_of {x | x IN topspace top /\ f x IN t}
            SUBSET {x | x IN topspace top /\ f x IN top' closure_of t})`
and CONTINUOUS_MAP_EQ_CLOSURE_PREIMAGE_SUBSET_ALT = `(!top top' f:A->B.
        continuous_map (top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !t. t SUBSET topspace top'
            ==> top closure_of {x | x IN topspace top /\ f x IN t}
                SUBSET {x | x IN topspace top /\ f x IN top' closure_of t})`;;

let CONTINUOUS_MAP_INTERIOR_PREIMAGE_SUBSET = `!top top' (f:A->B) t.
        continuous_map (top,top') f
        ==> {x | x IN topspace top /\ f x IN top' interior_of t} SUBSET
            top interior_of {x | x IN topspace top /\ f x IN t}`;;

let CONTINUOUS_MAP_EQ_INTERIOR_PREIMAGE_SUBSET = `(!top top' f:A->B.
        continuous_map (top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !t. {x | x IN topspace top /\ f x IN top' interior_of t} SUBSET
            top interior_of {x | x IN topspace top /\ f x IN t})`
and CONTINUOUS_MAP_EQ_INTERIOR_PREIMAGE_SUBSET_ALT = `(!top top' f:A->B.
        continuous_map (top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !t. t SUBSET topspace top'
            ==> {x | x IN topspace top /\ f x IN top' interior_of t} SUBSET
                top interior_of {x | x IN topspace top /\ f x IN t})`;;

let CONTINUOUS_MAP_FRONTIER_FRONTIER_PREIMAGE_SUBSET = `!top top' (f:A->B) t.
        continuous_map (top,top') f
        ==> top frontier_of {x | x IN topspace top /\ f x IN t}
            SUBSET {x | x IN topspace top /\ f x IN top' frontier_of t}`;;

let CONTINUOUS_MAP_ID = `!top:A topology. continuous_map (top,top) (\x. x)`;;

let TOPOLOGY_FINER_CONTINUOUS_ID = `!top top':A topology.
        topspace top' = topspace top
        ==> ((!s. open_in top s ==> open_in top' s) <=>
             continuous_map (top',top) (\x. x))`;;

let CONTINUOUS_MAP_CONST = `!top1:A topology top2:B topology c.
       continuous_map (top1,top2) (\x. c) <=>
       topspace top1 = {} \/ c IN topspace top2`;;

let CONTINUOUS_MAP_COMPOSE = `!top top' top'' f:A->B g:B->C.
        continuous_map (top,top') f /\ continuous_map (top',top'') g
        ==> continuous_map (top,top'') (g o f)`;;

let CONTINUOUS_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ continuous_map (top,top') f
        ==> continuous_map (top,top') g`;;

let RESTRICTION_CONTINUOUS_MAP = `!top top' f:A->B s.
        topspace top SUBSET s
        ==> (continuous_map (top,top') (RESTRICTION s f) <=>
             continuous_map (top,top') f)`;;

let CONTINUOUS_MAP_IN_SUBTOPOLOGY = `!top top' s f:A->B.
     continuous_map (top,subtopology top' s) f <=>
     continuous_map (top,top')  f /\ IMAGE f (topspace top) SUBSET s`;;

let CONTINUOUS_MAP_FROM_SUBTOPOLOGY = `!top top' f:A->B s.
        continuous_map (top,top') f
        ==> continuous_map (subtopology top s,top') f`;;

let CONTINUOUS_MAP_INTO_FULLTOPOLOGY = `!top top' f:A->B t.
        continuous_map (top,subtopology top' t) f
        ==> continuous_map (top,top') f`;;

let CONTINUOUS_MAP_INTO_SUBTOPOLOGY = `!top top' f:A->B t.
        continuous_map (top,top') f /\
        IMAGE f (topspace top) SUBSET t
        ==> continuous_map (top,subtopology top' t) f`;;

let CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO = `!top top' f s t.
           continuous_map (subtopology top t,top') f /\ s SUBSET t
           ==> continuous_map (subtopology top s,top') f`;;

let CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY = `!(f:A->B) top u.
        continuous_map (discrete_topology u,top) f <=>
        IMAGE f u SUBSET topspace top`;;

let PASTING_LEMMA = `!top top' (f:K->A->B) g t k.
        (!i. i IN k
             ==> open_in top (t i) /\
                 continuous_map(subtopology top (t i),top') (f i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN topspace top INTER t i INTER t j
                 ==> f i x = f j x) /\
        (!x. x IN topspace top ==> ?j. j IN k /\ x IN t j /\ g x = f j x)
        ==> continuous_map(top,top') g`;;

let PASTING_LEMMA_EXISTS = `!top top' (f:K->A->B) t k.
        topspace top SUBSET UNIONS {t i | i IN k} /\
        (!i. i IN k
             ==> open_in top (t i) /\
                 continuous_map(subtopology top (t i),top') (f i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN topspace top INTER t i INTER t j
                 ==> f i x = f j x)
        ==> ?g. continuous_map(top,top') g /\
                !x i. i IN k /\ x IN topspace top INTER t i ==> g x = f i x`;;

let PASTING_LEMMA_LOCALLY_FINITE = `!top top' (f:K->A->B) g t k.
        (!x. x IN topspace top
             ==> ?v. open_in top v /\ x IN v /\
                     FINITE {i | i IN k /\ ~(t i INTER v = {})}) /\
        (!i. i IN k
             ==> closed_in top (t i) /\
                 continuous_map(subtopology top (t i),top') (f i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN topspace top INTER t i INTER t j
                 ==> f i x = f j x) /\
        (!x. x IN topspace top ==> ?j. j IN k /\ x IN t j /\ g x = f j x)
        ==> continuous_map(top,top') g`;;

let PASTING_LEMMA_EXISTS_LOCALLY_FINITE = `!top top' (f:K->A->B) t k.
        (!x. x IN topspace top
             ==> ?v. open_in top v /\ x IN v /\
                     FINITE {i | i IN k /\ ~(t i INTER v = {})}) /\
        topspace top SUBSET UNIONS {t i | i IN k} /\
        (!i. i IN k
             ==> closed_in top (t i) /\
                 continuous_map(subtopology top (t i),top') (f i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN topspace top INTER t i INTER t j
                 ==> f i x = f j x)
        ==> ?g. continuous_map(top,top') g /\
                !x i. i IN k /\ x IN topspace top INTER t i ==> g x = f i x`;;

let PASTING_LEMMA_CLOSED = `!top top' (f:K->A->B) g t k.
        FINITE k /\
        (!i. i IN k
             ==> closed_in top (t i) /\
                 continuous_map(subtopology top (t i),top') (f i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN topspace top INTER t i INTER t j
                 ==> f i x = f j x) /\
        (!x. x IN topspace top ==> ?j. j IN k /\ x IN t j /\ g x = f j x)
        ==> continuous_map(top,top') g`;;

let PASTING_LEMMA_EXISTS_CLOSED = `!top top' (f:K->A->B) t k.
        FINITE k /\
        topspace top SUBSET UNIONS {t i | i IN k} /\
        (!i. i IN k
             ==> closed_in top (t i) /\
                 continuous_map(subtopology top (t i),top') (f i)) /\
        (!i j x. i IN k /\ j IN k /\ x IN topspace top INTER t i INTER t j
                 ==> f i x = f j x)
        ==> ?g. continuous_map(top,top') g /\
                !x i. i IN k /\ x IN topspace top INTER t i ==> g x = f i x`;;

let CONTINUOUS_MAP_CASES = `!top top' P f g:A->B.
        continuous_map (subtopology top (top closure_of {x | P x}),top') f /\
        continuous_map (subtopology top (top closure_of {x | ~P x}),top') g /\
        (!x. x IN top frontier_of {x | P x} ==> f x = g x)
        ==> continuous_map (top,top') (\x. if P x then f x else g x)`;;

let CONTINUOUS_MAP_CASES_ALT = `!top top' P f g:A->B.
        continuous_map (subtopology top
         (top closure_of {x | x IN topspace top /\ P x}),top') f /\
        continuous_map (subtopology top
         (top closure_of {x | x IN topspace top /\ ~P x}),top') g /\
        (!x. x IN top frontier_of {x | x IN topspace top /\ P x} ==> f x = g x)
        ==> continuous_map (top,top') (\x. if P x then f x else g x)`;;

let CONTINUOUS_MAP_CASES_FUNCTION = `!top top' top'' (p:A->C) f (g:A->B) u.
        continuous_map (top,top'') p /\
        continuous_map (subtopology top
         {x | x IN topspace top /\ p x IN top'' closure_of u},top') f /\
        continuous_map (subtopology top
         {x | x IN topspace top /\
              p x IN top'' closure_of (topspace top'' DIFF u)},top') g /\
        (!x. x IN topspace top /\ p x IN top'' frontier_of u ==> f x = g x)
        ==> continuous_map (top,top') (\x. if p x IN u then f x else g x)`;;

let CONTINUOUS_MAP_SEPARATED_UNION = `!top top' (f:A->B) s t.
        continuous_map (subtopology top s,top') f /\
        continuous_map (subtopology top t,top') f /\
        DISJOINT s (top closure_of t) /\
        DISJOINT t (top closure_of s)
        ==> continuous_map (subtopology top (s UNION t),top') f`;;

(* ------------------------------------------------------------------------- *)
(* Open and closed maps (not a priori assumed continuous).                   *)
(* ------------------------------------------------------------------------- *)

let open_map = new_definition
 `open_map (top1,top2) (f:A->B) <=>
  !u. open_in top1 u ==> open_in top2 (IMAGE f u)`;;

let closed_map = new_definition
 `closed_map (top1,top2) (f:A->B) <=>
  !u. closed_in top1 u ==> closed_in top2 (IMAGE f u)`;;

let OPEN_MAP_IMP_SUBSET_TOPSPACE = `!top1 top2 f:A->B.
        open_map (top1,top2) f
        ==> IMAGE f (topspace top1) SUBSET topspace top2`;;

let OPEN_MAP_IMP_SUBSET = `!top1 top2 f:A->B s.
        open_map (top1,top2) f /\ s SUBSET topspace top1
        ==> IMAGE f s SUBSET topspace top2`;;

let TOPOLOGY_FINER_OPEN_ID = `!top top':A topology.
        (!s. open_in top s ==> open_in top' s) <=>
        open_map (top,top') (\x. x)`;;

let OPEN_MAP_ID = `!top:A topology. open_map(top,top) (\x. x)`;;

let OPEN_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ open_map (top,top') f
        ==> open_map (top,top') g`;;

let OPEN_MAP_INCLUSION_EQ = `!top s:A->bool.
        open_map (subtopology top s,top) (\x. x) <=>
        open_in top (topspace top INTER s)`;;

let OPEN_MAP_INCLUSION = `!top s:A->bool.
        open_in top s ==> open_map (subtopology top s,top) (\x. x)`;;

let OPEN_MAP_COMPOSE = `!top top' top'' (f:A->B) (g:B->C).
        open_map(top,top') f /\ open_map(top',top'') g
        ==> open_map(top,top'') (g o f)`;;

let CLOSED_MAP_IMP_SUBSET_TOPSPACE = `!top1 top2 f:A->B.
        closed_map (top1,top2) f
        ==> IMAGE f (topspace top1) SUBSET topspace top2`;;

let CLOSED_MAP_IMP_SUBSET = `!top1 top2 f:A->B s.
        closed_map (top1,top2) f /\ s SUBSET topspace top1
        ==> IMAGE f s SUBSET topspace top2`;;

let TOPOLOGY_FINER_CLOSED_ID = `!top top':A topology.
        (!s. closed_in top s ==> closed_in top' s) <=>
        closed_map (top,top') (\x. x)`;;

let CLOSED_MAP_ID = `!top:A topology. closed_map(top,top) (\x. x)`;;

let CLOSED_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ closed_map (top,top') f
        ==> closed_map (top,top') g`;;

let CLOSED_MAP_COMPOSE = `!top top' top'' (f:A->B) (g:B->C).
        closed_map(top,top') f /\ closed_map(top',top'') g
        ==> closed_map(top,top'') (g o f)`;;

let CLOSED_MAP_INCLUSION_EQ = `!top s:A->bool.
        closed_map (subtopology top s,top) (\x. x) <=>
        closed_in top (topspace top INTER s)`;;

let CLOSED_MAP_INCLUSION = `!top s:A->bool.
        closed_in top s ==> closed_map (subtopology top s,top) (\x. x)`;;

let OPEN_MAP_INTO_SUBTOPOLOGY = `!top top' (f:A->B) s.
        open_map (top,top') f /\ IMAGE f (topspace top) SUBSET s
        ==> open_map (top,subtopology top' s) f`;;

let CLOSED_MAP_INTO_SUBTOPOLOGY = `!top top' (f:A->B) s.
        closed_map (top,top') f /\ IMAGE f (topspace top) SUBSET s
        ==> closed_map (top,subtopology top' s) f`;;

let OPEN_MAP_INTO_DISCRETE_TOPOLOGY = `!(f:A->B) top u.
        open_map (top,discrete_topology u) f <=>
        IMAGE f (topspace top) SUBSET u`;;

let CLOSED_MAP_INTO_DISCRETE_TOPOLOGY = `!(f:A->B) top u.
        closed_map (top,discrete_topology u) f <=>
        IMAGE f (topspace top) SUBSET u`;;

let BIJECTIVE_OPEN_IMP_CLOSED_MAP = `!top top' f:A->B.
        open_map (top,top') f /\ IMAGE f (topspace top) = topspace top' /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y)
        ==> closed_map (top,top') f`;;

let BIJECTIVE_CLOSED_IMP_OPEN_MAP = `!top top' f:A->B.
        closed_map (top,top') f /\ IMAGE f (topspace top) = topspace top' /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y)
        ==> open_map (top,top') f`;;

let OPEN_MAP_ON_EMPTY = `!top top' (f:A->B). topspace top = {} ==> open_map(top,top') f`;;

let CLOSED_MAP_ON_EMPTY = `!top top' (f:A->B). topspace top = {} ==> closed_map(top,top') f`;;

let OPEN_MAP_FROM_SUBTOPOLOGY = `!top top' (f:A->B) u.
        open_map(top,top') f /\ open_in top u
        ==> open_map (subtopology top u,top') f`;;

let CLOSED_MAP_FROM_SUBTOPOLOGY = `!top top' (f:A->B) u.
        closed_map(top,top') f /\ closed_in top u
        ==> closed_map (subtopology top u,top') f`;;

let OPEN_MAP_RESTRICTION = `!top top' (f:A->B) u v.
        open_map(top,top') f /\ {x | x IN topspace top /\ f x IN v} = u
        ==> open_map (subtopology top u,subtopology top' v) f`;;

let CLOSED_MAP_RESTRICTION = `!top top' (f:A->B) u v.
        closed_map(top,top') f /\ {x | x IN topspace top /\ f x IN v} = u
        ==> closed_map (subtopology top u,subtopology top' v) f`;;

let CLOSED_MAP_CLOSURE_OF_IMAGE = `!top top' f:A->B.
        closed_map (top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !s. s SUBSET topspace top
            ==> top' closure_of (IMAGE f s) SUBSET IMAGE f (top closure_of s)`;;

let OPEN_MAP_INTERIOR_OF_IMAGE_SUBSET = `(!top top' f:A->B.
        open_map (top,top') f <=>
        !s. IMAGE f (top interior_of s) SUBSET
            top' interior_of (IMAGE f s))`
and OPEN_MAP_INTERIOR_OF_IMAGE_SUBSET_ALT = `(!top top' f:A->B.
      open_map (top,top') f <=>
      !s. s SUBSET topspace top
          ==> IMAGE f (top interior_of s) SUBSET
              top' interior_of (IMAGE f s))`
and OPEN_MAP_INTERIOR_OF_IMAGE_SUBSET_GEN = `(!top top' f:A->B.
      open_map (top,top') f <=>
      IMAGE f (topspace top) SUBSET topspace top' /\
      !s. IMAGE f (top interior_of s) SUBSET top' interior_of (IMAGE f s))`;;

let OPEN_MAP_PREIMAGE_NEIGHBOURHOOD = `!top top' (f:A->B).
        open_map(top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !u t. closed_in top u /\ t SUBSET topspace top' /\
              {x | x IN topspace top /\ f x IN t} SUBSET u
              ==> ?v. closed_in top' v /\ t SUBSET v /\
                      {x | x IN topspace top /\ f x IN v} SUBSET u`;;

let CLOSED_MAP_PREIMAGE_NEIGHBOURHOOD = `!top top' (f:A->B).
        closed_map(top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !u t. open_in top u /\ t SUBSET topspace top' /\
              {x | x IN topspace top /\ f x IN t} SUBSET u
              ==> ?v. open_in top' v /\ t SUBSET v /\
                      {x | x IN topspace top /\ f x IN v} SUBSET u`;;

let CLOSED_MAP_FIBRE_NEIGHBOURHOOD = `!top top' (f:A->B).
        closed_map(top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !u y. open_in top u /\ y IN topspace top' /\
              {x | x IN topspace top /\ f x = y} SUBSET u
              ==> ?v. open_in top' v /\ y IN v /\
                      {x | x IN topspace top /\ f x IN v} SUBSET u`;;

let OPEN_MAP_IN_SUBTOPOLOGY = `!top top' s (f:A->B).
        open_in top' s
        ==> (open_map(top,subtopology top' s) f <=>
             open_map(top,top') f /\ IMAGE f (topspace top) SUBSET s)`;;

let OPEN_MAP_FROM_OPEN_SUBTOPOLOGY = `!top top' s (f:A->B).
        open_in top' s /\ open_map(top,subtopology top' s) f
        ==> open_map(top,top') f`;;

let CLOSED_MAP_IN_SUBTOPOLOGY = `!top top' s (f:A->B).
        closed_in top' s
        ==> (closed_map(top,subtopology top' s) f <=>
             closed_map(top,top') f /\ IMAGE f (topspace top) SUBSET s)`;;

let CLOSED_MAP_FROM_CLOSED_SUBTOPOLOGY = `!top top' s (f:A->B).
        closed_in top' s /\ closed_map(top,subtopology top' s) f
        ==> closed_map(top,top') f`;;

let CLOSED_MAP_FROM_COMPOSITION_LEFT = `!top top' top'' (f:A->B) (g:B->C).
        closed_map(top,top'') (g o f) /\
        continuous_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> closed_map(top',top'') g`;;

let CLOSED_MAP_FROM_COMPOSITION_RIGHT = `!top top' top'' (f:A->B) (g:B->C).
        closed_map(top,top'') (g o f) /\
        IMAGE f (topspace top) SUBSET topspace top' /\
        continuous_map(top',top'') g /\
        (!x y. x IN topspace top' /\ y IN topspace top' /\ g x = g y
               ==> x = y)
        ==> closed_map(top,top') f`;;

let OPEN_MAP_FROM_COMPOSITION_LEFT = `!top top' top'' (f:A->B) (g:B->C).
        open_map(top,top'') (g o f) /\
        continuous_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> open_map(top',top'') g`;;

let OPEN_MAP_FROM_COMPOSITION_RIGHT = `!top top' top'' (f:A->B) (g:B->C).
        open_map(top,top'') (g o f) /\
        IMAGE f (topspace top) SUBSET topspace top' /\
        continuous_map(top',top'') g /\
        (!x y. x IN topspace top' /\ y IN topspace top' /\ g x = g y
               ==> x = y)
        ==> open_map(top,top') f`;;

let CLOSED_MAP_CONST = `!(top:A topology) top' (c:B).
        closed_map(top,top') (\x. c) <=>
        topspace top = {} \/ closed_in top' {c}`;;

let DISCRETE_SPACE_OPEN_MAP_IMAGE = `!top top' (f:A->B).
        open_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        discrete_space top
        ==> discrete_space top'`;;

let DISCRETE_SPACE_CLOSED_MAP_IMAGE = `!top top' (f:A->B).
        closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        discrete_space top
        ==> discrete_space top'`;;

(* ------------------------------------------------------------------------- *)
(* Quotient maps.                                                            *)
(* ------------------------------------------------------------------------- *)

let quotient_map = new_definition
 `quotient_map (top,top') (f:A->B) <=>
        IMAGE f (topspace top) = topspace top' /\
        !u. u SUBSET topspace top'
            ==> (open_in top {x | x IN topspace top /\ f x IN u} <=>
                 open_in top' u)`;;

let QUOTIENT_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ quotient_map (top,top') f
        ==> quotient_map (top,top') g`;;

let QUOTIENT_MAP_COMPOSE = `!top top' top'' (f:A->B) (g:B->C).
        quotient_map(top,top') f /\ quotient_map(top',top'') g
        ==> quotient_map(top,top'') (g o f)`;;

let QUOTIENT_MAP_FROM_COMPOSITION = `!top top' top'' (f:A->B) (g:B->C).
        continuous_map(top,top') f /\ continuous_map(top',top'') g /\
        quotient_map(top,top'') (g o f)
        ==> quotient_map(top',top'') g`;;

let QUOTIENT_IMP_CONTINUOUS_MAP = `!top top' f:A->B.
        quotient_map (top,top') f ==> continuous_map (top,top') f`;;

let QUOTIENT_IMP_SURJECTIVE_MAP = `!top top' f:A->B.
        quotient_map (top,top') f ==> IMAGE f (topspace top) = topspace top'`;;

let QUOTIENT_MAP = `!top top' f:A->B.
        quotient_map (top,top') f <=>
        IMAGE f (topspace top) = topspace top' /\
        !u. u SUBSET topspace top'
            ==> (closed_in top {x | x IN topspace top /\ f x IN u} <=>
                 closed_in top' u)`;;

let CONTINUOUS_OPEN_IMP_QUOTIENT_MAP = `!top top' f:A->B.
        continuous_map (top,top') f /\ open_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> quotient_map (top,top') f`;;

let CONTINUOUS_CLOSED_IMP_QUOTIENT_MAP = `!top top' f:A->B.
        continuous_map (top,top') f /\ closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> quotient_map (top,top') f`;;

let CONTINUOUS_OPEN_QUOTIENT_MAP = `!top top' f:A->B.
        continuous_map (top,top') f /\
        open_map (top,top') f
        ==> (quotient_map (top,top') f <=>
             IMAGE f (topspace top) = topspace top')`;;

let CONTINUOUS_CLOSED_QUOTIENT_MAP = `!top top' f:A->B.
        continuous_map (top,top') f /\
        closed_map (top,top') f
        ==> (quotient_map (top,top') f <=>
             IMAGE f (topspace top) = topspace top')`;;

let INJECTIVE_QUOTIENT_MAP = `!top top' f:A->B.
        (!x y. x IN topspace top /\ y IN topspace top
               ==> (f x = f y <=> x = y))
        ==> (quotient_map (top,top') f <=>
             continuous_map (top,top') f /\
             open_map (top,top') f /\
             closed_map (top,top') f /\
             IMAGE f (topspace top) = topspace top')`;;

let CONTINUOUS_COMPOSE_QUOTIENT_MAP = `!top top' top'' (f:A->B) (g:B->C).
        quotient_map (top,top') f /\
        continuous_map (top,top'') (g o f)
        ==> continuous_map (top',top'') g`;;

let CONTINUOUS_COMPOSE_QUOTIENT_MAP_EQ = `!top top' top'' (f:A->B) (g:B->C).
        quotient_map (top,top') f
        ==> (continuous_map (top,top'') (g o f) <=>
             continuous_map (top',top'') g)`;;

let QUOTIENT_MAP_COMPOSE_EQ = `!top top' top'' (f:A->B) (g:B->C).
        quotient_map(top,top') f
        ==> (quotient_map(top,top'') (g o f) <=> quotient_map(top',top'') g)`;;

let QUOTIENT_MAP_RESTRICTION = `!top top' (f:A->B) u v.
        quotient_map(top,top') f /\
        (open_in top' v \/ closed_in top' v) /\
        {x | x IN topspace top /\ f x IN v} = u
        ==> quotient_map (subtopology top u,subtopology top' v) f`;;

let QUOTIENT_MAP_SATURATED_OPEN = `!top top' f:A->B.
        quotient_map (top,top') f <=>
        continuous_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        !u. open_in top u /\
            {x | x IN topspace top /\ f x IN IMAGE f u} SUBSET u
            ==> open_in top' (IMAGE f u)`;;

let QUOTIENT_MAP_SATURATED_CLOSED = `!top top' f:A->B.
        quotient_map (top,top') f <=>
        continuous_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        !u. closed_in top u /\
            {x | x IN topspace top /\ f x IN IMAGE f u} SUBSET u
            ==> closed_in top' (IMAGE f u)`;;

let QUOTIENT_MAP_ONTO_IMAGE = `!top top' (f:A->B).
        IMAGE f (topspace top) SUBSET topspace top' /\
        (!u. u SUBSET topspace top'
             ==> (open_in top {x | x IN topspace top /\ f x IN u} <=>
                  open_in top' u))
        ==> quotient_map(top,subtopology top' (IMAGE f (topspace top))) f`;;

let QUOTIENT_MAP_LIFT_EXISTS = `!top top' top'' (f:A->B) (h:A->C).
        quotient_map (top,top') f /\
        continuous_map (top,top'') h /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y
               ==> h x = h y)
        ==> ?g. continuous_map (top',top'') g /\
                IMAGE g (topspace top') = IMAGE h (topspace top) /\
                !x. x IN topspace top ==> g(f x) = h x`;;

let DISCRETE_SPACE_QUOTIENT_MAP_IMAGE = `!top top' (q:A->B).
        quotient_map (top,top') q /\ discrete_space top
        ==> discrete_space top'`;;

(* ------------------------------------------------------------------------- *)
(* A binary product topology where the two types can be different.           *)
(* ------------------------------------------------------------------------- *)

let prod_topology = new_definition
 `prod_topology (top1:A topology) (top2:B topology) =
    topology (ARBITRARY UNION_OF
               {s CROSS t | open_in top1 s /\ open_in top2 t})`;;

let OPEN_IN_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
     open_in (prod_topology top1 top2) =
     (ARBITRARY UNION_OF {s CROSS t | open_in top1 s /\ open_in top2 t})`;;

let TOPSPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        topspace(prod_topology top1 top2) =
        topspace top1 CROSS topspace top2`;;

let SUBTOPOLOGY_CROSS = `!top1:A topology top2:B topology s t.
        subtopology (prod_topology top1 top2) (s CROSS t) =
        prod_topology (subtopology top1 s) (subtopology top2 t)`;;

let PROD_TOPOLOGY_SUBTOPOLOGY = `(!(top:A topology) (top':B topology) s.
        prod_topology (subtopology top s) top' =
        subtopology (prod_topology top top') (s CROSS topspace top')) /\
   (!(top:A topology) (top':B topology) t.
        prod_topology top (subtopology top' t) =
        subtopology (prod_topology top top') (topspace top CROSS t))`;;

let PROD_TOPOLOGY_DISCRETE_TOPOLOGY = `!s:A->bool t:B->bool.
        prod_topology (discrete_topology s) (discrete_topology t) =
        discrete_topology (s CROSS t)`;;

let OPEN_IN_PROD_TOPOLOGY_ALT = `!top1:A topology top2:B topology s.
        open_in (prod_topology top1 top2) s <=>
        !x y. (x,y) IN s
              ==> ?u v. open_in top1 u /\ open_in top2 v /\
                        x IN u /\ y IN v /\ u CROSS v SUBSET s`;;

let OPEN_IN_CROSS = `!top1:A topology top2:B topology s t.
        open_in (prod_topology top1 top2) (s CROSS t) <=>
        s = {} \/ t = {} \/ open_in top1 s /\ open_in top2 t`;;

let CLOSURE_OF_CROSS = `!top1:A topology top2:B topology s t.
        (prod_topology top1 top2) closure_of (s CROSS t) =
        (top1 closure_of s) CROSS (top2 closure_of t)`;;

let CLOSED_IN_CROSS = `!top1:A topology top2:B topology s t.
        closed_in (prod_topology top1 top2) (s CROSS t) <=>
        s = {} \/ t = {} \/ closed_in top1 s /\ closed_in top2 t`;;

let INTERIOR_OF_CROSS = `!top1:A topology top2:B topology s t.
        (prod_topology top1 top2) interior_of (s CROSS t) =
        (top1 interior_of s) CROSS (top2 interior_of t)`;;

let DISCRETE_SPACE_PROD_TOPOLOGY = `!(top1:A topology) (top2:B topology).
        discrete_space(prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        discrete_space top1 /\ discrete_space top2`;;

let CONTINUOUS_MAP_PAIRWISE = `!top top1 top2 f:A->B#C.
        continuous_map (top,prod_topology top1 top2) f <=>
        continuous_map (top,top1) (FST o f) /\
        continuous_map (top,top2) (SND o f)`;;

let CONTINUOUS_MAP_PAIRED = `!top top1 top2 (f:A->B) (g:A->C).
        continuous_map (top,prod_topology top1 top2) (\x. f x,g x) <=>
        continuous_map(top,top1) f /\ continuous_map(top,top2) g`;;

let CONTINUOUS_MAP_FST = `(!top1:A topology top2:B topology.
        continuous_map (prod_topology top1 top2,top1) FST)`
and CONTINUOUS_MAP_SND = `(!top1:A topology top2:B topology.
        continuous_map (prod_topology top1 top2,top2) SND)`;;

let CONTINUOUS_MAP_FST_OF = `!top top1 top2 f:A->B#C.
         continuous_map (top,prod_topology top1 top2) f
         ==> continuous_map (top,top1) (\x. FST(f x))`;;

let CONTINUOUS_MAP_SND_OF = `!top top1 top2 f:A->B#C.
         continuous_map (top,prod_topology top1 top2) f
         ==> continuous_map (top,top2) (\x. SND(f x))`;;

let OPEN_MAP_FST = `(!top1:A topology top2:B topology.
      open_map (prod_topology top1 top2,top1) FST)`
and OPEN_MAP_SND = `(!top1:A topology top2:B topology.
      open_map (prod_topology top1 top2,top2) SND)`;;

let QUOTIENT_MAP_FST = `!top:A topology top':B topology.
        quotient_map(prod_topology top top',top) FST <=>
        (topspace top' = {} ==> topspace top = {})`;;

let QUOTIENT_MAP_SND = `!top:A topology top':B topology.
        quotient_map(prod_topology top top',top') SND <=>
        (topspace top = {} ==> topspace top' = {})`;;

let CONTINUOUS_MAP_OF_FST = `!top:C topology top1:A topology top2:B topology f.
        continuous_map (prod_topology top1 top2,top) (\x. f(FST x)) <=>
        topspace top2 = {} \/ continuous_map (top1,top) f`;;

let CONTINUOUS_MAP_OF_SND = `!top:C topology top1:A topology top2:B topology f.
        continuous_map (prod_topology top1 top2,top) (\x. f(SND x)) <=>
        topspace top1 = {} \/ continuous_map (top2,top) f`;;

let CONTINUOUS_MAP_PROD = `!top1 top2 top3 top4 (f:A->B) (g:C->D).
        continuous_map (prod_topology top1 top2,prod_topology top3 top4)
                       (\(x,y). f x,g y) <=>
        topspace(prod_topology top1 top2) = {} \/
        continuous_map (top1,top3) f /\ continuous_map (top2,top4) g`;;

let OPEN_MAP_PROD = `!top1 top1' top2 top2' (f:A->C) (g:B->D).
        open_map (prod_topology top1 top2,prod_topology top1' top2')
                 (\(x,y). f x,g y) <=>
        topspace(prod_topology top1 top2) = {} \/
        open_map (top1,top1') f /\ open_map (top2,top2') g`;;

let IN_PROD_TOPOLOGY_CLOSURE_OF = `!top1 top2 s z:A#B.
        z IN (prod_topology top1 top2) closure_of s
        ==> FST z IN top1 closure_of (IMAGE FST s) /\
            SND z IN top2 closure_of (IMAGE SND s)`;;

let CLOSED_MAP_PROD = `!top1 top1' top2 top2' (f:A->C) (g:B->D).
        closed_map (prod_topology top1 top2,prod_topology top1' top2')
                   (\(x,y). f x,g y)
        ==> topspace(prod_topology top1 top2) = {} \/
            closed_map (top1,top1') f /\ closed_map (top2,top2') g`;;

let PROD_TOPOLOGY_EQ = `!(top1:A topology) (top2:B topology) top1' top2'.
        prod_topology top1 top2 = prod_topology top1' top2' <=>
        topspace(prod_topology top1 top2) = {} /\
        topspace(prod_topology top1' top2') = {} \/
        top1 = top1' /\ top2 = top2'`;;

(* ------------------------------------------------------------------------- *)
(* The usual (Tychonoff) product topology for general cartesian products.    *)
(* ------------------------------------------------------------------------- *)

let product_topology = new_definition
 `product_topology t (tops:K->A topology) =
        topology
          (ARBITRARY UNION_OF
             ((FINITE INTERSECTION_OF
              { {x:K->A | x k IN u} | k,u | k IN t /\ open_in (tops k) u})
              relative_to {x | EXTENSIONAL t x /\
                               !k. k IN t ==> x k IN topspace(tops k)}))`;;

let TOPSPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) t.
        topspace (product_topology t tops) =
        cartesian_product t (topspace o tops)`;;

let TOPSPACE_PRODUCT_TOPOLOGY_ALT = `!(tops:K->A topology) t.
        topspace (product_topology t tops) =
        {x | EXTENSIONAL t x /\ !k. k IN t ==> x k IN topspace(tops k)}`;;

let PRODUCT_TOPOLOGY_EMPTY_DISCRETE = `!tops:K->A topology.
        product_topology {} tops = discrete_topology {(\x. ARB)}`;;

let OPEN_IN_PRODUCT_TOPOLOGY = `!(tops:K->A topology) t.
        open_in (product_topology t tops) =
        ARBITRARY UNION_OF
          ((FINITE INTERSECTION_OF
           { {x:K->A | x k IN u} | k,u | k IN t /\ open_in (tops k) u})
           relative_to topspace (product_topology t tops))`;;

let SUBTOPOLOGY_CARTESIAN_PRODUCT = `!tops:K->A topology s k.
        subtopology (product_topology k tops) (cartesian_product k s) =
        product_topology k (\i. subtopology (tops i) (s i))`;;

let PRODUCT_TOPOLOGY_SUBBASE_ALT = `!tops:K->A topology.
        ((FINITE INTERSECTION_OF
          { {x | x k IN u} | k,u | k IN t /\ open_in (tops k) u})
         relative_to topspace (product_topology t tops)) =
        ((FINITE INTERSECTION_OF
         { {x | x k IN u} | k,u |
           k IN t /\ open_in (tops k) u /\ u PSUBSET topspace (tops k)})
         relative_to topspace (product_topology t tops))`;;

let PRODUCT_TOPOLOGY_BASE_ALT = `!(tops:K->A topology) k.
        FINITE INTERSECTION_OF {{x | x i IN u} | i IN k /\ open_in (tops i) u}
        relative_to topspace(product_topology k tops) =
        { cartesian_product k u | u |
          FINITE {i | i IN k /\ ~(u i = topspace(tops i))} /\
          !i. i IN k ==> open_in (tops i) (u i)}`;;

let OPEN_IN_PRODUCT_TOPOLOGY_ALT = `!k (tops:K->A topology) s.
         open_in (product_topology k tops) s <=>
         !x. x IN s
             ==> ?u. FINITE {i | i IN k /\ ~(u i = topspace(tops i))} /\
                     (!i. i IN k ==> open_in (tops i) (u i)) /\
                     x IN cartesian_product k u /\
                     cartesian_product k u SUBSET s`;;

let OPEN_IN_PRODUCT_TOPOLOGY_ALT_EXPAND = `!k (tops:K->A topology) s.
        open_in (product_topology k tops) s <=>
        s SUBSET topspace(product_topology k tops) /\
        !x. x IN s
            ==> ?u. FINITE {i | i IN k /\ ~(u i = topspace(tops i))} /\
                    (!i. i IN k ==> open_in (tops i) (u i) /\ x i IN u i) /\
                    cartesian_product k u SUBSET s`;;

let CONTINUOUS_MAP_COMPONENTWISE = `!top:A topology (tops:K->B topology) t f.
       continuous_map (top,product_topology t tops) f <=>
       IMAGE f (topspace top) SUBSET EXTENSIONAL t /\
       !k. k IN t ==> continuous_map (top,tops k) (\x. f x k)`;;

let CONTINUOUS_MAP_COMPONENTWISE_UNIV = `!top tops (f:A->K->B).
         continuous_map (top,product_topology (:K) tops) f <=>
         !k. continuous_map (top,tops k) (\x. f x k)`;;

let CONTINUOUS_MAP_PRODUCT_PROJECTION = `!(tops:K->A topology) t k.
        k IN t ==> continuous_map (product_topology t tops,tops k) (\x. x k)`;;

let OPEN_MAP_PRODUCT_PROJECTION = `!(tops:K->A topology) t k.
        k IN t ==> open_map (product_topology t tops,tops k) (\x. x k)`;;

let OPEN_IN_CARTESIAN_PRODUCT_GEN = `!(tops:K->A topology) s k.
        open_in (product_topology k tops) (cartesian_product k s) <=>
        cartesian_product k s = {} \/
        FINITE {i | i IN k /\ ~(s i = topspace(tops i))} /\
        (!i. i IN k ==> open_in (tops i) (s i))`;;

let OPEN_IN_CARTESIAN_PRODUCT = `!(tops:K->A topology) (s:K->A->bool) k.
        FINITE k
        ==> (open_in (product_topology k tops) (cartesian_product k s) <=>
             cartesian_product k s = {} \/
             (!i. i IN k ==> open_in (tops i) (s i)))`;;

let PRODUCT_TOPOLOGY_EMPTY = `(!tops:K->A topology.
        product_topology {} tops = topology {{},{\k. ARB}})`
and OPEN_IN_PRODUCT_TOPOLOGY_EMPTY = `(!tops:K->A topology s.
        open_in (product_topology {} tops) s <=> s IN {{},{\k. ARB}})`;;

let TOPSPACE_PRODUCT_TOPOLOGY_EMPTY = `!tops:K->A topology.
        topspace(product_topology {} tops) = {\k. ARB}`;;

let CLOSURE_OF_CARTESIAN_PRODUCT = `!k tops s:K->A->bool.
        (product_topology k tops) closure_of (cartesian_product k s) =
        cartesian_product k (\i. (tops i) closure_of (s i))`;;

let CLOSED_IN_CARTESIAN_PRODUCT = `!(tops:K->A topology) (s:K->A->bool) k.
        closed_in (product_topology k tops) (cartesian_product k s) <=>
        cartesian_product k s = {} \/
        (!i. i IN k ==> closed_in (tops i) (s i))`;;

let INTERIOR_IN_CARTESIAN_PRODUCT = `!k tops s:K->A->bool.
        FINITE k
        ==> ((product_topology k tops) interior_of (cartesian_product k s) =
             cartesian_product k (\i. (tops i) interior_of (s i)))`;;

let QUOTIENT_MAP_PRODUCT_PROJECTION = `!(tops:K->A topology) k i.
      i IN k
      ==> (quotient_map(product_topology k tops,tops i) (\x. x i) <=>
           topspace(product_topology k tops) = {} ==> topspace(tops i) = {})`;;

let CONTINUOUS_MAP_PRODUCT = `!k top top' (f:K->A->B).
        continuous_map (product_topology k top,product_topology k top')
                       (product_map k f) <=>
        topspace(product_topology k top) = {} \/
        !i. i IN k ==> continuous_map(top i,top' i) (f i)`;;

let OPEN_MAP_PRODUCT = `!k top top' (f:K->A->B).
        open_map (product_topology k top,product_topology k top')
                 (product_map k f) <=>
        topspace(product_topology k top) = {} \/
        FINITE {i | i IN k /\
                    IMAGE (f i) (topspace(top i)) PSUBSET topspace(top' i)} /\
        !i. i IN k ==> open_map(top i,top' i) (f i)`;;

let CLOSED_MAP_PRODUCT = `!k top top' (f:K->A->B).
        closed_map (product_topology k top,product_topology k top')
                   (product_map k f)
        ==> topspace(product_topology k top) = {} \/
            !i. i IN k ==> closed_map(top i,top' i) (f i)`;;

let IN_PRODUCT_TOPOLOGY_CLOSURE_OF = `!(tops:K->A topology) s k z.
        z IN (product_topology k tops) closure_of s
        ==> !i. i IN k ==> z i IN ((tops i) closure_of (IMAGE (\x. x i) s))`;;

let PRODUCT_TOPOLOGY_EQ = `!k top (top':K->A topology).
        product_topology k top = product_topology k top' <=>
        topspace(product_topology k top) = {} /\
        topspace(product_topology k top') = {} \/
        (!i. i IN k ==> top i = top' i)`;;

let DISCRETE_TOPOLOGY_CARTESIAN_PRODUCT_EQ = `!k (s:K->A->bool).
        discrete_topology(cartesian_product k s) =
        product_topology k (discrete_topology o s) <=>
        cartesian_product k s = {} \/
        FINITE {i | i IN k /\ ~(?a. s i SUBSET {a})}`;;

let DISCRETE_TOPOLOGY_CARTESIAN_PRODUCT = `!k (s:K->A->bool).
        FINITE {i | i IN k /\ ~(?a. s i SUBSET {a})}
        ==> discrete_topology(cartesian_product k s) =
            product_topology k (discrete_topology o s)`;;

let DISCRETE_SPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) k.
        discrete_space(product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        FINITE {i | i IN k /\ ~(?a. topspace(tops i) SUBSET {a})} /\
        !i. i IN k ==> discrete_space(tops i)`;;

(* ------------------------------------------------------------------------- *)
(* Disjoint sum of arbitarily many spaces.                                   *)
(* ------------------------------------------------------------------------- *)

let sum_topology = new_definition
 `sum_topology (k:K->bool) (top:K->A topology) =
        topology { u | u SUBSET disjoint_union k (topspace o top) /\
                       !i. i IN k ==> open_in (top i) {x | (i,x) IN u}}`;;

let OPEN_IN_SUM_TOPOLOGY = `!k (top:K->A topology) u.
        open_in (sum_topology k top) u <=>
        u SUBSET disjoint_union k (topspace o top) /\
        !i. i IN k ==> open_in (top i) {x | (i,x) IN u}`;;

let OPEN_IN_DISJOINT_UNION = `!k (top:K->A topology) u.
        open_in (sum_topology k top) (disjoint_union k u) <=>
        !i. i IN k ==> open_in (top i) (u i)`;;

let TOPSPACE_SUM_TOPOLOGY = `!k (top:K->A topology).
        topspace(sum_topology k top) = disjoint_union k (topspace o top)`;;

let OPEN_IN_SUM_TOPOLOGY_ALT = `!k (top:K->A topology) u.
        open_in (sum_topology k top) u <=>
        ?t. u = disjoint_union k t /\
            !i. i IN k ==> open_in (top i) (t i)`;;

let FORALL_OPEN_IN_SUM_TOPOLOGY = `!k (top:K->A topology).
        (!u. open_in (sum_topology k top) u ==> P u) <=>
        (!t. (!i. i IN k ==> open_in (top i) (t i))
             ==> P(disjoint_union k t))`;;

let EXISTS_OPEN_IN_SUM_TOPOLOGY = `!k (top:K->A topology).
        (?u. open_in (sum_topology k top) u /\ P u) <=>
        (?t. (!i. i IN k ==> open_in (top i) (t i)) /\
             P(disjoint_union k t))`;;

let CLOSED_IN_SUM_TOPOLOGY = `!k (top:K->A topology) u.
        closed_in (sum_topology k top) u <=>
        u SUBSET disjoint_union k (topspace o top) /\
        !i. i IN k ==> closed_in (top i) {x | (i,x) IN u}`;;

let CLOSED_IN_DISJOINT_UNION = `!k (top:K->A topology) u.
        closed_in (sum_topology k top) (disjoint_union k u) <=>
        !i. i IN k ==> closed_in (top i) (u i)`;;

let CLOSED_IN_SUM_TOPOLOGY_ALT = `!k (top:K->A topology) u.
        closed_in (sum_topology k top) u <=>
        ?t. u = disjoint_union k t /\
            !i. i IN k ==> closed_in (top i) (t i)`;;

let FORALL_CLOSED_IN_SUM_TOPOLOGY = `!k (top:K->A topology).
        (!u. closed_in (sum_topology k top) u ==> P u) <=>
        (!t. (!i. i IN k ==> closed_in (top i) (t i))
             ==> P(disjoint_union k t))`;;

let EXISTS_CLOSED_IN_SUM_TOPOLOGY = `!k (top:K->A topology).
        (?u. closed_in (sum_topology k top) u /\ P u) <=>
        (?t. (!i. i IN k ==> closed_in (top i) (t i)) /\
             P(disjoint_union k t))`;;

let OPEN_MAP_COMPONENT_INJECTION = `!k (top:K->A topology) i.
        i IN k ==> open_map(top i,sum_topology k top) (\x. (i,x))`;;

let CLOSED_MAP_COMPONENT_INJECTION = `!k (top:K->A topology) i.
        i IN k ==> closed_map(top i,sum_topology k top) (\x. (i,x))`;;

let CONTINUOUS_MAP_COMPONENT_INJECTION = `!k (top:K->A topology) i.
        i IN k ==> continuous_map(top i,sum_topology k top) (\x. (i,x))`;;

let SUBTOPOLOGY_SUM_TOPOLOGY = `!k top s:K->A->bool.
        subtopology (sum_topology k top) (disjoint_union k s) =
        sum_topology k (\i. subtopology (top i) (s i))`;;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms (1-way and 2-way versions may be useful in places).        *)
(* ------------------------------------------------------------------------- *)

let homeomorphic_map = new_definition
 `homeomorphic_map (top,top') (f:A->B) <=>
      quotient_map (top,top') f /\
      !x y. x IN topspace top /\ y IN topspace top
            ==> (f x = f y <=> x = y)`;;

let homeomorphic_maps = new_definition
 `homeomorphic_maps(top,top') (f:A->B,g) <=>
        continuous_map(top,top') f /\
        continuous_map(top',top) g /\
        (!x. x IN topspace top ==> g(f x) = x) /\
        (!y. y IN topspace top' ==> f(g y) = y)`;;

let HOMEOMORPHIC_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ homeomorphic_map (top,top') f
        ==> homeomorphic_map (top,top') g`;;

let HOMEOMORPHIC_MAPS_EQ = `!top top' f (f':A->B) g g'.
        (!x. x IN topspace top ==> f x = f' x) /\
        (!x. x IN topspace top' ==> g x = g' x) /\
        homeomorphic_maps (top,top') (f,g)
        ==> homeomorphic_maps (top,top') (f',g')`;;

let HOMEOMORPHIC_MAPS_SYM = `!(f:A->B) g top top'.
        homeomorphic_maps(top,top') (f,g) <=>
        homeomorphic_maps(top',top) (g,f)`;;

let HOMEOMORPHIC_MAPS_ID = `!top top':A topology.
        homeomorphic_maps(top,top') ((\x. x),(\x. x)) <=> top' = top`;;

let HOMEOMORPHIC_MAP_ID = `!top top':A topology.
        homeomorphic_map(top,top') (\x. x) <=> top' = top`;;

let HOMEOMORPHIC_MAPS_I = `!top top':A topology.
        homeomorphic_maps(top,top') (I,I) <=> top' = top`;;

let HOMEOMORPHIC_MAP_I = `!top top':A topology. homeomorphic_map(top,top') I <=> top' = top`;;

let HOMEOMORPHIC_MAP_COMPOSE = `!top top' top'' (f:A->B) (g:B->C).
        homeomorphic_map(top,top') f /\ homeomorphic_map(top',top'') g
        ==> homeomorphic_map(top,top'') (g o f)`;;

let HOMEOMORPHIC_MAPS_COMPOSE = `!top top' top'' (f:A->B) (g:B->C) h k.
        homeomorphic_maps(top,top') (f,h) /\
        homeomorphic_maps(top',top'') (g,k)
        ==> homeomorphic_maps(top,top'') (g o f,h o k)`;;

let HOMEOMORPHIC_EQ_EVERYTHING_MAP = `!top top' f:A->B.
        homeomorphic_map (top,top') f <=>
        continuous_map (top,top') f /\
        open_map (top,top') f /\
        closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        !x y. x IN topspace top /\ y IN topspace top
              ==> (f x = f y <=> x = y)`;;

let HOMEOMORPHIC_IMP_QUOTIENT_MAP = `!top top' (f:A->B).
        homeomorphic_map(top,top') f ==> quotient_map(top,top') f`;;

let HOMEOMORPHIC_IMP_CONTINUOUS_MAP = `!top top' f:A->B.
        homeomorphic_map (top,top') f ==> continuous_map (top,top') f`;;

let HOMEOMORPHIC_IMP_OPEN_MAP = `!top top' f:A->B.
        homeomorphic_map (top,top') f ==> open_map (top,top') f`;;

let HOMEOMORPHIC_IMP_CLOSED_MAP = `!top top' f:A->B.
        homeomorphic_map (top,top') f ==> closed_map (top,top') f`;;

let HOMEOMORPHIC_IMP_SURJECTIVE_MAP = `!top top' f:A->B.
        homeomorphic_map (top,top') f
        ==> IMAGE f (topspace top) = topspace top'`;;

let HOMEOMORPHIC_IMP_INJECTIVE_MAP = `!top top' f:A->B.
        homeomorphic_map (top,top') f
        ==> !x y. x IN topspace top /\ y IN topspace top
                  ==> (f x = f y <=> x = y)`;;

let BIJECTIVE_OPEN_IMP_HOMEOMORPHIC_MAP = `!top top' f:A->B.
        continuous_map (top,top') f /\
        open_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        (!x y. x IN topspace top /\ y IN topspace top
               ==> (f x = f y <=> x = y))
        ==> homeomorphic_map(top,top') f`;;

let BIJECTIVE_CLOSED_IMP_HOMEOMORPHIC_MAP = `!top top' f:A->B.
        continuous_map (top,top') f /\
        closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        (!x y. x IN topspace top /\ y IN topspace top
               ==> (f x = f y <=> x = y))
        ==> homeomorphic_map(top,top') f`;;

let OPEN_EQ_CONTINUOUS_INVERSE_MAP = `!top top' (f:A->B) g.
        (!x. x IN topspace top ==> f x IN topspace top' /\ g(f x) = x) /\
        (!y. y IN topspace top' ==> g y IN topspace top /\ f(g y) = y)
        ==> (open_map (top,top') f <=> continuous_map (top',top) g)`;;

let CLOSED_EQ_CONTINUOUS_INVERSE_MAP = `!top top' (f:A->B) g.
        (!x. x IN topspace top ==> f x IN topspace top' /\ g(f x) = x) /\
        (!y. y IN topspace top' ==> g y IN topspace top /\ f(g y) = y)
        ==> (closed_map (top,top') f <=> continuous_map (top',top) g)`;;

let HOMEOMORPHIC_MAPS_MAP = `!top top' (f:A->B) g.
        homeomorphic_maps(top,top') (f:A->B,g) <=>
        homeomorphic_map(top,top') f /\
        homeomorphic_map(top',top) g /\
        (!x. x IN topspace top ==> g(f x) = x) /\
        (!y. y IN topspace top' ==> f(g y) = y)`;;

let HOMEOMORPHIC_MAPS_IMP_MAP = `!top top' (f:A->B) g.
        homeomorphic_maps (top,top') (f,g) ==> homeomorphic_map (top,top') f`;;

let HOMEOMORPHIC_MAP_MAPS = `!top top' f:A->B.
     homeomorphic_map (top,top') f <=> ?g. homeomorphic_maps (top,top') (f,g)`;;

let HOMEOMORPHIC_MAPS_INVOLUTION = `!top (f:A->A).
        continuous_map(top,top) f /\ (!x. x IN topspace top ==> f(f x) = x)
        ==> homeomorphic_maps (top,top) (f,f)`;;

let HOMEOMORPHIC_MAP_INVOLUTION = `!top (f:A->A).
        continuous_map(top,top) f /\ (!x. x IN topspace top ==> f(f x) = x)
        ==> homeomorphic_map (top,top) f`;;

let HOMEOMORPHIC_MAP_OPENNESS = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f /\ u SUBSET topspace top
        ==> (open_in top' (IMAGE f u) <=> open_in top u)`;;

let HOMEOMORPHIC_MAP_CLOSEDNESS = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f /\ u SUBSET topspace top
        ==> (closed_in top' (IMAGE f u) <=> closed_in top u)`;;

let HOMEOMORPHIC_MAP_OPENNESS_EQ = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f
        ==> (open_in top u <=>
             u SUBSET topspace top /\ open_in top' (IMAGE f u))`;;

let HOMEOMORPHIC_MAP_CLOSEDNESS_EQ = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f
        ==> (closed_in top u <=>
             u SUBSET topspace top /\ closed_in top' (IMAGE f u))`;;

let FORALL_OPEN_IN_HOMEOMORPHIC_IMAGE = `!(f:A->B) top top' P.
        homeomorphic_map(top,top') f
        ==> ((!v. open_in top' v ==> P v) <=>
             (!u. open_in top u ==> P(IMAGE f u)))`;;

let FORALL_CLOSED_IN_HOMEOMORPHIC_IMAGE = `!(f:A->B) top top' P.
        homeomorphic_map(top,top') f
        ==> ((!v. closed_in top' v ==> P v) <=>
             (!u. closed_in top u ==> P(IMAGE f u)))`;;

let HOMEOMORPHIC_MAP_DERIVED_SET_OF = `!(f:A->B) top top' s.
        homeomorphic_map (top,top') f /\ s SUBSET topspace top
        ==> top' derived_set_of (IMAGE f s) = IMAGE f (top derived_set_of s)`;;

let HOMEOMORPHIC_MAP_CLOSURE_OF = `!(f:A->B) top top' s.
        homeomorphic_map (top,top') f /\ s SUBSET topspace top
        ==> top' closure_of (IMAGE f s) = IMAGE f (top closure_of s)`;;

let HOMEOMORPHIC_MAP_INTERIOR_OF = `!(f:A->B) top top' s.
        homeomorphic_map (top,top') f /\ s SUBSET topspace top
        ==> top' interior_of (IMAGE f s) = IMAGE f (top interior_of s)`;;

let HOMEOMORPHIC_MAP_FRONTIER_OF = `!(f:A->B) top top' s.
        homeomorphic_map (top,top') f /\ s SUBSET topspace top
        ==> top' frontier_of (IMAGE f s) = IMAGE f (top frontier_of s)`;;

let HOMEOMORPHIC_MAPS_SUBTOPOLOGIES = `!top top' (f:A->B) g s t.
        homeomorphic_maps(top,top') (f,g) /\
        IMAGE f (topspace top INTER s) = topspace top' INTER t
        ==> homeomorphic_maps(subtopology top s,subtopology top' t) (f,g)`;;

let HOMEOMORPHIC_MAPS_SUBTOPOLOGIES_ALT = `!top top' (f:A->B) g s t.
        homeomorphic_maps (top,top') (f,g) /\
        IMAGE f (topspace top INTER s) SUBSET t /\
        IMAGE g (topspace top' INTER t) SUBSET s
        ==> homeomorphic_maps (subtopology top s,subtopology top' t) (f,g)`;;

let HOMEOMORPHIC_MAP_SUBTOPOLOGIES = `!top top' (f:A->B) s t.
        homeomorphic_map(top,top') f /\
        IMAGE f (topspace top INTER s) = topspace top' INTER t
        ==> homeomorphic_map(subtopology top s,subtopology top' t) f`;;

let HOMEOMORPHIC_MAP_SUBTOPOLOGIES_ALT = `!top top' (f:A->B) s t.
        homeomorphic_map (top,top') f /\
        (!x. x IN topspace top /\ f x IN topspace top'
             ==> (f x IN t <=> x IN s))
        ==> homeomorphic_map (subtopology top s,subtopology top' t) f`;;

let HOMEOMORPHIC_MAPS_PROD = `!top1 top2 top3 top4 (f:A->B) (g:C->D) f' g'.
        homeomorphic_maps (prod_topology top1 top2,prod_topology top3 top4)
                          ((\(x,y). f x,g y),(\(x,y). f' x,g' y)) <=>
        topspace(prod_topology top1 top2) = {} /\
        topspace(prod_topology top3 top4) = {} \/
        homeomorphic_maps (top1,top3) (f,f') /\
        homeomorphic_maps (top2,top4) (g,g')`;;

let HOMEOMORPHIC_MAPS_SWAP = `!(top:A topology) (top':B topology).
        homeomorphic_maps (prod_topology top top',prod_topology top' top)
                          ((\(x,y). y,x),(\(y,x). x,y))`;;

let HOMEOMORPHIC_MAP_SWAP = `!(top:A topology) (top':B topology).
        homeomorphic_map (prod_topology top top',prod_topology top' top)
                         (\(x,y). y,x)`;;

(* ------------------------------------------------------------------------- *)
(* Relation of homeomorphism between topological spaces.                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("homeomorphic_space",(12,"right"));;

let homeomorphic_space = new_definition
 `(top:A topology) homeomorphic_space (top':B topology) <=>
        ?f g. homeomorphic_maps(top,top') (f,g)`;;

let HOMEOMORPHIC_SPACE_REFL = `!top:A topology. top homeomorphic_space top`;;

let HOMEOMORPHIC_SPACE_SYM = `!top:A topology top':B topology.
        top homeomorphic_space top' <=> top' homeomorphic_space top`;;

let HOMEOMORPHIC_SPACE_TRANS = `!top1:A topology top2:B topology top3:C topology.
        top1 homeomorphic_space top2 /\ top2 homeomorphic_space top3
        ==> top1 homeomorphic_space top3`;;

let HOMEOMORPHIC_SPACE = `!top:A topology top':B topology.
        top homeomorphic_space top' <=> ?f. homeomorphic_map (top,top') f`;;

let HOMEOMORPHIC_MAPS_IMP_HOMEOMORPHIC_SPACE = `!top top' (f:A->B) g.
        homeomorphic_maps (top,top') (f,g) ==> top homeomorphic_space top'`;;

let HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE = `!top top' f:A->B.
        homeomorphic_map (top,top') f ==> top homeomorphic_space top'`;;

let HOMEOMORPHIC_SPACE_IMP_CARD_EQ = `!top:A topology top':B topology.
        top homeomorphic_space top' ==> topspace top =_c topspace top'`;;

let HOMEOMORPHIC_SPACE_FINITENESS = `!top:A topology top':B topology.
        top homeomorphic_space top'
        ==> (FINITE(topspace top) <=> FINITE(topspace top'))`;;

let HOMEOMORPHIC_SPACE_INFINITENESS = `!top:A topology top':B topology.
        top homeomorphic_space top'
        ==> (INFINITE(topspace top) <=> INFINITE(topspace top'))`;;

let HOMEOMORPHIC_SPACE_COUNTABILITY = `!top:A topology top':B topology.
        top homeomorphic_space top'
        ==> (COUNTABLE(topspace top) <=> COUNTABLE(topspace top'))`;;

let HOMEOMORPHIC_EMPTY_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (topspace top = {} <=> topspace top' = {})`;;

let HOMEOMORPHIC_EMPTY_SPACE_EQ = `(!(top:A topology) (top':B topology).
        topspace top = {}
        ==> (top homeomorphic_space top' <=> topspace top' = {})) /\
   (!(top:A topology) (top':B topology).
        topspace top' = {}
        ==> (top homeomorphic_space top' <=> topspace top = {}))`;;

let PROD_TOPOLOGY_HOMEOMORPHIC_SPACE_LEFT = `!(top:A topology) (top':B topology) b.
        topspace top' = {b} ==> prod_topology top top' homeomorphic_space top`;;

let PROD_TOPOLOGY_HOMEOMORPHIC_SPACE_RIGHT = `!(top:A topology) (top':B topology) a.
        topspace top = {a} ==> prod_topology top top' homeomorphic_space top'`;;

let HOMEOMORPHIC_SPACE_PROD_TOPOLOGY_SING = `(!top:A topology top':B topology b.
      b IN topspace top'
      ==> top homeomorphic_space (prod_topology top (subtopology top' {b}))) /\
   (!top:A topology top':B topology a.
      a IN topspace top
      ==> top' homeomorphic_space (prod_topology (subtopology top {a}) top'))`;;

let TOPOLOGICAL_PROPERTY_OF_PROD_COMPONENT = `!P Q R (top1:A topology) (top2:B topology).
        (!a. a IN topspace top1 /\ P(prod_topology top1 top2)
             ==> P(subtopology (prod_topology top1 top2)
                               ({a} CROSS topspace top2))) /\
        (!b. b IN topspace top2 /\ P(prod_topology top1 top2)
             ==> P(subtopology (prod_topology top1 top2)
                               (topspace top1 CROSS {b}))) /\
        (!top top'. top homeomorphic_space top' ==> (P top <=> Q top')) /\
        (!top top'. top homeomorphic_space top' ==> (P top <=> R top'))
        ==> P(prod_topology top1 top2)
            ==> topspace(prod_topology top1 top2) = {} \/
                Q top1 /\ R top2`;;

let PRODUCT_TOPOLOGY_HOMEOMORPHIC_COMPONENT = `!(tops:K->A topology) k i.
        i IN k /\
        (!j. j IN k /\ ~(j = i) ==> ?a. topspace(tops j) = {a})
        ==> product_topology k tops homeomorphic_space (tops i)`;;

let TOPOLOGICAL_PROPERTY_OF_PRODUCT_COMPONENT = `!P Q (tops:K->A topology) k.
        (!z i. z IN topspace(product_topology k tops) /\
               P(product_topology k tops) /\
               i IN k
               ==> P(subtopology
                       (product_topology k tops)
                       (cartesian_product k
                         (\j. if j = i then topspace(tops i) else {z j})))) /\
        (!top top'. top homeomorphic_space top' ==> (P top <=> Q top'))
        ==> P(product_topology k tops)
            ==> topspace(product_topology k tops) = {} \/
                !i. i IN k ==> Q(tops i)`;;

let HOMEOMORPHIC_SPACE_PROD_TOPOLOGY = `!(top1:A topology) (top1':B topology) (top2:C topology) (top2':D topology).
        top1 homeomorphic_space top1' /\ top2 homeomorphic_space top2'
        ==> prod_topology top1 top2 homeomorphic_space
            prod_topology top1' top2'`;;

let HOMEOMORPHIC_SPACE_PROD_TOPOLOGY_SWAP = `!(top:A topology) (top':B topology).
        (prod_topology top top') homeomorphic_space (prod_topology top' top)`;;

let HOMEOMORPHIC_SPACE_SINGLETON_PRODUCT = `!(tops:K->A topology) k.
        product_topology {k} tops homeomorphic_space (tops k)`;;

(* ------------------------------------------------------------------------- *)
(* Embedding maps.                                                           *)
(* ------------------------------------------------------------------------- *)

let embedding_map = new_definition
 `embedding_map (top,top') (f:A->B) <=>
        homeomorphic_map (top,subtopology top' (IMAGE f (topspace top))) f`;;

let EMBEDDING_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ embedding_map (top,top') f
        ==> embedding_map (top,top') g`;;

let EMBEDDING_MAP_COMPOSE = `!top top' top'' (f:A->B) (g:B->C).
        embedding_map(top,top') f /\ embedding_map(top',top'') g
        ==> embedding_map(top,top'') (g o f)`;;

let SURJECTIVE_EMBEDDING_MAP = `!top top' f:A->B.
      embedding_map (top,top') f /\ IMAGE f (topspace top) = topspace top' <=>
      homeomorphic_map (top,top') f`;;

let EMBEDDING_MAP_IN_SUBTOPOLOGY = `!top top' s f:A->B.
         embedding_map (top,subtopology top' s) f <=>
         embedding_map (top,top') f /\ IMAGE f (topspace top) SUBSET s`;;

let INJECTIVE_OPEN_IMP_EMBEDDING_MAP = `!top top' (f:A->B).
           continuous_map (top,top') f /\
           open_map (top,top') f /\
           (!x y. x IN topspace top /\ y IN topspace top
                  ==> (f x = f y <=> x = y))
           ==> embedding_map (top,top') f`;;

let INJECTIVE_CLOSED_IMP_EMBEDDING_MAP = `!top top' (f:A->B).
           continuous_map (top,top') f /\
           closed_map (top,top') f /\
           (!x y. x IN topspace top /\ y IN topspace top
                  ==> (f x = f y <=> x = y))
           ==> embedding_map (top,top') f`;;

let EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE = `!top top' f:A->B.
      embedding_map (top,top') f
      ==> top homeomorphic_space (subtopology top' (IMAGE f (topspace top)))`;;

let EMBEDDING_IMP_CONTINUOUS_MAP = `!top top' (f:A->B).
     embedding_map(top,top') f ==> continuous_map(top,top') f`;;

let EMBEDDING_IMP_INJECTIVE_MAP = `!top top' (f:A->B).
     embedding_map(top,top') f
     ==> !x y. x IN topspace top /\ y IN topspace top
               ==> (f x = f y <=> x = y)`;;

let EMBEDDING_IMP_CLOSED_MAP = `!top top' (f:A->B).
        embedding_map(top,top') f /\ closed_in top' (IMAGE f (topspace top))
        ==> closed_map(top,top') f`;;

let EMBEDDING_IMP_CLOSED_MAP_EQ = `!top top' (f:A->B).
     embedding_map(top,top') f
     ==> (closed_map(top,top') f <=> closed_in top' (IMAGE f (topspace top)))`;;

let EMBEDDING_IMP_OPEN_MAP = `!top top' (f:A->B).
        embedding_map(top,top') f /\ open_in top' (IMAGE f (topspace top))
        ==> open_map(top,top') f`;;

let EMBEDDING_IMP_OPEN_MAP_EQ = `!top top' (f:A->B).
      embedding_map(top,top') f
      ==> (open_map(top,top') f <=> open_in top' (IMAGE f (topspace top)))`;;

let EMBEDDING_MAP_ON_EMPTY = `!top top' (f:A->B). topspace top = {} ==> embedding_map(top,top') f`;;

let EMBEDDING_MAP_COMPONENT_INJECTION = `!k (top:K->A topology) i.
        i IN k ==> embedding_map(top i,sum_topology k top) (\x. (i,x))`;;

let TOPOLOGICAL_PROPERTY_OF_SUM_COMPONENT = `!P Q (tops:K->A topology) k.
        (!top s. P top /\ closed_in top s /\ open_in top s
                 ==> P(subtopology top s)) /\
        (!top top'. top homeomorphic_space top' ==> (P top <=> Q top'))
        ==> P(sum_topology k tops) ==> !i. i IN k ==> Q(tops i)`;;

(* ------------------------------------------------------------------------- *)
(* Retraction and section maps (having 1-sided inverses).                    *)
(* ------------------------------------------------------------------------- *)

let retraction_maps = new_definition
 `retraction_maps (top,top') (f:A->B,g) <=>
        continuous_map(top,top') f /\
        continuous_map(top',top) g /\
        (!x. x IN topspace top' ==> f(g x) = x)`;;

let section_map = new_definition
 `section_map (top,top') (f:A->B) <=>
    ?g. retraction_maps (top',top) (g,f)`;;

let retraction_map = new_definition
 `retraction_map (top,top') (f:A->B) <=>
    ?g. retraction_maps (top,top') (f,g)`;;

let RETRACTION_IMP_CONTINUOUS_MAP = `!top top' (f:A->B).
        retraction_map (top,top') f ==> continuous_map(top,top') f`;;

let SECTION_IMP_CONTINUOUS_MAP = `!top top' (f:A->B).
        section_map (top,top') f ==> continuous_map(top,top') f`;;

let RETRACTION_MAPS_EQ = `!top top' f (f':A->B) g g'.
        (!x. x IN topspace top ==> f x = f' x) /\
        (!x. x IN topspace top' ==> g x = g' x) /\
        retraction_maps (top,top') (f,g)
        ==> retraction_maps (top,top') (f',g')`;;

let SECTION_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ section_map (top,top') f
        ==> section_map (top,top') g`;;

let RETRACTION_MAP_EQ = `!top top' f g:A->B.
        (!x. x IN topspace top ==> f x = g x) /\ retraction_map (top,top') f
        ==> retraction_map (top,top') g`;;

let HOMEOMORPHIC_IMP_RETRACTION_MAPS = `!top top' (f:A->B) g.
    homeomorphic_maps(top,top') (f,g) ==> retraction_maps (top,top') (f,g)`;;

let SECTION_AND_RETRACTION_EQ_HOMEOMORPHIC_MAP = `!top top' (f:A->B).
        section_map (top,top') f /\ retraction_map (top,top') f <=>
        homeomorphic_map (top,top') f`;;

let HOMEOMORPHIC_IMP_RETRACTION_MAP = `!top top' (f:A->B).
        homeomorphic_map(top,top') f ==> retraction_map (top,top') f`;;

let HOMEOMORPHIC_IMP_SECTION_MAP = `!top top' (f:A->B).
        homeomorphic_map(top,top') f ==> section_map (top,top') f`;;

let SECTION_IMP_EMBEDDING_MAP = `!top top' (f:A->B).
        section_map(top,top') f ==> embedding_map(top,top') f`;;

let RETRACTION_IMP_QUOTIENT_MAP = `!top top' (f:A->B).
        retraction_map(top,top') f ==> quotient_map(top,top') f`;;

let RETRACTION_MAPS_COMPOSE = `!top1 top2 top3 (f:A->B) (g:B->C) f' g'.
        retraction_maps (top1,top2) (f,f') /\
        retraction_maps (top2,top3) (g,g')
        ==> retraction_maps (top1,top3) (g o f,f' o g')`;;

let RETRACTION_MAP_COMPOSE = `!top1 top2 top3 (f:A->B) (g:B->C).
        retraction_map (top1,top2) f /\
        retraction_map (top2,top3) g
        ==> retraction_map (top1,top3) (g o f)`;;

let SECTION_MAP_COMPOSE = `!top1 top2 top3 (f:A->B) (g:B->C).
        section_map (top1,top2) f /\
        section_map (top2,top3) g
        ==> section_map (top1,top3) (g o f)`;;

let SURJECTIVE_SECTION_EQ_HOMEOMORPHIC_MAP = `!top top' (f:A->B).
        section_map(top,top') f /\ IMAGE f (topspace top) = topspace top' <=>
        homeomorphic_map (top,top') f`;;

let SURJECTIVE_RETRACTION_OR_SECTION_MAP = `!top top' (f:A->B).
        IMAGE f (topspace top) = topspace top'
        ==> (retraction_map(top,top') f \/ section_map(top,top') f <=>
             retraction_map(top,top') f)`;;

let RETRACTION_IMP_SURJECTIVE_MAP = `!top top' (f:A->B).
        retraction_map(top,top') f ==> IMAGE f (topspace top) = topspace top'`;;

let SECTION_IMP_INJECTIVE_MAP = `!top top' (f:A->B).
        section_map(top,top') f
        ==> (!x y. x IN topspace top /\ y IN topspace top
                   ==> (f x = f y <=> x = y))`;;

let RETRACTION_MAPS_TO_RETRACT_MAPS = `!top top' (r:A->B) s.
        retraction_maps(top,top') (r,s)
        ==> retraction_maps (top,subtopology top (IMAGE s (topspace top')))
                            (s o r,I)`;;

let EMBEDDING_EQ_SECTION_MAP = `!top top' (f:A->B).
        embedding_map(top,top') f <=>
        section_map(top,subtopology top' (IMAGE f (topspace top))) f`;;

let RETRACTION_MAP_INTO_SUBTOPOLOGY = `!top top' t (r:A->B).
        retraction_map(top,top') r /\ IMAGE r (topspace top) SUBSET t
        ==> retraction_map(top,subtopology top' t) r`;;

let RETRACTION_MAPS_SUBTOPOLOGIES = `!top top' s t (r:A->B) r'.
        retraction_maps(top,top') (r,r') /\
        IMAGE r s SUBSET t /\ IMAGE r' t SUBSET s
        ==> retraction_maps(subtopology top s,subtopology top' t) (r,r')`;;

let RETRACTION_MAP_FST = `!(top1:A topology) (top2:B topology).
        retraction_map (prod_topology top1 top2,top1) FST <=>
        topspace top2 = {} ==> topspace top1 = {}`;;

let RETRACTION_MAP_SND = `!(top1:A topology) (top2:B topology).
        retraction_map (prod_topology top1 top2,top2) SND <=>
        topspace top1 = {} ==> topspace top2 = {}`;;

let RETRACTION_MAP_PRODUCT_PROJECTION = `!k (tops:K->A topology) i.
        i IN k
        ==> (retraction_map (product_topology k tops,tops i) (\x. x i) <=>
             topspace (product_topology k tops) = {}
             ==> topspace (tops i) = {})`;;

let DISCRETE_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map (top,top') r /\ discrete_space top
        ==> discrete_space top'`;;

let HOMEOMORPHIC_DISCRETE_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (discrete_space top <=> discrete_space top')`;;

let HOMEOMORPHIC_DISCRETE_SPACES = `!(top:A topology) (top':B topology).
        discrete_space top /\ discrete_space top'
        ==> (top homeomorphic_space top' <=>
             topspace top =_c topspace top')`;;

(* ------------------------------------------------------------------------- *)
(* When a subset is a retract of a topological space.                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("retract_of_space",(12,"right"));;

let retract_of_space = new_definition
 `(s:A->bool) retract_of_space top <=>
        s SUBSET topspace top /\
        ?r. continuous_map(top,subtopology top s) r /\
            !x. x IN s ==> r x = x`;;

let RETRACT_OF_SPACE_RETRACTION_MAPS = `!top s:A->bool.
        s retract_of_space top <=>
        s SUBSET topspace top /\
        ?r. retraction_maps (top,subtopology top s) (r,I)`;;

let RETRACT_OF_SPACE_SECTION_MAP = `!top s:A->bool.
        s retract_of_space top <=>
        s SUBSET topspace top /\ section_map (subtopology top s,top) (\x. x)`;;

let RETRACT_OF_SPACE_IMP_SUBSET = `!top s:A->bool. s retract_of_space top ==> s SUBSET topspace top`;;

let RETRACT_OF_SPACE_TOPSPACE = `!top:A topology. topspace top retract_of_space top`;;

let RETRACT_OF_SPACE_EMPTY = `!top:A topology. {} retract_of_space top <=> topspace top = {}`;;

let RETRACT_OF_SPACE_IMP_NONEMPTY = `!top s:A->bool.
        s retract_of_space top /\ ~(topspace top = {}) ==> ~(s = {})`;;

let RETRACT_OF_SPACE_SING = `!top a:A. {a} retract_of_space top <=> a IN topspace top`;;

let RETRACT_OF_SPACE_TRANS = `!top s t:A->bool.
        s retract_of_space top /\ t retract_of_space (subtopology top s)
        ==> t retract_of_space top`;;

let RETRACT_OF_SPACE_SUBTOPOLOGY = `!top s u:A->bool.
        s retract_of_space top /\ s SUBSET u
        ==> s retract_of_space (subtopology top u)`;;

let RETRACT_OF_SPACE_CLOPEN = `!top s:A->bool.
        open_in top s /\ closed_in top s /\ (s = {} ==> topspace top = {})
        ==> s retract_of_space top`;;

let RETRACT_OF_SPACE_DISJOINT_UNION = `!top s t:A->bool.
     open_in top s /\ open_in top t /\ DISJOINT s t /\
     s UNION t = topspace top /\
     (s = {} ==> topspace top = {})
     ==> s retract_of_space top`;;

let RETRACTION_MAPS_SECTION_IMAGE = `!top top' (r:A->B) s.
        retraction_maps(top,top') (r,s)
        ==> IMAGE s (topspace top') retract_of_space top /\
            subtopology top (IMAGE s (topspace top')) homeomorphic_space top'`;;

let HEREDITARY_IMP_RETRACTIVE_PROPERTY = `!(P:A topology->bool) (Q:B topology->bool).
        (!top s. P top ==> P(subtopology top s)) /\
        (!top top'. top homeomorphic_space top' ==> (P top <=> Q top'))
        ==> !top top' r. retraction_map(top,top') r /\ P top ==> Q top'`;;

(* ------------------------------------------------------------------------- *)
(* Compact sets and compact topological spaces.                              *)
(* ------------------------------------------------------------------------- *)

let compact_in = new_definition
  `!top s:A->bool.
     compact_in top s <=>
     s SUBSET topspace top /\
     (!U. (!u. u IN U ==> open_in top u) /\ s SUBSET UNIONS U
          ==> (?V. FINITE V /\ V SUBSET U /\ s SUBSET UNIONS V))`;;

let compact_space = new_definition
 `compact_space(top:A topology) <=> compact_in top (topspace top)`;;

let COMPACT_SPACE_ALT = `!top:A topology.
        compact_space top <=>
        !U. (!u. u IN U ==> open_in top u) /\
            topspace top SUBSET UNIONS U
            ==> ?V. FINITE V /\ V SUBSET U /\ topspace top SUBSET UNIONS V`;;

let COMPACT_SPACE = `!top:A topology.
        compact_space top <=>
        !U. (!u. u IN U ==> open_in top u) /\
            UNIONS U = topspace top
            ==> ?V. FINITE V /\ V SUBSET U /\ UNIONS V = topspace top`;;

let COMPACT_IN_ABSOLUTE = `!top s:A->bool.
        compact_in (subtopology top s) s <=> compact_in top s`;;

let COMPACT_IN_SUBSPACE = `!top s:A->bool.
        compact_in top s <=>
        s SUBSET topspace top /\ compact_space (subtopology top s)`;;

let COMPACT_SPACE_SUBTOPOLOGY = `!top s:A->bool. compact_in top s ==> compact_space (subtopology top s)`;;

let COMPACT_IN_SUBTOPOLOGY = `!top s t:A->bool.
        compact_in (subtopology top s) t <=> compact_in top t /\ t SUBSET s`;;

let COMPACT_IN_SUBSET_TOPSPACE = `!top s:A->bool. compact_in top s ==> s SUBSET topspace top`;;

let COMPACT_IN_CONTRACTIVE = `!top top':A topology.
        topspace top' = topspace top /\
        (!u. open_in top u ==> open_in top' u)
        ==> !s. compact_in top' s ==> compact_in top s`;;

let COMPACT_SPACE_CONTRACTIVE = `!top top':A topology.
        topspace top' = topspace top /\
        (!u. open_in top u ==> open_in top' u)
        ==> compact_space top' ==> compact_space top`;;

let FINITE_IMP_COMPACT_IN = `!top s:A->bool. s SUBSET topspace top /\ FINITE s ==> compact_in top s`;;

let COMPACT_IN_EMPTY = `!top:A topology. compact_in top {}`;;

let COMPACT_SPACE_TOPSPACE_EMPTY = `!top:A topology. topspace top = {} ==> compact_space top`;;

let FINITE_IMP_COMPACT_IN_EQ = `!top s:A->bool.
        FINITE s ==> (compact_in top s <=> s SUBSET topspace top)`;;

let COMPACT_IN_SING = `!top a:A. compact_in top {a} <=> a IN topspace top`;;

let CLOSED_COMPACT_IN = `!top k c:A->bool. compact_in top k /\ c SUBSET k /\ closed_in top c
                     ==> compact_in top c`;;

let CLOSED_IN_COMPACT_SPACE = `!top s:A->bool.
        compact_space top /\ closed_in top s ==> compact_in top s`;;

let COMPACT_INTER_CLOSED_IN = `!top s t:A->bool.
        compact_in top s /\ closed_in top t ==> compact_in top (s INTER t)`;;

let CLOSED_INTER_COMPACT_IN = `!top s t:A->bool.
        closed_in top s /\ compact_in top t ==> compact_in top (s INTER t)`;;

let COMPACT_IN_UNION = `!top s t:A->bool.
        compact_in top s /\ compact_in top t ==> compact_in top (s UNION t)`;;

let COMPACT_IN_UNIONS = `!top f:(A->bool)->bool.
        FINITE f /\ (!s. s IN f ==> compact_in top s)
        ==> compact_in top (UNIONS f)`;;

let COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT = `!top k s:A->bool.
     compact_in (subtopology top s) k ==> compact_in top k`;;

let COMPACT_IMP_COMPACT_IN_SUBTOPOLOGY = `!top k s:A->bool.
     compact_in top k /\ k SUBSET s ==> compact_in (subtopology top s) k`;;

let CLOSED_IN_COMPACT_SUBTOPOLOGY = `!top k s.
        compact_in top k /\ closed_in(subtopology top k) s
        ==> compact_in top s`;;

let COMPACT_SPACE_FIP = `!top:A topology.
        compact_space top <=>
        !f. (!c. c IN f ==> closed_in top c) /\
            (!f'. FINITE f' /\ f' SUBSET f ==> ~(INTERS f' = {}))
           ==> ~(INTERS f = {})`;;

let COMPACT_IN_FIP = `!top s:A->bool.
        compact_in top s <=>
        s SUBSET topspace top /\
        !f. (!c. c IN f ==> closed_in top c) /\
            (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER INTERS f' = {}))
            ==> ~(s INTER INTERS f = {})`;;

let COMPACT_SPACE_IMP_NEST = `!top c:num->A->bool.
        compact_space top /\
        (!n. closed_in top (c n)) /\
        (!n. ~(c n = {})) /\
        (!m n. m <= n ==> c n SUBSET c m)
        ==> ~(INTERS {c n | n IN (:num)} = {})`;;

let COMPACT_IN_DISCRETE_TOPOLOGY = `!u s:A->bool.
        compact_in (discrete_topology u) s <=> s SUBSET u /\ FINITE s`;;

let COMPACT_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. compact_space(discrete_topology u) <=> FINITE u`;;

let COMPACT_SPACE_IMP_BOLZANO_WEIERSTRASS = `!top s:A->bool.
        compact_space top /\ INFINITE s /\ s SUBSET topspace top
        ==> ~(top derived_set_of s = {})`;;

let COMPACT_IN_IMP_BOLZANO_WEIERSTRASS = `!top s t:A->bool.
        compact_in top s /\ INFINITE t /\ t SUBSET s
        ==> ~(s INTER top derived_set_of t = {})`;;

let COMPACT_CLOSURE_OF_IMP_BOLZANO_WEIERSTRASS = `!top s t:A->bool.
        compact_in top (top closure_of s) /\
        INFINITE t /\ t SUBSET s /\ t SUBSET topspace top
        ==> ~(top derived_set_of t = {})`;;

let DISCRETE_COMPACT_IN_EQ_FINITE = `!top s:A->bool.
        s INTER top derived_set_of s = {}
        ==> (compact_in top s <=> s SUBSET topspace top /\ FINITE s)`;;

let DISCRETE_COMPACT_SPACE_EQ_FINITE = `!top:A topology.
        top derived_set_of (topspace top) = {}
        ==> (compact_space top <=> FINITE(topspace top))`;;

let IMAGE_COMPACT_IN = `!top top' (f:A->B) s.
     compact_in top s /\ continuous_map (top,top')  f
     ==> compact_in top' (IMAGE f s)`;;

let HOMEOMORPHIC_COMPACT_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (compact_space top <=> compact_space top')`;;

let HOMEOMORPHIC_MAP_COMPACTNESS = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f /\ u SUBSET topspace top
        ==> (compact_in top' (IMAGE f u) <=> compact_in top u)`;;

let HOMEOMORPHIC_MAP_COMPACTNESS_EQ = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f
        ==> (compact_in top u <=>
             u SUBSET topspace top /\ compact_in top' (IMAGE f u))`;;

let COMPACT_SPACE_QUOTIENT_MAP_IMAGE = `!top top' (q:A->B).
        quotient_map(top,top') q /\ compact_space top
        ==> compact_space top'`;;

let COMPACT_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ compact_space top
        ==> compact_space top'`;;

let ALEXANDER_SUBBASE_THEOREM = `!top:A topology B.
        topology
          (ARBITRARY UNION_OF
               (FINITE INTERSECTION_OF B relative_to UNIONS B)) = top /\
        (!C. C SUBSET B /\ UNIONS C = topspace top
             ==> ?C'. FINITE C' /\ C' SUBSET C /\ UNIONS C' = topspace top)
        ==> compact_space top`;;

let ALEXANDER_SUBBASE_THEOREM_ALT = `!top:A topology B u.
        u SUBSET UNIONS B /\
        topology
          (ARBITRARY UNION_OF
               (FINITE INTERSECTION_OF B relative_to u)) = top /\
        (!C. C SUBSET B /\ u SUBSET UNIONS C
             ==> ?C'. FINITE C' /\ C' SUBSET C /\ u SUBSET UNIONS C')
        ==> compact_space top`;;

let COMPACT_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        compact_space(prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        compact_space top1 /\ compact_space top2`;;

let COMPACT_IN_CROSS = `!top1 top2 s:A->bool t:B->bool.
        compact_in (prod_topology top1 top2) (s CROSS t) <=>
        s = {} \/ t = {} \/ compact_in top1 s /\ compact_in top2 t`;;

let COMPACT_SPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) t.
        compact_space(product_topology t tops) <=>
        topspace(product_topology t tops) = {} \/
        !k. k IN t ==> compact_space(tops k)`;;

let COMPACT_IN_CARTESIAN_PRODUCT = `!tops:K->A topology s k.
        compact_in (product_topology k tops) (cartesian_product k s) <=>
        cartesian_product k s = {} \/
        !i. i IN k ==> compact_in (tops i) (s i)`;;

let TUBE_LEMMA_LEFT = `!top top' (k:A->bool) (y:B) w.
        open_in (prod_topology top top') w /\
        compact_in top k /\
        y IN topspace top' /\
        k CROSS {y} SUBSET w
        ==> ?u v. open_in top u /\ open_in top' v /\
                  k SUBSET u /\ y IN v /\ u CROSS v SUBSET w`;;

let TUBE_LEMMA_RIGHT = `!top top' (x:A) (k:B->bool) w.
        open_in (prod_topology top top') w /\
        compact_in top' k /\
        x IN topspace top /\
        {x} CROSS k SUBSET w
        ==> ?u v. open_in top u /\ open_in top' v /\
                  x IN u /\ k SUBSET v /\ u CROSS v SUBSET w`;;

let CLOSED_MAP_FST = `!(top:A topology) (top':B topology).
        compact_space top' ==> closed_map(prod_topology top top',top) FST`;;

let CLOSED_MAP_SND = `!(top:A topology) (top':B topology).
        compact_space top ==> closed_map(prod_topology top top',top') SND`;;

let WALLACE_THEOREM_PROD_TOPOLOGY = `!top top' w (k:A->bool) (l:B->bool).
        compact_in top k /\ compact_in top' l /\
        open_in (prod_topology top top') w /\
        k CROSS l SUBSET w
        ==> ?u v. open_in top u /\ open_in top' v /\
                  k SUBSET u /\ l SUBSET v /\ u CROSS v SUBSET w`;;

let LOCALLY_FINITE_COVER_OF_COMPACT_SPACE = `!(top:A topology) u.
        compact_space top /\
        topspace top SUBSET UNIONS u /\
        locally_finite_in top u
        ==> FINITE u`;;

(* ------------------------------------------------------------------------- *)
(* Separated sets.                                                           *)
(* ------------------------------------------------------------------------- *)

let separated_in = new_definition
 `separated_in top s t <=>
     s SUBSET topspace top /\ t SUBSET topspace top /\
     s INTER top closure_of t = {} /\ t INTER top closure_of s = {}`;;

let SEPARATED_IN_EMPTY = `(!top s:A->bool. separated_in top s {} <=> s SUBSET topspace top) /\
   (!top s:A->bool. separated_in top {} s <=> s SUBSET topspace top)`;;

let SEPARATED_IN_REFL = `!top s:A->bool. separated_in top s s <=> s = {}`;;

let SEPARATED_IN_SYM = `!top s t:A->bool.
        separated_in top s t <=> separated_in top t s`;;

let SEPARATED_IN_IMP_DISJOINT = `!top s t:A->bool. separated_in top s t ==> DISJOINT s t`;;

let SEPARATED_IN_MONO = `!top s t s' t':A->bool.
        separated_in top s t /\ s' SUBSET s /\ t' SUBSET t
        ==> separated_in top s' t'`;;

let SEPARATED_IN_OPEN_SETS = `!top s t:A->bool.
        open_in top s /\ open_in top t
        ==> (separated_in top s t <=> DISJOINT s t)`;;

let SEPARATED_IN_CLOSED_SETS = `!top s t:A->bool.
        closed_in top s /\ closed_in top t
        ==> (separated_in top s t <=> DISJOINT s t)`;;

let SEPARATED_IN_COMPLEMENT = `!top s:A->bool.
        separated_in top s (topspace top DIFF s) <=>
        closed_in top s /\ open_in top s`;;

let SEPARATED_IN_SUBTOPOLOGY = `!top u s t:A->bool.
        separated_in (subtopology top u) s t <=>
        s SUBSET u /\ t SUBSET u /\ separated_in top s t`;;

let SEPARATED_IN_DISCRETE_TOPOLOGY = `!u s t:A->bool.
        separated_in (discrete_topology u) s t <=>
        s SUBSET u /\ t SUBSET u /\ DISJOINT s t`;;

let SEPARATED_EQ_DISTINGUISHABLE = `!top x y:A.
        separated_in top {x} {y} <=>
        x IN topspace top /\ y IN topspace top /\
        (?u. open_in top u /\ x IN u /\ ~(y IN u)) /\
        (?v. open_in top v /\ y IN v /\ ~(x IN v))`;;

let SEPARATED_IN_UNION = `(!top s t u:A->bool.
        separated_in top s (t UNION u) <=>
        separated_in top s t /\ separated_in top s u) /\
   (!top s t u:A->bool.
        separated_in top (s UNION t) u <=>
        separated_in top s u /\ separated_in top t u)`;;

let SEPARATED_IN_UNIONS = `(!top s u:(A->bool)->bool.
        FINITE u
        ==> (separated_in top s (UNIONS u) <=>
             s SUBSET topspace top /\ !t. t IN u ==> separated_in top s t)) /\
   (!top s u:(A->bool)->bool.
        FINITE u
        ==> (separated_in top (UNIONS u) s <=>
             (!t. t IN u ==> separated_in top s t) /\ s SUBSET topspace top))`;;

let SEPARATED_IN_DIFFS = `!top s t:A->bool.
        open_in top s /\ open_in top t \/ closed_in top s /\ closed_in top t
        ==> separated_in top (s DIFF t) (t DIFF s)`;;

let SEPARATION_CLOSED_IN_UNION_GEN = `!top s t:A->bool.
        separated_in top s t <=>
        s SUBSET topspace top /\ t SUBSET topspace top /\ DISJOINT s t /\
        closed_in (subtopology top (s UNION t)) s /\
        closed_in (subtopology top (s UNION t)) t`;;

let SEPARATION_OPEN_IN_UNION_GEN = `!top s t:A->bool.
        separated_in top s t <=>
        s SUBSET topspace top /\ t SUBSET topspace top /\ DISJOINT s t /\
        open_in (subtopology top (s UNION t)) s /\
        open_in (subtopology top (s UNION t)) t`;;

let SEPARATED_IN_FULL = `!top s t:A->bool.
        s UNION t = topspace top
        ==> (separated_in top s t <=>
             DISJOINT s t /\
             closed_in top s /\ open_in top s /\
             closed_in top t /\ open_in top t)`;;

let HOMEOMORPHIC_MAP_SEPARATION = `!(f:A->B) top top' s t.
        homeomorphic_map (top,top') f /\
        s SUBSET topspace top /\ t SUBSET topspace top
        ==> (separated_in top' (IMAGE f s) (IMAGE f t) <=>
             separated_in top s t)`;;

(* ------------------------------------------------------------------------- *)
(* T_1 spaces with equivalences to many naturally "nice" properties.         *)
(* ------------------------------------------------------------------------- *)

let t1_space = new_definition
 `t1_space top <=>
  !x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
        ==> ?u. open_in top u /\ x IN u /\ ~(y IN u)`;;

let T1_SPACE_EXPANSIVE = `!top top':A topology.
         topspace top' = topspace top /\ (!u. open_in top u ==> open_in top' u)
         ==> t1_space top ==> t1_space top'`;;

let T1_SPACE_ALT = `!top:A topology.
        t1_space top <=>
        !x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
              ==> ?u. closed_in top u /\ x IN u /\ ~(y IN u)`;;

let T1_SPACE_SEPARATED_IN = `!top:A topology.
        t1_space top <=>
        !x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
              ==> separated_in top {x} {y}`;;

let T1_SPACE_DERIVED_SET_OF_SING = `!top:A topology.
      t1_space top <=> !x. x IN topspace top ==> top derived_set_of {x} = {}`;;

let T1_SPACE_DERIVED_SET_OF_FINITE = `!top:A topology.
      t1_space top <=> !s. FINITE s ==> top derived_set_of s = {}`;;

let T1_SPACE_CLOSED_IN_SING = `!top:A topology.
      t1_space top <=> !x. x IN topspace top ==> closed_in top {x}`;;

let CLOSED_IN_T1_SING = `!top a:A. t1_space top /\ a IN topspace top ==> closed_in top {a}`;;

let T1_SPACE_CLOSED_IN_FINITE = `!top:A topology.
      t1_space top <=>
      !s. FINITE s /\ s SUBSET topspace top ==> closed_in top s`;;

let CLOSURE_OF_SING = `!top a:A.
        t1_space top
        ==> top closure_of {a} = if a IN topspace top then {a} else {}`;;

let SEPARATED_IN_SING = `(!top s a:A.
        t1_space top
        ==> (separated_in top {a} s <=>
             a IN topspace top /\ s SUBSET topspace top /\
             ~(a IN top closure_of s))) /\
   (!top s a:A.
        t1_space top
        ==> (separated_in top s {a} <=>
             a IN topspace top /\ s SUBSET topspace top /\
             ~(a IN top closure_of s)))`;;

let T1_SPACE_OPEN_IN_DELETE = `!top:A topology.
        t1_space top <=>
        !u x. open_in top u /\ x IN u ==> open_in top (u DELETE x)`;;

let T1_SPACE_OPEN_IN_DELETE_ALT = `!top:A topology.
        t1_space top <=> !u x. open_in top u ==> open_in top (u DELETE x)`;;

let T1_SPACE_SING_INTERS_OPEN = `(!top:A topology.
      t1_space top <=>
      !x. x IN topspace top ==> INTERS {u | open_in top u /\ x IN u} = {x})`
and T1_SPACE_INTERS_OPEN_SUPERSETS = `(!top:A topology.
      t1_space top <=>
      !s. s SUBSET topspace top
          ==> INTERS {u | open_in top u /\ s SUBSET u} = s)`;;

let T1_SPACE_DERIVED_SET_OF_INFINITE_OPEN_IN = `!top:A topology.
        t1_space top <=>
        !s. top derived_set_of s =
            {x | x IN topspace top /\
                 !u. x IN u /\ open_in top u ==> INFINITE(s INTER u)}`;;

let FINITE_T1_SPACE_IMP_DISCRETE_TOPOLOGY = `!top u:A->bool.
        topspace top = u /\ FINITE u /\ t1_space top
        ==> top = discrete_topology u`;;

let T1_SPACE_SUBTOPOLOGY = `!top u:A->bool.
        t1_space top ==> t1_space(subtopology top u)`;;

let CLOSED_IN_DERIVED_SET_OF_GEN = `!top s:A->bool. t1_space top ==> closed_in top (top derived_set_of s)`;;

let DERIVED_SET_OF_DERIVED_SET_SUBSET_GEN = `!top s:A->bool.
        t1_space top
        ==> top derived_set_of (top derived_set_of s) SUBSET
            top derived_set_of s`;;

let SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_GEN_FINITE = `!top s:A->bool.
        t1_space top /\ FINITE s
        ==> subtopology top s = discrete_topology(topspace top INTER s)`;;

let SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_FINITE = `!top s:A->bool.
        t1_space top /\ s SUBSET topspace top /\ FINITE s
        ==> subtopology top s = discrete_topology s`;;

let T1_SPACE_CLOSED_MAP_IMAGE = `!f:A->B top top'.
        closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        t1_space top
        ==> t1_space top'`;;

let HOMEOMORPHIC_T1_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (t1_space top <=> t1_space top')`;;

let T1_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ t1_space top ==> t1_space top'`;;

let T1_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        t1_space(prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        t1_space top1 /\ t1_space top2`;;

let T1_SPACE_PRODUCT_TOPOLOGY = `!tops:K->A topology k.
        t1_space (product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        !i. i IN k ==> t1_space (tops i)`;;

let CARD_LE_TOPSPACE_CLOSED_SETS = `!top:A topology. t1_space top ==> topspace top <=_c {s | closed_in top s}`;;

let CARD_LE_TOPSPACE_OPEN_SETS = `!top:A topology. t1_space top ==> topspace top <=_c {s | open_in top s}`;;

let INFINITE_PERFECT_SET_GEN = `!top s:A->bool.
        t1_space top /\ s SUBSET top derived_set_of s /\ ~(s = {})
        ==> INFINITE s`;;

(* ------------------------------------------------------------------------- *)
(* Hausdorff spaces.                                                         *)
(* ------------------------------------------------------------------------- *)

let hausdorff_space = new_definition
 `hausdorff_space (top:A topology) <=>
        !x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
              ==> ?u v. open_in top u /\ open_in top v /\ x IN u /\ y IN v /\
                        DISJOINT u v`;;

let HAUSDORFF_SPACE_EXPANSIVE = `!top top':A topology.
         topspace top' = topspace top /\ (!u. open_in top u ==> open_in top' u)
         ==> hausdorff_space top ==> hausdorff_space top'`;;

let HAUSDORFF_SPACE_TOPSPACE_EMPTY = `!top:A topology. topspace top = {} ==> hausdorff_space top`;;

let HAUSDORFF_IMP_T1_SPACE = `!top:A topology. hausdorff_space top ==> t1_space top`;;

let CLOSED_IN_DERIVED_SET_OF = `!(top:A topology) s.
        hausdorff_space top ==> closed_in top (top derived_set_of s)`;;

let T1_OR_HAUSDORFF_SPACE = `!top:A topology.
        t1_space top \/ hausdorff_space top <=> t1_space top`;;

let HAUSDORFF_SPACE_SING_INTERS_OPENS = `!top a:A.
        hausdorff_space top /\ a IN topspace top
        ==> INTERS {u | open_in top u /\ a IN u} =  {a}`;;

let HAUSDORFF_SPACE_SING_INTERS_CLOSED = `!top:A topology.
      hausdorff_space top <=>
      !x. x IN topspace top
          ==> INTERS {u | closed_in top u /\ x IN top interior_of u} = {x}`;;

let HAUSDORFF_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        hausdorff_space top ==> hausdorff_space(subtopology top s)`;;

let HAUSDORFF_SPACE_COMPACT_SEPARATION = `!top s t:A->bool.
        hausdorff_space top /\
        compact_in top s /\ compact_in top t /\ DISJOINT s t
        ==> ?u v. open_in top u /\ open_in top v /\
                  s SUBSET u /\ t SUBSET v /\ DISJOINT u v`;;

let HAUSDORFF_SPACE_COMPACT_SETS = `!top:A topology.
        hausdorff_space top <=>
        !s t. compact_in top s /\ compact_in top t /\ DISJOINT s t
              ==> ?u v. open_in top u /\ open_in top v /\
                        s SUBSET u /\ t SUBSET v /\ DISJOINT u v`;;

let COMPACT_IN_IMP_CLOSED_IN = `!top s:A->bool.
        hausdorff_space top /\ compact_in top s ==> closed_in top s`;;

let CLOSED_IN_HAUSDORFF_SING = `!top x:A. hausdorff_space top /\ x IN topspace top ==> closed_in top {x}`;;

let CLOSED_IN_HAUSDORFF_SING_EQ = `!top x:A. hausdorff_space top
             ==> (closed_in top {x} <=> x IN topspace top)`;;

let HAUSDORFF_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. hausdorff_space(discrete_topology u)`;;

let COMPACT_IN_INTER = `!top s t:A->bool.
        hausdorff_space top /\ compact_in top s /\ compact_in top t
        ==> compact_in top (s INTER t)`;;

let FINITE_TOPSPACE_IMP_DISCRETE_TOPOLOGY = `!top:A topology.
        topspace top = u /\ FINITE u /\ hausdorff_space top
        ==> top = discrete_topology u`;;

let DERIVED_SET_OF_FINITE = `!top s:A->bool.
        hausdorff_space top /\ FINITE s ==> top derived_set_of s = {}`;;

let DERIVED_SET_OF_SING = `!top x:A. hausdorff_space top ==> top derived_set_of {x} = {}`;;

let CLOSED_IN_HAUSDORFF_FINITE = `!top s:A->bool.
        hausdorff_space top /\ s SUBSET topspace top /\ FINITE s
        ==> closed_in top s`;;

let OPEN_IN_HAUSDORFF_DELETE = `!top s x:A.
        hausdorff_space top /\ open_in top s ==> open_in top (s DELETE x)`;;

let CLOSED_IN_HAUSDORFF_FINITE_EQ = `!top s:A->bool.
        hausdorff_space top /\ FINITE s
        ==> (closed_in top s <=> s SUBSET topspace top)`;;

let DERIVED_SET_OF_INFINITE_OPEN_IN = `!top s:A->bool.
        hausdorff_space top
        ==> top derived_set_of s =
            {x | x IN topspace top /\
                 !u. x IN u /\ open_in top u ==> INFINITE(s INTER u)}`;;

let HAUSDORFF_SPACE_DISCRETE_COMPACT_IN = `!top s:A->bool.
        hausdorff_space top
        ==> (s INTER top derived_set_of s = {} /\ compact_in top s <=>
             s SUBSET topspace top /\ FINITE s)`;;

let HAUSDORFF_SPACE_FINITE_TOPSPACE = `!top:A topology.
        hausdorff_space top
        ==> (top derived_set_of (topspace top) = {} /\ compact_space top <=>
             FINITE(topspace top))`;;

let DERIVED_SET_OF_DERIVED_SET_SUBSET = `!top s:A->bool.
        hausdorff_space top
        ==> top derived_set_of (top derived_set_of s) SUBSET
            top derived_set_of s`;;

let HAUSDORFF_SPACE_INJECTIVE_PREIMAGE = `!top top' f:A->B.
       continuous_map (top,top') f /\
       (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y) /\
       hausdorff_space top'
       ==> hausdorff_space top`;;

let HOMEOMORPHIC_HAUSDORFF_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (hausdorff_space top <=> hausdorff_space top')`;;

let HAUSDORFF_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ hausdorff_space top
        ==> hausdorff_space top'`;;

let COMPACT_HAUSDORFF_SPACE_OPTIMAL = `!top top':A topology.
        topspace top' = topspace top /\
        (!u. open_in top u ==> open_in top' u) /\
        hausdorff_space top /\ compact_space top'
        ==> top' = top`;;

let CONTINUOUS_IMP_CLOSED_MAP = `!top top' f:A->B.
        compact_space top /\ hausdorff_space top' /\
        continuous_map (top,top') f
        ==> closed_map (top,top') f`;;

let CONTINUOUS_IMP_QUOTIENT_MAP  = `!top top' f:A->B.
        compact_space top /\ hausdorff_space top' /\
        continuous_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> quotient_map (top,top') f`;;

let CONTINUOUS_IMP_HOMEOMORPHIC_MAP = `!top top' f:A->B.
        compact_space top /\ hausdorff_space top' /\
        continuous_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        (!x y. x IN topspace top /\ y IN topspace top
               ==> (f x = f y <=> x = y))
        ==> homeomorphic_map(top,top') f`;;

let CONTINUOUS_IMP_EMBEDDING_MAP = `!top top' f:A->B.
        compact_space top /\ hausdorff_space top' /\
        continuous_map (top,top') f /\
        (!x y. x IN topspace top /\ y IN topspace top
               ==> (f x = f y <=> x = y))
        ==> embedding_map(top,top') f`;;

let CONTINUOUS_INVERSE_MAP = `!top top' (f:A->B) g s.
        compact_space top /\ hausdorff_space top' /\
        continuous_map (top,top') f /\
        (!x. x IN topspace top ==> g(f x) = x) /\
        s SUBSET IMAGE f (topspace top)
        ==> continuous_map(subtopology top' s,top) g`;;

let HAUSDORFF_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        hausdorff_space(prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        hausdorff_space top1 /\ hausdorff_space top2`;;

let HAUSDORFF_SPACE_PRODUCT_TOPOLOGY = `!tops:K->A topology k.
        hausdorff_space (product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        !i. i IN k ==> hausdorff_space (tops i)`;;

let HAUSDORFF_SPACE_CLOSED_NEIGHBOURHOOD = `!top:A topology.
        hausdorff_space top <=>
        !x. x IN topspace top
            ==> ?u c. open_in top u /\
                      closed_in top c /\
                      hausdorff_space(subtopology top c) /\
                      x IN u /\
                      u SUBSET c`;;

let INFINITE_PERFECT_SET = `!top s:A->bool.
        hausdorff_space top /\ s SUBSET top derived_set_of s /\ ~(s = {})
        ==> INFINITE s`;;

(* ------------------------------------------------------------------------- *)
(* Closed diagonals and graphs.                                              *)
(* ------------------------------------------------------------------------- *)

let HAUSDORFF_SPACE_CLOSED_IN_DIAGONAL = `!top:A topology.
        hausdorff_space top <=>
        closed_in (prod_topology top top) {(x,x) | x IN topspace top}`;;

let CLOSED_MAP_DIAG_EQ = `!top:A topology.
        closed_map(top,prod_topology top top) (\x. x,x) <=>
        hausdorff_space top`;;

let CLOSED_IN_CONTINUOUS_MAPS_EQ = `!(f:A->B) g top top'.
        hausdorff_space top' /\
        continuous_map (top,top') f /\
        continuous_map (top,top') g
        ==> closed_in top {x | x IN topspace top /\ f x = g x}`;;

let FORALL_IN_CLOSURE_OF_EQ = `!top top' f g:A->B.
        hausdorff_space top' /\
        continuous_map (top,top') f /\ continuous_map (top,top') g /\
        (!x. x IN s ==> f x = g x)
        ==> !x. x IN top closure_of s ==> f x = g x`;;

let RETRACT_OF_SPACE_IMP_CLOSED_IN = `!top s:A->bool.
        hausdorff_space top /\ s retract_of_space top ==> closed_in top s`;;

let WEAKLY_HEREDITARY_IMP_RETRACTIVE_PROPERTY = `!(P:A topology->bool) (Q:B topology->bool).
        (!top. P top ==> hausdorff_space top) /\
        (!top s. P top /\ closed_in top s ==> P(subtopology top s)) /\
        (!top top'. top homeomorphic_space top' ==> (P top <=> Q top'))
        ==> !top top' r. retraction_map(top,top') r /\ P top ==> Q top'`;;

let HOMEOMORPHIC_MAPS_GRAPH = `!top top' (f:A->B).
        homeomorphic_maps
         (top,subtopology (prod_topology top top')
                          (IMAGE (\x. x,f x) (topspace top)))
         ((\x. x,f x),FST) <=>
        continuous_map(top,top') f`;;

let EMBEDDING_MAP_GRAPH = `!top top' (f:A->B).
        embedding_map(top,prod_topology top top') (\x. x,f x) <=>
        continuous_map (top,top') f`;;

let CONTINUOUS_MAP_IMP_CLOSED_GRAPH = `!top top' (f:A->B).
        continuous_map(top,top') f /\ hausdorff_space top'
        ==> closed_in (prod_topology top top') {x,f x | x IN topspace top}`;;

let CLOSED_MAP_PAIRED_CONTINUOUS_MAP_RIGHT = `!top top' (f:A->B).
        continuous_map(top,top') f /\ hausdorff_space top'
        ==> closed_map(top,prod_topology top top') (\x. x,f x)`;;

let CLOSED_MAP_PAIRED_CONTINUOUS_MAP_LEFT = `!top top' (f:A->B).
        continuous_map(top,top') f /\ hausdorff_space top'
        ==> closed_map(top,prod_topology top' top) (\x. f x,x)`;;

let EMBEDDING_MAP_ON_DENSE_SUBTOPOLOGY = `!top top' (f:A->B) s.
        hausdorff_space top /\
        s SUBSET topspace top /\
        top closure_of s = topspace top /\
        continuous_map (top,top') f /\
        embedding_map (subtopology top s,top') f
        ==> DISJOINT (IMAGE f s) (IMAGE f (topspace top DIFF s))`;;

(* ------------------------------------------------------------------------- *)
(* KC spaces, those where all compact sets are closed.                       *)
(* ------------------------------------------------------------------------- *)

let kc_space = new_definition
 `kc_space (top:A topology) <=> !s. compact_in top s ==> closed_in top s`;;

let KC_SPACE_EXPANSIVE = `!top top':A topology.
         topspace top' = topspace top /\ (!u. open_in top u ==> open_in top' u)
         ==> kc_space top ==> kc_space top'`;;

let COMPACT_IN_IMP_CLOSED_IN_GEN = `!top s:A->bool. kc_space top /\ compact_in top s ==> closed_in top s`;;

let HAUSDORFF_IMP_KC_SPACE = `!top:A topology. hausdorff_space top ==> kc_space top`;;

let KC_IMP_T1_SPACE = `!top:A topology. kc_space top ==> t1_space top`;;

let KC_SPACE_SUBTOPOLOGY = `!top s:A->bool. kc_space top ==> kc_space(subtopology top s)`;;

let KC_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. kc_space(discrete_topology u)`;;

let KC_SPACE_CONTINUOUS_INJECTIVE_MAP_PREIMAGE = `!top top' (f:A->B).
      continuous_map(top,top') f /\
      (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y) /\
      kc_space top'
      ==> kc_space top`;;

let KC_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ kc_space top ==> kc_space top'`;;

let HOMEOMORPHIC_KC_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (kc_space top <=> kc_space top')`;;

let COMPACT_KC_EQ_MAXIMAL_COMPACT_SPACE = `!top:A topology.
        compact_space top
        ==> (kc_space top <=>
             !top'. topspace top' = topspace top /\
                    (!s. open_in top s ==> open_in top' s) /\
                    compact_space top'
                    ==> top' = top)`;;

let CONTINUOUS_IMP_CLOSED_MAP_GEN = `!top top' (f:A->B).
        compact_space top /\ kc_space top' /\ continuous_map(top,top') f
        ==> closed_map(top,top') f`;;

let KC_SPACE_COMPACT_SUBTOPOLOGIES = `!top:A topology.
        kc_space top <=> !k. compact_in top k ==> kc_space(subtopology top k)`;;

let KC_SPACE_COMPACT_PROD_TOPOLOGY = `!top:A topology.
        compact_space top
        ==> (kc_space(prod_topology top top) <=> hausdorff_space top)`;;

let KC_SPACE_PROD_TOPOLOGY = `!top:A topology.
        kc_space(prod_topology top top) <=>
        !k. compact_in top k ==> hausdorff_space(subtopology top k)`;;

let KC_SPACE_PROD_TOPOLOGY_ALT = `!top:A topology.
        kc_space(prod_topology top top) <=>
        kc_space top /\
        !k. compact_in top k ==> hausdorff_space(subtopology top k)`;;

let KC_SPACE_PROD_TOPOLOGY_LEFT = `!(top:A topology) (top':B topology).
        kc_space top /\ hausdorff_space top'
        ==> kc_space (prod_topology top top')`;;

let KC_SPACE_PROD_TOPOLOGY_RIGHT = `!(top:A topology) (top':B topology).
        hausdorff_space top /\ kc_space top'
        ==> kc_space (prod_topology top top')`;;

let KC_SPACE_PROD_TOPOLOGY_GEN = `!(top:A topology) (top':B topology).
        kc_space top /\ kc_space top' /\
        ((!k. compact_in top k ==> hausdorff_space (subtopology top k)) \/
         (!l. compact_in top' l ==> hausdorff_space (subtopology top' l)))
        ==> kc_space(prod_topology top top')`;;

(* ------------------------------------------------------------------------- *)
(* Proper maps (not a priori assumed continuous)                             *)
(* ------------------------------------------------------------------------- *)

let proper_map = new_definition
 `proper_map (top,top') (f:A->B) <=>
        closed_map (top,top') f /\
        !y. y IN topspace top'
            ==> compact_in top {x | x IN topspace top /\ f x = y}`;;

let PROPER_IMP_CLOSED_MAP = `!top top' (f:A->B). proper_map(top,top') f ==> closed_map(top,top') f`;;

let PROPER_MAP_IMP_SUBSET_TOPSPACE = `!top top' (f:A->B).
      proper_map(top,top') f ==> IMAGE f (topspace top) SUBSET topspace top'`;;

let CLOSED_INJECTIVE_IMP_PROPER_MAP = `!top top' (f:A->B).
        closed_map(top,top') f /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y)
        ==> proper_map(top,top') f`;;

let INJECTIVE_IMP_PROPER_EQ_CLOSED_MAP = `!top top' (f:A->B).
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y)
        ==> (proper_map(top,top') f <=> closed_map(top,top') f)`;;

let PROPER_MAP_DIAG_EQ = `!top:A topology.
        proper_map (top,prod_topology top top) (\x. x,x) <=>
        hausdorff_space top`;;

let HOMEOMORPHIC_IMP_PROPER_MAP = `!top top' (f:A->B).
        homeomorphic_map(top,top') f ==> proper_map(top,top') f`;;

let COMPACT_IN_PROPER_MAP_PREIMAGE = `!top top' (f:A->B) k.
        proper_map(top,top') f /\ compact_in top' k
        ==> compact_in top {x | x IN topspace top /\ f x IN k}`;;

let COMPACT_SPACE_PROPER_MAP_PREIMAGE = `!top top' (f:A->B).
        proper_map(top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        compact_space top'
        ==> compact_space top`;;

let PROPER_MAP_ALT = `!top top' (f:A->B).
        proper_map (top,top') f <=>
        closed_map (top,top') f /\
        !k. compact_in top' k
            ==> compact_in top {x | x IN topspace top /\ f x IN k}`;;

let PROPER_MAP_ON_EMPTY = `!top top' (f:A->B). topspace top = {} ==> proper_map(top,top') f`;;

let PROPER_MAP_ID = `!top:A topology. proper_map(top,top) (\x. x)`;;

let PROPER_MAP_COMPOSE = `!top top' top'' (f:A->B) (g:B->C).
        proper_map(top,top') f /\ proper_map(top',top'') g
        ==> proper_map(top,top'') (g o f)`;;

let PROPER_MAP_CONST = `!(top:A topology) top' (c:B).
        proper_map(top,top') (\x. c) <=>
        compact_space top /\ (topspace top = {} \/ closed_in top' {c})`;;

let PROPER_MAP_INCLUSION = `!top s:A->bool.
        s SUBSET topspace top
        ==> (proper_map(subtopology top s,top) (\x. x) <=>
             closed_in top s /\
             !k. compact_in top k ==> compact_in top (s INTER k))`;;

let PROPER_MAP_PAIRED_CONTINUOUS_MAP_RIGHT = `!top top' (f:A->B).
        continuous_map(top,top') f /\ hausdorff_space top'
        ==> proper_map(top,prod_topology top top') (\x. x,f x)`;;

let PROPER_MAP_PAIRED_CONTINUOUS_MAP_LEFT = `!top top' (f:A->B).
        continuous_map(top,top') f /\ hausdorff_space top'
        ==> proper_map(top,prod_topology top' top) (\x. f x,x)`;;

let COMPACT_IMP_PROPER_MAP_GEN = `!top'. (!s. s SUBSET topspace top' /\
               (!k. compact_in top' k ==> compact_in top' (s INTER k))
               ==> closed_in top' s)
          ==> !top (f:A->B).
                   IMAGE f (topspace top) SUBSET topspace top' /\
                   (continuous_map(top,top') f \/ kc_space top) /\
                   (!k. compact_in top' k
                        ==> compact_in top {x | x IN topspace top /\ f x IN k})
                   ==> proper_map(top,top') f`;;

let CONTINUOUS_CLOSED_IMP_PROPER_MAP = `!top top' (f:A->B).
        compact_space top /\
        t1_space top' /\
        continuous_map (top,top') f /\
        closed_map (top,top') f
        ==> proper_map (top,top') f`;;

let CONTINUOUS_IMP_PROPER_MAP = `!top top' (f:A->B).
        compact_space top /\
        kc_space top' /\
        continuous_map (top,top') f
        ==> proper_map (top,top') f`;;

let PROPER_IMP_CONTINUOUS_MAP = `!top top' (f:A->B).
        kc_space top /\
        compact_space top' /\
        proper_map (top,top') f
        ==> continuous_map (top,top') f`;;

let PROPER_MAP_FST = `!(top:A topology) (top':B topology).
        proper_map(prod_topology top top',top) FST <=>
        topspace top = {} \/ compact_space top'`;;

let PROPER_MAP_SND = `!(top:A topology) (top':B topology).
        proper_map(prod_topology top top',top') SND <=>
        compact_space top \/ topspace top' = {}`;;

let PROPER_MAP_INTO_SUBTOPOLOGY = `!top top' (f:A->B) c.
        proper_map (top,top') f /\ IMAGE f (topspace top) SUBSET c
        ==> proper_map (top,subtopology top' c) f`;;

let PROPER_MAP_FROM_SUBTOPOLOGY = `!top top' (f:A->B) c.
        proper_map (top,top') f /\ closed_in top c
        ==> proper_map (subtopology top c,top') f`;;

let PROPER_MAP_RESTRICTION = `!top top' (f:A->B) u v.
        proper_map (top,top') f /\ {x | x IN topspace top /\ f x IN v} = u
        ==> proper_map (subtopology top u,subtopology top' v) f`;;

let PROPER_MAP_IN_SUBTOPOLOGY = `!top top' s (f:A->B).
        closed_in top' s
        ==> (proper_map(top,subtopology top' s) f <=>
             proper_map(top,top') f /\ IMAGE f (topspace top) SUBSET s)`;;

let PROPER_MAP_FROM_CLOSED_SUBTOPOLOGY = `!top top' s (f:A->B).
        closed_in top' s /\ proper_map(top,subtopology top' s) f
        ==> proper_map(top,top') f`;;

let PROPER_MAP_FROM_COMPOSITION_LEFT = `!top top' top'' (f:A->B) (g:B->C).
        proper_map(top,top'') (g o f) /\
        continuous_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> proper_map(top',top'') g`;;

let PROPER_MAP_FROM_COMPOSITION_RIGHT_INJ = `!top top' top'' (f:A->B) (g:B->C).
        proper_map(top,top'') (g o f) /\
        IMAGE f (topspace top) SUBSET topspace top' /\
        continuous_map(top',top'') g /\
        (!x y. x IN topspace top' /\ y IN topspace top' /\ g x = g y
               ==> x = y)
        ==> proper_map(top,top') f`;;

let PROPER_MAP_PROD = `!top1 top1' top2 top2' (f:A->C) (g:B->D).
        proper_map (prod_topology top1 top2,prod_topology top1' top2')
                   (\(x,y). f x,g y) <=>
        topspace(prod_topology top1 top2) = {} \/
        proper_map (top1,top1') f /\ proper_map (top2,top2') g`;;

let PROPER_MAP_PAIRED = `!top top1 top2 (f:A->B) (g:A->C).
        hausdorff_space top /\
        proper_map(top,top1) f /\ proper_map(top,top2) g \/
        hausdorff_space top1 /\
        continuous_map(top,top1) f /\ proper_map(top,top2) g \/
        hausdorff_space top2 /\
        proper_map(top,top1) f /\ continuous_map(top,top2) g
        ==> proper_map (top,prod_topology top1 top2) (\x. f x,g x)`;;

let PROPER_MAP_PAIRWISE = `!top top1 top2 f:A->B#C.
        hausdorff_space top /\
        proper_map(top,top1) (FST o f) /\ proper_map(top,top2) (SND o f) \/
        hausdorff_space top1 /\
        continuous_map(top,top1) (FST o f) /\ proper_map(top,top2) (SND o f) \/
        hausdorff_space top2 /\
        proper_map(top,top1) (FST o f) /\ continuous_map(top,top2) (SND o f)
        ==> proper_map (top,prod_topology top1 top2) f`;;

let PROPER_MAP_FROM_COMPOSITION_RIGHT = `!top top' top'' (f:A->B) (g:B->C).
        hausdorff_space top' /\
        proper_map(top,top'') (g o f) /\
        continuous_map(top,top') f /\
        continuous_map(top',top'') g
        ==> proper_map(top,top') f`;;

let CONTINUOUS_EXTENSION_OF_PROPER_MAP_FROM_SUBTOPOLOGY = `!top top' (f:A->B).
        hausdorff_space top /\
        s SUBSET topspace top /\
        continuous_map (top,top') f /\
        proper_map(subtopology top s,top') f
        ==> closed_in top s`;;

(* ------------------------------------------------------------------------- *)
(* Perfect maps (proper, continuous and surjective).                         *)
(* ------------------------------------------------------------------------- *)

let perfect_map = new_definition
 `perfect_map (top,top') (f:A->B) <=>
        continuous_map(top,top') f /\
        proper_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'`;;

let HOMEOMORPHIC_IMP_PERFECT_MAP = `!top top' (f:A->B).
        homeomorphic_map(top,top') f ==> perfect_map(top,top') f`;;

let PERFECT_IMP_QUOTIENT_MAP = `!top top' (f:A->B). perfect_map(top,top') f ==> quotient_map(top,top') f`;;

let HOMEOMORPHIC_EQ_INJECTIVE_PERFECT_MAP = `!top top' (f:A->B).
        homeomorphic_map(top,top') f <=>
        perfect_map(top,top') f /\
        !x y. x IN topspace top /\ y IN topspace top
              ==> (f x = f y <=> x = y)`;;

let PERFECT_INJECTIVE_EQ_HOMEOMORPHIC_MAP = `!top top' (f:A->B).
      perfect_map(top,top') f /\
      (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y) <=>
      homeomorphic_map(top,top') f`;;

let PERFECT_MAP_ID = `!top:A topology. perfect_map(top,top) (\x. x)`;;

let PERFECT_MAP_COMPOSE = `!top top' top'' (f:A->B) (g:B->C).
        perfect_map(top,top') f /\ perfect_map(top',top'') g
        ==> perfect_map(top,top'') (g o f)`;;

let PERFECT_IMP_CONTINUOUS_MAP = `!top top' (f:A->B).
        perfect_map(top,top') f ==> continuous_map(top,top') f`;;

let PERFECT_IMP_CLOSED_MAP = `!top top' (f:A->B).
        perfect_map(top,top') f ==> closed_map(top,top') f`;;

let PERFECT_IMP_PROPER_MAP = `!top top' (f:A->B).
        perfect_map(top,top') f ==> proper_map(top,top') f`;;

let PERFECT_IMP_SURJECTIVE_MAP = `!top top' (f:A->B).
        perfect_map(top,top') f ==> IMAGE f (topspace top) = topspace top'`;;

let CONTINUOUS_CLOSED_IMP_PERFECT_MAP = `!top top' (f:A->B).
        compact_space top /\ t1_space top' /\
        continuous_map (top,top') f /\
        closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> perfect_map (top,top') f`;;

let CONTINUOUS_IMP_PEFECT_MAP = `!top top' (f:A->B).
        compact_space top /\ kc_space top' /\
        continuous_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> perfect_map (top,top') f`;;

let PERFECT_MAP_FST = `!(top:A topology) (top':B topology).
        perfect_map(prod_topology top top',top) FST <=>
        (topspace top = {} \/ compact_space top') /\
        (topspace top' = {} ==> topspace top = {})`;;

let PERFECT_MAP_SND = `!(top:A topology) (top':B topology).
        perfect_map(prod_topology top top',top') SND <=>
        (topspace top' = {} \/ compact_space top) /\
        (topspace top = {} ==> topspace top' = {})`;;

let PERFECT_MAP_RESTRICTION = `!top top' (f:A->B) u v.
        perfect_map (top,top') f /\ {x | x IN topspace top /\ f x IN v} = u
        ==> perfect_map (subtopology top u,subtopology top' v) f`;;

let PERFECT_MAP_FROM_COMPOSITION_LEFT = `!top top' top'' (f:A->B) (g:B->C).
        perfect_map(top,top'') (g o f) /\
        continuous_map(top,top') f /\
        continuous_map(top',top'') g /\
        IMAGE f (topspace top) = topspace top'
        ==> perfect_map(top',top'') g`;;

let PERFECT_MAP_FROM_COMPOSITION_RIGHT = `!top top' top'' (f:A->B) (g:B->C).
        hausdorff_space top' /\
        perfect_map(top,top'') (g o f) /\
        continuous_map(top,top') f /\
        continuous_map(top',top'') g /\
        IMAGE f (topspace top) = topspace top'
        ==> perfect_map(top,top') f`;;

let PERFECT_MAP_FROM_COMPOSITION_RIGHT_INJ = `!top top' top'' (f:A->B) (g:B->C).
        perfect_map(top,top'') (g o f) /\
        IMAGE f (topspace top) = topspace top' /\
        continuous_map(top,top') f /\
        continuous_map(top',top'') g /\
        (!x y. x IN topspace top' /\ y IN topspace top' /\ g x = g y
               ==> x = y)
        ==> perfect_map(top,top') f`;;

(* ------------------------------------------------------------------------- *)
(* Preservation theorems for proper or perfect maps.                         *)
(* ------------------------------------------------------------------------- *)

let DISCRETE_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
        discrete_space top /\ perfect_map (top,top') f
        ==> discrete_space top'`;;

let KC_SPACE_PROPER_MAP_IMAGE = `!top top' (f:A->B).
        kc_space top /\
        proper_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> kc_space top'`;;

let KC_SPACE_CLOSED_CONTINUOUS_MAP_IMAGE = `!top top' (f:A->B).
        kc_space top /\
        compact_space top /\
        closed_map(top,top') f /\
        continuous_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> kc_space top'`;;

let KC_SPACE_CLOSED_CONTINUOUS_MAP_IMAGE_EQ = `!top top' (f:A->B).
        kc_space top /\
        compact_space top /\
        continuous_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> (closed_map(top,top') f <=> kc_space top')`;;

let HAUSDORFF_SPACE_PROPER_MAP_IMAGE = `!top top' (f:A->B).
        hausdorff_space top /\
        proper_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> hausdorff_space top'`;;

let HAUSDORFF_SPACE_CLOSED_CONTINUOUS_MAP_IMAGE = `!top top' (f:A->B).
        compact_space top /\ hausdorff_space top /\
        closed_map(top,top') f /\ continuous_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> hausdorff_space top'`;;

let HAUSDORFF_SPACE_CLOSED_CONTINUOUS_MAP_IMAGE_EQ = `!top top' (f:A->B).
        compact_space top /\ hausdorff_space top /\
        continuous_map(top,top') f /\ IMAGE f (topspace top) = topspace top'
        ==> (closed_map(top,top') f <=> hausdorff_space top')`;;

let HAUSDORFF_SPACE_CONTINUOUS_MAP_IMAGE = `!top top' (f:A->B).
        compact_space top /\ hausdorff_space top /\ kc_space top' /\
        continuous_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> hausdorff_space top'`;;

let HAUSDORFF_SPACE_CONTINUOUS_MAP_IMAGE_EQ = `!top top' (f:A->B).
        compact_space top /\ hausdorff_space top /\
        continuous_map(top,top') f /\ IMAGE f (topspace top) = topspace top'
        ==> (hausdorff_space top' <=> kc_space top')`;;

let T1_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
        t1_space top /\ perfect_map(top,top') f ==> t1_space top'`;;

let HAUSDORFF_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
    hausdorff_space top /\ perfect_map(top,top') f ==> hausdorff_space top'`;;

let COMPACT_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
    compact_space top /\ perfect_map(top,top') f ==> compact_space top'`;;

let COMPACT_SPACE_PERFECT_MAP_IMAGE_EQ = `!top top' (f:A->B).
      perfect_map(top,top') f ==> (compact_space top <=> compact_space top')`;;

let KC_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
      kc_space top /\ perfect_map(top,top') f
      ==> kc_space top'`;;

(* ------------------------------------------------------------------------- *)
(* Lindelof spaces.                                                          *)
(* ------------------------------------------------------------------------- *)

let lindelof_space = new_definition
 `lindelof_space (top:A topology) <=>
        !U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
            ==> ?V. COUNTABLE V /\ V SUBSET U /\ UNIONS V = topspace top`;;

let LINDELOF_SPACE_ALT = `!top:A topology.
        lindelof_space top <=>
        !U. (!u. u IN U ==> open_in top u) /\
            topspace top SUBSET UNIONS U
            ==> ?V. COUNTABLE V /\ V SUBSET U /\ topspace top SUBSET UNIONS V`;;

let COMPACT_IMP_LINDELOF_SPACE = `!top:A topology. compact_space top ==> lindelof_space top`;;

let LINDELOF_SPACE_TOPSPACE_EMPTY = `!top:A topology. topspace top = {} ==> lindelof_space top`;;

let LINDELOF_SPACE_UNIONS = `!top U:(A->bool)->bool.
        COUNTABLE U /\
        (!c. c IN U ==> lindelof_space (subtopology top c))
        ==> lindelof_space (subtopology top (UNIONS U))`;;

let COUNTABLE_IMP_LINDELOF_SPACE = `!top:A topology. COUNTABLE(topspace top) ==> lindelof_space top`;;

let LINDELOF_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        lindelof_space(subtopology top s) <=>
        !U. (!u. u IN U ==> open_in top u) /\
            topspace top INTER s SUBSET UNIONS U
            ==> ?V. COUNTABLE V /\ V SUBSET U /\
                    topspace top INTER s SUBSET UNIONS V`;;

let LINDELOF_SPACE_SUBTOPOLOGY_SUBSET = `!top s:A->bool.
        s SUBSET topspace top
        ==> (lindelof_space(subtopology top s) <=>
             !U. (!u. u IN U ==> open_in top u) /\ s SUBSET UNIONS U
                 ==> ?V. COUNTABLE V /\ V SUBSET U /\ s SUBSET UNIONS V)`;;

let LINDELOF_SPACE_CLOSED_IN_SUBTOPOLOGY = `!top s:A->bool.
        lindelof_space top /\ closed_in top s
        ==> lindelof_space(subtopology top s)`;;

let LINDELOF_SPACE_CONTINUOUS_MAP_IMAGE = `!top top' f:A->B.
        lindelof_space top /\
        continuous_map (top,top') f /\ IMAGE f (topspace top) = topspace top'
        ==> lindelof_space top'`;;

let LINDELOF_SPACE_QUOTIENT_MAP_IMAGE = `!top top' (q:A->B).
        quotient_map(top,top') q /\ lindelof_space top
        ==> lindelof_space top'`;;

let LINDELOF_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ lindelof_space top
        ==> lindelof_space top'`;;

let LOCALLY_FINITE_COVER_OF_LINDELOF_SPACE = `!(top:A topology) u.
        lindelof_space top /\
        topspace top SUBSET UNIONS u /\
        locally_finite_in top u
        ==> COUNTABLE u`;;

let LINDELOF_SPACE_PROPER_MAP_PREIMAGE = `!top top' (f:A->B).
        proper_map(top,top') f /\ lindelof_space top'
        ==> lindelof_space top`;;

let LINDELOF_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
    lindelof_space top /\ perfect_map(top,top') f ==> lindelof_space top'`;;

let LINDELOF_SPACE_PERFECT_MAP_IMAGE_EQ = `!top top' (f:A->B).
      perfect_map(top,top') f ==> (lindelof_space top <=> lindelof_space top')`;;

(* ------------------------------------------------------------------------- *)
(* Other countability properties.                                            *)
(* ------------------------------------------------------------------------- *)

let second_countable = new_definition
 `second_countable (top:A topology) <=>
         ?b. COUNTABLE b /\
             (!v. v IN b ==> open_in top v) /\
             (!u x. open_in top u /\ x IN u
                    ==> ?v. v IN b /\ x IN v /\ v SUBSET u)`;;

let first_countable = new_definition
 `first_countable (top:A topology) <=>
        !x. x IN topspace top
            ==> ?b. COUNTABLE b /\
                    (!v. v IN b ==> open_in top v) /\
                    (!u. open_in top u /\ x IN u
                         ==> ?v. v IN b /\ x IN v /\ v SUBSET u)`;;

let separable_space = new_definition
 `separable_space (top:A topology) <=>
        ?c. COUNTABLE c /\
            c SUBSET topspace top /\
            top closure_of c = topspace top`;;

let SECOND_COUNTABLE = `!top:A topology.
        second_countable top <=>
        ?b. COUNTABLE b /\ open_in top = ARBITRARY UNION_OF b`;;

let SECOND_COUNTABLE_SUBTOPOLOGY = `!top (s:A->bool).
        second_countable top ==> second_countable(subtopology top s)`;;

let SECOND_COUNTABLE_DISCRETE_TOPOLOGY = `!u:A->bool. second_countable(discrete_topology u) <=> COUNTABLE u`;;

let SECOND_COUNTABLE_OPEN_MAP_IMAGE = `!(f:A->B) top top'.
        continuous_map(top,top') f /\ open_map(top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        second_countable top
        ==> second_countable top'`;;

let HOMEOMORPHIC_SPACE_SECOND_COUNTABILITY = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (second_countable top <=> second_countable top')`;;

let SECOND_COUNTABLE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ second_countable top
        ==> second_countable top'`;;

let SECOND_COUNTABLE_IMP_FIRST_COUNTABLE = `!top:A topology. second_countable top ==> first_countable top`;;

let FIRST_COUNTABLE_SUBTOPOLOGY = `!top s:A->bool. first_countable top ==> first_countable(subtopology top s)`;;

let FIRST_COUNTABLE_DISCRETE_TOPOLOGY = `!u:A->bool. first_countable(discrete_topology u)`;;

let FIRST_COUNTABLE_OPEN_MAP_IMAGE = `!(f:A->B) top top'.
        continuous_map(top,top') f /\ open_map(top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        first_countable top
        ==> first_countable top'`;;

let HOMEOMORPHIC_SPACE_FIRST_COUNTABILITY = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (first_countable top <=> first_countable top')`;;

let FIRST_COUNTABLE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ first_countable top
        ==> first_countable top'`;;

let SEPARABLE_SPACE_OPEN_SUBSET = `!top s:A->bool.
        separable_space top /\ open_in top s
        ==> separable_space(subtopology top s)`;;

let SEPARABLE_SPACE_CONTINUOUS_MAP_IMAGE = `!top top' f:A->B.
        separable_space top /\
        continuous_map (top,top') f /\ IMAGE f (topspace top) = topspace top'
        ==> separable_space top'`;;

let SEPARABLE_SPACE_QUOTIENT_MAP_IMAGE = `!top top' (q:A->B).
        quotient_map(top,top') q /\ separable_space top
        ==> separable_space top'`;;

let SEPARABLE_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ separable_space top
        ==> separable_space top'`;;

let HOMEOMORPHIC_SEPARABLE_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (separable_space top <=> separable_space top')`;;

let SEPARABLE_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. separable_space(discrete_topology u) <=> COUNTABLE u`;;

let SECOND_COUNTABLE_IMP_SEPARABLE_SPACE = `!top:A topology. second_countable top ==> separable_space top`;;

let SECOND_COUNTABLE_IMP_LINDELOF_SPACE = `!top:A topology. second_countable top ==> lindelof_space top`;;

(* ------------------------------------------------------------------------- *)
(* A variant of nets (slightly non-standard but good for our purposes).      *)
(* ------------------------------------------------------------------------- *)

let net_tybij = new_type_definition "net" ("mk_net","dest_net")
 (prove
   (`?g:((A->bool)->bool)#(A->bool).
        !s t. s IN FST g /\ t IN FST g ==> (s INTER t) IN FST g`,
    REWRITE_TAC[EXISTS_PAIR_THM] THEN EXISTS_TAC `(:A->bool)` THEN
    REWRITE_TAC[IN_UNIV]));;

let netfilter = new_definition
 `netfilter(n:A net) = FST(dest_net n)`;;

let netlimits = new_definition
 `netlimits(n:A net) = SND(dest_net n)`;;

let netlimit = new_definition
 `netlimit(n:A net) = @x. x IN netlimits n`;;

let NET = `!n s t. !s t. s IN netfilter n /\ t IN netfilter n
                 ==> (s INTER t) IN netfilter n`;;

(* ------------------------------------------------------------------------- *)
(* The generic "within" modifier for nets.                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("within",(14,"right"));;

let within = new_definition
  `net within s = mk_net (netfilter net relative_to s,netlimits net)`;;

let WITHIN = `(!n s:A->bool. netfilter(n within s) = netfilter n relative_to s)`
and NETLIMITS_WITHIN = `(!n s:A->bool. netlimits(n within s) = netlimits n)`;;

let NET_WITHIN_UNIV = `!net. net within (:A) = net`;;

let WITHIN_WITHIN = `!net s t. (net within s) within t = net within (s INTER t)`;;

(* ------------------------------------------------------------------------- *)
(* Some property holds "eventually" for a net.                               *)
(* ------------------------------------------------------------------------- *)

let eventually = new_definition
 `eventually (P:A->bool) net <=>
        netfilter net = {} \/
        ?u. u IN netfilter net /\
            !x. x IN u DIFF netlimits net ==> P x`;;

let trivial_limit = new_definition
  `trivial_limit net <=> eventually (\x. F) net`;;

let EVENTUALLY_WITHIN_IMP = `!net (P:A->bool) s.
        eventually P (net within s) <=>
        eventually (\x. x IN s ==> P x) net`;;

let EVENTUALLY_IMP_WITHIN = `!net (P:A->bool) s.
        eventually P net ==> eventually P (net within s)`;;

let EVENTUALLY_WITHIN_INTER_IMP = `!net (P:A->bool) s t.
        eventually P (net within s INTER t) <=>
        eventually (\x. x IN t ==> P x) (net within s)`;;

let NONTRIVIAL_LIMIT_WITHIN = `!net s. trivial_limit net ==> trivial_limit(net within s)`;;

let EVENTUALLY_HAPPENS = `!net p. eventually p net ==> trivial_limit net \/ ?x. p x`;;

let ALWAYS_EVENTUALLY = `(!x. p x) ==> eventually p net`;;

let EVENTUALLY_MONO = `!net:(A net) p q.
        (!x. p x ==> q x) /\ eventually p net
        ==> eventually q net`;;

let EVENTUALLY_AND = `!net:(A net) p q.
        eventually (\x. p x /\ q x) net <=>
        eventually p net /\ eventually q net`;;

let EVENTUALLY_MP = `!net:(A net) p q.
        eventually (\x. p x ==> q x) net /\ eventually p net
        ==> eventually q net`;;

let EVENTUALLY_EQ_MP = `!net P Q. eventually (\x:A. P x <=> Q x) net /\ eventually P net
             ==> eventually Q net`;;

let EVENTUALLY_IFF = `!net P Q. eventually (\x:A. P x <=> Q x) net
             ==> (eventually P net <=> eventually Q net)`;;

let EVENTUALLY_FALSE = `!net. eventually (\x. F) net <=> trivial_limit net`;;

let EVENTUALLY_TRUE = `!net. eventually (\x. T) net <=> T`;;

let EVENTUALLY_WITHIN_SUBSET = `!P net s t:A->bool.
    eventually P (net within s) /\ t SUBSET s ==> eventually P (net within t)`;;

let ALWAYS_WITHIN_EVENTUALLY = `!net P. (!x. x IN s ==> P x) ==> eventually P (net within s)`;;

let NOT_EVENTUALLY = `!net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)`;;

let EVENTUALLY_FORALL = `!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)`;;

let FORALL_EVENTUALLY = `!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> ((!a. a IN s ==> eventually (p a) net) <=>
             eventually (\x. !a. a IN s ==> p a x) net)`;;

let EVENTUALLY_TRIVIAL = `!net P:A->bool. trivial_limit net ==> eventually P net`;;

(* ------------------------------------------------------------------------- *)
(* Sequential limits.                                                        *)
(* ------------------------------------------------------------------------- *)

let sequentially = new_definition
  `sequentially = mk_net({from n | n IN (:num)},{})`;;

let SEQUENTIALLY = `(!n. netfilter sequentially = {from n | n IN (:num)})`
and NETLIMITS_SEQUENTIALLY = `(netlimits sequentially = {})`;;

let EVENTUALLY_SEQUENTIALLY = `!p. eventually p sequentially <=> ?N. !n. N <= n ==> p n`;;

let TRIVIAL_LIMIT_SEQUENTIALLY = `~(trivial_limit sequentially)`;;

let EVENTUALLY_HAPPENS_SEQUENTIALLY = `!P. eventually P sequentially ==> ?n. P n`;;

let EVENTUALLY_SEQUENTIALLY_WITHIN = `!k p. eventually p (sequentially within k) <=>
         FINITE k \/ (?N. !n. n IN k /\ N <= n ==> p n)`;;

let TRIVIAL_LIMIT_SEQUENTIALLY_WITHIN = `!k. trivial_limit (sequentially within k) <=> FINITE k`;;

let EVENTUALLY_SUBSEQUENCE = `!P r. (!m n. m < n ==> r m < r n) /\ eventually P sequentially
         ==> eventually (P o r) sequentially`;;

let ARCH_EVENTUALLY_LT = `!x. eventually (\n. x < &n) sequentially`;;

let ARCH_EVENTUALLY_LE = `!x. eventually (\n. x <= &n) sequentially`;;

let ARCH_EVENTUALLY_ABS_INV_OFFSET = `!a e. eventually (\n. abs(inv(&n + a)) < e) sequentially <=> &0 < e`;;

let ARCH_EVENTUALLY_INV_OFFSET = `!a e. eventually (\n. inv (&n + a) < e) sequentially <=> &0 < e`;;

let ARCH_EVENTUALLY_INV1 = `!e. eventually (\n. inv(&n + &1) < e) sequentially <=> &0 < e`;;

let ARCH_EVENTUALLY_INV = `!e. eventually (\n. inv(&n) < e) sequentially <=> &0 < e`;;

let ARCH_EVENTUALLY_POW = `!x b. &1 < x ==> eventually (\n. b < x pow n) sequentially`;;

let ARCH_EVENTUALLY_POW_INV = `!x e. &0 < e /\ abs(x) < &1
         ==> eventually (\n. abs(x pow n) < e) sequentially`;;

let EVENTUALLY_IN_SEQUENTIALLY = `!P. eventually P sequentially <=> FINITE {n | ~P n}`;;

let EVENTUALLY_NO_SUBSEQUENCE = `!P. eventually P sequentially <=>
       ~(?r:num->num. (!m n. m < n ==> r m < r n) /\ (!n. ~P(r n)))`;;

let EVENTUALLY_UBOUND_LE_SEQUENTIALLY = `!f. (?b. eventually (\n. f n <= b) sequentially) <=> (?b. !n. f n <= b)`;;

let EVENTUALLY_LBOUND_LE_SEQUENTIALLY = `!f. (?b. eventually (\n. b <= f n) sequentially) <=> (?b. !n. b <= f n)`;;

(* ------------------------------------------------------------------------- *)
(* F_sigma and G_delta sets in a topological space.                          *)
(* ------------------------------------------------------------------------- *)

let fsigma_in = new_definition
 `fsigma_in (top:A topology) = COUNTABLE UNION_OF closed_in top`;;

let gdelta_in = new_definition
 `gdelta_in (top:A topology) =
        (COUNTABLE INTERSECTION_OF open_in top) relative_to topspace top`;;

let FSIGMA_IN_ASCENDING = `!top s:A->bool.
        fsigma_in top s <=>
        ?c. (!n. closed_in top (c n)) /\
            (!n. c n SUBSET c(n + 1)) /\
            UNIONS {c n | n IN (:num)} = s`;;

let GDELTA_IN_ALT = `!top s:A->bool.
        gdelta_in top s <=>
        s SUBSET topspace top /\ (COUNTABLE INTERSECTION_OF open_in top) s`;;

let FSIGMA_IN_SUBSET = `!top s:A->bool. fsigma_in top s ==> s SUBSET topspace top`;;

let GDELTA_IN_SUBSET = `!top s:A->bool. gdelta_in top s ==> s SUBSET topspace top`;;

let CLOSED_IMP_FSIGMA_IN = `!top s:A->bool. closed_in top s ==> fsigma_in top s`;;

let OPEN_IMP_GDELTA_IN = `!top s:A->bool. open_in top s ==> gdelta_in top s`;;

let FSIGMA_IN_EMPTY = `!top:A topology. fsigma_in top {}`;;

let GDELTA_IN_EMPTY = `!top:A topology. gdelta_in top {}`;;

let FSIGMA_IN_TOPSPACE = `!top:A topology. fsigma_in top (topspace top)`;;

let GDELTA_IN_TOPSPACE = `!top:A topology. gdelta_in top (topspace top)`;;

let FSIGMA_IN_UNIONS = `!top t:(A->bool)->bool.
        COUNTABLE t /\ (!s. s IN t ==> fsigma_in top s)
        ==> fsigma_in top (UNIONS t)`;;

let FSIGMA_IN_UNION = `!top s t:A->bool.
        fsigma_in top s /\ fsigma_in top t ==> fsigma_in top (s UNION t)`;;

let FSIGMA_IN_INTER = `!top s t:A->bool.
        fsigma_in top s /\ fsigma_in top t ==> fsigma_in top (s INTER t)`;;

let GDELTA_IN_INTERS = `!top t:(A->bool)->bool.
        COUNTABLE t /\ ~(t = {}) /\ (!s. s IN t ==> gdelta_in top s)
        ==> gdelta_in top (INTERS t)`;;

let GDELTA_IN_INTER = `!top s t:A->bool.
        gdelta_in top s /\ gdelta_in top t ==> gdelta_in top (s INTER t)`;;

let GDELTA_IN_UNION = `!top s t:A->bool.
        gdelta_in top s /\ gdelta_in top t ==> gdelta_in top (s UNION t)`;;

let FSIGMA_IN_DIFF = `!top s t:A->bool.
        fsigma_in top s /\ gdelta_in top t ==> fsigma_in top (s DIFF t)`;;

let GDELTA_IN_DIFF = `!top s t:A->bool.
        gdelta_in top s /\ fsigma_in top t ==> gdelta_in top (s DIFF t)`;;

let GDELTA_IN_FSIGMA_IN = `!top s:A->bool.
       gdelta_in top s <=>
       s SUBSET topspace top /\ fsigma_in top (topspace top DIFF s)`;;

let FSIGMA_IN_GDELTA_IN = `!top s:A->bool.
        fsigma_in top s <=>
        s SUBSET topspace top /\ gdelta_in top (topspace top DIFF s)`;;

let GDELTA_IN_DESCENDING = `!top s:A->bool.
        gdelta_in top s <=>
        ?c. (!n. open_in top (c n)) /\
            (!n. c(n + 1) SUBSET c n) /\
            INTERS {c n | n IN (:num)} = s`;;

let HOMEOMORPHIC_MAP_FSIGMANESS = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f /\ u SUBSET topspace top
        ==> (fsigma_in top' (IMAGE f u) <=> fsigma_in top u)`;;

let HOMEOMORPHIC_MAP_FSIGMANESS_EQ = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f
        ==> (fsigma_in top u <=>
             u SUBSET topspace top /\ fsigma_in top' (IMAGE f u))`;;

let HOMEOMORPHIC_MAP_GDELTANESS = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f /\ u SUBSET topspace top
        ==> (gdelta_in top' (IMAGE f u) <=> gdelta_in top u)`;;

let HOMEOMORPHIC_MAP_GDELTANESS_EQ = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f
        ==> (gdelta_in top u <=>
             u SUBSET topspace top /\ gdelta_in top' (IMAGE f u))`;;

let FSIGMA_IN_RELATIVE_TO = `!top s:A->bool.
        (fsigma_in top relative_to s) = fsigma_in (subtopology top s)`;;

let FSIGMA_IN_SUBTOPOLOGY = `!top u s:A->bool.
         fsigma_in (subtopology top u) s <=>
         ?t. fsigma_in top t /\ s = t INTER u`;;

let GDELTA_IN_RELATIVE_TO = `!top s:A->bool.
        (gdelta_in top relative_to s) = gdelta_in (subtopology top s)`;;

let GDELTA_IN_SUBTOPOLOGY = `!top u s:A->bool.
         gdelta_in (subtopology top u) s <=>
         ?t. gdelta_in top t /\ s = t INTER u`;;

let FSIGMA_IN_FSIGMA_SUBTOPOLOGY = `!top s t:A->bool.
        fsigma_in top s
        ==> (fsigma_in (subtopology top s) t <=>
             fsigma_in top t /\ t SUBSET s)`;;

let GDELTA_IN_GDELTA_SUBTOPOLOGY = `!top s t:A->bool.
        gdelta_in top s
        ==> (gdelta_in (subtopology top s) t <=>
             gdelta_in top t /\ t SUBSET s)`;;

(* ------------------------------------------------------------------------- *)
(* Borel sets                                                                *)
(* ------------------------------------------------------------------------- *)

let borel_in_RULES,borel_in_INDUCT,borel_in_CASES = new_inductive_definition
 `(!s:A->bool. open_in top s ==> borel_in top s) /\
  (!s:A->bool. borel_in top s ==> borel_in top (topspace top DIFF s)) /\
  (!u:(A->bool)->bool.
       COUNTABLE u /\ (!s. s IN u ==> borel_in top s)
       ==> borel_in top (UNIONS u))`;;

let OPEN_IMP_BOREL_IN = `!top s:A->bool. open_in top s ==> borel_in top s`;;

let BOREL_IN_COMPLEMENT = `!top s:A->bool.
        borel_in top s ==> borel_in top (topspace top DIFF s)`;;

let BOREL_IN_COMPLEMENT_EQ = `!top s:A->bool.
     s SUBSET topspace top
     ==> (borel_in top (topspace top DIFF s) <=> borel_in top s)`;;

let BOREL_IN_UNIONS = `!top (u:(A->bool)->bool).
        COUNTABLE u /\ (!s. s IN u ==> borel_in top s)
        ==> borel_in top (UNIONS u)`;;

let BOREL_IN_SUBSET_TOPSPACE = `!top s:A->bool. borel_in top s ==> s SUBSET topspace top`;;

let BOREL_IN_TOPSPACE = `!top:A topology. borel_in top (topspace top)`;;

let BOREL_IN_EMPTY = `!top:A topology. borel_in top {}`;;

let BOREL_IN_INTERS = `!top (u:(A->bool)->bool).
     COUNTABLE u /\ ~(u = {}) /\ (!s. s IN u ==> borel_in top s)
     ==> borel_in top (INTERS u)`;;

let BOREL_IN_UNION = `!top s t:A->bool.
     borel_in top s /\ borel_in top t ==> borel_in top (s UNION t)`;;

let BOREL_IN_INTER = `!top s t:A->bool.
     borel_in top s /\ borel_in top t ==> borel_in top (s INTER t)`;;

let BOREL_IN_DIFF = `!top s t:A->bool.
     borel_in top s /\ borel_in top t ==> borel_in top (s DIFF t)`;;

let CLOSED_IMP_BOREL_IN = `!top s:A->bool. closed_in top s ==> borel_in top s`;;

let FSIGMA_IMP_BOREL_IN = `!top s:A->bool. fsigma_in top s ==> borel_in top s`;;

let GDELTA_IMP_BOREL_IN = `!top s:A->bool. gdelta_in top s ==> borel_in top s`;;

let OPEN_IN_SUBTOPOLOGY_BOREL_IN = `!top t s:A->bool.
     open_in (subtopology top t) s /\ borel_in top t ==> borel_in top s`;;

let CLOSED_IN_SUBTOPOLOGY_BOREL_IN = `!top t s:A->bool.
     closed_in (subtopology top t) s /\ borel_in top t ==> borel_in top s`;;

let BOREL_IN_SUBTOPOLOGY = `!top (u:A->bool) s.
        borel_in (subtopology top u) s <=>
        ?t. borel_in top t /\ s = t INTER u`;;

let BOREL_FROM_SUBTOPOLOGY = `!top (u:A->bool) s.
        borel_in (subtopology top u) s /\ borel_in top u ==> borel_in top s`;;

let BOREL_IN_INTER_SUBTOPOLOGY = `!top s t:A->bool.
     borel_in top t ==> borel_in (subtopology top s) (t INTER s)`;;

let BOREL_IN_SUBTOPOLOGY_EQ = `!top u s:A->bool.
        borel_in top u
        ==> (borel_in (subtopology top u) s <=> borel_in top s /\ s SUBSET u)`;;

let BOREL_IN_CONTINUOUS_MAP_PREIMAGE = `!top1 top2 (f:A->B) t.
        continuous_map (top1,top2) f /\ borel_in top2 t
        ==> borel_in top1 {x | x IN topspace top1 /\ f x IN t}`;;

let BOREL_IN_HOMEOMORPHIC_MAP_IMAGE = `!top top' (f:A->B) s.
        homeomorphic_map (top,top') f /\ borel_in top s
        ==> borel_in top' (IMAGE f s)`;;

let BOREL_IN_HOMEOMORPHIC_MAPS_IMAGE_EQ = `!top top' (f:A->B) g s.
        homeomorphic_maps (top,top') (f,g) /\ s SUBSET topspace top
        ==> (borel_in top' (IMAGE f s) <=> borel_in top s)`;;

let BOREL_IN_HOMEOMORPHIC_MAP_IMAGE_EQ = `!top top' (f:A->B) s.
     homeomorphic_map (top,top') f /\ s SUBSET topspace top
     ==> (borel_in top' (IMAGE f s) <=> borel_in top s)`;;

(* ------------------------------------------------------------------------- *)
(* Borel measurable maps.                                                    *)
(* ------------------------------------------------------------------------- *)

let borel_measurable_map = new_definition
 `borel_measurable_map (top1,top2) (f:A->B) <=>
    (!x. x IN topspace top1 ==> f x IN topspace top2) /\
    (!u. borel_in top2 u
         ==> borel_in top1 {x | x IN topspace top1 /\ f x IN u})`;;

let BOREL_MEASURABLE_MAP_OPEN_IN = `!top1 top2 (f:A->B).
        borel_measurable_map (top1,top2) f <=>
        (!x. x IN topspace top1 ==> f x IN topspace top2) /\
        (!c. open_in top2 c
             ==> borel_in top1 {x | x IN topspace top1 /\ f x IN c})`;;

let BOREL_MEASURABLE_MAP_CLOSED_IN = `!top1 top2 (f:A->B).
     borel_measurable_map (top1,top2) f <=>
     (!x. x IN topspace top1 ==> f x IN topspace top2) /\
     (!c. closed_in top2 c
          ==> borel_in top1 {x | x IN topspace top1 /\ f x IN c})`;;

let BOREL_MEASURABLE_MAP_IMAGE_SUBSET_TOPSPACE = `!top1 top2 (f:A->B).
     borel_measurable_map (top1,top2) f
     ==> IMAGE f (topspace top1) SUBSET topspace top2`;;

let CONTINUOUS_IMP_BOREL_MEASURABLE_MAP = `!top1 top2 (f:A->B).
     continuous_map (top1,top2) f ==> borel_measurable_map (top1,top2) f`;;

let BOREL_MEASURABLE_MAP_ID = `!top:A topology. borel_measurable_map (top,top) (\x. x)`;;

let BOREL_MEASURABLE_MAP_CONST = `!top1 top2 (c:B).
     borel_measurable_map (top1,top2) (\x:A. c) <=>
     topspace top1 = {} \/ c IN topspace top2`;;

let BOREL_MEASURABLE_MAP_EQ = `!top1 top2 (f:A->B) g.
        (!x. x IN topspace top1 ==> f x = g x) /\
        borel_measurable_map (top1,top2) f
        ==> borel_measurable_map (top1,top2) g`;;

let BOREL_MEASURABLE_MAP_COMPOSE = `!top1 top2 top3 (f:A->B) (g:B->C).
     borel_measurable_map (top1,top2) f /\ borel_measurable_map (top2,top3) g
     ==> borel_measurable_map (top1,top3) (g o f)`;;

let BOREL_MEASURABLE_MAP_FROM_SUBTOPOLOGY = `!top1 top2 (f:A->B) s.
        borel_measurable_map (top1,top2) f
        ==> borel_measurable_map (subtopology top1 s,top2) f`;;

let BOREL_MEASURABLE_MAP_INTO_SUBTOPOLOGY = `!top1 top2 (f:A->B) s.
     borel_measurable_map (top1,subtopology top2 s) f <=>
     borel_measurable_map (top1,top2) f /\ IMAGE f (topspace top1) SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* Metric spaces.                                                            *)
(* ------------------------------------------------------------------------- *)

let is_metric_space = new_definition
  `is_metric_space (s,d) <=>
   (!x y:A. x IN s /\ y IN s ==> &0 <= d(x,y)) /\
   (!x y. x IN s /\ y IN s ==> (d(x,y) = &0 <=> x = y)) /\
   (!x y. x IN s /\ y IN s ==> d(x,y) = d(y,x)) /\
   (!x y z. x IN s /\ y IN s /\ z IN s ==> d(x,z) <= d(x,y) + d(y,z))`;;

let IS_METRIC_SPACE = `!s d:A#A->real.
        is_metric_space (s,d) <=>
        (!x y. x IN s /\ y IN s ==> (d(x,y) = &0 <=> x = y)) /\
        (!x y z.
              x IN s /\ y IN s /\ z IN s ==> d(x,z) <= d(y,x) + d(y,z))`;;

let metric_tybij =
 (new_type_definition "metric" ("metric","dest_metric") o prove)
 (`?m:(A->bool)#(A#A->real). is_metric_space m`,
  EXISTS_TAC `({}:A->bool,(\p:A#A. &0))` THEN
  REWRITE_TAC[is_metric_space; NOT_IN_EMPTY]);;

let IS_METRIC_SPACE_SUBSPACE = `!(s:A->bool) d. is_metric_space (s,d) ==>
                   (! s'. s' SUBSET s ==> is_metric_space (s',d))`;;

let mspace = new_definition
  `!m:A metric. mspace m = FST (dest_metric m)`;;

let mdist = new_definition
  `!m:A metric. mdist m = SND (dest_metric m)`;;

let METRIC = `!s d. is_metric_space (s:A->bool,d)
         ==> mspace (metric (s,d)) = s /\
             mdist (metric (s,d)) = d`;;

let MSPACE = `!s:A->bool d. is_metric_space (s,d) ==> mspace (metric (s,d)) = s`;;

let MDIST = `!s:A->bool d. is_metric_space (s,d) ==> mdist (metric (s,d)) = d`;;

(* ------------------------------------------------------------------------- *)
(* Distance properties.                                                      *)
(* ------------------------------------------------------------------------- *)

let [MDIST_POS_LE; MDIST_0; MDIST_SYM; MDIST_TRIANGLE] =
  let FORALL_METRIC_THM = prove
   (`!P. (!m. P m) <=>
         (!s:A->bool d. is_metric_space(s,d) ==> P(metric (s,d)))`,
    REWRITE_TAC[GSYM FORALL_PAIR_THM; metric_tybij] THEN
    MESON_TAC[CONJUNCT1 metric_tybij]) in
  let METRIC_AXIOMS =
   (`!m. (!x y:A. x IN mspace m /\ y IN mspace m
                  ==> &0 <= mdist m (x,y)) /\
         (!x y. x IN mspace m /\ y IN mspace m
                ==> (mdist m (x,y) = &0 <=> x = y)) /\
         (!x y. x IN mspace m /\ y IN mspace m
                ==> mdist m (x,y) = mdist m (y,x)) /\
         (!x y z. x IN mspace m /\ y IN mspace m /\ z IN mspace m
                  ==> mdist m (x,z) <= mdist m (x,y) + mdist m (y,z))`,
    SIMP_TAC[FORALL_METRIC_THM; MSPACE; MDIST; is_metric_space]) in
  (CONJUNCTS o REWRITE_RULE [FORALL_AND_THM] o prove) METRIC_AXIOMS;;

let REAL_ABS_MDIST = `!m x y:A. x IN mspace m /\ y IN mspace m
             ==> abs(mdist m (x,y)) = mdist m (x,y)`;;

let MDIST_POS_LT = `!m x y:A. x IN mspace m /\ y IN mspace m /\ ~(x=y)
             ==> &0 < mdist m (x,y)`;;

let MDIST_REFL = `!m x:A. x IN mspace m ==> mdist m (x,x) = &0`;;

let MDIST_POS_EQ = `!m x y:A.
        x IN mspace m /\ y IN mspace m
        ==> (&0 < mdist m (x,y) <=> ~(x = y))`;;

let MDIST_REVERSE_TRIANGLE = `!m x y z:A. x IN mspace m /\ y IN mspace m /\ z IN mspace m
               ==> abs(mdist m (x,y) - mdist m (y,z)) <= mdist m (x,z)`;;

(* ------------------------------------------------------------------------- *)
(* Open ball.                                                                *)
(* ------------------------------------------------------------------------- *)

let mball = new_definition
  `mball m (x:A,r) =
   {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r}`;;

let IN_MBALL = `!m x y:A r.
     y IN mball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r`;;

let CENTRE_IN_MBALL = `!m x:A r. &0 < r /\ x IN mspace m ==> x IN mball m (x,r)`;;

let CENTRE_IN_MBALL_EQ = `!m x:A r. x IN mball m (x,r) <=> x IN mspace m /\ &0 < r`;;

let MBALL_SUBSET_MSPACE = `!m (x:A) r. mball m (x,r) SUBSET mspace m`;;

let MBALL_EMPTY = `!m x:A r. r <= &0 ==> mball m (x,r) = {}`;;

let MBALL_EMPTY_ALT = `!m x:A r. ~(x IN mspace m) ==> mball m (x,r) = {}`;;

let MBALL_EQ_EMPTY = `!m x:A r. mball m (x,r) = {} <=> ~(x IN mspace m) \/ r <= &0`;;

let MBALL_SUBSET = `!m x y:A a b. y IN mspace m /\ mdist m (x,y) + a <= b
                 ==> mball m (x,a) SUBSET mball m (y,b)`;;

let DISJOINT_MBALL = `!m x:A x' r r'. r + r' <= mdist m (x,x')
             ==> DISJOINT (mball m (x,r)) (mball m (x',r'))`;;

let MBALL_SUBSET_CONCENTRIC = `!m (x:A) r1 r2. r1 <= r2 ==> mball m (x,r1) SUBSET mball m (x,r2)`;;

(* ------------------------------------------------------------------------- *)
(* Subspace of a metric space.                                               *)
(* ------------------------------------------------------------------------- *)

let submetric = new_definition
  `submetric (m:A metric) s = metric (s INTER mspace m, mdist m)`;;

let SUBMETRIC = `(!m:A metric s. mspace (submetric m s) = s INTER mspace m) /\
   (!m:A metric s. mdist (submetric m s) = mdist m)`;;

let MBALL_SUBMETRIC_EQ = `!m s a:A r. mball (submetric m s) (a,r) =
               if a IN s then s INTER mball m (a,r) else {}`;;

let MBALL_SUBMETRIC = `!m s x:A r. x IN s ==> mball (submetric m s) (x,r) = mball m (x,r) INTER s`;;

let SUBMETRIC_UNIV = `submetric m (:A) = m`;;

let SUBMETRIC_SUBMETRIC = `!m s t:A->bool.
        submetric (submetric m s) t = submetric m (s INTER t)`;;

let SUBMETRIC_MSPACE = `!m:A metric. submetric m (mspace m) = m`;;

let SUBMETRIC_RESTRICT = `!m s:A->bool. submetric m s = submetric m (mspace m INTER s)`;;

(* ------------------------------------------------------------------------- *)
(* Metric topology                                                           *)
(* ------------------------------------------------------------------------- *)

let mtopology = new_definition
  `mtopology (m:A metric) =
   topology {u | u SUBSET mspace m /\
                 !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}`;;

let IS_TOPOLOGY_METRIC_TOPOLOGY = `istopology {u | u SUBSET mspace m /\
                   !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}`;;

let OPEN_IN_MTOPOLOGY = `!m:A metric u.
     open_in (mtopology m) u <=>
     u SUBSET mspace m /\
     (!x. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u)`;;

let TOPSPACE_MTOPOLOGY = `!m:A metric. topspace (mtopology m) = mspace m`;;

let SUBTOPOLOGY_MSPACE = `!m:A metric. subtopology (mtopology m) (mspace m) = mtopology m`;;

let OPEN_IN_MSPACE = `!m:A metric. open_in (mtopology m) (mspace m)`;;

let CLOSED_IN_MSPACE = `!m:A metric. closed_in (mtopology m) (mspace m)`;;

let OPEN_IN_MBALL = `!m (x:A) r. open_in (mtopology m) (mball m (x,r))`;;

let MTOPOLOGY_SUBMETRIC = `!m:A metric s. mtopology (submetric m s) = subtopology (mtopology m) s`;;

let METRIC_INJECTIVE_IMAGE = `!(f:A->B) m s.
        IMAGE f s SUBSET mspace m /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> (mspace(metric(s,\(x,y). mdist m (f x,f y))) = s) /\
            (mdist(metric(s,\(x,y). mdist m (f x,f y))) =
             \(x,y). mdist m (f x,f y))`;;

let MTOPOLOGY_BASE = `!m:A metric.
      mtopology m =
      topology(ARBITRARY UNION_OF
                 {mball m (x,r) |x,r| x IN mspace m /\ &0 < r})`;;

let CLOSED_IN_METRIC = `!m c:A->bool.
     closed_in (mtopology m) c <=>
     c SUBSET mspace m /\
     (!x. x IN mspace m DIFF c ==> ?r. &0 < r /\ DISJOINT c (mball m (x,r)))`;;

let mcball = new_definition
  `mcball m (x:A,r) =
   {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r}`;;

let IN_MCBALL = `!m (x:A) r y.
     y IN mcball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r`;;

let CENTRE_IN_MCBALL = `!m x:A r. &0 <= r /\ x IN mspace m ==> x IN mcball m (x,r)`;;

let CENTRE_IN_MCBALL_EQ = `!m x:A r. x IN mcball m (x,r) <=> x IN mspace m /\ &0 <= r`;;

let MCBALL_EQ_EMPTY = `!m x:A r. mcball m (x,r) = {} <=> ~(x IN mspace m) \/ r < &0`;;

let MCBALL_EMPTY = `!m (x:A) r. r < &0 ==> mcball m (x,r) = {}`;;

let MCBALL_EMPTY_ALT = `!m (x:A) r. ~(x IN mspace m) ==> mcball m (x,r) = {}`;;

let MCBALL_SUBSET_MSPACE = `!m (x:A) r. mcball m (x,r) SUBSET (mspace m)`;;

let MBALL_SUBSET_MCBALL = `!m x:A r. mball m (x,r) SUBSET mcball m (x,r)`;;

let MCBALL_SUBSET = `!m x y:A a b. y IN mspace m /\ mdist m (x,y) + a <= b
                 ==> mcball m (x,a) SUBSET mcball m (y,b)`;;

let MCBALL_SUBSET_CONCENTRIC = `!m (x:A) a b. a <= b ==> mcball m (x,a) SUBSET mcball m (x,b)`;;

let MCBALL_SUBSET_MBALL = `!m x y:A a b.
     y IN mspace m /\ mdist m (x,y) + a < b
     ==> mcball m (x,a) SUBSET mball m (y,b)`;;

let MCBALL_SUBSET_MBALL_CONCENTRIC = `!m x:A a b. a < b ==> mcball m (x,a) SUBSET mball m (x,b)`;;

let CLOSED_IN_MCBALL = `!m:A metric x r. closed_in (mtopology m) (mcball m (x,r))`;;

let MCBALL_SUBMETRIC_EQ = `!m s a:A r. mcball (submetric m s) (a,r) =
               if a IN s then s INTER mcball m (a,r) else {}`;;

let MCBALL_SUBMETRIC = `!m s x:A r.
     x IN s ==> mcball (submetric m s) (x,r) = mcball m (x,r) INTER s`;;

let msphere = new_definition
  `msphere m (x:A,e) = {y | mdist m (x,y) = e}`;;

let OPEN_IN_MTOPOLOGY_MCBALL = `!m u. open_in (mtopology m) (u:A->bool) <=>
         u SUBSET mspace m /\
         (!x. x IN u ==> (?r. &0 < r /\ mcball m (x,r) SUBSET u))`;;

let METRIC_DERIVED_SET_OF = `!m s.
      mtopology m derived_set_of s =
      {x:A | x IN mspace m /\
            (!r. &0 < r ==> (?y. ~(y = x) /\ y IN s /\ y IN mball m (x,r)))}`;;

let METRIC_CLOSURE_OF = `!m s.
      mtopology m closure_of s =
      {x:A | x IN mspace m /\
            (!r. &0 < r ==> (?y. y IN s /\ y IN mball m (x,r)))}`;;

let METRIC_CLOSURE_OF_ALT = `!m s:A->bool.
      mtopology m closure_of s =
      {x | x IN mspace m /\
           !r. &0 < r ==> ?y. y IN s /\ y IN mcball m (x,r)}`;;

let METRIC_INTERIOR_OF = `!m s:A->bool.
        mtopology m interior_of s =
        {x | x IN mspace m /\ ?e. &0 < e /\ mball m (x,e) SUBSET s}`;;

let METRIC_INTERIOR_OF_ALT = `!m s:A->bool.
        mtopology m interior_of s =
        {x | x IN mspace m /\ ?e. &0 < e /\ mcball m (x,e) SUBSET s}`;;

let IN_INTERIOR_OF_MBALL = `!m s x:A.
        x IN (mtopology m) interior_of s <=>
        x IN mspace m /\
        ?e. &0 < e /\ mball m (x,e) SUBSET s`;;

let IN_INTERIOR_OF_MCBALL = `!m s x:A.
        x IN (mtopology m) interior_of s <=>
        x IN mspace m /\
        ?e. &0 < e /\ mcball m (x,e) SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* Bounded sets.                                                             *)
(* ------------------------------------------------------------------------- *)

let mbounded = new_definition
  `mbounded m s <=> (?c:A b. s SUBSET mcball m (c,b))`;;

let MBOUNDED_POS = `!m s:A->bool.
        mbounded m s <=> ?c b. &0 < b /\ s SUBSET mcball m (c,b)`;;

let MBOUNDED_ALT = `!m s:A->bool.
        mbounded m s <=>
        s SUBSET mspace m /\
        ?b. !x y. x IN s /\ y IN s ==> mdist m (x,y) <= b`;;

let MBOUNDED_ALT_POS = `!m s:A->bool.
        mbounded m s <=>
        s SUBSET mspace m /\
        ?B. &0 < B /\ !x y. x IN s /\ y IN s ==> mdist m (x,y) <= B`;;

let MBOUNDED_SUBSET = `!m s t:A->bool. mbounded m t /\ s SUBSET t ==> mbounded m s`;;

let MBOUNDED_SUBSET_MSPACE = `!m s:A->bool. mbounded m s ==> s SUBSET mspace m`;;

let MBOUNDED = `!m s. mbounded m s <=>
         s = {} \/
         (!x:A. x IN s ==> x IN mspace m) /\
         (?c b. c IN mspace m /\ (!x. x IN s ==> mdist m (c,x) <= b))`;;

let MBOUNDED_EMPTY = `!m:A metric. mbounded m {}`;;

let MBOUNDED_MCBALL = `!m:A metric c b. mbounded m (mcball m (c,b))`;;

let MBOUNDED_MBALL = `!m:A metric c b. mbounded m (mball m (c,b))`;;

let MBOUNDED_INSERT = `!m a:A s. mbounded m (a INSERT s) <=> a IN mspace m /\ mbounded m s`;;

let MBOUNDED_INTER = `!m:A metric s t. mbounded m s /\ mbounded m t ==> mbounded m (s INTER t)`;;

let MBOUNDED_UNION = `!m:A metric s t. mbounded m (s UNION t) <=> mbounded m s /\ mbounded m t`;;

let MBOUNDED_UNIONS = `!m f:(A->bool)->bool.
        FINITE f /\ (!s. s IN f ==> mbounded m s)
        ==> mbounded m (UNIONS f)`;;

let MBOUNDED_CLOSURE_OF = `!m s:A->bool.
      mbounded m s ==> mbounded m (mtopology m closure_of s)`;;

let MBOUNDED_CLOSURE_OF_EQ = `!m s:A->bool.
        s SUBSET mspace m
        ==> (mbounded m (mtopology m closure_of s) <=> mbounded m s)`;;

let MBOUNDED_SUBMETRIC = `!m:A metric s.
     mbounded (submetric m s) t <=> mbounded m (s INTER t) /\ t SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* A decision procedure for metric spaces.                                   *)
(* ------------------------------------------------------------------------- *)

let METRIC_ARITH : term -> thm =
  let SUP_CONV =
    let conv0 = REWR_CONV SUP_INSERT_INSERT
    and conv1 = REWR_CONV SUP_SING in
    conv1 ORELSEC (conv0 THENC REPEATC conv0 THENC TRY_CONV conv1) in
  let MAXDIST_THM = prove
   (`!m s x y:A.
       mbounded m s /\ x IN s /\ y IN s
       ==> mdist m (x,y) =
           sup (IMAGE (\a. abs(mdist m (x,a) - mdist m (a,y))) s)`,
    REPEAT GEN_TAC THEN INTRO_TAC "bnd x y" THEN
    MATCH_MP_TAC (GSYM SUP_UNIQUE) THEN
    CLAIM_TAC "inc" `!p:A. p IN s ==> p IN mspace m` THENL
    [HYP SET_TAC "bnd" [MBOUNDED_SUBSET_MSPACE]; ALL_TAC] THEN
    GEN_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN EQ_TAC THENL
    [INTRO_TAC "le; ![z]; z" THEN
     TRANS_TAC REAL_LE_TRANS `mdist m (x:A,y)` THEN
     ASM_SIMP_TAC[MDIST_REVERSE_TRIANGLE];
     DISCH_THEN (MP_TAC o C MATCH_MP (ASSUME `y:A IN s`)) THEN
     ASM_SIMP_TAC[MDIST_REFL; REAL_SUB_RZERO; REAL_ABS_MDIST]])
  and METRIC_EQ_THM = prove
   (`!m s x y:A.
       s SUBSET mspace m /\ x IN s /\ y IN s
       ==> (x = y <=> (!a. a IN s ==> mdist m (x,a) = mdist m (y,a)))`,
    INTRO_TAC "!m s x y; sub sx sy" THEN EQ_TAC THEN SIMP_TAC[] THEN
    DISCH_THEN (MP_TAC o SPEC `y:A`) THEN
    CLAIM_TAC "x y" `x:A IN mspace m /\ y IN mspace m` THENL
    [ASM SET_TAC []; ASM_SIMP_TAC[MDIST_REFL; MDIST_0]]) in
  let CONJ1_CONV : conv -> conv =
    let TRUE_CONJ_CONV = REWR_CONV (MESON [] `T /\ p <=> p`) in
    fun conv -> LAND_CONV conv THENC TRUE_CONJ_CONV in
  let IN_CONV : conv =
    let DISJ_TRUE_CONV = REWR_CONV (MESON [] `p \/ T <=> T`)
    and TRUE_DISJ_CONV = REWR_CONV (MESON [] `T \/ p <=> T`) in
    let REFL_CONV = REWR_CONV (MESON [] `x:A = x <=> T`) in
    let conv0 = REWR_CONV (EQF_INTRO (SPEC_ALL NOT_IN_EMPTY)) in
    let conv1 = REWR_CONV IN_INSERT in
    let conv2 = LAND_CONV REFL_CONV THENC TRUE_DISJ_CONV in
    let rec IN_CONV tm =
      (conv0 ORELSEC
       (conv1 THENC
        (conv2 ORELSEC
         (RAND_CONV IN_CONV THENC DISJ_TRUE_CONV)))) tm in
    IN_CONV
  and IMAGE_CONV : conv =
    let pth0,pth1 = CONJ_PAIR IMAGE_CLAUSES in
    let conv0 = REWR_CONV pth0
    and conv1 = REWR_CONV pth1 THENC TRY_CONV (LAND_CONV BETA_CONV) in
    let rec IMAGE_CONV tm =
      (conv0 ORELSEC (conv1 THENC RAND_CONV IMAGE_CONV)) tm in
    IMAGE_CONV in
  let SUBSET_CONV : conv -> conv =
    let conv0 = REWR_CONV (EQT_INTRO (SPEC_ALL EMPTY_SUBSET)) in
    let conv1 = REWR_CONV INSERT_SUBSET in
    fun conv ->
      let conv2 = conv1 THENC CONJ1_CONV conv in
      REPEATC conv2 THENC conv0 in
  let rec prove_hyps th =
    match hyp th with
    | [] -> th
    | htm :: _ ->
        let emth = SPEC htm EXCLUDED_MIDDLE in
        let nhp = EQF_INTRO (ASSUME (mk_neg htm)) in
        let nth1 = (SUBS_CONV [nhp] THENC PRESIMP_CONV) (concl th) in
        let nth2 = MESON [nhp] (rand (concl nth1)) in
        let nth = EQ_MP (SYM nth1) nth2 in
        prove_hyps(DISJ_CASES emth th nth) in
  let rec guess_metric tm =
    match tm with
    | Comb(Const("mdist",_),m) -> m
    | Comb(Const("mspace",_),m) -> m
    | Comb(s,t) -> (try guess_metric s with Failure _ -> guess_metric t)
    | Abs(_, bd) -> guess_metric bd
    | _ -> failwith "metric not found" in
  let find_mdist mtm =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("mdist",_),pmtm),p) when pmtm = mtm -> [tm]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find
  and find_eq mty =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("=",ty),_),_) when fst(dest_fun_ty ty) = mty -> [tm]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find
  and find_points mtm =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("mdist",_),pmtm),p) when pmtm = mtm ->
          let x,y = dest_pair p in
          if x = y then [x] else [x;y]
      | Comb(Comb(Const("IN",_),x),Comb(Const("mspace",_),pmtm))
          when pmtm = mtm -> [x]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find in
  let prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PURE_REWRITE_CONV[FORALL_SIMP; EXISTS_SIMP] THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV `(/\)` CONDS_CELIM_CONV THENC
    PRESIMP_CONV THENC
    GEN_REWRITE_CONV REDEPTH_CONV
      [AND_FORALL_THM; LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM;
       LEFT_OR_FORALL_THM; RIGHT_OR_FORALL_THM] THENC
    PRENEX_CONV
  and real_poly_conv =
    let eths = REAL_ARITH
      `(x = y <=> x - y = &0) /\
       (x < y <=> y - x > &0) /\
       (x > y <=> x - y > &0) /\
       (x <= y <=> y - x >= &0) /\
       (x >= y <=> x - y >= &0)` in
    GEN_REWRITE_CONV I [eths] THENC LAND_CONV REAL_POLY_CONV
  and augment_mdist_pos_thm =
    MESON [] `p ==> (q <=> r) ==> (q <=> (p ==> r))` in
  fun tm ->
    let mtm = guess_metric tm in
    let mty = hd(snd(dest_type(type_of mtm))) in
    let mspace_tm = mk_icomb(mk_const("mspace",[]),mtm) in
    let metric_eq_thm = ISPEC mtm METRIC_EQ_THM
    and mk_in_mspace_th =
      let in_tm = mk_const("IN",[mty,aty]) in
      fun pt -> ASSUME (mk_comb(mk_comb(in_tm,pt),mspace_tm)) in
    let th0 = prenex_conv tm in
    let tm0 = rand (concl th0) in
    let avs,bod = strip_forall tm0 in
    let points = find_points mtm bod in
    let in_mspace_conv = GEN_REWRITE_CONV I (map mk_in_mspace_th points) in
    let in_mspace2_conv = CONJ1_CONV in_mspace_conv THENC in_mspace_conv in
    let MDIST_REFL_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm MDIST_REFL) in
      fun tm -> MP_CONV in_mspace_conv (pconv tm)
    and MDIST_SYM_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm MDIST_SYM) in
      fun tm -> let x,y = dest_pair (rand tm) in
                if x <= y then failwith "MDIST_SYM_CONV" else
                MP_CONV in_mspace2_conv (pconv tm)
    and MBOUNDED_CONV =
      let conv0 = REWR_CONV (EQT_INTRO (ISPEC mtm MBOUNDED_EMPTY)) in
      let conv1 = REWR_CONV (ISPEC mtm MBOUNDED_INSERT) in
      let rec mbounded_conv tm =
        try conv0 tm with Failure _ ->
        (conv1 THENC CONJ1_CONV in_mspace_conv THENC mbounded_conv) tm in
      mbounded_conv in
    let REFL_SYM_CONV = MDIST_REFL_CONV ORELSEC MDIST_SYM_CONV in
    let ABS_MDIST_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm REAL_ABS_MDIST) in
      fun tm -> MP_CONV in_mspace2_conv (pconv tm) in
    let metric_eq_prerule =
      (CONV_RULE o BINDER_CONV o BINDER_CONV)
      (LAND_CONV (CONJ1_CONV (SUBSET_CONV in_mspace_conv)) THENC
       RAND_CONV (REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY])) in
    let MAXDIST_CONV =
      let maxdist_thm = ISPEC mtm MAXDIST_THM
      and ante_conv =
        CONJ1_CONV MBOUNDED_CONV THENC CONJ1_CONV IN_CONV THENC IN_CONV
      and image_conv =
        IMAGE_CONV THENC ONCE_DEPTH_CONV REFL_SYM_CONV THENC
        PURE_REWRITE_CONV
          [REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_SUB_REFL;
           REAL_ABS_0; REAL_ABS_NEG; REAL_ABS_SUB; INSERT_AC] THENC
        ONCE_DEPTH_CONV ABS_MDIST_CONV THENC
        PURE_REWRITE_CONV[INSERT_AC] in
      let sup_conv = RAND_CONV image_conv THENC SUP_CONV in
      fun fset_tm ->
        let maxdist_th = SPEC fset_tm maxdist_thm in
        fun tm ->
          let th0 = MP_CONV ante_conv (IMP_REWR_CONV maxdist_th tm) in
          let tm0 = rand (concl th0) in
          let th1 = sup_conv tm0 in
          TRANS th0 th1 in
    let AUGMENT_MDISTS_POS_RULE =
      let mdist_pos_le = ISPEC mtm MDIST_POS_LE in
      let augment_rule : term -> thm -> thm =
        let mk_mdist_pos_thm tm =
          let xtm,ytm = dest_pair (rand tm) in
          let pth = SPECL[xtm;ytm] mdist_pos_le in
          MP_CONV (CONJ1_CONV in_mspace_conv THENC in_mspace_conv) pth in
        fun mdist_tm ->
          let ith =
            MATCH_MP augment_mdist_pos_thm (mk_mdist_pos_thm mdist_tm) in
          fun th -> MATCH_MP ith th in
      fun th ->
        let mdist_thl = find_mdist mtm (concl th) in
        itlist augment_rule mdist_thl th in
    let BASIC_METRIC_ARITH (tm : term) : thm =
      let mdist_tms = find_mdist mtm tm in
      let th0 =
        let eqs =
          mapfilter (MDIST_REFL_CONV ORELSEC MDIST_SYM_CONV) mdist_tms in
        (ONCE_DEPTH_CONV in_mspace_conv THENC PRESIMP_CONV THENC
         SUBS_CONV eqs THENC REAL_RAT_REDUCE_CONV THENC
         ONCE_DEPTH_CONV real_poly_conv) tm in
      let tm0 = rand (concl th0) in
      let points = find_points mtm tm0 in
      let fset_tm = mk_setenum(points,mty) in
      let METRIC_EQ_CONV =
        let th = metric_eq_prerule (SPEC fset_tm metric_eq_thm) in
        fun tm ->
          let xtm,ytm = dest_eq tm in
          let th0 = SPECL[xtm;ytm] th in
          let th1 = MP_CONV (CONJ1_CONV IN_CONV THENC IN_CONV) th0 in
          let tm1 = rand (concl th1) in
          let th2 = ONCE_DEPTH_CONV REFL_SYM_CONV tm1 in
          TRANS th1 th2 in
      let eq1 = map (MAXDIST_CONV fset_tm) (find_mdist mtm tm0)
      and eq2 = map METRIC_EQ_CONV (find_eq mty tm0) in
      let th1 = AUGMENT_MDISTS_POS_RULE (SUBS_CONV (eq1 @ eq2) tm0) in
      let tm1 = rand (concl th1) in
      prove_hyps (EQ_MP (SYM th0) (EQ_MP (SYM th1) (REAL_ARITH tm1))) in
    let SIMPLE_METRIC_ARITH tm =
      let th0 = (WEAK_CNF_CONV THENC CONJ_CANON_CONV) tm in
      let tml =
        try conjuncts (rand (concl th0))
        with Failure s -> failwith("conjuncts "^s) in
      let th1 =
        try end_itlist CONJ (map BASIC_METRIC_ARITH tml)
        with Failure s -> failwith("end_itlist "^s) in
      EQ_MP (SYM th0) th1 in
    let elim_exists tm =
      let points = find_points mtm tm in
      let rec try_points v tm ptl =
        if ptl = [] then fail () else
        let xtm = hd ptl in
        try EXISTS (mk_exists(v,tm),xtm) (elim_exists (vsubst [xtm,v] tm))
        with Failure _ -> try_points v tm (tl ptl)
      and elim_exists tm =
        try let v,bd = dest_exists tm in
            try_points v bd points
        with Failure _ -> SIMPLE_METRIC_ARITH tm in
      elim_exists tm in
    EQ_MP (SYM th0) (GENL avs (elim_exists bod));;

let METRIC_ARITH_TAC = CONV_TAC METRIC_ARITH;;

let ASM_METRIC_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  METRIC_ARITH_TAC;;

let COMPACT_IN_IMP_MBOUNDED = `!m s:A->bool. compact_in (mtopology m) s ==> mbounded m s`;;

let HAUSDORFF_SPACE_MTOPOLOGY = `!m:A metric. hausdorff_space(mtopology m)`;;

let T1_SPACE_MTOPOLOGY = `!m:A metric. t1_space(mtopology m)`;;

(* ------------------------------------------------------------------------- *)
(* The discrete metric.                                                      *)
(* ------------------------------------------------------------------------- *)

let discrete_metric = new_definition
  `discrete_metric s = metric(s,(\(x,y). if x = y then &0 else &1))`;;

let DISCRETE_METRIC = `(!s:A->bool. mspace(discrete_metric s) = s) /\
   (!s x y:A. mdist (discrete_metric s) (x,y) = if x = y then &0 else &1)`;;

let MTOPOLOGY_DISCRETE_METRIC = `!s:A->bool. mtopology(discrete_metric s) = discrete_topology s`;;

let DISCRETE_ULTRAMETRIC = `!s x y z:A.
        mdist(discrete_metric s) (x,z) <=
        max (mdist(discrete_metric s) (x,y))
            (mdist(discrete_metric s) (y,z))`;;

let MBOUNDED_DISCRETE_METRIC = `!u s:A->bool. mbounded (discrete_metric u) s <=> s SUBSET u`;;

(* ------------------------------------------------------------------------- *)
(* Metrizable spaces.                                                        *)
(* ------------------------------------------------------------------------- *)

let metrizable_space = new_definition
 `metrizable_space top <=> ?m. top = mtopology m`;;

let METRIZABLE_SPACE_MTOPOLOGY = `!m. metrizable_space (mtopology m)`;;

let FORALL_METRIC_TOPOLOGY = `!P. (!m:A metric. P (mtopology m) (mspace m)) <=>
       !top. metrizable_space top ==> P top (topspace top)`;;

let FORALL_METRIZABLE_SPACE = `!P. (!top. metrizable_space top ==> P top (topspace top)) <=>
       (!m:A metric. P (mtopology m) (mspace m))`;;

let EXISTS_METRIZABLE_SPACE = `!P. (?top. metrizable_space top /\ P top (topspace top)) <=>
       (?m:A metric. P (mtopology m) (mspace m))`;;

let METRIZABLE_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. metrizable_space(discrete_topology u)`;;

let METRIZABLE_SPACE_SUBTOPOLOGY = `!top s:A->bool.
    metrizable_space top ==> metrizable_space(subtopology top s)`;;

let HOMEOMORPHIC_METRIZABLE_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (metrizable_space top <=> metrizable_space top')`;;

let METRIZABLE_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ metrizable_space top
        ==> metrizable_space top'`;;

let METRIZABLE_IMP_HAUSDORFF_SPACE = `!top. metrizable_space top ==> hausdorff_space top`;;

let METRIZABLE_IMP_KC_SPACE = `!top:A topology. metrizable_space top ==> kc_space top`;;

let KC_SPACE_MTOPOLOGY = `!m:A metric. kc_space(mtopology m)`;;

let METRIZABLE_IMP_T1_SPACE = `!top. metrizable_space top ==> t1_space top`;;

let CLOSED_IMP_GDELTA_IN = `!top s:A->bool.
        metrizable_space top /\ closed_in top s ==> gdelta_in top s`;;

let OPEN_IMP_FSIGMA_IN = `!top s:A->bool.
        metrizable_space top /\ open_in top s ==> fsigma_in top s`;;

let FIRST_COUNTABLE_MTOPOLOGY = `!m:A metric. first_countable(mtopology m)`;;

let METRIZABLE_IMP_FIRST_COUNTABLE = `!top:A topology. metrizable_space top ==> first_countable top`;;

(* ------------------------------------------------------------------------- *)
(* Separable metrizable spaces are second-countable. Additional              *)
(* second-countability results including closed map images.                  *)
(* ------------------------------------------------------------------------- *)

let SEPARABLE_METRIZABLE_IMP_SECOND_COUNTABLE = `!top:A topology.
        separable_space top /\ metrizable_space top ==> second_countable top`;;

let SECOND_COUNTABLE_CLOSED_MAP_IMAGE = `!(f:B->C) top top'.
        continuous_map(top,top') f /\
        closed_map(top,top') f /\
        compact_space top /\
        hausdorff_space top' /\
        IMAGE f (topspace top) = topspace top' /\
        second_countable top
        ==> second_countable top'`;;

(* ------------------------------------------------------------------------- *)
(* Connected topological spaces.                                             *)
(* ------------------------------------------------------------------------- *)

let connected_space = new_definition
  `connected_space(top:A topology) <=>
        ~(?e1 e2. open_in top e1 /\ open_in top e2 /\
                  topspace top SUBSET e1 UNION e2 /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`;;

let connected_in = new_definition
 `connected_in top s <=>
  s SUBSET topspace top /\ connected_space (subtopology top s)`;;

let CONNECTED_IN_SUBSET_TOPSPACE = `!top s:A->bool. connected_in top s ==> s SUBSET topspace top`;;

let CONNECTED_IN_TOPSPACE = `!top:A topology. connected_in top (topspace top) <=> connected_space top`;;

let CONNECTED_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        connected_in top s ==> connected_space (subtopology top s)`;;

let CONNECTED_IN_SUBTOPOLOGY = `!top s t:A->bool.
      connected_in (subtopology top s) t <=> connected_in top t /\ t SUBSET s`;;

let CONNECTED_SPACE_EQ = `!top:A topology.
        connected_space(top:A topology) <=>
        ~(?e1 e2. open_in top e1 /\ open_in top e2 /\
                  e1 UNION e2 = topspace top /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`;;

let CONNECTED_SPACE_CLOSED_IN = `!top:A topology.
        connected_space(top:A topology) <=>
        ~(?e1 e2. closed_in top e1 /\ closed_in top e2 /\
                  topspace top SUBSET e1 UNION e2 /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`;;

let CONNECTED_SPACE_CLOSED_IN_EQ = `!top:A topology.
        connected_space(top:A topology) <=>
        ~(?e1 e2. closed_in top e1 /\ closed_in top e2 /\
                  e1 UNION e2 = topspace top /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`;;

let CONNECTED_SPACE_CLOPEN_IN = `!top:A topology.
        connected_space top <=>
        !t. open_in top t /\ closed_in top t ==> t = {} \/ t = topspace top`;;

let CONNECTED_SPACE_EQ_FRONTIER_EQ_EMPTY = `!top:A topology.
        connected_space top <=>
        !s. s SUBSET topspace top /\ top frontier_of s = {}
            ==> s = {} \/ s = topspace top`;;

let CONNECTED_SPACE_FRONTIER_EQ_EMPTY = `!top s:A->bool.
        connected_space top /\ s SUBSET topspace top
        ==> (top frontier_of s = {} <=> s = {} \/ s = topspace top)`;;

let CONNECTED_IN = `!top s:A->bool.
        connected_in top s <=>
        s SUBSET topspace top /\
        ~(?e1 e2. open_in top e1 /\ open_in top e2 /\
                  s SUBSET (e1 UNION e2) /\
                  (e1 INTER e2 INTER s = {}) /\
                  ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

let CONNECTED_IN_CLOSED_IN = `!top s:A->bool.
        connected_in top s <=>
        s SUBSET topspace top /\
        ~(?e1 e2. closed_in top e1 /\ closed_in top e2 /\
                  s SUBSET (e1 UNION e2) /\
                  (e1 INTER e2 INTER s = {}) /\
                  ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

let CONNECTED_IN_EMPTY = `!top:A topology. connected_in top {}`;;

let CONNECTED_SPACE_TOPSPACE_EMPTY = `!top:A topology. topspace top = {} ==> connected_space top`;;

let CONNECTED_IN_SING = `!top a:A. connected_in top {a} <=> a IN topspace top`;;

let CONNECTED_IN_ABSOLUTE = `!top s:A->bool. connected_in (subtopology top s) s <=> connected_in top s`;;

let CONNECTED_IN_UNIONS = `!top u:(A->bool)->bool.
        (!s. s IN u ==> connected_in top s) /\ ~(INTERS u = {})
        ==> connected_in top (UNIONS u)`;;

let CONNECTED_IN_UNION = `!top s t:A->bool.
        connected_in top s /\ connected_in top t /\ ~(s INTER t = {})
        ==> connected_in top (s UNION t)`;;

let CONNECTED_SPACE_SUBCONNECTED = `!top:A topology.
        connected_space top <=>
        !x y. x IN topspace top /\ y IN topspace top
              ==> ?s. connected_in top s /\ x IN s /\ y IN s`;;

let CONNECTED_IN_INTERMEDIATE_CLOSURE_OF = `!top s t:A->bool.
        connected_in top s /\ s SUBSET t /\ t SUBSET top closure_of s
        ==> connected_in top t`;;

let CONNECTED_IN_CLOSURE_OF = `!top s:A->bool. connected_in top s ==> connected_in top (top closure_of s)`;;

let CONNECTED_IN_SEPARATION = `(!top s:A->bool.
        connected_in top s <=>
        s SUBSET topspace top /\
        ~(?c1 c2. c1 UNION c2 = s /\ ~(c1 = {}) /\ ~(c2 = {}) /\
                  c1 INTER top closure_of c2 = {} /\
                  c2 INTER top closure_of c1 = {}))`
and CONNECTED_IN_SEPARATION_ALT = `(!top s:A->bool.
        connected_in top s <=>
        s SUBSET topspace top /\
        ~(?c1 c2.
            s SUBSET c1 UNION c2 /\ ~(c1 INTER s = {}) /\ ~(c2 INTER s = {}) /\
            c1 INTER top closure_of c2 = {} /\
            c2 INTER top closure_of c1 = {}))`;;

let CONNECTED_IN_EQ_NOT_SEPARATED = `!top s:A->bool.
         connected_in top s <=>
         s SUBSET topspace top /\
         ~(?c1 c2. c1 UNION c2 = s /\ ~(c1 = {}) /\ ~(c2 = {}) /\
                   separated_in top c1 c2)`;;

let CONNECTED_IN_EQ_NOT_SEPARATED_SUBSET = `!top s:A->bool.
         connected_in top s <=>
         s SUBSET topspace top /\
         ~(?c1 c2. s SUBSET c1 UNION c2 /\
                   ~(s INTER c1 = {}) /\ ~(s INTER c2 = {}) /\
                   separated_in top c1 c2)`;;

let CONNECTED_SPACE_EQ_NOT_SEPARATED = `!top:A topology.
        connected_space top <=>
        ~(?c1 c2. c1 UNION c2 = topspace top /\ ~(c1 = {}) /\ ~(c2 = {}) /\
                  separated_in top c1 c2)`;;

let CONNECTED_SPACE_EQ_NOT_SEPARATED_SUBSET = `!top:A topology.
      connected_space top <=>
      ~(?c1 c2. topspace top SUBSET c1 UNION c2 /\ ~(c1 = {}) /\ ~(c2 = {}) /\
                separated_in top c1 c2)`;;

let CONNECTED_IN_SUBSET_SEPARATED_UNION = `!top s t c:A->bool.
        connected_in top c /\ separated_in top s t /\ c SUBSET s UNION t
        ==> c SUBSET s \/ c SUBSET t`;;

let CONNECTED_IN_NONSEPARATED_UNION = `!top s t:A->bool.
        connected_in top s /\ connected_in top t /\ ~separated_in top s t
        ==> connected_in top (s UNION t)`;;

let CONNECTED_IN_UNIONS_STRONG = `!(top:A topology) f:(A->bool)->bool.
        (!s. s IN f ==> connected_in top s) /\
        ~(UNIONS f INTER INTERS {top closure_of s | s IN f} = {})
        ==> connected_in top (UNIONS f)`;;

(* ------------------------------------------------------------------------- *)
(* Connectedness of the intersection of a chain of compact connected sets.   *)
(* This is the general topology version of CONNECTED_CHAIN from topology.ml. *)
(* Hausdorff is needed to separate disjoint compact sets.                    *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_IN_CHAIN = `!top (f:(A->bool)->bool).
        hausdorff_space top /\
        ~(f = {}) /\
        (!s. s IN f ==> compact_in top s /\ connected_in top s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> connected_in top (INTERS f)`;;

let CONNECTED_IN_CHAIN_GEN = `!top (f:(A->bool)->bool).
        hausdorff_space top /\
        (!s. s IN f ==> closed_in top s /\ connected_in top s) /\
        (?s. s IN f /\ compact_in top s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> connected_in top (INTERS f)`;;

let CONNECTED_IN_NEST = `!top (s:num->A->bool).
        hausdorff_space top /\
        (!n. compact_in top (s n) /\ connected_in top (s n)) /\
        (!m n. m <= n ==> s n SUBSET s m)
        ==> connected_in top (INTERS {s n | n IN (:num)})`;;

let CONNECTED_IN_NEST_GEN = `!top (s:num->A->bool).
        hausdorff_space top /\
        (!n. closed_in top (s n) /\ connected_in top (s n)) /\
        (?n. compact_in top (s n)) /\
        (!m n. m <= n ==> s n SUBSET s m)
        ==> connected_in top (INTERS {s n | n IN (:num)})`;;

let CONNECTED_IN_EQ_SUBSET_SEPARATED_UNION = `!top c:A->bool.
        connected_in top c <=>
        c SUBSET topspace top /\
        !s t. separated_in top s t /\ c SUBSET s UNION t
              ==> c SUBSET s \/ c SUBSET t`;;

let CONNECTED_IN_CLOPEN_CASES = `!top c t:A->bool.
        connected_in top c /\ closed_in top t /\ open_in top t
        ==> c SUBSET t \/ DISJOINT c t`;;

let CONNECTED_SPACE_CLOSURES = `!top:A topology.
        connected_space top <=>
        ~(?e1 e2. e1 UNION e2 = topspace top /\
                  top closure_of e1 INTER top closure_of e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`;;

let CONNECTED_IN_INTER_FRONTIER_OF = `!top s t:A->bool.
        connected_in top s /\ ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER top frontier_of t = {})`;;

let CONNECTED_IN_CONTINUOUS_MAP_IMAGE = `!f:A->B top top' s.
        continuous_map (top,top') f /\ connected_in top s
        ==> connected_in top' (IMAGE f s)`;;

let HOMEOMORPHIC_CONNECTED_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (connected_space top <=> connected_space top')`;;

let HOMEOMORPHIC_MAP_CONNECTEDNESS = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f /\ u SUBSET topspace top
        ==> (connected_in top' (IMAGE f u) <=> connected_in top u)`;;

let HOMEOMORPHIC_MAP_CONNECTEDNESS_EQ = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f
        ==> (connected_in top u <=>
             u SUBSET topspace top /\ connected_in top' (IMAGE f u))`;;

let CONNECTED_SPACE_QUOTIENT_MAP_IMAGE = `!top top' (q:A->B).
        quotient_map(top,top') q /\ connected_space top
        ==> connected_space top'`;;

let CONNECTED_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ connected_space top
        ==> connected_space top'`;;

let CONNECTED_IN_DISCRETE_TOPOLOGY = `!u s:A->bool.
       connected_in (discrete_topology u) s <=>
       s SUBSET u /\ ?a. s SUBSET {a}`;;

let CONNECTED_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool.
        connected_space (discrete_topology u) <=>
        ?a. u SUBSET {a}`;;

let CONNECTED_IN_IMP_PERFECT_GEN = `!top s:A->bool.
        t1_space top /\ connected_in top s /\ ~(?a. s = {a})
        ==> s SUBSET top derived_set_of s`;;

let CONNECTED_IN_IMP_PERFECT = `!top s:A->bool.
        hausdorff_space top /\ connected_in top s /\ ~(?a. s = {a})
        ==> s SUBSET top derived_set_of s`;;

let CARD_LE_PAIRWISE_SEPARATED_CONNECTED_IN = `!(top:A topology) u v.
        FINITE u /\
        pairwise (separated_in top) u /\
        (!c. c IN u ==> ~(c = {})) /\
        (!c. c IN v ==> connected_in top c) /\
        UNIONS u = UNIONS v
        ==> u <=_c v`;;

let CONNECTED_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        connected_space(prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        connected_space top1 /\ connected_space top2`;;

let CONNECTED_IN_CROSS = `!top1 top2 s:A->bool t:B->bool.
        connected_in (prod_topology top1 top2) (s CROSS t) <=>
        s = {} \/ t = {} \/ connected_in top1 s /\ connected_in top2 t`;;

let CONNECTED_SPACE_PRODUCT_TOPOLOGY = `!tops:K->A topology k.
        connected_space(product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        !i. i IN k ==> connected_space(tops i)`;;

let CONNECTED_IN_CARTESIAN_PRODUCT = `!tops:K->A topology s k.
        connected_in (product_topology k tops) (cartesian_product k s) <=>
        cartesian_product k s = {} \/
        !i. i IN k ==> connected_in (tops i) (s i)`;;

(* ------------------------------------------------------------------------- *)
(* The notion of "separated between" (complement of "connected between")     *)
(* ------------------------------------------------------------------------- *)

let separated_between = new_definition
 `separated_between top (s:A->bool) t <=>
        ?u v. open_in top u /\ open_in top v /\
              u UNION v = topspace top /\ DISJOINT u v /\
              s SUBSET u /\ t SUBSET v`;;

let SEPARATED_BETWEEN_ALT = `!top s (t:A->bool).
        separated_between top s t <=>
        ?u v. closed_in top u /\ closed_in top v /\
              u UNION v = topspace top /\ DISJOINT u v /\
              s SUBSET u /\ t SUBSET v`;;

let SEPARATED_BETWEEN = `!top s (t:A->bool).
        separated_between top s t <=>
        ?u. closed_in top u /\ open_in top u /\
            s SUBSET u /\ t SUBSET (topspace top DIFF u)`;;

let SEPARATED_BETWEEN_MONO = `!top s t s' t':A->bool.
        separated_between top s t /\ s' SUBSET s /\ t' SUBSET t
        ==> separated_between top s' t'`;;

let SEPARATED_BETWEEN_REFL = `!top s:A->bool. separated_between top s s <=> s = {}`;;

let SEPARATED_BETWEEN_SYM = `!top s (t:A->bool).
        separated_between top s t <=> separated_between top t s`;;

let SEPARATED_BETWEEN_IMP_SUBSET = `!top s (t:A->bool).
        separated_between top s t
        ==> s SUBSET topspace top /\ t SUBSET topspace top`;;

let SEPARATED_BETWEEN_EMPTY = `(!top s:A->bool. separated_between top {} s <=> s SUBSET topspace top) /\
   (!top s:A->bool. separated_between top s {} <=> s SUBSET topspace top)`;;

let SEPARATED_BETWEEN_UNION = `(!top s t u:A->bool.
        separated_between top s (t UNION u) <=>
        separated_between top s t /\
        separated_between top s u) /\
   (!top s t u:A->bool.
        separated_between top (s UNION t) u <=>
        separated_between top s u /\
        separated_between top t u)`;;

let SEPARATED_BETWEEN_IMP_DISJOINT = `!top s (t:A->bool). separated_between top s t ==> DISJOINT s t`;;

let SEPARATED_BETWEEN_IMP_SEPARATED_IN = `!top s (t:A->bool). separated_between top s t ==> separated_in top s t`;;

let SEPARATED_BETWEEN_FULL = `!top s t:A->bool.
        s UNION t = topspace top
        ==> (separated_between top s t <=>
             DISJOINT s t /\
             closed_in top s /\ open_in top s /\
             closed_in top t /\ open_in top t)`;;

let SEPARATED_BETWEEN_EQ_SEPARATED_IN = `!top s t:A->bool.
        s UNION t = topspace top
        ==> (separated_between top s t <=> separated_in top s t)`;;

let SEPARATED_BETWEEN_POINTWISE_LEFT = `!top s t:A->bool.
        compact_in top s
        ==> (separated_between top s t <=>
             (s = {} ==> t SUBSET topspace top) /\
             !x. x IN s ==> separated_between top {x} t)`;;

let SEPARATED_BETWEEN_POINTWISE_RIGHT = `!top s t:A->bool.
        compact_in top t
        ==> (separated_between top s t <=>
             (t = {} ==> s SUBSET topspace top) /\
             !y. y IN t ==> separated_between top s {y})`;;

let SEPARATED_BETWEEN_CLOSURE_OF = `(!top s t:A->bool.
        s SUBSET topspace top
        ==> (separated_between top (top closure_of s) t <=>
             separated_between top s t)) /\
   (!top s t:A->bool.
        t SUBSET topspace top
        ==> (separated_between top s (top closure_of t) <=>
             separated_between top s t))`;;

let SEPARATED_BETWEEN_CLOSURE_OF_EQ = `(!top s t:A->bool.
        separated_between top s t <=>
        s SUBSET topspace top /\
        separated_between top (top closure_of s) t) /\
   (!top s t:A->bool.
        separated_between top s t <=>
        t SUBSET topspace top /\
        separated_between top s (top closure_of t))`;;

let SEPARATED_BETWEEN_FRONTIER_OF_EQ = `(!top s t:A->bool.
        separated_between top s t <=>
        s SUBSET topspace top /\ DISJOINT s t /\
        separated_between top (top frontier_of s) t) /\
   (!top s t:A->bool.
        separated_between top s t <=>
        t SUBSET topspace top /\ DISJOINT s t /\
        separated_between top s (top frontier_of t))`;;

let SEPARATED_BETWEEN_FRONTIER_OF = `(!top s t:A->bool.
        s SUBSET topspace top /\ DISJOINT s t
        ==> (separated_between top (top frontier_of s) t <=>
             separated_between top s t)) /\
   (!top s t:A->bool.
        t SUBSET topspace top /\ DISJOINT s t
        ==> (separated_between top s (top frontier_of t) <=>
             separated_between top s t))`;;

let CONNECTED_SPACE_SEPARATED_BETWEEN = `!top:A topology.
        connected_space top <=>
        !s t. separated_between top s t ==> s = {} \/ t = {}`;;

let CONNECTED_SPACE_IMP_SEPARATED_BETWEEN_TRIVIAL = `!top s t:A->bool.
        connected_space top
        ==> (separated_between top s t <=>
             s = {} /\ t SUBSET topspace top \/
             s SUBSET topspace top /\ t = {})`;;

(* ------------------------------------------------------------------------- *)
(* Connected components.                                                     *)
(* ------------------------------------------------------------------------- *)

let connected_component_of = new_definition
 `connected_component_of top x y <=>
        ?t. connected_in top t /\ x IN t /\ y IN t`;;

let connected_components_of = new_definition
 `connected_components_of top =
    {connected_component_of top x |x| x IN topspace top}`;;

let CONNECTED_COMPONENT_IN_TOPSPACE = `!top x y:A.
        connected_component_of top x y
        ==> x IN topspace top /\ y IN topspace top`;;

let CONNECTED_COMPONENT_OF_REFL = `!top x:A. connected_component_of top x x <=> x IN topspace top`;;

let CONNECTED_COMPONENT_OF_SYM = `!top x y:A.
    connected_component_of top x y <=> connected_component_of top y x`;;

let CONNECTED_COMPONENT_OF_TRANS = `!top x y z:A.
        connected_component_of top x y /\ connected_component_of top y z
        ==> connected_component_of top x z`;;

let CONNECTED_COMPONENT_OF_SUBTOPOLOGY = `!top s x y:A.
        connected_component_of (subtopology top s) x y
        ==> connected_component_of top x y`;;

let CONNECTED_COMPONENT_OF_MONO = `!top s t x y:A.
        connected_component_of (subtopology top s) x y /\ s SUBSET t
        ==> connected_component_of (subtopology top t) x y`;;

let CONNECTED_COMPONENT_OF_SET = `!top x:A.
        connected_component_of top x =
        {y | ?t. connected_in top t /\ x IN t /\ y IN t}`;;

let CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE = `!top x. (connected_component_of top x) SUBSET topspace top`;;

let CONNECTED_COMPONENT_OF_SUBTOPOLOGY_EQ = `!top u x:A.
      connected_component_of (subtopology top u) x =
      connected_component_of top x <=>
      connected_component_of top x SUBSET u`;;

let CONNECTED_COMPONENTS_OF_SUBTOPOLOGY = `!top u c:A->bool.
        c IN connected_components_of top /\ c SUBSET u
        ==> c IN connected_components_of (subtopology top u)`;;

let CONNECTED_COMPONENT_OF_EQ_EMPTY = `!top x. connected_component_of top x = {} <=> ~(x IN topspace top)`;;

let CONNECTED_SPACE_IFF_CONNECTED_COMPONENT = `!top:A topology.
        connected_space top <=>
        !x y. x IN topspace top /\ y IN topspace top
              ==> connected_component_of top x y`;;

let CONNECTED_SPACE_IMP_CONNECTED_COMPONENT_OF = `!top a b:A.
        connected_space top /\ a IN topspace top /\ b IN topspace top
        ==> connected_component_of top a b`;;

let CONNECTED_SPACE_CONNECTED_COMPONENT_SET = `!top. connected_space top <=>
         !x:A. x IN topspace top
               ==> connected_component_of top x = topspace top`;;

let CONNECTED_COMPONENT_OF_MAXIMAL = `!top s x:A.
     connected_in top s /\ x IN s ==> s SUBSET (connected_component_of top x)`;;

let CONNECTED_COMPONENT_OF_EQUIV = `!top x y:A.
        connected_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        connected_component_of top x = connected_component_of top y`;;

let CONNECTED_COMPONENT_OF_DISJOINT = `!top x y:A.
        DISJOINT (connected_component_of top x)
                 (connected_component_of top y) <=>
        ~(connected_component_of top x y)`;;

let CONNECTED_COMPONENT_OF_EQ = `!top x y:A.
        connected_component_of top x = connected_component_of top y <=>
        ~(x IN topspace top) /\ ~(y IN topspace top) \/
        x IN topspace top /\ y IN topspace top /\
        connected_component_of top x y`;;

let CONNECTED_IN_CONNECTED_COMPONENT_OF = `!top x:A. connected_in top (connected_component_of top x)`;;

let UNIONS_CONNECTED_COMPONENTS_OF = `!top:A topology. UNIONS (connected_components_of top) = topspace top`;;

let CONNECTED_COMPONENTS_OF_MAXIMAL = `!top s c:A->bool.
        c IN connected_components_of top /\ connected_in top s /\ ~DISJOINT c s
        ==> s SUBSET c`;;

let PAIRWISE_DISJOINT_CONNECTED_COMPONENTS_OF = `!top:A topology. pairwise DISJOINT (connected_components_of top)`;;

let COMPLEMENT_CONNECTED_COMPONENTS_OF_UNIONS = `!top c:A->bool.
      c IN connected_components_of top
      ==> topspace top DIFF c = UNIONS (connected_components_of top DELETE c)`;;

let NONEMPTY_CONNECTED_COMPONENTS_OF = `!top c:A->bool. c IN connected_components_of top ==> ~(c = {})`;;

let CONNECTED_COMPONENTS_OF_SUBSET = `!top c:A->bool. c IN connected_components_of top ==> c SUBSET topspace top`;;

let CONNECTED_IN_CONNECTED_COMPONENTS_OF = `!top c:A->bool. c IN connected_components_of top ==> connected_in top c`;;

let CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF = `!top a:A.
        connected_component_of top a IN connected_components_of top <=>
        a IN topspace top`;;

let CONNECTED_SPACE_IFF_COMPONENTS_EQ = `!top:A topology.
        connected_space top <=>
        !c c'. c IN connected_components_of top /\
               c' IN connected_components_of top
               ==> c = c'`;;

let CONNECTED_COMPONENTS_OF_EQ_EMPTY = `!top:A topology. connected_components_of top = {} <=> topspace top = {}`;;

let CONNECTED_COMPONENTS_OF_EMPTY_SPACE = `!top:A topology. topspace top = {} ==> connected_components_of top = {}`;;

let CONNECTED_COMPONENTS_OF_SUBSET_SING = `!top s:A->bool.
        connected_components_of top SUBSET {s} <=>
        connected_space top /\ (topspace top = {} \/ topspace top = s)`;;

let CONNECTED_SPACE_IFF_COMPONENTS_SUBSET_SING = `!top:A topology.
        connected_space top <=> ?a. connected_components_of top SUBSET {a}`;;

let CONNECTED_COMPONENTS_OF_EQ_SING = `!top s:A->bool.
        connected_components_of top = {s} <=>
        connected_space top /\ ~(topspace top = {}) /\ s = topspace top`;;

let CONNECTED_COMPONENTS_OF_CONNECTED_SPACE = `!top:A topology.
        connected_space top
        ==> connected_components_of top =
            if topspace top = {} then {} else {topspace top}`;;

let EXISTS_CONNECTED_COMPONENT_OF_SUPERSET = `!top s:A->bool.
        connected_in top s /\ ~(topspace top = {})
        ==> ?c. c IN connected_components_of top /\ s SUBSET c`;;

let CLOSED_IN_CONNECTED_COMPONENTS_OF = `!top c:A->bool.
        c IN connected_components_of top ==> closed_in top c`;;

let CLOSED_IN_CONNECTED_COMPONENT_OF = `!top x:A. closed_in top (connected_component_of top x)`;;

let OPEN_IN_FINITE_CONNECTED_COMPONENTS = `!top c:A->bool.
        FINITE(connected_components_of top) /\
        c IN connected_components_of top
        ==> open_in top c`;;

let CONNECTED_COMPONENT_OF_EQ_OVERLAP = `!top x y:A.
      connected_component_of top x = connected_component_of top y <=>
      ~(x IN topspace top) /\ ~(y IN topspace top) \/
      ~(connected_component_of top x INTER connected_component_of top y = {})`;;

let CONNECTED_COMPONENT_OF_NONOVERLAP = `!top x y:A.
     connected_component_of top x INTER connected_component_of top y = {} <=>
     ~(x IN topspace top) \/ ~(y IN topspace top) \/
     ~(connected_component_of top x = connected_component_of top y)`;;

let CONNECTED_COMPONENT_OF_OVERLAP = `!top x y:A.
    ~(connected_component_of top x INTER connected_component_of top y = {}) <=>
    x IN topspace top /\ y IN topspace top /\
    connected_component_of top x = connected_component_of top y`;;

let CONNECTED_COMPONENTS_OF_DISJOINT = `!top c c'.
        c IN connected_components_of top /\ c' IN connected_components_of top
        ==> (DISJOINT c c' <=> ~(c = c'))`;;

let CONNECTED_COMPONENTS_OF_OVERLAP = `!top c c'.
        c IN connected_components_of top /\ c' IN connected_components_of top
        ==> (~(c INTER c' = {}) <=> c = c')`;;

let CONNECTED_IN_IFF_CONNECTED_COMPONENT_OF = `!top s:A->bool.
        connected_in top s <=>
        s SUBSET topspace top /\
        !x y. x IN s /\ y IN s ==> connected_component_of (subtopology top s) x y`;;

let PAIRWISE_SEPARATED_CONNECTED_COMPONENTS_OF = `!top:A topology.
        pairwise (separated_in top) (connected_components_of top)`;;

let CARD_LE_CONNECTED_COMPONENTS_OF_TOPSPACE = `!top:A topology. connected_components_of top <=_c topspace top`;;

let FINITE_CONNECTED_COMPONENTS_OF_FINITE = `!top:A topology.
        FINITE(topspace top) ==> FINITE(connected_components_of top)`;;

let CONNECTED_COMPONENT_OF_UNIQUE = `!top c x:A.
        x IN c /\ connected_in top c /\
        (!c'. x IN c' /\ connected_in top c' ==> c' SUBSET c)
        ==> connected_component_of top x = c`;;

let CLOSED_IN_CONNECTED_COMPONENT_OF_SUBTOPOLOGY = `!top c:A->bool.
        c IN connected_components_of(subtopology top s) /\
        top closure_of c SUBSET s
        ==> closed_in top c`;;

let CONNECTED_COMPONENT_OF_DISCRETE_TOPOLOGY = `!u x:A. connected_component_of (discrete_topology u) x =
           if x IN u then {x} else {}`;;

let CONNECTED_COMPONENTS_OF_DISCRETE_TOPOLOGY = `!u:A->bool.
        connected_components_of (discrete_topology u) = {{x} | x IN u}`;;

let CARD_LE_CONNNECTED_COMPONENTS_CONNECTED_IN = `!(top:A topology) u.
        (!c. c IN u ==> connected_in top c) /\
        UNIONS u = topspace top
        ==> connected_components_of top <=_c u`;;

let CARD_LE_CONNECTED_COMPONENTS_ALT = `!(top:A topology) n.
       ((1..n) <=_c connected_components_of top <=>
       n = 0 \/
       ?u. u HAS_SIZE n /\
           pairwise (separated_in top) u /\
           (!t. t IN u ==> ~(t = {})) /\
           UNIONS u = topspace top)`;;

let CONNECTED_COMPONENT_OF_CONTINUOUS_IMAGE = `!top top' (f:A->B) x y.
        continuous_map(top,top') f /\
        connected_component_of top x y
        ==> connected_component_of top' (f x) (f y)`;;

let HOMEOMORPHIC_MAP_CONNECTED_COMPONENT_OF = `!(f:A->B) top top' x.
        homeomorphic_map(top,top') f /\ x IN topspace top
        ==> connected_component_of top' (f x) =
            IMAGE f (connected_component_of top x)`;;

let HOMEOMORPHIC_MAP_CONNECTED_COMPONENTS_OF = `!(f:A->B) top top'.
      homeomorphic_map(top,top') f
      ==> connected_components_of top' =
          IMAGE (IMAGE f) (connected_components_of top)`;;

let CONNECTED_COMPONENT_OF_PAIR = `!top1 top2 (x:A) (y:B).
        connected_component_of (prod_topology top1 top2) (x,y) =
        connected_component_of top1 x CROSS connected_component_of top2 y`;;

let CONNECTED_COMPONENTS_OF_PROD_TOPOLOGY = `!(top1:A topology) (top2:B topology).
        connected_components_of (prod_topology top1 top2) =
        {c1 CROSS c2 | c1 IN connected_components_of top1 /\
                       c2 IN connected_components_of top2}`;;

let CONNECTED_COMPONENT_OF_PRODUCT_TOPOLOGY = `!k (tops:K->A topology) x.
        connected_component_of (product_topology k tops) x =
        if EXTENSIONAL k x
        then cartesian_product k (\i. connected_component_of (tops i) (x i))
        else {}`;;

let CONNECTED_COMPONENTS_OF_PRODUCT_TOPOLOGY = `!k (tops:K->A topology).
        connected_components_of (product_topology k tops) =
        { cartesian_product k c |c|
          !i. i IN k ==> c i IN connected_components_of(tops i)}`;;

(* ------------------------------------------------------------------------- *)
(* Monotone (in the general topological sense) maps.                         *)
(* ------------------------------------------------------------------------- *)

let monotone_map = new_definition
 `monotone_map(top,top') (f:A->B) <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !y. y IN topspace top'
            ==> connected_in top {x | x IN topspace top /\ f x = y}`;;

let MONOTONE_MAP = `!top top' f:A->B.
        monotone_map(top,top') f <=>
        IMAGE f (topspace top) SUBSET topspace top' /\
        !y. connected_in top {x | x IN topspace top /\ f x = y}`;;

let MONOTONE_MAP_IN_SUBTOPOLOGY = `!top top' s f:A->B.
        monotone_map(top,subtopology top' s) f <=>
        monotone_map(top,top') f /\ IMAGE f (topspace top) SUBSET s`;;

let MONOTONE_MAP_FROM_SUBTOPOLOGY = `!top top' s f:A->B.
        monotone_map(top,top') f /\
        (!x y. x IN topspace top /\ y IN topspace top /\ x IN s /\ f x = f y
               ==> y IN s)
        ==> monotone_map(subtopology top s,top') f`;;

let MONOTONE_MAP_RESTRICTION = `!top top' (f:A->B) u v.
        monotone_map(top,top') f /\ {x | x IN topspace top /\ f x IN v} = u
        ==> monotone_map (subtopology top u,subtopology top' v) f`;;

let INJECTIVE_IMP_MONOTONE_MAP = `!top top' f:A->B.
        IMAGE f (topspace top) SUBSET topspace top' /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y)
        ==> monotone_map (top,top') f`;;

let EMBEDDING_IMP_MONOTONE_MAP = `!top top' f:A->B.
        embedding_map (top,top') f ==> monotone_map (top,top') f`;;

let SECTION_IMP_MONOTONE_MAP = `!top top' f:A->B.
        section_map (top,top') f ==> monotone_map (top,top') f`;;

let HOMEOMORPHIC_IMP_MONOTONE_MAP = `!top top' f:A->B.
        homeomorphic_map (top,top') f ==> monotone_map (top,top') f`;;

let CONNECTED_SPACE_MONOTONE_QUOTIENT_MAP_PREIMAGE = `!top top' f:A->B.
        monotone_map(top,top') f /\ quotient_map (top,top') f /\
        connected_space top'
        ==> connected_space top`;;

let CONNECTED_IN_MONOTONE_QUOTIENT_MAP_PREIMAGE = `!top top' (f:A->B) c.
        monotone_map(top,top') f /\ quotient_map (top,top') f /\
        connected_in top' c /\ (open_in top' c \/ closed_in top' c)
        ==> connected_in top {x | x IN topspace top /\ f x IN c}`;;

let MONOTONE_OPEN_MAP = `!top top' f:A->B.
        continuous_map(top,top') f /\
        open_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> (monotone_map(top,top') f <=>
             !c. connected_in top' c
                 ==> connected_in top {x | x IN topspace top /\ f x IN c})`;;

let MONOTONE_CLOSED_MAP = `!top top' f:A->B.
        continuous_map(top,top') f /\
        closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> (monotone_map(top,top') f <=>
             !c. connected_in top' c
                 ==> connected_in top {x | x IN topspace top /\ f x IN c})`;;

(* ------------------------------------------------------------------------- *)
(* Neigbourhood bases (useful for "local" properties of various kind).       *)
(* ------------------------------------------------------------------------- *)

let neighbourhood_base_at = new_definition
 `neighbourhood_base_at (x:A) P top <=>
        !w. open_in top w /\ x IN w
            ==>  ?u v. open_in top u /\ P v /\
                     x IN u /\ u SUBSET v /\ v SUBSET w`;;

let neighbourhood_base_of = new_definition
 `neighbourhood_base_of P top <=>
        !x. x IN topspace top ==> neighbourhood_base_at x P top`;;

let NEIGHBOURHOOD_BASE_OF = `!(top:A topology) P.
        neighbourhood_base_of P top <=>
        !w x. open_in top w /\ x IN w
              ==> ?u v. open_in top u /\ P v /\
                        x IN u /\ u SUBSET v /\ v SUBSET w`;;

let NEIGHBOURHOOD_BASE_AT_MONO = `!top P Q x:A.
        (!s. P s /\ x IN s ==> Q s) /\ neighbourhood_base_at x P top
        ==> neighbourhood_base_at x Q top`;;

let NEIGHBOURHOOD_BASE_OF_MONO = `!top P Q:(A->bool)->bool.
        (!s. P s ==> Q s) /\ neighbourhood_base_of P top
        ==> neighbourhood_base_of Q top`;;

let OPEN_NEIGHBOURHOOD_BASE_AT = `!top P x:A.
        (!s. P s /\ x IN s ==> open_in top s)
        ==> (neighbourhood_base_at x P top <=>
             !w. open_in top w /\ x IN w ==> ?u. P u /\ x IN u /\ u SUBSET w)`;;

let OPEN_NEIGHBOURHOOD_BASE_OF = `!top P:(A->bool)->bool.
      (!s. P s ==> open_in top s)
      ==> (neighbourhood_base_of P top <=>
           !w x. open_in top w /\ x IN w ==> ?u. P u /\ x IN u /\ u SUBSET w)`;;

let OPEN_IN_TOPOLOGY_NEIGHBOURHOOD_BASE_UNIQUE = `!top b:(A->bool)->bool.
        open_in top = ARBITRARY UNION_OF b <=>
        (!u. u IN b ==> open_in top u) /\ neighbourhood_base_of b top`;;

let NEIGHBOURHOOD_BASE_OF_OPEN_SUBSET = `!top P s:A->bool.
        neighbourhood_base_of P top /\ open_in top s
        ==> neighbourhood_base_of P (subtopology top s)`;;

let NEIGHBOURHOOD_BASE_AT_TOPOLOGY_BASE = `!P top b x:A.
        open_in top = ARBITRARY UNION_OF b
        ==> (neighbourhood_base_at x P top <=>
             !w. w IN b /\ x IN w
                 ==> ?u v. open_in top u /\
                           P v /\
                           x IN u /\
                           u SUBSET v /\
                           v SUBSET w)`;;

let NEIGHBOURHOOD_BASE_OF_TOPOLOGY_BASE = `!P top b:(A->bool)->bool.
        open_in top = ARBITRARY UNION_OF b
        ==> (neighbourhood_base_of P top <=>
             !w x. w IN b /\ x IN w
                   ==> ?u v. open_in top u /\
                             P v /\
                             x IN u /\
                             u SUBSET v /\
                             v SUBSET w)`;;

let NEIGHBOURHOOD_BASE_AT_UNLOCALIZED = `!top P x:A.
       (!s t. P s /\ open_in top t /\ x IN t /\ t SUBSET s ==> P t)
       ==> (neighbourhood_base_at x P top <=>
            x IN topspace top
            ==> ?u v. open_in top u /\ P v /\ x IN u /\
                      u SUBSET v /\ v SUBSET topspace top)`;;

let NEIGHBOURHOOD_BASE_OF_UNLOCALIZED = `!top P:(A->bool)->bool.
       (!s t. P s /\ open_in top t /\ ~(t = {}) /\ t SUBSET s ==> P t)
       ==> (neighbourhood_base_of P top <=>
            !x. x IN topspace top
                ==> ?u v. open_in top u /\ P v /\ x IN u /\
                          u SUBSET v /\ v SUBSET topspace top)`;;

let NEIGHBOURHOOD_BASE_AT_DISCRETE_TOPOLOGY = `!P u x:A.
        neighbourhood_base_at x P (discrete_topology u) <=>
        x IN u ==> P {x}`;;

let NEIGHBOURHOOD_BASE_OF_DISCRETE_TOPOLOGY = `!P u:A->bool.
        neighbourhood_base_of P (discrete_topology u) <=>
        !x. x IN u ==> P {x}`;;

let NEIGHBOURHOOD_BASE_AT_WITH_SUBSET = `!P top u x:A.
        open_in top u /\ x IN u
        ==> (neighbourhood_base_at x P top <=>
             neighbourhood_base_at x (\t. t SUBSET u /\ P t) top)`;;

let NEIGHBOURHOOD_BASE_OF_WITH_SUBSET = `!P top:A topology.
        neighbourhood_base_of P top <=>
        neighbourhood_base_of (\t. t SUBSET topspace top /\ P t) top`;;

let SECOND_COUNTABLE_NEIGHBOURHOOD_BASE_ALT = `!top:A topology.
        second_countable top <=>
        ?b. COUNTABLE b /\
            (!v. v IN b ==> open_in top v) /\
            neighbourhood_base_of b top`;;

let FIRST_COUNTABLE_NEIGHBOURHOOD_BASE_ALT = `!top:A topology.
        first_countable top <=>
        !x. x IN topspace top
            ==> ?b. COUNTABLE b /\
                    (!v. v IN b ==> open_in top v) /\
                    neighbourhood_base_at x b top`;;

let SECOND_COUNTABLE_NEIGHBOURHOOD_BASE = `!top:A topology.
        second_countable top <=>
        ?b. COUNTABLE b /\ neighbourhood_base_of b top`;;

let FIRST_COUNTABLE_NEIGHBOURHOOD_BASE = `!top:A topology.
        first_countable top <=>
        !x. x IN topspace top
            ==> ?b. COUNTABLE b /\ neighbourhood_base_at x b top`;;

(* ------------------------------------------------------------------------- *)
(* T_0 spaces and the Kolmogorov quotient.                                   *)
(* ------------------------------------------------------------------------- *)

let t0_space = new_definition
 `t0_space (top:A topology) <=>
        !x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
              ==> ?u. open_in top u /\ ~(x IN u <=> y IN u)`;;

let T0_SPACE_EXPANSIVE = `!top top':A topology.
         topspace top' = topspace top /\ (!u. open_in top u ==> open_in top' u)
         ==> t0_space top ==> t0_space top'`;;

let T1_IMP_T0_SPACE = `!top:A topology. t1_space top ==> t0_space top`;;

let T1_EQ_SYMMETRIC_T0_SPACE_ALT = `!top:A topology.
        t1_space top <=>
        t0_space top /\
        !x y. x IN topspace top /\ y IN topspace top
              ==> (x IN top closure_of {y} <=> y IN top closure_of {x})`;;

let T1_EQ_SYMMETRIC_T0_SPACE = `!top:A topology.
        t1_space top <=>
        t0_space top /\
        !x y. x IN top closure_of {y} <=> y IN top closure_of {x}`;;

let HAUSDORFF_IMP_T0_SPACE = `!top:A topology. hausdorff_space top ==> t0_space top`;;

let T0_SPACE = `!top:A topology.
        t0_space top <=>
        !x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
              ==> ?c. closed_in top c /\ ~(x IN c <=> y IN c)`;;

let HOMEOMORPHIC_T0_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (t0_space top <=> t0_space top')`;;

let T0_SPACE_CLOSURE_OF_SING = `!top:A topology.
        t0_space top <=>
        !x y. x IN topspace top /\ y IN topspace top /\
              top closure_of {x} = top closure_of {y}
              ==> x = y`;;

let T0_SPACE_DISCRETE_TOPOLOGY = `!s:A->bool. t0_space(discrete_topology s)`;;

let T0_SPACE_SUBTOPOLOGY = `!top u:A->bool.
        t0_space top ==> t0_space(subtopology top u)`;;

let T0_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ t0_space top ==> t0_space top'`;;

let T0_SPACE_PROD_TOPOLOGY = `!(top1:A topology) (top2:B topology).
        t0_space(prod_topology top1 top2) <=>
        topspace (prod_topology top1 top2) = {} \/
        t0_space top1 /\ t0_space top2`;;

let T0_SPACE_PRODUCT_TOPOLOGY = `!tops:K->A topology k.
        t0_space (product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        !i. i IN k ==> t0_space (tops i)`;;

let kolmogorov_quotient = new_definition
 `kolmogorov_quotient top =
     \x:A. @y. !u. open_in top u ==> (y IN u <=> x IN u)`;;

let KOLMOGOROV_QUOTIENT_IN_OPEN = `!top u x:A. open_in top u ==> (kolmogorov_quotient top x IN u <=> x IN u)`;;

let KOLMOGOROV_QUOTIENT_IN_TOPSPACE = `!top x:A. kolmogorov_quotient top x IN topspace top <=> x IN topspace top`;;

let KOLMOGOROV_QUOTIENT_IN_CLOSED = `!top c x:A.
      closed_in top c ==> (kolmogorov_quotient top x IN c <=> x IN c)`;;

let CONTINUOUS_MAP_KOLMOGOROV_QUOTIENT = `!top:A topology.
        continuous_map (top,top) (kolmogorov_quotient top)`;;

let OPEN_MAP_KOLMOGOROV_QUOTIENT_EXPLICIT = `!top u:A->bool.
        open_in top u
        ==> IMAGE (kolmogorov_quotient top) u =
            IMAGE (kolmogorov_quotient top) (topspace top) INTER u`;;

let OPEN_MAP_KOLMOGOROV_QUOTIENT_GEN = `!top s:A->bool.
        open_map (subtopology top s,
                  subtopology top (IMAGE (kolmogorov_quotient top) s))
                 (kolmogorov_quotient top)`;;

let OPEN_MAP_KOLMOGOROV_QUOTIENT = `!top:A topology.
        open_map (top,subtopology top
                        (IMAGE (kolmogorov_quotient top) (topspace top)))
                 (kolmogorov_quotient top)`;;

let CLOSED_MAP_KOLMOGOROV_QUOTIENT_EXPLICIT = `!top u:A->bool.
        closed_in top u
        ==> IMAGE (kolmogorov_quotient top) u =
            IMAGE (kolmogorov_quotient top) (topspace top) INTER u`;;

let CLOSED_MAP_KOLMOGOROV_QUOTIENT_GEN = `!top s:A->bool.
        closed_map (subtopology top s,
                  subtopology top (IMAGE (kolmogorov_quotient top) s))
                 (kolmogorov_quotient top)`;;

let CLOSED_MAP_KOLMOGOROV_QUOTIENT = `!top:A topology.
        closed_map (top,subtopology top
                        (IMAGE (kolmogorov_quotient top) (topspace top)))
                   (kolmogorov_quotient top)`;;

let QUOTIENT_MAP_KOLMOGOROV_QUOTIENT_GEN = `!top s:A->bool.
        quotient_map (subtopology top s,
                      subtopology top (IMAGE (kolmogorov_quotient top) s))
                     (kolmogorov_quotient top)`;;

let QUOTIENT_MAP_KOLMOGOROV_QUOTIENT = `!top:A topology.
        quotient_map (top,subtopology top
                         (IMAGE (kolmogorov_quotient top) (topspace top)))
                     (kolmogorov_quotient top)`;;

let KOLMOGOROV_QUOTIENT_EQ = `!top x y:A.
        kolmogorov_quotient top x = kolmogorov_quotient top y <=>
        !u. open_in top u ==> (x IN u <=> y IN u)`;;

let KOLMOGOROV_QUOTIENT_EQ_ALT = `!top x y:A.
        kolmogorov_quotient top x = kolmogorov_quotient top y <=>
        !u. closed_in top u ==> (x IN u <=> y IN u)`;;

let KOLMOGOROV_QUOTIENT_CONTINUOUS_MAP = `!top top' (f:A->B) x.
        continuous_map (top,top') f /\ t0_space top' /\ x IN topspace top
        ==> f (kolmogorov_quotient top x) = f x`;;

let T0_SPACE_KOLMOGOROV_QUOTIENT = `!top:A topology.
        t0_space (subtopology top
                   (IMAGE (kolmogorov_quotient top) (topspace top)))`;;

let KOLMOGOROV_QUOTIENT_ID = `!top x:A. t0_space top /\ x IN topspace top
             ==> kolmogorov_quotient top x = x`;;

let KOLMOGOROV_QUOTIENT_IDEMP = `!top x:A.
    kolmogorov_quotient top (kolmogorov_quotient top x) =
    kolmogorov_quotient top x`;;

let RETRACTION_MAPS_KOLMOGOROV_QUOTIENT = `!top:A topology.
        retraction_maps
         (top,
          subtopology top (IMAGE (kolmogorov_quotient top) (topspace top)))
         (kolmogorov_quotient top,I)`;;

let RETRACTION_MAP_KOLMOGOROV_QUOTIENT = `!top:A topology.
        retraction_map
         (top,
          subtopology top (IMAGE (kolmogorov_quotient top) (topspace top)))
         (kolmogorov_quotient top)`;;

let RETRACT_OF_SPACE_KOLMOGOROV_QUOTIENT_IMAGE = `!top:A topology.
        IMAGE (kolmogorov_quotient top) (topspace top)
        retract_of_space top`;;

let KOLMOGOROV_QUOTIENT_LIFT_EXISTS = `!top top' (f:A->B) s.
      s SUBSET topspace top /\ t0_space top' /\
      continuous_map (subtopology top s,top') f
      ==> ?g. continuous_map
               (subtopology top (IMAGE (kolmogorov_quotient top) s), top') g /\
              !x. x IN s ==> g(kolmogorov_quotient top x) = f x`;;

(* ------------------------------------------------------------------------- *)
(* Regular spaces. These are *not* a priori assumed to be Hausdorff/T_1.     *)
(* ------------------------------------------------------------------------- *)

let regular_space = new_definition
 `regular_space top <=>
        !c a:A. closed_in top c /\ a IN topspace top DIFF c
                ==> ?u v. open_in top u /\ open_in top v /\
                          a IN u /\ c SUBSET v /\ DISJOINT u v`;;

let HOMEOMORPHIC_REGULAR_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (regular_space top <=> regular_space top')`;;

let REGULAR_SPACE = `!top:A topology.
        regular_space top <=>
        !c a. closed_in top c /\ a IN topspace top DIFF c
              ==> ?u. open_in top u /\ a IN u /\
                      DISJOINT c (top closure_of u)`;;

let NEIGHBOURHOOD_BASE_OF_CLOSED_IN = `!top:A topology.
      neighbourhood_base_of (closed_in top) top <=> regular_space top`;;

let REGULAR_SPACE_DISCRETE_TOPOLOGY = `!s:A->bool. regular_space(discrete_topology s)`;;

let REGULAR_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        regular_space top ==> regular_space(subtopology top s)`;;

let REGULAR_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ regular_space top
        ==> regular_space top'`;;

let REGULAR_T0_IMP_HAUSDORFF_SPACE = `!top:A topology.
        regular_space top /\ t0_space top ==> hausdorff_space top`;;

let REGULAR_T0_EQ_HAUSDORFF_SPACE = `!top:A topology.
        regular_space top ==> (t0_space top <=> hausdorff_space top)`;;

let REGULAR_T1_IMP_HAUSDORFF_SPACE = `!top:A topology.
        regular_space top /\ t1_space top ==> hausdorff_space top`;;

let REGULAR_T1_EQ_HAUSDORFF_SPACE = `!top:A topology.
        regular_space top ==> (t1_space top <=> hausdorff_space top)`;;

let COMPACT_HAUSDORFF_IMP_REGULAR_SPACE = `!top:A topology.
        compact_space top /\ hausdorff_space top ==> regular_space top`;;

let NEIGHBOURHOOD_BASE_OF_CLOSED_HAUSDORFF_SPACE = `!top:A topology.
        regular_space top /\ hausdorff_space top <=>
        neighbourhood_base_of
         (\c. closed_in top c /\ hausdorff_space(subtopology top c)) top`;;

let LOCALLY_COMPACT_IMP_KC_EQ_HAUSDORFF_SPACE = `!top:A topology.
        neighbourhood_base_of (compact_in top) top
        ==> (kc_space top <=> hausdorff_space top)`;;

let REGULAR_SPACE_MTOPOLOGY = `!m:A metric. regular_space(mtopology m)`;;

let METRIZABLE_IMP_REGULAR_SPACE = `!top:A topology. metrizable_space top ==> regular_space top`;;

let REGULAR_SPACE_COMPACT_CLOSED_SEPARATION = `!top s t:A->bool.
        regular_space top /\
        compact_in top s /\ closed_in top t /\ DISJOINT s t
        ==> ?u v. open_in top u /\ open_in top v /\
                  s SUBSET u /\ t SUBSET v /\ DISJOINT u v`;;

let REGULAR_SPACE_COMPACT_CLOSED_SETS = `!top:A topology.
        regular_space top <=>
        !s t. compact_in top s /\ closed_in top t /\ DISJOINT s t
              ==> ?u v. open_in top u /\ open_in top v /\
                        s SUBSET u /\ t SUBSET v /\ DISJOINT u v`;;

let REGULAR_SPACE_PROD_TOPOLOGY = `!(top1:A topology) (top2:B topology).
        regular_space (prod_topology top1 top2) <=>
        topspace (prod_topology top1 top2) = {} \/
        regular_space top1 /\ regular_space top2`;;

let REGULAR_SPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) k.
        regular_space (product_topology k tops) <=>
        topspace (product_topology k tops) = {} \/
        !i. i IN k ==> regular_space (tops i)`;;

let CLOSED_MAP_PAIRED_GEN = `!top top1 top2 (f:A->B) (g:A->C).
        closed_map(top,top1) f /\
        closed_map(top,top2) g /\
        (regular_space top1 /\ continuous_map(top,top1) f /\
         (!z. z IN topspace top2
              ==> closed_in top {x | x IN topspace top /\ g x = z}) \/
         regular_space top2 /\ continuous_map(top,top2) g /\
         (!y. y IN topspace top1
              ==> closed_in top {x | x IN topspace top /\ f x = y}))
        ==> closed_map (top,prod_topology top1 top2) (\x. f x,g x)`;;

let CLOSED_MAP_PAIRED = `!top top1 top2 (f:A->B) (g:A->C).
        closed_map(top,top1) f /\ continuous_map(top,top1) f /\
        closed_map(top,top2) g /\ continuous_map(top,top2) g /\
        (t1_space top1 /\ regular_space top2 \/
         regular_space top1 /\ t1_space top2)
        ==> closed_map (top,prod_topology top1 top2) (\x. f x,g x)`;;

let CLOSED_MAP_PAIRWISE = `!top top1 top2 f:A->B#C.
        closed_map(top,top1) (FST o f) /\ continuous_map(top,top1) (FST o f) /\
        closed_map(top,top2) (SND o f) /\ continuous_map(top,top2) (SND o f) /\
        (t1_space top1 /\ regular_space top2 \/
         regular_space top1 /\ t1_space top2)
        ==> closed_map (top,prod_topology top1 top2) f`;;

let CLOSED_MAP_PAIRED_CLOSED_MAP_RIGHT = `!top top' (f:A->B).
        closed_map(top,top') f /\
        (!y. y IN topspace top'
              ==> closed_in top {x | x IN topspace top /\ f x = y}) /\
        regular_space top
        ==> closed_map(top,prod_topology top top') (\x. x,f x)`;;

let CLOSED_MAP_PAIRED_CLOSED_MAP_LEFT = `!top top' (f:A->B).
        closed_map(top,top') f /\
        (!y. y IN topspace top'
              ==> closed_in top {x | x IN topspace top /\ f x = y}) /\
        regular_space top
        ==> closed_map(top,prod_topology top' top) (\x. f x,x)`;;

let CLOSED_MAP_IMP_CLOSED_GRAPH = `!top top' (f:A->B).
        closed_map(top,top') f /\
        (!y. y IN topspace top'
              ==> closed_in top {x | x IN topspace top /\ f x = y}) /\
        regular_space top
        ==> closed_in (prod_topology top top') {x,f x | x IN topspace top}`;;

let PROPER_MAP_PAIRED_CLOSED_MAP_RIGHT = `!top top' (f:A->B).
        closed_map(top,top') f /\
        (!y. y IN topspace top'
              ==> closed_in top {x | x IN topspace top /\ f x = y}) /\
        regular_space top
        ==> proper_map(top,prod_topology top top') (\x. x,f x)`;;

let PROPER_MAP_PAIRED_CLOSED_MAP_LEFT = `!top top' (f:A->B).
        closed_map(top,top') f /\
        (!y. y IN topspace top'
              ==> closed_in top {x | x IN topspace top /\ f x = y}) /\
        regular_space top
        ==> proper_map(top,prod_topology top' top) (\x. f x,x)`;;

let REGULAR_SPACE_CONTINUOUS_PROPER_MAP_IMAGE = `!top top' (f:A->B).
        regular_space top /\
        continuous_map(top,top') f /\
        proper_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> regular_space top'`;;

let REGULAR_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
    regular_space top /\ perfect_map(top,top') f ==> regular_space top'`;;

let REGULAR_SPACE_PERFECT_MAP_IMAGE_EQ = `!top top' (f:A->B).
        hausdorff_space top /\ perfect_map(top,top') f
        ==> (regular_space top <=> regular_space top')`;;

(* ------------------------------------------------------------------------- *)
(* Locally compact spaces.                                                   *)
(* ------------------------------------------------------------------------- *)

let locally_compact_space = new_definition
 `locally_compact_space top <=>
    !x. x IN topspace top
        ==> ?u k. open_in top u /\ compact_in top k /\ x IN u /\ u SUBSET k`;;

let HOMEOMORPHIC_LOCALLY_COMPACT_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (locally_compact_space top <=> locally_compact_space top')`;;

let LOCALLY_COMPACT_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map (top,top') r /\ locally_compact_space top
        ==> locally_compact_space top'`;;

let COMPACT_IMP_LOCALLY_COMPACT_SPACE = `!top:A topology. compact_space top ==> locally_compact_space top`;;

let NEIGHBOURHOOD_BASE_IMP_LOCALLY_COMPACT_SPACE = `!top:A topology.
         neighbourhood_base_of (compact_in top) top
         ==> locally_compact_space top`;;

let LOCALLY_COMPACT_SPACE_NEIGHBOURHOOD_BASE = `(!top:A topology.
        hausdorff_space top \/ regular_space top
        ==> (locally_compact_space top <=>
             neighbourhood_base_of (compact_in top) top))`
and LOCALLY_COMPACT_HAUSDORFF_IMP_REGULAR_SPACE = `(!top:A topology.
        locally_compact_space top /\ hausdorff_space top
        ==> regular_space top)`;;

let LOCALLY_COMPACT_HAUSDORFF_OR_REGULAR = `!top:A topology.
        locally_compact_space top /\
        (hausdorff_space top \/ regular_space top) <=>
        locally_compact_space top /\ regular_space top`;;

let LOCALLY_COMPACT_SPACE_COMPACT_CLOSED_IN = `!top:A topology.
        hausdorff_space top \/ regular_space top
        ==> (locally_compact_space top <=>
             !x. x IN topspace top
                 ==> ?u k. open_in top u /\
                           compact_in top k /\ closed_in top k /\
                           x IN u /\ u SUBSET k)`;;

let LOCALLY_COMPACT_SPACE_COMPACT_CLOSURE_OF = `!top:A topology.
        hausdorff_space top \/ regular_space top
        ==> (locally_compact_space top <=>
             !x. x IN topspace top
                 ==> ?u. open_in top u /\ compact_in top (top closure_of u) /\
                         x IN u)`;;

let LOCALLY_COMPACT_SPACE_NEIGHBOURHOOD_BASE_CLOSED_IN = `!top:A topology.
     hausdorff_space top \/ regular_space top
     ==> (locally_compact_space top <=>
          neighbourhood_base_of(\c. compact_in top c /\ closed_in top c) top)`;;

let LOCALLY_COMPACT_SPACE_NEIGHBOURHOOD_BASE_CLOSURE_OF = `!top:A topology.
      hausdorff_space top \/ regular_space top
      ==> (locally_compact_space top <=>
           neighbourhood_base_of (\t. compact_in top (top closure_of t)) top)`;;

let LOCALLY_COMPACT_SPACE_NEIGHBOURHOOD_BASE_OPEN_CLOSURE_OF = `!top:A topology.
        hausdorff_space top \/ regular_space top
        ==> (locally_compact_space top <=>
             neighbourhood_base_of
              (\u. open_in top u /\ compact_in top (top closure_of u))
             top)`;;

let LOCALLY_COMPACT_SPACE_COMPACT_CLOSED_COMPACT = `!top:A topology.
        hausdorff_space top \/ regular_space top
        ==> (locally_compact_space top <=>
             !k. compact_in top k
                 ==> ?u l. open_in top u /\
                           compact_in top l /\
                           closed_in top l /\
                           k SUBSET u /\
                           u SUBSET l)`;;

let LOCALLY_COMPACT_REGULAR_SPACE_NEIGHBOURHOOD_BASE = `!top:A topology.
        locally_compact_space top /\ regular_space top <=>
        neighbourhood_base_of (\c. compact_in top c /\ closed_in top c) top`;;

let LOCALLY_COMPACT_KC_SPACE = `!top:A topology.
        neighbourhood_base_of (compact_in top) top /\ kc_space top <=>
        locally_compact_space top /\ hausdorff_space top`;;

let LOCALLY_COMPACT_KC_SPACE_ALT = `!top:A topology.
        neighbourhood_base_of (compact_in top) top /\ kc_space top <=>
        locally_compact_space top /\ hausdorff_space top /\ regular_space top`;;

let LOCALLY_COMPACT_KC_IMP_REGULAR_SPACE = `!top:A topology.
        neighbourhood_base_of (compact_in top) top /\ kc_space top
        ==> regular_space top`;;

let KC_LOCALLY_COMPACT_SPACE = `!top:A topology.
        kc_space top
        ==> (neighbourhood_base_of (compact_in top) top <=>
             locally_compact_space top /\
             hausdorff_space top /\
             regular_space top)`;;

let LOCALLY_COMPACT_SPACE_CLOSED_SUBSET = `!top s:A->bool.
        locally_compact_space top /\ closed_in top s
        ==> locally_compact_space (subtopology top s)`;;

let LOCALLY_COMPACT_SPACE_OPEN_SUBSET = `!top s:A->bool.
        (hausdorff_space top \/ regular_space top) /\
        locally_compact_space top /\ open_in top s
        ==> locally_compact_space (subtopology top s)`;;

let LOCALLY_COMPACT_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. locally_compact_space (discrete_topology u)`;;

let LOCALLY_COMPACT_SPACE_CONTINUOUS_OPEN_MAP_IMAGE = `!top top' f:A->B.
        continuous_map (top,top') f /\ open_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        locally_compact_space top
        ==> locally_compact_space top'`;;

let LOCALLY_COMPACT_SUBSPACE_OPEN_IN_CLOSURE_OF = `!top s:A->bool.
        hausdorff_space top /\
        s SUBSET topspace top /\ locally_compact_space(subtopology top s)
        ==> open_in (subtopology top (top closure_of s)) s`;;

let LOCALLY_COMPACT_SUBSPACE_CLOSED_INTER_OPEN_IN = `!top s:A->bool.
        hausdorff_space top /\
        s SUBSET topspace top /\ locally_compact_space(subtopology top s)
        ==> ?c u. closed_in top c /\ open_in top u /\ c INTER u = s`;;

let LOCALLY_COMPACT_SUBSPACE_OPEN_IN_CLOSURE_OF_EQ = `!top s:A->bool.
      hausdorff_space top /\ locally_compact_space top
      ==> (open_in (subtopology top (top closure_of s)) s <=>
           s SUBSET topspace top /\ locally_compact_space(subtopology top s))`;;

let LOCALLY_COMPACT_SUBSPACE_CLOSED_INTER_OPEN_IN_EQ = `!top s:A->bool.
      hausdorff_space top /\ locally_compact_space top
      ==> ((?c u. closed_in top c /\ open_in top u /\ c INTER u = s) <=>
           s SUBSET topspace top /\ locally_compact_space(subtopology top s))`;;

let DENSE_LOCALLY_COMPACT_OPEN_IN_HAUSDORFF_SPACE = `!top s:A->bool.
        hausdorff_space top /\
        s SUBSET topspace top /\
        top closure_of s = topspace top /\
        locally_compact_space(subtopology top s)
        ==> open_in top s`;;

let LOCALLY_COMPACT_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        locally_compact_space (prod_topology top1 top2) <=>
        topspace (prod_topology top1 top2) = {} \/
        locally_compact_space top1 /\ locally_compact_space top2`;;

let LOCALLY_COMPACT_SPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) k.
        locally_compact_space(product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        FINITE {i | i IN k /\ ~compact_space(tops i)} /\
        !i. i IN k ==> locally_compact_space(tops i)`;;

let LOCALLY_COMPACT_SPACE_SUM_TOPOLOGY = `!k (top:K->A topology).
        locally_compact_space(sum_topology k top) <=>
        !i. i IN k ==> locally_compact_space(top i)`;;

let QUOTIENT_MAP_PROD_RIGHT = `!(top:A topology) top1 top2 (f:B->C).
     locally_compact_space top /\ (hausdorff_space top \/ regular_space top) /\
     quotient_map(top1,top2) f
     ==> quotient_map (prod_topology top top1,prod_topology top top2)
                      (\(x,y). x,f y)`;;

let QUOTIENT_MAP_PROD_LEFT = `!top1 top2 (top:C topology) (f:A->B).
     locally_compact_space top /\ (hausdorff_space top \/ regular_space top) /\
     quotient_map(top1,top2) f
     ==> quotient_map (prod_topology top1 top,prod_topology top2 top)
                      (\(x,y). f x,y)`;;

let QUOTIENT_MAP_PROD = `!top1 top2 top1' top2' (f:A->B) (g:C->D).
        (locally_compact_space top1 /\
         (hausdorff_space top1 \/ regular_space top1) /\
         locally_compact_space top2' /\
         (hausdorff_space top2' \/ regular_space top2') \/
         locally_compact_space top1' /\
         (hausdorff_space top1' \/ regular_space top1') /\
         locally_compact_space top2 /\
         (hausdorff_space top2 \/ regular_space top2)) /\
        quotient_map(top1,top1') f /\ quotient_map(top2,top2') g
        ==> quotient_map (prod_topology top1 top2,prod_topology top1' top2')
                         (\(x,y). f x,g y)`;;

let LOCALLY_COMPACT_SPACE_PERFECT_MAP_PREIMAGE = `!top top' (f:A->B).
        locally_compact_space top' /\
        perfect_map(top,top') f
        ==> locally_compact_space top`;;

let LOCALLY_COMPACT_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
     (hausdorff_space top \/ regular_space top) /\
     locally_compact_space top /\
     perfect_map(top,top') f
     ==> locally_compact_space top'`;;

let LOCALLY_COMPACT_SPACE_PERFECT_MAP_IMAGE_EQ = `!top top' (f:A->B).
     (hausdorff_space top \/ regular_space top) /\
     perfect_map(top,top') f
     ==> (locally_compact_space top <=>
          locally_compact_space top')`;;

(* ------------------------------------------------------------------------- *)
(* The most basic facts about usual topology and metric on R.                *)
(* ------------------------------------------------------------------------- *)

let real_open = new_definition
  `real_open s <=>
      !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`;;

let real_closed = new_definition
 `real_closed s <=> real_open((:real) DIFF s)`;;

let euclideanreal = new_definition
 `euclideanreal = topology real_open`;;

let REAL_OPEN_EMPTY = `real_open {}`;;

let REAL_OPEN_UNIV = `real_open(:real)`;;

let REAL_OPEN_INTER = `!s t. real_open s /\ real_open t ==> real_open (s INTER t)`;;

let REAL_OPEN_UNIONS = `(!s. s IN f ==> real_open s) ==> real_open(UNIONS f)`;;

let REAL_OPEN_IN = `!s. real_open s <=> open_in euclideanreal s`;;

let TOPSPACE_EUCLIDEANREAL = `topspace euclideanreal = (:real)`;;

let TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY = `!s. topspace (subtopology euclideanreal s) = s`;;

let REAL_CLOSED_IN = `!s. real_closed s <=> closed_in euclideanreal s`;;

let REAL_OPEN_UNION = `!s t. real_open s /\ real_open t ==> real_open(s UNION t)`;;

let REAL_OPEN_SUBREAL_OPEN = `!s. real_open s <=> !x. x IN s ==> ?t. real_open t /\ x IN t /\ t SUBSET s`;;

let REAL_CLOSED_EMPTY = `real_closed {}`;;

let REAL_CLOSED_UNIV = `real_closed(:real)`;;

let REAL_CLOSED_UNION = `!s t. real_closed s /\ real_closed t ==> real_closed(s UNION t)`;;

let REAL_CLOSED_INTER = `!s t. real_closed s /\ real_closed t ==> real_closed(s INTER t)`;;

let REAL_CLOSED_INTERS = `!f. (!s. s IN f ==> real_closed s) ==> real_closed(INTERS f)`;;

let REAL_OPEN_REAL_CLOSED = `!s. real_open s <=> real_closed(UNIV DIFF s)`;;

let REAL_OPEN_DIFF = `!s t. real_open s /\ real_closed t ==> real_open(s DIFF t)`;;

let REAL_CLOSED_DIFF = `!s t. real_closed s /\ real_open t ==> real_closed(s DIFF t)`;;

let REAL_OPEN_INTERS = `!s. FINITE s /\ (!t. t IN s ==> real_open t) ==> real_open(INTERS s)`;;

let REAL_CLOSED_UNIONS = `!s. FINITE s /\ (!t. t IN s ==> real_closed t) ==> real_closed(UNIONS s)`;;

let REAL_OPEN_HALFSPACE_GT = `!a. real_open {x | x > a}`;;

let REAL_OPEN_HALFSPACE_LT = `!a. real_open {x | x < a}`;;

let REAL_OPEN_REAL_INTERVAL = `!a b. real_open(real_interval(a,b))`;;

let REAL_CLOSED_HALFSPACE_LE = `!a. real_closed {x | x <= a}`;;

let REAL_CLOSED_HALFSPACE_GE = `!a. real_closed {x | x >= a}`;;

let REAL_CLOSED_REAL_INTERVAL = `!a b. real_closed(real_interval[a,b])`;;

let REAL_CLOSED_SING = `!a. real_closed {a}`;;

let real_euclidean_metric = new_definition
  `real_euclidean_metric = metric ((:real),\(x,y). abs(y-x))`;;

let REAL_EUCLIDEAN_METRIC = `mspace real_euclidean_metric = (:real) /\
   (!x y. mdist real_euclidean_metric (x,y) = abs(y-x))`;;

let MTOPOLOGY_REAL_EUCLIDEAN_METRIC = `mtopology real_euclidean_metric = euclideanreal`;;

let MBALL_REAL_INTERVAL = `!x r. mball real_euclidean_metric (x,r) = real_interval(x - r,x + r)`;;

let MCBALL_REAL_INTERVAL = `!x r. mcball real_euclidean_metric (x,r) = real_interval[x - r,x + r]`;;

let METRIZABLE_SPACE_EUCLIDEANREAL = `metrizable_space euclideanreal`;;

let HAUSDORFF_SPACE_EUCLIDEANREAL = `hausdorff_space euclideanreal`;;

let KC_SPACE_EUCLIDEANREAL = `kc_space euclideanreal`;;

let T1_SPACE_EUCLIDEANREAL = `t1_space euclideanreal`;;

let REGULAR_SPACE_EUCLIDEANREAL = `regular_space euclideanreal`;;

let SUBBASE_SUBTOPOLOGY_EUCLIDEANREAL = `!u. topology
        (ARBITRARY UNION_OF
          (FINITE INTERSECTION_OF
            ({{x | x > a} | a IN (:real)} UNION {{x | x < a} | a IN (:real)})
           relative_to u)) =
       subtopology euclideanreal u`;;

let EUCLIDEANREAL_CLOSURE_OF_HALFSPACE_GE = `!a. euclideanreal closure_of {x | x >= a} = {x | x >= a}`;;

let EUCLIDEANREAL_CLOSURE_OF_HALFSPACE_LE = `!a. euclideanreal closure_of {x | x <= a} = {x | x <= a}`;;

let EUCLIDEANREAL_CLOSURE_OF_HALFSPACE_GT = `!a. euclideanreal closure_of {x | x > a} = {x | x >= a}`;;

let EUCLIDEANREAL_CLOSURE_OF_HALFSPACE_LT = `!a. euclideanreal closure_of {x | x < a} = {x | x <= a}`;;

let EUCLIDEANREAL_INTERIOR_OF_HALFSPACE_GE = `!a. euclideanreal interior_of {x | x >= a} = {x | x > a}`;;

let EUCLIDEANREAL_INTERIOR_OF_HALFSPACE_LE = `!a. euclideanreal interior_of {x | x <= a} = {x | x < a}`;;

let EUCLIDEANREAL_INTERIOR_OF_HALFSPACE_GT = `!a. euclideanreal interior_of {x | x > a} = {x | x > a}`;;

let EUCLIDEANREAL_INTERIOR_OF_HALFSPACE_LT = `!a. euclideanreal interior_of {x | x < a} = {x | x < a}`;;

let EUCLIDEANREAL_FRONTIER_OF_HALFSPACE_GE = `!a. euclideanreal frontier_of {x | x >= a} = {x | x = a}`;;

let EUCLIDEANREAL_FRONTIER_OF_HALFSPACE_LE = `!a. euclideanreal frontier_of {x | x <= a} = {x | x = a}`;;

let EUCLIDEANREAL_FRONTIER_OF_HALFSPACE_GT = `!a. euclideanreal frontier_of {x | x > a} = {x | x = a}`;;

let EUCLIDEANREAL_FRONTIER_OF_HALFSPACE_LT = `!a. euclideanreal frontier_of {x | x < a} = {x | x = a}`;;

let EUCLIDEANREAL_CLOSURE_OF_RATIONAL = `euclideanreal closure_of rational = (:real)`;;

let EUCLIDEANREAL_CLOSURE_OF_IRRATIONAL = `euclideanreal closure_of {z | ~rational z} = (:real)`;;

let NOT_LOCALLY_COMPACT_SPACE_RATIONAL_GEN = `!s. ~(euclideanreal interior_of s = {})
       ==> ~locally_compact_space
              (subtopology euclideanreal {q | q IN s /\ rational q})`;;

let NOT_LOCALLY_COMPACT_SPACE_IRRATIONAL_GEN = `!s. ~(euclideanreal interior_of s = {})
       ==> ~locally_compact_space
              (subtopology euclideanreal {q | q IN s /\ ~rational q})`;;

let NOT_LOCALLY_COMPACT_SPACE_RATIONAL = `~locally_compact_space (subtopology euclideanreal rational)`;;

let NOT_LOCALLY_COMPACT_SPACE_IRRATIONAL = `~locally_compact_space (subtopology euclideanreal {z | ~rational z})`;;

(* ------------------------------------------------------------------------- *)
(* Boundedness in R.                                                         *)
(* ------------------------------------------------------------------------- *)

let real_bounded = new_definition
 `real_bounded s <=> ?B. !x. x IN s ==> abs(x) <= B`;;

let REAL_BOUNDED_POS = `!s. real_bounded s <=> ?B. &0 < B /\ !x. x IN s ==> abs(x) <= B`;;

let MBOUNDED_REAL_EUCLIDEAN_METRIC = `mbounded real_euclidean_metric = real_bounded`;;

let REAL_BOUNDED_REAL_INTERVAL = `(!a b. real_bounded(real_interval[a,b])) /\
   (!a b. real_bounded(real_interval(a,b)))`;;

let REAL_BOUNDED_SHRINK = `!s. real_bounded (IMAGE (\x. x / (&1 + abs x)) s)`;;

let NOT_REAL_BOUNDED_UNIV = `~real_bounded (:real)`;;

(* ------------------------------------------------------------------------- *)
(* Connectedness and compactness characterizations for R.                    *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_IN_EUCLIDEANREAL = `!s. connected_in euclideanreal s <=> is_realinterval s`;;

let CONNECTED_IN_EUCLIDEANREAL_INTERVAL = `(!a b. connected_in euclideanreal (real_interval[a,b])) /\
   (!a b. connected_in euclideanreal (real_interval(a,b)))`;;

let COMPACT_IN_EUCLIDEANREAL_INTERVAL = `!a b. compact_in euclideanreal (real_interval[a,b])`;;

let COMPACT_IN_EUCLIDEANREAL = `!s. compact_in euclideanreal s <=>
       mbounded real_euclidean_metric s /\ closed_in euclideanreal s`;;

let real_compact_def = new_definition
 `real_compact s <=> compact_in euclideanreal s`;;

let REAL_COMPACT_EQ_BOUNDED_CLOSED = `!s. real_compact s <=> real_bounded s /\ real_closed s`;;

let REAL_COMPACT_IMP_BOUNDED = `!s. real_compact s ==> real_bounded s`;;

let REAL_COMPACT_IMP_CLOSED = `!s. real_compact s ==> real_closed s`;;

let NOT_REAL_COMPACT_UNIV = `~real_compact (:real)`;;

let NOT_COMPACT_SPACE_EUCLIDEANREAL = `~compact_space euclideanreal`;;

let REAL_COMPACT_INTERVAL = `!a b. real_compact(real_interval[a,b])`;;

let REAL_COMPACT_UNION = `!s t. real_compact s /\ real_compact t ==> real_compact(s UNION t)`;;

let REAL_CLOSED_CONTAINS_SUP = `!s b. real_closed s /\ ~(s = {}) /\ (!x. x IN s ==> x <= b)
         ==> sup s IN s`;;

let REAL_COMPACT_CONTAINS_SUP = `!s. real_compact s /\ ~(s = {}) ==> sup s IN s`;;

let REAL_COMPACT_ATTAINS_SUP = `!s. real_compact s /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> y <= x`;;

let REAL_CLOSED_CONTAINS_INF = `!s b. real_closed s /\ ~(s = {}) /\ (!x. x IN s ==> b <= x)
         ==> inf s IN s`;;

let REAL_COMPACT_CONTAINS_INF = `!s. real_compact s /\ ~(s = {}) ==> inf s IN s`;;

let REAL_COMPACT_ATTAINS_INF = `!s. real_compact s /\ ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> x <= y`;;

let REAL_COMPACT_IS_REALINTERVAL = `!s. real_compact s /\ is_realinterval s <=> ?a b. s = real_interval[a,b]`;;

let IS_REALINTERVAL_CLOSURE_OF = `!s. is_realinterval s ==> is_realinterval(euclideanreal closure_of s)`;;

let IS_REALINTERVAL_INTERIOR_OF = `!s. is_realinterval s ==> is_realinterval(euclideanreal interior_of s)`;;

let IS_REALINTERVAL_INTERIOR_SEGMENT = `!s a b.
        is_realinterval s /\
        a IN euclideanreal closure_of s /\ b IN euclideanreal closure_of s
        ==> real_interval(a,b) SUBSET euclideanreal interior_of s`;;

let REAL_OPEN_SUBSET_CLOSURE_OF_REALINTERVAL = `!u s. real_open u /\ is_realinterval s
         ==> (u SUBSET euclideanreal closure_of s <=>
              u SUBSET euclideanreal interior_of s)`;;

let REAL_OPEN_SUBSET_CLOSURE_OF_REALINTERVAL_ALT = `!u s. real_open u /\ is_realinterval s
         ==> (u SUBSET euclideanreal closure_of s <=> u SUBSET s)`;;

let INTERIOR_OF_CLOSURE_OF_REALINTERVAL = `!s. is_realinterval s
       ==> euclideanreal interior_of (euclideanreal closure_of s) =
           euclideanreal interior_of s`;;

let CLOSURE_OF_REAL_INTERVAL = `!a b. euclideanreal closure_of real_interval(a,b) =
         if real_interval(a,b) = {} then {} else real_interval[a,b]`;;

let INTERIOR_OF_REAL_INTERVAL = `!a b. euclideanreal interior_of real_interval[a,b] = real_interval(a,b)`;;

let CLOSURE_OF_INTERIOR_OF_REALINTERVAL = `!s. is_realinterval s /\ ~(euclideanreal interior_of s = {})
       ==> euclideanreal closure_of (euclideanreal interior_of s) =
           euclideanreal closure_of s`;;

let CARD_FRONTIER_OF_REALINTERVAL = `!s. is_realinterval s
       ==> FINITE(euclideanreal frontier_of s) /\
           CARD(euclideanreal frontier_of s) <= 2`;;

let LOCALLY_COMPACT_SPACE_EUCLIDEANREAL = `locally_compact_space euclideanreal`;;

(* ------------------------------------------------------------------------- *)
(* Limits at a point in a topological space.                                 *)
(* ------------------------------------------------------------------------- *)

let atpointof = new_definition
 `atpointof top a = mk_net({u | open_in top u /\ a IN u},{a})`;;

let ATPOINTOF = `(!top a:A.
        netfilter(atpointof top a) = {u | open_in top u /\ a IN u})`
and NETLIMITS_ATPOINTOF = `(!top a:A. netlimits(atpointof top a) = {a})`;;

let NETLIMIT_ATPOINTOF = `!top a:A. netlimit(atpointof top a) = a`;;

let EVENTUALLY_ATPOINTOF = `!P top a:A.
        eventually P (atpointof top a) <=>
        ~(a IN topspace top) \/
        ?u. open_in top u /\ a IN u /\ !x. x IN u DELETE a ==> P x`;;

let ATPOINTOF_WITHIN_TRIVIAL = `!top u a:A.
     topspace top SUBSET u ==> (atpointof top a) within u = atpointof top a`;;

let ATPOINTOF_WITHIN_TOPSPACE = `!top a:A. (atpointof top a) within (topspace top) = atpointof top a`;;

let TRIVIAL_LIMIT_ATPOINTOF_WITHIN = `!top s a:A.
        trivial_limit(atpointof top a within s) <=>
        ~(a IN top derived_set_of s)`;;

let DERIVED_SET_OF_TRIVIAL_LIMIT = `!top s a:A.
      a IN top derived_set_of s <=> ~trivial_limit(atpointof top a within s)`;;

let TRIVIAL_LIMIT_ATPOINTOF = `!top a:A.
        trivial_limit(atpointof top a) <=>
        ~(a IN top derived_set_of topspace top)`;;

let ATPOINTOF_SUBTOPOLOGY = `!top s a:A.
        a IN s
        ==> (atpointof (subtopology top s) a =
             atpointof top a within s)`;;

let EVENTUALLY_ATPOINTOF_METRIC = `!P m a:A.
        eventually P (atpointof (mtopology m) a) <=>
        a IN mspace m
        ==> ?d. &0 < d /\
                !x. x IN mspace m /\ &0 < mdist m (x,a) /\ mdist m (x,a) < d
                    ==> P x`;;

(* ------------------------------------------------------------------------- *)
(* Limits in a topological space.                                            *)
(* ------------------------------------------------------------------------- *)

let limit = new_definition
  `limit top (f:A->B) l net <=>
   l IN topspace top /\
   (!u. open_in top u /\ l IN u ==> eventually (\x. f x IN u) net)`;;

let LIMIT_IMP_WITHIN = `!net top (f:A->B) l s.
        limit top f l net ==> limit top f l (net within s)`;;

let LIMIT_IN_TOPSPACE = `!net top f:A->B l. limit top f l net ==> l IN topspace top`;;

let LIMIT_CONST = `!net:A net l:B. limit top (\a. l) l net <=> l IN topspace top`;;

let LIMIT_REAL_CONST = `!net:A net l. limit euclideanreal (\a. l) l net`;;

let LIMIT_CONST_EQ = `!(net:K net) top (a:A) l.
        t1_space top /\ ~trivial_limit net
        ==> (limit top (\k. a) l net <=> l IN topspace top /\ a = l)`;;

let LIMIT_EVENTUALLY = `!top net f:K->A l.
        l IN topspace top /\ eventually (\x. f x = l) net
        ==> limit top f l net`;;

let LIMIT_WITHIN_SUBSET = `!net top f:A->B l s t.
        limit top f l (net within s) /\ t SUBSET s
        ==> limit top f l (net within t)`;;

let LIMIT_SUBSEQUENCE = `!top f:num->A l r.
        (!m n. m < n ==> r m < r n) /\ limit top f l sequentially
        ==> limit top (f o r) l sequentially`;;

let LIMIT_SUBTOPOLOGY = `!net top s l f:A->B.
        limit (subtopology top s) f l net <=>
        l IN s /\ eventually (\a. f a IN s) net /\ limit top f l net`;;

let LIMIT_SEQUENTIALLY = `!top s l:A.
     limit top s l sequentially <=>
     l IN topspace top /\
     (!u. open_in top u /\ l IN u ==> (?N. !n. N <= n ==> s n IN u))`;;

let LIMIT_SEQUENTIALLY_OFFSET = `!top f l:A k. limit top f l sequentially
                 ==> limit top (\i. f (i + k)) l sequentially`;;

let LIMIT_SEQUENTIALLY_OFFSET_REV = `!top f l:A k. limit top (\i. f (i + k)) l sequentially
                 ==> limit top f l sequentially`;;

let LIMIT_ATPOINTOF = `!top top' f:A->B x y.
        limit top' f y (atpointof top x) <=>
        y IN topspace top' /\
        (x IN topspace top
         ==> !v. open_in top' v /\ y IN v
                 ==> ?u. open_in top u /\ x IN u /\
                         IMAGE f (u DELETE x) SUBSET v)`;;

let LIMIT_ATPOINTOF_SELF = `!top1 top2 f:A->B a.
        limit top2 f (f a) (atpointof top1 a) <=>
        f a IN topspace top2 /\
        (a IN topspace top1
         ==> (!v. open_in top2 v /\ f a IN v
                  ==> (?u. open_in top1 u /\ a IN u /\ IMAGE f u SUBSET v)))`;;

let LIMIT_TRIVIAL = `!net f:A->B top y.
        trivial_limit net /\ y IN topspace top ==> limit top f y net`;;

let LIMIT_TRANSFORM_EVENTUALLY = `!net top f:A->B g l.
        eventually (\x. f x = g x) net /\ limit top f l net
        ==> limit top g l net`;;

let CONTINUOUS_MAP_LIMIT = `!net top top' f:A->B g:B->C l.
     continuous_map (top,top')  g /\ limit top f l net
     ==> limit top' (g o f) (g l) net`;;

let LIMIT_PAIRWISE = `!(net:C net) top1:A topology top2:B topology f l.
        limit (prod_topology top1 top2) f l net <=>
        limit top1 (FST o f) (FST l) net /\
        limit top2 (SND o f) (SND l) net`;;

let LIMIT_COMPONENTWISE = `!(net:C net) (tops:K->A topology) t f l.
        limit (product_topology t tops) f l net <=>
        EXTENSIONAL t l /\
        eventually (\a. f a IN topspace(product_topology t tops)) net /\
        !k. k IN t ==> limit (tops k) (\c. f c k) (l k) net`;;

let COMPACT_IN_SEQUENCE_WITH_LIMIT = `!top s a l:A.
        limit top a l sequentially /\
        s SUBSET IMAGE a (:num) /\ s SUBSET topspace top
        ==> compact_in top (l INSERT s)`;;

let LIMIT_HAUSDORFF_UNIQUE = `!net top f:A->B l1 l2.
     ~trivial_limit net /\
     hausdorff_space top /\
     limit top f l1 net /\
     limit top f l2 net
     ==> l1 = l2`;;

let LIMIT_KC_UNIQUE = `!top (f:num->A) l1 l2.
      kc_space top /\
      limit top f l1 sequentially /\
      limit top f l2 sequentially
      ==> l1 = l2`;;

(* ------------------------------------------------------------------------- *)
(* Topological limit in metric spaces.                                       *)
(* ------------------------------------------------------------------------- *)

let LIMIT_IN_MSPACE = `!net m f:A->B l. limit (mtopology m) f l net ==> l IN mspace m`;;

let LIMIT_METRIC_UNIQUE = `!net m f:A->B l1 l2.
     ~trivial_limit net /\
     limit (mtopology m) f l1 net /\
     limit (mtopology m) f l2 net
     ==> l1 = l2`;;

let LIMIT_METRIC = `!m f:A->B l net.
     limit (mtopology m) f l net <=>
     l IN mspace m /\
     (!e. &0 < e
          ==> eventually (\x. f x IN mspace m /\ mdist m (f x, l) < e) net)`;;

let LIMIT_METRIC_SEQUENTIALLY = `!m f:num->A l.
     limit (mtopology m) f l sequentially <=>
     l IN mspace m /\
     (!e. &0 < e ==> (?N. !n. N <= n
                              ==> f n IN mspace m /\ mdist m (f n,l) < e))`;;

let LIMIT_IN_CLOSED_IN = `!net top s f:A->B l.
      ~trivial_limit net /\ limit top f l net /\
      closed_in top s /\ eventually (\x. f x IN s) net
      ==> l IN s`;;

let LIMIT_SUBMETRIC_IFF = `!net m s f:A->B l.
     limit (mtopology (submetric m s)) f l net <=>
     l IN s /\ eventually (\x. f x IN s) net /\ limit (mtopology m) f l net`;;

let METRIC_CLOSED_IN_IFF_SEQUENTIALLY_CLOSED = `!m s:A->bool.
     closed_in (mtopology m) s <=>
     s SUBSET mspace m /\
     (!a l. (!n. a n IN s) /\ limit (mtopology m) a l sequentially
            ==> l IN s)`;;

let LIMIT_ATPOINTOF_METRIC = `!m top f:A->B x y.
        limit top f y (atpointof (mtopology m) x) <=>
        y IN topspace top /\
        (x IN mspace m
         ==> !v. open_in top v /\ y IN v
                 ==> ?d. &0 < d /\
                         !x'. x' IN mspace m /\
                              &0 < mdist m (x',x) /\ mdist m (x',x) < d
                              ==> f x' IN v)`;;

let LIMIT_METRIC_DIST_NULL = `!net m (f:K->A) l.
        limit (mtopology m) f l net <=>
        l IN mspace m /\ eventually (\x. f x IN mspace m) net /\
        limit euclideanreal (\x. mdist m (f x,l)) (&0) net`;;

let LIMIT_NULL_REAL = `!net f:A->real.
        limit euclideanreal f (&0) net <=>
        !e. &0 < e ==> eventually (\a. abs(f a) < e) net`;;

let LIMIT_NULL_REAL_ABS = `!net (f:A->real).
        limit euclideanreal (\a. abs(f a)) (&0) net <=>
        limit euclideanreal f (&0) net`;;

let LIMIT_NULL_REAL_COMPARISON = `!net f g:A->real.
        limit euclideanreal f (&0) net /\
        eventually (\a. abs(g a) <= abs(f a)) net
        ==> limit euclideanreal g (&0) net`;;

let LIMIT_NULL_REAL_HARMONIC_OFFSET = `!a. limit euclideanreal (\n. inv(&n + a)) (&0) sequentially`;;

(* ------------------------------------------------------------------------- *)
(* More sequential characterizations in a metric space.                      *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY = `(!met P s a:A.
        eventually P (atpointof (mtopology met) a within s) <=>
        !x. (!n. x(n) IN (s INTER mspace met) DELETE a) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially)`
and EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_INJ = `(!met P s a:A.
        eventually P (atpointof (mtopology met) a within s) <=>
        !x. (!n. x(n) IN (s INTER mspace met) DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially)`
and EVENTUALLY_ATPOINTOF_WITHIN_SEQUENTIALLY_DECREASING = `(!met P s a:A.
        eventually P (atpointof (mtopology met) a within s) <=>
        !x. (!n. x(n) IN (s INTER mspace met) DELETE a) /\
            (!m n. m < n ==> mdist met (x n,a) < mdist met (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially)`;;

let EVENTUALLY_ATPOINTOF_SEQUENTIALLY = `!met P a:A.
        eventually P (atpointof (mtopology met) a) <=>
        !x. (!n. x(n) IN mspace met DELETE a) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially`;;

let EVENTUALLY_ATPOINTOF_SEQUENTIALLY_INJ = `!met P a:A.
        eventually P (atpointof (mtopology met) a) <=>
        !x. (!n. x(n) IN mspace met DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially`;;

let EVENTUALLY_ATPOINTOF_SEQUENTIALLY_DECREASING = `!met P a:A.
        eventually P (atpointof (mtopology met) a) <=>
        !x. (!n. x(n) IN mspace met DELETE a) /\
            (!m n. m < n ==> mdist met (x n,a) < mdist met (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology met) x a sequentially
            ==> eventually (\n. P(x n)) sequentially`;;

let LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN = `!m1 m2 s f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a within s) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN (s INTER mspace m1) DELETE a) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`;;

let LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN_INJ = `!m1 m2 s f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a within s) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN (s INTER mspace m1) DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`;;

let LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN_DECREASING = `!m1 m2 s f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a within s) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN (s INTER mspace m1) DELETE a) /\
            (!m n. m < n ==> mdist m1 (x n,a) < mdist m1 (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`;;

let LIMIT_ATPOINTOF_SEQUENTIALLY = `!m1 m2 f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN mspace m1 DELETE a) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`;;

let LIMIT_ATPOINTOF_SEQUENTIALLY_INJ = `!m1 m2 f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN mspace m1 DELETE a) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`;;

let LIMIT_ATPOINTOF_SEQUENTIALLY_DECREASING = `!m1 m2 f:A->B a l.
        limit (mtopology m2) f l (atpointof (mtopology m1) a) <=>
        l IN mspace m2 /\
        !x. (!n. x(n) IN mspace m1 DELETE a) /\
            (!m n. m < n ==> mdist m1 (x n,a) < mdist m1 (x m,a)) /\
            (!m n. x m = x n <=> m = n) /\
            limit (mtopology m1) x a sequentially
            ==> limit (mtopology m2) (f o x) l sequentially`;;

let DERIVED_SET_OF_SEQUENTIALLY = `!met s:A->bool.
        (mtopology met) derived_set_of s =
        {x | x IN mspace met /\
             ?f. (!n. f(n) IN ((s INTER mspace met) DELETE x)) /\
                 limit (mtopology met) f x sequentially}`;;

let DERIVED_SET_OF_SEQUENTIALLY_ALT = `!met s:A->bool.
        (mtopology met) derived_set_of s =
        {x | ?f. (!n. f(n) IN (s DELETE x)) /\
                 limit (mtopology met) f x sequentially}`;;

let DERIVED_SET_OF_SEQUENTIALLY_INJ = `!met s:A->bool.
        (mtopology met) derived_set_of s =
        {x | x IN mspace met /\
             ?f. (!n. f(n) IN ((s INTER mspace met) DELETE x)) /\
                 (!m n. f m = f n <=> m = n) /\
                 limit (mtopology met) f x sequentially}`;;

let DERIVED_SET_OF_SEQUENTIALLY_INJ_ALT = `!met s:A->bool.
        (mtopology met) derived_set_of s =
        {x | ?f. (!n. f(n) IN (s DELETE x)) /\
                 (!m n. f m = f n <=> m = n) /\
                 limit (mtopology met) f x sequentially}`;;

let DERIVED_SET_OF_SEQUENTIALLY_DECREASING = `!met s:A->bool.
        (mtopology met) derived_set_of s =
        {x | x IN mspace met /\
             ?f. (!n. f(n) IN ((s INTER mspace met) DELETE x)) /\
                 (!m n. m < n ==> mdist met (f n,x) < mdist met (f m,x)) /\
                 (!m n. f m = f n <=> m = n) /\
                 limit (mtopology met) f x sequentially}`;;

let DERIVED_SET_OF_SEQUENTIALLY_DECREASING_ALT = `!met s:A->bool.
        (mtopology met) derived_set_of s =
        {x | ?f. (!n. f(n) IN (s DELETE x)) /\
                 (!m n. m < n ==> mdist met (f n,x) < mdist met (f m,x)) /\
                 (!m n. f m = f n <=> m = n) /\
                 limit (mtopology met) f x sequentially}`;;

let CLOSURE_OF_SEQUENTIALLY = `!met s:A->bool.
        (mtopology met) closure_of s =
        {x | x IN mspace met /\
             ?f. (!n. f(n) IN (s INTER mspace met)) /\
                 limit (mtopology met) f x sequentially}`;;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for real limits.                                       *)
(* ------------------------------------------------------------------------- *)

let LIMIT_REAL_MUL = `!(net:A net) f g l m.
        limit euclideanreal f l net /\ limit euclideanreal g m net
        ==> limit euclideanreal (\x. f x * g x) (l * m) net`;;

let LIMIT_REAL_LMUL = `!(net:A net) c f l.
        limit euclideanreal f l net
        ==> limit euclideanreal (\x. c * f x) (c * l) net`;;

let LIMIT_REAL_LMUL_EQ = `!(net:A net) c f l.
        limit euclideanreal (\x. c * f x) (c * l) net <=>
        c = &0 \/ limit euclideanreal f l net`;;

let LIMIT_REAL_RMUL = `!(net:A net) f c l.
        limit euclideanreal f l net
        ==> limit euclideanreal (\x. f x * c) (l * c) net`;;

let LIMIT_REAL_RMUL_EQ = `!(net:A net) f c l.
        limit euclideanreal (\x. f x * c) (l * c) net <=>
        c = &0 \/ limit euclideanreal f l net`;;

let LIMIT_REAL_NEG = `!(net:A net) f l.
        limit euclideanreal f l net
        ==> limit euclideanreal (\x. --(f x)) (--l) net`;;

let LIMIT_REAL_NEG_EQ = `!(net:A net) f l.
        limit euclideanreal (\x. --(f x)) l net <=>
        limit euclideanreal f (--l) net`;;

let LIMIT_REAL_ADD = `!(net:A net) f g l m.
        limit euclideanreal f l net /\ limit euclideanreal g m net
        ==> limit euclideanreal (\x. f x + g x) (l + m) net`;;

let LIMIT_REAL_SUB = `!(net:A net) f g l m.
        limit euclideanreal f l net /\ limit euclideanreal g m net
        ==> limit euclideanreal (\x. f x - g x) (l - m) net`;;

let LIMIT_REAL_ABS = `!(net:A net) f l.
        limit euclideanreal f l net
        ==> limit euclideanreal (\x. abs(f x)) (abs l) net`;;

let LIMIT_REAL_MAX = `!(net:A net) f g l m.
        limit euclideanreal f l net /\ limit euclideanreal g m net
        ==> limit euclideanreal (\x. max (f x) (g x)) (max l m) net`;;

let LIMIT_REAL_MIN = `!(net:A net) f g l m.
        limit euclideanreal f l net /\ limit euclideanreal g m net
        ==> limit euclideanreal (\x. min (f x) (g x)) (min l m) net`;;

let LIMIT_SUM = `!net f:A->K->real l k.
        FINITE k /\
        (!i. i IN k ==> limit euclideanreal (\x. f x i) (l i) net)
        ==> limit euclideanreal (\x. sum k (f x)) (sum k l) net`;;

let LIMIT_PRODUCT = `!net f:A->K->real l k.
        FINITE k /\
        (!i. i IN k ==> limit euclideanreal (\x. f x i) (l i) net)
        ==> limit euclideanreal (\x. product k (f x)) (product k l) net`;;

let LIMIT_REAL_INV = `!(net:A net) f l.
        limit euclideanreal f l net /\ ~(l = &0)
        ==> limit euclideanreal (\x. inv(f x)) (inv l) net`;;

let LIMIT_REAL_DIV = `!(net:A net) f g l m.
      limit euclideanreal f l net /\ limit euclideanreal g m net /\ ~(m = &0)
      ==> limit euclideanreal (\x. f x / g x) (l / m) net`;;

let LIMIT_INF = `!net f:A->K->real l k.
        FINITE k /\
        (!i. i IN k ==> limit euclideanreal (\x. f x i) (l i) net)
        ==> limit euclideanreal
              (\x. inf {f x i | i IN k}) (inf {l i | i IN k}) net`;;

let LIMIT_SUP = `!net f:A->K->real l k.
        FINITE k /\
        (!i. i IN k ==> limit euclideanreal (\x. f x i) (l i) net)
        ==> limit euclideanreal
              (\x. sup {f x i | i IN k}) (sup {l i | i IN k}) net`;;

(* ------------------------------------------------------------------------- *)
(* Closure of Borel measurable functions under pointwise limits. This        *)
(* version needs a metric space for the codomain, though the result can be   *)
(* further generalized to perfectly normal topological spaces.               *)
(* ------------------------------------------------------------------------- *)

let BOREL_MEASURABLE_MAP_LIMIT = `!top1 top2 (f:num->A->B) g.
      metrizable_space top2 /\
      (!n. borel_measurable_map (top1,top2) (f n)) /\
      (!x. x IN topspace top1 ==> limit top2 (\k. f k x) (g x) sequentially)
      ==> borel_measurable_map (top1,top2) g`;;

(* ------------------------------------------------------------------------- *)
(* Cauchy sequences and complete metric spaces.                              *)
(* ------------------------------------------------------------------------- *)

let cauchy_in = new_definition
  `!m:A metric s:num->A.
     cauchy_in m s <=>
     (!n. s n IN mspace m) /\
     (!e. &0 < e
          ==> (?N. !n n'. N <= n /\ N <= n'
                          ==> mdist m (s n,s n') < e))`;;

let mcomplete = new_definition
  `!m:A metric.
     mcomplete m <=>
     (!s. cauchy_in m s ==> ?x. limit (mtopology m) s x sequentially)`;;

let MCOMPLETE = `!m:A metric.
        mcomplete m <=>
        !s. eventually (\n. s n IN mspace m) sequentially /\
            (!e. &0 < e
                 ==> ?N. !n n'. N <= n /\ N <= n' ==> mdist m (s n,s n') < e)
            ==> ?x. limit (mtopology m) s x sequentially`;;

let MCOMPLETE_EMPTY_MSPACE = `!m:A metric. mspace m = {} ==> mcomplete m`;;

let MCOMPLETE_SUBMETRIC_EMPTY = `!m:A metric. mcomplete(submetric m {})`;;

let CAUCHY_IN_SUBMETRIC = `!m s x:num->A.
    cauchy_in (submetric m s) x <=> (!n. x n IN s) /\ cauchy_in m x`;;

let CAUCHY_IN_CONST = `!m a:A. cauchy_in m (\n. a) <=> a IN mspace m`;;

let CONVERGENT_IMP_CAUCHY_IN = `!m x l:A. (!n. x n IN mspace m) /\ limit (mtopology m) x l sequentially
             ==> cauchy_in m x`;;

let MCOMPLETE_ALT = `!m:A metric.
        mcomplete m <=>
        !s. cauchy_in m s <=>
            (!n. s n IN mspace m) /\
            ?x. limit (mtopology m) s x sequentially`;;

let CAUCHY_IN_SUBSEQUENCE = `!m (x:num->A) r.
        (!m n. m < n ==> r m < r n) /\ cauchy_in m x
        ==> cauchy_in m (x o r)`;;

let CAUCHY_IN_OFFSET = `!m a x:num->A.
        (!n. n < a ==> x n IN mspace m) /\ cauchy_in m (\n. x(a + n))
        ==> cauchy_in m x`;;

let CAUCHY_IN_CONVERGENT_SUBSEQUENCE = `!m r a x:num->A.
        cauchy_in m x /\
        (!m n. m < n ==> r m < r n) /\
        limit (mtopology m) (x o r) a sequentially
        ==> limit (mtopology m) x a sequentially`;;

let CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE = `!m s:A->bool. closed_in (mtopology m) s /\ mcomplete m
                 ==> mcomplete (submetric m s)`;;

let SEQUENTIALLY_CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE = `!m s:A->bool.
     mcomplete m /\
     (!x l. (!n. x n IN s) /\ limit (mtopology m) x l sequentially ==> l IN s)
            ==> mcomplete (submetric m s)`;;

let CAUCHY_IN_INTERLEAVING_GEN = `!m x y:num->A.
        cauchy_in m (\n. if EVEN n then x(n DIV 2) else y(n DIV 2)) <=>
        cauchy_in m x /\ cauchy_in m y /\
        limit euclideanreal (\n. mdist m (x n,y n)) (&0) sequentially`;;

let CAUCHY_IN_INTERLEAVING = `!m x a:A.
         cauchy_in m (\n. if EVEN n then x(n DIV 2) else a) <=>
         (!n. x n IN mspace m) /\ limit (mtopology m) x a sequentially`;;

let MCOMPLETE_NEST = `!m:A metric.
      mcomplete m <=>
      !c. (!n. closed_in (mtopology m) (c n)) /\
          (!n. ~(c n = {})) /\
          (!m n. m <= n ==> c n SUBSET c m) /\
          (!e. &0 < e ==> ?n a. c n SUBSET mcball m (a,e))
          ==> ~(INTERS {c n | n IN (:num)} = {})`;;

let MCOMPLETE_NEST_SING = `!m:A metric.
      mcomplete m <=>
      !c. (!n. closed_in (mtopology m) (c n)) /\
          (!n. ~(c n = {})) /\
          (!m n. m <= n ==> c n SUBSET c m) /\
          (!e. &0 < e ==> ?n a. c n SUBSET mcball m (a,e))
          ==> ?l. l IN mspace m /\ INTERS {c n | n IN (:num)} = {l}`;;

let MCOMPLETE_FIP = `!m:A metric.
        mcomplete m <=>
        !f. (!c. c IN f ==> closed_in (mtopology m) c) /\
            (!e. &0 < e ==> ?c a. c IN f /\ c SUBSET mcball m (a,e)) /\
            (!f'. FINITE f' /\ f' SUBSET f ==> ~(INTERS f' = {}))
            ==> ~(INTERS f = {})`;;

let MCOMPLETE_FIP_SING = `!m:A metric.
        mcomplete m <=>
        !f. (!c. c IN f ==> closed_in (mtopology m) c) /\
            (!e. &0 < e ==> ?c a. c IN f /\ c SUBSET mcball m (a,e)) /\
            (!f'. FINITE f' /\ f' SUBSET f ==> ~(INTERS f' = {}))
            ==> ?l. l IN mspace m /\ INTERS f = {l}`;;

let MCOMPLETE_UNION = `!m s t:A->bool.
        mcomplete(submetric m s) /\ mcomplete(submetric m t)
        ==> mcomplete(submetric m (s UNION t))`;;

let MCOMPLETE_UNIONS = `!m s. FINITE s /\ (!t. t IN s ==> mcomplete(submetric m t))
         ==> mcomplete(submetric m (UNIONS s))`;;

let MCOMPLETE_INTERS = `!m s:(A->bool)->bool.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> mcomplete(submetric m t))
        ==> mcomplete(submetric m (INTERS s))`;;

let MCOMPLETE_INTER = `!m s t:A->bool.
        mcomplete(submetric m s) /\ mcomplete(submetric m t)
        ==> mcomplete(submetric m (s INTER t))`;;

(* ------------------------------------------------------------------------- *)
(* Totally bounded subsets of metric spaces.                                 *)
(* ------------------------------------------------------------------------- *)

let totally_bounded_in = new_definition
 `totally_bounded_in m (s:A->bool) <=>
        !e. &0 < e
            ==> ?k. FINITE k /\ k SUBSET s /\
                    s SUBSET UNIONS { mball m (x,e) | x IN k}`;;

let TOTALLY_BOUNDED_IN_EMPTY = `!m:A metric. totally_bounded_in m {}`;;

let FINITE_IMP_TOTALLY_BOUNDED_IN = `!m s:A->bool. FINITE s /\ s SUBSET mspace m ==> totally_bounded_in m s`;;

let TOTALLY_BOUNDED_IN_IMP_SUBSET = `!m s:A->bool. totally_bounded_in m s ==> s SUBSET mspace m`;;

let TOTALLY_BOUNDED_IN_SING = `!m x:A. totally_bounded_in m {x} <=> x IN mspace m`;;

let TOTALLY_BOUNDED_IN_SEQUENTIALLY = `!m s:A->bool.
        totally_bounded_in m s <=>
        s SUBSET mspace m /\
        !x:num->A. (!n. x n IN s)
                   ==> ?r. (!m n. m < n ==> r m < r n) /\
                           cauchy_in m (x o r)`;;

let TOTALLY_BOUNDED_IN_SUBSET = `!m s t:A->bool.
     totally_bounded_in m s /\ t SUBSET s ==> totally_bounded_in m t`;;

let TOTALLY_BOUNDED_IN_UNION = `!m s t:A->bool.
        totally_bounded_in m s /\ totally_bounded_in m t
        ==> totally_bounded_in m (s UNION t)`;;

let TOTALLY_BOUNDED_IN_UNIONS = `!m f:(A->bool)->bool.
        FINITE f /\ (!s. s IN f ==> totally_bounded_in m s)
        ==> totally_bounded_in m (UNIONS f)`;;

let TOTALLY_BOUNDED_IN_IMP_MBOUNDED = `!m s:A->bool. totally_bounded_in m s ==> mbounded m s`;;

let TOTALLY_BOUNDED_IN_SUBMETRIC = `!m s t:A->bool.
        totally_bounded_in m s /\ s SUBSET t
        ==> totally_bounded_in (submetric m t) s`;;

let TOTALLY_BOUNDED_IN_ABSOLUTE = `!m s:A->bool.
        totally_bounded_in (submetric m s) s <=> totally_bounded_in m s`;;

let TOTALLY_BOUNDED_IN_CLOSURE_OF = `!m s:A->bool.
        totally_bounded_in m s
        ==> totally_bounded_in m (mtopology m closure_of s)`;;

let TOTALLY_BOUNDED_IN_CLOSURE_OF_EQ = `!m s:A->bool.
        s SUBSET mspace m
        ==> (totally_bounded_in m (mtopology m closure_of s) <=>
             totally_bounded_in m s)`;;

let MBALL_INTER_DSEPARATED_SINGLETON = `!m:A metric s t d x y.
     t SUBSET s /\ s SUBSET mspace m /\ &0 < d /\
     (!a b. a IN t /\ b IN t /\ ~(a = b) ==> mdist m (a,b) >= d) /\
     x IN mspace m /\ y IN mball m (x, d / &2) INTER t
     ==> mball m (x, d / &2) INTER t = {y}`;;

let TOTALLY_BOUNDED_IMP_DISCRETE_FINITE = `!m:A metric s t d.
     totally_bounded_in m s /\ t SUBSET s /\ &0 < d /\
     (!x y. x IN t /\ y IN t /\ ~(x = y) ==> mdist m (x,y) >= d)
     ==> FINITE t`;;

let TOTALLY_BOUNDED_IN_CAUCHY_SEQUENCE = `!m x:num->A.
        cauchy_in m x ==> totally_bounded_in m (IMAGE x (:num))`;;

let CAUCHY_IN_IMP_MBOUNDED = `!m:A metric x. cauchy_in m x ==> mbounded m {x i | i IN (:num)}`;;

(* ------------------------------------------------------------------------- *)
(* Compactness in metric spaces.                                             *)
(* ------------------------------------------------------------------------- *)

let BOLZANO_WEIERSTRASS_PROPERTY = `!m u s:A->bool.
      s SUBSET u /\ s SUBSET mspace m
      ==> ((!x. (!n:num. x n IN s)
                ==> ?l r. l IN u /\ (!m n. m < n ==> r m < r n) /\
                          limit (mtopology m) (x o r) l sequentially) <=>
           (!t. t SUBSET s /\ INFINITE t
                ==> ~(u INTER (mtopology m) derived_set_of t = {})))`;;

let COMPACT_IN_EQ_BOLZANO_WEIERSTRASS = `(!m s:A->bool.
        compact_in (mtopology m) s <=>
        s SUBSET mspace m /\
        !t. t SUBSET s /\ INFINITE t
            ==> ~(s INTER (mtopology m) derived_set_of t = {}))`
and COMPACT_IN_SEQUENTIALLY = `(!m s:A->bool.
        compact_in (mtopology m) s <=>
        s SUBSET mspace m /\
        !x. (!n:num. x n IN s)
            ==> ?l r. l IN s /\ (!m n. m < n ==> r m < r n) /\
                      limit (mtopology m) (x o r) l sequentially)`
and COMPACT_IN_IMP_TOTALLY_BOUNDED_IN_EXPLICIT = `(!m (s:A->bool) e.
        compact_in (mtopology m) s /\ &0 < e
        ==> ?k. FINITE k /\ k SUBSET s /\
                s SUBSET UNIONS { mball m (x,e) | x IN k})`
and LEBESGUE_NUMBER = `(!m (s:A->bool) U.
        compact_in (mtopology m) s /\
        (!u. u IN U ==> open_in (mtopology m) u) /\ s SUBSET UNIONS U
        ==> ?e. &0 < e /\
                !x. x IN s ==> ?u. u IN U /\ mball m (x,e) SUBSET u)`;;

let COMPACT_SPACE_SEQUENTIALLY = `!m:A metric.
        compact_space(mtopology m) <=>
        !x. (!n:num. x n IN mspace m)
            ==> ?l r. l IN mspace m /\
                      (!m n. m < n ==> r m < r n) /\
                      limit (mtopology m) (x o r) l sequentially`;;

let COMPACT_SPACE_EQ_BOLZANO_WEIERSTRASS = `!m:A metric.
        compact_space(mtopology m) <=>
        !s. s SUBSET mspace m /\ INFINITE s
            ==> ~(mtopology m derived_set_of s = {})`;;

let COMPACT_SPACE_NEST = `!m:A metric.
        compact_space(mtopology m) <=>
        !c. (!n. closed_in (mtopology m) (c n)) /\
            (!n. ~(c n = {})) /\
            (!m n. m <= n ==> c n SUBSET c m)
            ==> ~(INTERS {c n | n IN (:num)} = {})`;;

let COMPACT_IN_IMP_TOTALLY_BOUNDED_IN = `!m (s:A->bool). compact_in (mtopology m) s ==> totally_bounded_in m s`;;

let MCOMPLETE_DISCRETE_METRIC = `!s:A->bool. mcomplete (discrete_metric s)`;;

let COMPACT_SPACE_IMP_MCOMPLETE = `!m:A metric. compact_space(mtopology m) ==> mcomplete m`;;

let COMPACT_IN_IMP_MCOMPLETE = `!m s:A->bool. compact_in (mtopology m) s ==> mcomplete (submetric m s)`;;

let MCOMPLETE_IMP_CLOSED_IN = `!m s:A->bool.
       mcomplete(submetric m s) /\ s SUBSET mspace m
       ==> closed_in (mtopology m) s`;;

let CLOSED_IN_EQ_MCOMPLETE = `!m s:A->bool.
        mcomplete m
        ==> (closed_in (mtopology m) s <=>
             s SUBSET mspace m /\ mcomplete(submetric m s))`;;

let COMPACT_SPACE_EQ_MCOMPLETE_TOTALLY_BOUNDED_IN = `!m:A metric.
        compact_space(mtopology m) <=>
        mcomplete m /\ totally_bounded_in m (mspace m)`;;

let COMPACT_CLOSURE_OF_IMP_TOTALLY_BOUNDED_IN = `!m s:A->bool.
      s SUBSET mspace m /\ compact_in (mtopology m) (mtopology m closure_of s)
      ==> totally_bounded_in m s`;;

let TOTALLY_BOUNDED_IN_EQ_COMPACT_CLOSURE_OF = `!m s:A->bool.
        mcomplete m
        ==> (totally_bounded_in m s <=>
             s SUBSET mspace m /\
             compact_in (mtopology m) (mtopology m closure_of s))`;;

let COMPACT_CLOSURE_OF_EQ_BOLZANO_WEIERSTRASS = `!m s:A->bool.
        compact_in (mtopology m) (mtopology m closure_of s) <=>
        !t. INFINITE t /\ t SUBSET s /\ t SUBSET mspace m
            ==> ~(mtopology m derived_set_of t = {})`;;

let MCOMPLETE_REAL_EUCLIDEAN_METRIC = `mcomplete real_euclidean_metric`;;

let MCOMPLETE_SUBMETRIC_REAL_EUCLIDEAN_METRIC = `!s. mcomplete(submetric real_euclidean_metric s) <=>
       closed_in euclideanreal s`;;

let TOTALLY_BOUNDED_IN_DISCRETE_METRIC = `!u s:A->bool. totally_bounded_in (discrete_metric u) s <=>
                 FINITE s /\ s SUBSET u`;;

let DERIVED_SET_OF_INFINITE_OPEN_IN_METRIC = `!m s:A->bool.
        mtopology m derived_set_of s =
        {x | x IN mspace m /\
             !u. x IN u /\ open_in (mtopology m) u ==> INFINITE(s INTER u)}`;;

let DERIVED_SET_OF_INFINITE_MBALL = `(!m s:A->bool.
        mtopology m derived_set_of s =
        {x | x IN mspace m /\
             !e. &0 < e ==> INFINITE(s INTER mball m (x,e))})`
and DERIVED_SET_OF_INFINITE_MCBALL = `(!m s:A->bool.
        mtopology m derived_set_of s =
        {x | x IN mspace m /\
             !e. &0 < e ==> INFINITE(s INTER mcball m (x,e))})`;;

(* ------------------------------------------------------------------------- *)
(* Pointwise continuity in topological spaces.                               *)
(* ------------------------------------------------------------------------- *)

let topcontinuous_at = new_definition
  `!top top' f:A->B x.
     topcontinuous_at top top' f x <=>
     x IN topspace top /\
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!v. open_in top' v /\ f x IN v
          ==> (?u. open_in top u /\ x IN u /\ (!y. y IN u ==> f y IN v)))`;;

let TOPCONTINUOUS_AT_ATPOINTOF = `!top top' f:A->B x.
        topcontinuous_at top top' f x <=>
        x IN topspace top /\
        (!x. x IN topspace top ==> f x IN topspace top') /\
        limit top' f (f x) (atpointof top x)`;;

let CONTINUOUS_MAP_EQ_TOPCONTINUOUS_AT = `!top top' f:A->B.
     continuous_map (top,top')  f <=>
     (!x. x IN topspace top ==> topcontinuous_at top top' f x)`;;

let CONTINUOUS_MAP_ATPOINTOF = `!top top' f:A->B.
        continuous_map (top,top') f <=>
        !x. x IN topspace top ==> limit top' f (f x) (atpointof top x)`;;

let LIMIT_CONTINUOUS_MAP = `!top top' (f:A->B) a b.
        continuous_map(top,top') f /\ a IN topspace top /\ f a = b
        ==> limit top' f b (atpointof top a)`;;

let LIMIT_CONTINUOUS_MAP_WITHIN = `!top top' (f:A->B) a b.
        continuous_map(subtopology top s,top') f /\
        a IN s /\ a IN topspace top /\ f a = b
        ==> limit top' f b (atpointof top a within s)`;;

(* ------------------------------------------------------------------------- *)
(* Continuity via bases/subbases, hence upper and lower semicontinuity.      *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MAP_INTO_TOPOLOGY_BASE = `!top top' b f:A->B.
        open_in top' = ARBITRARY UNION_OF b /\
        (!x. x IN topspace top ==> f x IN topspace top') /\
        (!u. u IN b ==> open_in top {x | x IN topspace top /\ f x IN u})
        ==> continuous_map(top,top') f`;;

let CONTINUOUS_MAP_INTO_TOPOLOGY_BASE_EQ = `!top top' b f:A->B.
      open_in top' = ARBITRARY UNION_OF b
      ==> (continuous_map(top,top') f <=>
           (!x. x IN topspace top ==> f x IN topspace top') /\
           (!u. u IN b ==> open_in top {x | x IN topspace top /\ f x IN u}))`;;

let CONTINUOUS_MAP_INTO_TOPOLOGY_SUBBASE = `!top top' b u f:A->B.
        topology(ARBITRARY UNION_OF (FINITE INTERSECTION_OF b relative_to u)) =
        top' /\
        (!x. x IN topspace top ==> f x IN topspace top') /\
        (!u. u IN b ==> open_in top {x | x IN topspace top /\ f x IN u})
        ==> continuous_map(top,top') f`;;

let CONTINUOUS_MAP_INTO_TOPOLOGY_SUBBASE_EQ = `!top top' b u f:A->B.
      topology(ARBITRARY UNION_OF
                (FINITE INTERSECTION_OF b relative_to u)) = top'
      ==> (continuous_map(top,top') f <=>
           (!x. x IN topspace top ==> f x IN topspace top') /\
           (!u. u IN b ==> open_in top {x | x IN topspace top /\ f x IN u}))`;;

let CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LT_GEN = `!top u f:A->real.
         continuous_map (top,subtopology euclideanreal u) f <=>
         (!x. x IN topspace top ==> f x IN u) /\
         (!a. open_in top {x | x IN topspace top /\ f x > a}) /\
         (!a. open_in top {x | x IN topspace top /\ f x < a})`;;

let CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LT = `!top f:A->real.
         continuous_map (top,euclideanreal) f <=>
         (!a. open_in top {x | x IN topspace top /\ f x > a}) /\
         (!a. open_in top {x | x IN topspace top /\ f x < a})`;;

let CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LE_GEN = `!top u f:A->real.
         continuous_map (top,subtopology euclideanreal u) f <=>
         (!x. x IN topspace top ==> f x IN u) /\
         (!a. closed_in top {x | x IN topspace top /\ f x >= a}) /\
         (!a. closed_in top {x | x IN topspace top /\ f x <= a})`;;

let CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LE = `!top f:A->real.
         continuous_map (top,euclideanreal) f <=>
         (!a. closed_in top {x | x IN topspace top /\ f x >= a}) /\
         (!a. closed_in top {x | x IN topspace top /\ f x <= a})`;;

let CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LTE_GEN = `!top u f:A->real.
         continuous_map (top,subtopology euclideanreal u) f <=>
         (!x. x IN topspace top ==> f x IN u) /\
         (!a. open_in top {x | x IN topspace top /\ f x < a}) /\
         (!a. closed_in top {x | x IN topspace top /\ f x <= a})`;;

let CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LTE = `!top f:A->real.
         continuous_map (top,euclideanreal) f <=>
         (!a. open_in top {x | x IN topspace top /\ f x < a}) /\
         (!a. closed_in top {x | x IN topspace top /\ f x <= a})`;;

(* ------------------------------------------------------------------------- *)
(* Continuous functions on metric spaces.                                    *)
(* ------------------------------------------------------------------------- *)

let METRIC_CONTINUOUS_MAP = `!m m' f:A->B.
     continuous_map (mtopology m,mtopology m') f <=>
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!a e. &0 < e /\ a IN mspace m
            ==> (?d. &0 < d /\
                     (!x. x IN mspace m /\ mdist m (a,x) < d
                          ==> mdist m' (f a, f x) < e)))`;;

let CONTINUOUS_MAP_TO_METRIC = `!t m f:A->B.
     continuous_map (t,mtopology m) f <=>
     (!x. x IN topspace t
          ==> (!r. &0 < r
                   ==> (?u. open_in t u /\
                            x IN u /\
                            (!y. y IN u ==> f y IN mball m (f x,r)))))`;;

let CONTINUOUS_MAP_FROM_METRIC = `!m top f:A->B.
        continuous_map (mtopology m,top) f <=>
        IMAGE f (mspace m) SUBSET topspace top /\
        !a. a IN mspace m
            ==> !u. open_in top u /\ f(a) IN u
                    ==> ?d. &0 < d /\
                            !x. x IN mspace m /\ mdist m (a,x) < d
                                ==> f x IN u`;;

let CONTINUOUS_MAP_UNIFORM_LIMIT = `!net top m f:K->A->B g.
        ~trivial_limit net /\
        eventually (\n. continuous_map (top,mtopology m) (f n)) net /\
        (!e. &0 < e
             ==> eventually
                   (\n. !x. x IN topspace top
                            ==> g x IN mspace m /\ mdist m (f n x,g x) < e)
                 net)
        ==> continuous_map (top,mtopology m) g`;;

let CONTINUOUS_MAP_UNIFORM_LIMIT_ALT = `!net top m f:K->A->B g.
        ~trivial_limit net /\
        IMAGE g (topspace top) SUBSET mspace m /\
        eventually (\n. continuous_map (top,mtopology m) (f n)) net /\
        (!e. &0 < e
             ==> eventually
                   (\n. !x. x IN topspace top ==> mdist m (f n x,g x) < e)
                 net)
        ==> continuous_map (top,mtopology m) g`;;

let CONTINUOUS_MAP_UNIFORMLY_CAUCHY_LIMIT = `!top ms f:num->A->B.
      ~trivial_limit sequentially /\ mcomplete ms /\
      eventually (\n. continuous_map (top,mtopology ms) (f n)) sequentially /\
      (!e. &0 < e
           ==> ?N. !m n x. N <= m /\ N <= n /\ x IN topspace top
                           ==> mdist ms (f m x,f n x) < e)
      ==> ?g. continuous_map (top,mtopology ms) g /\
              !e. &0 < e
                  ==> eventually
                       (\n. !x. x IN topspace top
                                ==> mdist ms (f n x,g x) < e)
                       sequentially`;;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for continuous functions into the reals.               *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MAP_REAL_CONST = `!top. continuous_map (top,euclideanreal) (\x:A. c)`;;

let CONTINUOUS_MAP_REAL_MUL = `!top f g:A->real.
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g
        ==> continuous_map (top,euclideanreal) (\x. f x * g x)`;;

let CONTINUOUS_MAP_REAL_POW = `!top (f:A->real) n.
        continuous_map (top,euclideanreal) f
        ==> continuous_map (top,euclideanreal) (\x. f x pow n)`;;

let CONTINUOUS_MAP_REAL_LMUL = `!top c f:A->real.
        continuous_map (top,euclideanreal) f
        ==> continuous_map (top,euclideanreal) (\x. c * f x)`;;

let CONTINUOUS_MAP_REAL_LMUL_EQ = `!top c f:A->real.
        continuous_map (top,euclideanreal) (\x. c * f x) <=>
        c = &0 \/ continuous_map (top,euclideanreal) f`;;

let CONTINUOUS_MAP_REAL_RMUL = `!top c f:A->real.
        continuous_map (top,euclideanreal) f
        ==> continuous_map (top,euclideanreal) (\x. f x * c)`;;

let CONTINUOUS_MAP_REAL_RMUL_EQ = `!top c f:A->real.
        continuous_map (top,euclideanreal) (\x. f x * c) <=>
        c = &0 \/ continuous_map (top,euclideanreal) f`;;

let CONTINUOUS_MAP_REAL_NEG = `!top f:A->real.
        continuous_map (top,euclideanreal) f
        ==> continuous_map (top,euclideanreal) (\x. --(f x))`;;

let CONTINUOUS_MAP_REAL_NEG_EQ = `!top f:A->real.
        continuous_map (top,euclideanreal) (\x. --(f x)) <=>
        continuous_map (top,euclideanreal) f`;;

let CONTINUOUS_MAP_REAL_ADD = `!top f g:A->real.
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g
        ==> continuous_map (top,euclideanreal) (\x. f x + g x)`;;

let CONTINUOUS_MAP_REAL_SUB = `!top f g:A->real.
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g
        ==> continuous_map (top,euclideanreal) (\x. f x - g x)`;;

let CONTINUOUS_MAP_REAL_ABS = `!top f:A->real.
        continuous_map (top,euclideanreal) f
        ==> continuous_map (top,euclideanreal) (\x. abs(f x))`;;

let CONTINUOUS_MAP_REAL_MAX = `!top f g:A->real.
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g
        ==> continuous_map (top,euclideanreal) (\x. max (f x) (g x))`;;

let CONTINUOUS_MAP_REAL_MIN = `!top f g:A->real.
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g
        ==> continuous_map (top,euclideanreal) (\x. min (f x) (g x))`;;

let CONTINUOUS_MAP_SUM = `!top f:A->K->real k.
        FINITE k /\
        (!i. i IN k ==> continuous_map (top,euclideanreal) (\x. f x i))
        ==> continuous_map (top,euclideanreal) (\x. sum k (f x))`;;

let CONTINUOUS_MAP_REAL_PRODUCT = `!top f:A->K->real k.
        FINITE k /\
        (!i. i IN k ==> continuous_map (top,euclideanreal) (\x. f x i))
        ==> continuous_map (top,euclideanreal) (\x. product k (f x))`;;

let CONTINUOUS_MAP_REAL_INV = `!top f:A->real.
        continuous_map (top,euclideanreal) f /\
        (!x. x IN topspace top ==> ~(f x = &0))
        ==> continuous_map (top,euclideanreal) (\x. inv(f x))`;;

let CONTINUOUS_MAP_REAL_DIV = `!top f g:A->real.
        continuous_map (top,euclideanreal) f /\
        continuous_map (top,euclideanreal) g /\
        (!x. x IN topspace top ==> ~(g x = &0))
        ==> continuous_map (top,euclideanreal) (\x. f x / g x)`;;

let CONTINUOUS_MAP_INF = `!top f:A->K->real k.
        FINITE k /\
        (!i. i IN k ==> continuous_map (top,euclideanreal) (\x. f x i))
        ==> continuous_map (top,euclideanreal) (\x. inf {f x i | i IN k})`;;

let CONTINUOUS_MAP_SUP = `!top f:A->K->real k.
        FINITE k /\
        (!i. i IN k ==> continuous_map (top,euclideanreal) (\x. f x i))
        ==> continuous_map (top,euclideanreal) (\x. sup {f x i | i IN k})`;;

let CONTINUOUS_MAP_REAL_SHRINK = `continuous_map (euclideanreal,
                   subtopology euclideanreal (real_interval(--(&1),&1)))
                  (\x. x / (&1 + abs x))`;;

let CONTINUOUS_MAP_REAL_GROW = `continuous_map (subtopology euclideanreal (real_interval(--(&1),&1)),
                   euclideanreal)
                  (\x. x / (&1 - abs x))`;;

let HOMEOMORPHIC_MAPS_REAL_SHRINK = `homeomorphic_maps
     (euclideanreal,subtopology euclideanreal (real_interval(--(&1),&1)))
     ((\x. x / (&1 + abs x)),(\y. y / (&1 - abs y)))`;;

let CONTINUOUS_MAP_CASES_LE = `!top top' p q f (g:A->B).
        continuous_map (top,euclideanreal) p /\
        continuous_map (top,euclideanreal) q /\
        continuous_map
         (subtopology top {x | x IN topspace top /\ p x <= q x},top') f /\
        continuous_map
         (subtopology top {x | x IN topspace top /\ q x <= p x},top') g /\
        (!x. x IN topspace top /\ p x = q x ==> f x = g x)
        ==> continuous_map (top,top') (\x. if p x <= q x then f x else g x)`;;

let CONTINUOUS_MAP_CASES_LT = `!top top' p q f (g:A->B).
        continuous_map (top,euclideanreal) p /\
        continuous_map (top,euclideanreal) q /\
        continuous_map
         (subtopology top {x | x IN topspace top /\ p x <= q x},top') f /\
        continuous_map
         (subtopology top {x | x IN topspace top /\ q x <= p x},top') g /\
        (!x. x IN topspace top /\ p x = q x ==> f x = g x)
        ==> continuous_map (top,top') (\x. if p x < q x then f x else g x)`;;

(* ------------------------------------------------------------------------- *)
(* Some elementary results on real limits, proved here for convenience.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("--->",(12,"right"));;

let tendsto_real_def = new_definition
  `(f ---> l) (net:A net) <=> limit euclideanreal f l net`;;

let reallim = new_definition
 `reallim net (f:A->real) = @l. (f ---> l) net`;;

(* Epsilon-delta characterization (named to avoid clash with TENDSTO_REAL
   in realanalysis.ml, which is the lift/drop bridge theorem) *)
let TENDSTO_REAL_EPS_DELTA = `!(f:A->real) l net.
     (f ---> l) net <=>
     !e. &0 < e ==> eventually (\x. abs(f x - l) < e) net`;;

let REALLIM_CONST = `!net:A net a. ((\x. a) ---> a) net`;;

let REALLIM_SUB = `!net (f:A->real) g l m.
     (f ---> l) net /\ (g ---> m) net
     ==> ((\x. f x - g x) ---> l - m) net`;;

let REALLIM_UBOUND = `!net (f:A->real) l b.
     (f ---> l) net /\ ~trivial_limit net /\
     eventually (\x. f x <= b) net
     ==> l <= b`;;

let REALLIM_LBOUND = `!net (f:A->real) l b.
     (f ---> l) net /\ ~trivial_limit net /\
     eventually (\x. b <= f x) net
     ==> b <= l`;;

let REALLIM_LE = `!net (f:A->real) g l m.
     (f ---> l) net /\ (g ---> m) net /\ ~trivial_limit net /\
     eventually (\x. f x <= g x) net
     ==> l <= m`;;

let REALLIM_SEQUENTIALLY = `!(f:num->real) l.
     (f ---> l) sequentially <=>
     !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n - l) < e`;;

(* ------------------------------------------------------------------------- *)
(* Similar elementary results for infinite series of reals.                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("real_sums",(12,"right"));;

let real_sums = new_definition
 `(f real_sums l) s <=>
    ((\n. sum (s INTER (0..n)) f) ---> l) sequentially`;;

let real_infsum = new_definition
 `real_infsum s f = @l. (f real_sums l) s`;;

let real_summable = new_definition
 `real_summable s f <=> ?l. (f real_sums l) s`;;

let REAL_SUMS_SUMMABLE = `!f l s. (f real_sums l) s ==> real_summable s f`;;

let REAL_SUMS_INFSUM = `!f s. (f real_sums (real_infsum s f)) s <=> real_summable s f`;;

let REAL_SERIES_FROM = `!f l k. (f real_sums l) (from k) <=>
           ((\n. sum(k..n) f) ---> l) sequentially`;;

(* Cauchy criterion for real summation *)
let REAL_SUMMABLE_CAUCHY = `!f s.
        real_summable s f <=>
        !e. &0 < e
            ==> ?N. !m n. m >= N ==> abs(sum(s INTER (m..n)) f) < e`;;

(* Comparison test *)
let REAL_SUMMABLE_COMPARISON = `!f g s. real_summable s g /\
           (?N. !n. n >= N /\ n IN s ==> abs(f n) <= g n)
           ==> real_summable s f`;;

let REAL_SERIES_LE = `!f g s y z.
     (f real_sums y) s /\ (g real_sums z) s /\
     (!i. i IN s ==> f i <= g i)
     ==> y <= z`;;

(* ------------------------------------------------------------------------- *)
(* Paths and path-connectedness.                                             *)
(* ------------------------------------------------------------------------- *)

let path_in = new_definition
 `path_in top (g:real->A) <=>
  continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) g`;;

let PATH_IN_COMPOSE = `!top top' f:A->B g:real->A.
        path_in top g /\ continuous_map(top,top') f ==> path_in top' (f o g)`;;

let PATH_IN_SUBTOPOLOGY = `!top s g:real->A.
        path_in (subtopology top s) g <=>
        path_in top g /\ (!x. x IN real_interval[&0,&1] ==> g x IN s)`;;

let PATH_IN_CONST = `!top a:A. path_in top (\x. a) <=> a IN topspace top`;;

let path_connected_space = new_definition
 `path_connected_space top <=>
        !x y:A. x IN topspace top /\ y IN topspace top
                ==> ?g. path_in top g /\ g(&0) = x /\ g(&1) = y`;;

let path_connected_in = new_definition
 `path_connected_in top (s:A->bool) <=>
  s SUBSET topspace top /\ path_connected_space(subtopology top s)`;;

let PATH_CONNECTED_IN_ABSOLUTE = `!top s:A->bool.
        path_connected_in (subtopology top s) s <=> path_connected_in top s`;;

let PATH_CONNECTED_IN_SUBSET_TOPSPACE = `!top s:A->bool. path_connected_in top s ==> s SUBSET topspace top`;;

let PATH_CONNECTED_IN_SUBTOPOLOGY = `!top s t:A->bool.
      path_connected_in (subtopology top s) t <=>
      path_connected_in top t /\ t SUBSET s`;;

let PATH_CONNECTED_IN = `!top s:A->bool.
        path_connected_in top s <=>
        s SUBSET topspace top /\
        !x y. x IN s /\ y IN s
              ==> ?g. path_in top g /\
                      IMAGE g (real_interval[&0,&1]) SUBSET s /\
                      g(&0) = x /\ g(&1) = y`;;

let PATH_CONNECTED_IN_TOPSPACE = `!top:A topology. path_connected_in top (topspace top) <=>
                    path_connected_space top`;;

let PATH_CONNECTED_IMP_CONNECTED_SPACE = `!top:A topology. path_connected_space top ==> connected_space top`;;

let PATH_CONNECTED_IN_IMP_CONNECTED_IN = `!top s:A->bool. path_connected_in top s ==> connected_in top s`;;

let PATH_CONNECTED_SPACE_TOPSPACE_EMPTY = `!top:A topology. topspace top = {} ==> path_connected_space top`;;

let PATH_CONNECTED_IN_EMPTY = `!top:A topology. path_connected_in top {}`;;

let PATH_CONNECTED_IN_SING = `!top a:A. path_connected_in top {a} <=> a IN topspace top`;;

let PATH_CONNECTED_IN_CONTINUOUS_MAP_IMAGE = `!f:A->B top top' s.
        continuous_map (top,top') f /\ path_connected_in top s
        ==> path_connected_in top' (IMAGE f s)`;;

let HOMEOMORPHIC_PATH_CONNECTED_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (path_connected_space top <=> path_connected_space top')`;;

let HOMEOMORPHIC_MAP_PATH_CONNECTEDNESS = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f /\ u SUBSET topspace top
        ==> (path_connected_in top' (IMAGE f u) <=> path_connected_in top u)`;;

let HOMEOMORPHIC_MAP_PATH_CONNECTEDNESS_EQ = `!(f:A->B) top top' u.
        homeomorphic_map(top,top') f
        ==> (path_connected_in top u <=>
             u SUBSET topspace top /\ path_connected_in top' (IMAGE f u))`;;

let PATH_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE = `!top top' (q:A->B).
        quotient_map(top,top') q /\ path_connected_space top
        ==> path_connected_space top'`;;

let PATH_CONNECTED_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ path_connected_space top
        ==> path_connected_space top'`;;

let PATH_CONNECTED_IN_EUCLIDEANREAL_INTERVAL = `(!a b. path_connected_in euclideanreal (real_interval[a,b])) /\
   (!a b. path_connected_in euclideanreal (real_interval(a,b)))`;;

let PATH_CONNECTED_IN_PATH_IMAGE = `!top g:real->A.
     path_in top g ==> path_connected_in top (IMAGE g (real_interval[&0,&1]))`;;

let CONNECTED_IN_PATH_IMAGE = `!top g:real->A.
     path_in top g ==> connected_in top (IMAGE g (real_interval[&0,&1]))`;;

let COMPACT_IN_PATH_IMAGE = `!top g:real->A.
     path_in top g ==> compact_in top (IMAGE g (real_interval[&0,&1]))`;;

let PATH_START_IN_TOPSPACE = `!top g:real->A. path_in top g ==> g(&0) IN topspace top`;;

let PATH_FINISH_IN_TOPSPACE = `!top g:real->A. path_in top g ==> g(&1) IN topspace top`;;

let PATH_IMAGE_SUBSET_TOPSPACE = `!top g:real->A.
    path_in top g ==> IMAGE g (real_interval[&0,&1]) SUBSET topspace top`;;

let PATH_CONNECTED_SPACE_SUBCONNECTED = `!top. path_connected_space top <=>
         !x y:A. x IN topspace top /\ y IN topspace top
                 ==> ?s. path_connected_in top s /\
                         x IN s /\
                         y IN s`;;

let PATH_CONNECTED_IN_EUCLIDEANREAL = `!s. path_connected_in euclideanreal s <=> is_realinterval s`;;

let PATH_CONNECTED_IN_DISCRETE_TOPOLOGY = `!u s:A->bool.
       path_connected_in (discrete_topology u) s <=>
       s SUBSET u /\ ?a. s SUBSET {a}`;;

let PATH_CONNECTED_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool.
        path_connected_space (discrete_topology u) <=>
        ?a. u SUBSET {a}`;;

let PATH_CONNECTED_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        path_connected_space(prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        path_connected_space top1 /\ path_connected_space top2`;;

let PATH_CONNECTED_IN_CROSS = `!top1 top2 s:A->bool t:B->bool.
        path_connected_in (prod_topology top1 top2) (s CROSS t) <=>
        s = {} \/ t = {} \/
        path_connected_in top1 s /\ path_connected_in top2 t`;;

let PATH_CONNECTED_SPACE_PRODUCT_TOPOLOGY = `!tops:K->A topology k.
        path_connected_space(product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        !i. i IN k ==> path_connected_space(tops i)`;;

let PATH_CONNECTED_IN_CARTESIAN_PRODUCT = `!tops:K->A topology s k.
        path_connected_in (product_topology k tops) (cartesian_product k s) <=>
        cartesian_product k s = {} \/
        !i. i IN k ==> path_connected_in (tops i) (s i)`;;

(* ------------------------------------------------------------------------- *)
(* Path components.                                                          *)
(* ------------------------------------------------------------------------- *)

let path_component_of = new_definition
 `path_component_of top x y <=>
        ?g. path_in top g /\ g(&0) = x /\ g(&1) = y`;;

let path_components_of = new_definition
 `path_components_of top = {path_component_of top x |x| x IN topspace top}`;;

let PATH_COMPONENT_IN_TOPSPACE = `!top x y:A.
        path_component_of top x y ==> x IN topspace top /\ y IN topspace top`;;

let PATH_COMPONENT_OF_REFL = `!top x:A. path_component_of top x x <=> x IN topspace top`;;

let PATH_COMPONENT_OF_SYM = `!top x y:A. path_component_of top x y <=> path_component_of top y x`;;

let PATH_COMPONENT_OF_TRANS = `!top x y z:A.
        path_component_of top x y /\ path_component_of top y z
        ==> path_component_of top x z`;;

let PATH_COMPONENT_OF_SUBTOPOLOGY = `!top s x y:A.
        path_component_of (subtopology top s) x y
        ==> path_component_of top x y`;;

let PATH_COMPONENT_OF_MONO = `!top s t x y:A.
        path_component_of (subtopology top s) x y /\ s SUBSET t
        ==> path_component_of (subtopology top t) x y`;;

let PATH_COMPONENT_OF = `!top x y:A.
        path_component_of top x y <=>
        ?t. path_connected_in top t /\ x IN t /\ y IN t`;;

let PATH_COMPONENT_OF_SET = `!top x:A.
        path_component_of top x =
        {y | ?g. path_in top g /\ g(&0) = x /\ g(&1) = y}`;;

let PATH_COMPONENT_OF_SET_ALT = `!top x:A.
         path_component_of top x =
         {y | ?t. path_connected_in top t /\ x IN t /\ y IN t}`;;

let PATH_COMPONENT_OF_SUBTOPOLOGY_EQ = `!top u x:A.
      path_component_of (subtopology top u) x =
      path_component_of top x <=>
      path_component_of top x SUBSET u`;;

let PATH_COMPONENTS_OF_SUBTOPOLOGY = `!top u c:A->bool.
        c IN path_components_of top /\ c SUBSET u
        ==> c IN path_components_of (subtopology top u)`;;

let PATH_COMPONENT_OF_SUBSET_TOPSPACE = `!top x. (path_component_of top x) SUBSET topspace top`;;

let PATH_COMPONENT_OF_EQ_EMPTY = `!top x. path_component_of top x = {} <=> ~(x IN topspace top)`;;

let PATH_CONNECTED_SPACE_IFF_PATH_COMPONENT = `!top:A topology.
        path_connected_space top <=>
        !x y. x IN topspace top /\ y IN topspace top
              ==> path_component_of top x y`;;

let PATH_CONNECTED_SPACE_IMP_PATH_COMPONENT_OF = `!top a b:A.
        path_connected_space top /\ a IN topspace top /\ b IN topspace top
        ==> path_component_of top a b`;;

let PATH_CONNECTED_SPACE_PATH_COMPONENT_SET = `!top. path_connected_space top <=>
         !x:A. x IN topspace top ==> path_component_of top x = topspace top`;;

let PATH_COMPONENT_OF_MAXIMAL = `!top s x:A.
     path_connected_in top s /\ x IN s ==> s SUBSET (path_component_of top x)`;;

let PATH_COMPONENT_OF_EQUIV = `!top x y:A.
        path_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        path_component_of top x = path_component_of top y`;;

let PATH_COMPONENT_OF_DISJOINT = `!top x y:A.
        DISJOINT (path_component_of top x) (path_component_of top y) <=>
        ~(path_component_of top x y)`;;

let PATH_COMPONENT_OF_EQ = `!top x y:A.
        path_component_of top x = path_component_of top y <=>
        ~(x IN topspace top) /\ ~(y IN topspace top) \/
        x IN topspace top /\ y IN topspace top /\ path_component_of top x y`;;

let PATH_CONNECTED_IN_PATH_COMPONENT_OF = `!top x:A. path_connected_in top (path_component_of top x)`;;

let UNIONS_PATH_COMPONENTS_OF = `!top:A topology. UNIONS (path_components_of top) = topspace top`;;

let PATH_COMPONENTS_OF_MAXIMAL = `!top s c:A->bool.
        c IN path_components_of top /\ path_connected_in top s /\ ~DISJOINT c s
        ==> s SUBSET c`;;

let PAIRWISE_DISJOINT_PATH_COMPONENTS_OF = `!top:A topology. pairwise DISJOINT (path_components_of top)`;;

let COMPLEMENT_PATH_COMPONENTS_OF_UNIONS = `!top c:A->bool.
        c IN path_components_of top
        ==> topspace top DIFF c = UNIONS (path_components_of top DELETE c)`;;

let NONEMPTY_PATH_COMPONENTS_OF = `!top c:A->bool. c IN path_components_of top ==> ~(c = {})`;;

let PATH_COMPONENTS_OF_SUBSET = `!top c:A->bool. c IN path_components_of top ==> c SUBSET topspace top`;;

let PATH_CONNECTED_IN_PATH_COMPONENTS_OF = `!top c:A->bool. c IN path_components_of top ==> path_connected_in top c`;;

let PATH_COMPONENT_IN_PATH_COMPONENTS_OF = `!top a:A.
        path_component_of top a IN path_components_of top <=>
        a IN topspace top`;;

let PATH_CONNECTED_IN_UNIONS = `!top u:(A->bool)->bool.
        (!s. s IN u ==> path_connected_in top s) /\ ~(INTERS u = {})
        ==> path_connected_in top (UNIONS u)`;;

let PATH_CONNECTED_IN_UNION = `!top s t:A->bool.
        path_connected_in top s /\ path_connected_in top t /\ ~(s INTER t = {})
        ==> path_connected_in top (s UNION t)`;;

let PATH_CONNECTED_SPACE_IFF_COMPONENTS_EQ = `!top:A topology.
        path_connected_space top <=>
        !c c'. c IN path_components_of top /\
               c' IN path_components_of top
               ==> c = c'`;;

let PATH_COMPONENTS_OF_EQ_EMPTY = `!top:A topology. path_components_of top = {} <=> topspace top = {}`;;

let PATH_COMPONENTS_OF_EMPTY_SPACE = `!top:A topology. topspace top = {} ==> path_components_of top = {}`;;

let PATH_COMPONENTS_OF_SUBSET_SING = `!top s:A->bool.
        path_components_of top SUBSET {s} <=>
        path_connected_space top /\ (topspace top = {} \/ topspace top = s)`;;

let PATH_CONNECTED_SPACE_IFF_COMPONENTS_SUBSET_SING = `!top:A topology.
        path_connected_space top <=> ?a. path_components_of top SUBSET {a}`;;

let PATH_COMPONENTS_OF_EQ_SING = `!top s:A->bool.
        path_components_of top = {s} <=>
        path_connected_space top /\ ~(topspace top = {}) /\ s = topspace top`;;

let PATH_COMPONENTS_OF_PATH_CONNECTED_SPACE = `!top:A topology.
        path_connected_space top
        ==> path_components_of top =
            if topspace top = {} then {} else {topspace top}`;;

let PATH_COMPONENT_SUBSET_CONNECTED_COMPONENT_OF = `!top x:A. path_component_of top x SUBSET connected_component_of top x`;;

let PATH_IMP_CONNECTED_COMPONENT_OF = `!top x y:A. path_component_of top x y ==> connected_component_of top x y`;;

let EXISTS_PATH_COMPONENT_OF_SUPERSET = `!top s:A->bool.
        path_connected_in top s /\ ~(topspace top = {})
        ==> ?c. c IN path_components_of top /\ s SUBSET c`;;

let PATH_COMPONENT_OF_EQ_OVERLAP = `!top x y:A.
      path_component_of top x = path_component_of top y <=>
      ~(x IN topspace top) /\ ~(y IN topspace top) \/
      ~(path_component_of top x INTER path_component_of top y = {})`;;

let PATH_COMPONENT_OF_NONOVERLAP = `!top x y:A.
     path_component_of top x INTER path_component_of top y = {} <=>
     ~(x IN topspace top) \/ ~(y IN topspace top) \/
     ~(path_component_of top x = path_component_of top y)`;;

let PATH_COMPONENT_OF_OVERLAP = `!top x y:A.
    ~(path_component_of top x INTER path_component_of top y = {}) <=>
    x IN topspace top /\ y IN topspace top /\
    path_component_of top x = path_component_of top y`;;

let PATH_COMPONENTS_OF_DISJOINT = `!top c c'.
        c IN path_components_of top /\ c' IN path_components_of top
        ==> (DISJOINT c c' <=> ~(c = c'))`;;

let PATH_COMPONENTS_OF_OVERLAP = `!top c c'.
        c IN path_components_of top /\ c' IN path_components_of top
        ==> (~(c INTER c' = {}) <=> c = c')`;;

let CARD_LE_PATH_COMPONENTS_OF_TOPSPACE = `!top:A topology. path_components_of top <=_c topspace top`;;

let FINITE_PATH_COMPONENTS_OF_FINITE = `!top:A topology.
        FINITE(topspace top) ==> FINITE(path_components_of top)`;;

let PATH_COMPONENT_OF_UNIQUE = `!top c x:A.
        x IN c /\ path_connected_in top c /\
        (!c'. x IN c' /\ path_connected_in top c' ==> c' SUBSET c)
        ==> path_component_of top x = c`;;

let PATH_COMPONENT_OF_DISCRETE_TOPOLOGY = `!u x:A. path_component_of (discrete_topology u) x =
           if x IN u then {x} else {}`;;

let PATH_COMPONENTS_OF_DISCRETE_TOPOLOGY = `!u:A->bool.
        path_components_of (discrete_topology u) = {{x} | x IN u}`;;

let PATH_COMPONENT_OF_CONTINUOUS_IMAGE = `!top top' (f:A->B) x y.
        continuous_map(top,top') f /\
        path_component_of top x y
        ==> path_component_of top' (f x) (f y)`;;

let HOMEOMORPHIC_MAP_PATH_COMPONENT_OF = `!(f:A->B) top top' x.
        homeomorphic_map(top,top') f /\ x IN topspace top
        ==> path_component_of top' (f x) =
            IMAGE f (path_component_of top x)`;;

let HOMEOMORPHIC_MAP_PATH_COMPONENTS_OF = `!(f:A->B) top top'.
      homeomorphic_map(top,top') f
      ==> path_components_of top' = IMAGE (IMAGE f) (path_components_of top)`;;

let PATH_COMPONENT_OF_PAIR = `!top1 top2 (x:A) (y:B).
        path_component_of (prod_topology top1 top2) (x,y) =
        path_component_of top1 x CROSS path_component_of top2 y`;;

let PATH_COMPONENTS_OF_PROD_TOPOLOGY = `!(top1:A topology) (top2:B topology).
        path_components_of (prod_topology top1 top2) =
        {c1 CROSS c2 | c1 IN path_components_of top1 /\
                       c2 IN path_components_of top2}`;;

let PATH_COMPONENT_OF_PRODUCT_TOPOLOGY = `!k (tops:K->A topology) x.
        path_component_of (product_topology k tops) x =
        if EXTENSIONAL k x
        then cartesian_product k (\i. path_component_of (tops i) (x i))
        else {}`;;

let PATH_COMPONENTS_OF_PRODUCT_TOPOLOGY = `!k (tops:K->A topology).
        path_components_of (product_topology k tops) =
        { cartesian_product k c |c|
          !i. i IN k ==> c i IN path_components_of(tops i)}`;;

(* ------------------------------------------------------------------------- *)
(* Special characterizations of classes of functions into and out of R.      *)
(* ------------------------------------------------------------------------- *)

let EMBEDDING_MAP_INTO_EUCLIDEANREAL = `!top f:A->real.
        path_connected_space top
        ==> (embedding_map(top,euclideanreal) f <=>
             continuous_map(top,euclideanreal) f /\
             !x y. x IN topspace top /\ y IN topspace top /\ f x = f y
                   ==> x = y)`;;

let MONOTONE_MAP_INTO_EUCLIDEANREAL_ALT = `!top (f:A->real).
        continuous_map(top,euclideanreal) f
        ==> ((!k. is_realinterval k
                  ==> connected_in top {x | x IN topspace top /\ f x IN k}) <=>
             connected_space top /\ monotone_map(top,euclideanreal) f)`;;

let MONOTONE_MAP_INTO_EUCLIDEANREAL = `!top (f:A->real).
        connected_space top /\ continuous_map(top,euclideanreal) f
        ==> (monotone_map(top,euclideanreal) f <=>
             !k. is_realinterval k
                  ==> connected_in top {x | x IN topspace top /\ f x IN k})`;;

let MONOTONE_MAP_EUCLIDEANREAL_ALT = `!f s.
      (!c. is_realinterval c ==> is_realinterval {x | x IN s /\ f x IN c}) <=>
      is_realinterval s /\
      ((!x y. x IN s /\ y IN s /\ x <= y ==> f x <= f y) \/
       (!x y. x IN s /\ y IN s /\ x <= y ==> f y <= f x))`;;

let MONOTONE_MAP_EUCLIDEANREAL = `!f s. is_realinterval s /\
         continuous_map(subtopology euclideanreal s,euclideanreal) f
         ==> (monotone_map(subtopology euclideanreal s,euclideanreal) f <=>
              (!x y. x IN s /\ y IN s /\ x <= y ==> f x <= f y) \/
              (!x y. x IN s /\ y IN s /\ x <= y ==> f y <= f x))`;;

let INJECTIVE_EQ_MONOTONE_MAP = `!f s. is_realinterval s /\
         continuous_map(subtopology euclideanreal s,euclideanreal) f
         ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!x y. x IN s /\ y IN s /\ x < y ==> f x < f y) \/
              (!x y. x IN s /\ y IN s /\ x < y ==> f y < f x))`;;

let INJECTIVE_EQ_REAL_OPEN_MAP_EUCLIDEANREAL = `!f s. is_realinterval s /\
         continuous_map(subtopology euclideanreal s,euclideanreal) f
         ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              !u. real_open u /\ u SUBSET s ==> real_open(IMAGE f u))`;;

(* ------------------------------------------------------------------------- *)
(* Normal spaces including Urysohn's lemma and the Tietze extension theorem. *)
(* ------------------------------------------------------------------------- *)

let normal_space = new_definition
 `normal_space (top:A topology) <=>
        !s t. closed_in top s /\ closed_in top t /\ DISJOINT s t
              ==> ?u v. open_in top u /\ open_in top v /\
                        s SUBSET u /\ t SUBSET v /\
                        DISJOINT u v`;;

let NORMAL_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ normal_space top ==> normal_space top'`;;

let HOMEOMORPHIC_NORMAL_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (normal_space top <=> normal_space top')`;;

let NORMAL_SPACE = `!top:A topology.
      normal_space (top:A topology) <=>
      !s t. closed_in top s /\ closed_in top t /\ DISJOINT s t
            ==> ?u. open_in top u /\
                    s SUBSET u /\ DISJOINT t (top closure_of u)`;;

let NORMAL_SPACE_ALT = `!top:A topology.
      normal_space (top:A topology) <=>
      !s u. closed_in top s /\ open_in top u /\ s SUBSET u
            ==> ?v. open_in top v /\ s SUBSET v /\ top closure_of v SUBSET u`;;

let NORMAL_SPACE_CLOSURES = `!top:A topology.
        normal_space top <=>
        !s t. s SUBSET topspace top /\ t SUBSET topspace top /\
              DISJOINT (top closure_of s) (top closure_of t)
              ==> ?u v. open_in top u /\
                        open_in top v /\
                        s SUBSET u /\
                        t SUBSET v /\
                        DISJOINT u v`;;

let NORMAL_SPACE_DISJOINT_CLOSURES = `!top:A topology.
        normal_space top <=>
        !s t. closed_in top s /\ closed_in top t /\ DISJOINT s t
              ==> ?u v. open_in top u /\ open_in top v /\
                        s SUBSET u /\ t SUBSET v /\
                        DISJOINT (top closure_of u) (top closure_of v)`;;

let NORMAL_SPACE_DUAL = `!top:A topology.
        normal_space top <=>
        !u v. open_in top u /\ open_in top v /\ u UNION v = topspace top
              ==> ?s t. closed_in top s /\ closed_in top t /\
                        s SUBSET u /\ t SUBSET v /\ s UNION t = topspace top`;;

let NORMAL_T1_IMP_HAUSDORFF_SPACE = `!top:A topology.
        normal_space top /\ t1_space top ==> hausdorff_space top`;;

let NORMAL_T1_EQ_HAUSDORFF_SPACE = `!top:A topology.
        normal_space top ==> (t1_space top <=> hausdorff_space top)`;;

let NORMAL_T1_IMP_REGULAR_SPACE = `!top:A topology.
        normal_space top /\ t1_space top ==> regular_space top`;;

let COMPACT_HAUSDORFF_OR_REGULAR_IMP_NORMAL_SPACE = `!top:A topology.
        compact_space top /\ (hausdorff_space top \/ regular_space top)
        ==> normal_space top`;;

let NORMAL_SPACE_MTOPOLOGY = `!m:A metric. normal_space(mtopology m)`;;

let METRIZABLE_IMP_NORMAL_SPACE = `!top:A topology. metrizable_space top ==> normal_space top`;;

let NORMAL_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. normal_space(discrete_topology u)`;;

let NORMAL_SPACE_FSIGMAS = `!top:A topology.
        normal_space top <=>
        !s t. fsigma_in top s /\ fsigma_in top t /\ separated_in top s t
              ==> ?u v. open_in top u /\
                        open_in top v /\
                        s SUBSET u /\
                        t SUBSET v /\
                        DISJOINT u v`;;

let NORMAL_SPACE_FSIGMA_SUBTOPOLOGY = `!top s:A->bool.
        normal_space top /\ fsigma_in top s
        ==> normal_space(subtopology top s)`;;

let NORMAL_SPACE_CLOSED_SUBTOPOLOGY = `!top s:A->bool.
        normal_space top /\ closed_in top s
        ==> normal_space (subtopology top s)`;;

let NORMAL_SPACE_CONTINUOUS_CLOSED_MAP_IMAGE = `!top top' f:A->B.
        continuous_map (top,top') f /\ closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        normal_space top
        ==> normal_space top'`;;

let HEREDITARILY_NORMAL_SPACE_CONTINUOUS_CLOSED_MAP_IMAGE = `!top top' f:A->B.
        continuous_map (top,top') f /\
        closed_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        hereditarily normal_space top
        ==> hereditarily normal_space top'`;;

let HOMEOMORPHIC_HEREDITARILY_NORMAL_SPACE = `!(top:A topology) (top':B topology).
      top homeomorphic_space top'
      ==> (hereditarily normal_space top <=> hereditarily normal_space top')`;;

let HEREDITARILY_NORMAL_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ hereditarily normal_space top
        ==> hereditarily normal_space top'`;;

let URYSOHN_LEMMA = `!(top:A topology) s t a b.
        a <= b /\ normal_space top /\
        closed_in top s /\ closed_in top t /\ DISJOINT s t
        ==> ?f. continuous_map
                    (top,subtopology euclideanreal (real_interval[a,b])) f /\
                (!x. x IN s ==> f x = a) /\
                (!x. x IN t ==> f x = b)`;;

let URYSOHN_LEMMA_ALT = `!(top:A topology) s t a b.
        normal_space top /\ closed_in top s /\ closed_in top t /\ DISJOINT s t
        ==> ?f. continuous_map(top,euclideanreal) f /\
                (!x. x IN s ==> f x = a) /\
                (!x. x IN t ==> f x = b)`;;

let NORMAL_SPACE_EQ_URYSOHN_GEN_ALT = `!top:A topology a b.
     ~(a = b)
     ==> (normal_space top <=>
          !s t. closed_in top s /\ closed_in top t /\ DISJOINT s t
                ==> ?f. continuous_map (top,euclideanreal) f /\
                        (!x. x IN s ==> f x = a) /\
                        (!x. x IN t ==> f x = b))`;;

let NORMAL_SPACE_EQ_URYSOHN_GEN = `!top:A topology a b.
     a < b
     ==> (normal_space top <=>
          !s t. closed_in top s /\ closed_in top t /\ DISJOINT s t
                ==> ?f. continuous_map
                         (top,
                          subtopology euclideanreal (real_interval[a,b])) f /\
                        (!x. x IN s ==> f x = a) /\
                        (!x. x IN t ==> f x = b))`;;

let NORMAL_SPACE_EQ_URYSOHN_ALT = `!top:A topology.
     normal_space top <=>
     !s t. closed_in top s /\ closed_in top t /\ DISJOINT s t
           ==> ?f. continuous_map (top,euclideanreal) f /\
                   (!x. x IN s ==> f x = &0) /\
                   (!x. x IN t ==> f x = &1)`;;

let NORMAL_SPACE_EQ_URYSOHN = `!top:A topology.
     normal_space top <=>
     !s t. closed_in top s /\ closed_in top t /\ DISJOINT s t
           ==> ?f. continuous_map
                    (top,subtopology euclideanreal (real_interval[&0,&1])) f /\
                   (!x. x IN s ==> f x = &0) /\
                   (!x. x IN t ==> f x = &1)`;;

let TIETZE_EXTENSION_CLOSED_REAL_INTERVAL = `!top f:A->real s a b.
        normal_space top /\ closed_in top s /\ a <= b /\
        continuous_map (subtopology top s,euclideanreal) f /\
        (!x. x IN s ==> f x IN real_interval[a,b])
        ==> ?g. continuous_map(top,euclideanreal) g /\
                (!x. x IN topspace top ==> g x IN real_interval[a,b]) /\
                (!x. x IN s ==> g x = f x)`;;

let TIETZE_EXTENSION_REALINTERVAL = `!top f:A->real s t.
        normal_space top /\ closed_in top s /\
        is_realinterval t /\ ~(t = {}) /\
        continuous_map (subtopology top s,euclideanreal) f /\
        (!x. x IN s ==> f x IN t)
        ==> ?g. continuous_map(top,euclideanreal) g /\
                (!x. x IN topspace top ==> g x IN t) /\
                (!x. x IN s ==> g x = f x)`;;

let NORMAL_SPACE_EQ_TIETZE = `!top:A topology.
        normal_space top <=>
        !f s. closed_in top s /\
              continuous_map (subtopology top s,euclideanreal) f
              ==> ?g. continuous_map(top,euclideanreal) g /\
                      !x. x IN s ==> g x = f x`;;

let NORMAL_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
    normal_space top /\ perfect_map(top,top') f ==> normal_space top'`;;

let HAUSDORFF_NORMAL_SPACE_CLOSED_CONTINUOUS_MAP_IMAGE = `!top top' (f:A->B).
        normal_space top /\
        closed_map (top,top') f /\
        continuous_map (top,top') f /\
        IMAGE f (topspace top) = topspace top' /\
        t1_space top'
        ==> hausdorff_space top'`;;

let NORMAL_HAUSDORFF_SPACE_CLOSED_CONTINUOUS_MAP_IMAGE = `!top top' (f:A->B).
        normal_space top /\
        hausdorff_space top /\
        closed_map (top,top') f /\
        continuous_map (top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> normal_space top' /\ hausdorff_space top'`;;

let REGULAR_LINDELOF_IMP_NORMAL_SPACE = `!top:A topology.
        regular_space top /\ lindelof_space top ==> normal_space top`;;

(* ------------------------------------------------------------------------- *)
(* Hereditarily normal spaces.                                               *)
(* ------------------------------------------------------------------------- *)

let HEREDITARILY_NORMAL_SPACE = `(!top:A topology.
        hereditarily normal_space top <=>
        !u. open_in top u ==> normal_space(subtopology top u))`
and HEREDITARILY_NORMAL_SEPARATION = `(!top:A topology.
        hereditarily normal_space top <=>
        !s t. separated_in top s t
              ==> ?u v. open_in top u /\ open_in top v /\
                        s SUBSET u /\ t SUBSET v /\ DISJOINT u v)`;;

let METRIZABLE_IMP_HEREDITARILY_NORMAL_SPACE = `!top:A topology. metrizable_space top ==> hereditarily normal_space top`;;

let METRIZABLE_SPACE_SEPARATION = `!top s t:A->bool.
        metrizable_space top /\ separated_in top s t
        ==> ?u v. open_in top u /\ open_in top v /\
                  s SUBSET u /\ t SUBSET v /\ DISJOINT u v`;;

let HEREDITARILY_NORMAL_SEPARATION_PAIRWISE = `!top:A topology.
        hereditarily normal_space top <=>
        !u. FINITE u /\ (!s. s IN u ==> s SUBSET topspace top) /\
            pairwise (separated_in top) u
            ==> ?f. (!s. s IN u ==> open_in top (f s) /\ s SUBSET f s) /\
                    pairwise (\s t. DISJOINT (f s) (f t)) u`;;

let HEREDITARILY_NORMAL_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
    hereditarily normal_space top /\ perfect_map(top,top') f
    ==> hereditarily normal_space top'`;;

let REGULAR_SECOND_COUNTABLE_IMP_HEREDITARILY_NORMAL_SPACE = `!top:A topology.
        regular_space top /\ second_countable top
        ==> hereditarily normal_space top`;;

let REGULAR_SECOND_COUNTABLE_HAUSDORFF_IMP_NORMAL_SPACE = `!top:A topology.
        regular_space top /\ second_countable top /\ hausdorff_space top
        ==> normal_space top`;;

(* ------------------------------------------------------------------------- *)
(* Completely regular spaces.                                                *)
(* ------------------------------------------------------------------------- *)

let completely_regular_space = new_definition
 `completely_regular_space (top:A topology) <=>
    !s x. closed_in top s /\ x IN topspace top DIFF s
          ==> ?f. continuous_map
                   (top,subtopology euclideanreal (real_interval[&0,&1])) f /\
                  f(x) = &0 /\ !x. x IN s ==> f x = &1`;;

let HOMEOMORPHIC_COMPLETELY_REGULAR_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (completely_regular_space top <=> completely_regular_space top')`;;

let COMPLETELY_REGULAR_SPACE_ALT = `!top:A topology.
        completely_regular_space top <=>
        !s x. closed_in top s /\ x IN topspace top DIFF s
              ==> ?f. continuous_map (top,euclideanreal) f /\
                      f(x) = &0 /\ (!x. x IN s ==> f x = &1)`;;

let COMPLETELY_REGULAR_SPACE_GEN_ALT = `!(top:A topology) a b.
        ~(a = b)
        ==> (completely_regular_space top <=>
             !s x. closed_in top s /\ x IN topspace top DIFF s
                   ==> ?f. continuous_map (top,euclideanreal) f /\
                           f(x) = a /\ !x. x IN s ==> f x = b)`;;

let COMPLETELY_REGULAR_SPACE_GEN = `!(top:A topology) a b.
        a < b
        ==> (completely_regular_space top <=>
             !s x. closed_in top s /\ x IN topspace top DIFF s
                   ==> ?f. continuous_map
                              (top,subtopology euclideanreal
                                     (real_interval[a,b])) f /\
                           f(x) = a /\ !x. x IN s ==> f x = b)`;;

let NORMAL_IMP_COMPLETELY_REGULAR_SPACE_GEN = `!top:A topology.
        normal_space top /\
        (t1_space top \/ hausdorff_space top \/ regular_space top)
        ==> completely_regular_space top`;;

let NORMAL_IMP_COMPLETELY_REGULAR_SPACE = `!top:A topology.
        normal_space top /\ (hausdorff_space top \/ regular_space top)
        ==> completely_regular_space top`;;

let COMPLETELY_REGULAR_SPACE_MTOPOLOGY = `!m:A metric. completely_regular_space (mtopology m)`;;

let METRIZABLE_IMP_COMPLETELY_REGULAR_SPACE = `!top:A topology. metrizable_space top ==> completely_regular_space top`;;

let COMPLETELY_REGULAR_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. completely_regular_space(discrete_topology u)`;;

let COMPLETELY_REGULAR_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        completely_regular_space top
        ==> completely_regular_space (subtopology top s)`;;

let COMPLETELY_REGULAR_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ completely_regular_space top
        ==> completely_regular_space top'`;;

let COMPLETELY_REGULAR_IMP_REGULAR_SPACE = `!top:A topology. completely_regular_space top ==> regular_space top`;;

let LOCALLY_COMPACT_REGULAR_IMP_COMPLETELY_REGULAR_SPACE = `!top:A topology.
        locally_compact_space top /\ (hausdorff_space top \/ regular_space top)
        ==> completely_regular_space top`;;

let COMPLETELY_REGULAR_EQ_REGULAR_SPACE = `!top:A topology.
        locally_compact_space top
        ==> (completely_regular_space top <=> regular_space top)`;;

let COMPLETELY_REGULAR_SPACE_PROD_TOPOLOGY = `!(top1:A topology) (top2:B topology).
        completely_regular_space (prod_topology top1 top2) <=>
        topspace (prod_topology top1 top2) = {} \/
        completely_regular_space top1 /\ completely_regular_space top2`;;

let COMPLETELY_REGULAR_SPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) k.
        completely_regular_space (product_topology k tops) <=>
        topspace (product_topology k tops) = {} \/
        !i. i IN k ==> completely_regular_space (tops i)`;;

(* ------------------------------------------------------------------------- *)
(* Locally path-connected spaces.                                            *)
(* ------------------------------------------------------------------------- *)

let weakly_locally_path_connected_at = new_definition
 `weakly_locally_path_connected_at x top <=>
    neighbourhood_base_at x (path_connected_in top) top`;;

let locally_path_connected_at = new_definition
 `locally_path_connected_at x top <=>
    neighbourhood_base_at x
      (\u. open_in top u /\ path_connected_in top u ) top`;;

let locally_path_connected_space = new_definition
 `locally_path_connected_space top <=>
        neighbourhood_base_of (path_connected_in top) top`;;

let LOCALLY_PATH_CONNECTED_SPACE_ALT = `(!top:A topology.
        locally_path_connected_space top <=>
        neighbourhood_base_of
          (\u. open_in top u /\ path_connected_in top u) top)`
and LOCALLY_PATH_CONNECTED_SPACE_EQ_OPEN_PATH_COMPONENT_OF = `(!top:A topology.
        locally_path_connected_space top <=>
        !u x. open_in top u /\ x IN u
              ==> open_in top (path_component_of (subtopology top u) x))`;;

let LOCALLY_PATH_CONNECTED_SPACE = `!top:A topology.
        locally_path_connected_space top <=>
        !v x. open_in top v /\ x IN v
              ==> ?u. open_in top u /\
                      path_connected_in top u /\
                      x IN u /\ u SUBSET v`;;

let LOCALLY_PATH_CONNECTED_SPACE_OPEN_PATH_COMPONENTS = `!top:A topology.
        locally_path_connected_space top <=>
        !u c. open_in top u /\ c IN path_components_of(subtopology top u)
              ==> open_in top c`;;

let OPEN_IN_PATH_COMPONENT_OF_LOCALLY_PATH_CONNECTED_SPACE = `!top x:A. locally_path_connected_space top
             ==> open_in top (path_component_of top x)`;;

let OPEN_IN_PATH_COMPONENTS_OF_LOCALLY_PATH_CONNECTED_SPACE = `!top c:A->bool.
        locally_path_connected_space top /\ c IN path_components_of top
        ==> open_in top c`;;

let CLOSED_IN_PATH_COMPONENTS_OF_LOCALLY_PATH_CONNECTED_SPACE = `!top c:A->bool.
        locally_path_connected_space top /\ c IN path_components_of top
        ==> closed_in top c`;;

let CLOSED_IN_PATH_COMPONENT_OF_LOCALLY_PATH_CONNECTED_SPACE = `!top x:A. locally_path_connected_space top
             ==> closed_in top (path_component_of top x)`;;

let WEAKLY_LOCALLY_PATH_CONNECTED_AT = `!top x:A.
        weakly_locally_path_connected_at x top <=>
        !v. open_in top v /\ x IN v
            ==> ?u. open_in top u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?c. path_connected_in top c /\
                                c SUBSET v /\ x IN c /\ y IN c`;;

let LOCALLY_PATH_CONNECTED_SPACE_IM_KLEINEN = `!top:A topology.
        locally_path_connected_space top <=>
        !v x. open_in top v /\ x IN v
            ==> ?u. open_in top u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?c. path_connected_in top c /\
                                c SUBSET v /\ x IN c /\ y IN c`;;

let LOCALLY_PATH_CONNECTED_SPACE_OPEN_SUBSET = `!top s:A->bool.
        locally_path_connected_space top /\ open_in top s
        ==> locally_path_connected_space (subtopology top s)`;;

let LOCALLY_PATH_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE = `!top top' f:A->B.
        quotient_map(top,top') f /\ locally_path_connected_space top
        ==> locally_path_connected_space top'`;;

let HOMEOMORPHIC_LOCALLY_PATH_CONNECTED_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (locally_path_connected_space top <=>
             locally_path_connected_space top')`;;

let LOCALLY_PATH_CONNECTED_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map (top,top') r /\ locally_path_connected_space top
        ==> locally_path_connected_space top'`;;

let LOCALLY_PATH_CONNECTED_SPACE_EUCLIDEANREAL = `locally_path_connected_space euclideanreal`;;

let LOCALLY_PATH_CONNECTED_IS_REALINTERVAL = `!s. is_realinterval s
       ==> locally_path_connected_space(subtopology euclideanreal s)`;;

let LOCALLY_PATH_CONNECTED_REAL_INTERVAL = `(!a b. locally_path_connected_space
           (subtopology euclideanreal(real_interval[a,b]))) /\
   (!a b. locally_path_connected_space
           (subtopology euclideanreal(real_interval(a,b))))`;;

let LOCALLY_PATH_CONNECTED_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. locally_path_connected_space (discrete_topology u)`;;

let PATH_COMPONENT_EQ_CONNECTED_COMPONENT_OF = `!top x:A. locally_path_connected_space top
             ==> (path_component_of top x = connected_component_of top x)`;;

let PATH_COMPONENTS_EQ_CONNECTED_COMPONENTS_OF = `!top:A topology.
        locally_path_connected_space top
        ==> (path_components_of top = connected_components_of top)`;;

let PATH_CONNECTED_EQ_CONNECTED_SPACE = `!top. locally_path_connected_space top
         ==> (path_connected_space top <=> connected_space top)`;;

let LOCALLY_PATH_CONNECTED_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
      locally_path_connected_space (prod_topology top1 top2) <=>
      topspace (prod_topology top1 top2) = {} \/
      locally_path_connected_space top1 /\ locally_path_connected_space top2`;;

let LOCALLY_PATH_CONNECTED_SPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) k.
        locally_path_connected_space(product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        FINITE {i | i IN k /\ ~path_connected_space(tops i)} /\
        !i. i IN k ==> locally_path_connected_space(tops i)`;;

let LOCALLY_PATH_CONNECTED_SPACE_SUM_TOPOLOGY = `!k (top:K->A topology).
        locally_path_connected_space(sum_topology k top) <=>
        !i. i IN k ==> locally_path_connected_space(top i)`;;

(* ------------------------------------------------------------------------- *)
(* Locally connected spaces.                                                 *)
(* ------------------------------------------------------------------------- *)

let weakly_locally_connected_at = new_definition
 `weakly_locally_connected_at x top <=>
    neighbourhood_base_at x (connected_in top) top`;;

let locally_connected_at = new_definition
 `locally_connected_at x top <=>
    neighbourhood_base_at x
      (\u. open_in top u /\ connected_in top u ) top`;;

let locally_connected_space = new_definition
 `locally_connected_space top <=>
        neighbourhood_base_of (connected_in top) top`;;

let LOCALLY_CONNECTED_SPACE_ALT = `(!top:A topology.
        locally_connected_space top <=>
        neighbourhood_base_of
          (\u. open_in top u /\ connected_in top u) top)`
and LOCALLY_CONNECTED_SPACE_EQ_OPEN_CONNECTED_COMPONENT_OF = `(!top:A topology.
        locally_connected_space top <=>
        !u x. open_in top u /\ x IN u
              ==> open_in top (connected_component_of (subtopology top u) x))`;;

let LOCALLY_CONNECTED_SPACE = `!top:A topology.
        locally_connected_space top <=>
        !v x. open_in top v /\ x IN v
              ==> ?u. open_in top u /\
                      connected_in top u /\
                      x IN u /\ u SUBSET v`;;

let LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE = `!top: A topology.
        locally_path_connected_space top ==> locally_connected_space top`;;

let LOCALLY_CONNECTED_SPACE_OPEN_CONNECTED_COMPONENTS = `!top:A topology.
        locally_connected_space top <=>
        !u c. open_in top u /\ c IN connected_components_of(subtopology top u)
              ==> open_in top c`;;

let OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE = `!top x:A. locally_connected_space top
             ==> open_in top (connected_component_of top x)`;;

let OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE = `!top c:A->bool.
        locally_connected_space top /\ c IN connected_components_of top
        ==> open_in top c`;;

let WEAKLY_LOCALLY_CONNECTED_AT = `!top x:A.
        weakly_locally_connected_at x top <=>
        !v. open_in top v /\ x IN v
            ==> ?u. open_in top u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?c. connected_in top c /\
                                c SUBSET v /\ x IN c /\ y IN c`;;

let LOCALLY_CONNECTED_SPACE_IM_KLEINEN = `!top:A topology.
        locally_connected_space top <=>
        !v x. open_in top v /\ x IN v
            ==> ?u. open_in top u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?c. connected_in top c /\
                                c SUBSET v /\ x IN c /\ y IN c`;;

let LOCALLY_CONNECTED_SPACE_OPEN_SUBSET = `!top s:A->bool.
        locally_connected_space top /\ open_in top s
        ==> locally_connected_space (subtopology top s)`;;

let LOCALLY_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE = `!top top' f:A->B.
        quotient_map(top,top') f /\ locally_connected_space top
        ==> locally_connected_space top'`;;

let LOCALLY_CONNECTED_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map (top,top') r /\ locally_connected_space top
        ==> locally_connected_space top'`;;

let HOMEOMORPHIC_LOCALLY_CONNECTED_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (locally_connected_space top <=>
             locally_connected_space top')`;;

let LOCALLY_CONNECTED_SPACE_EUCLIDEANREAL = `locally_connected_space euclideanreal`;;

let LOCALLY_CONNECTED_IS_REALINTERVAL = `!s. is_realinterval s
       ==> locally_connected_space(subtopology euclideanreal s)`;;

let LOCALLY_CONNECTED_REAL_INTERVAL = `(!a b. locally_connected_space
           (subtopology euclideanreal(real_interval[a,b]))) /\
   (!a b. locally_connected_space
           (subtopology euclideanreal(real_interval(a,b))))`;;

let LOCALLY_CONNECTED_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. locally_connected_space (discrete_topology u)`;;

let LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_AT = `!top x:a. locally_path_connected_at x top ==> locally_connected_at x top`;;

let WEAKLY_LOCALLY_PATH_CONNECTED_IMP_WEAKLY_LOCALLY_CONNECTED_AT = `!top x:a. weakly_locally_path_connected_at x top
             ==> weakly_locally_connected_at x top`;;

let INTERIOR_OF_LOCALLY_CONNECTED_SUBSPACE_COMPONENT = `!top s c:A->bool.
        locally_connected_space top /\
        c IN connected_components_of (subtopology top s)
        ==> top interior_of c = c INTER top interior_of s`;;

let FRONTIER_OF_LOCALLY_CONNECTED_SUBSPACE_COMPONENT = `!top s c:A->bool.
        locally_connected_space top /\
        closed_in top s /\
        c IN connected_components_of (subtopology top s)
        ==> top frontier_of c = c INTER top frontier_of s`;;

let LOCALLY_CONNECTED_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
      locally_connected_space (prod_topology top1 top2) <=>
      topspace (prod_topology top1 top2) = {} \/
      locally_connected_space top1 /\ locally_connected_space top2`;;

let LOCALLY_CONNECTED_SPACE_PRODUCT_TOPOLOGY = `!(tops:K->A topology) k.
        locally_connected_space(product_topology k tops) <=>
        topspace(product_topology k tops) = {} \/
        FINITE {i | i IN k /\ ~connected_space(tops i)} /\
        !i. i IN k ==> locally_connected_space(tops i)`;;

let LOCALLY_CONNECTED_SPACE_SUM_TOPOLOGY = `!k (top:K->A topology).
        locally_connected_space(sum_topology k top) <=>
        !i. i IN k ==> locally_connected_space(top i)`;;

(* ------------------------------------------------------------------------- *)
(* Quasi-components.                                                         *)
(* ------------------------------------------------------------------------- *)

let quasi_component_of = new_definition
 `quasi_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        !t. closed_in top t /\ open_in top t ==> (x IN t <=> y IN t)`;;

let quasi_components_of = new_definition
 `quasi_components_of top =
    {quasi_component_of top x |x| x IN topspace top}`;;

let QUASI_COMPONENT_IN_TOPSPACE = `!top x y:A.
        quasi_component_of top x y
        ==> x IN topspace top /\ y IN topspace top`;;

let QUASI_COMPONENT_OF_REFL = `!top x:A. quasi_component_of top x x <=> x IN topspace top`;;

let QUASI_COMPONENT_OF_SYM = `!top x y:A.
    quasi_component_of top x y <=> quasi_component_of top y x`;;

let QUASI_COMPONENT_OF_TRANS = `!top x y z:A.
        quasi_component_of top x y /\ quasi_component_of top y z
        ==> quasi_component_of top x z`;;

let QUASI_COMPONENT_OF_SUBSET_TOPSPACE = `!top x. (quasi_component_of top x) SUBSET topspace top`;;

let QUASI_COMPONENT_OF_EQ_EMPTY = `!top x. quasi_component_of top x = {} <=> ~(x IN topspace top)`;;

let QUASI_COMPONENT_OF = `!top x y:A.
        quasi_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        !t. x IN t /\ closed_in top t /\ open_in top t ==> y IN t`;;

let QUASI_COMPONENT_OF_ALT = `!top x y:A.
        quasi_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        ~(?u v. open_in top u /\ open_in top v /\
                u UNION v = topspace top /\
                DISJOINT u v /\ x IN u /\ y IN v)`;;

let QUASI_COMPONENT_OF_SET = `!top x:A.
        quasi_component_of top x =
        if x IN topspace top
        then INTERS {t | closed_in top t /\ open_in top t /\ x IN t}
        else {}`;;

let QUASI_COMPONENT_OF_SEPARATED = `!top x y:A.
        quasi_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        ~(?u v. separated_in top u v /\ u UNION v = topspace top /\
                x IN u /\ y IN v)`;;

let QUASI_COMPONENT_OF_SUBTOPOLOGY = `!top s x y:A.
        quasi_component_of (subtopology top s) x y
        ==> quasi_component_of top x y`;;

let QUASI_COMPONENT_OF_MONO = `!top s t x y:A.
        quasi_component_of (subtopology top s) x y /\ s SUBSET t
        ==> quasi_component_of (subtopology top t) x y`;;

let QUASI_COMPONENT_OF_EQUIV = `!top x y:A.
        quasi_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        quasi_component_of top x = quasi_component_of top y`;;

let QUASI_COMPONENT_OF_DISJOINT = `!top x y:A.
        DISJOINT (quasi_component_of top x)
                 (quasi_component_of top y) <=>
        ~(quasi_component_of top x y)`;;

let QUASI_COMPONENT_OF_EQ = `!top x y:A.
        quasi_component_of top x = quasi_component_of top y <=>
        ~(x IN topspace top) /\ ~(y IN topspace top) \/
        x IN topspace top /\ y IN topspace top /\
        quasi_component_of top x y`;;

let UNIONS_QUASI_COMPONENTS_OF = `!top:A topology. UNIONS (quasi_components_of top) = topspace top`;;

let PAIRWISE_DISJOINT_QUASI_COMPONENTS_OF = `!top:A topology. pairwise DISJOINT (quasi_components_of top)`;;

let COMPLEMENT_QUASI_COMPONENTS_OF_UNIONS = `!top c:A->bool.
      c IN quasi_components_of top
      ==> topspace top DIFF c = UNIONS (quasi_components_of top DELETE c)`;;

let NONEMPTY_QUASI_COMPONENTS_OF = `!top c:A->bool. c IN quasi_components_of top ==> ~(c = {})`;;

let QUASI_COMPONENTS_OF_SUBSET = `!top c:A->bool. c IN quasi_components_of top ==> c SUBSET topspace top`;;

let QUASI_COMPONENT_IN_QUASI_COMPONENTS_OF = `!top a:A.
        quasi_component_of top a IN quasi_components_of top <=>
        a IN topspace top`;;

let QUASI_COMPONENTS_OF_EQ_EMPTY = `!top:A topology. quasi_components_of top = {} <=> topspace top = {}`;;

let QUASI_COMPONENTS_OF_EMPTY_SPACE = `!top:A topology. topspace top = {} ==> quasi_components_of top = {}`;;

let CLOSED_IN_QUASI_COMPONENT_OF = `!top x:A. closed_in top (quasi_component_of top x)`;;

let CLOSED_IN_QUASI_COMPONENTS_OF = `!top c:A->bool.
        c IN quasi_components_of top ==> closed_in top c`;;

let OPEN_IN_FINITE_QUASI_COMPONENTS = `!top c:A->bool.
        FINITE(quasi_components_of top) /\
        c IN quasi_components_of top
        ==> open_in top c`;;

let QUASI_COMPONENT_OF_EQ_OVERLAP = `!top x y:A.
      quasi_component_of top x = quasi_component_of top y <=>
      ~(x IN topspace top) /\ ~(y IN topspace top) \/
      ~(quasi_component_of top x INTER quasi_component_of top y = {})`;;

let QUASI_COMPONENT_OF_NONOVERLAP = `!top x y:A.
     quasi_component_of top x INTER quasi_component_of top y = {} <=>
     ~(x IN topspace top) \/ ~(y IN topspace top) \/
     ~(quasi_component_of top x = quasi_component_of top y)`;;

let QUASI_COMPONENT_OF_OVERLAP = `!top x y:A.
    ~(quasi_component_of top x INTER quasi_component_of top y = {}) <=>
    x IN topspace top /\ y IN topspace top /\
    quasi_component_of top x = quasi_component_of top y`;;

let QUASI_COMPONENTS_OF_DISJOINT = `!top c c'.
        c IN quasi_components_of top /\ c' IN quasi_components_of top
        ==> (DISJOINT c c' <=> ~(c = c'))`;;

let QUASI_COMPONENTS_OF_OVERLAP = `!top c c'.
        c IN quasi_components_of top /\ c' IN quasi_components_of top
        ==> (~(c INTER c' = {}) <=> c = c')`;;

let PAIRWISE_SEPARATED_QUASI_COMPONENTS_OF = `!top:A topology.
        pairwise (separated_in top) (quasi_components_of top)`;;

let CARD_LE_QUASI_COMPONENTS_OF_TOPSPACE = `!top:A topology. quasi_components_of top <=_c topspace top`;;

let FINITE_QUASI_COMPONENTS_OF_FINITE = `!top:A topology.
        FINITE(topspace top) ==> FINITE(quasi_components_of top)`;;

let CONNECTED_IMP_QUASI_COMPONENT_OF = `!top x y:A. connected_component_of top x y ==> quasi_component_of top x y`;;

let CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF = `!top x:A. connected_component_of top x SUBSET quasi_component_of top x`;;

let QUASI_COMPONENT_AS_CONNECTED_COMPONENT_UNIONS = `!top x:A.
        quasi_component_of top x =
        UNIONS {connected_component_of top y |y| quasi_component_of top x y}`;;

let QUASI_COMPONENTS_AS_CONNECTED_COMPONENTS_UNIONS = `!top c:A->bool.
        c IN quasi_components_of top
        ==> ?t. t SUBSET connected_components_of top /\ UNIONS t = c`;;

let PATH_IMP_QUASI_COMPONENT_OF = `!top x y:A. path_component_of top x y ==> quasi_component_of top x y`;;

let PATH_COMPONENT_SUBSET_QUASI_COMPONENT_OF = `!top x:A. path_component_of top x SUBSET quasi_component_of top x`;;

let CONNECTED_SPACE_IFF_QUASI_COMPONENT = `!top:A topology.
        connected_space top <=>
        !x y. x IN topspace top /\ y IN topspace top
              ==> quasi_component_of top x y`;;

let CONNECTED_SPACE_IMP_QUASI_COMPONENT_OF = `!top a b:A.
        connected_space top /\ a IN topspace top /\ b IN topspace top
        ==> quasi_component_of top a b`;;

let CONNECTED_SPACE_QUASI_COMPONENT_SET = `!top. connected_space top <=>
         !x:A. x IN topspace top
               ==> quasi_component_of top x = topspace top`;;

let CONNECTED_SPACE_IFF_QUASI_COMPONENTS_EQ = `!top:A topology.
        connected_space top <=>
        !c c'. c IN quasi_components_of top /\
               c' IN quasi_components_of top
               ==> c = c'`;;

let QUASI_COMPONENTS_OF_SUBSET_SING = `!top s:A->bool.
        quasi_components_of top SUBSET {s} <=>
        connected_space top /\ (topspace top = {} \/ topspace top = s)`;;

let CONNECTED_SPACE_IFF_QUASI_COMPONENTS_SUBSET_SING = `!top:A topology.
        connected_space top <=> ?a. quasi_components_of top SUBSET {a}`;;

let QUASI_COMPONENTS_OF_EQ_SING = `!top s:A->bool.
        quasi_components_of top = {s} <=>
        connected_space top /\ ~(topspace top = {}) /\ s = topspace top`;;

let QUASI_COMPONENTS_OF_CONNECTED_SPACE = `!top:A topology.
        connected_space top
        ==> quasi_components_of top =
            if topspace top = {} then {} else {topspace top}`;;

let SEPARATED_BETWEEN_SINGS = `!top x y:A.
        separated_between top {x} {y} <=>
        x IN topspace top /\ y IN topspace top /\
        ~(quasi_component_of top x y)`;;

let QUASI_COMPONENT_NONSEPARATED = `!top x y:A.
        quasi_component_of top x y <=>
        x IN topspace top /\ y IN topspace top /\
        ~(separated_between top {x} {y})`;;

let SEPARATED_BETWEEN_QUASI_COMPONENT_POINTWISE_LEFT = `!top c s:A->bool.
        c IN quasi_components_of top
        ==> (separated_between top c s <=>
             ?x. x IN c /\ separated_between top {x} s)`;;

let SEPARATED_BETWEEN_QUASI_COMPONENT_POINTWISE_RIGHT = `!top s c:A->bool.
        c IN quasi_components_of top
        ==> (separated_between top s c <=>
             ?x. x IN c /\ separated_between top s {x})`;;

let SEPARATED_BETWEEN_QUASI_COMPONENT_POINT = `!top c x:A.
        c IN quasi_components_of top
        ==> (separated_between top c {x} <=> x IN topspace top DIFF c)`;;

let SEPARATED_BETWEEN_POINT_QUASI_COMPONENT = `!top (x:A) c.
        c IN quasi_components_of top
        ==> (separated_between top {x} c <=> x IN topspace top DIFF c)`;;

let SEPARATED_BETWEEN_QUASI_COMPONENT_COMPACT = `!top c k:A->bool.
        c IN quasi_components_of top /\ compact_in top k
        ==> (separated_between top c k <=> DISJOINT c k)`;;

let SEPARATED_BETWEEN_COMPACT_QUASI_COMPONENT = `!top k c:A->bool.
        compact_in top k /\ c IN quasi_components_of top
        ==> (separated_between top k c <=> DISJOINT k c)`;;

let SEPARATED_BETWEEN_QUASI_COMPONENTS = `!top c c':A->bool.
        c IN quasi_components_of top /\ c' IN quasi_components_of top
        ==> (separated_between top c c' <=> DISJOINT c c')`;;

let QUASI_EQ_CONNECTED_COMPONENT_OF_EQ = `!top x:A. quasi_component_of top x = connected_component_of top x <=>
             connected_in top (quasi_component_of top x)`;;

let CONNECTED_QUASI_COMPONENT_OF = `!top c:A->bool.
        c IN quasi_components_of top
        ==> (c IN connected_components_of top <=> connected_in top c)`;;

let QUASI_COMPONENT_OF_CLOPEN_CASES = `!top c t:A->bool.
        c IN quasi_components_of top /\ closed_in top t /\ open_in top t
        ==> c SUBSET t \/ DISJOINT c t`;;

let QUASI_COMPONENTS_OF_SET = `!top c:A->bool.
        c IN quasi_components_of top
        ==> INTERS {t | closed_in top t /\ open_in top t /\ c SUBSET t} = c`;;

let OPEN_QUASI_EQ_CONNECTED_COMPONENTS_OF = `!top c:A->bool.
        open_in top c
        ==> (c IN quasi_components_of top <=>
             c IN connected_components_of top)`;;

let QUASI_COMPONENT_OF_CONTINUOUS_IMAGE = `!top top' (f:A->B) x y.
        continuous_map(top,top') f /\
        quasi_component_of top x y
        ==> quasi_component_of top' (f x) (f y)`;;

let QUASI_COMPONENT_OF_DISCRETE_TOPOLOGY = `!u x:A. quasi_component_of (discrete_topology u) x =
           if x IN u then {x} else {}`;;

let QUASI_COMPONENTS_OF_DISCRETE_TOPOLOGY = `!u:A->bool.
        quasi_components_of (discrete_topology u) = {{x} | x IN u}`;;

let HOMEOMORPHIC_MAP_QUASI_COMPONENT_OF = `!(f:A->B) top top' x.
        homeomorphic_map(top,top') f /\ x IN topspace top
        ==> quasi_component_of top' (f x) =
            IMAGE f (quasi_component_of top x)`;;

let HOMEOMORPHIC_MAP_QUASI_COMPONENTS_OF = `!(f:A->B) top top'.
      homeomorphic_map(top,top') f
      ==> quasi_components_of top' =
          IMAGE (IMAGE f) (quasi_components_of top)`;;

let OPEN_IN_QUASI_COMPONENT_OF_LOCALLY_CONNECTED_SPACE = `!top x:A.
        locally_connected_space top
        ==> open_in top (quasi_component_of top x)`;;

let OPEN_IN_QUASI_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE = `!top c:A->bool.
        locally_connected_space top /\ c IN quasi_components_of top
        ==> open_in top c`;;

let QUASI_EQ_CONNECTED_COMPONENTS_OF_ALT = `!top:A topology.
        quasi_components_of top = connected_components_of top <=>
        !c. c IN quasi_components_of top ==> connected_in top c`;;

let CONNECTED_SUBSET_QUASI_COMPONENTS_OF_POINTWISE = `!top:A topology.
        connected_components_of top SUBSET quasi_components_of top <=>
        !x. x IN topspace top
            ==> quasi_component_of top x = connected_component_of top x`;;

let QUASI_SUBSET_CONNECTED_COMPONENTS_OF_POINTWISE = `!top:A topology.
        quasi_components_of top SUBSET connected_components_of top <=>
        !x. x IN topspace top
            ==> quasi_component_of top x = connected_component_of top x`;;

let QUASI_EQ_CONNECTED_COMPONENTS_OF_POINTWISE = `!top:A topology.
        quasi_components_of top = connected_components_of top <=>
        !x. x IN topspace top
            ==> quasi_component_of top x = connected_component_of top x`;;

let QUASI_EQ_CONNECTED_COMPONENTS_OF_POINTWISE_ALT = `!top:A topology.
        quasi_components_of top = connected_components_of top <=>
        !x. quasi_component_of top x = connected_component_of top x`;;

let QUASI_EQ_CONNECTED_COMPONENTS_OF_INCLUSION = `!top:A topology.
        quasi_components_of top = connected_components_of top <=>
        connected_components_of top SUBSET quasi_components_of top \/
        quasi_components_of top SUBSET connected_components_of top`;;

let QUASI_EQ_CONNECTED_COMPONENTS_OF = `!top:A topology.
      FINITE(connected_components_of top) \/
      FINITE(quasi_components_of top) \/
      locally_connected_space top \/
      compact_space top /\
      (hausdorff_space top \/ regular_space top \/ normal_space top)
      ==> quasi_components_of top = connected_components_of top`;;

let QUASI_EQ_CONNECTED_COMPONENT_OF = `!top (x:A).
      FINITE(connected_components_of top) \/
      FINITE(quasi_components_of top) \/
      locally_connected_space top \/
      compact_space top /\
      (hausdorff_space top \/ regular_space top \/ normal_space top)
      ==> quasi_component_of top x = connected_component_of top x`;;

(* ------------------------------------------------------------------------- *)
(* Additional quasicomponent and continuum properties like Boundary Bumping. *)
(* ------------------------------------------------------------------------- *)

let CUT_WIRE_FENCE_THEOREM_GEN = `!top s t:A->bool.
        compact_space top /\
        (hausdorff_space top \/ regular_space top \/ normal_space top) /\
        compact_in top s /\ closed_in top t /\
        (!c. connected_in top c ==> DISJOINT c s \/ DISJOINT c t)
        ==> separated_between top s t`;;

let CUT_WIRE_FENCE_THEOREM = `!top s t:A->bool.
        compact_space top /\ hausdorff_space top /\
        closed_in top s /\ closed_in top t /\
        (!c. connected_in top c ==> DISJOINT c s \/ DISJOINT c t)
        ==> separated_between top s t`;;

let SEPARATED_BETWEEN_FROM_CLOSED_SUBTOPOLOGY = `!top s t c:A->bool.
        separated_between (subtopology top c) s (top frontier_of c) /\
        separated_between (subtopology top c) s t
        ==> separated_between top s t`;;

let SEPARATED_BETWEEN_FROM_CLOSED_SUBTOPOLOGY_FRONTIER = `!top s t:A->bool.
        separated_between (subtopology top t) s (top frontier_of t)
        ==> separated_between top s (top frontier_of t)`;;

let SEPARATED_BETWEEN_FROM_FRONTIER_OF_CLOSED_SUBTOPOLOGY = `!top s t:A->bool.
        separated_between (subtopology top t) s (top frontier_of t)
        ==> separated_between top s (topspace top DIFF t)`;;

let SEPARATED_BETWEEN_COMPACT_CONNECTED_COMPONENT = `!top c t:A->bool.
        locally_compact_space top /\ hausdorff_space top /\
        c IN connected_components_of top /\ compact_in top c /\
        closed_in top t /\ DISJOINT c t
        ==> separated_between top c t`;;

let WILDER_LOCALLY_COMPACT_COMPONENT_THM = `!top c w:A->bool.
        locally_compact_space top /\ hausdorff_space top /\
        c IN connected_components_of top /\ compact_in top c /\
        open_in top w /\ c SUBSET w
        ==> ?u v. open_in top u /\ open_in top v /\
                  DISJOINT u v /\ u UNION v = topspace top /\
                  c SUBSET u /\ u SUBSET w`;;

let COMPACT_QUASI_EQ_CONNECTED_COMPONENTS_OF = `!top c:A->bool.
        locally_compact_space top /\ hausdorff_space top /\
        compact_in top c
        ==> (c IN quasi_components_of top <=>
             c IN connected_components_of top)`;;

let BOUNDARY_BUMPING_THEOREM_CLOSED_GEN = `!top s c:A->bool.
        connected_space top /\
        locally_compact_space top /\
        hausdorff_space top /\
        closed_in top s /\
        ~(s = topspace top) /\
        compact_in top c /\
        c IN connected_components_of(subtopology top s)
        ==> ~(c INTER top frontier_of s = {})`;;

let BOUNDARY_BUMPING_THEOREM_CLOSED = `!top s c:A->bool.
        connected_space top /\ compact_space top /\ hausdorff_space top /\
        closed_in top s /\ ~(s = topspace top) /\
        c IN connected_components_of(subtopology top s)
        ==> ~(c INTER top frontier_of s = {})`;;

let INTERMEDIATE_CONTINUUM_EXISTS = `!top c u:A->bool.
        connected_space top /\
        locally_compact_space top /\
        hausdorff_space top /\
        compact_in top c /\ connected_in top c /\
        ~(c = {}) /\ ~(c = topspace top) /\
        open_in top u /\ c SUBSET u
        ==> ?d. compact_in top d /\ connected_in top d /\
                c PSUBSET d /\ d PSUBSET u`;;

let BOUNDARY_BUMPING_THEOREM_GEN = `!top s c:A->bool.
        connected_space top /\
        locally_compact_space top /\
        hausdorff_space top /\
        s PSUBSET topspace top /\
        c IN connected_components_of(subtopology top s) /\
        compact_in top (top closure_of c)
        ==> ~(top frontier_of c INTER top frontier_of s = {})`;;

let BOUNDARY_BUMPING_THEOREM = `!top s c:A->bool.
        connected_space top /\
        compact_space top /\
        hausdorff_space top /\
        s PSUBSET topspace top /\
        c IN connected_components_of(subtopology top s)
        ==> ~(top frontier_of c INTER top frontier_of s = {})`;;

(* ------------------------------------------------------------------------- *)
(* k-spaces (with no Hausdorff-ness assumptions built in).                   *)
(* ------------------------------------------------------------------------- *)

let k_space = new_definition
 `k_space (top:A topology) <=>
        !s. s SUBSET topspace top
            ==> (closed_in top s <=>
                 !k. compact_in top k
                     ==> closed_in (subtopology top k) (k INTER s))`;;

let K_SPACE = `!top:A topology.
        k_space top <=>
        !s. s SUBSET topspace top /\
            (!k. compact_in top k
                 ==> closed_in (subtopology top k) (k INTER s))
            ==> closed_in top s`;;

let K_SPACE_OPEN = `!top:A topology.
        k_space top <=>
        !s. s SUBSET topspace top /\
            (!k. compact_in top k
                 ==> open_in (subtopology top k) (k INTER s))
            ==> open_in top s`;;

let K_SPACE_ALT = `!top:A topology.
        k_space top <=>
        !s. s SUBSET topspace top
            ==> (open_in top s <=>
                 !k. compact_in top k
                     ==> open_in (subtopology top k) (k INTER s))`;;

let K_SPACE_QUOTIENT_MAP_IMAGE = `!top top' (q:A->B).
        quotient_map(top,top') q /\ k_space top ==> k_space top'`;;

let K_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map (top,top') r /\ k_space top ==> k_space top'`;;

let HOMEOMORPHIC_K_SPACE = `!(top:A topology) (top':B topology).
      top homeomorphic_space top'
      ==> (k_space top <=> k_space top')`;;

let K_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
        k_space top /\ perfect_map(top,top') f
        ==> k_space top'`;;

let LOCALLY_COMPACT_IMP_K_SPACE = `!top:A topology. locally_compact_space top ==> k_space top`;;

let COMPACT_IMP_K_SPACE = `!top:A topology. compact_space top ==> k_space top`;;

let K_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. k_space(discrete_topology u)`;;

let METRIZABLE_IMP_K_SPACE = `!top:A topology. metrizable_space top ==> k_space top`;;

let K_SPACE_MTOPOLOGY = `!m:A metric. k_space(mtopology m)`;;

let K_SPACE_EUCLIDEANREAL = `k_space euclideanreal`;;

let K_SPACE_CLOSED_SUBTOPOLOGY = `!top s:A->bool.
        k_space top /\ closed_in top s ==> k_space(subtopology top s)`;;

let K_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        (!t. t SUBSET topspace top /\ t SUBSET s /\
             (!k. compact_in top k
                  ==> closed_in (subtopology top (k INTER s)) (k INTER t))
             ==> closed_in (subtopology top s) t) /\
        (!k. compact_in top k
             ==> k_space(subtopology top (k INTER s)))
        ==> k_space(subtopology top s)`;;

let K_SPACE_SUBTOPOLOGY_OPEN = `!top s:A->bool.
        (!t. t SUBSET topspace top /\ t SUBSET s /\
             (!k. compact_in top k
                  ==> open_in (subtopology top (k INTER s)) (k INTER t))
             ==> open_in (subtopology top s) t) /\
        (!k. compact_in top k
             ==> k_space(subtopology top (k INTER s)))
        ==> k_space(subtopology top s)`;;

let K_SPACE_OPEN_SUBTOPOLOGY = `!top s:A->bool.
        (kc_space top \/ hausdorff_space top \/ regular_space top) /\
        k_space top /\ open_in top s
        ==> k_space(subtopology top s)`;;

let K_KC_SPACE_SUBTOPOLOGY = `!top s:A->bool.
        k_space top /\ kc_space top /\
        (open_in top s \/ closed_in top s)
        ==> k_space(subtopology top s) /\ kc_space(subtopology top s)`;;

let K_SPACE_AS_QUOTIENT_EXPLICIT = `!top:A topology.
        k_space top <=>
        quotient_map (sum_topology {k | compact_in top k} (subtopology top),
                      top)
                     SND`;;

let K_SPACE_AS_QUOTIENT = `!top:A topology.
        k_space top <=>
        ?q (top':((A->bool)#A)topology).
                locally_compact_space top' /\ quotient_map(top',top) q`;;

let K_SPACE_PROD_TOPOLOGY_LEFT = `!(top:A topology) (top':B topology).
        locally_compact_space top /\
        (hausdorff_space top \/ regular_space top) /\
        k_space top'
        ==> k_space(prod_topology top top')`;;

let K_SPACE_PROD_TOPOLOGY_RIGHT = `!(top:A topology) (top':B topology).
        k_space top /\
        locally_compact_space top' /\
        (hausdorff_space top' \/ regular_space top')
        ==> k_space(prod_topology top top')`;;

let CONTINUOUS_MAP_FROM_K_SPACE = `!top top' (f:A->B).
        k_space top /\
        (!k. compact_in top k ==> continuous_map(subtopology top k,top') f)
        ==> continuous_map(top,top') f`;;

let CLOSED_MAP_INTO_K_SPACE = `!top top' (f:A->B).
      k_space top' /\
      IMAGE f (topspace top) SUBSET topspace top' /\
      (!k. compact_in top' k
           ==> closed_map(subtopology top {x | x IN topspace top /\ f x IN k},
                          subtopology top' k) f)
      ==> closed_map(top,top') f`;;

let OPEN_MAP_INTO_K_SPACE = `!top top' (f:A->B).
      k_space top' /\
      IMAGE f (topspace top) SUBSET topspace top' /\
      (!k. compact_in top' k
           ==> open_map(subtopology top {x | x IN topspace top /\ f x IN k},
                        subtopology top' k) f)
      ==> open_map(top,top') f`;;

let QUOTIENT_MAP_INTO_K_SPACE = `!top top' (f:A->B).
     k_space top' /\
     continuous_map(top,top') f /\
     IMAGE f (topspace top) = topspace top' /\
     (!k. compact_in top' k
          ==> quotient_map(subtopology top {x | x IN topspace top /\ f x IN k},
                           subtopology top' k) f)
     ==> quotient_map(top,top') f`;;

let QUOTIENT_MAP_INTO_K_SPACE_EQ = `!top top' (f:A->B).
        k_space top' /\ kc_space top'
        ==> (quotient_map(top,top') f <=>
             continuous_map(top,top') f /\
             IMAGE f (topspace top) = topspace top' /\
             !k. compact_in top' k
                  ==> quotient_map
                       (subtopology top {x | x IN topspace top /\ f x IN k},
                        subtopology top' k) f)`;;

let OPEN_MAP_INTO_K_SPACE_EQ = `!top top' (f:A->B).
        k_space top'
        ==> (open_map(top,top') f <=>
             IMAGE f (topspace top) SUBSET topspace top' /\
             !k. compact_in top' k
                  ==> open_map
                       (subtopology top {x | x IN topspace top /\ f x IN k},
                        subtopology top' k) f)`;;

let CLOSED_MAP_INTO_K_SPACE_EQ = `!top top' (f:A->B).
        k_space top'
        ==> (closed_map(top,top') f <=>
             IMAGE f (topspace top) SUBSET topspace top' /\
             !k. compact_in top' k
                  ==> closed_map
                       (subtopology top {x | x IN topspace top /\ f x IN k},
                        subtopology top' k) f)`;;

let PROPER_MAP_INTO_K_SPACE = `!top top' (f:A->B).
      k_space top' /\
      IMAGE f (topspace top) SUBSET topspace top' /\
      (!k. compact_in top' k
           ==> proper_map(subtopology top {x | x IN topspace top /\ f x IN k},
                          subtopology top' k) f)
      ==> proper_map(top,top') f`;;

let PROPER_MAP_INTO_K_SPACE_EQ = `!top top' (f:A->B).
        k_space top'
        ==> (proper_map(top,top') f <=>
             IMAGE f (topspace top) SUBSET topspace top' /\
             !k. compact_in top' k
                  ==> proper_map
                       (subtopology top {x | x IN topspace top /\ f x IN k},
                        subtopology top' k) f)`;;

let COMPACT_IMP_PROPER_MAP = `!top top' (f:A->B).
        k_space top' /\ kc_space top' /\
        IMAGE f (topspace top) SUBSET topspace top' /\
        (continuous_map(top,top') f \/ kc_space top) /\
        (!k. compact_in top' k
             ==> compact_in top {x | x IN topspace top /\ f x IN k})
        ==> proper_map(top,top') f`;;

let PROPER_EQ_COMPACT_MAP = `!top top' (f:A->B).
        k_space top' /\ kc_space top' /\
        (continuous_map(top,top') f \/ kc_space top)
        ==> (proper_map(top,top') f <=>
             IMAGE f (topspace top) SUBSET topspace top' /\
             !k. compact_in top' k
                 ==> compact_in top {x | x IN topspace top /\ f x IN k})`;;

let COMPACT_IMP_PERFECT_MAP = `!top top' (f:A->B).
        k_space top' /\ kc_space top' /\
        continuous_map(top,top') f /\ IMAGE f (topspace top) = topspace top' /\
        (!k. compact_in top' k
             ==> compact_in top {x | x IN topspace top /\ f x IN k})
        ==> perfect_map(top,top') f`;;

(* ------------------------------------------------------------------------- *)
(* More generally, the k-ification functor.                                  *)
(* ------------------------------------------------------------------------- *)

let kification = define
 `kification (top:A topology) =
        topology {s | s SUBSET topspace top /\
                      !k. compact_in top k
                           ==> open_in (subtopology top k) (k INTER s)}`;;

let OPEN_IN_KIFICATION = `!top (u:A->bool).
        open_in (kification top) u <=>
        u SUBSET topspace top /\
        !k. compact_in top k  ==> open_in (subtopology top k) (k INTER u)`;;

let OPEN_IN_KIFICATION_FINER = `!top (s:A->bool).
        open_in top s ==> open_in (kification top) s`;;

let TOPSPACE_KIFICATION = `!top:A topology. topspace(kification top) = topspace top`;;

let CLOSED_IN_KIFICATION = `!top (u:A->bool).
        closed_in (kification top) u <=>
        u SUBSET topspace top /\
        !k. compact_in top k  ==> closed_in (subtopology top k) (k INTER u)`;;

let CLOSED_IN_KIFICATION_FINER = `!top (s:A->bool).
        closed_in top s ==> closed_in (kification top) s`;;

let KIFICATION_EQ_SELF = `!top:A topology. kification top = top <=> k_space top`;;

let COMPACT_IN_KIFICATION = `!top (k:A->bool).
        compact_in (kification top) k <=> compact_in top k`;;

let COMPACT_SPACE_KIFICATION = `!top:A topology. compact_space(kification top) <=> compact_space top`;;

let KIFICATION_KIFICATION = `!top:A topology. kification(kification top) = kification top`;;

let K_SPACE_KIFICATION = `!top:A topology. k_space(kification top)`;;

let CONTINUOUS_MAP_INTO_KIFICATION = `!top top' (f:A->B).
        k_space top
        ==> (continuous_map(top,kification top') f <=>
             continuous_map(top,top') f)`;;

let CONTINUOUS_MAP_FROM_KIFICATION = `!top top' (f:A->B).
        continuous_map(top,top') f ==> continuous_map(kification top,top') f`;;

let CONTINUOUS_MAP_KIFICATION = `!top top' (f:A->B).
        continuous_map(top,top') f
        ==> continuous_map(kification top,kification top') f`;;

let SUBTOPOLOGY_KIFICATION_COMPACT = `!top (k:A->bool).
        compact_in top k
        ==> subtopology (kification top) k = subtopology top k`;;

let SUBTOPOLOGY_KIFICATION_FINER = `!top (s:A->bool) u.
        open_in (subtopology (kification top) s) u
        ==> open_in (kification (subtopology top s)) u`;;

let PROPER_MAP_FROM_KIFICATION = `!top top' (f:A->B).
        k_space top'
        ==> (proper_map(kification top,top') f <=>
             proper_map(top,top') f)`;;

let PERFECT_MAP_FROM_KIFICATION = `!top top' (f:A->B).
        k_space top' /\ perfect_map(top,top') f
        ==> perfect_map(kification top,top') f`;;

let K_SPACE_PERFECT_MAP_IMAGE_EQ = `!top top' (f:A->B).
     hausdorff_space top /\ perfect_map(top,top') f
     ==> (k_space top <=> k_space top')`;;

(* ------------------------------------------------------------------------- *)
(* One-point compactifications and the Alexandroff extension construction.   *)
(* ------------------------------------------------------------------------- *)

let ONE_POINT_COMPACTIFICATION_DENSE = `!top a:A.
        compact_space top /\ ~compact_in top (topspace top DELETE a)
        ==> top closure_of (topspace top DELETE a) = topspace top`;;

let ONE_POINT_COMPACTIFICATION_INTERIOR = `!top a:A.
        compact_space top /\ ~compact_in top (topspace top DELETE a)
        ==> top interior_of {a} = {}`;;

let KC_SPACE_ONE_POINT_COMPACTIFICATION_GEN = `!top a:A.
        compact_space top
        ==> (kc_space top <=>
             open_in top (topspace top DELETE a) /\
             (!k. compact_in top k /\ ~(a IN k) ==> closed_in top k) /\
             k_space (subtopology top (topspace top DELETE a)) /\
             kc_space (subtopology top (topspace top DELETE a)))`;;

let alexandroff_compactification = new_definition
 `alexandroff_compactification (top:A topology) =
        topology ({ IMAGE INL u | open_in top u} UNION
                  { INR one INSERT IMAGE INL (topspace top DIFF c) | c |
                    compact_in top c /\ closed_in top c})`;;

let OPEN_IN_ALEXANDROFF_COMPACTIFICATION = `!(top:A topology) v.
        open_in(alexandroff_compactification top) v <=>
        (?u. open_in top u /\ v = IMAGE INL u) \/
        (?c. compact_in top c /\ closed_in top c /\
             v = INR one INSERT IMAGE INL (topspace top DIFF c))`;;

let TOPSPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology.
        topspace(alexandroff_compactification top) =
        INR one INSERT IMAGE INL (topspace top)`;;

let CLOSED_IN_ALEXANDROFF_COMPACTIFICATION = `!(top:A topology) c.
        closed_in (alexandroff_compactification top) c <=>
        (?k. compact_in top k /\ closed_in top k /\ c = IMAGE INL k) \/
        (?u. open_in top u /\
             c = topspace(alexandroff_compactification top) DIFF IMAGE INL u)`;;

let CLOSED_IN_ALEXANDROFF_COMPACTIFICATION_IMAGE_INL = `!(top:A topology) k.
        closed_in (alexandroff_compactification top) (IMAGE INL k) <=>
        compact_in top k /\ closed_in top k`;;

let OPEN_MAP_INL = `!top:A topology. open_map(top,alexandroff_compactification top) INL`;;

let CONTINUOUS_MAP_INL = `!top:A topology. continuous_map(top,alexandroff_compactification top) INL`;;

let EMBEDDING_MAP_INL = `!top:A topology. embedding_map(top,alexandroff_compactification top) INL`;;

let COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology. compact_space(alexandroff_compactification top)`;;

let TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE = `!top:A topology.
        topspace(alexandroff_compactification top) DELETE (INR one) =
        IMAGE INL (topspace top)`;;

let ALEXANDROFF_COMPACTIFICATION_DENSE = `!top:A topology.
        ~compact_space top
        ==> (alexandroff_compactification top)
            closure_of (IMAGE INL (topspace top)) =
            topspace(alexandroff_compactification top)`;;

let T0_SPACE_ONE_POINT_COMPACTIFICATION = `!top a:A.
        compact_space top /\
        open_in top (topspace top DELETE a)
        ==> (t0_space top <=>
             t0_space (subtopology top (topspace top DELETE a)))`;;

let T0_SPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology.
        t0_space(alexandroff_compactification top) <=>
        t0_space top`;;

let T1_SPACE_ONE_POINT_COMPACTIFICATION = `!top a:A.
        open_in top (topspace top DELETE a) /\
        (!k. compact_in (subtopology top (topspace top DELETE a)) k /\
             closed_in (subtopology top (topspace top DELETE a)) k
             ==> closed_in top k)
        ==> (t1_space top <=>
             t1_space (subtopology top (topspace top DELETE a)))`;;

let T1_SPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology.
        t1_space(alexandroff_compactification top) <=>
        t1_space top`;;

let KC_SPACE_ONE_POINT_COMPACTIFICATION = `!top a:A.
        compact_space top /\
        open_in top (topspace top DELETE a) /\
        (!k. compact_in (subtopology top (topspace top DELETE a)) k /\
             closed_in (subtopology top (topspace top DELETE a)) k
             ==> closed_in top k)
        ==> (kc_space top <=>
             k_space (subtopology top (topspace top DELETE a)) /\
             kc_space (subtopology top (topspace top DELETE a)))`;;

let KC_SPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology.
        kc_space(alexandroff_compactification top) <=>
        k_space top /\ kc_space top`;;

let REGULAR_SPACE_ONE_POINT_COMPACTIFICATION = `!top a:A.
        compact_space top /\
        open_in top (topspace top DELETE a) /\
        (!k. compact_in (subtopology top (topspace top DELETE a)) k /\
             closed_in (subtopology top (topspace top DELETE a)) k
             ==> closed_in top k)
        ==> (regular_space top <=>
             regular_space (subtopology top (topspace top DELETE a)) /\
             locally_compact_space (subtopology top (topspace top DELETE a)))`;;

let REGULAR_SPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology.
        regular_space(alexandroff_compactification top) <=>
        regular_space top /\ locally_compact_space top`;;

let HAUSDORFF_SPACE_ONE_POINT_COMPACTIFICATION = `!top a:A.
        compact_space top /\
        open_in top (topspace top DELETE a) /\
        (!k. compact_in (subtopology top (topspace top DELETE a)) k /\
             closed_in (subtopology top (topspace top DELETE a)) k
             ==> closed_in top k)
        ==> (hausdorff_space top <=>
             hausdorff_space (subtopology top (topspace top DELETE a)) /\
             locally_compact_space (subtopology top (topspace top DELETE a)))`;;

let HAUSDORFF_SPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology.
        hausdorff_space(alexandroff_compactification top) <=>
        hausdorff_space top /\ locally_compact_space top`;;

let COMPLETELY_REGULAR_SPACE_ALEXANDROFF_COMPACTIFICATION = `!top:A topology.
        completely_regular_space(alexandroff_compactification top) <=>
        completely_regular_space top /\ locally_compact_space top`;;

let HAUSDORFF_SPACE_ONE_POINT_COMPACTIFICATION_ASYMMETRIC_PROD = `!top a:A.
        compact_space top
        ==> (hausdorff_space top <=>
             kc_space
              (prod_topology top (subtopology top (topspace top DELETE a))) /\
             k_space
              (prod_topology top (subtopology top (topspace top DELETE a))))`;;

let HAUSDORFF_SPACE_ALEXANDROFF_COMPACTIFICATION_ASYMMETRIC_PROD = `!top:A topology.
        hausdorff_space(alexandroff_compactification top) <=>
        kc_space(prod_topology (alexandroff_compactification top) top) /\
        k_space(prod_topology (alexandroff_compactification top) top)`;;

let KC_SPACE_AS_COMPACTIFICATION_UNIQUE = `!top a:A.
        kc_space top /\ compact_space top
        ==> !u. open_in top u <=>
                if a IN u
                then u SUBSET topspace top /\
                     compact_in top (topspace top DIFF u)
                else open_in (subtopology top (topspace top DELETE a)) u`;;

let KC_SPACE_AS_COMPACTIFICATION_UNIQUE_EXPLICIT = `!top a:A.
        kc_space top /\ compact_space top
        ==> !u. open_in top u <=>
                if a IN u
                then u SUBSET topspace top /\
                     compact_in (subtopology top (topspace top DELETE a))
                                (topspace top DIFF u) /\
                     closed_in (subtopology top (topspace top DELETE a))
                                (topspace top DIFF u)
                else open_in (subtopology top (topspace top DELETE a)) u`;;

let ALEXANDROFF_COMPACTIFICATION_UNIQUE = `!top a:A.
        kc_space top /\ compact_space top /\ a IN topspace top
        ==> alexandroff_compactification
             (subtopology top (topspace top DELETE a))
            homeomorphic_space top`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy of maps p,q : X->Y with property P of all intermediate maps.     *)
(* We often just want to require that it fixes some subset, but to take in   *)
(* the case of loop homotopy it's convenient to have a general property P.   *)
(* ------------------------------------------------------------------------- *)

let homotopic_with = new_definition
  `homotopic_with P (X,Y) p q <=>
   ?h. continuous_map
       (prod_topology (subtopology euclideanreal (real_interval[&0,&1])) X,
        Y) h /\
       (!x. h(&0,x) = p x) /\ (!x. h(&1,x) = q x) /\
       (!t. t IN real_interval[&0,&1] ==> P(\x. h(t,x)))`;;

let HOMOTOPIC_WITH = `!P X Y p q:A->B.
        (!h k. (!x. x IN topspace X ==> h x = k x) ==> (P h <=> P k))
        ==> (homotopic_with P (X,Y) p q <=>
             ?h. continuous_map
                  (prod_topology
                   (subtopology euclideanreal (real_interval [&0,&1])) X,
                   Y) h /\
                (!x. x IN topspace X ==> h (&0,x) = p x) /\
                (!x. x IN topspace X ==> h (&1,x) = q x) /\
                (!t. t IN real_interval[&0,&1] ==> P (\x. h (t,x))))`;;

let HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS = `!P X Y p q:A->B.
        homotopic_with P (X,Y) p q
        ==> continuous_map (X,Y) p /\ continuous_map (X,Y) q`;;

let HOMOTOPIC_WITH_IMP_PROPERTY = `!P X Y f g:A->B. homotopic_with P (X,Y) f g ==> P f /\ P g`;;

let HOMOTOPIC_WITH_EQUAL = `!P top top' (f:A->B) g.
        P f /\ P g /\
        continuous_map(top,top') f /\
        (!x. x IN topspace top ==> f x = g x)
        ==> homotopic_with P (top,top') f g`;;

let HOMOTOPIC_WITH_REFL = `!P top top' f:A->B.
        homotopic_with P (top,top') f f <=>
        continuous_map (top,top') f /\ P f`;;

let HOMOTOPIC_WITH_SYM = `!P X Y f g:A->B.
     homotopic_with P (X,Y) f g <=> homotopic_with P (X,Y) g f`;;

let HOMOTOPIC_WITH_TRANS = `!P top top' (f:A->B) g h.
        homotopic_with P (top,top') f g /\
        homotopic_with P (top,top') g h
        ==> homotopic_with P (top,top') f h`;;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT = `!p q (f:A->B) g (h:B->C) top1 top2 top3.
        homotopic_with p (top1,top2) f g /\
        continuous_map (top2,top3) h /\
        (!j. p j ==> q(h o j))
        ==> homotopic_with q (top1,top3) (h o f) (h o g)`;;

let HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_LEFT = `!(f:A->B) g (h:B->C) top1 top2 top3.
        homotopic_with (\k. T) (top1,top2) f g /\
        continuous_map (top2,top3) h
        ==> homotopic_with (\k. T) (top1,top3) (h o f) (h o g)`;;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT = `!p q (f:B->C) g (h:A->B) top1 top2 top3.
        homotopic_with p (top2,top3) f g /\
        continuous_map (top1,top2) h /\
        (!j. p j ==> q(j o h))
        ==> homotopic_with q (top1,top3) (f o h) (g o h)`;;

let HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_RIGHT = `!(f:B->C) g (h:A->B) top1 top2 top3.
        homotopic_with (\k. T) (top2,top3) f g /\
        continuous_map (top1,top2) h
        ==> homotopic_with (\k. T) (top1,top3) (f o h) (g o h)`;;

let HOMOTOPIC_FROM_SUBTOPOLOGY = `!P top top' s f (g:A->B).
        homotopic_with P (top,top') f g
        ==> homotopic_with P (subtopology top s,top') f g`;;

let HOMOTOPIC_ON_EMPTY = `!top top' (f:A->B) g.
        topspace top = {}
        ==> (homotopic_with P (top,top') f g <=> P f /\ P g)`;;

let HOMOTOPIC_CONSTANT_MAPS = `!(top:A topology) (top':B topology) a b.
        homotopic_with (\x. T) (top,top') (\x. a) (\x. b) <=>
        topspace top = {} \/ path_component_of top' a b`;;

let HOMOTOPIC_WITH_EQ = `!P top top' f g f' g':A->B.
        homotopic_with P (top,top') f g /\
        (!x. x IN topspace top ==> f' x = f x /\ g' x = g x) /\
        (!h k. (!x. x IN topspace top ==> h x = k x) ==> (P h <=> P k))
        ==>  homotopic_with P (top,top') f' g'`;;

let HOMOTOPIC_WITH_PROD_TOPOLOGY = `!p q r top1 top1' top2 top2' (f:A->B) (g:C->D) f' g'.
      homotopic_with p (top1,top1') f f' /\
      homotopic_with q (top2,top2') g g' /\
      (!i j. p i /\ q j ==> r(\(x,y). i x,j y))
      ==> homotopic_with r (prod_topology top1 top2,prod_topology top1' top2')
                           (\z. f(FST z),g(SND z)) (\z. f'(FST z),g'(SND z))`;;

let HOMOTOPIC_WITH_PRODUCT_TOPOLOGY = `!k (tops:K->A topology) (tops':K->B topology) p q f g.
     (!i. i IN k
          ==> homotopic_with (p i) (tops i,tops' i) (f i) (g i)) /\
     (!h. (!i. i IN k ==> p i (h i)) ==> q(\x. RESTRICTION k (\i. h i (x i))))
     ==> homotopic_with q (product_topology k tops,product_topology k tops')
                          (\z. RESTRICTION k (\i. (f i) (z i)))
                          (\z. RESTRICTION k (\i. (g i) (z i)))`;;

(* ------------------------------------------------------------------------- *)
(* Homotopy equivalence of topological spaces.                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("homotopy_equivalent_space",(12,"right"));;

let homotopy_equivalent_space = new_definition
 `(top:A topology) homotopy_equivalent_space (top':B topology) <=>
        ?f g. continuous_map (top,top') f /\
              continuous_map (top',top) g /\
              homotopic_with (\x. T) (top,top) (g o f) I /\
              homotopic_with (\x. T) (top',top') (f o g) I`;;

let HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> top homotopy_equivalent_space top'`;;

let HOMOTOPY_EQUIVALENT_SPACE_REFL = `!top:A topology. top homotopy_equivalent_space top`;;

let HOMOTOPY_EQUIVALENT_SPACE_SYM = `!(top:A topology) (top':B topology).
        top homotopy_equivalent_space top' <=>
        top' homotopy_equivalent_space top`;;

let HOMOTOPY_EQUIVALENT_SPACE_TRANS = `!top1:A topology top2:B topology top3:C topology.
        top1 homotopy_equivalent_space top2 /\
        top2 homotopy_equivalent_space top3
        ==> top1 homotopy_equivalent_space top3`;;

let DEFORMATION_RETRACTION_IMP_HOMOTOPY_EQUIVALENT_SPACE = `!top top' (r:A->B) s.
        homotopic_with (\x. T) (top,top) (s o r) I /\
        retraction_maps(top,top') (r,s)
        ==> top homotopy_equivalent_space top'`;;

let DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT_SPACE = `!top top' (r:A->A).
        homotopic_with (\x. T) (top,top) r I /\
        retraction_maps(top,top') (r,I)
        ==> top homotopy_equivalent_space top'`;;

let DEFORMATION_RETRACT_OF_SPACE = `!top s:A->bool.
        s SUBSET topspace top /\
        (?r. homotopic_with (\x. T) (top,top) I r /\
             retraction_maps(top,subtopology top s) (r,I)) <=>
        s retract_of_space top /\
        (?f. homotopic_with (\x. T) (top,top) I f /\
             IMAGE f (topspace top) SUBSET s)`;;

(* ------------------------------------------------------------------------- *)
(* Contractible spaces. The definition (which agrees with "contractible" on  *)
(* subsets of Euclidean space) is a little cryptic because we don't in fact  *)
(* assume that the constant "a" is in the space. This forces the convention  *)
(* that the empty space / set is contractible, avoiding some special cases.  *)
(* ------------------------------------------------------------------------- *)

let contractible_space = new_definition
 `contractible_space (top:A topology) <=>
        ?a. homotopic_with (\x. T) (top,top) (\x. x) (\x. a)`;;

let CONTRACTIBLE_SPACE_EMPTY = `!top:A topology. topspace top = {} ==> contractible_space top`;;

let CONTRACTIBLE_SPACE_SING = `!top a:A. topspace top = {a} ==> contractible_space top`;;

let CONTRACTIBLE_SPACE_SUBSET_SING = `!top a:A. topspace top SUBSET {a} ==> contractible_space top`;;

let CONTRACTIBLE_SPACE_SUBTOPOLOGY_SING = `!top a:A. contractible_space(subtopology top {a})`;;

let CONTRACTIBLE_SPACE = `!top:A topology.
        contractible_space top <=>
        topspace top = {} \/
        ?a. a IN topspace top /\
            homotopic_with (\x. T) (top,top) (\x. x) (\x. a)`;;

let CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE = `!top:A topology.
        contractible_space top ==> path_connected_space top`;;

let CONTRACTIBLE_IMP_CONNECTED_SPACE = `!top:A topology. contractible_space top ==> connected_space top`;;

let CONTRACTIBLE_SPACE_ALT = `!top:A topology.
        contractible_space top <=>
        !a. a IN topspace top
            ==> homotopic_with (\x. T) (top,top) (\x. x) (\x. a)`;;

let NULLHOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE = `!(f:A->B) (g:B->C) top1 top2 top3.
        continuous_map (top1,top2) f /\
        continuous_map (top2,top3) g /\
        contractible_space top2
        ==> ?c. homotopic_with (\h. T) (top1,top3) (g o f) (\x. c)`;;

let NULLHOMOTOPIC_INTO_CONTRACTIBLE_SPACE = `!(f:A->B) top1 top2.
        continuous_map (top1,top2) f /\ contractible_space top2
        ==> ?c. homotopic_with (\h. T) (top1,top2) f (\x. c)`;;

let NULLHOMOTOPIC_FROM_CONTRACTIBLE_SPACE = `!(f:A->B) top1 top2.
        continuous_map (top1,top2) f /\ contractible_space top1
        ==> ?c. homotopic_with (\h. T) (top1,top2) f (\x. c)`;;

let HOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE = `!(f:A->B) (g:B->C) f' g' top1 top2 top3.
        continuous_map (top1,top2) f /\
        continuous_map (top1,top2) f' /\
        continuous_map (top2,top3) g /\
        continuous_map (top2,top3) g' /\
        contractible_space top2 /\ path_connected_space top3
        ==> homotopic_with (\h. T) (top1,top3) (g o f) (g' o f')`;;

let HOMOTOPIC_FROM_CONTRACTIBLE_SPACE = `!(f:A->B) g top top'.
        continuous_map (top,top') f /\ continuous_map (top,top') g /\
        contractible_space top /\ path_connected_space top'
        ==> homotopic_with (\x. T) (top,top') f g`;;

let HOMOTOPIC_INTO_CONTRACTIBLE_SPACE = `!(f:A->B) g top top'.
        continuous_map (top,top') f /\ continuous_map (top,top') g /\
        contractible_space top'
        ==> homotopic_with (\x. T) (top,top') f g`;;

let HOMOTOPY_DOMINATED_CONTRACTIBILITY = `!(f:A->B) g top top'.
        continuous_map (top,top') f /\
        continuous_map (top',top) g /\
        homotopic_with (\x. T) (top',top') (f o g) I /\
        contractible_space top
        ==> contractible_space top'`;;

let HOMOTOPY_EQUIVALENT_SPACE_CONTRACTIBILITY = `!(top:A topology) (top':B topology).
        top homotopy_equivalent_space top'
        ==> (contractible_space top <=> contractible_space top')`;;

let HOMEOMORPHIC_SPACE_CONTRACTIBILITY = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (contractible_space top <=> contractible_space top')`;;

let CONTRACTIBLE_EQ_HOMOTOPY_EQUIVALENT_SINGLETON_SUBTOPOLOGY = `!top:A topology.
        contractible_space top <=>
        topspace top = {} \/
        ?a. a IN topspace top /\
            top homotopy_equivalent_space (subtopology top {a})`;;

let CONTRACTIBLE_SPACE_RETRACTION_MAP_IMAGE = `!top top' (f:A->B).
        retraction_map(top,top') f /\ contractible_space top
        ==> contractible_space top'`;;

let CONTRACTIBLE_SPACE_PROD_TOPOLOGY = `!(top1:A topology) (top2:B topology).
        contractible_space(prod_topology top1 top2) <=>
        topspace top1 = {} \/ topspace top2 = {} \/
        contractible_space top1 /\ contractible_space top2`;;

let CONTRACTIBLE_SPACE_PRODUCT_TOPOLOGY = `!k (tops:K->A topology).
        contractible_space(product_topology k tops) <=>
        topspace (product_topology k tops) = {} \/
        !i. i IN k ==> contractible_space(tops i)`;;

let CONTRACTIBLE_SPACE_SUBTOPOLOGY_EUCLIDEANREAL = `!s. contractible_space(subtopology euclideanreal s) <=> is_realinterval s`;;

let CONTRACTIBLE_SPACE_EUCLIDEANREAL = `contractible_space euclideanreal`;;

(* ------------------------------------------------------------------------- *)
(* Completely metrizable (a.k.a. "topologically complete") spaces.           *)
(* ------------------------------------------------------------------------- *)

let completely_metrizable_space = new_definition
 `completely_metrizable_space top <=>
  ?m. mcomplete m /\ top = mtopology m`;;

let COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE = `!top:A topology. completely_metrizable_space top ==> metrizable_space top`;;

let FORALL_MCOMPLETE_TOPOLOGY = `!P. (!m:A metric. mcomplete m ==> P (mtopology m) (mspace m)) <=>
       !top. completely_metrizable_space top ==> P top (topspace top)`;;

let FORALL_COMPLETELY_METRIZABLE_SPACE = `(!top. completely_metrizable_space top ==> P top (topspace top)) <=>
   (!m:A metric. mcomplete m ==> P (mtopology m) (mspace m))`;;

let EXISTS_COMPLETELY_METRIZABLE_SPACE = `!P. (?top. completely_metrizable_space top /\ P top (topspace top)) <=>
       (?m:A metric.mcomplete m /\  P (mtopology m) (mspace m))`;;

let COMPLETELY_METRIZABLE_SPACE_MTOPOLOGY = `!m:A metric. mcomplete m ==> completely_metrizable_space(mtopology m)`;;

let COMPLETELY_METRIZABLE_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. completely_metrizable_space(discrete_topology u)`;;

let COMPLETELY_METRIZABLE_SPACE_EUCLIDEANREAL = `completely_metrizable_space euclideanreal`;;

let COMPLETELY_METRIZABLE_SPACE_CLOSED_IN = `!top s:A->bool.
        completely_metrizable_space top /\ closed_in top s
        ==> completely_metrizable_space(subtopology top s)`;;

let HOMEOMORPHIC_COMPLETELY_METRIZABLE_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (completely_metrizable_space top <=>
             completely_metrizable_space top')`;;

let COMPLETELY_METRIZABLE_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ completely_metrizable_space top
        ==> completely_metrizable_space top'`;;

(* ------------------------------------------------------------------------- *)
(* Product metric. For the nicest fit with the main Euclidean theories, we   *)
(* make this the Euclidean product, though others would work topologically.  *)
(* ------------------------------------------------------------------------- *)

let prod_metric = new_definition
 `prod_metric m1 m2 =
  metric((mspace m1 CROSS mspace m2):A#B->bool,
         \((x,y),(x',y')).
            sqrt(mdist m1 (x,x') pow 2 + mdist m2 (y,y') pow 2))`;;

let PROD_METRIC = `(!(m1:A metric) (m2:B metric).
      mspace(prod_metric m1 m2) = mspace m1 CROSS mspace m2) /\
   (!(m1:A metric) (m2:B metric).
        mdist(prod_metric m1 m2) =
        \((x,y),(x',y')).
            sqrt(mdist m1 (x,x') pow 2 + mdist m2 (y,y') pow 2))`;;

let COMPONENT_LE_PROD_METRIC = `!m1 m2 x1 y1 x2:A y2:B.
        mdist m1 (x1,x2) <= mdist (prod_metric m1 m2) ((x1,y1),(x2,y2)) /\
        mdist m2 (y1,y2) <= mdist (prod_metric m1 m2) ((x1,y1),(x2,y2))`;;

let PROD_METRIC_LE_COMPONENTS = `!m1 m2 x1 y1 x2:A y2:B.
        x1 IN mspace m1 /\ x2 IN mspace m1 /\
        y1 IN mspace m2 /\ y2 IN mspace m2
        ==> mdist (prod_metric m1 m2) ((x1,y1),(x2,y2))
            <= mdist m1 (x1,x2) + mdist m2 (y1,y2)`;;

let MBALL_PROD_METRIC_SUBSET = `!m1 m2 x:A y:B r.
        mball (prod_metric m1 m2) ((x,y),r) SUBSET
        mball m1 (x,r) CROSS mball m2 (y,r)`;;

let MCBALL_PROD_METRIC_SUBSET = `!m1 m2 x:A y:B r.
        mcball (prod_metric m1 m2) ((x,y),r) SUBSET
        mcball m1 (x,r) CROSS mcball m2 (y,r)`;;

let MBALL_SUBSET_PROD_METRIC = `!m1 m2 x:A y:B r r'.
        mball m1 (x,r) CROSS mball m2 (y,r')
        SUBSET mball (prod_metric m1 m2) ((x,y),r + r')`;;

let MCBALL_SUBSET_PROD_METRIC = `!m1 m2 x:A y:B r r'.
        mcball m1 (x,r) CROSS mcball m2 (y,r')
        SUBSET mcball (prod_metric m1 m2) ((x,y),r + r')`;;

let MTOPOLOGY_PROD_METRIC = `!(m1:A metric) (m2:B metric).
        mtopology(prod_metric m1 m2) =
        prod_topology (mtopology m1) (mtopology m2)`;;

let SUBMETRIC_PROD_METRIC = `!m1 m2 s:A->bool t:B->bool.
        submetric (prod_metric m1 m2) (s CROSS t) =
        prod_metric (submetric m1 s) (submetric m2 t)`;;

let METRIZABLE_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        metrizable_space (prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        metrizable_space top1 /\ metrizable_space top2`;;

let CAUCHY_IN_PROD_METRIC = `!m1 m2 x:num->A#B.
        cauchy_in (prod_metric m1 m2) x <=>
        cauchy_in m1 (FST o x) /\ cauchy_in m2 (SND o x)`;;

let MCOMPLETE_PROD_METRIC = `!(m1:A metric) (m2:B metric).
        mcomplete (prod_metric m1 m2) <=>
        mspace m1 = {} \/ mspace m2 = {} \/ mcomplete m1 /\ mcomplete m2`;;

let COMPLETELY_METRIZABLE_SPACE_PROD_TOPOLOGY = `!top1:A topology top2:B topology.
        completely_metrizable_space (prod_topology top1 top2) <=>
        topspace(prod_topology top1 top2) = {} \/
        completely_metrizable_space top1 /\ completely_metrizable_space top2`;;

let MBOUNDED_CROSS = `!(m1:A metric) (m2:B metric) s t.
        mbounded (prod_metric m1 m2) (s CROSS t) <=>
        s = {} \/ t = {} \/ mbounded m1 s /\ mbounded m2 t`;;

let MBOUNDED_PROD_METRIC = `!(m1:A metric) (m2:B metric) u.
        mbounded (prod_metric m1 m2) u <=>
        mbounded m1 (IMAGE FST u) /\ mbounded m2 (IMAGE SND u)`;;

let TOTALLY_BOUNDED_IN_CROSS = `!(m1:A metric) (m2:B metric) s t.
       totally_bounded_in (prod_metric m1 m2) (s CROSS t) <=>
       s = {} \/ t = {} \/ totally_bounded_in m1 s /\ totally_bounded_in m2 t`;;

let TOTALLY_BOUNDED_IN_PROD_METRIC = `!(m1:A metric) (m2:B metric) u.
        totally_bounded_in (prod_metric m1 m2) u <=>
        totally_bounded_in m1 (IMAGE FST u) /\
        totally_bounded_in m2 (IMAGE SND u)`;;

(* ------------------------------------------------------------------------- *)
(* Three more restrictive notions of continuity for metric spaces.           *)
(* ------------------------------------------------------------------------- *)

let lipschitz_continuous_map = new_definition
 `lipschitz_continuous_map (m1,m2) f <=>
        IMAGE f (mspace m1) SUBSET mspace m2 /\
        ?B. !x y. x IN mspace m1 /\ y IN mspace m1
                  ==> mdist m2 (f x,f y) <= B * mdist m1 (x,y)`;;

let LIPSCHITZ_CONTINUOUS_MAP_POS = `!m1 m2 f:A->B.
        lipschitz_continuous_map (m1,m2) f <=>
        IMAGE f (mspace m1) SUBSET mspace m2 /\
        ?B. &0 < B /\
            !x y. x IN mspace m1 /\ y IN mspace m1
                  ==> mdist m2 (f x,f y) <= B * mdist m1 (x,y)`;;

let LIPSCHITZ_CONTINUOUS_MAP_EQ = `!m1 m2 f g.
      (!x. x IN mspace m1 ==> f x = g x) /\ lipschitz_continuous_map (m1,m2) f
      ==> lipschitz_continuous_map (m1,m2) g`;;

let LIPSCHITZ_CONTINUOUS_MAP_FROM_SUBMETRIC = `!m1 m2 s f:A->B.
        lipschitz_continuous_map (m1,m2) f
        ==> lipschitz_continuous_map (submetric m1 s,m2) f`;;

let LIPSCHITZ_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO = `!m1 m2 f s t.
           lipschitz_continuous_map (submetric m1 t,m2) f /\ s SUBSET t
           ==> lipschitz_continuous_map (submetric m1 s,m2) f`;;

let LIPSCHITZ_CONTINUOUS_MAP_INTO_SUBMETRIC = `!m1 m2 s f:A->B.
        lipschitz_continuous_map (m1,submetric m2 s) f <=>
        IMAGE f (mspace m1) SUBSET s /\
        lipschitz_continuous_map (m1,m2) f`;;

let LIPSCHITZ_CONTINUOUS_MAP_CONST = `!m1:A metric m2:B metric c.
        lipschitz_continuous_map (m1,m2) (\x. c) <=>
        mspace m1 = {} \/ c IN mspace m2`;;

let LIPSCHITZ_CONTINUOUS_MAP_ID = `!m1:A metric. lipschitz_continuous_map (m1,m1) (\x. x)`;;

let LIPSCHITZ_CONTINUOUS_MAP_COMPOSE = `!m1 m2 m3 f:A->B g:B->C.
      lipschitz_continuous_map (m1,m2) f /\ lipschitz_continuous_map (m2,m3) g
      ==> lipschitz_continuous_map (m1,m3) (g o f)`;;

let uniformly_continuous_map = new_definition
 `uniformly_continuous_map (m1,m2) f <=>
        IMAGE f (mspace m1) SUBSET mspace m2 /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN mspace m1 /\ x' IN mspace m1 /\
                           mdist m1 (x',x) < d
                           ==> mdist m2 (f x',f x) < e`;;

let UNIFORMLY_CONTINUOUS_MAP_SEQUENTIALLY = `(!m1 m2 f:A->B.
        uniformly_continuous_map (m1,m2) f <=>
        IMAGE f (mspace m1) SUBSET mspace m2 /\
        !x y. (!n. x n IN mspace m1) /\ (!n. y n IN mspace m1) /\
              limit euclideanreal (\n. mdist m1 (x n,y n)) (&0) sequentially
              ==> limit euclideanreal
                    (\n. mdist m2 (f(x n),f(y n))) (&0) sequentially)`
and UNIFORMLY_CONTINUOUS_MAP_SEQUENTIALLY_ALT = `(!m1 m2 f:A->B.
        uniformly_continuous_map (m1,m2) f <=>
        IMAGE f (mspace m1) SUBSET mspace m2 /\
        !e x y. &0 < e /\ (!n. x n IN mspace m1) /\ (!n. y n IN mspace m1) /\
                limit euclideanreal (\n. mdist m1 (x n,y n)) (&0) sequentially
                ==> ?n. mdist m2 (f(x n),f(y n)) < e)`;;

let UNIFORMLY_CONTINUOUS_MAP_EQ = `!m1 m2 f g.
      (!x. x IN mspace m1 ==> f x = g x) /\ uniformly_continuous_map (m1,m2) f
      ==> uniformly_continuous_map (m1,m2) g`;;

let UNIFORMLY_CONTINUOUS_MAP_FROM_SUBMETRIC = `!m1 m2 s f:A->B.
        uniformly_continuous_map (m1,m2) f
        ==> uniformly_continuous_map (submetric m1 s,m2) f`;;

let UNIFORMLY_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO = `!m1 m2 f s t.
           uniformly_continuous_map (submetric m1 t,m2) f /\ s SUBSET t
           ==> uniformly_continuous_map (submetric m1 s,m2) f`;;

let UNIFORMLY_CONTINUOUS_MAP_INTO_SUBMETRIC = `!m1 m2 s f:A->B.
        uniformly_continuous_map (m1,submetric m2 s) f <=>
        IMAGE f (mspace m1) SUBSET s /\
        uniformly_continuous_map (m1,m2) f`;;

let UNIFORMLY_CONTINUOUS_MAP_CONST = `!m1:A metric m2:B metric c.
        uniformly_continuous_map (m1,m2) (\x. c) <=>
        mspace m1 = {} \/ c IN mspace m2`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_CONST = `!m. uniformly_continuous_map (m,real_euclidean_metric) (\x:A. c)`;;

let UNIFORMLY_CONTINUOUS_MAP_ID = `!m1:A metric. uniformly_continuous_map (m1,m1) (\x. x)`;;

let UNIFORMLY_CONTINUOUS_MAP_COMPOSE = `!m1 m2 f:A->B g:B->C.
    uniformly_continuous_map (m1,m2) f /\ uniformly_continuous_map (m2,m3) g
    ==> uniformly_continuous_map (m1,m3) (g o f)`;;

let cauchy_continuous_map = new_definition
 `cauchy_continuous_map (m1,m2) f <=>
        !x. cauchy_in m1 x ==> cauchy_in m2 (f o x)`;;

let CAUCHY_CONTINUOUS_MAP_IMAGE = `!m1 m2 f:A->B.
        cauchy_continuous_map (m1,m2) f
        ==> IMAGE f (mspace m1) SUBSET mspace m2`;;

let CAUCHY_CONTINUOUS_MAP_EQ = `!m1 m2 f g.
      (!x. x IN mspace m1 ==> f x = g x) /\ cauchy_continuous_map (m1,m2) f
      ==> cauchy_continuous_map (m1,m2) g`;;

let CAUCHY_CONTINUOUS_MAP_FROM_SUBMETRIC = `!m1 m2 s f:A->B.
        cauchy_continuous_map (m1,m2) f
        ==> cauchy_continuous_map (submetric m1 s,m2) f`;;

let CAUCHY_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO = `!m1 m2 f s t.
           cauchy_continuous_map (submetric m1 t,m2) f /\ s SUBSET t
           ==> cauchy_continuous_map (submetric m1 s,m2) f`;;

let CAUCHY_CONTINUOUS_MAP_INTO_SUBMETRIC = `!m1 m2 s f:A->B.
        cauchy_continuous_map (m1,submetric m2 s) f <=>
        IMAGE f (mspace m1) SUBSET s /\
        cauchy_continuous_map (m1,m2) f`;;

let CAUCHY_CONTINUOUS_MAP_CONST = `!m1:A metric m2:B metric c.
        cauchy_continuous_map (m1,m2) (\x. c) <=>
        mspace m1 = {} \/ c IN mspace m2`;;

let CAUCHY_CONTINUOUS_MAP_REAL_CONST = `!m. cauchy_continuous_map (m,real_euclidean_metric) (\x:A. c)`;;

let CAUCHY_CONTINUOUS_MAP_ID = `!m1:A metric. cauchy_continuous_map (m1,m1) (\x. x)`;;

let CAUCHY_CONTINUOUS_MAP_COMPOSE = `!m1 m2 f:A->B g:B->C.
    cauchy_continuous_map (m1,m2) f /\ cauchy_continuous_map (m2,m3) g
    ==> cauchy_continuous_map (m1,m3) (g o f)`;;

let LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        lipschitz_continuous_map (m1,m2) f
        ==> uniformly_continuous_map (m1,m2) f`;;

let UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        uniformly_continuous_map (m1,m2) f
        ==> cauchy_continuous_map (m1,m2) f`;;

let LOCALLY_CAUCHY_CONTINUOUS_MAP = `!m1 m2 e f:A->B.
        &0 < e /\
        (!x. x IN mspace m1
             ==> cauchy_continuous_map (submetric m1 (mball m1 (x,e)),m2) f)
        ==> cauchy_continuous_map (m1,m2) f`;;

let CAUCHY_CONTINUOUS_IMP_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        cauchy_continuous_map (m1,m2) f
        ==> continuous_map (mtopology m1,mtopology m2) f`;;

let UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        uniformly_continuous_map (m1,m2) f
        ==> continuous_map (mtopology m1,mtopology m2) f`;;

let LIPSCHITZ_CONTINUOUS_IMP_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        lipschitz_continuous_map(m1,m2) f
        ==> continuous_map (mtopology m1,mtopology m2) f`;;

let LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        lipschitz_continuous_map(m1,m2) f
        ==> cauchy_continuous_map(m1,m2) f`;;

let CONTINUOUS_IMP_CAUCHY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        mcomplete m1 /\
        continuous_map (mtopology m1,mtopology m2) f
        ==> cauchy_continuous_map (m1,m2) f`;;

let CAUCHY_IMP_UNIFORMLY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        totally_bounded_in m1 (mspace m1) /\
        cauchy_continuous_map (m1,m2) f
        ==> uniformly_continuous_map (m1,m2) f`;;

let CONTINUOUS_IMP_UNIFORMLY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        compact_space (mtopology m1) /\
        continuous_map (mtopology m1,mtopology m2) f
        ==> uniformly_continuous_map (m1,m2) f`;;

let CONTINUOUS_EQ_CAUCHY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        mcomplete m1
        ==> (continuous_map (mtopology m1,mtopology m2) f <=>
             cauchy_continuous_map (m1,m2) f)`;;

let CONTINUOUS_EQ_UNIFORMLY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        compact_space (mtopology m1)
        ==> (continuous_map (mtopology m1,mtopology m2) f <=>
             uniformly_continuous_map (m1,m2) f)`;;

let CAUCHY_EQ_UNIFORMLY_CONTINUOUS_MAP = `!m1 m2 f:A->B.
        totally_bounded_in m1 (mspace m1)
        ==> (cauchy_continuous_map (m1,m2) f <=>
             uniformly_continuous_map (m1,m2) f)`;;

let LIPSCHITZ_CONTINUOUS_MAP_PROJECTIONS = `(!m1:A metric m2:B metric.
        lipschitz_continuous_map (prod_metric m1 m2,m1) FST) /\
   (!m1:A metric m2:B metric.
        lipschitz_continuous_map (prod_metric m1 m2,m2) SND)`;;

let LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE = `!m m1 m2 (f:A->B#C).
        lipschitz_continuous_map(m,prod_metric m1 m2) f <=>
        lipschitz_continuous_map(m,m1) (FST o f) /\
        lipschitz_continuous_map(m,m2) (SND o f)`;;

let UNIFORMLY_CONTINUOUS_MAP_PAIRWISE = `!m m1 m2 (f:A->B#C).
        uniformly_continuous_map(m,prod_metric m1 m2) f <=>
        uniformly_continuous_map(m,m1) (FST o f) /\
        uniformly_continuous_map(m,m2) (SND o f)`;;

let CAUCHY_CONTINUOUS_MAP_PAIRWISE = `!m m1 m2 (f:A->B#C).
        cauchy_continuous_map(m,prod_metric m1 m2) f <=>
        cauchy_continuous_map(m,m1) (FST o f) /\
        cauchy_continuous_map(m,m2) (SND o f)`;;

let LIPSCHITZ_CONTINUOUS_MAP_PAIRED = `!m m1 m2 (f:A->B) (g:A->C).
        lipschitz_continuous_map (m,prod_metric m1 m2) (\x. f x,g x) <=>
        lipschitz_continuous_map(m,m1) f /\ lipschitz_continuous_map(m,m2) g`;;

let UNIFORMLY_CONTINUOUS_MAP_PAIRED = `!m m1 m2 (f:A->B) (g:A->C).
        uniformly_continuous_map (m,prod_metric m1 m2) (\x. f x,g x) <=>
        uniformly_continuous_map(m,m1) f /\ uniformly_continuous_map(m,m2) g`;;

let CAUCHY_CONTINUOUS_MAP_PAIRED = `!m m1 m2 (f:A->B) (g:A->C).
        cauchy_continuous_map (m,prod_metric m1 m2) (\x. f x,g x) <=>
        cauchy_continuous_map(m,m1) f /\ cauchy_continuous_map(m,m2) g`;;

let MBOUNDED_LIPSCHITZ_CONTINUOUS_IMAGE = `!m1 m2 (f:A->B) s.
        lipschitz_continuous_map (m1,m2) f /\ mbounded m1 s
        ==> mbounded m2 (IMAGE f s)`;;

let TOTALLY_BOUNDED_IN_CAUCHY_CONTINUOUS_IMAGE = `!m1 m2 (f:A->B) s.
        cauchy_continuous_map (m1,m2) f /\ totally_bounded_in m1 s
        ==> totally_bounded_in m2 (IMAGE f s)`;;

let LIPSCHITZ_COEFFICIENT_POS = `!m m' f:A->B k.
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m' (f x,f y) <= k * mdist m (x,y)) /\
     (?x y. x IN mspace m /\ y IN mspace m /\ ~(f x = f y))
     ==> &0 < k`;;

let LIPSCHITZ_CONTINUOUS_MAP_METRIC = `!m:A metric.
        lipschitz_continuous_map
          (prod_metric m m,real_euclidean_metric)
          (mdist m)`;;

let LIPSCHITZ_CONTINUOUS_MAP_MDIST = `!m m' (f:A->B) g.
      lipschitz_continuous_map (m,m') f /\
      lipschitz_continuous_map (m,m') g
      ==> lipschitz_continuous_map (m,real_euclidean_metric)
             (\x. mdist m' (f x,g x))`;;

let UNIFORMLY_CONTINUOUS_MAP_MDIST = `!m m' (f:A->B) g.
      uniformly_continuous_map (m,m') f /\
      uniformly_continuous_map (m,m') g
      ==> uniformly_continuous_map (m,real_euclidean_metric)
             (\x. mdist m' (f x,g x))`;;

let CAUCHY_CONTINUOUS_MAP_MDIST = `!m m' (f:A->B) g.
      cauchy_continuous_map (m,m') f /\
      cauchy_continuous_map (m,m') g
      ==> cauchy_continuous_map (m,real_euclidean_metric)
             (\x. mdist m' (f x,g x))`;;

let CONTINUOUS_MAP_METRIC = `!m:A metric.
        continuous_map (prod_topology (mtopology m) (mtopology m),
                        euclideanreal)
                       (mdist m)`;;

let CONTINUOUS_MAP_MDIST_ALT = `!m f:A->B#B.
        continuous_map (top,prod_topology (mtopology m) (mtopology m)) f
        ==> continuous_map (top,euclideanreal) (\x. mdist m (f x))`;;

let CONTINUOUS_MAP_MDIST = `!top m f g:A->B.
        continuous_map (top,mtopology m) f /\
        continuous_map (top,mtopology m) g
        ==> continuous_map (top,euclideanreal) (\x. mdist m (f x,g x))`;;

let CONTINUOUS_ON_MDIST = `!m a. a:A IN mspace m
         ==> continuous_map (mtopology m,euclideanreal) (\x. mdist m (a,x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION = `!c. lipschitz_continuous_map(real_euclidean_metric,real_euclidean_metric)
         (\x. c * x)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_RIGHT_MULTIPLICATION = `!c. lipschitz_continuous_map(real_euclidean_metric,real_euclidean_metric)
         (\x. x * c)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_NEGATION = `lipschitz_continuous_map(real_euclidean_metric,real_euclidean_metric) (--)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_ABSOLUTE_VALUE = `lipschitz_continuous_map(real_euclidean_metric,real_euclidean_metric) abs`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_ADDITION = `lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\(x,y). x + y)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_SUBTRACTION = `lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\(x,y). x - y)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_MAXIMUM = `lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\(x,y). max x y)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_MINIMUM = `lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\(x,y). min x y)`;;

let LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_MULTIPLICATION = `!s. mbounded (prod_metric real_euclidean_metric real_euclidean_metric) s
       ==> lipschitz_continuous_map
            (submetric
              (prod_metric real_euclidean_metric real_euclidean_metric) s,
             real_euclidean_metric)
            (\(x,y). x * y)`;;

let CAUCHY_CONTINUOUS_MAP_REAL_MULTIPLICATION = `cauchy_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\(x,y). x * y)`;;

let LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_INVERSION = `!s. ~(&0 IN euclideanreal closure_of s)
       ==> lipschitz_continuous_map
             (submetric real_euclidean_metric s,real_euclidean_metric)
             inv`;;

let LIPSCHITZ_CONTINUOUS_MAP_FST = `!m m1 m2 f:A->B#C.
        lipschitz_continuous_map(m,prod_metric m1 m2) f
        ==> lipschitz_continuous_map(m,m1) (\x. FST(f x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_SND = `!m m1 m2 f:A->B#C.
        lipschitz_continuous_map(m,prod_metric m1 m2) f
        ==> lipschitz_continuous_map(m,m2) (\x. SND(f x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_LMUL = `!m c f:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. c * f x)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_RMUL = `!m c f:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. f x * c)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_NEG = `!m f:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. --(f x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_ABS = `!m f:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. abs(f x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_INV = `!m f:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f /\
      ~(&0 IN euclideanreal closure_of (IMAGE f (mspace m)))
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. inv(f x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_ADD = `!m f g:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f /\
      lipschitz_continuous_map (m,real_euclidean_metric) g
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. f x + g x)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_SUB = `!m f g:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f /\
      lipschitz_continuous_map (m,real_euclidean_metric) g
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. f x - g x)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_MAX = `!m f g:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f /\
      lipschitz_continuous_map (m,real_euclidean_metric) g
      ==> lipschitz_continuous_map (m,real_euclidean_metric)
            (\x. max (f x) (g x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_MIN = `!m f g:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f /\
      lipschitz_continuous_map (m,real_euclidean_metric) g
      ==> lipschitz_continuous_map (m,real_euclidean_metric)
            (\x. min (f x) (g x))`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_MUL = `!m f g:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f /\
      lipschitz_continuous_map (m,real_euclidean_metric) g /\
      real_bounded (IMAGE f (mspace m)) /\ real_bounded (IMAGE g (mspace m))
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. f x * g x)`;;

let LIPSCHITZ_CONTINUOUS_MAP_REAL_DIV = `!m f g:A->real.
      lipschitz_continuous_map (m,real_euclidean_metric) f /\
      lipschitz_continuous_map (m,real_euclidean_metric) g /\
      real_bounded (IMAGE f (mspace m)) /\
      ~(&0 IN euclideanreal closure_of (IMAGE g (mspace m)))
      ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. f x / g x)`;;

let LIPSCHITZ_CONTINUOUS_MAP_SUM = `!m f:K->A->real k.
      FINITE k /\
      (!i. i IN k
          ==> lipschitz_continuous_map (m,real_euclidean_metric) (\x. f x i))
      ==> lipschitz_continuous_map (m,real_euclidean_metric)
                (\x. sum k (f x))`;;

let UNIFORMLY_CONTINUOUS_MAP_FST = `!m m1 m2 f:A->B#C.
        uniformly_continuous_map(m,prod_metric m1 m2) f
        ==> uniformly_continuous_map(m,m1) (\x. FST(f x))`;;

let UNIFORMLY_CONTINUOUS_MAP_SND = `!m m1 m2 f:A->B#C.
        uniformly_continuous_map(m,prod_metric m1 m2) f
        ==> uniformly_continuous_map(m,m2) (\x. SND(f x))`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_LMUL = `!m c f:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. c * f x)`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_RMUL = `!m c f:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. f x * c)`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_NEG = `!m f:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. --(f x))`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_ABS = `!m f:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. abs(f x))`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_INV = `!m f:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f /\
      ~(&0 IN euclideanreal closure_of (IMAGE f (mspace m)))
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. inv(f x))`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_ADD = `!m f g:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f /\
      uniformly_continuous_map (m,real_euclidean_metric) g
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. f x + g x)`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_SUB = `!m f g:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f /\
      uniformly_continuous_map (m,real_euclidean_metric) g
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. f x - g x)`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_MAX = `!m f g:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f /\
      uniformly_continuous_map (m,real_euclidean_metric) g
     ==> uniformly_continuous_map (m,real_euclidean_metric)
            (\x. max (f x) (g x))`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_MIN = `!m f g:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f /\
      uniformly_continuous_map (m,real_euclidean_metric) g
     ==> uniformly_continuous_map (m,real_euclidean_metric)
            (\x. min (f x) (g x))`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_MUL = `!m f g:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f /\
      uniformly_continuous_map (m,real_euclidean_metric) g /\
      real_bounded (IMAGE f (mspace m)) /\ real_bounded (IMAGE g (mspace m))
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. f x * g x)`;;

let UNIFORMLY_CONTINUOUS_MAP_REAL_DIV = `!m f g:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f /\
      uniformly_continuous_map (m,real_euclidean_metric) g /\
      real_bounded (IMAGE f (mspace m)) /\
      ~(&0 IN euclideanreal closure_of (IMAGE g (mspace m)))
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. f x / g x)`;;

let UNIFORMLY_CONTINUOUS_MAP_SUM = `!m f:K->A->real k.
      FINITE k /\
      (!i. i IN k
          ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. f x i))
      ==> uniformly_continuous_map (m,real_euclidean_metric)
                (\x. sum k (f x))`;;

let CAUCHY_CONTINUOUS_MAP_FST = `!m m1 m2 f:A->B#C.
        cauchy_continuous_map(m,prod_metric m1 m2) f
        ==> cauchy_continuous_map(m,m1) (\x. FST(f x))`;;

let CAUCHY_CONTINUOUS_MAP_SND = `!m m1 m2 f:A->B#C.
        cauchy_continuous_map(m,prod_metric m1 m2) f
        ==> cauchy_continuous_map(m,m2) (\x. SND(f x))`;;

let CAUCHY_CONTINUOUS_MAP_REAL_INV = `!m f:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f /\
      ~(&0 IN euclideanreal closure_of (IMAGE f (mspace m)))
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. inv(f x))`;;

let CAUCHY_CONTINUOUS_MAP_REAL_ADD = `!m f g:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f /\
      cauchy_continuous_map (m,real_euclidean_metric) g
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. f x + g x)`;;

let CAUCHY_CONTINUOUS_MAP_REAL_MUL = `!m f g:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f /\
      cauchy_continuous_map (m,real_euclidean_metric) g
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. f x * g x)`;;

let CAUCHY_CONTINUOUS_MAP_REAL_LMUL = `!m c f:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. c * f x)`;;

let CAUCHY_CONTINUOUS_MAP_REAL_RMUL = `!m c f:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. f x * c)`;;

let CAUCHY_CONTINUOUS_MAP_REAL_POW = `!m (f:A->real) n.
        cauchy_continuous_map (m,real_euclidean_metric) f
        ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. f x pow n)`;;

let CAUCHY_CONTINUOUS_MAP_REAL_NEG = `!m f:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. --(f x))`;;

let CAUCHY_CONTINUOUS_MAP_REAL_ABS = `!m f:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. abs(f x))`;;

let CAUCHY_CONTINUOUS_MAP_REAL_SUB = `!m f g:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f /\
      cauchy_continuous_map (m,real_euclidean_metric) g
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. f x - g x)`;;

let CAUCHY_CONTINUOUS_MAP_REAL_MAX = `!m f g:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f /\
      cauchy_continuous_map (m,real_euclidean_metric) g
    ==> cauchy_continuous_map (m,real_euclidean_metric)
            (\x. max (f x) (g x))`;;

let CAUCHY_CONTINUOUS_MAP_REAL_MIN = `!m f g:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f /\
      cauchy_continuous_map (m,real_euclidean_metric) g
    ==> cauchy_continuous_map (m,real_euclidean_metric)
            (\x. min (f x) (g x))`;;

let CAUCHY_CONTINUOUS_MAP_REAL_DIV = `!m f g:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f /\
      cauchy_continuous_map (m,real_euclidean_metric) g /\
      ~(&0 IN euclideanreal closure_of (IMAGE g (mspace m)))
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. f x / g x)`;;

let CAUCHY_CONTINUOUS_MAP_SUM = `!m f:K->A->real k.
      FINITE k /\
      (!i. i IN k
          ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. f x i))
      ==> cauchy_continuous_map (m,real_euclidean_metric)
                (\x. sum k (f x))`;;

let UNIFORMLY_CONTINUOUS_MAP_SQUARE_ROOT = `uniformly_continuous_map(real_euclidean_metric,real_euclidean_metric) sqrt`;;

let CONTINUOUS_MAP_SQUARE_ROOT = `continuous_map(euclideanreal,euclideanreal) sqrt`;;

let UNIFORMLY_CONTINUOUS_MAP_SQRT = `!m f:A->real.
      uniformly_continuous_map (m,real_euclidean_metric) f
      ==> uniformly_continuous_map (m,real_euclidean_metric) (\x. sqrt(f x))`;;

let CAUCHY_CONTINUOUS_MAP_SQRT = `!m f:A->real.
      cauchy_continuous_map (m,real_euclidean_metric) f
      ==> cauchy_continuous_map (m,real_euclidean_metric) (\x. sqrt(f x))`;;

let CONTINUOUS_MAP_SQRT = `!top f:A->real.
        continuous_map (top,euclideanreal) f
        ==> continuous_map (top,euclideanreal) (\x. sqrt(f x))`;;

let ISOMETRY_IMP_EMBEDDING_MAP = `!m m' (f:A->B).
        IMAGE f (mspace m) SUBSET mspace m' /\
        (!x y. x IN mspace m /\ y IN mspace m
               ==> mdist m' (f x,f y) = mdist m (x,y))
        ==> embedding_map(mtopology m,mtopology m') f`;;

let ISOMETRY_IMP_HOMEOMORPHIC_MAP = `!m m' (f:A->B).
        IMAGE f (mspace m) = mspace m' /\
        (!x y. x IN mspace m /\ y IN mspace m
               ==> mdist m' (f x,f y) = mdist m (x,y))
        ==> homeomorphic_map(mtopology m,mtopology m') f`;;

(* ------------------------------------------------------------------------- *)
(* Extending continuous maps "pointwise" in a regular space.                 *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE_OF = `!top top' f:A->B s t.
       regular_space top' /\
       t SUBSET top closure_of s /\
       (!x. x IN t ==> limit top' f (f x) (atpointof top x within s))
       ==> continuous_map (subtopology top t,top') f`;;

let CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE_OF_EQ = `!top top' f:A->B s t.
        regular_space top' /\ s SUBSET t /\ t SUBSET top closure_of s
        ==> (continuous_map (subtopology top t,top') f <=>
             !x. x IN t ==> limit top' f (f x) (atpointof top x within s))`;;

let CONTINUOUS_MAP_EXTENSION_POINTWISE_ALT = `!top1 top2 f:A->B s t.
        regular_space top2 /\ s SUBSET t /\ t SUBSET top1 closure_of s /\
        continuous_map (subtopology top1 s,top2) f /\
        (!x. x IN t DIFF s ==> ?l. limit top2 f l (atpointof top1 x within s))
        ==> ?g. continuous_map (subtopology top1 t,top2) g /\
                (!x. x IN s ==> g x = f x)`;;

let CONTINUOUS_MAP_EXTENSION_POINTWISE = `!top1 top2 f:A->B s t.
        regular_space top2 /\ s SUBSET t /\ t SUBSET top1 closure_of s /\
        (!x. x IN t
             ==> ?g. continuous_map (subtopology top1 (x INSERT s),top2) g /\
                     !x. x IN s ==> g x = f x)
        ==> ?g. continuous_map (subtopology top1 t,top2) g /\
                (!x. x IN s ==> g x = f x)`;;

(* ------------------------------------------------------------------------- *)
(* Extending Cauchy continuous functions to the closure.                     *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF = `!m1 m2 (f:A->B) s.
        mcomplete m2 /\ cauchy_continuous_map (submetric m1 s,m2) f
        ==> ?g. continuous_map
                 (subtopology (mtopology m1) (mtopology m1 closure_of s),
                  mtopology m2) g /\
                !x. x IN s ==> g x = f x`;;

let CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_INTERMEDIATE_CLOSURE_OF = `!m1 m2 (f:A->B) s t.
        mcomplete m2 /\ cauchy_continuous_map (submetric m1 s,m2) f /\
        t SUBSET mtopology m1 closure_of s
        ==> ?g. continuous_map(subtopology (mtopology m1) t,mtopology m2) g /\
                !x. x IN s ==> g x = f x`;;

let LIPSCHITZ_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE = `!m1 m2 f:A->B s t.
        s SUBSET t /\ t SUBSET (mtopology m1) closure_of s /\
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f /\
        lipschitz_continuous_map (submetric m1 s,m2) f
        ==> lipschitz_continuous_map (submetric m1 t,m2) f`;;

let LIPSCHITZ_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF = `!m1 m2 (f:A->B) s.
        mcomplete m2 /\ lipschitz_continuous_map (submetric m1 s,m2) f
        ==> ?g. lipschitz_continuous_map
                   (submetric m1 (mtopology m1 closure_of s),m2) g /\
                !x. x IN s ==> g x = f x`;;

let LIPSCHITZ_CONTINUOUS_MAP_EXTENDS_TO_INTERMEDIATE_CLOSURE_OF = `!m1 m2 (f:A->B) s t.
        mcomplete m2 /\
        lipschitz_continuous_map (submetric m1 s,m2) f /\
        t SUBSET mtopology m1 closure_of s
        ==> ?g. lipschitz_continuous_map (submetric m1 t,m2) g /\
                !x. x IN s ==> g x = f x`;;

let UNIFORMLY_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE = `!m1 m2 f:A->B s t.
        s SUBSET t /\ t SUBSET (mtopology m1) closure_of s /\
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f /\
        uniformly_continuous_map (submetric m1 s,m2) f
        ==> uniformly_continuous_map (submetric m1 t,m2) f`;;

let UNIFORMLY_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF = `!m1 m2 (f:A->B) s.
        mcomplete m2 /\ uniformly_continuous_map (submetric m1 s,m2) f
        ==> ?g. uniformly_continuous_map
                   (submetric m1 (mtopology m1 closure_of s),m2) g /\
                !x. x IN s ==> g x = f x`;;

let UNIFORMLY_CONTINUOUS_MAP_EXTENDS_TO_INTERMEDIATE_CLOSURE_OF = `!m1 m2 (f:A->B) s t.
        mcomplete m2 /\
        uniformly_continuous_map (submetric m1 s,m2) f /\
        t SUBSET mtopology m1 closure_of s
        ==> ?g. uniformly_continuous_map (submetric m1 t,m2) g /\
                !x. x IN s ==> g x = f x`;;

let CAUCHY_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE = `!m1 m2 f:A->B s t.
        s SUBSET t /\ t SUBSET (mtopology m1) closure_of s /\
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f /\
        cauchy_continuous_map (submetric m1 s,m2) f
        ==> cauchy_continuous_map (submetric m1 t,m2) f`;;

let CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF = `!m1 m2 (f:A->B) s.
        mcomplete m2 /\ cauchy_continuous_map (submetric m1 s,m2) f
        ==> ?g. cauchy_continuous_map
                   (submetric m1 (mtopology m1 closure_of s),m2) g /\
                !x. x IN s ==> g x = f x`;;

let CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_INTERMEDIATE_CLOSURE_OF = `!m1 m2 (f:A->B) s t.
        mcomplete m2 /\
        cauchy_continuous_map (submetric m1 s,m2) f /\
        t SUBSET mtopology m1 closure_of s
        ==> ?g. cauchy_continuous_map (submetric m1 t,m2) g /\
                !x. x IN s ==> g x = f x`;;

(* ------------------------------------------------------------------------- *)
(* Lavrentiev extension etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let CONVERGENT_EQ_ZERO_OSCILLATION_GEN = `!top m (f:A->B) s a.
        mcomplete m /\ IMAGE f (topspace top INTER s) SUBSET mspace m
        ==> ((?l. limit (mtopology m) f l (atpointof top a within s)) <=>
             ~(mspace m = {}) /\
             (a IN topspace top
              ==> !e. &0 < e
                      ==> ?u. open_in top u /\ a IN u /\
                              !x y. x IN (s INTER u) DELETE a /\
                                    y IN (s INTER u) DELETE a
                                    ==> mdist m (f x,f y) < e))`;;

let GDELTA_IN_POINTS_OF_CONVERGENCE_WITHIN = `!top top' (f:A->B) s.
        completely_metrizable_space top' /\
        (continuous_map (subtopology top s,top') f \/
         t1_space top /\ IMAGE f s SUBSET topspace top')
        ==> gdelta_in top
             {x | x IN topspace top /\
                  ?l. limit top' f l (atpointof top x within s)}`;;

let LAVRENTIEV_EXTENSION_GEN = `!top s top' (f:A->B).
        s SUBSET topspace top /\
        completely_metrizable_space top' /\
        continuous_map(subtopology top s,top') f
        ==> ?u g. gdelta_in top u /\
                  s SUBSET u /\
                  continuous_map
                     (subtopology top (top closure_of s INTER u),top') g /\
                  !x. x IN s ==> g x = f x`;;

let LAVRENTIEV_EXTENSION = `!top s top' (f:A->B).
        s SUBSET topspace top /\
        (metrizable_space top \/ topspace top SUBSET top closure_of s) /\
        completely_metrizable_space top' /\
        continuous_map(subtopology top s,top') f
        ==> ?u g. gdelta_in top u /\
                  s SUBSET u /\
                  u SUBSET top closure_of s /\
                  continuous_map(subtopology top u,top') g /\
                  !x. x IN s ==> g x = f x`;;

(* ------------------------------------------------------------------------- *)
(* Diameter of a set in a metric space.                                      *)
(* ------------------------------------------------------------------------- *)

let mdiameter = new_definition
  `mdiameter (m:A metric) (s:A->bool) =
   if s = {} then &0
   else sup {mdist m (x,y) | x IN s /\ y IN s}`;;

let MDIAMETER_EMPTY = `!m:A metric. mdiameter m {} = &0`;;

let MDIAMETER_SING = `!m:A metric. !x. x IN mspace m ==> mdiameter m {x} = &0`;;

let MDIAMETER_POS_LE = `!m s:A->bool. mbounded m s ==> &0 <= mdiameter m s`;;

let MDIAMETER_BOUNDED = `!m s:A->bool.
     mbounded m s
     ==> (!x y. x IN s /\ y IN s ==> mdist m (x,y) <= mdiameter m s) /\
         (!d. &0 <= d /\ d < mdiameter m s
              ==> ?x y. x IN s /\ y IN s /\ mdist m (x,y) > d)`;;

let MDIAMETER_BOUNDED_BOUND = `!m s:A->bool x y.
     mbounded m s /\ x IN s /\ y IN s
     ==> mdist m (x,y) <= mdiameter m s`;;

let MDIAMETER_LE = `!m s:A->bool d.
     s SUBSET mspace m /\
     (~(s = {}) \/ &0 <= d) /\
     (!x y. x IN s /\ y IN s ==> mdist m (x,y) <= d)
     ==> mdiameter m s <= d`;;

let MBOUNDED_AND_MDIAMETER_LE = `!m (s:A->bool) r.
        s SUBSET mspace m
        ==> (mbounded m s /\ mdiameter m s <= r <=>
             &0 <= r /\ !x y. x IN s /\ y IN s ==> mdist m(x,y) <= r)`;;

let MDIAMETER_SUBSET = `!m s t:A->bool.
     s SUBSET t /\ mbounded m t ==> mdiameter m s <= mdiameter m t`;;

let MBOUNDED_IMP_IN_MSPACE = `!m:A metric s x. mbounded m s /\ x IN s ==> x IN mspace m`;;

let MDIAMETER_CLOSURE = `!m s:A->bool.
     mbounded m s
     ==> mdiameter m (mtopology m closure_of s) = mdiameter m s`;;

let MDIAMETER_COMPACT_ATTAINED = `!m:A metric s.
     compact_in (mtopology m) s /\ ~(s = {})
     ==> ?x y. x IN s /\ y IN s /\ mdist m (x,y) = mdiameter m s`;;

let MDIAMETER_SUBSET_MCBALL_NONEMPTY = `!m:A metric s.
     mbounded m s /\ ~(s = {})
     ==> ?z. z IN s /\ s SUBSET mcball m (z,mdiameter m s)`;;

let MDIAMETER_SUBSET_MCBALL = `!m:A metric s.
     mbounded m s ==> ?z. s SUBSET mcball m (z,mdiameter m s)`;;

let MDIAMETER_EQ_0 = `!m:A metric s.
     mbounded m s
     ==> (mdiameter m s = &0 <=> s = {} \/ ?a. s = {a})`;;

let MDIAMETER_UNION_LE = `!m:A metric s t.
     mbounded m s /\ mbounded m t /\ ~(s INTER t = {})
     ==> mdiameter m (s UNION t) <= mdiameter m s + mdiameter m t`;;

(* ------------------------------------------------------------------------- *)
(* Submetric preserves mdiameter (mdist is the same).                        *)
(* ------------------------------------------------------------------------- *)

let MDIAMETER_SUBMETRIC = `!m:A metric s t. mdiameter (submetric m s) t = mdiameter m t`;;

let LEBESGUE_COVERING_LEMMA = `!m:A metric s c.
     compact_in (mtopology m) s /\ ~(c = {}) /\
     s SUBSET UNIONS c /\ (!b. b IN c ==> open_in (mtopology m) b)
     ==> ?d. &0 < d /\
             !t. t SUBSET s /\ mdiameter m t <= d
                 ==> ?b. b IN c /\ t SUBSET b`;;

let LEBESGUE_COVERING_LEMMA_GEN = `!m:A metric u s c.
     compact_in (mtopology m) s /\ ~(c = {}) /\
     s SUBSET UNIONS c /\
     (!b. b IN c ==> open_in (subtopology (mtopology m) u) b)
     ==> ?d. &0 < d /\
             !t. t SUBSET s /\ mdiameter m t <= d
                 ==> ?b. b IN c /\ t SUBSET b`;;

(* ------------------------------------------------------------------------- *)
(* Well-chained sets in metric spaces (epsilon-chains).                      *)
(* Generalizes the Euclidean well-chained theory from paths.ml.              *)
(* ------------------------------------------------------------------------- *)

let WELLCHAINED_ELEMENTS = `!m:A metric s a (b:A) e.
        (?p n. p 0 = a /\ p n = b /\
               (!i. i <= n ==> p i IN s) /\
               (!i. i < n ==> mdist m (p i,p(SUC i)) < e)) <=>
        a IN s /\ b IN s /\
        (!c. c SUBSET s /\ a IN c /\
             (!x y. x IN c /\ y IN s /\ mdist m (x,y) < e ==> y IN c)
             ==> b IN c)`;;

let WELLCHAINED_SETS = `!m:A metric s e.
     (!a b. a IN s /\ b IN s
            ==> ?p n. p 0 = a /\ p n = b /\
                      (!i. i <= n ==> p i IN s) /\
                      (!i. i < n ==> mdist m (p i,p(SUC i)) < e)) <=>
     (!c. c SUBSET s /\ ~(c = {}) /\
          (!x y. x IN c /\ y IN s /\ mdist m (x,y) < e ==> y IN c)
          ==> c = s)`;;

(* Helper: epsilon-absorbing subsets are clopen in subtopology *)
let EPSILON_ABSORBING_IMP_CLOPEN =
 `!m:A metric s c e.
     s SUBSET mspace m /\ c SUBSET s /\ &0 < e /\
     (!x y. x IN c /\ y IN s /\ mdist m (x,y) < e ==> y IN c)
     ==> open_in (subtopology (mtopology m) s) c /\
         closed_in (subtopology (mtopology m) s) c`;;

let CONNECTED_IN_IMP_WELLCHAINED = `!m:A metric s e a b.
        connected_in (mtopology m) s /\ &0 < e /\ a IN s /\ b IN s
        ==> ?p n. p 0 = a /\ p n = b /\
                  (!i. i <= n ==> p i IN s) /\
                  (!i. i < n ==> mdist m (p i,p(SUC i)) < e)`;;

let CONNECTED_COMPONENT_OF_IMP_WELLCHAINED = `!m:A metric s a (b:A) e.
        &0 < e /\ connected_component_of (subtopology (mtopology m) s) a b
        ==> ?p n. p 0 = a /\ p n = b /\
                  (!i. i <= n ==> p i IN s) /\
                  (!i. i < n ==> mdist m (p i,p (SUC i)) < e)`;;

let CONNECTED_EQ_WELLCHAINED_IN = `!m:A metric s.
    compact_in (mtopology m) s
    ==> (connected_in (mtopology m) s <=>
         !e. &0 < e
             ==> !a b. a IN s /\ b IN s
                       ==> ?p n. p 0 = a /\ p n = b /\
                                 (!i. i <= n ==> p i IN s) /\
                                 (!i. i < n ==> mdist m (p i,p(SUC i)) < e))`;;

(* In a compact metric space, connected components = well-chained components.
   Points a and b are in the same connected component of K iff they can be
   epsilon-chained in K for every epsilon > 0. Uses the fact that in compact
   Hausdorff spaces, quasi-components = connected components. *)

let CONNECTED_COMPONENT_OF_EQ_WELLCHAINED = `!m:A metric K a b.
     compact_in (mtopology m) K
     ==> (connected_component_of (subtopology (mtopology m) K) a b <=>
          a IN K /\ b IN K /\
          !e. &0 < e
              ==> ?p n. p 0 = a /\ p n = b /\
                        (!i. i <= n ==> p i IN K) /\
                        (!i. i < n ==> mdist m (p i,p (SUC i)) < e))`;;

(* Helper: for nested compact sets, every point of s(N) is close to k *)
let NESTED_COMPACT_APPROX = `!m:A metric s.
     (!n. compact_in (mtopology m) (s n)) /\
     (!n. s(SUC n) SUBSET s n)
     ==> !e. &0 < e
             ==> ?N. !x. x IN s N
                      ==> ?y. y IN INTERS {s n | n IN (:num)} /\
                               mdist m (x,y) < e`;;

(* Triangle inequality with strict bounds on both legs *)
let MDIST_TRIANGLE_LT = `!m x y z:A a b.
     x IN mspace m /\ y IN mspace m /\ z IN mspace m /\
     mdist m (x,y) < a /\ mdist m (y,z) < b
     ==> mdist m (x,z) < a + b`;;

(* Well-chained inters for nested compact sets *)
let WELLCHAINED_INTERS = `!m:A metric (s:num->A->bool) d e.
      d < e /\
      (!n. compact_in (mtopology m) (s n)) /\
      (!n. s(SUC n) SUBSET s n) /\
      (!n a b.
           a IN s n /\ b IN s n
           ==> ?p k. p 0 = a /\ p k = b /\
                      (!i. i <= k ==> p i IN s n) /\
                      (!i. i < k ==> mdist m (p i,p (SUC i)) < d))
      ==> !a b. a IN INTERS {s n | n IN (:num)} /\
                b IN INTERS {s n | n IN (:num)}
                ==> ?p k. p 0 = a /\ p k = b /\
                          (!i. i <= k ==> p i IN INTERS {s n | n IN (:num)}) /\
                          (!i. i < k ==> mdist m (p i,p (SUC i)) < e)`;;

(* ------------------------------------------------------------------------- *)
(* Uniformly locally connected and Property S for metric spaces              *)
(* ------------------------------------------------------------------------- *)

(* Property S (Fine Connected Coverable): For every e > 0, there exists
   a finite cover of the space by connected sets of diameter <= e *)
let fccoverable_space = new_definition
  `fccoverable_space (m:A metric) <=>
   !e. &0 < e
       ==> ?c. FINITE c /\
               UNIONS c = mspace m /\
               (!t. t IN c
                    ==> connected_in (mtopology m) t /\
                        mbounded m t /\
                        mdiameter m t <= e)`;;

(* Uniformly Locally Connected: For every e > 0, there exists d > 0 such that
   any two points at distance < d can be connected within the space by a
   connected set of diameter <= e *)
let ulc_space = new_definition
  `ulc_space (m:A metric) <=>
   !e. &0 < e
       ==> ?d. &0 < d /\
               !x y. x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < d
                     ==> ?c. x IN c /\ y IN c /\
                             c SUBSET mspace m /\
                             connected_in (mtopology m) c /\
                             mbounded m c /\
                             mdiameter m c <= e`;;

(* Property S for a subset s of the metric space *)
let fccoverable_in = new_definition
  `fccoverable_in (m:A metric) s <=>
   s SUBSET mspace m /\
   !e. &0 < e
       ==> ?c. FINITE c /\
               UNIONS c = s /\
               (!t. t IN c
                    ==> connected_in (mtopology m) t /\
                        mbounded m t /\
                        mdiameter m t <= e)`;;

(* ------------------------------------------------------------------------- *)
(* Main theorems                                                             *)
(* ------------------------------------------------------------------------- *)

(* Helper: if x is in closure of t, then t is contained in a ball around x *)
let IN_CLOSURE_OF_IMP_SUBSET_MCBALL = `!m:A metric x t.
     x IN mspace m /\ mbounded m t /\ x IN mtopology m closure_of t
     ==> t SUBSET mcball m (x, mdiameter m t)`;;

let FCCOVERABLE_SPACE_IMP_LOCALLY_CONNECTED_SPACE = `!m:A metric.
     fccoverable_space m ==> locally_connected_space (mtopology m)`;;

let ULC_SPACE_IMP_LOCALLY_CONNECTED_SPACE = `!m:A metric.
     ulc_space m ==> locally_connected_space (mtopology m)`;;

(* ------------------------------------------------------------------------- *)
(* Property S for intermediate sets between s and closure s                  *)
(* ------------------------------------------------------------------------- *)

let FCCOVERABLE_SPACE_EQ_FCCOVERABLE_IN_MSPACE = `!m:A metric. fccoverable_space m <=> fccoverable_in m (mspace m)`;;

let FCCOVERABLE_SPACE_INTERMEDIATE_CLOSURE = `!m:A metric s t.
     s SUBSET t /\ t SUBSET (mtopology m closure_of s) /\ fccoverable_in m s
     ==> fccoverable_in m t`;;

(* ------------------------------------------------------------------------- *)
(* fccoverable_in is equivalent to fccoverable_space on the submetric.       *)
(* ------------------------------------------------------------------------- *)

let FCCOVERABLE_IN_IMP_FCCOVERABLE_SPACE_SUBMETRIC = `!m:A metric s. fccoverable_in m s ==> fccoverable_space (submetric m s)`;;

(* ------------------------------------------------------------------------- *)
(* fccoverable_in implies locally_connected_space on subtopology             *)
(* ------------------------------------------------------------------------- *)

let FCCOVERABLE_IN_IMP_LOCALLY_CONNECTED_SPACE = `!m:A metric (s:A->bool).
     fccoverable_in m s
     ==> locally_connected_space (subtopology (mtopology m) s)`;;

let MDIAMETER_SUBSET_MBALL = `!m:A metric x r t.
     x IN mspace m /\ &0 < r /\ t SUBSET mball m (x,r)
     ==> mdiameter m t <= &2 * r`;;

(* ------------------------------------------------------------------------- *)
(* Compact + locally connected implies ULC                                   *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IN_LOCALLY_CONNECTED_IMP_ULC_SPACE = `!m:A metric.
     compact_in (mtopology m) (mspace m) /\
     locally_connected_space (mtopology m)
     ==> ulc_space m`;;

(* Alternative: connecting sets lie in balls around both endpoints *)
let COMPACT_IN_LOCALLY_CONNECTED_IMP_ULC_SPACE_ALT = `!m:A metric.
     compact_in (mtopology m) (mspace m) /\
     locally_connected_space (mtopology m)
     ==> !e. &0 < e
             ==> ?d. &0 < d /\ d < e /\
                     !x y. x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < d
                           ==> ?c. connected_in (mtopology m) c /\
                                   x IN c /\ y IN c /\
                                   c SUBSET mspace m INTER mball m (x,e) INTER
                                           mball m (y,e)`;;

(* ------------------------------------------------------------------------- *)
(* Totally bounded + ULC implies Property S                                  *)
(* ------------------------------------------------------------------------- *)

(* Note: For general metric spaces, we need totally_bounded_in rather than
   just mbounded, since bounded + discrete doesn't imply finite in general. *)

let TOTALLY_BOUNDED_ULC_SPACE_IMP_FCCOVERABLE_SPACE = `!m:A metric.
     totally_bounded_in m (mspace m) /\ ulc_space m
     ==> fccoverable_space m`;;

(* Note: For general metric spaces, mbounded does NOT imply totally bounded.
   The Euclidean version BOUNDED_ULC_SPACE_IMP_FCCOVERABLE_SPACE relies on
   DISCRETE_BOUNDED_IMP_FINITE which is specific to R^n.
   The correct general statement is TOTALLY_BOUNDED_ULC_SPACE_IMP_FCCOVERABLE_SPACE above. *)

let COMPACT_IN_LOCALLY_CONNECTED_IMP_FCCOVERABLE_SPACE = `!m:A metric.
     compact_in (mtopology m) (mspace m) /\
     locally_connected_space (mtopology m)
     ==> fccoverable_space m`;;

let COMPACT_IN_LOCALLY_CONNECTED_EQ_FCCOVERABLE_SPACE = `!m:A metric.
     compact_in (mtopology m) (mspace m) /\
     locally_connected_space (mtopology m) <=>
     (!e. &0 < e
          ==> ?c. FINITE c /\ UNIONS c = mspace m /\
                  !t. t IN c
                      ==> connected_in (mtopology m) t /\
                          compact_in (mtopology m) t /\
                          mdiameter m t <= e)`;;

(* ------------------------------------------------------------------------- *)
(* Localization of Property S (fccoverability).                              *)
(* Whyburn, Analytic Topology, Ch. I Sec. 15; H-Y exercises 3-6 to 3-9.    *)
(* ------------------------------------------------------------------------- *)

(* Common chain construction for LOCALLY_FCCOVERABLE_SPACE *)
let LOCALLY_FCCOVERABLE_SPACE_CHAIN = `!m:A metric s u a r.
     s SUBSET mspace m /\ a IN s /\ a IN mspace m /\ &0 < r /\
     s INTER mcball m (a, &2 * r) SUBSET u /\
     locally_connected_space (subtopology (mtopology m) s) /\
     (!e. &0 < e ==> ?c. FINITE c /\
                  (!w. w IN c ==> w SUBSET s /\
                           connected_in (mtopology m) w /\
                           mbounded m w /\ mdiameter m w <= e) /\
                  (!x. x IN s /\ x IN mball m (a, &2 * r)
                       ==> ?w. w IN c /\ x IN w))
     ==> ?v. open_in (subtopology (mtopology m) s) v /\
             connected_in (subtopology (mtopology m) s) v /\
             a IN v /\ v SUBSET u /\ fccoverable_in m v`;;

(* Helper: compact + locally connected implies fccoverable_in *)
let FCCOVERABLE_IN_COMPACT_LOCALLY_CONNECTED = `!m:A metric K.
        compact_in (mtopology m) K /\
        locally_connected_space (subtopology (mtopology m) K)
        ==> fccoverable_in m K`;;

let LOCALLY_FCCOVERABLE_SPACE = `!m:A metric s u a.
     locally_compact_space (subtopology (mtopology m) s) /\
     locally_connected_space (subtopology (mtopology m) s) /\
     open_in (subtopology (mtopology m) s) u /\ a IN u
     ==> ?v. open_in (subtopology (mtopology m) s) v /\
             connected_in (subtopology (mtopology m) s) v /\
             a IN v /\ v SUBSET u /\ fccoverable_in m v`;;

let LOCALLY_CONNECTED_CONTINUUM_SPACE = `!m:A metric s.
       neighbourhood_base_of
        (\c. compact_in (subtopology (mtopology m) s) c /\
             connected_in (subtopology (mtopology m) s) c /\
             locally_connected_space (subtopology (mtopology m) c))
        (subtopology (mtopology m) s) <=>
     locally_compact_space (subtopology (mtopology m) s) /\
     locally_connected_space (subtopology (mtopology m) s)`;;

let COMPACT_IN_LOCALLY_CONNECTED_EQ_FCCOVERABLE_SPACE_ALT = `!m:A metric.
        compact_in (mtopology m) (mspace m) /\
        locally_connected_space (mtopology m) <=>
        (!e. &0 < e
             ==> ?c. FINITE c /\ UNIONS c = mspace m /\
                     !t. t IN c
                         ==> connected_in (mtopology m) t /\
                             compact_in (mtopology m) t /\
                             locally_connected_space
                               (subtopology (mtopology m) t) /\
                             mdiameter m t <= e)`;;

(* ------------------------------------------------------------------------- *)
(* Compact locally connected spaces have finitely many connected components  *)
(* ------------------------------------------------------------------------- *)

let FINITE_CONNECTED_COMPONENTS_COMPACT_LOCALLY_CONNECTED = `!m:A metric.
        compact_in (mtopology m) (mspace m) /\
        locally_connected_space (mtopology m)
        ==> FINITE(connected_components_of(mtopology m))`;;

(* ------------------------------------------------------------------------- *)
(* Semi-locally connected spaces (finitely many components in complements).  *)
(* Whyburn, Analytic Topology, Ch. I Sec. 13.                               *)
(* ------------------------------------------------------------------------- *)

(* Helper lemma for SEMI_LOCALLY_CONNECTED_GEN_SPACE finiteness argument *)
let FINITE_CONNECTED_COMPONENTS_CLOPEN_UNION = `!top C s:A->bool.
        locally_connected_space top /\
        open_in top C /\ closed_in top C /\ C SUBSET topspace top /\
        s SUBSET C /\ FINITE(connected_components_of top) /\
        FINITE(connected_components_of (subtopology top (C DIFF s)))
        ==> FINITE(connected_components_of
                    (subtopology top (topspace top DIFF s)))`;;

(* Helper: Semi-local connectedness for connected spaces *)
let SEMI_LOCALLY_CONNECTED_CONNECTED = `!m:A metric. connected_in (mtopology m) (mspace m) /\
     locally_compact_space (mtopology m) /\
     locally_connected_space (mtopology m)
     ==> !x v. open_in (mtopology m) v /\ x IN v
               ==> ?u. open_in (mtopology m) u /\ x IN u /\ u SUBSET v /\
                       FINITE(connected_components_of(subtopology (mtopology m)
                                                      (mspace m DIFF u)))`;;

(* SEMI_LOCALLY_CONNECTED_GEN_SPACE: Use *)
(* SEMI_LOCALLY_CONNECTED_CONNECTED on each component *)
let SEMI_LOCALLY_CONNECTED_GEN_SPACE = `!m:A metric. FINITE(connected_components_of(mtopology m)) /\
     locally_compact_space (mtopology m) /\
     locally_connected_space (mtopology m)
     ==> !x v. open_in (mtopology m) v /\ x IN v
               ==> ?u. open_in (mtopology m) u /\ x IN u /\ u SUBSET v /\
                       FINITE(connected_components_of(subtopology (mtopology m)
                                                      (mspace m DIFF u)))`;;

let SEMI_LOCALLY_CONNECTED_COMPACT_SPACE = `!m:A metric.
     compact_in (mtopology m) (mspace m) /\
     locally_connected_space (mtopology m)
     ==> !x v. open_in (mtopology m) v /\ x IN v
               ==> ?u. open_in (mtopology m) u /\ x IN u /\ u SUBSET v /\
                       FINITE(connected_components_of(subtopology (mtopology m)
                                                      (mspace m DIFF u)))`;;

(* ------------------------------------------------------------------------- *)
(* The dyadic rationals in [0,1] are dense in [0,1].                        *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_OF_DYADIC_RATIONALS_IN_UNIT_INTERVAL = `euclideanreal closure_of {&k / &2 pow n | k <= 2 EXP n} =
   real_interval[&0,&1]`;;

(* ------------------------------------------------------------------------- *)
(* Path-connectivity of complete locally connected metric spaces.            *)
(* Whyburn, Analytic Topology, Theorems (5.1)-(5.4); H-Y Theorem 3-17.       *)
(* ------------------------------------------------------------------------- *)

(* Chain from open cover: in a connected space, any open cover admits a      *)
(* finite chain between any two points (H-Y Theorem 3-4).                   *)

let CHAIN_FROM_OPEN_COVER = `!top:A topology U a b.
        connected_space top /\
        a IN topspace top /\ b IN topspace top /\
        (!x. x IN topspace top ==> ?u. u IN U /\ x IN u) /\
        (!u. u IN U ==> open_in top u) ==> ?c n. (!i. i <= n ==> c i IN U) /\
                  a IN c 0 /\ b IN c n /\
                  (!i. i < n ==> ~(c i INTER c(SUC i) = {}))`;;

(* CONNECTED_IN_CHAIN_UNIONS: A finite chain of connected sets (consecutive  *)
(* links overlapping) has connected union.                                   *)

let CONNECTED_IN_CHAIN_UNIONS = `!top (c:num->A->bool) n.
        (!i. i <= n ==> connected_in top (c i)) /\
        (!i. i < n ==> ~(c i INTER c(SUC i) = {}))
        ==> connected_in top (UNIONS {c i | i <= n})`;;

(* Helper: intersection of nested unions of closures with vanishing           *)
(* diameter in a complete metric space is compact. Proved for the whole       *)
(* metric space; localized versions follow by instantiating m to submetric.  *)

let COMPACT_NESTED_INTERS = `!m:A metric (c:num->num->A->bool) (N:num->num).
        mcomplete m /\
        (!n i. i <= N n ==> c n i SUBSET mspace m) /\
        (!n i. i <= N n ==> !x y. x IN c n i /\ y IN c n i
                         ==> mdist m (x:A,y) < inv(&(n + 1)))
        ==> compact_in (mtopology m)
              (INTERS {UNIONS {mtopology m closure_of c n i | i |
                                i <= N n} | n IN (:num)})`;;

(* Helper: in a locally connected metric space, each point in an open set    *)
(* has a connected open neighbourhood with closure inside the open set and   *)
(* small diameter.                                                           *)

let OPEN_CONNECTED_FINE_COVER = `!m:A metric u e.
        locally_connected_space (mtopology m) /\
        open_in (mtopology m) u /\ &0 < e ==> !x. x IN u
        ==> ?v. open_in (mtopology m) v /\ connected_in (mtopology m) v /\
                x IN v /\ v SUBSET u /\
                (mtopology m closure_of v) SUBSET u /\
                !y z. y IN v /\ z IN v ==> mdist m (y:A,z) < e`;;

(* Helper: chain within a single open connected set, with closures inside    *)

let CHAIN_IN_OPEN_CONNECTED_SET = `!m:A metric g e a' b'.
    locally_connected_space (mtopology m) /\
    open_in (mtopology m) g /\ connected_in (mtopology m) g /\
    a' IN g /\ b' IN g /\ &0 < e
    ==> ?c' M'. (!i. i <= M' ==> open_in (mtopology m) (c' i) /\
                                  connected_in (mtopology m) (c' i) /\
                                  (mtopology m closure_of c' i) SUBSET g) /\
                a' IN c' 0 /\ b' IN c' M' /\
                (!i. i < M' ==> ~(c' i INTER c'(SUC i) = {})) /\
                (!i. i <= M' ==>
                     !x y. x IN c' i /\ y IN c' i ==> mdist m (x:A,y) < e)`;;

(* Helper: chain refinement step - refine a coarse chain to a finer one     *)
let CHAIN_REFINEMENT_STEP = `!m:A metric (g:num->A->bool) M e a b.
    locally_connected_space (mtopology m) /\
    (!i. i <= M ==> open_in (mtopology m) (g i) /\
                     connected_in (mtopology m) (g i)) /\
    a IN g 0 /\ b IN g M /\ (!i. i < M ==> ~(g i INTER g(SUC i) = {})) /\
    &0 < e
    ==> ?g' M'. (!i. i <= M' ==> open_in (mtopology m) (g' i) /\
                            connected_in (mtopology m) (g' i)) /\
          a IN g' 0 /\ b IN g' M' /\
          (!i. i < M' ==> ~(g' i INTER g'(SUC i) = {})) /\ (!i. i <= M' ==>
               !x y. x IN g' i /\ y IN g' i ==> mdist m (x:A,y) < e) /\
          (!j. j <= M' ==> ?i. i <= M /\
                   (mtopology m closure_of g' j) SUBSET g i) /\
          (?ff. (!j. j <= M' ==> ff j <= M /\
                     (mtopology m closure_of g' j) SUBSET g (ff j)) /\
                (!j1 j2. j1 <= j2 /\ j2 <= M' ==> ff j1 <= ff j2) /\
                (!i. i <= M ==> ?j. j <= M' /\ ff j = i)) /\
          (!i. i <= M ==> ?j. j <= M' /\
                   (mtopology m closure_of g' j) SUBSET g i)`;;

(* Helper: chain hierarchy construction via DEPENDENT_CHOICE.                *)
(* Builds a sequence of increasingly fine chains from a to b.                *)

let CHAIN_HIERARCHY = `!m:A metric a b.
    connected_space (mtopology m) /\
    locally_connected_space (mtopology m) /\ a IN mspace m /\ b IN mspace m
    ==> ?c (N:num->num). (!n i. i <= N n
                 ==> open_in (mtopology m) ((c:num->num->A->bool) n i)) /\
          (!n i. i <= N n ==> connected_in (mtopology m) (c n i)) /\
          (!n. (a:A) IN c n 0) /\ (!n. b IN c n (N n)) /\
          (!n i. i < N n ==> ~(c n i INTER c n (SUC i) = {})) /\
          (!n i. i <= N n ==> !x y. x IN c n i /\ y IN c n i
                           ==> mdist m (x:A,y) < inv(&(n + 1))) /\
          (!n j. j <= N(SUC n) ==> ?i. i <= N n /\
                     (mtopology m closure_of c (SUC n) j) SUBSET c n i) /\
          (!n i. i <= N n ==> ?j. j <= N(SUC n) /\ (mtopology m closure_of
                       (c:num->num->A->bool) (SUC n) j) SUBSET c n i) /\
          (!n. ?ff. (!j. j <= N(SUC n) ==> ff j <= N n /\
                             (mtopology m closure_of
                               (c:num->num->A->bool) (SUC n) j) SUBSET
                             c n (ff j)) /\
                    (!j1 j2. j1 <= j2 /\ j2 <= N(SUC n) ==> ff j1 <= ff j2) /\
                    (!i. i <= N n ==> ?j. j <= N(SUC n) /\ ff j = i))`;;

(* Helper lemma: construct a uniformly continuous function on dyadic         *)
(* rationals D = {k/2^n | k <= 2^n} mapping into a complete connected       *)
(* locally connected metric space. This is the core of the Menger theorem.   *)

let MCOMPLETE_DYADIC_APPROXIMATION = `!m:A metric a b.
    mcomplete m /\ connected_space (mtopology m) /\
    locally_connected_space (mtopology m) /\ a IN mspace m /\ b IN mspace m
    ==> ?f:real->A. f(&0) = a /\ f(&1) = b /\
         (!m' n. m' <= 2 EXP n ==> f(&m' / &2 pow n) IN mspace m) /\
         (!j. ?d. &0 < d /\ !n m1 m2. m1 <= 2 EXP n /\ m2 <= 2 EXP n /\
                            abs(&m1 / &2 pow n - &m2 / &2 pow n) < d
                            ==> mdist m (f(&m1 / &2 pow n),
                                         f(&m2 / &2 pow n):A)
                                < inv(&2 pow j))`;;

(* Imbedding Theorem: Whyburn, Analytic Topology, Theorem (4.2).             *)
(* In a complete, connected, locally connected metric space, any two points  *)
(* are contained in a locally connected continuum (compact connected locally *)
(* connected subset). Build a uniformly continuous function on dyadics via   *)
(* the chain construction, extend to [0,1] by completeness, and observe      *)
(* that the image is compact, connected, and locally connected.              *)

let MCOMPLETE_IMBEDDING_IN_LC_CONTINUUM = `!m:A metric a b.
        mcomplete m /\
        connected_space (mtopology m) /\
        locally_connected_space (mtopology m) /\
        a IN mspace m /\
        b IN mspace m
        ==> ?K. compact_in (mtopology m) K /\
                connected_in (mtopology m) K /\
                locally_connected_space
                  (subtopology (mtopology m) K) /\
                a IN K /\ b IN K`;;


(* Localized version: imbedding theorem for a complete     *)
(* metric subspace.                                        *)

let MCOMPLETE_IMBEDDING_IN_LC_CONTINUUM_IN = `!m:A metric s a b.
        mcomplete(submetric m s) /\
        connected_in (mtopology m) s /\
        locally_connected_space (subtopology (mtopology m) s) /\
        a IN s /\ b IN s
        ==> ?K. compact_in (mtopology m) K /\
                connected_in (mtopology m) K /\
                locally_connected_space
                  (subtopology (mtopology m) K) /\
                K SUBSET s /\ a IN K /\ b IN K`;;

(* ------------------------------------------------------------------------- *)
(* "Capped" equivalent bounded metrics and general product metrics.          *)
(* ------------------------------------------------------------------------- *)

let capped_metric = new_definition
 `capped_metric d (m:A metric) =
        if d <= &0 then m
        else metric(mspace m,(\(x,y). min d (mdist m (x,y))))`;;

let CAPPED_METRIC = `!d m:A metric.
        mspace (capped_metric d m) = mspace m /\
        mdist (capped_metric d m) =
           \(x,y). if d <= &0 then mdist m (x,y) else min d (mdist m (x,y))`;;

let MDIST_CAPPED = `!d m x y:A. &0 < d ==> mdist(capped_metric d m) (x,y) <= d`;;

let MTOPOLOGY_CAPPED_METRIC = `!d m:A metric. mtopology(capped_metric d m) = mtopology m`;;

let CAUCHY_IN_CAPPED_METRIC = `!d (m:A metric) x.
        cauchy_in (capped_metric d m) x <=> cauchy_in m x`;;

let MCOMPLETE_CAPPED_METRIC = `!d (m:A metric). mcomplete(capped_metric d m) <=> mcomplete m`;;

let BOUNDED_EQUIVALENT_METRIC = `!m:A metric d.
        &0 < d
        ==> ?m'. mspace m' = mspace m /\
                 mtopology m' = mtopology m /\
                 !x y. mdist m' (x,y) < d`;;

let SUP_METRIC_CARTESIAN_PRODUCT = `!k (m:K->(A)metric) m'.
        metric(cartesian_product k (mspace o m),
               \(x,y). sup {mdist(m i) (x i,y i) | i IN k}) = m' /\
        ~(k = {}) /\
        (?c. !i x y. i IN k /\ x IN mspace(m i) /\ y IN mspace(m i)
                      ==> mdist(m i) (x,y) <= c)
        ==> mspace m' = cartesian_product k (mspace o m) /\
            mdist m' = (\(x,y). sup {mdist(m i) (x i,y i) | i IN k}) /\
            !x y b. x IN cartesian_product k (mspace o m) /\
                    y IN cartesian_product k (mspace o m)
                    ==> (mdist m' (x,y) <= b <=>
                         !i. i IN k ==> mdist (m i) (x i,y i) <= b)`;;

let METRIZABLE_SPACE_PRODUCT_TOPOLOGY = `(!(tops:K->A topology) k.
        metrizable_space (product_topology k tops) <=>
        topspace (product_topology k tops) = {} \/
        COUNTABLE {i | i IN k /\ ~(?a. topspace(tops i) SUBSET {a})} /\
        !i. i IN k ==> metrizable_space (tops i))`
and COMPLETELY_METRIZABLE_SPACE_PRODUCT_TOPOLOGY = `(!(tops:K->A topology) k.
        completely_metrizable_space (product_topology k tops) <=>
        topspace (product_topology k tops) = {} \/
        COUNTABLE {i | i IN k /\ ~(?a. topspace(tops i) SUBSET {a})} /\
        !i. i IN k ==> completely_metrizable_space (tops i))`;;

(* ------------------------------------------------------------------------- *)
(* Urysohn's metrization theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let EMBEDDING_INTO_METRIZABLE_IMP_METRIZABLE = `!top top' (f:A->B).
        embedding_map (top,top') f /\ metrizable_space top'
        ==> metrizable_space top`;;

(* Helper lemma: separating functions give injectivity *)
let SEPARATING_FUNCTIONS_INJECTIVE = `!top (fs:num->A->real) x y.
     hausdorff_space top /\
     (!x0 u. open_in top u /\ x0 IN u
             ==> (?n. fs n x0 > &0 /\
                      (!x. x IN topspace top /\ ~(x IN u) ==> fs n x = &0))) /\
     x IN topspace top /\ y IN topspace top
     ==> ((\n. fs n x) = (\n. fs n y) <=> x = y)`;;

let METRIZABLE_PRODUCT_EUCLIDEANREAL_NUM = `metrizable_space (product_topology (:num) (\n. euclideanreal))`;;

let URYSOHN_METRIZATION = `!top:A topology.
        regular_space top /\ second_countable top /\ hausdorff_space top
        ==> metrizable_space top`;;

(* Corollary: equivalential form of Urysohn metrization *)
let URYSOHN_METRIZATION_EQ = `!top:A topology.
        second_countable top
        ==> (regular_space top /\ hausdorff_space top <=>
             metrizable_space top)`;;

(* ------------------------------------------------------------------------- *)
(* A perfect set in common cases must have cardinality >= c.                 *)
(* ------------------------------------------------------------------------- *)

let CARD_GE_PERFECT_SET = `!top s:A->bool.
        (completely_metrizable_space top \/
         locally_compact_space top /\ hausdorff_space top) /\
        top derived_set_of s = s /\ ~(s = {})
        ==> (:real) <=_c s`;;

(* ------------------------------------------------------------------------- *)
(* Euclidean space and n-spheres, as subtopologies of infinite product R^N.  *)
(* ------------------------------------------------------------------------- *)

let euclidean_space = new_definition
 `euclidean_space n = subtopology (product_topology (:num) (\i. euclideanreal))
                         {x | !i. ~(i IN 1..n) ==> x i = &0}`;;

let TOPSPACE_EUCLIDEAN_SPACE = `!n. topspace(euclidean_space n) = {x | !i. ~(i IN 1..n) ==> x i = &0}`;;

let NONEMPTY_EUCLIDEAN_SPACE = `!n. ~(topspace(euclidean_space n) = {})`;;

let SUBSET_EUCLIDEAN_SPACE = `!m n. topspace(euclidean_space m) SUBSET topspace(euclidean_space n) <=>
         m <= n`;;

let CLOSED_IN_EUCLIDEAN_SPACE = `!n. closed_in (product_topology (:num) (\i. euclideanreal))
                 (topspace(euclidean_space n))`;;

let COMPLETELY_METRIZABLE_EUCLIDEAN_SPACE = `!n. completely_metrizable_space(euclidean_space n)`;;

let METRIZABLE_EUCLIDEAN_SPACE = `!n. metrizable_space(euclidean_space n)`;;

let CONTINUOUS_MAP_COMPONENTWISE_EUCLIDEAN_SPACE = `!top (f:A->num->real) n.
        continuous_map (top,euclidean_space n)
                       (\x i. if 1 <= i /\ i <= n then f x i else &0) <=>
   !i. 1 <= i /\ i <= n ==> continuous_map(top,euclideanreal) (\x. f x i)`;;

let CONTINUOUS_MAP_EUCLIDEAN_SPACE_ADD = `!f g:A->num->real.
        continuous_map(top,euclidean_space n) f /\
        continuous_map(top,euclidean_space n) g
        ==> continuous_map(top,euclidean_space n) (\x i. f x i + g x i)`;;

let CONTINUOUS_MAP_EUCLIDEAN_SPACE_SUB = `!f g:A->num->real.
        continuous_map(top,euclidean_space n) f /\
        continuous_map(top,euclidean_space n) g
        ==> continuous_map(top,euclidean_space n) (\x i. f x i - g x i)`;;

let HOMEOMORPHIC_EUCLIDEAN_SPACE_PRODUCT_TOPOLOGY = `!n. euclidean_space n homeomorphic_space
       product_topology (1..n) (\i. euclideanreal)`;;

let CONTRACTIBLE_EUCLIDEAN_SPACE = `!n. contractible_space(euclidean_space n)`;;

let PATH_CONNECTED_EUCLIDEAN_SPACE = `!n. path_connected_space(euclidean_space n)`;;

let CONNECTED_EUCLIDEAN_SPACE = `!n. connected_space(euclidean_space n)`;;

let LOCALLY_COMPACT_EUCLIDEAN_SPACE = `!n. locally_compact_space(euclidean_space n)`;;

let LOCALLY_PATH_CONNECTED_EUCLIDEAN_SPACE = `!n. locally_path_connected_space(euclidean_space n)`;;

let LOCALLY_CONNECTED_EUCLIDEAN_SPACE = `!n. locally_connected_space(euclidean_space n)`;;

let HAUSDORFF_EUCLIDEAN_SPACE = `!n. hausdorff_space (euclidean_space n)`;;

let COMPACT_EUCLIDEAN_SPACE = `!n. compact_space(euclidean_space n) <=> n = 0`;;

let nsphere = new_definition
 `nsphere n = subtopology (euclidean_space (n + 1))
                          { x | sum(1..n+1) (\i. x i pow 2) = &1 }`;;

let NSPHERE = `!n. nsphere n = subtopology (product_topology (:num) (\i. euclideanreal))
                               {x | sum(1..n+1) (\i. x i pow 2) = &1 /\
                                    !i. ~(i IN 1..n+1) ==> x i = &0}`;;

let NONEMPTY_NSPHERE = `!n. ~(topspace(nsphere n) = {})`;;

let SUBTOPOLOGY_NSPHERE_EQUATOR = `!n. subtopology (nsphere (n + 1)) {x | x(n+2) = &0} = nsphere n`;;

let CONTINUOUS_MAP_NSPHERE_REFLECTION = `!n k. continuous_map (nsphere n,nsphere n)
                        (\x i. if i = k then --x i else x i)`;;

let CONTRACTIBLE_SPACE_UPPER_HEMISPHERE = `!n k. k IN 1..n+1
         ==> contractible_space(subtopology (nsphere n) {x | x k >= &0})`;;

let CONTRACTIBLE_SPACE_LOWER_HEMISPHERE = `!n k. k IN 1..n+1
         ==> contractible_space(subtopology (nsphere n) {x | x k <= &0})`;;

let NULLHOMOTOPIC_NONSURJECTIVE_SPHERE_MAP = `!p f. continuous_map(nsphere p,nsphere p) f /\
         ~(IMAGE f (topspace(nsphere p)) = topspace(nsphere p))
         ==> ?a. homotopic_with (\x. T) (nsphere p,nsphere p) f (\x. a)`;;

(* ------------------------------------------------------------------------- *)
(* Contractions.                                                             *)
(* ------------------------------------------------------------------------- *)

let CONTRACTION_IMP_UNIQUE_FIXPOINT = `!m (f:A->A) k x y.
     k < &1 /\
     (!x. x IN mspace m ==> f x IN mspace m) /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m (f x, f y) <= k * mdist m (x,y)) /\
     x IN mspace m /\ y IN mspace m /\ f x = x /\ f y = y
     ==> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Banach Fixed-Point Theorem (aka, Contraction Mapping Principle).          *)
(* ------------------------------------------------------------------------- *)

let BANACH_FIXPOINT_THM = `!m f:A->A k.
     ~(mspace m = {}) /\
     mcomplete m /\
     (!x. x IN mspace m ==> f x IN mspace m) /\
     k < &1 /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m (f x, f y) <= k * mdist m (x,y))
     ==> (?!x. x IN mspace m /\ f x = x)`;;

(* ------------------------------------------------------------------------- *)
(* Metric space of bounded functions.                                        *)
(* ------------------------------------------------------------------------- *)

let funspace = new_definition
  `funspace s m =
   metric ({f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                     f IN EXTENSIONAL s /\
                     mbounded m (IMAGE f s)},
           (\(f,g). if s = {} then &0 else
                    sup {mdist m (f x,g x) | x | x IN s}))`;;

let FUNSPACE =
 `!s m.
     mspace (funspace s m) =
       {f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                 f IN EXTENSIONAL s /\
                 mbounded m (IMAGE f s)} /\
     (!f g. mdist (funspace s m) (f,g) =
              if s = {} then &0 else
              sup {mdist m (f x,g x) | x | x IN s})`;;

let FUNSPACE_IMP_WELLDEFINED = `!s m f:A->B x. f IN mspace (funspace s m) /\ x IN s ==> f x IN mspace m`;;

let FUNSPACE_IMP_EXTENSIONAL = `!s m f:A->B. f IN mspace (funspace s m) ==> f IN EXTENSIONAL s`;;

let FUNSPACE_IMP_BOUNDED_IMAGE = `!s m f:A->B. f IN mspace (funspace s m) ==> mbounded m (IMAGE f s)`;;

let FUNSPACE_IMP_BOUNDED = `!s m f:A->B. f IN mspace (funspace s m)
                ==> s = {} \/ (?c b. !x. x IN s ==> mdist m (c,f x) <= b)`;;

let FUNSPACE_IMP_BOUNDED2 = `!s m f g:A->B. f IN mspace (funspace s m) /\ g IN mspace (funspace s m)
                  ==> (?b. !x. x IN s ==> mdist m (f x,g x) <= b)`;;

let FUNSPACE_MDIST_LE = `!s m f g:A->B a.
     ~(s = {}) /\
     f IN mspace (funspace s m) /\
     g IN mspace (funspace s m)
     ==> (mdist (funspace s m) (f,g) <= a <=>
          !x. x IN s ==> mdist m (f x, g x) <= a)`;;

let MCOMPLETE_FUNSPACE = `!s:A->bool m:B metric. mcomplete m ==> mcomplete (funspace s m)`;;

(* ------------------------------------------------------------------------- *)
(* Metric space of continuous bounded functions.                             *)
(* ------------------------------------------------------------------------- *)

let cfunspace = new_definition
  `cfunspace top m =
   submetric (funspace (topspace top) m)
     {f:A->B | continuous_map (top,mtopology m) f}`;;

let CFUNSPACE =
 `(!top m.
      mspace (cfunspace top m) =
      {f:A->B | (!x. x IN topspace top ==> f x IN mspace m) /\
                f IN EXTENSIONAL (topspace top) /\
                mbounded m (IMAGE f (topspace top)) /\
                continuous_map (top,mtopology m) f}) /\
     (!f g:A->B.
        mdist (cfunspace top m) (f,g) =
        if topspace top = {} then &0 else
        sup {mdist m (f x,g x) | x IN topspace top})`;;

let CFUNSPACE_SUBSET_FUNSPACE = `!top:A topology m:B metric.
     mspace (cfunspace top m) SUBSET mspace (funspace (topspace top) m)`;;

let MDIST_CFUNSPACE_EQ_MDIST_FUNSPACE = `!top m f g:A->B.
     mdist (cfunspace top m) (f,g) = mdist (funspace (topspace top) m) (f,g)`;;

let CFUNSPACE_MDIST_LE = `!top m f g:A->B a.
     ~(topspace top = {}) /\
     f IN mspace (cfunspace top m) /\
     g IN mspace (cfunspace top m)
     ==> (mdist (cfunspace top m) (f,g) <= a <=>
          !x. x IN topspace top ==> mdist m (f x, g x) <= a)`;;

let CFUNSPACE_IMP_BOUNDED2 = `!top m f g:A->B.
     f IN mspace (cfunspace top m) /\ g IN mspace (cfunspace top m)
     ==> (?b. !x. x IN topspace top ==> mdist m (f x,g x) <= b)`;;

let CFUNSPACE_MDIST_LT = `!top m f g:A->B a x.
     compact_in top (topspace top) /\
     f IN mspace (cfunspace top m) /\ g IN mspace (cfunspace top m) /\
     mdist (cfunspace top m) (f, g) < a /\
     x IN topspace top
     ==> mdist m (f x, g x) < a`;;

let MDIST_CFUNSPACE_LE = `!top m B f g.
     &0 <= B /\
     (!x:A. x IN topspace top ==> mdist m (f x:B, g x) <= B)
     ==> mdist (cfunspace top m) (f,g) <= B`;;

let MDIST_CFUNSPACE_IMP_MDIST_LE = `!top m f g:A->B a x.
     f IN mspace (cfunspace top m) /\
     g IN mspace (cfunspace top m) /\
     mdist (cfunspace top m) (f,g) <= a /\
     x IN topspace top
     ==> mdist m (f x,g x) <= a`;;

let COMPACT_IN_MSPACE_CFUNSPACE = `!top m.
     compact_in top (topspace top)
     ==> mspace (cfunspace top m) =
          {f | (!x:A. x IN topspace top ==> f x:B IN mspace m) /\
               f IN EXTENSIONAL (topspace top) /\
               continuous_map (top,mtopology m) f}`;;

let MCOMPLETE_CFUNSPACE = `!top:A topology m:B metric. mcomplete m ==> mcomplete (cfunspace top m)`;;

(* ------------------------------------------------------------------------- *)
(* Existence of completion for any metric space M as a subspace of M->R.     *)
(* ------------------------------------------------------------------------- *)

let METRIC_COMPLETION_EXPLICIT = `!m:A metric. ?s f:A->A->real.
      s SUBSET mspace(funspace (mspace m) real_euclidean_metric) /\
      mcomplete(submetric (funspace (mspace m) real_euclidean_metric) s) /\
      IMAGE f (mspace m) SUBSET s /\
      mtopology(funspace (mspace m) real_euclidean_metric) closure_of
      IMAGE f (mspace m) = s /\
      !x y. x IN mspace m /\ y IN mspace m
            ==> mdist (funspace (mspace m) real_euclidean_metric) (f x,f y) =
                mdist m (x,y)`;;

let METRIC_COMPLETION = `!m:A metric.
        ?m' f:A->A->real.
                mcomplete m' /\
                IMAGE f (mspace m) SUBSET mspace m' /\
                (mtopology m') closure_of (IMAGE f (mspace m)) = mspace m' /\
                !x y. x IN mspace m /\ y IN mspace m
                      ==> mdist m' (f x,f y) = mdist m (x,y)`;;

let METRIZABLE_SPACE_COMPLETION = `!top:A topology.
        metrizable_space top
        ==> ?top' (f:A->A->real).
                completely_metrizable_space top' /\
                embedding_map(top,top') f /\
                top' closure_of (IMAGE f (topspace top)) = topspace top'`;;

(* ------------------------------------------------------------------------- *)
(* The Baire Category Theorem                                                *)
(* ------------------------------------------------------------------------- *)

let METRIC_BAIRE_CATEGORY = `!m:A metric g.
     mcomplete m /\
     COUNTABLE g /\
     (!t. t IN g ==> open_in (mtopology m) t /\
                     mtopology m closure_of t = mspace m)
     ==> mtopology m closure_of INTERS g = mspace m`;;

let METRIC_BAIRE_CATEGORY_ALT = `!m g:(A->bool)->bool.
         mcomplete m /\
         COUNTABLE g /\
         (!t. t IN g
              ==> closed_in (mtopology m) t /\ mtopology m interior_of t = {})
         ==> mtopology m interior_of (UNIONS g) = {}`;;

let BAIRE_CATEGORY_ALT = `!top g:(A->bool)->bool.
        (completely_metrizable_space top \/
         locally_compact_space top /\
         (hausdorff_space top \/ regular_space top)) /\
        COUNTABLE g /\
        (!t. t IN g ==> closed_in top t /\ top interior_of t = {})
        ==> top interior_of (UNIONS g) = {}`;;

let BAIRE_CATEGORY = `!top g:(A->bool)->bool.
        (completely_metrizable_space top \/
         locally_compact_space top /\
         (hausdorff_space top \/ regular_space top)) /\
        COUNTABLE g /\
        (!t. t IN g ==> open_in top t /\ top closure_of t = topspace top)
        ==> top closure_of INTERS g = topspace top`;;

(* ------------------------------------------------------------------------- *)
(* Sierpinski-Hausdorff type results about countable closed unions.          *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONNECTED_NOT_COUNTABLE_CLOSED_UNION = `!top u:(A->bool)->bool.
        ~(topspace top = {}) /\
        connected_space top /\
        locally_connected_space top /\
        (completely_metrizable_space top \/
         locally_compact_space top /\ hausdorff_space top) /\
        COUNTABLE u /\ pairwise DISJOINT u /\
        (!c. c IN u ==> closed_in top c /\ ~(c = {})) /\
        UNIONS u = topspace top
         ==> u = {topspace top}`;;

let REAL_SIERPINSKI_LEMMA = `!a b u.
        a <= b /\
        COUNTABLE u /\ pairwise DISJOINT u /\
        (!c. c IN u ==> real_closed c /\ ~(c = {})) /\
        UNIONS u = real_interval[a,b]
         ==> u = {real_interval[a,b]}`;;

(* ------------------------------------------------------------------------- *)
(* Size bounds on connected or path-connected spaces.                        *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_SPACE_IMP_CARD_GE_ALT = `!top s:A->bool.
        connected_space top /\ completely_regular_space top /\
        closed_in top s /\ ~(s = {}) /\ ~(s = topspace top)
        ==> (:real) <=_c topspace top`;;

let CONNECTED_SPACE_IMP_CARD_GE_GEN = `!top s t:A->bool.
        connected_space top /\ normal_space top /\
        closed_in top s /\ closed_in top t /\
        ~(s = {}) /\ ~(t = {}) /\ DISJOINT s t
        ==> (:real) <=_c topspace top`;;

let CONNECTED_SPACE_IMP_CARD_GE = `!top:A topology.
        connected_space top /\ normal_space top /\
        (t1_space top \/ hausdorff_space top) /\
        ~(?a. topspace top SUBSET {a})
        ==> (:real) <=_c topspace top`;;

let CONNECTED_SPACE_IMP_INFINITE_GEN = `!top:A topology.
        connected_space top /\ t1_space top /\
        ~(?a. topspace top SUBSET {a})
        ==> INFINITE(topspace top)`;;

let CONNECTED_SPACE_IMP_INFINITE = `!top:A topology.
        connected_space top /\ hausdorff_space top /\
        ~(?a. topspace top SUBSET {a})
        ==> INFINITE(topspace top)`;;

let CONNECTED_SPACE_IMP_INFINITE_ALT = `!top s:A->bool.
        connected_space top /\ regular_space top /\
        closed_in top s /\ ~(s = {}) /\ ~(s = topspace top)
        ==> INFINITE(topspace top)`;;

let PATH_CONNECTED_SPACE_IMP_CARD_GE = `!top:A topology.
        path_connected_space top /\ hausdorff_space top /\
        ~(?a. topspace top SUBSET {a})
        ==> (:real) <=_c topspace top`;;

let CONNECTED_SPACE_IMP_UNCOUNTABLE = `!top:A topology.
        connected_space top /\ regular_space top /\ hausdorff_space top /\
        ~(?a. topspace top SUBSET {a})
        ==> ~COUNTABLE(topspace top)`;;

let PATH_CONNECTED_SPACE_IMP_UNCOUNTABLE = `!top:A topology.
        path_connected_space top /\ t1_space top /\
        ~(?a. topspace top SUBSET {a})
        ==> ~COUNTABLE(topspace top)`;;

(* ------------------------------------------------------------------------- *)
(* The Tychonoff embedding.                                                  *)
(* ------------------------------------------------------------------------- *)

let COMPLETELY_REGULAR_SPACE_CUBE_EMBEDDING_EXPLICIT = `!top:A topology.
        completely_regular_space top /\ hausdorff_space top
        ==> embedding_map
             (top,
              product_topology
                (mspace (submetric (cfunspace top real_euclidean_metric)
                  {f | IMAGE f (topspace top) SUBSET real_interval [&0,&1]}))
                (\f. subtopology euclideanreal (real_interval [&0,&1])))
             (\x. RESTRICTION
                  (mspace (submetric (cfunspace top real_euclidean_metric)
                    {f | IMAGE f (topspace top) SUBSET real_interval [&0,&1]}))
                  (\f. f x))`;;

let COMPLETELY_REGULAR_SPACE_CUBE_EMBEDDING = `!top:A topology.
        completely_regular_space top /\ hausdorff_space top
        ==> ?k:((A->real)->bool) e.
               embedding_map
                (top,
                 product_topology k
                  (\f. subtopology euclideanreal (real_interval[&0,&1])))
                e`;;

(* ------------------------------------------------------------------------- *)
(* Urysohn and Tietze analogs for completely regular spaces if (one) set is  *)
(* assumed compact instead of closed. Note that Hausdorffness is *not*       *)
(* required: inside one proof we factor through the Kolmogorov quotient.     *)
(* ------------------------------------------------------------------------- *)

let URYSOHN_COMPLETELY_REGULAR_CLOSED_COMPACT = `!top s (t:A->bool) a b.
        a <= b /\ completely_regular_space top /\
        closed_in top s /\ compact_in top t /\ DISJOINT s t
        ==> ?f. continuous_map
                  (top,subtopology euclideanreal (real_interval[a,b])) f /\
                (!x. x IN t ==> f x = a) /\
                (!x. x IN s ==> f x = b)`;;

let URYSOHN_COMPLETELY_REGULAR_COMPACT_CLOSED = `!top s (t:A->bool) a b.
        a <= b /\ completely_regular_space top /\
        compact_in top s /\ closed_in top t /\ DISJOINT s t
        ==> ?f. continuous_map
                  (top,subtopology euclideanreal (real_interval[a,b])) f /\
                (!x. x IN t ==> f x = a) /\
                (!x. x IN s ==> f x = b)`;;

let URYSOHN_COMPLETELY_REGULAR_COMPACT_CLOSED_ALT = `!top s (t:A->bool) a b.
        completely_regular_space top /\
        compact_in top s /\ closed_in top t /\ DISJOINT s t
        ==> ?f. continuous_map (top,euclideanreal) f /\
                (!x. x IN t ==> f x = a) /\
                (!x. x IN s ==> f x = b)`;;

let TIETZE_EXTENSION_COMPLETELY_REGULAR = `!top (f:A->real) s t.
         completely_regular_space top /\
         compact_in top s /\ is_realinterval t /\ ~(t = {}) /\
         continuous_map (subtopology top s,euclideanreal) f /\
         (!x. x IN s ==> f x IN t)
         ==> ?g. continuous_map (top,euclideanreal) g /\
                 (!x. x IN topspace top ==> g x IN t) /\
                 (!x. x IN s ==> g x = f x)`;;

(* ------------------------------------------------------------------------- *)
(* Embedding in products and hence more about completely metrizable spaces.  *)
(* ------------------------------------------------------------------------- *)

let GDELTA_HOMEOMORPHIC_SPACE_CLOSED_IN_PRODUCT = `!top (s:K->A->bool) k.
        metrizable_space top /\ (!i. i IN k ==> open_in top(s i))
        ==> ?t. closed_in
                 (prod_topology top (product_topology k (\i. euclideanreal)))
                 t /\
                 subtopology top (INTERS {s i | i IN k}) homeomorphic_space
                 subtopology
                  (prod_topology top (product_topology k (\i. euclideanreal)))
                  t`;;

let OPEN_HOMEOMORPHIC_SPACE_CLOSED_IN_PRODUCT = `!top (s:A->bool).
        metrizable_space top /\ open_in top s
        ==> ?t. closed_in (prod_topology top euclideanreal) t /\
                subtopology top s homeomorphic_space
                subtopology (prod_topology top euclideanreal) t`;;

let COMPLETELY_METRIZABLE_SPACE_GDELTA_IN_ALT = `!top s:A->bool.
        completely_metrizable_space top /\
        (COUNTABLE INTERSECTION_OF open_in top) s
        ==> completely_metrizable_space (subtopology top s)`;;

let COMPLETELY_METRIZABLE_SPACE_GDELTA_IN = `!top s:A->bool.
        completely_metrizable_space top /\ gdelta_in top s
        ==> completely_metrizable_space (subtopology top s)`;;

let COMPLETELY_METRIZABLE_SPACE_OPEN_IN = `!top s:A->bool.
        completely_metrizable_space top /\ open_in top s
        ==> completely_metrizable_space (subtopology top s)`;;

let LOCALLY_COMPACT_IMP_COMPLETELY_METRIZABLE_SPACE = `!top:A topology.
        metrizable_space top /\ locally_compact_space top
        ==> completely_metrizable_space top`;;

let COMPLETELY_METRIZABLE_SPACE_IMP_GDELTA_IN = `!top s:A->bool.
        metrizable_space top /\ s SUBSET topspace top /\
        completely_metrizable_space (subtopology top s)
        ==> gdelta_in top s`;;

(* ------------------------------------------------------------------------- *)
(* Locally compact subspaces of metrizable spaces are G-delta.               *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_COMPACT_SPACE_IMP_GDELTA_IN = `!top s:A->bool.
        metrizable_space top /\
        s SUBSET topspace top /\
        locally_compact_space(subtopology top s)
        ==> gdelta_in top s`;;

let COMPLETELY_METRIZABLE_SPACE_EQ_GDELTA_IN = `!top s:A->bool.
        completely_metrizable_space top /\ s SUBSET topspace top
        ==> (completely_metrizable_space (subtopology top s) <=>
             gdelta_in top s)`;;

let GDELTA_IN_EQ_COMPLETELY_METRIZABLE_SPACE = `!top s:A->bool.
        completely_metrizable_space top
        ==> (gdelta_in top s <=>
             s SUBSET topspace top /\
             completely_metrizable_space (subtopology top s))`;;

(* ------------------------------------------------------------------------- *)
(* Paracompact spaces.                                                       *)
(* ------------------------------------------------------------------------- *)

let paracompact_space = new_definition
 `paracompact_space (top:A topology) <=>
        !U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
            ==> ?V. (!v. v IN V ==> open_in top v) /\
                    UNIONS V = topspace top /\
                    (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                    locally_finite_in top V`;;

let COMPACT_IMP_PARACOMPACT_SPACE = `!top:A topology. compact_space top ==> paracompact_space top`;;

let PARACOMPACT_SPACE_CLOSED_SUBSET = `!top s:A->bool.
        paracompact_space top /\ closed_in top s
        ==> paracompact_space(subtopology top s)`;;

let PARACOMPACT_SPACE_RETRACTION_MAP_IMAGE = `!top top' (r:A->B).
        retraction_map(top,top') r /\ paracompact_space top
        ==> paracompact_space top'`;;

let HOMEOMORPHIC_PARACOMPACT_SPACE = `!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (paracompact_space top <=> paracompact_space top')`;;

let PARACOMPACT_HAUSDORFF_IMP_REGULAR_SPACE = `(!top:A topology.
        paracompact_space top /\ hausdorff_space top
        ==> regular_space top)`
and PARACOMPACT_HAUSDORFF_IMP_NORMAL_SPACE = `(!top:A topology.
        paracompact_space top /\ (hausdorff_space top \/ regular_space top)
        ==> normal_space top)`;;

let sigma_locally_finite_in = new_definition
 `sigma_locally_finite_in (top:A topology) (U:(A->bool)->bool) <=>
        ?f. (!n:num. locally_finite_in top (f n)) /\
            U = UNIONS {f n | n IN (:num)}`;;

(* Helper: Countable collection with elements in topspace is
   sigma-locally-finite. Each {u} is l.f., so take f(n) = {V_n}. *)
let COUNTABLE_IMP_SIGMA_LOCALLY_FINITE_IN = `!top:A topology U.
        COUNTABLE U /\ (!u. u IN U ==> u SUBSET topspace top)
        ==> sigma_locally_finite_in top U`;;

(* Munkres Lemma 39.2: Metric covers have sigma-locally-finite refinements *)
(* Key construction for Stone's theorem using well-ordering *)
let METRIC_COVER_SIGMA_LOCALLY_FINITE = `!m:A metric U.
        (!u. u IN U ==> open_in (mtopology m) u) /\
        UNIONS U = mspace m
        ==> ?V. (!v. v IN V ==> open_in (mtopology m) v) /\
                UNIONS V = mspace m /\
                (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                sigma_locally_finite_in (mtopology m) V`;;

(* Michael's Lemma - Steps (1)=>(2)=>(3)=>(4) from Munkres Lemma 41.3 *)
(* Step (1)=>(2): Shrinking sigma-l.f. to l.f. covering *)
(* The "shrinking trick": S_n(U) = U - UNION_{i<n} V_i where V_i = UNION B_i *)
(* Requires elements of B to be open for the proof to work *)
let SIGMA_LOCALLY_FINITE_IMP_LOCALLY_FINITE_COVERING = `!(top:A topology) B.
        (!b. b IN B ==> open_in top b) /\
        sigma_locally_finite_in top B /\
        UNIONS B = topspace top
        ==> ?C. UNIONS C = UNIONS B /\
                locally_finite_in top C /\
                (!c. c IN C ==> ?b. b IN B /\ c SUBSET b)`;;

(* Helper: In a regular space, open sets with closure in some element
   of an open cover form an open cover of the whole space *)
let REGULAR_CLOSURE_REFINEMENT_COVERS = `!(top:A topology) U.
        regular_space top /\
        (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
        ==> UNIONS {b | open_in top b /\ ?u. u IN U /\ top closure_of b SUBSET u}
            = topspace top`;;

(* Step (2)=>(3): Using regularity to get l.f. closed refinement *)
(* Given that every open cover has l.f. refinement, show every open cover
   has l.f. CLOSED refinement. The proof defines B = {U open | closure(U)
   in some element of A}, applies property (2) to B, then takes closures. *)
let LF_COVERING_IMP_LF_CLOSED = `!(top:A topology).
        regular_space top /\
        (!B. (!b. b IN B ==> open_in top b) /\ UNIONS B = topspace top
             ==> ?C. UNIONS C = topspace top /\
                     locally_finite_in top C /\
                     (!c. c IN C ==> ?b. b IN B /\ c SUBSET b))
        ==> !U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
                ==> ?W. UNIONS W = topspace top /\
                        locally_finite_in top W /\
                        (!w. w IN W ==> closed_in top w) /\
                        (!w. w IN W ==> ?u. u IN U /\ w SUBSET u)`;;

(* Helper: expansion set is open when C is locally finite closed.
   E(b) = X - UNIONS{c in C | c INTER b = {}} is open and contains b *)
let EXPANSION_SET_OPEN = `!(top:A topology) C b.
        locally_finite_in top C /\
        (!c. c IN C ==> closed_in top c) /\
        b SUBSET topspace top
        ==> open_in top (topspace top DIFF UNIONS {c | c IN C /\ c INTER b = {}})`;;

let EXPANSION_SET_CONTAINS = `!(top:A topology) C b.
        UNIONS C = topspace top /\ b SUBSET topspace top
        ==> b SUBSET topspace top DIFF UNIONS {c | c IN C /\ c INTER b = {}}`;;

(* Step (3)=>(4): Expanding l.f. covering to l.f. open refinement *)
(* Given that every open cover has l.f. refinement (including closed),
   show every open cover has l.f. OPEN refinement. The expansion trick:
   use property (3) twice to get closed l.f. covers B and C, then
   expand B using C to get open l.f. cover. Following Munkres Lemma 41.3. *)
let LF_COVERING_IMP_LF_OPEN = `!(top:A topology).
        regular_space top /\
        (!B. (!b. b IN B ==> open_in top b) /\ UNIONS B = topspace top
             ==> ?C. UNIONS C = topspace top /\
                     locally_finite_in top C /\
                     (!c. c IN C ==> closed_in top c) /\
                     (!c. c IN C ==> ?b. b IN B /\ c SUBSET b))
        ==> !U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
                ==> ?W. UNIONS W = topspace top /\
                        locally_finite_in top W /\
                        (!w. w IN W ==> open_in top w) /\
                        (!w. w IN W ==> ?u. u IN U /\ w SUBSET u)`;;

(* Michael's lemma: For regular spaces, sigma-locally-finite
   implies locally finite *)
(* Combines steps (1)=>(2)=>(3)=>(4) - Lemma 41.3 from Munkres *)
(* The full proof uses SIGMA_LOCALLY_FINITE_IMP_LOCALLY_FINITE_COVERING,
   LF_COVERING_IMP_LF_CLOSED, and LF_COVERING_IMP_LF_OPEN *)
let MICHAEL_LEMMA = `!top:A topology.
        regular_space top
        ==> (!U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
                 ==> ?V. (!v. v IN V ==> open_in top v) /\
                         UNIONS V = topspace top /\
                         (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                         sigma_locally_finite_in top V)
            ==> (!U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
                     ==> ?V. (!v. v IN V ==> open_in top v) /\
                             UNIONS V = topspace top /\
                             (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                             locally_finite_in top V)`;;

(* Engelking 5.1.3 / Munkres 41.4 (A.H. Stone):
   Every metrizable space is paracompact.
   Proof combines METRIC_COVER_SIGMA_LOCALLY_FINITE and MICHAEL_LEMMA *)
let METRIZABLE_IMP_PARACOMPACT_SPACE = `!top:A topology. metrizable_space top ==> paracompact_space top`;;

(* Immediate corollary: every metric space is paracompact *)
let PARACOMPACT_SPACE_MTOPOLOGY = `!m:A metric. paracompact_space(mtopology m)`;;

(* Helper: compact set in l.f. family has open neighborhood
   meeting finitely many. Uses compactness to get finite
   subcover by neighborhoods; union of finite sets is finite. *)
let COMPACT_LF_OPEN_NEIGHBORHOOD = `!(top:A topology) (K:A->bool) (V:(A->bool)->bool).
        compact_in top K /\ locally_finite_in top V
        ==> ?N. open_in top N /\ K SUBSET N /\
                FINITE {v | v IN V /\ ~(v INTER N = {})}`;;

(* Helper: LF closed refinement pushed forward by perfect map *)
let LF_CLOSED_PERFECT_MAP_IMAGE = `!top top' (f:A->B) (W:(A->bool)->bool).
        perfect_map(top,top') f /\
        locally_finite_in top W /\
        (!w. w IN W ==> closed_in top w)
        ==> locally_finite_in top' (IMAGE (IMAGE f) W) /\
            (!v. v IN IMAGE (IMAGE f) W ==> closed_in top' v)`;;

(* Engelking 5.1.33: Perfect image of paracompact Hausdorff is paracompact *)
let PARACOMPACT_SPACE_PERFECT_MAP_IMAGE = `!top top' (f:A->B).
        paracompact_space top /\ hausdorff_space top /\
        perfect_map(top,top') f
        ==> paracompact_space top'`;;

(* Engelking 5.1.28: F_sigma subspace of paracompact
   Hausdorff is paracompact *)
(* Proof: Via Michael's Lemma. Build sigma-locally-finite open refinement
   from ascending closed sets c(n), then Michael's Lemma (needs regularity
   from Hausdorff + paracompact) converts to locally-finite. *)
let PARACOMPACT_SPACE_FSIGMA_SUBSET = `!top s:A->bool.
        paracompact_space top /\ hausdorff_space top /\ fsigma_in top s
        ==> paracompact_space(subtopology top s)`;;

(* Helper for product theorem: locally finite in product *)
(* {w CROSS topspace INTER u | w IN W, u IN Ux(xw w)} is l.f.
   when W is l.f. For (x,y), use Nx CROSS topspace where Nx
   meets finitely many W-elements; each contributes finitely
   many u's from Ux(xw w). *)
let LOCALLY_FINITE_PRODUCT_TUBES = `!(top:A topology) (top':B topology) W U Ux xw.
        locally_finite_in top W /\
        (!w. w IN W ==> FINITE (Ux((xw:(A->bool)->A) w))) /\
        (!w. w IN W ==> Ux(xw w) SUBSET U) /\
        (!u. u IN U ==> open_in (prod_topology top top') u)
        ==> locally_finite_in (prod_topology top top')
              {(w:A->bool) CROSS topspace top' INTER (u:(A#B)->bool) |
               w IN W /\ u IN Ux(xw w)}`;;

(* Helper for product theorem: tube lemma combined with compactness *)
(* Uses compactness to extract finite subcover, then applies tube lemma *)
let COMPACT_TUBE_COVER = `!(top:A topology) (top':B topology) x U.
        compact_space top' /\
        x IN topspace top /\
        (!u. u IN U ==> open_in (prod_topology top top') u) /\
        {x} CROSS topspace top' SUBSET UNIONS U
        ==> ?v Ux. open_in top v /\ x IN v /\
                   FINITE Ux /\ Ux SUBSET (U:((A#B)->bool)->bool) /\
                   v CROSS topspace top' SUBSET UNIONS Ux`;;

(* Engelking 5.1.36: Product of paracompact with compact is paracompact *)
(* Proof uses tube lemma: for each x, {x} CROSS Y is compact, so finitely many
   elements of the cover suffice, and they extend to a tube Vx CROSS Y.
   Apply paracompactness to {Vx}, then use LOCALLY_FINITE_PRODUCT_TUBES. *)
let PARACOMPACT_SPACE_PRODUCT_COMPACT_LEFT = `!(top:A topology) (top':B topology).
        paracompact_space top /\ compact_space top'
        ==> paracompact_space(prod_topology top top')`;;

(* Symmetric version: compact times paracompact is paracompact *)
let PARACOMPACT_SPACE_PRODUCT_COMPACT_RIGHT = `!(top:A topology) (top':B topology).
        compact_space top /\ paracompact_space top'
        ==> paracompact_space(prod_topology top top')`;;

(* Helper: In a paracompact Hausdorff space, an open cover has a locally
   finite open refinement with closures contained in the original cover *)
let PARACOMPACT_HAUSDORFF_CLOSURE_REFINEMENT = `!top:A topology U.
        paracompact_space top /\ hausdorff_space top /\
        (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
        ==> ?V r. (!v. v IN V ==> open_in top v) /\
                  UNIONS V = topspace top /\
                  locally_finite_in top V /\
                  (!v:A->bool. v IN V
                      ==> (r v) IN U /\ top closure_of v SUBSET (r v))`;;

(* Indexed shrinking lemma: for each u IN U, produce v(u) open
   with closure in u, {v(u)} l.f. (by index, not set value) *)
let PARACOMPACT_HAUSDORFF_INDEXED_SHRINKING = `!top:A topology U.
        paracompact_space top /\ hausdorff_space top /\
        (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
        ==> ?v. (!u. u IN U ==> open_in top (v u) /\
                                 top closure_of (v u) SUBSET u) /\
                UNIONS (IMAGE v U) = topspace top /\
                (!x. x IN topspace top
                     ==> ?N. open_in top N /\ x IN N /\
                             FINITE {u | u IN U /\ ~(v u INTER N = {})})`;;

(* Continuity of a sum over a locally finite family *)
let CONTINUOUS_MAP_SUM_LOCALLY_FINITE = `!top (f:K->A->real) (v:K->A->bool) (U:K->bool).
    (!u. u IN U ==> continuous_map(top,euclideanreal) (f u)) /\
    (!u. u IN U ==> !x. x IN topspace top /\ ~(x IN v u)
         ==> f u x = &0) /\
    (!x:A. x IN topspace top
         ==> ?N. open_in top N /\ x IN N /\
                 FINITE {u:K | u IN U /\ ~(v u INTER N = {})})
    ==> continuous_map(top,euclideanreal) (\x. sum U (\u. f u x))`;;

(* Engelking 5.1.9: Partition of unity subordinate to locally finite cover *)
let PARACOMPACT_PARTITION_OF_UNITY = `!top:A topology U.
        paracompact_space top /\ hausdorff_space top /\
        (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
        ==> ?phi. (!u. u IN U
                       ==> continuous_map(top,euclideanreal) (phi u) /\
                           (!x. x IN topspace top ==> &0 <= phi u x) /\
                           {x | x IN topspace top /\ ~(phi u x = &0)}
                             SUBSET u) /\
                  (!x. x IN topspace top
                       ==> ?N. open_in top N /\ x IN N /\
                               FINITE {u | u IN U /\ ~(N INTER
                                 {y | y IN topspace top /\ ~(phi u y = &0)} = {})}) /\
                  (!x. x IN topspace top ==> sum U (\u. phi u x) = &1)`;;

(* Munkres 41.5: Regular Lindelof space is paracompact *)
(* Proof: A countable subcover is sigma-locally-finite; apply Michael's Lemma *)
let REGULAR_LINDELOF_IMP_PARACOMPACT_SPACE = `!top:A topology.
        regular_space top /\ lindelof_space top
        ==> paracompact_space top`;;

(* Corollary of Munkres 41.5: Second-countable regular space is paracompact *)
let SECOND_COUNTABLE_REGULAR_IMP_PARACOMPACT_SPACE = `!top:A topology.
        second_countable top /\ regular_space top
        ==> paracompact_space top`;;

(* Engelking 5.1.35: Perfect preimage of paracompact is paracompact *)
let PARACOMPACT_SPACE_PERFECT_MAP_PREIMAGE = `!top top' (f:A->B).
        perfect_map(top,top') f /\ paracompact_space top'
        ==> paracompact_space top`;;

(* Helper: locally finite is preserved under homeomorphism image *)
let LOCALLY_FINITE_IN_HOMEOMORPHIC_IMAGE = `!(top:A topology) (top':B topology) f g V.
        homeomorphic_maps(top,top') (f,g) /\ locally_finite_in top V
        ==> locally_finite_in top' (IMAGE (IMAGE f) V)`;;

(* Paracompactness of discrete topology *)
let PARACOMPACT_SPACE_DISCRETE_TOPOLOGY = `!u:A->bool. paracompact_space(discrete_topology u)`;;

(* Second countable + locally compact + Hausdorff implies paracompact *)
let SECOND_COUNTABLE_LOCALLY_COMPACT_HAUSDORFF_IMP_PARACOMPACT = `!top:A topology.
        second_countable top /\ locally_compact_space top /\
        hausdorff_space top
        ==> paracompact_space top`;;

(* For Lindelof Hausdorff spaces, regular <=> paracompact *)
let LINDELOF_HAUSDORFF_REGULAR_EQ_PARACOMPACT = `!top:A topology.
        lindelof_space top /\ hausdorff_space top
        ==> (regular_space top <=> paracompact_space top)`;;

(* Munkres Exercise 41.5: Expansion Lemma.
   If {B_alpha} is a locally finite family of subsets of a paracompact
   Hausdorff space X, there is a locally finite family {U_alpha} of open
   sets with B_alpha SUBSET U_alpha for each alpha.
   Proof: Build open cover N from LF of B, get LF closed refinement C,
   then use expansion E(b) = X \ UNIONS{c IN C | c INTER b = {}}. *)
let PARACOMPACT_HAUSDORFF_EXPANSION_LEMMA = `!top (B:(A->bool)->bool).
        paracompact_space top /\ hausdorff_space top /\
        (!b. b IN B ==> b SUBSET topspace top) /\
        locally_finite_in top B
        ==> ?f. (!b. b IN B ==> open_in top (f b)) /\
                (!b. b IN B ==> b SUBSET f b) /\
                locally_finite_in top {f b | b IN B}`;;

(* For regular spaces, paracompact iff every open cover has a
   locally finite closed refinement. *)
let PARACOMPACT_SPACE_EQ_CLOSED_REFINEMENT = `!top:A topology.
        regular_space top
        ==> (paracompact_space top <=>
             !U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
                 ==> ?V. (!v. v IN V ==> closed_in top v) /\
                         UNIONS V = topspace top /\
                         (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                         locally_finite_in top V)`;;

(* For regular spaces, paracompact iff every open cover has a
   locally finite refinement (not necessarily open or closed). *)
let PARACOMPACT_SPACE_EQ_LOCALLY_FINITE_REFINEMENT = `!top:A topology.
        regular_space top
        ==> (paracompact_space top <=>
             !U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
                 ==> ?V. UNIONS V = topspace top /\
                         (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                         locally_finite_in top V)`;;

(* ------------------------------------------------------------------------- *)
(* Basic definition of the small inductive dimension relation ind t <= n.    *)
(* We plan to prove most of the theorems in R^n so this is as good a         *)
(* definition as any other, but the present stuff works in any top space.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("dimension_le",(12,"right"));;

let DIMENSION_LE_RULES,DIMENSION_LE_INDUCT,DIMENSION_LE_CASES =
  new_inductive_definition
  `!top n. -- &1 <= n /\
           (!v a. open_in top v /\ a IN v
                  ==> ?u. a IN u /\ u SUBSET v /\ open_in top u /\
                          subtopology top (top frontier_of u)
                          dimension_le (n - &1))
            ==> (top:A topology) dimension_le (n:int)`;;

let DIMENSION_LE_NEIGHBOURHOOD_BASE = `!(top:A topology) n.
        top dimension_le n <=>
        -- &1 <= n /\
        neighbourhood_base_of
         (\u. open_in top u /\
              (subtopology top (top frontier_of u))
              dimension_le (n - &1)) top`;;

let DIMENSION_LE_BOUND = `!top:(A)topology n. top dimension_le n ==> -- &1 <= n`;;

let DIMENSION_LE_MONO = `!top:(A)topology m n. top dimension_le m /\ m <= n ==> top dimension_le n`;;

let DIMENSION_LE_EQ_EMPTY = `!top:(A)topology. top dimension_le (-- &1) <=> topspace top = {}`;;

let DIMENSION_LE_0_NEIGHBOURHOOD_BASE_OF_CLOPEN = `!top:A topology.
        top dimension_le &0 <=>
        neighbourhood_base_of (\u. closed_in top u /\ open_in top u) top`;;

let DIMENSION_LE_SUBTOPOLOGY = `!top n s:A->bool.
        top dimension_le n ==> (subtopology top s) dimension_le n`;;

let DIMENSION_LE_SUBTOPOLOGIES = `!top n s t:A->bool.
        s SUBSET t /\
        subtopology top t dimension_le n
        ==> (subtopology top s) dimension_le n`;;

let DIMENSION_LE_EQ_SUBTOPOLOGY = `!top s:A->bool n.
        (subtopology top s) dimension_le n <=>
        -- &1 <= n /\
        !v a. open_in top v /\ a IN v /\ a IN s
              ==> ?u. a IN u /\ u SUBSET v /\ open_in top u /\
                      subtopology top
                       ((subtopology top s frontier_of (s INTER u)))
                      dimension_le (n - &1)`;;

let HOMEOMORPHIC_SPACE_DIMENSION_LE = `!(top:A topology) (top':B topology) n.
        top homeomorphic_space top'
        ==> (top dimension_le n <=> top' dimension_le n)`;;

let DIMENSION_LE_RETRACTION_MAP_IMAGE = `!top top' n (r:A->B).
        retraction_map(top,top') r /\ top dimension_le n
        ==> top' dimension_le n`;;

let DIMENSION_LE_DISCRETE_TOPOLOGY = `!u:A->bool. (discrete_topology u) dimension_le &0`;;

let ZERO_DIMENSIONAL_IMP_COMPLETELY_REGULAR_SPACE = `!top:A topology. top dimension_le &0 ==> completely_regular_space top`;;

let ZERO_DIMENSIONAL_IMP_REGULAR_SPACE = `!top:A topology. top dimension_le &0 ==> regular_space top`;;

(* ------------------------------------------------------------------------- *)
(* The Cantor space {0,1}^N and its embedding in the reals as the Cantor set *)
(* via the ternary Cantor map: a |-> sum_{k=0}^inf 2*a(k) / 3^{k+1}          *)
(* ------------------------------------------------------------------------- *)

let cantor_space = new_definition
 `cantor_space = product_topology (:num) (\n:num. discrete_topology (:bool))`;;

let cantor_term = new_definition
 `cantor_term (a:num->bool) k = (if a k then &2 else &0) / &3 pow (k + 1)`;;

let cantor_map = new_definition
 `cantor_map (a:num->bool) = real_infsum (from 0) (cantor_term a)`;;

let cantor_set = new_definition
 `cantor_set = IMAGE cantor_map (:num->bool)`;;

let TOPSPACE_CANTOR_SPACE = `topspace cantor_space = (:num->bool)`;;

let COMPACT_SPACE_CANTOR_SPACE = `compact_space cantor_space`;;

let HAUSDORFF_SPACE_CANTOR_SPACE = `hausdorff_space cantor_space`;;

let METRIZABLE_SPACE_CANTOR_SPACE = `metrizable_space cantor_space`;;

let ZERO_DIMENSIONAL_CANTOR_SPACE = `cantor_space dimension_le &0`;;

let NONEMPTY_TOPSPACE_CANTOR_SPACE = `~(topspace cantor_space = {})`;;

(* The Cantor space has no isolated points (is "perfect") *)

let PERFECT_CANTOR_SPACE = `!x:num->bool. x IN topspace cantor_space
                 ==> x IN cantor_space derived_set_of (topspace cantor_space)`;;

let PERFECT_CANTOR_SPACE_EQ = `cantor_space derived_set_of (topspace cantor_space) =
   topspace cantor_space`;;

(* Each term is non-negative *)

let CANTOR_TERM_POS = `!a:num->bool k. &0 <= cantor_term a k`;;

(* Each term bounded by corresponding geometric term *)

let CANTOR_TERM_BOUND = `!a:num->bool k. cantor_term a k <= &2 / &3 pow (k + 1)`;;

(* Monotonicity of partial sums: more terms of non-negative series *)

let CANTOR_PARTIAL_SUM_MONO = `!a:num->bool m n. m <= n
     ==> sum(0..m) (cantor_term a) <= sum(0..n) (cantor_term a)`;;

(* Partial sum formula for the geometric series sum_{k=0}^n 2/3^{k+1} *)

let SUM_TWOTHIRDS = `!n. sum(0..n) (\k. &2 / &3 pow (k + 1)) = &1 - (&1 / &3) pow (n + 1)`;;

(* The geometric dominating series sums to 1 *)

let TWOTHIRDS_SUMS = `((\k. &2 / &3 pow (k + 1)) real_sums &1) (from 0)`;;

(* Cantor terms are summable by comparison with the geometric series *)

let CANTOR_MAP_SUMMABLE = `!a:num->bool. real_summable (from 0) (cantor_term a)`;;

(* The series converges to cantor_map *)

let CANTOR_MAP_SUMS = `!a:num->bool. (cantor_term a real_sums cantor_map a) (from 0)`;;

(* Upper bound: each term <= 2/3^{k+1}, and the geometric series sums to 1 *)

let CANTOR_MAP_LE_ONE = `!a:num->bool. cantor_map a <= &1`;;

(* Partial sums bounded by the limit (monotone convergence) *)

let CANTOR_MAP_GE_PARTIAL_SUM = `!a:num->bool n. sum(0..n) (cantor_term a) <= cantor_map a`;;

(* Tail bound: cantor_map - partial_sum <= geometric tail *)

let CANTOR_MAP_PARTIAL_SUM_BOUND = `!a:num->bool n. cantor_map a - sum(0..n) (cantor_term a) <=
                   (&1 / &3) pow (n + 1)`;;

(* Non-negativity: follows from partial sums being non-negative *)

let CANTOR_MAP_POS = `!a:num->bool. &0 <= cantor_map a`;;

let CANTOR_MAP_RANGE = `!a:num->bool. cantor_map a IN real_interval[&0,&1]`;;

(* Term continuity: each cantor_term a k is continuous in a *)

let CANTOR_TERM_CONTINUOUS = `!k. continuous_map (cantor_space, euclideanreal)
        (\a:num->bool. cantor_term a k)`;;

(* Cantor map continuity: uniform limit of continuous partial sums *)
let CANTOR_MAP_CONTINUOUS = `continuous_map (cantor_space, euclideanreal) cantor_map`;;

(* At the first disagreement k where a k /\ ~b k, the partial sums differ *)

let CANTOR_PARTIAL_SUM_DIFF_AT_K = `!a b:num->bool k.
     (!j. j < k ==> a j = b j) /\ a k /\ ~(b k)
     ==> sum(0..k) (cantor_term a) =
         sum(0..k) (cantor_term b) + &2 / &3 pow (k + 1)`;;

(* If a and b first disagree at k with a(k) true, then cantor_map b < cantor_map a *)

let CANTOR_MAP_STRICT_LT = `!a b:num->bool k.
     (!j. j < k ==> a j = b j) /\ a k /\ ~(b k)
     ==> cantor_map b < cantor_map a`;;

(* Injectivity of cantor_map *)

let CANTOR_MAP_INJECTIVE = `!a b:num->bool. cantor_map a = cantor_map b <=> a = b`;;

let CANTOR_MAP_EMBEDDING = `embedding_map (cantor_space,euclideanreal) cantor_map`;;

let CANTOR_MAP_CLOSED_IMAGE = `closed_in euclideanreal (IMAGE cantor_map (:num->bool))`;;

let CANTOR_MAP_IMAGE_SUBSET_INTERVAL = `IMAGE cantor_map (:num->bool) SUBSET real_interval [&0,&1]`;;

let CANTOR_MAP_CLOSED_IN_INTERVAL = `closed_in (subtopology euclideanreal (real_interval [&0,&1]))
             (IMAGE cantor_map (:num->bool))`;;

let CANTOR_SET_SUBSET_INTERVAL = `cantor_set SUBSET real_interval [&0,&1]`;;

let CLOSED_IN_CANTOR_SET = `closed_in euclideanreal cantor_set`;;

let CLOSED_IN_CANTOR_SET_INTERVAL = `closed_in (subtopology euclideanreal (real_interval [&0,&1])) cantor_set`;;

let CANTOR_SPACE_HOMEOMORPHIC_CANTOR_SET = `cantor_space homeomorphic_space
   subtopology euclideanreal cantor_set`;;

(* ------------------------------------------------------------------------- *)
(* Alexandroff-Hausdorff Theorem: H-Y Theorem 3-28.                          *)
(* Every nonempty compact metrizable space is a continuous image of          *)
(* the Cantor space.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Key refinement lemma: refine a locally constant assignment *)
let LOCALLY_CONSTANT_REFINEMENT = `!m:A metric (h:(num->bool)->(A->bool)) e.
    compact_space (mtopology m) /\
    &0 < e /\
    (!x. closed_in (mtopology m) (h x)) /\
    (!x. ~(h x = {})) /\
    (!x. h x SUBSET mspace m) /\
    (!x:num->bool. ?u. open_in cantor_space u /\ x IN u /\
      (!y. y IN u ==> h y = h x)) /\
    (!a. a IN mspace m ==> ?x. a IN h x)
    ==> ?h':(num->bool)->(A->bool).
         (!x. closed_in (mtopology m) (h' x)) /\
         (!x. ~(h' x = {})) /\
         (!x. h' x SUBSET mspace m) /\
         (!x. mdiameter m (h' x) < e) /\
         (!x. h' x SUBSET h x) /\
         (!x. ?u. open_in cantor_space u /\ x IN u /\
           (!y. y IN u ==> h' y = h' x)) /\
         (!a. a IN mspace m ==> ?x. a IN h' x)`;;

(* Main theorem: Alexandroff-Hausdorff *)
let ALEXANDROFF_HAUSDORFF = `!top:A topology.
        compact_space top /\ metrizable_space top /\ ~(topspace top = {})
        ==> ?f. continuous_map(cantor_space, top) f /\
                IMAGE f (topspace cantor_space) = topspace top`;;

(* ------------------------------------------------------------------ *)
(* Peano space properties: ULC and path-connectedness.                *)
(* ULC: Whyburn, Analytic Topology, Ch. I Sec. 15 (15.5);             *)
(* H-Y Theorem 3-13; Willard, General Topology, 31.4.                 *)
(* ------------------------------------------------------------------ *)

(* Uniform local connectedness for compact metrizable locally connected spaces:
   For every e > 0, there exists d > 0 such that any two points within d
   lie in a connected set of diameter < e. *)
let DENSE_FUNCTION_ON_DYADIC = `!m:A metric e.
     mcomplete m /\ &0 < e /\
     (!eps. &0 < eps
            ==> ?del. &0 < del /\
                      !x y:A. x IN mspace m /\ y IN mspace m /\
                              mdist m (x,y) < del
                              ==> ?c. connected_in(mtopology m) c /\
                                      x IN c /\ y IN c /\
                                      mbounded m c /\
                                      mdiameter m c < eps)
     ==> ?d. &0 < d /\
             !x y:A. x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < d
                     ==> ?f s. s SUBSET real_interval[&0,&1] /\
                               real_interval[&0,&1] SUBSET
                                 euclideanreal closure_of s /\
                               &0 IN s /\ &1 IN s /\
                               (f:real->A)(&0) = x /\ f(&1) = y /\
                               IMAGE f s SUBSET mspace m /\
                               (!a. a IN s ==> mdist m (x,f a) <= e / &4) /\
                               uniformly_continuous_map
                                 (submetric real_euclidean_metric s, m) f`;;

(* Core lemma: nearby points in compact metrizable locally connected space
   can be joined by a path of small diameter.
   Proof uses multi-scale ULC chain construction (Willard 31.4):
   1. Get ULC sequences eps_k, del_k at decreasing scales
   2. Build iterated chains: refine at each level
   3. Define function on dense set, show uniformly continuous
   4. Extend to [0,1] via extension theorem
   5. Extension gives continuous path with small diameter *)
let COMPACT_LOCALLY_CONNECTED_NEARBY_PATH = `!m:A metric.
     compact_space (mtopology m) /\ locally_connected_space (mtopology m)
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !x y. x IN mspace m /\ y IN mspace m /\
                            mdist m (x,y) < d
                           ==> ?g. path_in (mtopology m) g /\
                                   g(&0) = x /\ g(&1) = y /\
                                   IMAGE g (real_interval[&0,&1])
                                     SUBSET mspace m /\
                                   mdiameter m
                                     (IMAGE g (real_interval[&0,&1])) < e`;;

(* Key: compact metrizable locally connected =>        *)
(* locally path connected. Use nearby paths + chains.  *)
let COMPACT_METRIZABLE_LOCALLY_CONNECTED_IMP_LOCALLY_PATH_CONNECTED = `!top:A topology.
     compact_space top /\ metrizable_space top /\
     locally_connected_space top
     ==> locally_path_connected_space top`;;

(* Compact metrizable connected locally connected => path connected *)
let COMPACT_METRIZABLE_PEANO_IMP_PATH_CONNECTED = `!top:A topology.
     compact_space top /\ metrizable_space top /\
     connected_space top /\ locally_connected_space top
     ==> path_connected_space top`;;

(* ------------------------------------------------------------------------- *)
(* Hahn-Mazurkiewicz theorem (backward direction).                           *)
(* Whyburn, Analytic Topology, Theorem (4.1); H-Y Theorem 3-30;              *)
(* Willard, General Topology, Theorem 31.5.                                  *)
(* Every compact, connected, locally connected, metrizable, nonempty space   *)
(* is a continuous image of [0,1].                                           *)
(* ------------------------------------------------------------------------- *)

(* Gap-filling extension: extend continuous surjection from closed C in [0,1] *)
(* Proof sketch: X is path-connected (Peano space). For each gap (a,b) of
   [0,1] \ C, connect f(a) to f(b) by a path. Use ULPC for diameter control
   near boundary points of C. Define F by f on C and paths on gaps. *)
let PEANO_GAP_FILLING_EXTENSION = `!top:A topology (f:real->A) C.
    compact_space top /\ metrizable_space top /\
    connected_space top /\ locally_connected_space top /\
    ~(topspace top = {}) /\
    C SUBSET real_interval[&0,&1] /\
    closed_in (subtopology euclideanreal (real_interval[&0,&1])) C /\
    continuous_map (subtopology euclideanreal C, top) f /\
    IMAGE f C = topspace top
    ==> ?F. continuous_map
              (subtopology euclideanreal (real_interval[&0,&1]), top) F /\
            IMAGE F (real_interval[&0,&1]) = topspace
              top`;;

(* Backward direction: Peano space is continuous image of [0,1] *)
(* Proof: compose Alexandroff-Hausdorff surjection with inverse of Cantor
   embedding, then extend via gap-filling *)
let HAHN_MAZURKIEWICZ_IMP = `!top:A topology.
        compact_space top /\
        connected_space top /\
        locally_connected_space top /\
        metrizable_space top /\
        ~(topspace top = {})
        ==> ?f. continuous_map
                  (subtopology euclideanreal (real_interval[&0,&1]),top) f /\
                IMAGE f (real_interval[&0,&1]) = topspace top`;;

(* The full Hahn-Mazurkiewicz theorem: Whyburn (4.1); H-Y 3-30; Willard 31.5 *)
let HAHN_MAZURKIEWICZ = `!top:A topology.
        hausdorff_space top
        ==> ((?f. continuous_map
                   (subtopology euclideanreal (real_interval[&0,&1]),top)
                   f /\
                  IMAGE f (real_interval[&0,&1]) = topspace top) <=>
             compact_space top /\
             connected_space top /\
             locally_connected_space top /\
             metrizable_space top /\
             ~(topspace top = {}))`;;

(* Compact case: H-Y Theorem 3-15; Whyburn (5.1). Compact + connected +     *)
(* locally connected ==> path connected, via H-M backward (the space is     *)
(* a continuous image of [0,1], which is path connected).                    *)

let COMPACT_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED = `!m:A metric s.
        compact_in (mtopology m) s /\
        connected_in (mtopology m) s /\
        locally_connected_space (subtopology (mtopology m) s)
        ==> path_connected_space (subtopology (mtopology m) s)`;;

(* Mcomplete case: Whyburn, Analytic Topology, Theorem (5.4); H-Y 3-17.      *)
(* Any two points sit inside an LC continuum (by the Imbedding Theorem),     *)
(* and the compact case gives path-connectedness of that continuum.          *)

let MCOMPLETE_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED_IN =
  `!m:A metric s.
        mcomplete(submetric m s) /\
        connected_in (mtopology m) s /\
        locally_connected_space (subtopology (mtopology m) s)
        ==> path_connected_space (subtopology (mtopology m) s)`;;

let MCOMPLETE_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED = `!m:A metric.
        mcomplete m /\
        connected_space (mtopology m) /\
        locally_connected_space (mtopology m)
        ==> path_connected_space (mtopology m)`;;

(* Whyburn, Analytic Topology, Corollaries (5.2)-(5.3). *)
let LOCALLY_COMPACT_CONNECTED_IMP_PATH_CONNECTED_SPACE = `!m:A metric s.
        locally_compact_space (subtopology (mtopology m) s) /\
        connected_in (mtopology m) s /\
        locally_connected_space (subtopology (mtopology m) s)
        ==> path_connected_space (subtopology (mtopology m) s)`;;

(* The locally-path-connected part extracted as a standalone theorem:        *)
(* locally compact + locally connected ==> locally path connected.           *)

let LOCALLY_COMPACT_LOCALLY_CONNECTED_IMP_LOCALLY_PATH_CONNECTED_SPACE = `!m:A metric s.
        locally_compact_space(subtopology (mtopology m) s) /\
        locally_connected_space(subtopology (mtopology m) s)
        ==> locally_path_connected_space(subtopology (mtopology m) s)`;;

let LOCALLY_COMPACT_LOCALLY_PATH_CONNECTED_EQ_LOCALLY_CONNECTED_SPACE = `!m:A metric s.
        locally_compact_space(subtopology (mtopology m) s)
        ==> (locally_path_connected_space(subtopology (mtopology m) s) <=>
             locally_connected_space(subtopology (mtopology m) s))`;;

let MCOMPLETE_IN_LOCALLY_COMPACT_IMP_LOCALLY_COMPACT = `!m:A metric s.
        locally_compact_space(mtopology m) /\
        mcomplete(submetric m s) /\
        s SUBSET mspace m
        ==> locally_compact_space(subtopology (mtopology m) s)`;;

(* mcomplete + locally connected ==> locally path connected.               *)
(* Uses Alexandrov's theorem (open subsets of completely metrizable         *)
(* spaces are completely metrizable) combined with the Menger theorem.     *)

let MCOMPLETE_LOCALLY_CONNECTED_IMP_LOCALLY_PATH_CONNECTED = `!m:A metric.
        mcomplete m /\ locally_connected_space (mtopology m)
        ==> locally_path_connected_space (mtopology m)`;;

let MCOMPLETE_LOCALLY_PATH_CONNECTED_EQ_LOCALLY_CONNECTED = `!m:A metric.
        mcomplete m
        ==> (locally_path_connected_space(mtopology m) <=>
             locally_connected_space(mtopology m))`;;

let COMPLETELY_METRIZABLE_LOCALLY_PATH_CONNECTED_EQ_LOCALLY_CONNECTED =
  `!top:A topology.
        completely_metrizable_space top
        ==> (locally_path_connected_space top <=>
             locally_connected_space top)`;;

(* completely_metrizable_space + connected + locally connected            *)
(* ==> path connected. (Menger via completely_metrizable_space)           *)

let COMPLETELY_METRIZABLE_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED =
  `!top:A topology.
        completely_metrizable_space top /\
        connected_space top /\
        locally_connected_space top
        ==> path_connected_space top`;;

(* ------------------------------------------------------------------------- *)
(* Theorems from Kuratowski's "Remark on an Invariance Theorem", Fundamenta  *)
(* Mathematicae vol 37 (1950), pp. 251-252. The idea is that in suitable     *)
(* spaces, to show "number of components of the complement" (without         *)
(* distinguishing orders of infinity) is a homeomorphic invariant, it        *)
(* suffices to show it for closed subsets. Kuratowski states the main result *)
(* for a "locally connected continuum", and seems clearly to be implicitly   *)
(* assuming that means metrizable. We call out the general topological       *)
(* hypotheses more explicitly, which do not however include connectedness.   *)
(* ------------------------------------------------------------------------- *)

let SEPARATION_BY_CLOSED_INTERMEDIATES_COUNT = `!(top:A topology) s n.
        hereditarily normal_space top /\
        (?u. u HAS_SIZE n /\
             pairwise (separated_in top) u /\
             (!t. t IN u ==> ~(t = {})) /\
             UNIONS u = topspace top DIFF s)
        ==>  ?c. closed_in top c /\ c SUBSET s /\
                 !d. closed_in top d /\ c SUBSET d /\ d SUBSET s
                     ==> ?u. u HAS_SIZE n /\
                             pairwise (separated_in top) u /\
                             (!t. t IN u ==> ~(t = {})) /\
                             UNIONS u = topspace top DIFF d`;;

let SEPARATION_BY_CLOSED_INTERMEDIATES_GEN = `!(top:A topology) s.
        hereditarily normal_space top /\
        ~connected_in top (topspace top DIFF s)
        ==>  ?c. closed_in top c /\ c SUBSET s /\
                 !d. closed_in top d /\ c SUBSET d /\ d SUBSET s
                     ==> ~connected_in top (topspace top DIFF d)`;;

let SEPARATION_BY_CLOSED_INTERMEDIATES_EQ_COUNT = `!(top:A topology) s n.
        locally_connected_space top /\ hereditarily normal_space top
        ==> ((?u. u HAS_SIZE n /\
                  pairwise (separated_in top) u /\
                  (!t. t IN u ==> ~(t = {})) /\
                  UNIONS u = topspace top DIFF s) <=>
             (?c. closed_in top c /\ c SUBSET s /\
                  !d. closed_in top d /\ c SUBSET d /\ d SUBSET s
                      ==> ?u. u HAS_SIZE n /\
                              pairwise (separated_in top) u /\
                              (!t. t IN u ==> ~(t = {})) /\
                              UNIONS u = topspace top DIFF d))`;;

let SEPARATION_BY_CLOSED_INTERMEDIATES_EQ_GEN = `!(top:A topology) s.
        locally_connected_space top /\ hereditarily normal_space top
        ==> (~connected_in top (topspace top DIFF s) <=>
             ?c. closed_in top c /\ c SUBSET s /\
                 !d. closed_in top d /\ c SUBSET d /\ d SUBSET s
                     ==> ~connected_in top (topspace top DIFF d))`;;

let KURATOWSKI_COMPONENT_NUMBER_INVARIANCE = `!top:A topology.
      compact_space top /\
      hausdorff_space top /\
      locally_connected_space top /\
      hereditarily normal_space top
      ==> ((!s t n.
              closed_in top s /\ closed_in top t /\
              (subtopology top s) homeomorphic_space (subtopology top t)
              ==> (connected_components_of
                    (subtopology top (topspace top DIFF s)) HAS_SIZE n <=>
                   connected_components_of
                    (subtopology top (topspace top DIFF t)) HAS_SIZE n)) <=>
           (!s t n.
              (subtopology top s) homeomorphic_space (subtopology top t)
              ==> (connected_components_of
                    (subtopology top (topspace top DIFF s)) HAS_SIZE n <=>
                   connected_components_of
                    (subtopology top (topspace top DIFF t)) HAS_SIZE n)))`;;
