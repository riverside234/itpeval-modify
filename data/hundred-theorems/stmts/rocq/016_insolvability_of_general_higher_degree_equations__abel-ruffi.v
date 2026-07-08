From Corelib Require Import Setoid.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp Require Import all_solvable all_field polyrcf.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
From Abel Require Import various classic_ext map_gal algR.
From Abel Require Import char0 cyclotomic_ext real_closed_ext.

(*****************************************************************************)
(* We work inside a enclosing splittingFieldType L over a base field F0      *)
(*                                                                           *)
(*     radical U x n := x is a radical element of degree n over U            *)
(*    pradical U x p := x is a radical element of prime degree p over U      *)
(*   r.-tower U e pw := e is a chain of elements of L such that              *)
(*                      forall i, r <<U & take i e>> e`_i pw`_i              *)
(*        r.-ext U V := there exists e and pw such that <<U & e>> = V        *)
(*                      and r.-tower U e p  w.                               *)
(* solvable_by r E F := there is a field K, such that F <= K and r.-ext E K  *)
(*                      if p has roots rs, solvable_by radicals E <<E, rs>>  *)
(* solvable_ext_poly p := the Galois group of p is solvable in any splitting *)
(*                      field L for p. (i.e. p has roots rs in a splitting   *)
(*                      then, 'Gal(<<1 & rs>>/1) is solbable.                *)
(*                      This is equivalent to general classical existence    *)
(*                      or constructive existence over rat, of a splitting   *)
(*                      field for p, in which its  Galois group is solvable  *)
(* solvable_by_radical_poly p := solvable_by radical 1 <<1; rs>> in L        *)
(*                      L being any splitting field L where p has roots rs   *)
(*                      and which contains a n nth primitive root of unity,  *)
(*                      (we me make n explicit in ext_solvable_by_radical)   *)
(*                      This is equivalent to general classical existence    *)
(*                      or constructive existence over rat, of a splitting   *)
(*                      field for p, in which the roots of p are rs, and in  *)
(*                      which solvable_by radical 1 <<1; rs>> in L.          *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").
Local Notation "2" := 2%:R : ring_scope.
Local Notation "3" := 3%:R : ring_scope.
Local Notation "4" := 4%:R : ring_scope.
Local Notation "5" := 5%:R : ring_scope.

CoInductive unsplit_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | UnsplitLo (j : 'I_m) of i = lshift _ j : unsplit_spec i (inl _ j) true
  | UnsplitHi (k : 'I_n) of i = rshift _ k : unsplit_spec i (inr _ k) false.

Lemma unsplitP m n (i : 'I_(m + n)) : unsplit_spec i (split i) (i < m)%N.
Proof.
Admitted.

Let ratr_p' : map_poly ratr p %= \prod_(x <- rp') ('X - x%:P).
Proof.
Admitted.

Let rp'_uniq : uniq rp'.
Proof.
Admitted.

Let d := (size p).-1.
Hypothesis d_prime : prime d.
Hypothesis count_rp' : count [pred x | iota x \isn't Num.real] rp' = 2%N.

Let rp := [seq x <- rp' | iota x \isn't Num.real]
          ++ [seq x <- rp' | iota x \is Num.real].

Let rp_perm : perm_eq rp rp'. Proof.
Admitted.
Let rp_uniq : uniq rp. Proof.
Admitted.
Let ratr_p : map_poly ratr p %= \prod_(x <- rp) ('X - x%:P).
Proof.
Admitted.

Lemma nth_rp_real i : (iota rp`_i \is Num.
Proof.
Admitted.

Let K_split_p : splittingFieldFor 1%AS (map_poly ratr p) K.
Proof.
Admitted.

Let p_sep : separable_poly p.
Proof.
Admitted.

Let d_gt0 : (d > 0)%N.
Proof.
Admitted.

Let d_gt1 : (d > 1)%N.
Proof.
Admitted.

Lemma size_rp : size rp = d.
Proof.
Admitted.

Let i0 := Ordinal d_gt0.
Let i1 := Ordinal d_gt1.

Lemma ratr_p_over : map_poly (ratr : rat -> L) p \is a polyOver 1%AS.
Proof.
Admitted.

Lemma galois1K : galois 1%VS K.
Proof.
Admitted.

Lemma all_rpK : all (mem K) rp.
Proof.
Admitted.

Lemma root_p : root (p ^^ ratr) =i rp.
Proof.
Admitted.

Lemma rp_roots : all (root (map_poly ratr p)) rp.
Proof.
Admitted.

Lemma ratr_p_rp i : (i < d)%N -> (map_poly ratr p).
Proof.
Admitted.

Lemma rpK i : (i < d)%N -> rp`_i \in K.
Proof.
Admitted.

Lemma eq_size_rp : size rp == d.
Proof.
Admitted.
Let trp := Tuple eq_size_rp.

Lemma gal_perm_eq (g : gal_of K) : perm_eq [seq g x | x <- trp] trp.
Proof.
Admitted.

Definition gal_perm g : 'S_d := projT1 (sig_eqW (tuple_permP (gal_perm_eq g))).

Lemma gal_permP g i : rp`_(gal_perm g i) = g (rp`_i).
Proof.
Admitted.

(** N/A **)
Lemma gal_perm_is_morphism :
  {in ('Gal(K / 1%AS))%G &, {morph gal_perm : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
Admitted.
Canonical gal_perm_morphism :=  Morphism gal_perm_is_morphism.

Lemma minPoly_rp x : x \in rp -> minPoly 1%VS x %= map_poly ratr p.
Proof.
Admitted.

Lemma injm_gal_perm : ('injm gal_perm)%g.
Proof.
Admitted.

Lemma dvd_dG : (d %| #|'Gal(K / 1%VS)%g|)%N.
Proof.
Admitted.

Definition gal_cycle : gal_of K := projT1 (Cauchy d_prime dvd_dG).

Lemma gal_cycle_order : #[gal_cycle]%g = d.
Proof.
Admitted.

Lemma gal_perm_cycle_order : #[(gal_perm gal_cycle)]%g = d.
Proof.
Admitted.

Definition conjL : {lrmorphism L -> L} :=
  projT1 (restrict_aut_to_normal_num_field iota Num.conj_op).

Definition iotaJ : {morph iota : x / conjL x >-> x^*} :=
  projT2 (restrict_aut_to_normal_num_field _ _).

Lemma conjLK : involutive conjL.
Proof.
Admitted.

Lemma conjL_rp : {mono conjL : x / x \in rp}.
Proof.
Admitted.

Lemma conjL_K : {mono conjL : x / x \in K}.
Proof.
Admitted.

Lemma conj_rp0 : conjL rp`_i0 = rp`_i1.
Proof.
Admitted.

Lemma conj_rp1 : conjL rp`_i1 = rp`_i0.
Proof.
Admitted.

Lemma conj_nth_rp (i : 'I_d) : conjL (rp`_i) = rp`_(tperm i0 i1 i).
Proof.
Admitted.

Definition galJ : gal_of K := gal K (AHom (linfun_is_ahom conjL)).

Lemma galJ_tperm : gal_perm galJ = tperm i0 i1.
Proof.
Admitted.

Lemma surj_gal_perm : (gal_perm @* 'Gal (K / 1%AS) = 'Sym_('I_d))%g.
Proof.
Admitted.

Lemma isog_gal_perm : 'Gal (K / 1%AS) \isog 'Sym_('I_d).
Proof.
Admitted.

Lemma isog_gal : 'Gal ({:numfield p} / 1%AS) \isog 'Sym_('I_d).
Proof.
Admitted.

End PrimeDegreeTwoNonRealRoots.
End PrimeDegreeTwoNonRealRoots.
Module PDTNRR := PrimeDegreeTwoNonRealRoots.

Section Example1.

Definition poly_example_int : {poly int} := 'X^5 - 4 *: 'X + 2.
Definition poly_example : {poly rat} := 'X^5 - 4 *: 'X + 2.

Local Definition pesimp := (coefD, coefN, coefB, coefZ, coefXn, coefX, coefC,
  hornerD, hornerN, hornerC, hornerZ, hornerX, hornerXn, rmorph_nat).

Lemma polyCn (R : ringType) n : n%:R%:P = n%:R :> {poly R}.
Proof.
Admitted.

Lemma poly_exampleEint : poly_example = map_poly intr poly_example_int.
Proof.
Admitted.

Lemma size_poly_example_int : size poly_example_int = 6%N.
Proof.
Admitted.

Lemma size_poly_example : size poly_example = 6%N.
Proof.
Admitted.

Lemma poly_example_int_neq0 : poly_example_int != 0.
Proof.
Admitted.

Lemma poly_example_neq0 : poly_example != 0.
Proof.
Admitted.
#[local] Hint Resolve poly_example_neq0 : core.

Lemma poly_example_monic : poly_example \is monic.
Proof.
Admitted.
#[local] Hint Resolve poly_example_monic : core.

Lemma irreducible_example : irreducible_poly poly_example.
Proof.
Admitted.
#[local] Hint Resolve irreducible_example : core.

Lemma separable_example : separable_poly poly_example.
Proof.
Admitted.
#[local] Hint Resolve separable_example : core.

Lemma prime_example : prime (size poly_example).
Proof.
Admitted.

(* Using the package real_closed, we should be able to monitor the sign of    *)
(* the derivative, and find that the polynomial has exactly three real roots. *)
Definition example_roots : seq algC :=
  map (numfield_inC poly_example) (numfield_roots poly_example).

Lemma ratr_example_poly :
  poly_example ^^ ratr = \prod_(x <- example_roots) ('X - x%:P).
Proof.
Admitted.

Lemma size_example_roots : size example_roots = 5%N.
Proof.
Admitted.

Lemma example_roots_uniq : uniq example_roots.
Proof.
Admitted.

Lemma deriv_poly_example : poly_example^`() = 5%:R *: 'X^4 - 4%:R%:P.
Proof.
Admitted.

Lemma deriv_poly_example_neq0 : poly_example^`() != 0.
Proof.
Admitted.
#[local] Hint Resolve deriv_poly_example_neq0 : core.

Definition alpha : algR := Num.sqrt (2%:R / Num.sqrt 5%:R).

Lemma alpha_gt0 : alpha > 0.
Proof.
Admitted.

Lemma rootsR_deriv_poly_example :
  rootsR (poly_example^`() ^^ ratr) = [:: - alpha; alpha].
Proof.
Admitted.

Lemma count_roots_ex : count [predC Creal] example_roots = 2%N.
Proof.
Admitted.

Lemma example_not_solvable_by_radicals :
  ~ solvable_by_radical_poly ('X^5 - 4 *: 'X + 2 : {poly rat}).
Proof.
Admitted.

End Example1.

Section Formula.
Definition prim1root_ n := projT1 (@C_prim_root_exists n.-1.+1 isT).

Lemma prim1rootP n : (n > 0)%N -> n.
Proof.
Admitted.

Inductive const := Zero | One | URoot of nat.
Inductive binOp := Add | Mul.
Inductive unOp := Opp | Inv | Exp of nat | Root of nat.
Inductive algterm (F : Type) : Type :=
| Base of F
| Const of const
| UnOp of unOp & algterm F
| BinOp of binOp & algterm F & algterm F.
Arguments Const {F}.

Definition encode_const (c : const) : nat :=
   match c with Zero => 0 | One => 1 | URoot n => n.+2 end.
Definition decode_const (n : nat) : const :=
   match n with 0 => Zero | 1 => One | n.+2 => URoot n end.
Lemma code_constK : cancel encode_const decode_const.
Proof.
Admitted.
HB.instance Definition _ := Countable.copy const (can_type code_constK).

Definition encode_binOp (c : binOp) : bool :=
   match c with Add => false | Mul => true end.
Definition decode_binOp (b : bool) : binOp :=
   match b with false => Add | _ => Mul end.
Lemma code_binOpK : cancel encode_binOp decode_binOp.
Proof.
Admitted.
HB.instance Definition _ := Countable.copy binOp (can_type code_binOpK).

Definition encode_unOp (c : unOp) : nat + nat :=
   match c with Opp => inl _ 0%N | Inv => inl _ 1%N
           | Exp n => inl _ n.+2 | Root n => inr _ n end.
Definition decode_unOp (n : nat + nat) : unOp :=
   match n with inl 0 => Opp | inl 1 => Inv
           | inl n.+2 => Exp n | inr n => Root n end.
Lemma code_unOpK : cancel encode_unOp decode_unOp.
Proof.
Admitted.
HB.instance Definition _ := Countable.copy unOp (can_type code_unOpK).

Fixpoint encode_algT F (f : algterm F) : GenTree.tree (F + const) :=
  let T_ isbin := if isbin then binOp else unOp in
  match f with
  | Base x => GenTree.Leaf (inl x)
  | Const c => GenTree.Leaf (inr c)
  | UnOp u f1 => GenTree.Node (pickle (inl u : unOp + binOp))
                              [:: encode_algT f1]
  | BinOp b f1 f2 => GenTree.Node (pickle (inr b : unOp + binOp))
                                  [:: encode_algT f1; encode_algT f2]
  end.
Fixpoint decode_algT F (t : GenTree.tree (F + const)) : algterm F :=
  match t with
  | GenTree.Leaf (inl x) => Base x
  | GenTree.Leaf (inr c) => Const c
  | GenTree.Node n fs =>
    match locked (unpickle n), fs with
    | Some (inl u), f1 :: _ => UnOp u (decode_algT f1)
    | Some (inr b), f1 :: f2 :: _ => BinOp b (decode_algT f1) (decode_algT f2)
    | _, _ => Const Zero
    end
  end.
Lemma code_algTK F : cancel (@encode_algT F) (@decode_algT F).
Proof.
Admitted.
HB.instance Definition _ (F : eqType) := Equality.copy (algterm F)
  (can_type (@code_algTK F)).
HB.instance Definition _ (F : choiceType) := Choice.copy (algterm F)
  (can_type (@code_algTK F)).
HB.instance Definition _ (F : countType) := Countable.copy (algterm F)
  (can_type (@code_algTK F)).

Declare Scope algT_scope.
Delimit Scope algT_scope with algT.
Bind Scope algT_scope with algterm.
Local Notation "0" := (Const Zero) : algT_scope.
Local Notation "1" := (Const One) : algT_scope.
Local Notation "- x" := (UnOp Opp x) : algT_scope.
Local Notation "- 1" := (- (1)) : algT_scope.
Local Infix "+" := (BinOp Add) : algT_scope.
Local Notation "x ^-1" := (UnOp Inv x) : algT_scope.
Local Infix "*" := (BinOp Mul) : algT_scope.
Local Notation "x ^+ n" := (UnOp (Exp n) x) : algT_scope.
Local Notation "n '.+1-root'" := (UnOp (Root n))
  (at level 2, format "n '.+1-root'") : algT_scope.
Local Notation "n '.+1-prim1root'" := (Const (URoot n))
  (at level 2, format "n '.+1-prim1root'") : algT_scope.

Section eval.
Variables (F : fieldType) (iota : F -> algC).
Fixpoint algT_eval (f : algterm F) : algC :=
  match f with
  | Base x                => iota x
  | 0%algT                => 0
  | 1%algT                => 1
  | (f1 + f2)%algT        => algT_eval f1 + algT_eval f2
  | (- f1)%algT           => - algT_eval f1
  | (f1 * f2)%algT        => algT_eval f1 * algT_eval f2
  | (f1 ^-1)%algT         => (algT_eval f1)^-1
  | (f1 ^+ n)%algT        => (algT_eval f1) ^+ n
  | (n.+1-root f1)%algT   => n.+1.-root (algT_eval f1)
  | (j.+1-prim1root)%algT => prim1root_ j.+1
  end.

Fixpoint subeval (f : algterm F) : seq algC :=
  algT_eval f :: match f with
  | UnOp _ f1 => subeval f1
  | BinOp _ f1 f2 => subeval f1 ++ subeval f2
  | _ => [::]
  end.

Lemma subevalE f : subeval f = algT_eval f :: behead (subeval f).
Proof.
Admitted.

End eval.

Lemma solvable_formula (p : {poly rat}) : p != 0 ->
  solvable_by_radical_poly p <->
  {in root (p ^^ ratr), forall x,
     exists f : algterm rat, algT_eval ratr f = x}.
Proof.
Admitted.

End Formula.
