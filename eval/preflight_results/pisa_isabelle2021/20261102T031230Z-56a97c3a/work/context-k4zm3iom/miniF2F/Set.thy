(*  Title:      HOL/Set.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
*)

section \<open>Set theory for higher-order logic\<close>

theory Set
  imports Lattices Boolean_Algebras
begin
declare [[quick_and_dirty = true]]


subsection \<open>Sets as predicates\<close>

typedecl 'a set

axiomatization Collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" \<comment> \<open>comprehension\<close>
  and member :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" \<comment> \<open>membership\<close>
  where mem_Collect_eq [iff, code_unfold]: "member a (Collect P) = P a"
    and Collect_mem_eq [simp, code_unfold]: "Collect (\<lambda>x. member x A) = A"

notation
  member  (\<open>'(\<in>')\<close>) and
  member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50)

abbreviation not_member
  where "not_member x A \<equiv> \<not> (x \<in> A)" \<comment> \<open>non-membership\<close>
notation
  not_member  (\<open>'(\<notin>')\<close>) and
  not_member  (\<open>(\<open>notation=\<open>infix \<notin>\<close>\<close>_/ \<notin> _)\<close> [51, 51] 50)

open_bundle member_ASCII_syntax
begin
notation (ASCII)
  member  (\<open>'(:')\<close>) and
  member  (\<open>(\<open>notation=\<open>infix :\<close>\<close>_/ : _)\<close> [51, 51] 50) and
  not_member  (\<open>'(~:')\<close>) and
  not_member  (\<open>(\<open>notation=\<open>infix ~:\<close>\<close>_/ ~: _)\<close> [51, 51] 50)
end


text \<open>Set comprehensions\<close>

syntax
  "_Coll" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a set"    (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{_./ _})\<close>)
syntax_consts
  "_Coll" \<rightleftharpoons> Collect
translations
  "{x. P}" \<rightleftharpoons> "CONST Collect (\<lambda>x. P)"

syntax (ASCII)
  "_Collect" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a set"  (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{(_/: _)./ _})\<close>)
syntax
  "_Collect" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a set"  (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{(_/ \<in> _)./ _})\<close>)
translations
  "{p:A. P}" \<rightharpoonup> "CONST Collect (\<lambda>p. p \<in> A \<and> P)"

ML \<open>
  fun Collect_binder_tr' c [Abs (x, T, t), Const (\<^const_syntax>\<open>Collect\<close>, _) $ Abs (y, _, P)] =
        if x = y then
          let
            val x' = Syntax_Trans.mark_bound_body (x, T);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in Syntax.const c $ Syntax_Trans.mark_bound_abs (x, T) $ P' $ t' end
        else raise Match
    | Collect_binder_tr' _ _ = raise Match
\<close>

lemma CollectI: "P a \<Longrightarrow> a \<in> {x. P x}"
  
  sorry


lemma CollectD: "a \<in> {x. P x} \<Longrightarrow> P a"
  
  sorry


lemma Collect_cong: "(\<And>x. P x = Q x) \<Longrightarrow> {x. P x} = {x. Q x}"
  
  sorry


text \<open>
  Simproc for pulling \<open>x = t\<close> in \<open>{x. \<dots> \<and> x = t \<and> \<dots>}\<close>
  to the front (and similarly for \<open>t = x\<close>):
\<close>

simproc_setup defined_Collect ("{x. P x \<and> Q x}") = \<open>
  K (Quantifier1.rearrange_Collect
    (fn ctxt =>
      resolve_tac ctxt @{thms Collect_cong} 1 THEN
      resolve_tac ctxt @{thms iffI} 1 THEN
      ALLGOALS
        (EVERY' [REPEAT_DETERM o eresolve_tac ctxt @{thms conjE},
          DEPTH_SOLVE_1 o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms conjI})])))
\<close>

lemmas CollectE = CollectD [elim_format]

lemma set_eqI:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "A = B"
  
  sorry


lemma set_eq_iff: "A = B \<longleftrightarrow> (\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  
  sorry


lemma Collect_eqI:
  assumes "\<And>x. P x = Q x"
  shows "Collect P = Collect Q"
  
  sorry


text \<open>Lifting of predicate class instances\<close>

instantiation set :: (type) boolean_algebra
begin

definition less_eq_set
  where "A \<le> B \<longleftrightarrow> (\<lambda>x. member x A) \<le> (\<lambda>x. member x B)"

definition less_set
  where "A < B \<longleftrightarrow> (\<lambda>x. member x A) < (\<lambda>x. member x B)"

definition inf_set
  where "A \<sqinter> B = Collect ((\<lambda>x. member x A) \<sqinter> (\<lambda>x. member x B))"

definition sup_set
  where "A \<squnion> B = Collect ((\<lambda>x. member x A) \<squnion> (\<lambda>x. member x B))"

definition bot_set
  where "\<bottom> = Collect \<bottom>"

definition top_set
  where "\<top> = Collect \<top>"

definition uminus_set
  where "- A = Collect (- (\<lambda>x. member x A))"

definition minus_set
  where "A - B = Collect ((\<lambda>x. member x A) - (\<lambda>x. member x B))"

instance
  
  sorry


end

text \<open>Set enumerations\<close>

abbreviation empty :: "'a set" (\<open>{}\<close>)
  where "{} \<equiv> bot"

definition insert :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where insert_compr: "insert a B = {x. x = a \<or> x \<in> B}"

open_bundle set_enumeration_syntax
begin

syntax
  "_Finset" :: "args \<Rightarrow> 'a set"  (\<open>(\<open>indent=1 notation=\<open>mixfix set enumeration\<close>\<close>{_})\<close>)
syntax_consts
  "_Finset" \<rightleftharpoons> insert
translations
  "{x, xs}" \<rightleftharpoons> "CONST insert x {xs}"
  "{x}" \<rightleftharpoons> "CONST insert x {}"

end


subsection \<open>Subsets and bounded quantifiers\<close>

abbreviation subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "subset \<equiv> less"

abbreviation subset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "subset_eq \<equiv> less_eq"

notation
  subset  (\<open>'(\<subset>')\<close>) and
  subset  (\<open>(\<open>notation=\<open>infix \<subset>\<close>\<close>_/ \<subset> _)\<close> [51, 51] 50) and
  subset_eq  (\<open>'(\<subseteq>')\<close>) and
  subset_eq  (\<open>(\<open>notation=\<open>infix \<subseteq>\<close>\<close>_/ \<subseteq> _)\<close> [51, 51] 50)

abbreviation (input)
  supset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "supset \<equiv> greater"

abbreviation (input)
  supset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "supset_eq \<equiv> greater_eq"

notation
  supset  (\<open>'(\<supset>')\<close>) and
  supset  (\<open>(\<open>notation=\<open>infix \<supset>\<close>\<close>_/ \<supset> _)\<close> [51, 51] 50) and
  supset_eq  (\<open>'(\<supseteq>')\<close>) and
  supset_eq  (\<open>(\<open>notation=\<open>infix \<supseteq>\<close>\<close>_/ \<supseteq> _)\<close> [51, 51] 50)

notation (ASCII output)
  subset  (\<open>'(<')\<close>) and
  subset  (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ < _)\<close> [51, 51] 50) and
  subset_eq  (\<open>'(<=')\<close>) and
  subset_eq  (\<open>(\<open>notation=\<open>infix <=\<close>\<close>_/ <= _)\<close> [51, 51] 50)

definition Ball :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ball A P \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> P x)"   \<comment> \<open>bounded universal quantifiers\<close>

definition Bex :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Bex A P \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x)"   \<comment> \<open>bounded existential quantifiers\<close>

syntax (ASCII)
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ALL :\<close>\<close>ALL (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder EX :\<close>\<close>EX (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder EX! :\<close>\<close>EX! (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bleast"     :: "id \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a"           (\<open>(\<open>indent=3 notation=\<open>binder LEAST :\<close>\<close>LEAST (_/:_)./ _)\<close> [0, 0, 10] 10)

syntax (input)
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ! :\<close>\<close>! (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ? :\<close>\<close>? (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ?! :\<close>\<close>?! (_/:_)./ _)\<close> [0, 0, 10] 10)

syntax
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>(_/\<in>_)./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>(_/\<in>_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<exists>!\<close>\<close>\<exists>!(_/\<in>_)./ _)\<close> [0, 0, 10] 10)
  "_Bleast"     :: "id \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a"           (\<open>(\<open>indent=3 notation=\<open>binder LEAST\<close>\<close>LEAST(_/\<in>_)./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_Ball" \<rightleftharpoons> Ball and
  "_Bex" \<rightleftharpoons> Bex and
  "_Bex1" \<rightleftharpoons> Ex1 and
  "_Bleast" \<rightleftharpoons> Least

translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball A (\<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex A (\<lambda>x. P)"
  "\<exists>!x\<in>A. P" \<rightharpoonup> "\<exists>!x. x \<in> A \<and> P"
  "LEAST x:A. P" \<rightharpoonup> "LEAST x. x \<in> A \<and> P"

syntax (ASCII output)
  "_setlessAll" :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder ALL\<close>\<close>ALL _<_./ _)\<close>  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder EX\<close>\<close>EX _<_./ _)\<close>  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder ALL\<close>\<close>ALL _<=_./ _)\<close> [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder EX\<close>\<close>EX _<=_./ _)\<close> [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder EX!\<close>\<close>EX! _<=_./ _)\<close> [0, 0, 10] 10)

syntax
  "_setlessAll" :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>_\<subset>_./ _)\<close>  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>_\<subset>_./ _)\<close>  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>_\<subseteq>_./ _)\<close> [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>_\<subseteq>_./ _)\<close> [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<exists>!\<close>\<close>\<exists>!_\<subseteq>_./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_setlessAll" "_setleAll" \<rightleftharpoons> All and
  "_setlessEx" "_setleEx" \<rightleftharpoons> Ex and
  "_setleEx1" \<rightleftharpoons> Ex1

translations
  "\<forall>A\<subset>B. P" \<rightharpoonup> "\<forall>A. A \<subset> B \<longrightarrow> P"
  "\<exists>A\<subset>B. P" \<rightharpoonup> "\<exists>A. A \<subset> B \<and> P"
  "\<forall>A\<subseteq>B. P" \<rightharpoonup> "\<forall>A. A \<subseteq> B \<longrightarrow> P"
  "\<exists>A\<subseteq>B. P" \<rightharpoonup> "\<exists>A. A \<subseteq> B \<and> P"
  "\<exists>!A\<subseteq>B. P" \<rightharpoonup> "\<exists>!A. A \<subseteq> B \<and> P"

print_translation \<open>
  let
    val All_binder = Mixfix.binder_name \<^const_syntax>\<open>All\<close>;
    val Ex_binder = Mixfix.binder_name \<^const_syntax>\<open>Ex\<close>;
    val impl = \<^const_syntax>\<open>HOL.implies\<close>;
    val conj = \<^const_syntax>\<open>HOL.conj\<close>;
    val sbset = \<^const_syntax>\<open>subset\<close>;
    val sbset_eq = \<^const_syntax>\<open>subset_eq\<close>;

    val trans =
     [((All_binder, impl, sbset), \<^syntax_const>\<open>_setlessAll\<close>),
      ((All_binder, impl, sbset_eq), \<^syntax_const>\<open>_setleAll\<close>),
      ((Ex_binder, conj, sbset), \<^syntax_const>\<open>_setlessEx\<close>),
      ((Ex_binder, conj, sbset_eq), \<^syntax_const>\<open>_setleEx\<close>)];

    fun mk v (v', T) c n P =
      if v = v' andalso not (Term.exists_subterm (fn Free (x, _) => x = v | _ => false) n)
      then Syntax.const c $ Syntax_Trans.mark_bound_body (v', T) $ n $ P
      else raise Match;

    fun tr' q = (q, fn _ =>
      (fn [Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (v, \<^Type>\<open>set _\<close>),
          Const (c, _) $
            (Const (d, _) $ (Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (v', T)) $ n) $ P] =>
          (case AList.lookup (=) trans (q, c, d) of
            NONE => raise Match
          | SOME l => mk v (v', T) l n P)
        | _ => raise Match));
  in
    [tr' All_binder, tr' Ex_binder]
  end
\<close>


text \<open>
  \<^medskip>
  Translate between \<open>{e | x1\<dots>xn. P}\<close> and \<open>{u. \<exists>x1\<dots>xn. u = e \<and> P}\<close>;
  \<open>{y. \<exists>x1\<dots>xn. y = e \<and> P}\<close> is only translated if \<open>[0..n] \<subseteq> bvs e\<close>.
\<close>

syntax
  "_Setcompr" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"
    (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{_ |/_./ _})\<close>)
syntax_consts
  "_Setcompr" \<rightleftharpoons> Collect

parse_translation \<open>
  let
    val ex_tr = snd (Syntax_Trans.mk_binder_tr ("EX ", \<^const_syntax>\<open>Ex\<close>));

    fun nvars (Const (\<^syntax_const>\<open>_idts\<close>, _) $ _ $ idts) = nvars idts + 1
      | nvars _ = 1;

    fun setcompr_tr ctxt [e, idts, b] =
      let
        val eq = Syntax.const \<^const_syntax>\<open>HOL.eq\<close> $ Bound (nvars idts) $ e;
        val P = Syntax.const \<^const_syntax>\<open>HOL.conj\<close> $ eq $ b;
        val exP = ex_tr ctxt [idts, P];
      in Syntax.const \<^const_syntax>\<open>Collect\<close> $ absdummy dummyT exP end;

  in [(\<^syntax_const>\<open>_Setcompr\<close>, setcompr_tr)] end
\<close>

typed_print_translation \<open>
 [(\<^const_syntax>\<open>Ball\<close>, Syntax_Trans.preserve_binder_abs2_tr' \<^syntax_const>\<open>_Ball\<close>),
  (\<^const_syntax>\<open>Bex\<close>, Syntax_Trans.preserve_binder_abs2_tr' \<^syntax_const>\<open>_Bex\<close>)]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

print_translation \<open>
let
  val ex_tr' = snd (Syntax_Trans.mk_binder_tr' (\<^const_syntax>\<open>Ex\<close>, "DUMMY"));

  fun setcompr_tr' ctxt [Abs (abs as (_, _, P))] =
    let
      fun check (Const (\<^const_syntax>\<open>Ex\<close>, _) $ Abs (_, _, P), n) = check (P, n + 1)
        | check (Const (\<^const_syntax>\<open>HOL.conj\<close>, _) $
              (Const (\<^const_syntax>\<open>HOL.eq\<close>, _) $ Bound m $ e) $ P, n) =
            n > 0 andalso m = n andalso not (loose_bvar1 (P, n)) andalso
            subset (=) (0 upto (n - 1), add_loose_bnos (e, 0, []))
        | check _ = false;

        fun tr' (_ $ abs) =
          let val _ $ idts $ (_ $ (_ $ _ $ e) $ Q) = ex_tr' ctxt [abs]
          in Syntax.const \<^syntax_const>\<open>_Setcompr\<close> $ e $ idts $ Q end;
    in
      if check (P, 0) then tr' P
      else
        let
          val (x as _ $ Free(xN, _), t) = Syntax_Trans.atomic_abs_tr' ctxt abs;
          val M = Syntax.const \<^syntax_const>\<open>_Coll\<close> $ x $ t;
        in
          case t of
            Const (\<^const_syntax>\<open>HOL.conj\<close>, _) $
              (Const (\<^const_syntax>\<open>Set.member\<close>, _) $
                (Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (yN, _)) $ A) $ P =>
            if xN = yN then Syntax.const \<^syntax_const>\<open>_Collect\<close> $ x $ A $ P else M
          | _ => M
        end
    end;
  in [(\<^const_syntax>\<open>Collect\<close>, setcompr_tr')] end
\<close>

simproc_setup defined_Bex ("\<exists>x\<in>A. P x \<and> Q x") = \<open>
  K (Quantifier1.rearrange_Bex (fn ctxt => unfold_tac ctxt @{thms Bex_def}))
\<close>

simproc_setup defined_All ("\<forall>x\<in>A. P x \<longrightarrow> Q x") = \<open>
  K (Quantifier1.rearrange_Ball (fn ctxt => unfold_tac ctxt @{thms Ball_def}))
\<close>

lemma ballI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x\<in>A. P x"
  
  sorry


lemmas strip = impI allI ballI

lemma bspec [dest?]: "\<forall>x\<in>A. P x \<Longrightarrow> x \<in> A \<Longrightarrow> P x"
  
  sorry


text \<open>Gives better instantiation for bound:\<close>
setup \<open>
  map_theory_claset (fn ctxt =>
    ctxt addbefore ("bspec", fn ctxt' => dresolve_tac ctxt' @{thms bspec} THEN' assume_tac ctxt'))
\<close>

ML \<open>
structure Simpdata =
struct
  open Simpdata;
  val mksimps_pairs = [(\<^const_name>\<open>Ball\<close>, @{thms bspec})] @ mksimps_pairs;
end;

open Simpdata;
\<close>

declaration \<open>fn _ => Simplifier.map_simpset (Simplifier.set_mksimps (mksimps mksimps_pairs))\<close>

lemma ballE [elim]: "\<forall>x\<in>A. P x \<Longrightarrow> (P x \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q"
  
  sorry


lemma bexI [intro]: "P x \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>x\<in>A. P x"
  \<comment> \<open>Normally the best argument order: \<open>P x\<close> constrains the choice of \<open>x \<in> A\<close>.\<close>
  
  sorry


lemma rev_bexI [intro?]: "x \<in> A \<Longrightarrow> P x \<Longrightarrow> \<exists>x\<in>A. P x"
  \<comment> \<open>The best argument order when there is only one \<open>x \<in> A\<close>.\<close>
  
  sorry


lemma bexCI: "(\<forall>x\<in>A. \<not> P x \<Longrightarrow> P a) \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>x\<in>A. P x"
  
  sorry


lemma bexE [elim!]: "\<exists>x\<in>A. P x \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  
  sorry


lemma ball_triv [simp]: "(\<forall>x\<in>A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<longrightarrow> P)"
  \<comment> \<open>trivial rewrite rule.\<close>
  
  sorry


lemma bex_triv [simp]: "(\<exists>x\<in>A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<and> P)"
  \<comment> \<open>Dual form for existentials.\<close>
  
  sorry


lemma bex_triv_one_point1 [simp]: "(\<exists>x\<in>A. x = a) \<longleftrightarrow> a \<in> A"
  
  sorry


lemma bex_triv_one_point2 [simp]: "(\<exists>x\<in>A. a = x) \<longleftrightarrow> a \<in> A"
  
  sorry


lemma bex_one_point1 [simp]: "(\<exists>x\<in>A. x = a \<and> P x) \<longleftrightarrow> a \<in> A \<and> P a"
  
  sorry


lemma bex_one_point2 [simp]: "(\<exists>x\<in>A. a = x \<and> P x) \<longleftrightarrow> a \<in> A \<and> P a"
  
  sorry


lemma ball_one_point1 [simp]: "(\<forall>x\<in>A. x = a \<longrightarrow> P x) \<longleftrightarrow> (a \<in> A \<longrightarrow> P a)"
  
  sorry


lemma ball_one_point2 [simp]: "(\<forall>x\<in>A. a = x \<longrightarrow> P x) \<longleftrightarrow> (a \<in> A \<longrightarrow> P a)"
  
  sorry


lemma ball_conj_distrib: "(\<forall>x\<in>A. P x \<and> Q x) \<longleftrightarrow> (\<forall>x\<in>A. P x) \<and> (\<forall>x\<in>A. Q x)"
  
  sorry


lemma bex_disj_distrib: "(\<exists>x\<in>A. P x \<or> Q x) \<longleftrightarrow> (\<exists>x\<in>A. P x) \<or> (\<exists>x\<in>A. Q x)"
  
  sorry



text \<open>Congruence rules\<close>

lemma ball_cong:
  "\<lbrakk> A = B;  \<And>x. x \<in> B \<Longrightarrow> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<forall>x\<in>A. P x) \<longleftrightarrow> (\<forall>x\<in>B. Q x)"
  
  sorry


lemma ball_cong_simp [cong]:
  "\<lbrakk> A = B;  \<And>x. x \<in> B =simp=> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<forall>x\<in>A. P x) \<longleftrightarrow> (\<forall>x\<in>B. Q x)"
  
  sorry


lemma bex_cong:
  "\<lbrakk> A = B;  \<And>x. x \<in> B \<Longrightarrow> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<exists>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>B. Q x)"
  
  sorry


lemma bex_cong_simp [cong]:
  "\<lbrakk> A = B;  \<And>x. x \<in> B =simp=> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<exists>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>B. Q x)"
  
  sorry


lemma bex1_def: "(\<exists>!x\<in>X. P x) \<longleftrightarrow> (\<exists>x\<in>X. P x) \<and> (\<forall>x\<in>X. \<forall>y\<in>X. P x \<longrightarrow> P y \<longrightarrow> x = y)"
  
  sorry



subsection \<open>Basic operations\<close>

subsubsection \<open>Subsets\<close>

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  
  sorry


text \<open>
  \<^medskip>
  Map the type \<open>'a set \<Rightarrow> anything\<close> to just \<open>'a\<close>; for overloading constants
  whose first argument has type \<open>'a set\<close>.
\<close>

lemma subsetD [elim, intro?]: "A \<subseteq> B \<Longrightarrow> c \<in> A \<Longrightarrow> c \<in> B"
  
  sorry


lemma rev_subsetD [intro?,no_atp]: "c \<in> A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> c \<in> B"
  \<comment> \<open>The same, with reversed premises for use with @{method erule} -- cf. @{thm rev_mp}.\<close>
  
  sorry


lemma subsetCE [elim,no_atp]: "A \<subseteq> B \<Longrightarrow> (c \<notin> A \<Longrightarrow> P) \<Longrightarrow> (c \<in> B \<Longrightarrow> P) \<Longrightarrow> P"
  \<comment> \<open>Classical elimination rule.\<close>
  
  sorry


lemma subset_eq: "A \<subseteq> B \<longleftrightarrow> (\<forall>x\<in>A. x \<in> B)"
  
  sorry


lemma contra_subsetD [no_atp]: "A \<subseteq> B \<Longrightarrow> c \<notin> B \<Longrightarrow> c \<notin> A"
  
  sorry


lemma subset_refl: "A \<subseteq> A"
  
  sorry


lemma subset_trans: "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
  
  sorry


lemma subset_not_subset_eq [code]: "A \<subset> B \<longleftrightarrow> A \<subseteq> B \<and> \<not> B \<subseteq> A"
  
  sorry


lemma eq_mem_trans: "a = b \<Longrightarrow> b \<in> A \<Longrightarrow> a \<in> A"
  
  sorry


lemmas basic_trans_rules [trans] =
  order_trans_rules rev_subsetD subsetD eq_mem_trans


subsubsection \<open>Equality\<close>

lemma subset_antisym [intro!]: "A \<subseteq> B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> A = B"
  \<comment> \<open>Anti-symmetry of the subset relation.\<close>
  
  sorry


text \<open>\<^medskip> Equality rules from ZF set theory -- are they appropriate here?\<close>

lemma equalityD1: "A = B \<Longrightarrow> A \<subseteq> B"
  
  sorry


lemma equalityD2: "A = B \<Longrightarrow> B \<subseteq> A"
  
  sorry


text \<open>
  \<^medskip>
  Be careful when adding this to the claset as \<open>subset_empty\<close> is in the
  simpset: \<^prop>\<open>A = {}\<close> goes to \<^prop>\<open>{} \<subseteq> A\<close> and \<^prop>\<open>A \<subseteq> {}\<close>
  and then back to \<^prop>\<open>A = {}\<close>!
\<close>

lemma equalityE: "A = B \<Longrightarrow> (A \<subseteq> B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> P) \<Longrightarrow> P"
  
  sorry


lemma equalityCE [elim]: "A = B \<Longrightarrow> (c \<in> A \<Longrightarrow> c \<in> B \<Longrightarrow> P) \<Longrightarrow> (c \<notin> A \<Longrightarrow> c \<notin> B \<Longrightarrow> P) \<Longrightarrow> P"
  
  sorry


lemma eqset_imp_iff: "A = B \<Longrightarrow> x \<in> A \<longleftrightarrow> x \<in> B"
  
  sorry


lemma eqelem_imp_iff: "x = y \<Longrightarrow> x \<in> A \<longleftrightarrow> y \<in> A"
  
  sorry



subsubsection \<open>The empty set\<close>

lemma empty_def: "{} = {x. False}"
  
  sorry


lemma empty_iff [simp]: "c \<in> {} \<longleftrightarrow> False"
  
  sorry


lemma emptyE [elim!]: "a \<in> {} \<Longrightarrow> P"
  
  sorry


lemma empty_subsetI [iff]: "{} \<subseteq> A"
  \<comment> \<open>One effect is to delete the ASSUMPTION \<^prop>\<open>{} \<subseteq> A\<close>\<close>
  
  sorry


lemma equals0I: "(\<And>y. y \<in> A \<Longrightarrow> False) \<Longrightarrow> A = {}"
  
  sorry


lemma equals0D: "A = {} \<Longrightarrow> a \<notin> A"
  \<comment> \<open>Use for reasoning about disjointness: \<open>A \<inter> B = {}\<close>\<close>
  
  sorry


lemma ball_empty [simp]: "Ball {} P \<longleftrightarrow> True"
  
  sorry


lemma bex_empty [simp]: "Bex {} P \<longleftrightarrow> False"
  
  sorry



subsubsection \<open>The universal set -- UNIV\<close>

abbreviation UNIV :: "'a set"
  where "UNIV \<equiv> top"

lemma UNIV_def: "UNIV = {x. True}"
  
  sorry


lemma UNIV_I [simp]: "x \<in> UNIV"
  
  sorry


declare UNIV_I [intro]  \<comment> \<open>unsafe makes it less likely to cause problems\<close>

lemma UNIV_witness [intro?]: "\<exists>x. x \<in> UNIV"
  
  sorry


lemma subset_UNIV: "A \<subseteq> UNIV"
  
  sorry


text \<open>
  \<^medskip>
  Eta-contracting these two rules (to remove \<open>P\<close>) causes them
  to be ignored because of their interaction with congruence rules.
\<close>

lemma ball_UNIV [simp]: "Ball UNIV P \<longleftrightarrow> All P"
  
  sorry


lemma bex_UNIV [simp]: "Bex UNIV P \<longleftrightarrow> Ex P"
  
  sorry


lemma UNIV_eq_I: "(\<And>x. x \<in> A) \<Longrightarrow> UNIV = A"
  
  sorry


lemma UNIV_not_empty [iff]: "UNIV \<noteq> {}"
  
  sorry



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma empty_not_UNIV[simp]: "{} \<noteq> UNIV"
  
  