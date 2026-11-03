(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023-2024
 *               Larry Paulson <lp15 at cam.ac.edu>, 2024 *)

theory Skolem_Normal_Form
imports
  Prenex_Normal_Form
  Bumping
begin

lemma witness_imp_holds_exists:
  assumes \<open>is_interpretation (functions_term t, preds) (I :: (nat, nat) term intrp)\<close> and
    \<open>is_valuation I \<beta>\<close> and 
    \<open>I\<^bold>, \<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x t))\<close>
  shows \<open>I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
sorry

definition skolem1 :: "nat \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  \<open>skolem1 f x \<phi> = \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Fun f (map Var (sorted_list_of_set (FV (\<^bold>\<exists>x\<^bold>. \<phi>))))))\<close>

lemma fvt_var_x_simp: 
  \<open>FVT (Var x \<cdot> subst x (Fun f (map Var (sorted_list_of_set (FV \<phi> - {x}))))) = FV \<phi> - {x}\<close>
sorry


(* holds M v p /\
     (Dom M = Dom M') /\
     (!P zs. Pred M P zs = Pred M' P zs) /\
     (!f zs.
          f,LENGTH zs IN functions_form p ==> (Fun M f zs = Fun M' f zs))
     ==> holds M' v p` *)
(* essentially a repeat of holds_indep_intrp_if... needed? 
Seems to be lemma3 in skolem.ml [Larry]*)
lemma holds_indep_intrp_if2:
  fixes I I' :: "'a intrp"
  shows
 \<open>\<lbrakk>I\<^bold>,\<beta> \<Turnstile> \<phi>; dom I = dom I'; \<And>p. intrp_rel I p  = intrp_rel I' p;
  \<And>f zs. (f, length zs) \<in> functions_form \<phi> \<Longrightarrow> intrp_fn I f zs = intrp_fn I' f zs\<rbrakk> \<Longrightarrow>
  I'\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
sorry

lemma fun_upds_prop: \<open>length xs = length zs \<Longrightarrow> \<forall>z\<in>set zs. P z \<Longrightarrow> \<forall>v. P (g v) \<Longrightarrow> \<forall>v. P ((foldr (\<lambda>kv f. fun_upd f (fst kv) (snd kv)) (zip xs zs) g) v)\<close>
sorry

(*lemma \<open>(\<forall>kv \<in> set zs. P (f (fst kv) (snd kv))) \<Longrightarrow> (\<forall>v. P (x v)) \<Longrightarrow> (\<forall>v. P (\<lambda>zs (fold (\<lambda>kv f. fun_upd f (fst kv) (snd kv)) zs x)))\<close>*)

lemma \<open>{z. \<exists>y. y \<in> FV \<phi> \<and> z \<in> functions_term (Var y \<cdot> subst x t)} = functions_term t \<or>
   {z. \<exists>y. y \<in> FV \<phi> \<and> z \<in> functions_term (Var y \<cdot> subst x t)} = {}\<close>
sorry

lemma func_form_subst: \<open>x \<in> FV \<phi> \<Longrightarrow> (f, length ts) \<in> functions_form (\<phi>  \<cdot>\<^sub>f\<^sub>m subst x (Fun f ts))\<close>
sorry

(* the following lemmas may be useful*)
lemma holds_formsubst:
   "M\<^bold>,\<beta> \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m i) \<longleftrightarrow> M\<^bold>,(\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>M,\<beta>\<^esup>) \<circ> i \<Turnstile> p"
sorry

lemma holds_formsubst1:
   "M\<^bold>,\<beta> \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m Var(x:=t)) \<longleftrightarrow> M\<^bold>,\<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>M,\<beta>\<^esup>) \<Turnstile> p"
sorry

lemma holds_formsubst2:
   "M\<^bold>,\<beta> \<Turnstile> (p \<cdot>\<^sub>f\<^sub>m subst x t) \<longleftrightarrow> M\<^bold>,\<beta>(x := \<lbrakk>t\<rbrakk>\<^bsup>M,\<beta>\<^esup>) \<Turnstile> p"
sorry

lemma size_nonzero [simp]: "size fm > 0"
sorry

(* I think it's better to handle the conjuncts of the original giant formula separately, 
   possibly combining them at the end if it is really necessary.
  I believe it is a mistake to use so many abbreviations:
  ((\<^bold>\<forall>x\<^bold>. \<phi> \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> \<^bold>\<bottom>) and (\<^bold>\<exists>x\<^bold>. \<phi>) are tactically identical, which is not obvious.*)
lemma  
  assumes prenex_ex_phi: \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> 
    and notin_ff: \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  shows holds_skolem1a: "is_prenex (skolem1 f x \<phi>)" (is "?A")
      and holds_skolem1b: "FV (skolem1 f x \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?B")
      and holds_skolem1c: 
        "Prenex_Normal_Form.size (skolem1 f x \<phi>) < Prenex_Normal_Form.size (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?C")
      and holds_skolem1d: "predicates_form (skolem1 f x \<phi>) = predicates_form (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?D")
      and holds_skolem1e: "functions_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<subseteq> functions_form (skolem1 f x \<phi>)" (is "?E")
      and holds_skolem1f: "functions_form (skolem1 f x \<phi>) 
                          \<subseteq> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<triangleright> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)" (is "?F")
sorry

definition "define_fn \<equiv> \<lambda>FN f n h. \<lambda>g zs. if g=f \<and> length zs = n then h zs else FN g zs"

lemma holds_skolem1g:
  assumes prenex_ex_phi: \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> 
    and notin_ff: \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  fixes I :: "'a intrp" 
   assumes interp_I: "is_interpretation (language {\<phi>}) I"
    and nempty_I: "dom I \<noteq> {}" 
    and valid: "\<And>\<beta>. is_valuation I \<beta> \<Longrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)"
  obtains M where "dom M = dom I" 
                  "intrp_rel M = intrp_rel I"
                  "\<And>g zs. g \<noteq> f \<or> length zs \<noteq> card (FV (\<^bold>\<exists>x\<^bold>. \<phi>)) \<Longrightarrow> intrp_fn M g zs = intrp_fn I g zs"
                  "is_interpretation (language {skolem1 f x \<phi>}) M" 
                  "\<And>\<beta>. is_valuation M \<beta> \<Longrightarrow> M\<^bold>,\<beta> \<Turnstile> skolem1 f x \<phi>"
sorry

lemma holds_skolem1h:
  assumes prenex_ex_phi: \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> and \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  assumes is_intrp: "is_interpretation (language {skolem1 f x \<phi>}) N"
      and nempty_N: "dom N \<noteq> {}"
      and is_val: "is_valuation N \<beta>"
      and skol_holds: "N\<^bold>,\<beta> \<Turnstile> skolem1 f x \<phi>"
    shows "N\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)"
sorry

lemma holds_skolem1: 
  assumes \<open>is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close> and \<open>\<not> (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<in> functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
  shows \<open>is_prenex (skolem1 f x \<phi>) \<and>
  FV (skolem1 f x \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  size (skolem1 f x \<phi>) < size (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  predicates_form (skolem1 f x \<phi>) = predicates_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<and>
  functions_form (\<^bold>\<exists>x\<^bold>. \<phi>) \<subseteq> functions_form (skolem1 f x \<phi>) \<and>
  functions_form (skolem1 f x \<phi>) \<subseteq> insert (f, card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) (functions_form (\<^bold>\<exists>x\<^bold>. \<phi>)) \<and>
  (\<forall>(I :: 'a intrp). is_interpretation (language {\<phi>}) I \<and>
    \<not> (dom I = {}) \<and>
    (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>))) \<longrightarrow>
    (\<exists>(M :: 'a intrp). dom M = dom I \<and>
      intrp_rel M = intrp_rel I \<and>
      (\<forall>g zs. \<not>g=f \<or> \<not>(length zs = card (FV (\<^bold>\<exists>x\<^bold>. \<phi>))) \<longrightarrow> intrp_fn M g zs = intrp_fn I g zs) \<and>
      is_interpretation (language {skolem1 f x \<phi>}) M \<and>
      (\<forall>\<beta>. is_valuation M \<beta> \<longrightarrow> (M\<^bold>, \<beta> \<Turnstile> (skolem1 f x \<phi>))))) \<and>
  (\<forall>(N :: 'a intrp). is_interpretation (language {skolem1 f x \<phi>}) N \<and>
    \<not> (dom N = {}) \<longrightarrow>
    (\<forall>\<beta>. is_valuation N \<beta> \<and> (N\<^bold>, \<beta> \<Turnstile> (skolem1 f x \<phi>)) \<longrightarrow> (N\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>))))
\<close>
sorry

(* Skolems_EXISTENCE in hol-light *)
lemma skolems_ex: \<open>\<exists>skolems. \<forall>\<phi>. skolems \<phi> = (\<lambda>k. ppat (\<lambda>x \<psi>. \<^bold>\<forall>x\<^bold>. (skolems \<psi> k))
  (\<lambda>x \<psi>. skolems (skolem1 (numpair J k) x \<psi>) (Suc k)) (\<lambda>\<psi>. \<psi>) \<phi>)\<close>
sorry

consts skolems :: "nat \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form"
specification (skolems)
  skolems_eq: \<open>\<And>J \<psi> k. skolems J \<psi> k 
              = ppat (\<lambda>x \<phi>'. \<^bold>\<forall>x\<^bold>. (skolems J \<phi>' k)) (\<lambda>x \<phi>'. skolems J (skolem1 (numpair J k) x \<phi>') (Suc k)) (\<lambda>\<phi>. \<phi>) \<psi>\<close>
  using skolems_ex by meson

text \<open>bounding the possible Skolem functions in a given formula\<close>
definition "skolems_bounded \<equiv> \<lambda>p J k. \<forall>l m. (numpair J l, m) \<in> functions_form p \<longrightarrow> l < k"

lemma skolems_bounded_mono: "\<lbrakk>skolems_bounded p J k'; k'\<le>k\<rbrakk> \<Longrightarrow> skolems_bounded p J k"
sorry

lemma skolems_bounded_prenex: "skolems_bounded \<phi> K k \<Longrightarrow> skolems_bounded (prenex \<phi>) K k"
sorry

text \<open>Basic properties proved by induction on the number of Skolemisation steps. 
Harrison's gigantic conjunction broken up for more manageable proofs, at the cost of some repetition\<close>

text \<open>first, the simplest properties\<close>
lemma holds_skolems_induction_A:
  assumes "size p = n" and "is_prenex p" and "skolems_bounded p J k"
  shows "universal(skolems J p k) \<and>
         FV(skolems J p k) = FV p \<and>
         predicates_form (skolems J p k) = predicates_form p \<and>
         functions_form p \<subseteq> functions_form (skolems J p k) \<and>
         functions_form (skolems J p k) \<subseteq> {(numpair J l,m) | l m. k \<le> l} \<union> functions_form p"
sorry

text \<open>the final conjunct of the HOL Light version\<close>
lemma holds_skolems_induction_B:
  fixes N :: "'a intrp"
  assumes "size p = n" and "is_prenex p" and "skolems_bounded p J k"
    and "is_interpretation (language {skolems J p k}) N" "dom N \<noteq> {}"
    and "is_valuation N \<beta>" "N\<^bold>,\<beta> \<Turnstile> skolems J p k"
  shows "N\<^bold>,\<beta> \<Turnstile> p"
sorry

text \<open>the penultimate conjunct of the HOL Light version\<close>
lemma holds_skolems_induction_C:
  fixes M :: "'a intrp"
  assumes "size p = n" and "is_prenex p" and "skolems_bounded p J k"
    and "is_interpretation (language {p}) M" "dom M \<noteq> {}" "satisfies M {p}"
  shows "\<exists>M'. dom M' = dom M \<and> intrp_rel M' = intrp_rel M \<and>
                  (\<forall>g zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs
                        \<longrightarrow> (\<exists>l. k \<le> l \<and> g = numpair J l)) \<and>
                  is_interpretation (language {skolems J p k}) M' \<and>
                  satisfies M' {skolems J p k}"
sorry

(* HOLDS_SKOLEMS_PRENEX in hol-light *)
corollary holds_skolems_prenex_A:
  assumes "is_prenex \<phi>" "skolems_bounded \<phi> K 0"
  shows "universal(skolems K \<phi> 0) \<and> (FV (skolems K \<phi> 0) = FV \<phi>) \<and>
         predicates_form (skolems K \<phi> 0) = predicates_form \<phi> \<and>
         functions_form \<phi> \<subseteq> functions_form (skolems K \<phi> 0) \<and>
         functions_form (skolems K \<phi> 0) \<subseteq> {(numpair K l,m) | l m. True} \<union> (functions_form \<phi>)"
sorry

corollary holds_skolems_prenex_B:
  assumes "is_prenex \<phi>" "skolems_bounded \<phi> K 0"
      and "is_interpretation (language {skolems K \<phi> 0}) M" "dom M \<noteq> {}"
      and "is_valuation M \<beta>" "M\<^bold>,\<beta> \<Turnstile> skolems K \<phi> 0"
  shows "M\<^bold>,\<beta> \<Turnstile> \<phi>"
sorry

corollary holds_skolems_prenex_C:
  assumes "is_prenex \<phi>" "skolems_bounded \<phi> K 0"
    and "is_interpretation (language {\<phi>}) M" "dom M \<noteq> {}" "satisfies M {\<phi>}"
  shows "\<exists>M'. dom M' = dom M \<and> intrp_rel M' = intrp_rel M \<and>
              (\<forall>g zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs \<longrightarrow> (\<exists>l. g = numpair K l)) \<and>
              is_interpretation (language {skolems K \<phi> 0}) M' \<and>
              satisfies M' {skolems K \<phi> 0}"
sorry

(* SKOPRE in hol-light *)
definition skopre where
  \<open>skopre k \<phi> = skolems k (prenex \<phi>) 0\<close>

corollary skopre_model_A:
  assumes "skolems_bounded \<phi> K 0"
  shows "universal(skopre K \<phi>) \<and> (FV (skopre K \<phi>) = FV \<phi>) \<and>
         predicates_form (skopre K \<phi>) = predicates_form \<phi> \<and>
         functions_form \<phi> \<subseteq> functions_form (skopre K \<phi>) \<and>
         functions_form (skopre K \<phi>) \<subseteq> {(numpair K l,m) | l m. True} \<union> (functions_form \<phi>)"
sorry

corollary skopre_model_B:
  assumes "skolems_bounded \<phi> K 0"
      and "is_interpretation (language {skopre K \<phi>}) M" "dom M \<noteq> {}"
      and "is_valuation M \<beta>" "M\<^bold>,\<beta> \<Turnstile> skopre K \<phi>"
  shows "M\<^bold>,\<beta> \<Turnstile> \<phi>"
sorry

corollary skopre_model_C:
  assumes "skolems_bounded \<phi> K 0"
    and "is_interpretation (language {\<phi>}) M" "dom M \<noteq> {}" "satisfies M {\<phi>}"
  shows "\<exists>M'. dom M' = dom M \<and> intrp_rel M' = intrp_rel M \<and>
                  (\<forall>g zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs \<longrightarrow> (\<exists>l. g = numpair K l)) \<and>
                  is_interpretation (language {skopre K \<phi>}) M' \<and>
                  satisfies M' {skopre K \<phi>}"
sorry

definition skolemize where
  \<open>skolemize \<phi> = skopre (num_of_form (bump_form \<phi>) + 1) (bump_form \<phi>)\<close>

(* SKOLEMIZE_WORKS in hol-light *)

lemma no_skolems_bump_nterm:
  shows "i>0 \<Longrightarrow> (numpair i l, m) \<notin> functions_term (bump_nterm t)"
sorry

lemma no_skolems_bump_form: "i>0 \<Longrightarrow> skolems_bounded (bump_form \<phi>) i 0"
sorry

lemma universal_skolemize [iff]: "universal (skolemize \<phi>)" 
  and FV_skolemize [simp]: "FV (skolemize \<phi>) = FV (bump_form \<phi>)"
  and predicates_form_skolemize [simp]: "predicates_form (skolemize \<phi>) = predicates_form (bump_form \<phi>)"
sorry

lemma functions_bump_form: "functions_form (bump_form \<phi>) \<subseteq> functions_form (skolemize \<phi>)"
sorry

lemma functions_skolemize:
    "functions_form (skolemize \<phi>) \<subseteq> {(numpair (num_of_form (bump_form \<phi>)+1) l, m) |k l m. True} \<union> functions_form (bump_form \<phi>)"
sorry

lemma skolemize_imp_holds_bump_form:
  assumes "is_interpretation (language {skolemize \<phi>}) N" "dom N \<noteq> {}"
    and "is_valuation N \<beta>" "N\<^bold>,\<beta> \<Turnstile> skolemize \<phi>"
  shows "N\<^bold>,\<beta> \<Turnstile> bump_form \<phi>"
sorry

lemma is_interpretation_skolemize:
  assumes "is_interpretation (language {bump_form \<phi>}) M" "dom M \<noteq> {}" "satisfies M {bump_form \<phi>}"
  obtains M' where "dom M' = dom M" "intrp_rel M' = intrp_rel M" 
       "\<And>g zs. intrp_fn M' g zs \<noteq> intrp_fn M g zs \<Longrightarrow> \<exists>l. g = numpair (num_of_form (bump_form \<phi>) + 1) l" 
       "is_interpretation (language {skolemize \<phi>}) M'" "satisfies M' {skolemize \<phi>}"
sorry


(* FUNCTIONS_FORM_SKOLEMIZE in hol-light *)
lemma functions_form_skolemize: 
  assumes \<open>(f,m) \<in> functions_form (skolemize \<phi>)\<close>
  obtains k where \<open>f = numpair 0 k\<close> \<open>(k,m) \<in> functions_form \<phi>\<close> | l where \<open>f = numpair (num_of_form (bump_form \<phi>) + 1) l\<close>
sorry

definition skomod1 where
  \<open>skomod1 \<phi> M \<equiv> 
    if satisfies M {\<phi>}
    then (SOME M'. dom M' = dom (bump_intrp M) \<and>
                   intrp_rel M' = intrp_rel (bump_intrp M) \<and>
                   (\<forall>g zs. intrp_fn M' g zs \<noteq> intrp_fn (bump_intrp M) g zs \<longrightarrow>
                     (\<exists>l. g = numpair (num_of_form (bump_form \<phi>) + 1) l)) \<and>
                   is_interpretation (language {skolemize \<phi>}) M' \<and> satisfies M' {skolemize \<phi>})
    else (Abs_intrp (dom M, (\<lambda>g zs. (SOME a. a \<in> dom M)), intrp_rel M))\<close>

(* SKOMOD1_WORKS in hol-light *)
lemma skomod1_works:
  assumes M: \<open>is_interpretation (language {\<phi>}) M\<close> \<open>dom M \<noteq> {}\<close>
  shows \<open>dom (skomod1 \<phi> M) = dom (bump_intrp M) \<and>
         intrp_rel (skomod1 \<phi> M) = intrp_rel (bump_intrp M) \<and>
         is_interpretation (language {skolemize \<phi>}) (skomod1 \<phi> M) \<and>
         (satisfies M {\<phi>} \<longrightarrow>
           (\<forall>g zs. intrp_fn (skomod1 \<phi> M) g zs \<noteq> intrp_fn (bump_intrp M) g zs \<longrightarrow> 
             (\<exists>l. g = numpair (num_of_form (bump_form \<phi>) + 1) l)) \<and>
           satisfies (skomod1 \<phi> M) {skolemize \<phi>})\<close>
sorry

definition "skomod_FN \<equiv> \<lambda>M g zs. if numfst g = 0 then intrp_fn M (numsnd g) zs
                               else intrp_fn (skomod1 (unbump_form (form_of_num (numfst g - 1))) M) g zs"

definition skomod where
  \<open>skomod M \<equiv> Abs_intrp (dom M, skomod_FN M, intrp_rel M)\<close>

(* SKOMOD_INTERPRETATION in hol-light *)
lemma skomod_interpretation:
  assumes \<open>is_interpretation (language {\<phi>}) M\<close>  \<open>dom M \<noteq> {}\<close>
  shows \<open>is_interpretation (language {skolemize \<phi>}) (skomod M)\<close>
sorry


(* SKOMOD_WORKS in hol-light *)
proposition skomod_works:
  assumes \<open>is_interpretation (language {\<phi>}) M\<close>  \<open>dom M \<noteq> {}\<close>
  shows   \<open>satisfies M {\<phi>} \<longleftrightarrow> satisfies (skomod M) {skolemize \<phi>}\<close>
sorry


(* SKOLEMIZE_SATISFIABLE *)
proposition skolemize_satisfiable: 
  \<open>(\<exists>M::'a intrp. dom M \<noteq> {} \<and> is_interpretation (language S) M \<and> 
  satisfies M S) \<longleftrightarrow> 
   (\<exists>M::'a intrp. dom M \<noteq> {} \<and> is_interpretation (language (skolemize ` S)) M 
   \<and> satisfies M (skolemize ` S))\<close>   (is "?lhs = ?rhs")
sorry


fun specialize :: "form \<Rightarrow> form" where
  \<open>specialize \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>specialize (Atom p ts) = Atom p ts\<close>
| \<open>specialize (\<phi> \<^bold>\<longrightarrow> \<psi>) = \<phi> \<^bold>\<longrightarrow> \<psi>\<close>
| \<open>specialize (\<^bold>\<forall>x\<^bold>. \<phi>) = specialize \<phi>\<close>

(* SPECIALIZE_SATISFIES in hol-light *)
lemma specialize_satisfies: 
  fixes M :: "'a intrp"
  assumes \<open>dom M \<noteq> {}\<close>
  shows \<open>satisfies M (specialize  ` S) \<longleftrightarrow> satisfies M S\<close>
sorry

(* SPECIALIZE_QFREE in hol-light *)
lemma specialize_qfree: \<open>universal \<phi> \<Longrightarrow> qfree (specialize \<phi>)\<close>
sorry

lemma functions_form_specialize [simp]: "functions_form(specialize \<phi>) = functions_form \<phi>"
sorry

lemma predicates_form_form_specialize [simp]: "predicates_form(specialize \<phi>) = predicates_form \<phi>"
sorry

(* SPECIALIZE_LANGUAGE in hol-light *)
lemma specialize_language: \<open>language (specialize  ` S) = language S\<close>
sorry
definition skolem :: "form \<Rightarrow> form" where
  \<open>skolem \<phi> = specialize(skolemize \<phi>)\<close>

lemma skolem_qfree: \<open>qfree (skolem \<phi>)\<close>
sorry

theorem skolem_satisfiable:
     \<open>(\<exists>M::'a intrp. dom M \<noteq> {} \<and> is_interpretation (language S) M \<and> satisfies M S)
  \<longleftrightarrow> (\<exists>M::'a intrp. dom M \<noteq> {} \<and> is_interpretation (language (skolem  ` S)) M \<and> 
      satisfies M (skolem  ` S))\<close>
sorry

end
