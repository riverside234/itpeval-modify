(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory FOL_Semantics
  imports FOL_Syntax
begin

locale struct =
  fixes
    M :: \<open>'m set\<close> and
    FN :: \<open>nat \<Rightarrow> 'm list \<Rightarrow> 'm\<close> and
    REL :: \<open>nat \<Rightarrow> 'm list set\<close> (* in hol-ligh a boolean is returned instead *)
  assumes
    M_nonempty: \<open>M \<noteq> {}\<close>

typedef 'm intrp =
  \<open>{ (M :: 'm set, FN :: nat \<Rightarrow> 'm list \<Rightarrow> 'm, REL :: nat \<Rightarrow> 'm list set). struct M}\<close>
  using struct.intro
  by fastforce

declare Abs_intrp_inverse [simp] Rep_intrp_inverse [simp]

setup_lifting type_definition_intrp

lift_definition dom :: \<open>'m intrp \<Rightarrow> 'm set\<close> is fst .
lift_definition intrp_fn :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm list \<Rightarrow> 'm)\<close> is \<open>fst \<circ> snd\<close> .
lift_definition intrp_rel :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm list set)\<close> is \<open>snd \<circ> snd\<close> .

lemma intrp_is_struct [iff]: \<open>struct (dom \<M>)\<close>
sorry

lemma dom_Abs_is_fst [simp]: \<open>struct M \<Longrightarrow> dom (Abs_intrp (M, FN, REL)) = M\<close>
sorry

lemma intrp_fn_Abs_is_fst_snd [simp]: \<open>struct M \<Longrightarrow> intrp_fn (Abs_intrp (M, FN, REL)) = FN\<close>
sorry

lemma intrp_rel_Abs_is_snd_snd [simp]: 
  \<open>struct M \<Longrightarrow> intrp_rel (Abs_intrp (M, FN, REL)) = REL\<close>
sorry

(* in HOL Light: valuation *)
definition is_valuation :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> bool\<close> where
  \<open>is_valuation \<M> \<beta> \<longleftrightarrow> (\<forall> v. \<beta> v \<in> dom \<M>)\<close> 

lemma valuation_valmod: \<open>\<lbrakk>is_valuation \<M> \<beta>; a \<in> dom \<M>\<rbrakk> \<Longrightarrow> is_valuation \<M> (\<beta>(x := a))\<close>
sorry

fun eval (* HOL Light: termval *)
  :: \<open>nterm \<Rightarrow> 'm intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> 'm\<close>
  (\<open>\<lbrakk>_\<rbrakk>\<^bsup>_,_\<^esup>\<close> [50, 0, 0] 70) where
  \<open>\<lbrakk>Var v\<rbrakk>\<^bsup>_,\<beta>\<^esup> = \<beta> v\<close>
| \<open>\<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = intrp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close> 

definition list_all :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  [simp]: \<open>list_all P ls \<longleftrightarrow> (fold (\<lambda>l b. b \<and> P l) ls True)\<close>

(*TERMSUBST_TERMVAL*)
lemma term_subst_eval: \<open>intrp_fn M = Fun \<Longrightarrow> t \<cdot> v = eval t M v\<close>
sorry

(*TERMVAL_TRIV*)
lemma term_eval_triv[simp]: \<open>intrp_fn M = Fun \<Longrightarrow> eval t M Var = t\<close>
sorry

lemma fold_bool_prop: \<open>(fold (\<lambda>l b. b \<and> P l) ls b) = (b \<and> (\<forall>l\<in>set ls. P l))\<close>
sorry

lemma list_all_set: \<open>list_all P ls = (\<forall>l\<in>set ls. P l)\<close>
sorry

hide_const lang

definition is_interpretation where
  \<open>is_interpretation lang \<M> \<longleftrightarrow> 
    ((\<forall>f l. (f, length(l)) \<in> fst lang \<and> set l \<subseteq> dom \<M> \<longrightarrow> intrp_fn \<M> f l \<in> dom \<M>))\<close>

lemma interpretation_sublanguage: \<open>funs2 \<subseteq> funs1 \<Longrightarrow> is_interpretation (funs1, pred1) \<M>
  \<Longrightarrow> is_interpretation (funs2, preds2) \<M>\<close>
sorry

(*INTERPRETATION_TERMVAL in HOL Light*)
lemma interpretation_eval:
  assumes \<M>: \<open>is_interpretation (functions_term t,any) \<M>\<close> and val: \<open>is_valuation \<M> \<beta>\<close>
  shows \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> \<in> dom \<M>\<close>
sorry

(* Notation Warning: To prevent ambiguity with tuples, the comma is *bold* *)
fun holds
  :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> form \<Rightarrow> bool\<close> (\<open>_\<^bold>,_ \<Turnstile> _\<close> [30, 30, 80] 80) where
  \<open>\<M>\<^bold>,\<beta> \<Turnstile> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>\<M>\<^bold>,\<beta> \<Turnstile> Atom p ts \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> intrp_rel \<M> p\<close>
| \<open>\<M>\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi> \<longleftrightarrow> ((\<M>\<^bold>,\<beta> \<Turnstile> \<phi>) \<longrightarrow> (\<M>\<^bold>,\<beta> \<Turnstile> \<psi>))\<close>
| \<open>\<M>\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<longleftrightarrow> (\<forall>a \<in> dom \<M>. \<M>\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>

lemma holds_exists: \<open>\<M>\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>) \<longleftrightarrow> (\<exists>a \<in> dom \<M>. \<M>\<^bold>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
sorry

lemma holds_indep_\<beta>_if:
  \<open>\<forall> v \<in> FV \<phi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v \<Longrightarrow> \<M>\<^bold>,\<beta>\<^sub>1 \<Turnstile> \<phi> \<longleftrightarrow> \<M>\<^bold>,\<beta>\<^sub>2 \<Turnstile> \<phi>\<close>
sorry

lemma holds_indep_intrp_if:
  fixes
    \<phi> :: form and
    \<M> \<M>' :: \<open>'m intrp\<close> 
  assumes
    dom_eq: \<open>dom \<M> = dom \<M>'\<close> and
    rel_eq: \<open>\<forall> p. intrp_rel \<M> p = intrp_rel \<M>' p\<close> and
    fn_eq: \<open>\<forall> f ts. (f, length ts) \<in> functions_form \<phi> \<longrightarrow> intrp_fn \<M> f ts = intrp_fn \<M>' f ts\<close>
  shows
    \<open>\<forall>\<beta>.  \<M>\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> \<M>'\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
sorry

text \<open>the above in a more idiomatic form (it is a congruence rule)\<close>
corollary holds_cong:
  assumes
    \<open>dom \<M> = dom \<M>'\<close>
    \<open>\<And>p. intrp_rel \<M> p = intrp_rel \<M>' p\<close>
    \<open>\<And>f ts. (f, length ts) \<in> functions_form \<phi> \<Longrightarrow> intrp_fn \<M> f ts = intrp_fn \<M>' f ts\<close>
  shows \<open>\<M>\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> \<M>'\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
sorry

abbreviation (input) \<open>termsubst \<M> \<beta> \<sigma> v \<equiv> \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>

(* HOL Light: termval_termsubst *)
lemma subst_lemma_terms: \<open>\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>,termsubst \<M> \<beta> \<sigma>\<^esup>\<close>
sorry

lemma eval_indep_\<beta>_if:
  assumes \<open>\<forall> v \<in> FVT t. \<beta> v = \<beta>' v\<close>
  shows \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>'\<^esup>\<close>
sorry

lemma concat_map: \<open>[f t. t \<leftarrow> [g t. t \<leftarrow> ts]] = [f (g t). t \<leftarrow> ts]\<close> 
sorry

(* more general than HOL Light: holds_formsubst1 holds_rename *)
lemma swap_subst_eval: \<open>\<M>\<^bold>,\<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>\<^bold>,(\<lambda>v. termsubst \<M> \<beta> \<sigma> v) \<Turnstile> \<phi>\<close>
sorry

definition satisfies :: \<open>'m intrp \<Rightarrow> form set \<Rightarrow> bool\<close> where
  \<open>satisfies \<M> S \<equiv> (\<forall>\<beta> \<phi>. is_valuation \<M> \<beta> \<longrightarrow> \<phi> \<in> S \<longrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>

lemma satisfies_iff_satisfies_sing: \<open>satisfies M S \<longleftrightarrow> (\<forall>\<phi>\<in>S. satisfies M {\<phi>})\<close>
sorry

end
