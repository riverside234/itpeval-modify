(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2024 *)

theory Bumping
imports 
  FOL_Semantics
  "HOL-Library.Nat_Bijection"
begin

(* Diverges from hol-light version by reusing a nat \<times> nat \<Rightarrow> nat encoding available in Isabelle/HOL 
 * /!\ The encoding is not the same (but it serves the same purpose)
 * The hol-light names numpair, numfst and numsnd have been kept to help with the translation *)
abbreviation numpair where
  \<open>numpair m n \<equiv> prod_encode (m,n)\<close>

abbreviation numfst where
  \<open>numfst k \<equiv> fst (prod_decode k)\<close>

abbreviation numsnd where
  \<open>numsnd k \<equiv> snd (prod_decode k)\<close>

(* bumpmod in hol-light *)
definition bump_intrp :: "'m intrp \<Rightarrow> 'm intrp" where
  \<open>bump_intrp \<M> = Abs_intrp ((dom \<M>), (\<lambda>k zs. (intrp_fn \<M>) (numsnd k) zs), (intrp_rel \<M>))\<close>

lemma bump_dom [simp]: \<open>dom (bump_intrp \<M>) = dom \<M>\<close>
sorry

lemma bump_intrp_fn [simp]: \<open>intrp_fn (bump_intrp \<M>) (numpair 0 f) ts = intrp_fn \<M> f ts\<close>
sorry

lemma bump_intrp_rel [simp]: \<open>intrp_rel (bump_intrp \<M>) n = intrp_rel \<M> n\<close>
sorry

(* bumpterm in hol-light *)
fun bump_nterm :: "nterm \<Rightarrow> nterm" where
  \<open>bump_nterm (Var x) = Var x\<close>
| \<open>bump_nterm (Fun f ts) = Fun (numpair 0 f) (map bump_nterm ts)\<close>

(* bumpform in hol-light *)
fun bump_form :: "form \<Rightarrow> form" where
  \<open>bump_form \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>bump_form (Atom p ts) = Atom p (map bump_nterm ts)\<close>
| \<open>bump_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = (bump_form \<phi>) \<^bold>\<longrightarrow> (bump_form \<psi>)\<close>
| \<open>bump_form (\<^bold>\<forall> x\<^bold>. \<phi>) = \<^bold>\<forall> x\<^bold>. (bump_form \<phi>)\<close>


lemma bumpterm: \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>bump_nterm t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>\<close>
sorry

lemma bump_intrp_rel_holds: \<open>(map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) ts \<in> intrp_rel \<M> n) =
  (map ((\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>bump_intrp \<M>,\<beta>\<^esup>) \<circ> bump_nterm) ts \<in> intrp_rel (bump_intrp \<M>) n)\<close>
sorry

lemma bumpform: \<open>\<M>\<^bold>, \<beta> \<Turnstile> \<phi> = (bump_intrp \<M>)\<^bold>, \<beta> \<Turnstile> (bump_form \<phi>)\<close>
sorry

lemma functions_form_bumpform: \<open>(f, m) \<in> functions_form (bump_form \<phi>) \<Longrightarrow>
  \<exists>k. (f = numpair 0 k) \<and> (k, m) \<in> functions_form \<phi>\<close>
sorry

lemma bumpform_interpretation: \<open>is_interpretation (language {\<phi>}) \<M> \<Longrightarrow>
  is_interpretation (language {(bump_form \<phi>)}) (bump_intrp \<M>)\<close>
sorry

(* unbumpterm in hol-light *)
fun unbump_nterm :: "nterm \<Rightarrow> nterm" where
  \<open>unbump_nterm (Var x) = Var x\<close>
| \<open>unbump_nterm (Fun f ts) = Fun (numsnd f) (map unbump_nterm ts)\<close>

(* unbumpform in hol-light *)
fun unbump_form :: "form \<Rightarrow> form" where
  \<open>unbump_form \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>unbump_form (Atom p ts) = Atom p (map unbump_nterm ts)\<close>
| \<open>unbump_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = (unbump_form \<phi>) \<^bold>\<longrightarrow> (unbump_form \<psi>)\<close>
| \<open>unbump_form (\<^bold>\<forall> x\<^bold>. \<phi>) = \<^bold>\<forall> x\<^bold>. (unbump_form \<phi>)\<close>

lemma unbumpterm [simp]: "unbump_nterm (bump_nterm t) = t"
sorry

lemma unbumpform [simp]: \<open>unbump_form (bump_form \<phi>) = \<phi>\<close>
sorry

(* unbumpmod in hol-light *)
definition unbump_intrp :: "'m intrp \<Rightarrow> 'm intrp" where
  \<open>unbump_intrp \<M> = Abs_intrp (dom \<M>, (\<lambda>k zs. (intrp_fn \<M>) (numpair 0 k) zs), (intrp_rel \<M>))\<close>

(* UNBUMPMOD_TERM in hol-light *)
lemma unbump_term_intrp: \<open>\<lbrakk>bump_nterm t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>unbump_intrp \<M>,\<beta>\<^esup>\<close>
sorry

(*  UNBUMPMOD in hol-light *)
lemma unbump_holds: \<open>(\<M>\<^bold>,\<beta> \<Turnstile> bump_form \<phi>) = (unbump_intrp \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
sorry

abbreviation numlist where
  \<open>numlist ns \<equiv> list_encode ns\<close>

fun num_of_term :: "nterm \<Rightarrow> nat" where
  \<open>num_of_term (Var x) = numpair 0 x\<close>
| \<open>num_of_term (Fun f ts) = numpair 1 (numpair f (numlist (map num_of_term ts)))\<close>

(* to move in AFP theory First-Order Terms.Term *)
lemma term_induct2:
  "(\<And>x y. P (Var x) (Var y))
    \<Longrightarrow> (\<And>x g us. P (Var x) (Fun g us))
    \<Longrightarrow> (\<And>f ts y. P (Fun f ts) (Var y)) 
    \<Longrightarrow> (\<And>f ts g us. (\<And>p q. p \<in> set ts \<Longrightarrow> q \<in> set us \<Longrightarrow> P p q) \<Longrightarrow> P (Fun f ts) (Fun g us))
    \<Longrightarrow> P t1 t2"
sorry
(************************************************)

lemma num_of_term_inj: \<open>num_of_term s = num_of_term t \<longleftrightarrow> s = t\<close>
sorry

fun num_of_form :: "form \<Rightarrow> nat" where
  \<open>num_of_form \<^bold>\<bottom> = numpair 0 0\<close>
| \<open>num_of_form (Atom p ts) = numpair 1 (numpair p (numlist (map num_of_term ts)))\<close>
| \<open>num_of_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = numpair 2 (numpair (num_of_form \<phi>) (num_of_form \<psi>))\<close>
| \<open>num_of_form (\<^bold>\<forall>x\<^bold>. \<phi>) = numpair 3 (numpair x (num_of_form \<phi>))\<close>

lemma numlist_num_of_term: \<open>numlist (map num_of_term ts) = (numlist (map num_of_term us)) \<equiv> ts = us\<close>
sorry

lemma num_of_form_inj: \<open>num_of_form \<phi> = num_of_form \<psi> \<longleftrightarrow> \<phi> = \<psi>\<close>
sorry

consts term_of_num :: "nat \<Rightarrow> nterm"
specification (term_of_num) \<open>\<forall>n. term_of_num n = (THE t. num_of_term t = n)\<close>
  using num_of_term_inj by force

(* TERM_OF_NUM in hol-light *)
lemma term_of_num_of_term [simp]: \<open>term_of_num(num_of_term t) = t\<close>
sorry

consts form_of_num :: "nat \<Rightarrow> form"
specification (form_of_num) \<open>\<forall>n. form_of_num n = (THE \<phi>. num_of_form \<phi> = n)\<close>
  using num_of_form_inj by force

(* FORM_OF_NUM in hol-light *)
lemma form_of_num_of_form [simp]: \<open>form_of_num (num_of_form \<phi>) = \<phi>\<close>
sorry

end
