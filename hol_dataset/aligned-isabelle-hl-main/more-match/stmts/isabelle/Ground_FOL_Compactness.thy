(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory Ground_FOL_Compactness  
imports
    FOL_Semantics
begin


fun qfree :: \<open>form \<Rightarrow> bool\<close> where
  \<open>qfree \<^bold>\<bottom> = True\<close>
| \<open>qfree (Atom p ts) = True\<close>
| \<open>qfree (\<phi> \<^bold>\<longrightarrow> \<psi>) = (qfree \<phi> \<and> qfree \<psi>)\<close>
| \<open>qfree (\<^bold>\<forall> x\<^bold>. \<phi>) = False\<close>

lemma qfree_iff_BV_empty: "qfree \<phi> \<longleftrightarrow> BV \<phi> = {}"
sorry

lemma qfree_no_quantif: \<open>qfree r \<Longrightarrow> \<not>(\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) \<and> \<not>(\<exists>x p. r = \<^bold>\<exists>x\<^bold>. p)\<close>
sorry

lemma qfree_formsubst: \<open>qfree \<phi> \<equiv> qfree (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
sorry

(* != propositional compactness is not proved as in Harrison.
      Instead the existing AFP entry is reused *)

fun form_to_formula :: "form \<Rightarrow> (nat\<times>nterm list) formula" where
  \<open>form_to_formula \<^bold>\<bottom> = \<bottom>\<close>
| \<open>form_to_formula (Atom p ts) = formula.Atom (p,ts)\<close>
| \<open>form_to_formula (\<phi> \<^bold>\<longrightarrow> \<psi>) = Imp (form_to_formula \<phi>) (form_to_formula \<psi>)\<close>
| \<open>form_to_formula (\<^bold>\<forall> x\<^bold>. \<phi>) = \<bottom>\<close>

fun pholds :: \<open>(form \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>p _\<close> [30, 80] 80) where
  \<open>I \<Turnstile>\<^sub>p \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>I \<Turnstile>\<^sub>p Atom p ts \<longleftrightarrow> I (Atom p ts)\<close>
| \<open>I \<Turnstile>\<^sub>p \<phi> \<^bold>\<longrightarrow> \<psi> \<longleftrightarrow> ((I \<Turnstile>\<^sub>p \<phi>) \<longrightarrow> (I \<Turnstile>\<^sub>p \<psi>))\<close>
| \<open>I \<Turnstile>\<^sub>p (\<^bold>\<forall> x\<^bold>. \<phi>) \<longleftrightarrow> I (\<^bold>\<forall> x\<^bold>. \<phi>)\<close>

definition psatisfiable :: "form set \<Rightarrow> bool" where
  \<open>psatisfiable S \<equiv> \<exists>I. \<forall>\<phi>\<in>S. I \<Turnstile>\<^sub>p \<phi>\<close>

abbreviation psatisfies where \<open>psatisfies I \<Phi> \<equiv> \<forall>\<phi>\<in>\<Phi>. pholds I \<phi>\<close>

definition val_to_prop_val :: "(form \<Rightarrow> bool) \<Rightarrow> ((nat \<times> nterm list) \<Rightarrow> bool)" where
  \<open>val_to_prop_val I = (\<lambda>x. I (Atom (fst x) (snd x)))\<close>

lemma pholds_Not: \<open>I \<Turnstile>\<^sub>p Not \<phi> \<longleftrightarrow> \<not> (I \<Turnstile>\<^sub>p \<phi>)\<close>
sorry

lemma pentails_equiv: \<open>qfree \<phi> \<Longrightarrow> (I \<Turnstile>\<^sub>p \<phi> \<equiv> (val_to_prop_val I) \<Turnstile> (form_to_formula \<phi>))\<close>
sorry

lemma pentails_equiv_set:
  assumes all_qfree: \<open>\<forall>\<phi>\<in>S. qfree \<phi>\<close>
  shows \<open>psatisfiable S \<equiv> sat (form_to_formula ` S)\<close>
sorry

definition finsat :: "form set \<Rightarrow> bool" where
  \<open>finsat S \<equiv> \<forall>T\<subseteq>S. finite T \<longrightarrow> psatisfiable T\<close>

lemma finsat_fin_sat_eq:
  assumes all_qfree: \<open>\<forall>\<phi>\<in>S. qfree \<phi>\<close>
  shows \<open>finsat S \<longleftrightarrow> fin_sat (form_to_formula ` S)\<close>
sorry

lemma psatisfiable_mono: \<open>psatisfiable S  \<Longrightarrow> T \<subseteq> S \<Longrightarrow> psatisfiable T\<close>
sorry

lemma finsat_mono: \<open>finsat S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> finsat T\<close>
sorry

lemma finsat_satisfiable: \<open>psatisfiable S \<Longrightarrow> finsat S\<close>
sorry

lemma prop_compactness: \<open>(\<forall>\<phi> \<in> S. qfree \<phi>) \<Longrightarrow> finsat S = psatisfiable S\<close>
sorry

text \<open>as above, more in the style of HOL Light\<close>
lemma compact_prop:
  assumes \<open>\<And>B. \<lbrakk>finite B; B \<subseteq> A\<rbrakk> \<Longrightarrow> \<exists>I. psatisfies I B\<close> and \<open>\<And>\<phi>. \<phi> \<in> A \<longrightarrow> qfree \<phi>\<close>
  shows \<open>\<exists>I. psatisfies I A\<close>
sorry

text \<open>Three results required for the FOL uniformity theorem\<close>

lemma compact_prop_alt:
  assumes \<open>\<And>I. \<exists>\<phi>\<in>A. I \<Turnstile>\<^sub>p \<phi>\<close> \<open>\<And>\<phi>. \<phi> \<in> A \<longrightarrow> qfree \<phi>\<close>
  obtains B where \<open>finite B\<close> \<open>B \<subseteq> A\<close> \<open>\<And>I. \<exists>\<phi>\<in>B. I \<Turnstile>\<^sub>p \<phi>\<close>
sorry

lemma finite_disj_lemma:
  assumes \<open>finite A\<close>
  shows \<open>\<exists>\<Phi>. set \<Phi> \<subseteq> A \<and> (\<forall>I. I \<Turnstile>\<^sub>p foldr (\<^bold>\<or>) \<Phi> \<^bold>\<bottom> \<longleftrightarrow> (\<exists>\<phi>\<in>A. I \<Turnstile>\<^sub>p \<phi>))\<close>
sorry

lemma compact_disj:
  assumes \<open>\<And>I. \<exists>\<phi>\<in>A. I \<Turnstile>\<^sub>p \<phi>\<close> \<open>\<And>\<phi>. \<phi> \<in> A \<longrightarrow> qfree \<phi>\<close>
  obtains \<Phi> where \<open>set \<Phi> \<subseteq> A\<close> \<open>\<And>I. I \<Turnstile>\<^sub>p foldr (\<^bold>\<or>) \<Phi> \<^bold>\<bottom>\<close>
sorry

end
