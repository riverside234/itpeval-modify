(* Title:        Part of the proof of compactness of first-order logic following Harrison's in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2024
                 Larry Paulson, 2024 *)

theory Canonical_Models
  imports Skolem_Normal_Form
begin


inductive_set terms_set :: \<open>(nat \<times> nat) set \<Rightarrow> nterm set\<close> for fns :: \<open>(nat \<times> nat) set\<close> where
  vars: \<open>(Var v) \<in> terms_set fns\<close>
| fn: \<open>(Fun f ts) \<in> terms_set fns\<close>
  if \<open>(f, length ts) \<in> fns\<close> \<open>\<And>t. t \<in> set ts \<Longrightarrow> t \<in> terms_set fns\<close>

lemma struct_terms_set [iff]: \<open>struct (terms_set A)\<close>
sorry

(* STUPID_CANONDOM_LEMMA in HOL Light *)
lemma stupid_canondom: \<open>t \<in> terms_set (fst \<L>) \<Longrightarrow> functions_term t \<subseteq> (fst \<L>)\<close>
sorry

(* FINITE_SUBSET_INSTANCE in HOL Light *)
lemma finite_subset_instance: \<open>finite t' \<Longrightarrow> t' \<subseteq> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<sigma> \<phi>. P \<sigma> \<and> \<phi> \<in> s} \<Longrightarrow>
  (\<exists>t. finite t \<and> t \<subseteq> s \<and> t' \<subseteq> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<sigma> \<phi>. P \<sigma> \<and> \<phi> \<in> t})\<close>
sorry

(* FINITE_SUBSET_SKOLEM in HOL Light *)
lemma finite_subset_skolem: \<open>finite u \<Longrightarrow> u \<subseteq> {skolem \<phi> |\<phi>. \<phi> \<in> s} \<Longrightarrow>
  (\<exists>t. finite t \<and> t \<subseteq> s \<and> u = {skolem \<phi> |\<phi>. \<phi> \<in> t})\<close>
sorry

(* VALUATION_EXISTS in HOL Light *)
lemma valuation_exists: \<open>\<not> (dom M = {}) \<Longrightarrow> \<exists>\<beta>. is_valuation M \<beta>\<close>
sorry

(* HOLDS_ITLIST_EXISTS in HOL Light *)
lemma holds_itlist_exists: 
  \<open>(M\<^bold>,\<beta> \<Turnstile> (foldr (\<lambda>x p. \<^bold>\<exists>x\<^bold>. p) xs \<phi>)) \<longleftrightarrow> 
     (\<exists>as. length as = length xs \<and> set as \<subseteq> dom M \<and> 
           (M\<^bold>,(foldr (\<lambda>u \<beta>. \<beta>(fst u := snd u)) (rev (zip xs as)) \<beta>) \<Turnstile> \<phi>))\<close>
sorry

definition canonical :: \<open>(nat \<times> nat) set \<times> (nat \<times> nat) set \<Rightarrow> nterm intrp \<Rightarrow> bool\<close> where
\<open>canonical \<L> \<M> \<equiv> (dom \<M> = terms_set (fst \<L>) \<and> (\<forall>f. intrp_fn \<M> f = Fun f))\<close>

(* Slight deviation from the HOL Light definition where "Atom p ts" appears on the left, which is
   forbidden in Isabelle, I don't see how to define it only for atoms and obtain a propositional
   interpretation: *)
(* prop_of_model in HOL Light *)
definition pintrp_of_intrp :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> (form \<Rightarrow> bool)\<close> where
  \<open>pintrp_of_intrp \<M> \<beta> = (\<lambda>\<phi>. \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>

(* the predicates are not defined exactly in the same way here and in HOL Light, 
   I replaced the predicate d with the set of all valid atoms and the function returns the list
   of accepted arguments for a given predicate instead of being a Boolean for compatibility.
*)
definition 
  canon_of_prop :: \<open>((nat \<times> nat) set \<times> (nat \<times> nat) set) \<Rightarrow> (form \<Rightarrow> bool) \<Rightarrow> nterm intrp\<close> where
  \<open>canon_of_prop \<L> I \<equiv> Abs_intrp (terms_set (fst \<L>), Fun, (\<lambda>p. {ts. I (Atom p ts)}))\<close>

lemma dom_canon_of_prop [simp]: \<open>dom (canon_of_prop \<L> I) = terms_set (fst \<L>)\<close>
sorry

lemma intrp_fn_canon_of_prop [simp]: \<open>intrp_fn (canon_of_prop \<L> I) = Fun\<close>
sorry

lemma intrp_rel_canon_of_prop [simp]: \<open>intrp_rel (canon_of_prop \<L> I) = (\<lambda>p. {ts. I (Atom p ts)})\<close>
sorry

lemma pholds_pintrp_of_intrp:
  \<open>qfree \<phi> \<Longrightarrow> (pintrp_of_intrp \<M> \<beta>) \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
sorry

(* PROP_OF_CANON_OF_PROP in HOL Light *)
lemma intrp_of_canon_of_prop [simp]:
  \<open>pintrp_of_intrp (canon_of_prop \<L> I) Var (Atom p ts) = I (Atom p ts)\<close>
sorry

(* HOLDS_CANON_OF_PROP in HOL Light *)
lemma holds_canon_of_prop:
  assumes \<open>qfree \<phi>\<close> shows \<open>(canon_of_prop \<L> I)\<^bold>,Var \<Turnstile> \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p \<phi>\<close>
sorry

(* HOLDS_CANON_OF_PROP_GENERAL in HOL Light *)
(* It is strange to apply a valuation to a formula anyway, it is a kind of misuse of the fact that 
    valuations for canonical models and substitutions have the same type *)
lemma holds_canon_of_prop_general: 
  assumes \<open>qfree \<phi>\<close> shows \<open>(canon_of_prop \<L> I)\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p (\<phi> \<cdot>\<^sub>f\<^sub>m \<beta>)\<close>
sorry

(* CANONICAL_CANON_OF_PROP in HOL Light *)
lemma canonical_canon_of_prop: \<open>canonical \<L> (canon_of_prop \<L> I)\<close>
sorry

(* INTERPRETATION_CANON_OF_PROP in hol-ligh *)
lemma interpretation_canon_of_prop: \<open>is_interpretation \<L> (canon_of_prop \<L> I)\<close>
sorry

(* PROP_VALID_IMP_FOL_VALID in HOL Light *)
lemma prop_valid_imp_fol_valid: \<open>qfree \<phi> \<and> (\<forall>I. I \<Turnstile>\<^sub>p \<phi>) \<Longrightarrow> (\<forall>\<M> \<beta>. \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
sorry

(* FOL_VALID_IMP_PROP_VALID *)
lemma fol_valid_imp_prop_valid: \<open>qfree \<phi> \<and> (\<forall>\<M> \<beta>. canonical (language {\<phi>}) \<M> \<longrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)
  \<Longrightarrow> \<forall>I. I \<Turnstile>\<^sub>p \<phi>\<close>
sorry

(* SATISFIES_PSATISFIES *)
lemma satisfies_psatisfies: \<open>\<lbrakk>\<phi> \<in> \<Phi>; \<Phi> \<subseteq> {\<phi>. qfree \<phi>}; satisfies \<M> \<Phi>; is_valuation \<M> \<beta>\<rbrakk> \<Longrightarrow>
  psatisfies (pintrp_of_intrp \<M> \<beta>) \<Phi>\<close>
sorry

(* PSATISFIES_INSTANCES in HOL Light *)
lemma psatisfies_instances:
  assumes qf: \<open>\<Phi> \<subseteq> {\<phi>. qfree \<phi>}\<close>
    and ps: \<open>psatisfies I {\<phi> \<cdot>\<^sub>f\<^sub>m \<beta> |\<phi> \<beta>. (\<forall>x. \<beta> x \<in> terms_set (fst \<L>)) \<and> \<phi> \<in> \<Phi>}\<close>
  shows \<open>satisfies (canon_of_prop \<L> I) \<Phi>\<close>
sorry

(* SATISFIES_INSTANCES in HOL Light *)
lemma satisfies_instances:
  assumes \<open>is_interpretation (language \<Xi>) \<M>\<close>
  shows \<open>satisfies \<M> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<phi> \<sigma>. \<phi> \<in> \<Phi> \<and> (\<forall>x. \<sigma> x \<in> terms_set (fst (language \<Xi>)))} \<longleftrightarrow>
         satisfies \<M> \<Phi>\<close>
sorry

(* COMPACT_CANON_QFREE in HOL Light *)
(* I don't see the point of \<open>language \<Xi>\<close> here instead of, e.g., \<L> *)
lemma compact_canon_qfree:
  assumes qf: \<open>\<Phi> \<subseteq> {\<phi>. qfree \<phi>}\<close>
  and int: \<open>\<And>\<Psi>. \<lbrakk>finite \<Psi>; \<Psi> \<subseteq> \<Phi>\<rbrakk> 
             \<Longrightarrow> \<exists>\<M>::'a intrp. is_interpretation (language \<Xi>) \<M> \<and> dom \<M> \<noteq> {} \<and> satisfies \<M> \<Psi>\<close>
  obtains \<C> where \<open>is_interpretation (language \<Xi>) \<C>\<close> \<open>canonical (language \<Xi>) \<C>\<close> \<open>satisfies \<C> \<Phi>\<close>
sorry

(* INTERPRETATION_RESTRICTLANGUAGE in HOL Light *)
lemma interpretation_restrictlanguage: 
  \<open>\<Psi> \<subseteq> \<Phi> \<Longrightarrow> is_interpretation (language \<Phi>) \<M> \<Longrightarrow> is_interpretation (language \<Psi>) \<M>\<close>
sorry

(* INTERPRETATION_EXTENDLANGUAGE in HOL Light *)
lemma interpretation_extendlanguage: 
  fixes \<M>:: \<open>'a intrp\<close>
  assumes int: \<open>is_interpretation (language \<Psi>) \<M>\<close> and \<open>dom \<M> \<noteq> {}\<close>
    and \<open>satisfies \<M> \<Psi>\<close>
  obtains \<N> where \<open>dom \<N> = dom \<M>\<close> \<open>intrp_rel \<N> = intrp_rel \<M>\<close> 
                    \<open>is_interpretation (language \<Phi>) \<N>\<close> \<open>satisfies \<N> \<Psi>\<close>
sorry

(* COMPACT_LS in HOL Light *)
theorem compact_ls:
  assumes \<open>\<And>\<Psi>. \<lbrakk>finite \<Psi>; \<Psi> \<subseteq> \<Phi>\<rbrakk> 
             \<Longrightarrow> \<exists>\<M>::'a intrp. is_interpretation (language \<Phi>) \<M> \<and> dom \<M> \<noteq> {} \<and> satisfies \<M> \<Psi>\<close>
  obtains \<C>::\<open>nterm intrp\<close> where \<open>is_interpretation (language \<Phi>) \<C>\<close> \<open>dom \<C> \<noteq> {}\<close> \<open>satisfies \<C> \<Phi>\<close>
sorry

(* CANON in HOL Light *)
lemma canon:
  assumes \<open>is_interpretation (language \<Phi>) \<M>\<close> \<open>dom \<M> \<noteq> {}\<close> \<open>satisfies \<M> \<Phi>\<close>
  obtains \<C>::\<open>nterm intrp\<close> where \<open>is_interpretation (language \<Phi>) \<C>\<close> \<open>dom \<C> \<noteq> {}\<close> \<open>satisfies \<C> \<Phi>\<close>
sorry

(* LOWMOD in HOL Light *)
definition lowmod :: \<open>nterm intrp \<Rightarrow> nat intrp\<close> where
  \<open>lowmod \<M> \<equiv> Abs_intrp (num_of_term ` (dom \<M>), 
    (\<lambda>g ns. num_of_term (intrp_fn \<M> g (map term_of_num ns))), 
    (\<lambda>p. {ns. (map term_of_num ns) \<in> intrp_rel \<M> p}))\<close>

lemma dom_lowmod [simp]: \<open>dom (lowmod \<M>) = num_of_term ` (dom \<M>)\<close>
sorry

lemma intrp_fn_lowmod [simp]: \<open>intrp_fn (lowmod \<M>) f ns = num_of_term (intrp_fn \<M> f (map term_of_num ns))\<close>
sorry

lemma intrp_rel_lowmod [simp]: \<open>intrp_rel (lowmod \<M>) p = {ns. (map term_of_num ns) \<in> intrp_rel \<M> p}\<close>
sorry

lemma is_valuation_lowmod: \<open>is_valuation (lowmod \<C>) (num_of_term \<circ> \<beta>) \<longleftrightarrow> is_valuation \<C> \<beta>\<close>
sorry

(* LOWMOD_DOM_EMPTY in HOL Light *)
lemma lowmod_dom_empty: \<open>dom (lowmod \<M>) = {} \<longleftrightarrow> dom \<M> = {}\<close>
sorry

(* LOWMOD_TERMVAL in HOL Light *)
lemma lowmod_termval: 
  assumes \<open>is_valuation (lowmod \<M>) \<beta>\<close>
  shows \<open>eval t (lowmod \<M>) \<beta> = num_of_term (eval t \<M> (term_of_num \<circ> \<beta>))\<close>
sorry

(* LOWMOD_HOLDS in HOL Light *)
lemma lowmod_holds:
  assumes \<open>is_valuation (lowmod \<M>) \<beta>\<close>
  shows  \<open>(lowmod \<M>)\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> \<M>\<^bold>,(term_of_num \<circ> \<beta>) \<Turnstile> \<phi>\<close>
sorry

(* LOWMOD_INTERPRETATION in HOL Light *)
lemma lowmod_intrp: \<open>is_interpretation \<L> (lowmod \<M>) = is_interpretation \<L> \<M>\<close>
sorry

(* LS in HOL Light *)
lemma loewenheim_skolem: 
  assumes \<open>is_interpretation (language \<Phi>) \<M>\<close> \<open>dom \<M> \<noteq> {}\<close> 
  assumes \<open>\<And>\<phi>. \<phi> \<in> \<Phi> \<Longrightarrow> qfree \<phi>\<close> \<open>satisfies \<M> \<Phi>\<close>
  obtains \<N> :: \<open>nat intrp\<close> where \<open>is_interpretation (language \<Phi>) \<N>\<close> \<open>dom \<N> \<noteq> {}\<close> \<open>satisfies \<N> \<Phi>\<close>
sorry

(* UNIFORMITY in HOL Light *)
theorem uniformity:
  assumes \<open>qfree \<phi>\<close> 
          \<open>\<And>\<C>::nterm intrp. \<And>\<beta>. \<lbrakk>dom \<C> \<noteq> {}; is_valuation \<C> \<beta>\<rbrakk> \<Longrightarrow> \<C>\<^bold>,\<beta> \<Turnstile> foldr Exists xs \<phi>\<close>
  obtains \<sigma>s where \<open>\<And>\<sigma> x. \<sigma> \<in> set \<sigma>s \<Longrightarrow> \<sigma> x \<in> terms_set (fst (language {\<phi>}))\<close>
                   \<open>\<And>I. I \<Turnstile>\<^sub>p (foldr (\<lambda>\<phi> \<psi>. \<phi> \<^bold>\<or> \<psi>) (map (\<lambda>\<sigma>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<sigma>s) \<^bold>\<bottom>)\<close>
sorry

end
