(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory Prenex_Normal_Form
imports
    Ground_FOL_Compactness
begin


inductive is_prenex :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> is_prenex \<phi>\<close>
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>

inductive_simps is_prenex_simps [simp]:
  "is_prenex Bot"
  "is_prenex (Atom p ts)"
  "is_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>)"
  "is_prenex (\<^bold>\<forall> x\<^bold>. \<phi>)"

lemma prenex_formsubst1: \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
sorry

lemma prenex_formsubst2: \<open>is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<Longrightarrow> is_prenex \<phi>\<close>
sorry

lemma prenex_formsubst: \<open>is_prenex (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<equiv> is_prenex \<phi>\<close>
sorry

lemma prenex_imp: \<open>is_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) \<Longrightarrow>
  qfree (\<phi> \<^bold>\<longrightarrow> \<psi>) \<or> (\<psi> = \<^bold>\<bottom> \<and> (\<exists>x \<phi>'. is_prenex \<phi>' \<and> \<phi> = (\<^bold>\<forall>x\<^bold>. \<phi>' \<^bold>\<longrightarrow> \<^bold>\<bottom>)))\<close>
sorry

inductive universal :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> universal \<phi>\<close>
| \<open>universal \<phi> \<Longrightarrow> universal (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>

inductive_simps universal_simps [simp]:
  "universal Bot"
  "universal (Atom p ts)"
  "universal (\<phi> \<^bold>\<longrightarrow> \<psi>)"
  "universal (\<^bold>\<forall> x\<^bold>. \<phi>)"

fun size :: "form \<Rightarrow> nat" where
  \<open>size \<^bold>\<bottom> = 1\<close>
| \<open>size (Atom p ts) = 1\<close>
| \<open>size (\<phi> \<^bold>\<longrightarrow> \<psi>) = size \<phi> + size \<psi>\<close>
| \<open>size (\<^bold>\<forall> x\<^bold>. \<phi>) = 1 + size \<phi>\<close>

lemma wf_size: \<open>wfP (\<lambda>\<phi> \<psi>. size \<phi> < size \<psi>)\<close>
sorry

lemma size_indep_subst: \<open>size (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = size \<phi>\<close>
sorry

lemma prenex_distinct: \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<noteq> (\<^bold>\<exists>y\<^bold>. \<psi>)\<close>
sorry

lemma uniq_all_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)" (* necessaire pour décharger le "THE" *)
sorry

lemma uniq_all_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p))\<close>
sorry

lemma uniq_ex_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)"
sorry

lemma uniq_ex_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p))\<close>
sorry

definition ppat :: "(nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> form" where
  \<open>ppat A B C r = (if (\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) then
    A (THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p) (THE p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p)
  else (if \<exists>x p. r = \<^bold>\<exists>x\<^bold>. p then
    B (THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p) (THE p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p)
   else C r))\<close>

lemma ppat_simpA: \<open>\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p\<close>
sorry

lemma ppat_simpB: \<open>\<forall>x p. ppat A B C (\<^bold>\<exists>x\<^bold>. p) = B x p\<close>
sorry

(* simplified unneeded hypotheses: (\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p) \<Longrightarrow> (\<forall>x p. ppat A B C (\<^bold>\<exists>x\<^bold>. p) = B x p) *)
lemma ppat_last: \<open>(\<forall>r. \<not>(\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) \<and> \<not>(\<exists>x p. r = \<^bold>\<exists>x\<^bold>. p)) \<Longrightarrow> ppat A B C r = C r\<close>
sorry

(* idem here *)
lemma ppat_last_qfree: \<open>qfree r \<Longrightarrow> ppat A B C r = C r\<close>
sorry

(* holds but useless because not recursive *)
lemma ppat_to_ex_qfree:
  \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = ((A :: form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form) p) x q) \<and>
  (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = (B p) x q) \<and>
  (\<forall>p q. qfree q \<longrightarrow> f p q = (C p) q))\<close>
sorry

lemma size_rec:
  \<open>\<forall>f g x. (\<forall>(z::form). size z < size x \<longrightarrow> (f z = g z)) \<longrightarrow> (H f x = H g x) \<Longrightarrow> (\<exists>f. \<forall>x. f x = H f x)\<close>
sorry

abbreviation prenex_right_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  \<open>prenex_right_forall \<equiv>
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

abbreviation prenex_right_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  \<open>prenex_right_exists \<equiv>
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

lemma prenex_right_ex:
  \<open>\<exists>prenex_right. (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
sorry

(* is it unique? \<rightarrow> No, it is undefined in the last case if \<not>qfree \<phi>. Use SOME, not THE  *)
consts prenex_right :: "form \<Rightarrow> form \<Rightarrow> form"
specification (prenex_right) \<open>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
  using prenex_right_ex by blast

lemma prenex_right_qfree_case: \<open>qfree \<psi> \<Longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
sorry

lemma prenex_right_all_case: \<open>prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
sorry

lemma prenex_right_exist_case: \<open>prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
sorry

lemma prenex_right_exists_shape_case:
  \<open>\<exists>x2 \<sigma>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = \<^bold>\<exists>x2\<^bold>. prenex_right \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
sorry


abbreviation prenex_left_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  \<open>prenex_left_forall \<equiv>
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

abbreviation prenex_left_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where
  \<open>prenex_left_exists \<equiv>
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

lemma prenex_left_ex:
  \<open>\<exists>prenex_left. (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>)\<close>
sorry

definition prenex_left where \<open>prenex_left = (SOME prenex_left.
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>))\<close>

lemma prenex_left_forall_case: \<open>prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>\<close>
sorry

lemma prenex_left_qfree_case: \<open>qfree \<phi> \<Longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>\<close>
sorry

lemma prenex_left_exists_case: \<open>prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>\<close>
sorry

lemma prenex_left_exists_shape_case:
  \<open>\<exists>x2 \<sigma>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = \<^bold>\<forall>x2\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<psi>\<close>
sorry

fun prenex where
  \<open>prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>prenex (Atom p ts) = Atom p ts\<close>
| \<open>prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = prenex_left (prenex \<phi>) (prenex \<psi>)\<close>
| \<open>prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (prenex \<phi>)\<close>

lemma holds_indep_forall:
  assumes y_notin: \<open>y \<notin> FV (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
  shows \<open>(I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
sorry

lemma forall_imp_commute:
  assumes y_notin: \<open>y \<notin> FV \<phi>\<close>
  shows \<open>((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>y\<^bold>. \<psi>))  \<longleftrightarrow>  I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
sorry

lemma forall_imp_exists:
  assumes y_notin: \<open>y \<notin> FV \<psi>\<close>
  shows \<open>((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<forall>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>)  \<longleftrightarrow>  I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
sorry

lemma exists_imp_forall:
  assumes y_notin: \<open>y \<notin> FV \<psi>\<close>
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<exists>y\<^bold>.\<phi>) \<^bold>\<longrightarrow>  \<psi>)  \<longleftrightarrow>  I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>y\<^bold>. (\<phi> \<^bold>\<longrightarrow> \<psi>)))\<close>
sorry

lemma exists_imp_commute:
  assumes y_notin: \<open>y \<notin> FV \<phi>\<close>
  shows \<open>((I :: 'a intrp)\<^bold>, \<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>y\<^bold>. \<psi>)) \<longleftrightarrow> I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
sorry

lemma holds_indep_exists:
  \<open>y \<notin> FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<Longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>)  \<longleftrightarrow>  I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>y\<^bold>. \<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))\<close>
sorry

(* sublemmas for is_prenex(prenex _)*)

(* holds M (v:num->A) (p --> !!y (formsubst (valmod (x,V y) V) q)) *)
lemma prenex_right_forall_is:
  assumes \<open>dom I \<noteq> {}\<close>
  shows \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>))  \<longleftrightarrow>
  (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>.
             (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))))))))))\<close> (is "?lhs = ?rhs")
sorry

lemma prenex_right_exists_is:
  assumes \<open>dom I \<noteq> {}\<close>
  shows \<open>((I\<^bold>, \<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>))  \<longleftrightarrow>
  (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>.
             (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))))))))))\<close> (is "?lhs = ?rhs")
sorry

lemma prenex_left_forall_is:
  assumes \<open>dom I \<noteq> {}\<close>
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>)) \<equiv> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>.
               ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)))\<close>
sorry

lemma prenex_left_exists_is:
  assumes \<open>dom I \<noteq> {}\<close>
  shows \<open>(I\<^bold>, \<beta> \<Turnstile> ((\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>)) \<equiv> (I\<^bold>, \<beta> \<Turnstile> (\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>.
               ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)))\<close>
sorry

(* sublemmas for prenex prop on FV *)
lemma prenex_right_forall_FV: \<open>FV (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>)) =
  FV (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>))))))))\<close>
sorry

lemma prenex_right_exists_FV: \<open>FV (\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>)) =
  FV (\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>))))))))\<close>
sorry

lemma prenex_left_forall_FV: \<open>FV ((\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>) =
  FV (\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>))\<close>
sorry

lemma prenex_left_exists_FV: \<open>FV ((\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>) =
  FV (\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>))\<close>
sorry

(* sublemmas for prenex prop on language *)
lemma prenex_right_forall_language: \<open>language {\<phi> \<^bold>\<longrightarrow> (\<^bold>\<forall>x\<^bold>. \<psi>)} =
  language {\<^bold>\<forall>(variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)))))))}\<close>
sorry

lemma prenex_right_exists_language: \<open>language {\<phi> \<^bold>\<longrightarrow> (\<^bold>\<exists>x\<^bold>. \<psi>)} =
  language {\<^bold>\<exists>(variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))\<^bold>. (\<phi> \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)))))))}\<close>
sorry

lemma prenex_left_forall_language: \<open>language {(\<^bold>\<forall>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>} =
  language {\<^bold>\<exists>(variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)}\<close>
sorry

lemma prenex_left_exists_language: \<open>language {(\<^bold>\<exists>x\<^bold>. \<phi>) \<^bold>\<longrightarrow> \<psi>} =
  language {\<^bold>\<forall>(variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))\<^bold>. ((\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var (variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>))))) \<^bold>\<longrightarrow> \<psi>)}\<close>
sorry

(* prenex properties lemmas *)
lemma prenex_props_forall: \<open>P \<and> FV \<phi> = FV \<psi> \<and> language {\<phi>} = language {\<psi>} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)) \<Longrightarrow>
  P \<and> FV (\<^bold>\<forall>x\<^bold>. \<phi>) = FV (\<^bold>\<forall>x\<^bold>. \<psi>) \<and> language {(\<^bold>\<forall>x\<^bold>. \<phi>)} = language {(\<^bold>\<forall>x\<^bold>. \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<forall>x\<^bold>. \<psi>)))
\<close>
sorry

lemma prenex_props_exists: \<open>P \<and> FV \<phi> = FV \<psi> \<and> language {\<phi>} = language {\<psi>} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<psi>)) \<Longrightarrow>
  P \<and> FV (\<^bold>\<exists>x\<^bold>. \<phi>) = FV (\<^bold>\<exists>x\<^bold>. \<psi>) \<and> language {(\<^bold>\<exists>x\<^bold>. \<phi>)} = language {(\<^bold>\<exists>x\<^bold>. \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>) \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<psi>)))
\<close>
sorry

lemma prenex_right_props_imp0:
  assumes \<open>qfree \<phi>\<close>
  shows \<open>is_prenex \<psi> \<Longrightarrow> is_prenex (prenex_right \<phi> \<psi>)\<close>
sorry

lemma prenex_right_props_imp:
  assumes \<open>qfree \<phi>\<close>
  shows \<open>is_prenex \<psi> \<Longrightarrow>
         is_prenex (prenex_right \<phi> \<psi>) \<and>
         FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
         language {prenex_right \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
         (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_right \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>))))\<close>
        (is \<open>is_prenex \<psi> \<Longrightarrow> ?P \<psi>\<close>)
sorry

lemma prenex_right_props:
  \<open>qfree \<phi> \<and> is_prenex \<psi> \<Longrightarrow>
  is_prenex (prenex_right \<phi> \<psi>) \<and>
  FV (prenex_right \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
  language {prenex_right \<phi> \<psi>} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)} \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> ((I\<^bold>,\<beta> \<Turnstile> (prenex_right \<phi> \<psi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> (\<phi> \<^bold>\<longrightarrow> \<psi>))))\<close>
sorry

lemma prenex_left_props_imp0:
  assumes \<open>is_prenex \<psi>\<close>
  shows \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (prenex_left \<phi> \<psi>)\<close>
sorry

lemma prenex_left_props_imp:
  assumes \<open>is_prenex \<psi>\<close>
  shows \<open>is_prenex \<phi> \<Longrightarrow>
        is_prenex (prenex_left \<phi> \<psi>) \<and>
        FV (prenex_left \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
        (language {(prenex_left \<phi> \<psi>)} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)}) \<and>
        (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> prenex_left \<phi> \<psi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
    (is \<open>is_prenex \<phi> \<Longrightarrow> ?P \<phi>\<close>)
sorry

lemma prenex_left_props:
  \<open>is_prenex \<phi> \<and> is_prenex \<psi> \<Longrightarrow>
        is_prenex (prenex_left \<phi> \<psi>) \<and>
        FV (prenex_left \<phi> \<psi>) = FV (\<phi> \<^bold>\<longrightarrow> \<psi>) \<and>
        (language {(prenex_left \<phi> \<psi>)} = language {(\<phi> \<^bold>\<longrightarrow> \<psi>)}) \<and>
        (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>,\<beta> \<Turnstile> prenex_left \<phi> \<psi> \<longleftrightarrow> I\<^bold>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
sorry

theorem prenex_props: \<open>is_prenex (prenex \<phi>) \<and> (FV (prenex \<phi>) = FV \<phi>) \<and>
  (language {prenex \<phi>} = language {\<phi>}) \<and>
  (\<forall>(I :: 'a intrp) \<beta>. dom I \<noteq> {} \<longrightarrow> (I\<^bold>, \<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I\<^bold>, \<beta> \<Turnstile> \<phi>))\<close>
sorry

corollary is_prenex_prenex [simp]: \<open>is_prenex (prenex \<phi>)\<close>
  and FV_prenex [simp]: \<open>FV (prenex \<phi>) = FV \<phi>\<close>
  and language_prenex [simp]: \<open>language {prenex \<phi>} = language {\<phi>}\<close>
sorry

corollary prenex_holds [simp]: \<open>dom I \<noteq> {} \<Longrightarrow> (I\<^bold>,\<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
sorry

lemma prenex_satisfies [simp]:
  assumes "dom M \<noteq> {}"
  shows "satisfies M {prenex \<phi>} \<longleftrightarrow> satisfies M {\<phi>}"
sorry

end
