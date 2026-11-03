(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory FOL_Syntax
  imports
    Main
    Propositional_Proof_Systems.Compactness
    First_Order_Terms.Term
    First_Order_Terms.Subterm_and_Context
begin

(* Comments starting with != indicate discrepancies with Harrison's formalisation *)

no_notation Not ("\<^bold>\<not>")
no_notation And (infix "\<^bold>\<and>" 68)
no_notation Or  (infix "\<^bold>\<or>" 68)

(* ---------------------------------------------------------------------------------------*)
(* To remove once the following have been integrated to the AFP in First_Order_Terms.Term *)
lemma count_terms: \<^marker>\<open>contributor \<open>Sophie Tourret\<close>\<close>
  "OFCLASS(('f::countable, 'v::countable) term,countable_class)"
sorry

instance "term" :: (countable, countable) countable
  \<^marker>\<open>contributor \<open>Sophie Tourret\<close>\<close>
  using count_terms by simp
(* ---------------------------------------------------------------------------------------*)

type_synonym nterm = \<open>(nat, nat) term\<close>

lemma count_nterms: "OFCLASS(nterm,countable_class)"
sorry

instance formula :: (countable) countable
  by countable_datatype

term "test (0, [Var 0])"

abbreviation functions_term :: \<open>nterm \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>functions_term t \<equiv> funas_term t\<close>

datatype form =
  Bot (\<open>\<^bold>\<bottom>\<close>)
| Atom (pred:nat) (args:\<open>nterm list\<close>)
| Implies form form (infixl \<open>\<^bold>\<longrightarrow>\<close> 85)
| Forall nat form (\<open>\<^bold>\<forall> _\<^bold>. _\<close> [0, 70] 70)

fun functions_form :: \<open>form \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>functions_form \<^bold>\<bottom> = {}\<close>
| \<open>functions_form (Atom p ts) = (\<Union> t \<in> set ts. functions_term t)\<close> 
| \<open>functions_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = functions_form \<phi> \<union> functions_form \<psi>\<close>
| \<open>functions_form (\<^bold>\<forall> x\<^bold>. \<phi>) = functions_form \<phi>\<close>

fun predicates_form :: \<open>form \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>predicates_form \<^bold>\<bottom> = {}\<close>
| \<open>predicates_form (Atom p ts) = {(p, length ts)}\<close>
| \<open>predicates_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = predicates_form \<phi> \<union> predicates_form \<psi>\<close>
| \<open>predicates_form (\<^bold>\<forall> x\<^bold>. \<phi>) = predicates_form \<phi>\<close>

definition functions_forms :: \<open>form set \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>functions_forms fms \<equiv> \<Union>f \<in> fms. functions_form f\<close>

definition predicates :: \<open>form set \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>predicates fms \<equiv> \<Union>f \<in> fms. predicates_form f\<close>

definition language :: \<open>form set \<Rightarrow> ((nat \<times> nat) set \<times> (nat \<times> nat) set)\<close> where
  \<open>language fms = (functions_forms fms, predicates fms)\<close>

lemma lang_singleton: \<open>language {p} = (functions_form p, predicates_form p)\<close>
sorry

abbreviation Not :: \<open>form \<Rightarrow> form\<close> (\<open>\<^bold>\<not> _\<close> [90] 90) where
  \<open>\<^bold>\<not> \<phi> \<equiv> \<phi> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Top :: \<open>form\<close> (\<open>\<^bold>\<top>\<close>) where
  \<open>\<^bold>\<top> \<equiv> \<^bold>\<not> \<^bold>\<bottom>\<close>

abbreviation Or :: \<open>form \<Rightarrow> form \<Rightarrow> form\<close>
  (infixl \<open>\<^bold>\<or>\<close> 84) where
  \<open>\<phi> \<^bold>\<or> \<psi> \<equiv> (\<phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> \<psi>\<close>

abbreviation And :: \<open>form \<Rightarrow> form \<Rightarrow> form\<close>
  (infixl \<open>\<^bold>\<and>\<close> 84) where
  \<open>\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not> (\<^bold>\<not> \<phi> \<^bold>\<or> \<^bold>\<not> \<psi>)\<close>

abbreviation Equiv :: \<open>form \<Rightarrow> form \<Rightarrow> form\<close>
  (infix \<open>\<^bold>\<longleftrightarrow>\<close> 70) where
  \<open>\<phi> \<^bold>\<longleftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<and> \<psi> \<^bold>\<longrightarrow> \<phi>)\<close> 

abbreviation Exists :: \<open>nat \<Rightarrow> form \<Rightarrow> form\<close>
  (\<open>\<^bold>\<exists> _\<^bold>. _\<close> [0, 70] 70) where
  \<open>\<^bold>\<exists> x\<^bold>. \<phi> \<equiv> \<^bold>\<not> (\<^bold>\<forall> x\<^bold>. \<^bold>\<not> \<phi>)\<close>

lemma ex_all_distinct: \<open>\<^bold>\<forall>x\<^bold>. \<phi> \<noteq> \<^bold>\<exists>y\<^bold>. \<psi>\<close>
sorry

abbreviation FVT :: \<open>nterm \<Rightarrow> nat set\<close> where
  \<open>FVT \<equiv> vars_term\<close>

fun FV :: \<open>form \<Rightarrow> nat set\<close> where
  \<open>FV \<^bold>\<bottom> = {}\<close>
| \<open>FV (Atom _ ts) = (\<Union> a \<in> set ts. FVT a)\<close>
| \<open>FV (\<phi> \<^bold>\<longrightarrow> \<psi>) = FV \<phi> \<union> FV \<psi>\<close>
| \<open>FV (\<^bold>\<forall> x\<^bold>. \<phi>) = FV \<phi> - {x}\<close>

lemma FV_all_subs: \<open>FV \<phi> \<subseteq> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<union> {x}\<close>
sorry

lemma FV_exists: \<open>FV (\<^bold>\<exists>x\<^bold>. \<phi>) = FV \<phi> - {x}\<close>
sorry

lemma finite_FV: \<open>finite (FV \<phi>)\<close>
sorry

fun BV :: \<open>form \<Rightarrow> nat set\<close> where
  \<open>BV \<^bold>\<bottom> = {}\<close>
| \<open>BV (Atom _ args') = {}\<close>
| \<open>BV (\<phi> \<^bold>\<longrightarrow> \<psi>) = BV \<phi> \<union> BV \<psi>\<close>
| \<open>BV (\<^bold>\<forall> x\<^bold>. \<phi>) = BV \<phi> \<union> {x}\<close>

lemma finite_BV: \<open>finite (BV \<phi>)\<close>
sorry

(* != substitutions over terms are defined in the Term theory *)

definition variant :: \<open>nat set \<Rightarrow> nat\<close> where
  \<open>variant s = Max s + 1\<close>

lemma variant_finite: \<open>finite s \<Longrightarrow> \<not> (variant s \<in> s)\<close>
sorry

lemma variant_form: \<open>\<not> variant (FV \<phi>) \<in> FV \<phi>\<close>
sorry

fun formsubst :: \<open>form \<Rightarrow> (nat, nat) subst \<Rightarrow> form\<close> (infixl \<open>\<cdot>\<^sub>f\<^sub>m\<close> 75) where
  \<open>\<^bold>\<bottom> \<cdot>\<^sub>f\<^sub>m _ = \<^bold>\<bottom>\<close> 
| \<open>(Atom p ts) \<cdot>\<^sub>f\<^sub>m \<sigma> = Atom p [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
| \<open>(\<phi> \<^bold>\<longrightarrow> \<psi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
| \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> =
    (let \<sigma>' = \<sigma>(x := Var x);
         z = if \<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)
             then variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')) else x in
    \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>

fun formsubst2 :: \<open>form \<Rightarrow> (nat, nat) subst \<Rightarrow> form\<close> (infixl \<open>\<cdot>\<^sub>f\<^sub>m2\<close> 75) where
  \<open>\<^bold>\<bottom> \<cdot>\<^sub>f\<^sub>m2 _ = \<^bold>\<bottom>\<close> 
| \<open>(Atom p ts) \<cdot>\<^sub>f\<^sub>m2 \<sigma> = Atom p [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
| \<open>(\<phi> \<^bold>\<longrightarrow> \<psi>) \<cdot>\<^sub>f\<^sub>m2 \<sigma> = (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>) \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>)\<close>
| \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m2 \<sigma> = (let \<sigma>' = \<sigma>(x := Var x) in
    (if \<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)
    then (let z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>')) in
      \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>(x := Var z)))
    else \<^bold>\<forall> x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>')))\<close>

lemma formsubst_def_switch: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>\<close>
sorry

lemma termsubst_valuation: \<open>\<forall>x\<in>FVT t. \<sigma> x = \<sigma>' x \<Longrightarrow> t \<cdot> \<sigma> = t \<cdot> \<sigma>'\<close>
sorry

lemma termsetsubst_valuation: \<open>\<forall>y \<in> T. \<forall>x\<in>FVT y. \<sigma> x = \<sigma>' x \<Longrightarrow> t \<in> T \<Longrightarrow> t \<cdot> \<sigma> = t \<cdot> \<sigma>'\<close>
sorry

lemma formsubst_valuation: \<open>\<forall>x\<in>(FV \<phi>). (Var x) \<cdot> \<sigma> = (Var x) \<cdot> \<sigma>' \<Longrightarrow> \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
sorry

(* != needed in HOL-Light but seems trivial in modern Isabelle/HOL *)
lemma \<open>{x. \<exists>y. y \<in> (s \<union> t) \<and> P x y} = {x. \<exists>y. y \<in> s \<and> P x y} \<union> {x. \<exists>y. y \<in> t \<and> P x y}\<close>
sorry

lemma formsubst_structure_bot: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<bottom> \<longleftrightarrow> \<phi> = \<^bold>\<bottom>\<close>
sorry

lemma formsubst_structure_pred: \<open>(\<exists>p ts. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = Atom p ts) \<longleftrightarrow> (\<exists>p ts. \<phi> = Atom p ts)\<close>
sorry

lemma formsubst_structure_imp: \<open>(\<exists>\<phi>1 \<phi>2. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<longleftrightarrow> (\<exists>\<psi>1 \<psi>2. \<phi> = \<psi>1 \<^bold>\<longrightarrow> \<psi>2)\<close>
sorry

lemma formsubst_structure_all: \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi>))\<close>
sorry

lemma formsubst_structure_not: \<open>(\<exists>\<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = Not \<psi>) \<longleftrightarrow> (\<exists>\<psi>. \<phi> = Not \<psi>)\<close>
sorry

lemma formsubst_structure_not_all_imp: 
  \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi>) \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi>) \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
sorry

lemma formsubst_structure_all_not: 
  \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>))\<close>
sorry

lemma formsubst_structure_ex: \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<exists>x\<^bold>. \<psi>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<exists>x\<^bold>. \<psi>))\<close>
sorry

lemma formsubst_structure: \<open>(\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<bottom> \<longleftrightarrow> \<phi> = \<^bold>\<bottom>) \<and> 
  ((\<exists>p ts. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = Atom p ts) \<longleftrightarrow> (\<exists>p ts. \<phi> = Atom p ts)) \<and>
  ((\<exists>\<phi>1 \<phi>2. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<longleftrightarrow> (\<exists>\<psi>1 \<psi>2. \<phi> = \<psi>1 \<^bold>\<longrightarrow> \<psi>2)) \<and> 
  ((\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi>)))\<close>
sorry

lemma formsubst_fv: \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = {x. \<exists>y. y \<in> (FV \<phi>) \<and> x \<in> FVT ((Var y) \<cdot> \<sigma>)}\<close>
sorry

lemma subst_var [simp]: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m Var = \<phi>\<close>
sorry

lemma formsubst_rename: \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) - {y} = FV \<phi> - {x} - {y}\<close>
sorry

lemma termsubst_functions_term:
  \<open>functions_term (t \<cdot> \<sigma>) = functions_term t \<union> {x. \<exists>y. y \<in> FVT t \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>)}\<close>
sorry

lemma formsubst_functions_form: 
  \<open>functions_form (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = functions_form \<phi> \<union> {x. \<exists>y. y \<in> FV \<phi> \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>)}\<close>
sorry

lemma formsubst_predicates: \<open>predicates_form (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = predicates_form \<phi>\<close>
sorry

lemma formsubst_language_rename: \<open>language {\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)} = language {\<phi>}\<close>
sorry

end
