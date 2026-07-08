(*  Author: John Harrison, Marco Maggesi, Graziano Gentili, Gianni Ciolli, Valentina Bruno
    Ported from "hol_light/Multivariate/canal.ml" by L C Paulson (2014)
*)

section \<open>Complex Analysis Basics\<close>
text \<open>Definitions of analytic and holomorphic functions, limit theorems, complex differentiation\<close>

theory Complex_Analysis_Basics
  imports Derivative "HOL-Library.Nonpos_Ints" Uncountable_Sets
begin

subsection\<^marker>\<open>tag unimportant\<close>\<open>General lemmas\<close>

lemma nonneg_Reals_cmod_eq_Re: "z \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> norm z = Re z"
  by sorry

lemma fact_cancel:
  fixes c :: "'a::real_field"
  shows "of_nat (Suc n) * c / (fact (Suc n)) = c / (fact n)"
  by sorry

lemma vector_derivative_cnj_within:
  assumes "at x within A \<noteq> bot" and "f differentiable at x within A"
  shows   "vector_derivative (\<lambda>z. cnj (f z)) (at x within A) = 
             cnj (vector_derivative f (at x within A))" (is "_ = cnj ?D")
  by sorry

lemma vector_derivative_cnj:
  assumes "f differentiable at x"
  shows   "vector_derivative (\<lambda>z. cnj (f z)) (at x) = cnj (vector_derivative f (at x))"
  by sorry

lemma
  shows open_halfspace_Re_lt: "open {z. Re(z) < b}"
    and open_halfspace_Re_gt: "open {z. Re(z) > b}"
    and closed_halfspace_Re_ge: "closed {z. Re(z) \<ge> b}"
    and closed_halfspace_Re_le: "closed {z. Re(z) \<le> b}"
    and closed_halfspace_Re_eq: "closed {z. Re(z) = b}"
    and open_halfspace_Im_lt: "open {z. Im(z) < b}"
    and open_halfspace_Im_gt: "open {z. Im(z) > b}"
    and closed_halfspace_Im_ge: "closed {z. Im(z) \<ge> b}"
    and closed_halfspace_Im_le: "closed {z. Im(z) \<le> b}"
    and closed_halfspace_Im_eq: "closed {z. Im(z) = b}"
  by sorry

lemma uncountable_halfspace_Im_gt: "uncountable {z. Im z > c}"
  by sorry

lemma uncountable_halfspace_Im_lt: "uncountable {z. Im z < c}"
  by sorry

lemma uncountable_halfspace_Re_gt: "uncountable {z. Re z > c}"
  by sorry

lemma uncountable_halfspace_Re_lt: "uncountable {z. Re z < c}"
  by sorry

lemma connected_halfspace_Im_gt [intro]: "connected {z. c < Im z}"
  by sorry

lemma connected_halfspace_Im_lt [intro]: "connected {z. c > Im z}"
  by sorry

lemma connected_halfspace_Re_gt [intro]: "connected {z. c < Re z}"
  by sorry

lemma connected_halfspace_Re_lt [intro]: "connected {z. c > Re z}"
  by sorry
  
lemma closed_complex_Reals: "closed (\<real> :: complex set)"
  by sorry

lemma closed_Real_halfspace_Re_le: "closed (\<real> \<inter> {w. Re w \<le> x})"
  by sorry

lemma closed_nonpos_Reals_complex [simp]: "closed (\<real>\<^sub>\<le>\<^sub>0 :: complex set)"
  by sorry

lemma closed_Real_halfspace_Re_ge: "closed (\<real> \<inter> {w. x \<le> Re(w)})"
  by sorry

lemma closed_nonneg_Reals_complex [simp]: "closed (\<real>\<^sub>\<ge>\<^sub>0 :: complex set)"
  by sorry

lemma closed_real_abs_le: "closed {w \<in> \<real>. \<bar>Re w\<bar> \<le> r}"
  by sorry

lemma real_lim:
  fixes l::complex
  assumes "(f \<longlongrightarrow> l) F" and "\<not> trivial_limit F" and "eventually P F" and "\<And>a. P a \<Longrightarrow> f a \<in> \<real>"
  shows  "l \<in> \<real>"
  by sorry

lemma real_lim_sequentially:
  fixes l::complex
  shows "(f \<longlongrightarrow> l) sequentially \<Longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
  by sorry

lemma real_series:
  fixes l::complex
  shows "f sums l \<Longrightarrow> (\<And>n. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
  by sorry

lemma Lim_null_comparison_Re:
  assumes "eventually (\<lambda>x. norm(f x) \<le> Re(g x)) F" "(g \<longlongrightarrow> 0) F" shows "(f \<longlongrightarrow> 0) F"
  by sorry

subsection\<open>Holomorphic functions\<close>

definition\<^marker>\<open>tag important\<close> holomorphic_on :: "[complex \<Rightarrow> complex, complex set] \<Rightarrow> bool"
           (infixl \<open>(holomorphic'_on)\<close> 50)
  where "f holomorphic_on s \<equiv> \<forall>x\<in>s. f field_differentiable (at x within s)"

named_theorems\<^marker>\<open>tag important\<close> holomorphic_intros "structural introduction rules for holomorphic_on"

lemma holomorphic_onI [intro?]: "(\<And>x. x \<in> s \<Longrightarrow> f field_differentiable (at x within s)) \<Longrightarrow> f holomorphic_on s"
  by sorry

lemma holomorphic_onD [dest?]: "\<lbrakk>f holomorphic_on s; x \<in> s\<rbrakk> \<Longrightarrow> f field_differentiable (at x within s)"
  by sorry

lemma holomorphic_on_imp_differentiable_on:
    "f holomorphic_on s \<Longrightarrow> f differentiable_on s"
  by sorry

lemma holomorphic_on_imp_differentiable_at:
   "\<lbrakk>f holomorphic_on s; open s; x \<in> s\<rbrakk> \<Longrightarrow> f field_differentiable (at x)"
  by sorry

lemma holomorphic_on_empty [holomorphic_intros]: "f holomorphic_on {}"
  by sorry

lemma holomorphic_on_open:
    "open s \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>f'. DERIV f x :> f')"
  by sorry

lemma holomorphic_on_UN_open:
  assumes "\<And>n. n \<in> I \<Longrightarrow> f holomorphic_on A n" "\<And>n. n \<in> I \<Longrightarrow> open (A n)"
  shows   "f holomorphic_on (\<Union>n\<in>I. A n)"
  by sorry

lemma holomorphic_on_imp_continuous_on:
    "f holomorphic_on s \<Longrightarrow> continuous_on s f"
  by sorry

lemma holomorphic_closedin_preimage_constant:
  assumes "f holomorphic_on D" 
  shows "closedin (top_of_set D) {z\<in>D. f z = a}"
  by sorry

lemma holomorphic_closed_preimage_constant:
  assumes "f holomorphic_on UNIV" 
  shows "closed {z. f z = a}"
  by sorry

lemma holomorphic_on_subset [elim]:
    "f holomorphic_on s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> f holomorphic_on t"
  by sorry

lemma holomorphic_transform: "\<lbrakk>f holomorphic_on s; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g holomorphic_on s"
  by sorry

lemma holomorphic_cong: "s = t ==> (\<And>x. x \<in> s \<Longrightarrow> f x = g x) \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> g holomorphic_on t"
  by sorry

lemma holomorphic_on_linear [simp, holomorphic_intros]: "((*) c) holomorphic_on s"
  by sorry

lemma holomorphic_on_const [simp, holomorphic_intros]: "(\<lambda>z. c) holomorphic_on s"
  by sorry

lemma holomorphic_on_ident [simp, holomorphic_intros]: "(\<lambda>x. x) holomorphic_on s"
  by sorry

lemma holomorphic_on_id [simp, holomorphic_intros]: "id holomorphic_on s"
  by sorry

lemma constant_on_imp_holomorphic_on:
  assumes "f constant_on A"
  shows   "f holomorphic_on A"
  by sorry

lemma holomorphic_on_compose:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on (f ` s) \<Longrightarrow> (g \<circ> f) holomorphic_on s"
  by sorry

lemma holomorphic_on_compose_gen:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on t \<Longrightarrow> f ` s \<subseteq> t \<Longrightarrow> (g \<circ> f) holomorphic_on s"
  by sorry

lemma holomorphic_on_balls_imp_entire:
  assumes "\<not>bdd_above A" "\<And>r. r \<in> A \<Longrightarrow> f holomorphic_on ball c r"
  shows   "f holomorphic_on B"
  by sorry

lemma holomorphic_on_balls_imp_entire':
  assumes "\<And>r. r > 0 \<Longrightarrow> f holomorphic_on ball c r"
  shows   "f holomorphic_on B"
  by sorry

lemma holomorphic_on_minus [holomorphic_intros]: "f holomorphic_on A \<Longrightarrow> (\<lambda>z. -(f z)) holomorphic_on A"
  by sorry

lemma holomorphic_on_add [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on A; g holomorphic_on A\<rbrakk> \<Longrightarrow> (\<lambda>z. f z + g z) holomorphic_on A"
  by sorry

lemma holomorphic_on_diff [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on A; g holomorphic_on A\<rbrakk> \<Longrightarrow> (\<lambda>z. f z - g z) holomorphic_on A"
  by sorry

lemma holomorphic_on_mult [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on A; g holomorphic_on A\<rbrakk> \<Longrightarrow> (\<lambda>z. f z * g z) holomorphic_on A"
  by sorry

lemma holomorphic_on_inverse [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on A; \<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. inverse (f z)) holomorphic_on A"
  by sorry

lemma holomorphic_on_divide [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on A; g holomorphic_on A; \<And>z. z \<in> A \<Longrightarrow> g z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. f z / g z) holomorphic_on A"
  by sorry

lemma holomorphic_on_power [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>z. (f z)^n) holomorphic_on A"
  by sorry

lemma holomorphic_on_power_int [holomorphic_intros]:
  assumes nz: "n \<ge> 0 \<or> (\<forall>x\<in>A. f x \<noteq> 0)" and f: "f holomorphic_on A"
  shows   "(\<lambda>x. f x powi n) holomorphic_on A"
  by sorry

lemma holomorphic_on_sum [holomorphic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) holomorphic_on A) \<Longrightarrow> (\<lambda>x. sum (\<lambda>i. f i x) I) holomorphic_on A"
  by sorry

lemma holomorphic_on_prod [holomorphic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) holomorphic_on A) \<Longrightarrow> (\<lambda>x. prod (\<lambda>i. f i x) I) holomorphic_on A"
  by sorry

lemma holomorphic_pochhammer [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>s. pochhammer (f s) n) holomorphic_on A"
  by sorry

lemma holomorphic_on_scaleR [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>x. c *\<^sub>R f x) holomorphic_on A"
  by sorry

lemma holomorphic_on_Un [holomorphic_intros]:
  assumes "f holomorphic_on A" "f holomorphic_on B" "open A" "open B"
  shows   "f holomorphic_on (A \<union> B)"
  by sorry

lemma holomorphic_on_If_Un [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on B" "open A" "open B"
  assumes "\<And>z. z \<in> A \<Longrightarrow> z \<in> B \<Longrightarrow> f z = g z"
  shows   "(\<lambda>z. if z \<in> A then f z else g z) holomorphic_on (A \<union> B)" (is "?h holomorphic_on _")
  by sorry

lemma holomorphic_derivI:
     "\<lbrakk>f holomorphic_on S; open S; x \<in> S\<rbrakk> \<Longrightarrow> (f has_field_derivative deriv f x) (at x within T)"
  by sorry

lemma complex_derivative_transform_within_open:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s; open s; z \<in> s; \<And>w. w \<in> s \<Longrightarrow> f w = g w\<rbrakk>
   \<Longrightarrow> deriv f z = deriv g z"
  by sorry

lemma holomorphic_on_compose_cnj_cnj:
  assumes "f holomorphic_on cnj ` A" "open A"
  shows   "cnj \<circ> f \<circ> cnj holomorphic_on A"
  by sorry
  
lemma holomorphic_nonconstant:
  assumes holf: "f holomorphic_on S" and "open S" "\<xi> \<in> S" "deriv f \<xi> \<noteq> 0"
    shows "\<not> f constant_on S"
  by sorry

subsection\<open>Analyticity on a set\<close>

definition\<^marker>\<open>tag important\<close> analytic_on (infixl \<open>(analytic'_on)\<close> 50)
  where "f analytic_on S \<equiv> \<forall>x \<in> S. \<exists>\<epsilon>. 0 < \<epsilon> \<and> f holomorphic_on (ball x \<epsilon>)"

named_theorems\<^marker>\<open>tag important\<close> analytic_intros "introduction rules for proving analyticity"

lemma analytic_imp_holomorphic: "f analytic_on S \<Longrightarrow> f holomorphic_on S"
  by sorry

lemma analytic_on_open: "open S \<Longrightarrow> f analytic_on S \<longleftrightarrow> f holomorphic_on S"
  by sorry

lemma constant_on_imp_analytic_on:
  assumes "f constant_on A" "open A"
  shows "f analytic_on A"
  by sorry

lemma analytic_on_imp_differentiable_at:
  "f analytic_on S \<Longrightarrow> x \<in> S \<Longrightarrow> f field_differentiable (at x)"
  by sorry

lemma analytic_at_imp_isCont:
  assumes "f analytic_on {z}"
  shows   "isCont f z"
  by sorry

lemma analytic_at_neq_imp_eventually_neq:
  assumes "f analytic_on {x}" "f x \<noteq> c"
  shows   "eventually (\<lambda>y. f y \<noteq> c) (at x)"
  by sorry

lemma analytic_on_subset: "f analytic_on S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> f analytic_on T"
  by sorry

lemma analytic_on_Un: "f analytic_on (S \<union> T) \<longleftrightarrow> f analytic_on S \<and> f analytic_on T"
  by sorry

lemma analytic_on_Union: "f analytic_on (\<Union>\<T>) \<longleftrightarrow> (\<forall>T \<in> \<T>. f analytic_on T)"
  by sorry

lemma analytic_on_UN: "f analytic_on (\<Union>i\<in>I. S i) \<longleftrightarrow> (\<forall>i\<in>I. f analytic_on (S i))"
  by sorry

lemma analytic_on_holomorphic:
  "f analytic_on S \<longleftrightarrow> (\<exists>T. open T \<and> S \<subseteq> T \<and> f holomorphic_on T)"
  (is "?lhs = ?rhs")
  by sorry

lemma analytic_on_linear [analytic_intros,simp]: "((*) c) analytic_on S"
  by sorry

lemma analytic_on_const [analytic_intros,simp]: "(\<lambda>z. c) analytic_on S"
  by sorry

lemma analytic_on_ident [analytic_intros,simp]: "(\<lambda>x. x) analytic_on S"
  by sorry

lemma analytic_on_id [analytic_intros]: "id analytic_on S"
  by sorry

lemma analytic_on_scaleR [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. x *\<^sub>R f w) analytic_on A"
  by sorry

lemma analytic_on_compose:
  assumes f: "f analytic_on S"
      and g: "g analytic_on (f ` S)"
    shows "(g \<circ> f) analytic_on S"
  by sorry

lemma analytic_on_compose_gen:
  "f analytic_on S \<Longrightarrow> g analytic_on T \<Longrightarrow> (\<And>z. z \<in> S \<Longrightarrow> f z \<in> T)
             \<Longrightarrow> g \<circ> f analytic_on S"
  by sorry

lemma analytic_on_neg [analytic_intros]:
  "f analytic_on S \<Longrightarrow> (\<lambda>z. -(f z)) analytic_on S"
  by sorry

lemma analytic_on_add [analytic_intros]:
  assumes f: "f analytic_on S"
      and g: "g analytic_on S"
    shows "(\<lambda>z. f z + g z) analytic_on S"
  by sorry

lemma analytic_on_mult [analytic_intros]:
  assumes f: "f analytic_on S"
      and g: "g analytic_on S"
    shows "(\<lambda>z. f z * g z) analytic_on S"
  by sorry

lemma analytic_on_diff [analytic_intros]:
  assumes f: "f analytic_on S" and g: "g analytic_on S"
  shows "(\<lambda>z. f z - g z) analytic_on S"
  by sorry

lemma analytic_on_inverse [analytic_intros]:
  assumes f: "f analytic_on S"
      and nz: "(\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0)"
    shows "(\<lambda>z. inverse (f z)) analytic_on S"
  by sorry

lemma analytic_on_divide [analytic_intros]:
  assumes f: "f analytic_on S" and g: "g analytic_on S"
    and nz: "(\<And>z. z \<in> S \<Longrightarrow> g z \<noteq> 0)"
  shows "(\<lambda>z. f z / g z) analytic_on S"
  by sorry

lemma analytic_on_power [analytic_intros]:
  "f analytic_on S \<Longrightarrow> (\<lambda>z. (f z) ^ n) analytic_on S"
  by sorry

lemma analytic_on_power_int [analytic_intros]:
  assumes nz: "n \<ge> 0 \<or> (\<forall>x\<in>A. f x \<noteq> 0)" and f: "f analytic_on A"
  shows   "(\<lambda>x. f x powi n) analytic_on A"
  by sorry

lemma analytic_on_sum [analytic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) analytic_on S) \<Longrightarrow> (\<lambda>x. sum (\<lambda>i. f i x) I) analytic_on S"
  by sorry

lemma analytic_on_prod [analytic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) analytic_on S) \<Longrightarrow> (\<lambda>x. prod (\<lambda>i. f i x) I) analytic_on S"
  by sorry

lemma analytic_on_gbinomial [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<lambda>w. f w gchoose n) analytic_on A"
  by sorry

lemma deriv_left_inverse:
  assumes "f holomorphic_on S" and "g holomorphic_on T"
      and "open S" and "open T"
      and "f ` S \<subseteq> T"
      and [simp]: "\<And>z. z \<in> S \<Longrightarrow> g (f z) = z"
      and "w \<in> S"
    shows "deriv f w * deriv g (f w) = 1"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Analyticity at a point\<close>

lemma analytic_at_ball:
  "f analytic_on {z} \<longleftrightarrow> (\<exists>e. 0<e \<and> f holomorphic_on ball z e)"
  by sorry

lemma analytic_at:
  "f analytic_on {z} \<longleftrightarrow> (\<exists>s. open s \<and> z \<in> s \<and> f holomorphic_on s)"
  by sorry

lemma holomorphic_on_imp_analytic_at:
  assumes "f holomorphic_on A" "open A" "z \<in> A"
  shows   "f analytic_on {z}"
  by sorry

lemma analytic_on_analytic_at:
  "f analytic_on s \<longleftrightarrow> (\<forall>z \<in> s. f analytic_on {z})"
  by sorry

lemma analytic_at_two:
  "f analytic_on {z} \<and> g analytic_on {z} \<longleftrightarrow>
   (\<exists>S. open S \<and> z \<in> S \<and> f holomorphic_on S \<and> g holomorphic_on S)"
  (is "?lhs = ?rhs")
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Combining theorems for derivative with ``analytic at'' hypotheses\<close>

lemma
  assumes "f analytic_on {z}" "g analytic_on {z}"
  shows complex_derivative_add_at: "deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
    and complex_derivative_diff_at: "deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
    and complex_derivative_mult_at: "deriv (\<lambda>w. f w * g w) z =
           f z * deriv g z + deriv f z * g z"
  by sorry

lemma deriv_cmult_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. c * f w) z = c * deriv f z"
  by sorry

lemma deriv_cmult_right_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. f w * c) z = deriv f z * c"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Complex differentiation of sequences and series\<close>

(* TODO: Could probably be simplified using Uniform_Limit *)
lemma has_complex_derivative_sequence:
  fixes S :: "complex set"
  assumes cvs: "convex S"
      and df:  "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x within S)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> S \<longrightarrow> norm (f' n x - g' x) \<le> e"
      and "\<exists>x l. x \<in> S \<and> ((\<lambda>n. f n x) \<longlongrightarrow> l) sequentially"
    shows "\<exists>g. \<forall>x \<in> S. ((\<lambda>n. f n x) \<longlongrightarrow> g x) sequentially \<and>
                       (g has_field_derivative (g' x)) (at x within S)"
  by sorry

lemma has_complex_derivative_series:
  fixes S :: "complex set"
  assumes cvs: "convex S"
      and df:  "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x within S)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> S
                \<longrightarrow> cmod ((\<Sum>i<n. f' i x) - g' x) \<le> e"
      and "\<exists>x l. x \<in> S \<and> ((\<lambda>n. f n x) sums l)"
    shows "\<exists>g. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((g has_field_derivative g' x) (at x within S))"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Taylor on Complex Numbers\<close>

lemma sum_Suc_reindex:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  shows "sum f {0..n} = f 0 - f (Suc n) + sum (\<lambda>i. f (Suc i)) {0..n}"
  by sorry

lemma field_Taylor:
  assumes S: "convex S"
      and f: "\<And>i x. x \<in> S \<Longrightarrow> i \<le> n \<Longrightarrow> (f i has_field_derivative f (Suc i) x) (at x within S)"
      and B: "\<And>x. x \<in> S \<Longrightarrow> norm (f (Suc n) x) \<le> B"
      and w: "w \<in> S"
      and z: "z \<in> S"
    shows "norm(f 0 z - (\<Sum>i\<le>n. f i w * (z-w) ^ i / (fact i)))
          \<le> B * norm(z - w)^(Suc n) / fact n"
  by sorry

lemma complex_Taylor:
  assumes S: "convex S"
      and f: "\<And>i x. x \<in> S \<Longrightarrow> i \<le> n \<Longrightarrow> (f i has_field_derivative f (Suc i) x) (at x within S)"
      and B: "\<And>x. x \<in> S \<Longrightarrow> cmod (f (Suc n) x) \<le> B"
      and w: "w \<in> S"
      and z: "z \<in> S"
    shows "cmod(f 0 z - (\<Sum>i\<le>n. f i w * (z-w) ^ i / (fact i))) \<le> B * cmod(z - w)^(Suc n) / fact n"
  by sorry


text\<open>Something more like the traditional MVT for real components\<close>

lemma complex_mvt_line:
  assumes "\<And>u. u \<in> closed_segment w z \<Longrightarrow> (f has_field_derivative f'(u)) (at u)"
    shows "\<exists>u. u \<in> closed_segment w z \<and> Re(f z) - Re(f w) = Re(f'(u) * (z - w))"
  by sorry

lemma complex_Taylor_mvt:
  assumes "\<And>i x. \<lbrakk>x \<in> closed_segment w z; i \<le> n\<rbrakk> \<Longrightarrow> ((f i) has_field_derivative f (Suc i) x) (at x)"
    shows "\<exists>u. u \<in> closed_segment w z \<and>
            Re (f 0 z) =
            Re ((\<Sum>i = 0..n. f i w * (z - w) ^ i / (fact i)) +
                (f (Suc n) u * (z-u)^n / (fact n)) * (z - w))"
  by sorry

end
