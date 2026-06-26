(*  Title:      HOL/Analysis/Derivative.thy
    Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (translation from HOL Light); tidied by LCP
*)

section \<open>Derivative\<close>

theory Derivative
  imports
    Bounded_Linear_Function
    Line_Segment
    Convex_Euclidean_Space
begin

declare bounded_linear_inner_left [intro]

declare has_derivative_bounded_linear[dest]

subsection \<open>Derivatives\<close>

lemma has_derivative_add_const:
  "(f has_derivative f') net \<Longrightarrow> ((\<lambda>x. f x + c) has_derivative f') net"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Derivative with composed bilinear function\<close>

text \<open>More explicit epsilon-delta forms.\<close>

proposition has_derivative_within':
  "(f has_derivative f')(at x within s) \<longleftrightarrow>
    bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. 0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
      norm (f x' - f x - f'(x' - x)) / norm (x' - x) < e)"
  by sorry

lemma has_derivative_at':
  "(f has_derivative f') (at x) 
   \<longleftrightarrow> bounded_linear f' \<and>
       (\<forall>e>0. \<exists>d>0. \<forall>x'. 0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
        norm (f x' - f x - f'(x' - x)) / norm (x' - x) < e)"
  by sorry

lemma has_derivative_componentwise_within:
   "(f has_derivative f') (at a within S) \<longleftrightarrow>
    (\<forall>i \<in> Basis. ((\<lambda>x. f x \<bullet> i) has_derivative (\<lambda>x. f' x \<bullet> i)) (at a within S))"
  by sorry

lemma has_derivative_at_withinI:
  "(f has_derivative f') (at x) \<Longrightarrow> (f has_derivative f') (at x within s)"
  by sorry

lemma has_derivative_right:
  fixes f :: "real \<Rightarrow> real"
    and y :: "real"
  shows "(f has_derivative ((*) y)) (at x within ({x <..} \<inter> I)) \<longleftrightarrow>
         ((\<lambda>t. (f x - f t) / (x - t)) \<longlongrightarrow> y) (at x within ({x <..} \<inter> I))"
  by sorry

subsubsection \<open>Caratheodory characterization\<close>

lemma DERIV_caratheodory_within:
  "(f has_field_derivative l) (at x within S) \<longleftrightarrow>
   (\<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> continuous (at x within S) g \<and> g x = l)"
      (is "?lhs = ?rhs")
  by sorry

subsection \<open>Differentiability\<close>

definition\<^marker>\<open>tag important\<close>
  differentiable_on :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
    (infix \<open>differentiable'_on\<close> 50)
  where "f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable (at x within s))"

lemma differentiableI: "(f has_derivative f') net \<Longrightarrow> f differentiable net"
  by sorry

lemma differentiable_onD: "\<lbrakk>f differentiable_on S; x \<in> S\<rbrakk> \<Longrightarrow> f differentiable (at x within S)"
  by sorry

lemma differentiable_at_withinI: "f differentiable (at x) \<Longrightarrow> f differentiable (at x within s)"
  by sorry

lemma differentiable_at_imp_differentiable_on:
  "(\<And>x. x \<in> s \<Longrightarrow> f differentiable at x) \<Longrightarrow> f differentiable_on s"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> differentiable_iff_scaleR:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "f differentiable F \<longleftrightarrow> (\<exists>d. (f has_derivative (\<lambda>x. x *\<^sub>R d)) F)"
  by sorry

lemma differentiable_on_eq_differentiable_at:
  "open s \<Longrightarrow> f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable at x)"
  by sorry

lemma differentiable_transform_within:
  assumes "f differentiable (at x within s)"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x'\<in>s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "g differentiable (at x within s)"
  by sorry

lemma differentiable_on_ident [simp, derivative_intros]: "(\<lambda>x. x) differentiable_on S"
  by sorry

lemma differentiable_on_id [simp, derivative_intros]: "id differentiable_on S"
  by sorry

lemma differentiable_on_const [simp, derivative_intros]: "(\<lambda>z. c) differentiable_on S"
  by sorry

lemma differentiable_on_mult [simp, derivative_intros]:
  fixes f :: "'M::real_normed_vector \<Rightarrow> 'a::real_normed_algebra"
  shows "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z * g z) differentiable_on S"
  by sorry

lemma differentiable_on_compose:
   "\<lbrakk>g differentiable_on S; f differentiable_on (g ` S)\<rbrakk> \<Longrightarrow> (\<lambda>x. f (g x)) differentiable_on S"
  by sorry

lemma bounded_linear_imp_differentiable_on: "bounded_linear f \<Longrightarrow> f differentiable_on S"
  by sorry

lemma linear_imp_differentiable_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> f differentiable_on S"
  by sorry

lemma differentiable_on_minus [simp, derivative_intros]:
  "f differentiable_on S \<Longrightarrow> (\<lambda>z. -(f z)) differentiable_on S"
  by sorry

lemma differentiable_on_add [simp, derivative_intros]:
  "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z + g z) differentiable_on S"
  by sorry

lemma differentiable_on_diff [simp, derivative_intros]:
  "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z - g z) differentiable_on S"
  by sorry

lemma differentiable_on_inverse [simp, derivative_intros]:
  fixes f :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_field"
  shows "f differentiable_on S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow> (\<lambda>x. inverse (f x)) differentiable_on S"
  by sorry

lemma differentiable_on_scaleR [derivative_intros, simp]:
  "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>x. f x *\<^sub>R g x) differentiable_on S"
  by sorry

lemma has_derivative_sqnorm_at [derivative_intros, simp]:
  "((\<lambda>x. (norm x)\<^sup>2) has_derivative (\<lambda>x. 2 *\<^sub>R (a \<bullet> x))) (at a)"
  by sorry

lemma differentiable_sqnorm_at [derivative_intros, simp]:
  fixes a :: "'a :: {real_normed_vector,real_inner}"
  shows "(\<lambda>x. (norm x)\<^sup>2) differentiable (at a)"
  by sorry

lemma differentiable_on_sqnorm [derivative_intros, simp]:
  fixes S :: "'a :: {real_normed_vector,real_inner} set"
  shows "(\<lambda>x. (norm x)\<^sup>2) differentiable_on S"
  by sorry

lemma differentiable_norm_at [derivative_intros, simp]:
  fixes a :: "'a :: {real_normed_vector,real_inner}"
  shows "a \<noteq> 0 \<Longrightarrow> norm differentiable (at a)"
  by sorry

lemma differentiable_on_norm [derivative_intros, simp]:
  fixes S :: "'a :: {real_normed_vector,real_inner} set"
  shows "0 \<notin> S \<Longrightarrow> norm differentiable_on S"
  by sorry


subsection \<open>Frechet derivative and Jacobian matrix\<close>

definition "frechet_derivative f net = (SOME f'. (f has_derivative f') net)"

proposition frechet_derivative_works:
  "f differentiable net \<longleftrightarrow> (f has_derivative (frechet_derivative f net)) net"
  by sorry

lemma linear_frechet_derivative: "f differentiable net \<Longrightarrow> linear (frechet_derivative f net)"
  by sorry

lemma frechet_derivative_const [simp]: "frechet_derivative (\<lambda>x. c) (at a) = (\<lambda>x. 0)"
  by sorry

lemma frechet_derivative_id [simp]: "frechet_derivative id (at a) = id"
  by sorry

lemma frechet_derivative_ident [simp]: "frechet_derivative (\<lambda>x. x) (at a) = (\<lambda>x. x)"
  by sorry


subsection \<open>Differentiability implies continuity\<close>

proposition differentiable_imp_continuous_within:
  "f differentiable (at x within s) \<Longrightarrow> continuous (at x within s) f"
  by sorry

lemma differentiable_imp_continuous_on:
  "f differentiable_on s \<Longrightarrow> continuous_on s f"
  by sorry

lemma differentiable_on_subset:
  "f differentiable_on t \<Longrightarrow> s \<subseteq> t \<Longrightarrow> f differentiable_on s"
  by sorry

lemma differentiable_on_empty: "f differentiable_on {}"
  by sorry

lemma has_derivative_continuous_on:
  "(\<And>x. x \<in> s \<Longrightarrow> (f has_derivative f' x) (at x within s)) \<Longrightarrow> continuous_on s f"
  by sorry

text \<open>Results about neighborhoods filter.\<close>

lemma eventually_nhds_metric_le:
  "eventually P (nhds a) = (\<exists>d>0. \<forall>x. dist x a \<le> d \<longrightarrow> P x)"
  by sorry

lemma le_nhds: "F \<le> nhds a \<longleftrightarrow> (\<forall>S. open S \<and> a \<in> S \<longrightarrow> eventually (\<lambda>x. x \<in> S) F)"
  by sorry

lemma le_nhds_metric: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a < e) F)"
  by sorry

lemma le_nhds_metric_le: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a \<le> e) F)"
  by sorry

text \<open>Several results are easier using a "multiplied-out" variant.
(I got this idea from Dieudonne's proof of the chain rule).\<close>

lemma has_derivative_within_alt:
  "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y\<in>s. norm(y - x) < d \<longrightarrow> norm (f y - f x - f' (y - x)) \<le> e * norm (y - x))"
  by sorry

lemma has_derivative_within_alt2:
  "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. eventually (\<lambda>y. norm (f y - f x - f' (y - x)) \<le> e * norm (y - x)) (at x within s))"
  by sorry

lemma has_derivative_at_alt:
  "(f has_derivative f') (at x) \<longleftrightarrow>
    bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y. norm(y - x) < d \<longrightarrow> norm (f y - f x - f'(y - x)) \<le> e * norm (y - x))"
  by sorry


subsection \<open>The chain rule\<close>

proposition diff_chain_within[derivative_intros]:
  assumes "(f has_derivative f') (at x within s)"
    and "(g has_derivative g') (at (f x) within (f ` s))"
  shows "((g \<circ> f) has_derivative (g' \<circ> f'))(at x within s)"
  by sorry

lemma diff_chain_at[derivative_intros]:
  "(f has_derivative f') (at x) \<Longrightarrow>
    (g has_derivative g') (at (f x)) \<Longrightarrow> ((g \<circ> f) has_derivative (g' \<circ> f')) (at x)"
  by sorry

lemma has_vector_derivative_shift: "(f has_vector_derivative D x) (at x)
           \<Longrightarrow> ((+) d \<circ> f has_vector_derivative D x) (at x)"
  by sorry
  
lemma has_vector_derivative_within_open:
  "a \<in> S \<Longrightarrow> open S \<Longrightarrow>
    (f has_vector_derivative f') (at a within S) \<longleftrightarrow> (f has_vector_derivative f') (at a)"
  by sorry

lemma field_vector_diff_chain_within:
 assumes Df: "(f has_vector_derivative f') (at x within S)"
     and Dg: "(g has_field_derivative g') (at (f x) within f ` S)"
 shows "((g \<circ> f) has_vector_derivative (f' * g')) (at x within S)"
  by sorry

lemma vector_derivative_diff_chain_within:
  assumes Df: "(f has_vector_derivative f') (at x within S)"
     and Dg: "(g has_derivative g') (at (f x) within f`S)"
  shows "((g \<circ> f) has_vector_derivative (g' f')) (at x within S)"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Composition rules stated just for differentiability\<close>

lemma differentiable_chain_at:
  "f differentiable (at x) \<Longrightarrow>
    g differentiable (at (f x)) \<Longrightarrow> (g \<circ> f) differentiable (at x)"
  by sorry

lemma differentiable_chain_within:
  "f differentiable (at x within S) \<Longrightarrow>
    g differentiable (at(f x) within (f ` S)) \<Longrightarrow> (g \<circ> f) differentiable (at x within S)"
  by sorry


subsection \<open>Uniqueness of derivative\<close>


text\<^marker>\<open>tag important\<close> \<open>
 The general result is a bit messy because we need approachability of the
 limit point from any direction. But OK for nontrivial intervals etc.
\<close>

proposition frechet_derivative_unique_within:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes 1: "(f has_derivative f') (at x within S)"
    and 2: "(f has_derivative f'') (at x within S)"
    and S: "\<And>i e. \<lbrakk>i\<in>Basis; e>0\<rbrakk> \<Longrightarrow> \<exists>d. 0 < \<bar>d\<bar> \<and> \<bar>d\<bar> < e \<and> (x + d *\<^sub>R i) \<in> S"
  shows "f' = f''"
  by sorry
