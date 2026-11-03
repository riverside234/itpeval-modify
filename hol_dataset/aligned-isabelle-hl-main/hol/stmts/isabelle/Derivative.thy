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
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Derivative with composed bilinear function\<close>

text \<open>More explicit epsilon-delta forms.\<close>

proposition has_derivative_within':
  "(f has_derivative f')(at x within s) \<longleftrightarrow>
    bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. 0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
      norm (f x' - f x - f'(x' - x)) / norm (x' - x) < e)"
sorry

lemma has_derivative_at':
  "(f has_derivative f') (at x) 
   \<longleftrightarrow> bounded_linear f' \<and>
       (\<forall>e>0. \<exists>d>0. \<forall>x'. 0 < norm (x' - x) \<and> norm (x' - x) < d \<longrightarrow>
        norm (f x' - f x - f'(x' - x)) / norm (x' - x) < e)"
sorry

lemma has_derivative_componentwise_within:
   "(f has_derivative f') (at a within S) \<longleftrightarrow>
    (\<forall>i \<in> Basis. ((\<lambda>x. f x \<bullet> i) has_derivative (\<lambda>x. f' x \<bullet> i)) (at a within S))"
sorry

lemma has_derivative_at_withinI:
  "(f has_derivative f') (at x) \<Longrightarrow> (f has_derivative f') (at x within s)"
sorry

lemma has_derivative_right:
  fixes f :: "real \<Rightarrow> real"
    and y :: "real"
  shows "(f has_derivative ((*) y)) (at x within ({x <..} \<inter> I)) \<longleftrightarrow>
         ((\<lambda>t. (f x - f t) / (x - t)) \<longlongrightarrow> y) (at x within ({x <..} \<inter> I))"
sorry

subsubsection \<open>Caratheodory characterization\<close>

lemma DERIV_caratheodory_within:
  "(f has_field_derivative l) (at x within S) \<longleftrightarrow>
   (\<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> continuous (at x within S) g \<and> g x = l)"
      (is "?lhs = ?rhs")
sorry

subsection \<open>Differentiability\<close>

definition\<^marker>\<open>tag important\<close>
  differentiable_on :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
    (infix \<open>differentiable'_on\<close> 50)
  where "f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable (at x within s))"

lemma differentiableI: "(f has_derivative f') net \<Longrightarrow> f differentiable net"
sorry

lemma differentiable_onD: "\<lbrakk>f differentiable_on S; x \<in> S\<rbrakk> \<Longrightarrow> f differentiable (at x within S)"
sorry

lemma differentiable_at_withinI: "f differentiable (at x) \<Longrightarrow> f differentiable (at x within s)"
sorry

lemma differentiable_at_imp_differentiable_on:
  "(\<And>x. x \<in> s \<Longrightarrow> f differentiable at x) \<Longrightarrow> f differentiable_on s"
sorry

corollary\<^marker>\<open>tag unimportant\<close> differentiable_iff_scaleR:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "f differentiable F \<longleftrightarrow> (\<exists>d. (f has_derivative (\<lambda>x. x *\<^sub>R d)) F)"
sorry

lemma differentiable_on_eq_differentiable_at:
  "open s \<Longrightarrow> f differentiable_on s \<longleftrightarrow> (\<forall>x\<in>s. f differentiable at x)"
sorry

lemma differentiable_transform_within:
  assumes "f differentiable (at x within s)"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x'\<in>s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "g differentiable (at x within s)"
sorry

lemma differentiable_on_ident [simp, derivative_intros]: "(\<lambda>x. x) differentiable_on S"
sorry

lemma differentiable_on_id [simp, derivative_intros]: "id differentiable_on S"
sorry

lemma differentiable_on_const [simp, derivative_intros]: "(\<lambda>z. c) differentiable_on S"
sorry

lemma differentiable_on_mult [simp, derivative_intros]:
  fixes f :: "'M::real_normed_vector \<Rightarrow> 'a::real_normed_algebra"
  shows "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z * g z) differentiable_on S"
sorry

lemma differentiable_on_compose:
   "\<lbrakk>g differentiable_on S; f differentiable_on (g ` S)\<rbrakk> \<Longrightarrow> (\<lambda>x. f (g x)) differentiable_on S"
sorry

lemma bounded_linear_imp_differentiable_on: "bounded_linear f \<Longrightarrow> f differentiable_on S"
sorry

lemma linear_imp_differentiable_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> f differentiable_on S"
sorry

lemma differentiable_on_minus [simp, derivative_intros]:
  "f differentiable_on S \<Longrightarrow> (\<lambda>z. -(f z)) differentiable_on S"
sorry

lemma differentiable_on_add [simp, derivative_intros]:
  "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z + g z) differentiable_on S"
sorry

lemma differentiable_on_diff [simp, derivative_intros]:
  "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>z. f z - g z) differentiable_on S"
sorry

lemma differentiable_on_inverse [simp, derivative_intros]:
  fixes f :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_field"
  shows "f differentiable_on S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow> (\<lambda>x. inverse (f x)) differentiable_on S"
sorry

lemma differentiable_on_scaleR [derivative_intros, simp]:
  "\<lbrakk>f differentiable_on S; g differentiable_on S\<rbrakk> \<Longrightarrow> (\<lambda>x. f x *\<^sub>R g x) differentiable_on S"
sorry

lemma has_derivative_sqnorm_at [derivative_intros, simp]:
  "((\<lambda>x. (norm x)\<^sup>2) has_derivative (\<lambda>x. 2 *\<^sub>R (a \<bullet> x))) (at a)"
sorry

lemma differentiable_sqnorm_at [derivative_intros, simp]:
  fixes a :: "'a :: {real_normed_vector,real_inner}"
  shows "(\<lambda>x. (norm x)\<^sup>2) differentiable (at a)"
sorry

lemma differentiable_on_sqnorm [derivative_intros, simp]:
  fixes S :: "'a :: {real_normed_vector,real_inner} set"
  shows "(\<lambda>x. (norm x)\<^sup>2) differentiable_on S"
sorry

lemma differentiable_norm_at [derivative_intros, simp]:
  fixes a :: "'a :: {real_normed_vector,real_inner}"
  shows "a \<noteq> 0 \<Longrightarrow> norm differentiable (at a)"
sorry

lemma differentiable_on_norm [derivative_intros, simp]:
  fixes S :: "'a :: {real_normed_vector,real_inner} set"
  shows "0 \<notin> S \<Longrightarrow> norm differentiable_on S"
sorry

subsection \<open>Frechet derivative and Jacobian matrix\<close>

definition "frechet_derivative f net = (SOME f'. (f has_derivative f') net)"

proposition frechet_derivative_works:
  "f differentiable net \<longleftrightarrow> (f has_derivative (frechet_derivative f net)) net"
sorry

lemma linear_frechet_derivative: "f differentiable net \<Longrightarrow> linear (frechet_derivative f net)"
sorry

lemma frechet_derivative_const [simp]: "frechet_derivative (\<lambda>x. c) (at a) = (\<lambda>x. 0)"
sorry

lemma frechet_derivative_id [simp]: "frechet_derivative id (at a) = id"
sorry

lemma frechet_derivative_ident [simp]: "frechet_derivative (\<lambda>x. x) (at a) = (\<lambda>x. x)"
sorry

subsection \<open>Differentiability implies continuity\<close>

proposition differentiable_imp_continuous_within:
  "f differentiable (at x within s) \<Longrightarrow> continuous (at x within s) f"
sorry

lemma differentiable_imp_continuous_on:
  "f differentiable_on s \<Longrightarrow> continuous_on s f"
sorry

lemma differentiable_on_subset:
  "f differentiable_on t \<Longrightarrow> s \<subseteq> t \<Longrightarrow> f differentiable_on s"
sorry

lemma differentiable_on_empty: "f differentiable_on {}"
sorry

lemma has_derivative_continuous_on:
  "(\<And>x. x \<in> s \<Longrightarrow> (f has_derivative f' x) (at x within s)) \<Longrightarrow> continuous_on s f"
sorry

text \<open>Results about neighborhoods filter.\<close>

lemma eventually_nhds_metric_le:
  "eventually P (nhds a) = (\<exists>d>0. \<forall>x. dist x a \<le> d \<longrightarrow> P x)"
sorry

lemma le_nhds: "F \<le> nhds a \<longleftrightarrow> (\<forall>S. open S \<and> a \<in> S \<longrightarrow> eventually (\<lambda>x. x \<in> S) F)"
sorry

lemma le_nhds_metric: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a < e) F)"
sorry

lemma le_nhds_metric_le: "F \<le> nhds a \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist x a \<le> e) F)"
sorry

text \<open>Several results are easier using a "multiplied-out" variant.
(I got this idea from Dieudonne's proof of the chain rule).\<close>

lemma has_derivative_within_alt:
  "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y\<in>s. norm(y - x) < d \<longrightarrow> norm (f y - f x - f' (y - x)) \<le> e * norm (y - x))"
sorry

lemma has_derivative_within_alt2:
  "(f has_derivative f') (at x within s) \<longleftrightarrow> bounded_linear f' \<and>
    (\<forall>e>0. eventually (\<lambda>y. norm (f y - f x - f' (y - x)) \<le> e * norm (y - x)) (at x within s))"
sorry

lemma has_derivative_at_alt:
  "(f has_derivative f') (at x) \<longleftrightarrow>
    bounded_linear f' \<and>
    (\<forall>e>0. \<exists>d>0. \<forall>y. norm(y - x) < d \<longrightarrow> norm (f y - f x - f'(y - x)) \<le> e * norm (y - x))"
sorry

subsection \<open>The chain rule\<close>

proposition diff_chain_within[derivative_intros]:
  assumes "(f has_derivative f') (at x within s)"
    and "(g has_derivative g') (at (f x) within (f ` s))"
  shows "((g \<circ> f) has_derivative (g' \<circ> f'))(at x within s)"
sorry

lemma diff_chain_at[derivative_intros]:
  "(f has_derivative f') (at x) \<Longrightarrow>
    (g has_derivative g') (at (f x)) \<Longrightarrow> ((g \<circ> f) has_derivative (g' \<circ> f')) (at x)"
sorry

lemma has_vector_derivative_shift: "(f has_vector_derivative D x) (at x)
           \<Longrightarrow> ((+) d \<circ> f has_vector_derivative D x) (at x)"
sorry

lemma has_vector_derivative_within_open:
  "a \<in> S \<Longrightarrow> open S \<Longrightarrow>
    (f has_vector_derivative f') (at a within S) \<longleftrightarrow> (f has_vector_derivative f') (at a)"
sorry

lemma field_vector_diff_chain_within:
 assumes Df: "(f has_vector_derivative f') (at x within S)"
     and Dg: "(g has_field_derivative g') (at (f x) within f ` S)"
 shows "((g \<circ> f) has_vector_derivative (f' * g')) (at x within S)"
sorry

lemma vector_derivative_diff_chain_within:
  assumes Df: "(f has_vector_derivative f') (at x within S)"
     and Dg: "(g has_derivative g') (at (f x) within f`S)"
  shows "((g \<circ> f) has_vector_derivative (g' f')) (at x within S)"
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Composition rules stated just for differentiability\<close>

lemma differentiable_chain_at:
  "f differentiable (at x) \<Longrightarrow>
    g differentiable (at (f x)) \<Longrightarrow> (g \<circ> f) differentiable (at x)"
sorry

lemma differentiable_chain_within:
  "f differentiable (at x within S) \<Longrightarrow>
    g differentiable (at(f x) within (f ` S)) \<Longrightarrow> (g \<circ> f) differentiable (at x within S)"
sorry
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
sorry

proposition frechet_derivative_unique_within_closed_interval:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes ab: "\<And>i. i\<in>Basis \<Longrightarrow> a\<bullet>i < b\<bullet>i"
    and x: "x \<in> cbox a b"
    and "(f has_derivative f' ) (at x within cbox a b)"
    and "(f has_derivative f'') (at x within cbox a b)"
  shows "f' = f''"
sorry

lemma frechet_derivative_unique_within_open_interval:
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes x: "x \<in> box a b"
    and f: "(f has_derivative f' ) (at x within box a b)" "(f has_derivative f'') (at x within box a b)"
  shows "f' = f''"
sorry

lemma frechet_derivative_at:
  "(f has_derivative f') (at x) \<Longrightarrow> f' = frechet_derivative f (at x)"
sorry

lemma frechet_derivative_compose:
  "frechet_derivative (f o g) (at x) = frechet_derivative (f) (at (g x)) o frechet_derivative g (at x)"
  if "g differentiable at x" "f differentiable at (g x)"
sorry

lemma frechet_derivative_within_cbox:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>i. i\<in>Basis \<Longrightarrow> a\<bullet>i < b\<bullet>i"
    and "x \<in> cbox a b"
    and "(f has_derivative f') (at x within cbox a b)"
  shows "frechet_derivative f (at x within cbox a b) = f'"
sorry

lemma frechet_derivative_transform_within_open:
  "frechet_derivative f (at x) = frechet_derivative g (at x)"
  if "f differentiable at x" "open X" "x \<in> X" "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
sorry

subsection \<open>Derivatives of local minima and maxima are zero\<close>

lemma has_derivative_local_min:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes deriv: "(f has_derivative f') (at x)"
  assumes min: "eventually (\<lambda>y. f x \<le> f y) (at x)"
  shows "f' = (\<lambda>h. 0)"
sorry

lemma has_derivative_local_max:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "(f has_derivative f') (at x)"
  assumes "eventually (\<lambda>y. f y \<le> f x) (at x)"
  shows "f' = (\<lambda>h. 0)"
sorry

lemma differential_zero_maxmin:
  fixes f::"'a::real_normed_vector \<Rightarrow> real"
  assumes "x \<in> S"
    and "open S"
    and deriv: "(f has_derivative f') (at x)"
    and mono: "(\<forall>y\<in>S. f y \<le> f x) \<or> (\<forall>y\<in>S. f x \<le> f y)"
  shows "f' = (\<lambda>v. 0)"
sorry

lemma differential_zero_maxmin_component:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k \<in> Basis"
    and ball: "0 < e" "(\<forall>y \<in> ball x e. (f y)\<bullet>k \<le> (f x)\<bullet>k) \<or> (\<forall>y\<in>ball x e. (f x)\<bullet>k \<le> (f y)\<bullet>k)"
    and diff: "f differentiable (at x)"
  shows "(\<Sum>j\<in>Basis. (frechet_derivative f (at x) j \<bullet> k) *\<^sub>R j) = (0::'a)" (is "?D k = 0")
sorry

subsection \<open>One-dimensional mean value theorem\<close>

lemma mvt_simple:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
    and derf: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> (f has_derivative f' x) (at x within {a..b})"
  shows "\<exists>x\<in>{a<..<b}. f b - f a = f' x (b - a)"
sorry

lemma mvt_very_simple:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and derf: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> (f has_derivative f' x) (at x within {a..b})"
  shows "\<exists>x\<in>{a..b}. f b - f a = f' x (b - a)"
sorry

text \<open>A nice generalization (see Havin's proof of 5.19 from Rudin's book).\<close>

lemma mvt_general:
  fixes f :: "real \<Rightarrow> 'a::real_inner"
  assumes "a < b"
    and contf: "continuous_on {a..b} f"
    and derf: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> (f has_derivative f' x) (at x)"
  shows "\<exists>x\<in>{a<..<b}. norm (f b - f a) \<le> norm (f' x (b - a))"
sorry


subsection \<open>More general bound theorems\<close>

proposition differentiable_bound_general:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a < b"
    and f_cont: "continuous_on {a..b} f"
    and phi_cont: "continuous_on {a..b} \<phi>"
    and f': "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
    and phi': "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (\<phi> has_vector_derivative \<phi>' x) (at x)"
    and bnd: "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> norm (f' x) \<le> \<phi>' x"
  shows "norm (f b - f a) \<le> \<phi> b - \<phi> a"
sorry

lemma differentiable_bound:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex S"
    and derf: "\<And>x. x\<in>S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and B: "\<And>x. x \<in> S \<Longrightarrow> onorm (f' x) \<le> B"
    and x: "x \<in> S"
    and y: "y \<in> S"
  shows "norm (f x - f y) \<le> B * norm (x - y)"
sorry

lemma field_differentiable_bound:
  fixes S :: "'a::real_normed_field set"
  assumes cvs: "convex S"
      and df:  "\<And>z. z \<in> S \<Longrightarrow> (f has_field_derivative f' z) (at z within S)"
      and dn:  "\<And>z. z \<in> S \<Longrightarrow> norm (f' z) \<le> B"
      and "x \<in> S"  "y \<in> S"
    shows "norm(f x - f y) \<le> B * norm(x - y)"
sorry

lemma
  differentiable_bound_segment:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>t. t \<in> {0..1} \<Longrightarrow> x0 + t *\<^sub>R a \<in> G"
  assumes f': "\<And>x. x \<in> G \<Longrightarrow> (f has_derivative f' x) (at x within G)"
  assumes B: "\<And>x. x \<in> {0..1} \<Longrightarrow> onorm (f' (x0 + x *\<^sub>R a)) \<le> B"
  shows "norm (f (x0 + a) - f x0) \<le> norm a * B"
sorry

lemma differentiable_bound_linearization:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes S: "\<And>t. t \<in> {0..1} \<Longrightarrow> a + t *\<^sub>R (b - a) \<in> S"
  assumes f'[derivative_intros]: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes B: "\<And>x. x \<in> S \<Longrightarrow> onorm (f' x - f' x0) \<le> B"
  assumes "x0 \<in> S"
  shows "norm (f b - f a - f' x0 (b - a)) \<le> norm (b - a) * B"
sorry

lemma vector_differentiable_bound_linearization:
  fixes f::"real \<Rightarrow> 'b::real_normed_vector"
  assumes f': "\<And>x. x \<in> S \<Longrightarrow> (f has_vector_derivative f' x) (at x within S)"
  assumes "closed_segment a b \<subseteq> S"
  assumes B: "\<And>x. x \<in> S \<Longrightarrow> norm (f' x - f' x0) \<le> B"
  assumes "x0 \<in> S"
  shows "norm (f b - f a - (b - a) *\<^sub>R f' x0) \<le> norm (b - a) * B"
sorry

text \<open>In particular.\<close>

lemma has_derivative_zero_constant:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex s"
    and "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within s)"
  shows "\<exists>c. \<forall>x\<in>s. f x = c"
sorry

lemma has_field_derivative_zero_constant:
  assumes "convex s" "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative 0) (at x within s)"
  shows   "\<exists>c. \<forall>x\<in>s. f (x) = (c :: 'a :: real_normed_field)"
sorry

lemma
  has_vector_derivative_zero_constant:
  assumes "convex s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_vector_derivative 0) (at x within s)"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
sorry

lemma has_derivative_zero_unique:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex s"
    and "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within s)"
    and "x \<in> s" "y \<in> s"
  shows "f x = f y"
sorry

lemma has_derivative_zero_unique_connected:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "open s" "connected s"
  assumes f: "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative (\<lambda>x. 0)) (at x)"
  assumes "x \<in> s" "y \<in> s"
  shows "f x = f y"
sorry

subsection \<open>Differentiability of inverse function (most basic form)\<close>

lemma has_derivative_inverse_basic:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes derf: "(f has_derivative f') (at (g y))"
    and ling': "bounded_linear g'"
    and "g' \<circ> f' = id"
    and contg: "continuous (at y) g"
    and "open T"
    and "y \<in> T"
    and fg: "\<And>z. z \<in> T \<Longrightarrow> f (g z) = z"
  shows "(g has_derivative g') (at y)"
sorry

text\<^marker>\<open>tag unimportant\<close>\<open>Inverse function theorem for complex derivatives\<close>
lemma has_field_derivative_inverse_basic:
  shows "DERIV f (g y) :> f' \<Longrightarrow>
        f' \<noteq> 0 \<Longrightarrow>
        continuous (at y) g \<Longrightarrow>
        open t \<Longrightarrow>
        y \<in> t \<Longrightarrow>
        (\<And>z. z \<in> t \<Longrightarrow> f (g z) = z)
        \<Longrightarrow> DERIV g y :> inverse (f')"
sorry

text \<open>Simply rewrite that based on the domain point x.\<close>

lemma has_derivative_inverse_basic_x:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_derivative f') (at x)"
    and "bounded_linear g'"
    and "g' \<circ> f' = id"
    and "continuous (at (f x)) g"
    and "g (f x) = x"
    and "open T"
    and "f x \<in> T"
    and "\<And>y. y \<in> T \<Longrightarrow> f (g y) = y"
  shows "(g has_derivative g') (at (f x))"
sorry

text \<open>This is the version in Dieudonne', assuming continuity of f and g.\<close>

lemma has_derivative_inverse_dieudonne:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "open S"
    and fS: "open (f ` S)"
    and A: "continuous_on S f" "continuous_on (f ` S) g" 
           "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x" "x \<in> S"
    and B: "(f has_derivative f') (at x)" "bounded_linear g'" "g' \<circ> f' = id"
  shows "(g has_derivative g') (at (f x))"
sorry

text \<open>Here's the simplest way of not assuming much about g.\<close>

proposition has_derivative_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "compact S"
    and "x \<in> S"
    and fx: "f x \<in> interior (f ` S)"
    and "continuous_on S f"
    and gf: "\<And>y. y \<in> S \<Longrightarrow> g (f y) = y"
    and B: "(f has_derivative f') (at x)" "bounded_linear g'" "g' \<circ> f' = id"
  shows "(g has_derivative g') (at (f x))"
sorry


text \<open>Invertible derivative continuous at a point implies local
injectivity. It's only for this we need continuity of the derivative,
except of course if we want the fact that the inverse derivative is
also continuous. So if we know for some other reason that the inverse
function exists, it's OK.\<close>

proposition has_derivative_locally_injective:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "a \<in> S"
      and "open S"
      and bling: "bounded_linear g'"
      and "g' \<circ> f' a = id"
      and derf: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x)"
      and "\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. \<forall>x. dist a x < d \<longrightarrow> onorm (\<lambda>v. f' x v - f' a v) < e"
  obtains r where "r > 0" "ball a r \<subseteq> S" "inj_on f (ball a r)"
sorry


subsection \<open>Uniformly convergent sequence of derivatives\<close>

lemma has_derivative_sequence_lipschitz_lemma:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex S"
    and derf: "\<And>n x. x \<in> S \<Longrightarrow> ((f n) has_derivative (f' n x)) (at x within S)"
    and nle: "\<And>n x h. \<lbrakk>n\<ge>N; x \<in> S\<rbrakk> \<Longrightarrow> norm (f' n x h - g' x h) \<le> e * norm h"
    and "0 \<le> e"
  shows "\<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>S. \<forall>y\<in>S. norm ((f m x - f n x) - (f m y - f n y)) \<le> 2 * e * norm (x - y)"
sorry

lemma has_derivative_sequence_Lipschitz:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "convex S"
    and "\<And>n x. x \<in> S \<Longrightarrow> ((f n) has_derivative (f' n x)) (at x within S)"
    and nle: "\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
    and "e > 0"
  shows "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>x\<in>S. \<forall>y\<in>S.
    norm ((f m x - f n x) - (f m y - f n y)) \<le> e * norm (x - y)"
sorry

proposition has_derivative_sequence:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::banach"
  assumes "convex S"
    and derf: "\<And>n x. x \<in> S \<Longrightarrow> ((f n) has_derivative (f' n x)) (at x within S)"
    and nle: "\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
    and "x0 \<in> S"
    and lim: "((\<lambda>n. f n x0) \<longlongrightarrow> l) sequentially"
  shows "\<exists>g. \<forall>x\<in>S. (\<lambda>n. f n x) \<longlonglongrightarrow> g x \<and> (g has_derivative g'(x)) (at x within S)"
sorry


text \<open>Can choose to line up antiderivatives if we want.\<close>

lemma has_antiderivative_sequence:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::banach"
  assumes "convex S"
    and der: "\<And>n x. x \<in> S \<Longrightarrow> ((f n) has_derivative (f' n x)) (at x within S)"
    and no: "\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F n in sequentially.
       \<forall>x\<in>S. \<forall>h. norm (f' n x h - g' x h) \<le> e * norm h"
  shows "\<exists>g. \<forall>x\<in>S. (g has_derivative g' x) (at x within S)"
sorry

lemma has_antiderivative_limit:
  fixes g' :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'b::banach"
  assumes "convex S"
    and "\<And>e. e>0 \<Longrightarrow> \<exists>f f'. \<forall>x\<in>S.
           (f has_derivative (f' x)) (at x within S) \<and> (\<forall>h. norm (f' x h - g' x h) \<le> e * norm h)"
  shows "\<exists>g. \<forall>x\<in>S. (g has_derivative g' x) (at x within S)"
sorry


subsection \<open>Differentiation of a series\<close>

proposition has_derivative_series:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::banach"
  assumes "convex S"
    and "\<And>n x. x \<in> S \<Longrightarrow> ((f n) has_derivative (f' n x)) (at x within S)"
    and "\<And>e. e>0 \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. \<forall>h. norm (sum (\<lambda>i. f' i x h) {..<n} - g' x h) \<le> e * norm h"
    and "x \<in> S"
    and "(\<lambda>n. f n x) sums l"
  shows "\<exists>g. \<forall>x\<in>S. (\<lambda>n. f n x) sums (g x) \<and> (g has_derivative g' x) (at x within S)"
sorry

lemma has_field_derivative_series:
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex S"
  assumes "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x within S)"
  assumes "uniform_limit S (\<lambda>n x. \<Sum>i<n. f' i x) g' sequentially"
  assumes "x0 \<in> S" "summable (\<lambda>n. f n x0)"
  shows   "\<exists>g. \<forall>x\<in>S. (\<lambda>n. f n x) sums g x \<and> (g has_field_derivative g' x) (at x within S)"
sorry

lemma has_field_derivative_series':
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex S"
  assumes "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x within S)"
  assumes "uniformly_convergent_on S (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> S" "summable (\<lambda>n. f n x0)" "x \<in> interior S"
  shows   "summable (\<lambda>n. f n x)" "((\<lambda>x. \<Sum>n. f n x) has_field_derivative (\<Sum>n. f' n x)) (at x)"
sorry

lemma differentiable_series:
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex S" "open S"
  assumes "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
  assumes "uniformly_convergent_on S (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> S" "summable (\<lambda>n. f n x0)" and x: "x \<in> S"
  shows   "summable (\<lambda>n. f n x)" and "(\<lambda>x. \<Sum>n. f n x) differentiable (at x)"
sorry

lemma differentiable_series':
  fixes f :: "nat \<Rightarrow> ('a :: {real_normed_field,banach}) \<Rightarrow> 'a"
  assumes "convex S" "open S"
  assumes "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
  assumes "uniformly_convergent_on S (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> S" "summable (\<lambda>n. f n x0)"
  shows   "(\<lambda>x. \<Sum>n. f n x) differentiable (at x0)"
sorry

subsection \<open>Derivative as a vector\<close>

text \<open>Considering derivative \<^typ>\<open>real \<Rightarrow> 'b::real_normed_vector\<close> as a vector.\<close>

definition "vector_derivative f net = (SOME f'. (f has_vector_derivative f') net)"

lemma vector_derivative_unique_within:
  assumes not_bot: "at x within S \<noteq> bot"
    and f': "(f has_vector_derivative f') (at x within S)"
    and f'': "(f has_vector_derivative f'') (at x within S)"
  shows "f' = f''"
sorry

lemma vector_derivative_unique_at:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> (f has_vector_derivative f'') (at x) \<Longrightarrow> f' = f''"
sorry

lemma differentiableI_vector: "(f has_vector_derivative y) F \<Longrightarrow> f differentiable F"
sorry

proposition vector_derivative_works:
  "f differentiable net \<longleftrightarrow> (f has_vector_derivative (vector_derivative f net)) net"
    (is "?l = ?r")
sorry

lemma vector_derivative_within:
  assumes not_bot: "at x within S \<noteq> bot" and y: "(f has_vector_derivative y) (at x within S)"
  shows "vector_derivative f (at x within S) = y"
sorry

lemma deriv_of_real [simp]: 
  "at x within A \<noteq> bot \<Longrightarrow> vector_derivative of_real (at x within A) = 1"
sorry

lemma frechet_derivative_eq_vector_derivative:
  assumes "f differentiable (at x)"
    shows  "(frechet_derivative f (at x)) = (\<lambda>r. r *\<^sub>R vector_derivative f (at x))"
sorry

lemma has_real_derivative:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f has_derivative f') F"
  obtains c where "(f has_real_derivative c) F"
sorry

lemma has_real_derivative_iff:
  fixes f :: "real \<Rightarrow> real"
  shows "(\<exists>c. (f has_real_derivative c) F) = (\<exists>D. (f has_derivative D) F)"
sorry

lemma has_vector_derivative_cong_ev:
  assumes *: "eventually (\<lambda>x. x \<in> S \<longrightarrow> f x = g x) (nhds x)" "f x = g x"
  shows "(f has_vector_derivative f') (at x within S) = (g has_vector_derivative f') (at x within S)"
sorry

lemma vector_derivative_cong_eq:
  assumes "eventually (\<lambda>x. x \<in> A \<longrightarrow> f x = g x) (nhds x)" "x = y" "A = B" "x \<in> A"
  shows   "vector_derivative f (at x within A) = vector_derivative g (at y within B)"
sorry

lemma islimpt_closure_open:
  fixes s :: "'a::perfect_space set"
  assumes "open s" and t: "t = closure s" "x \<in> t"
  shows "x islimpt t"
sorry

lemma vector_derivative_unique_within_closed_interval:
  assumes ab: "a < b" "x \<in> cbox a b"
  assumes D: "(f has_vector_derivative f') (at x within cbox a b)" "(f has_vector_derivative f'') (at x within cbox a b)"
  shows "f' = f''"
sorry

lemma vector_derivative_at:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> vector_derivative f (at x) = f'"
sorry

lemma has_vector_derivative_id_at [simp]: "vector_derivative (\<lambda>x. x) (at a) = 1"
sorry

lemma vector_derivative_minus_at [simp]:
  "f differentiable at a
   \<Longrightarrow> vector_derivative (\<lambda>x. - f x) (at a) = - vector_derivative f (at a)"
sorry

lemma vector_derivative_add_at [simp]:
  "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x + g x) (at a) = vector_derivative f (at a) + vector_derivative g (at a)"
sorry

lemma vector_derivative_diff_at [simp,derivative_intros]:
  "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x - g x) (at a) = vector_derivative f (at a) - vector_derivative g (at a)"
sorry

lemma vector_derivative_mult_at [simp]:
  fixes f g :: "real \<Rightarrow> 'a :: real_normed_algebra"
  shows  "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x * g x) (at a) = f a * vector_derivative g (at a) + vector_derivative f (at a) * g a"
sorry

lemma vector_derivative_scaleR_at [simp]:
    "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x *\<^sub>R g x) (at a) = f a *\<^sub>R vector_derivative g (at a) + vector_derivative f (at a) *\<^sub>R g a"
sorry

lemma vector_derivative_within_cbox:
  assumes ab: "a < b" "x \<in> cbox a b"
  assumes f: "(f has_vector_derivative f') (at x within cbox a b)"
  shows "vector_derivative f (at x within cbox a b) = f'"
sorry

lemma vector_derivative_within_closed_interval:
  fixes f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "a < b" and "x \<in> {a..b}"
  assumes "(f has_vector_derivative f') (at x within {a..b})"
  shows "vector_derivative f (at x within {a..b}) = f'"
sorry

lemma has_vector_derivative_within_subset:
  "(f has_vector_derivative f') (at x within S) \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (f has_vector_derivative f') (at x within T)"
sorry

lemma has_vector_derivative_at_within:
  "(f has_vector_derivative f') (at x) \<Longrightarrow> (f has_vector_derivative f') (at x within S)"
sorry

lemma has_vector_derivative_weaken:
  fixes x D and f g S T
  assumes f: "(f has_vector_derivative D) (at x within T)"
    and "x \<in> S" "S \<subseteq> T"
    and "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "(g has_vector_derivative D) (at x within S)"
sorry

lemma has_vector_derivative_transform_within:
  assumes "(f has_vector_derivative f') (at x within S)"
    and "0 < d"
    and "x \<in> S"
    and "\<And>x'. \<lbrakk>x'\<in>S; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
    shows "(g has_vector_derivative f') (at x within S)"
sorry

lemma has_vector_derivative_transform_within_open:
  assumes "(f has_vector_derivative f') (at x)"
    and "open S"
    and "x \<in> S"
    and "\<And>y. y\<in>S \<Longrightarrow> f y = g y"
  shows "(g has_vector_derivative f') (at x)"
sorry

lemma has_vector_derivative_transform:
  assumes "x \<in> S" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  assumes f': "(f has_vector_derivative f') (at x within S)"
  shows "(g has_vector_derivative f') (at x within S)"
sorry

lemma vector_diff_chain_at:
  assumes "(f has_vector_derivative f') (at x)"
    and "(g has_vector_derivative g') (at (f x))"
  shows "((g \<circ> f) has_vector_derivative (f' *\<^sub>R g')) (at x)"
sorry

lemma vector_diff_chain_within:
  assumes "(f has_vector_derivative f') (at x within s)"
    and "(g has_vector_derivative g') (at (f x) within f ` s)"
  shows "((g \<circ> f) has_vector_derivative (f' *\<^sub>R g')) (at x within s)"
sorry

lemma vector_derivative_const_at [simp]: "vector_derivative (\<lambda>x. c) (at a) = 0"
sorry

lemma vector_derivative_at_within_ivl:
  "(f has_vector_derivative f') (at x) \<Longrightarrow>
    a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> a<b \<Longrightarrow> vector_derivative f (at x within {a..b}) = f'"
sorry

lemma vector_derivative_chain_at:
  assumes "f differentiable at x" "(g differentiable at (f x))"
  shows "vector_derivative (g \<circ> f) (at x) =
         vector_derivative f (at x) *\<^sub>R vector_derivative g (at (f x))"
sorry

lemma field_vector_diff_chain_at:  (*thanks to Wenda Li*)
 assumes Df: "(f has_vector_derivative f') (at x)"
     and Dg: "(g has_field_derivative g') (at (f x))"
 shows "((g \<circ> f) has_vector_derivative (f' * g')) (at x)"
sorry

lemma vector_derivative_chain_within: 
  assumes "at x within S \<noteq> bot" "f differentiable (at x within S)" 
    "(g has_derivative g') (at (f x) within f ` S)" 
  shows "vector_derivative (g \<circ> f) (at x within S) =
        g' (vector_derivative f (at x within S)) "
sorry

lemma field_differentiable_imp_differentiable:
  "f field_differentiable F \<Longrightarrow> f differentiable F"
sorry

lemma field_differentiable_imp_continuous_at:
    "f field_differentiable (at x within S) \<Longrightarrow> continuous (at x within S) f"
sorry

lemma field_differentiable_within_subset:
    "\<lbrakk>f field_differentiable (at x within S); T \<subseteq> S\<rbrakk> \<Longrightarrow> f field_differentiable (at x within T)"
sorry

lemma field_differentiable_at_within:
    "\<lbrakk>f field_differentiable (at x)\<rbrakk>
     \<Longrightarrow> f field_differentiable (at x within S)"
sorry

lemma field_differentiable_linear [simp,derivative_intros]: "((*) c) field_differentiable F"
sorry

lemma field_differentiable_const [simp,derivative_intros]: "(\<lambda>z. c) field_differentiable F"
sorry

lemma field_differentiable_ident [simp,derivative_intros]: "(\<lambda>z. z) field_differentiable F"
sorry

lemma field_differentiable_id [simp,derivative_intros]: "id field_differentiable F"
sorry

lemma field_differentiable_minus [derivative_intros]:
  "f field_differentiable F \<Longrightarrow> (\<lambda>z. - (f z)) field_differentiable F"
sorry

lemma field_differentiable_diff_const [simp,derivative_intros]:
  "(-)c field_differentiable F"
sorry

lemma field_differentiable_add [derivative_intros]:
  assumes "f field_differentiable F" "g field_differentiable F"
    shows "(\<lambda>z. f z + g z) field_differentiable F"
sorry

lemma field_differentiable_add_const [simp,derivative_intros]:
     "(+) c field_differentiable F"
sorry

lemma field_differentiable_sum [derivative_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) field_differentiable F) \<Longrightarrow> (\<lambda>z. \<Sum>i\<in>I. f i z) field_differentiable F"
sorry

lemma field_differentiable_diff [derivative_intros]:
  assumes "f field_differentiable F" "g field_differentiable F"
    shows "(\<lambda>z. f z - g z) field_differentiable F"
sorry

lemma field_differentiable_inverse [derivative_intros]:
  assumes "f field_differentiable (at a within S)" "f a \<noteq> 0"
  shows "(\<lambda>z. inverse (f z)) field_differentiable (at a within S)"
sorry

lemma field_differentiable_mult [derivative_intros]:
  assumes "f field_differentiable (at a within S)"
          "g field_differentiable (at a within S)"
    shows "(\<lambda>z. f z * g z) field_differentiable (at a within S)"
sorry

lemma field_differentiable_divide [derivative_intros]:
  assumes "f field_differentiable (at a within S)"
          "g field_differentiable (at a within S)"
          "g a \<noteq> 0"
    shows "(\<lambda>z. f z / g z) field_differentiable (at a within S)"
sorry

lemma field_differentiable_power [derivative_intros]:
  assumes "f field_differentiable (at a within S)"
    shows "(\<lambda>z. f z ^ n) field_differentiable (at a within S)"
sorry

lemma field_differentiable_cnj_cnj:
  assumes "f field_differentiable (at (cnj z))"
  shows   "(cnj \<circ> f \<circ> cnj) field_differentiable (at z)"
sorry

lemma field_differentiable_transform_within:
  "0 < d \<Longrightarrow>
        x \<in> S \<Longrightarrow>
        (\<And>x'. x' \<in> S \<Longrightarrow> dist x' x < d \<Longrightarrow> f x' = g x') \<Longrightarrow>
        f field_differentiable (at x within S)
        \<Longrightarrow> g field_differentiable (at x within S)"
sorry

lemma field_differentiable_compose_within:
  assumes "f field_differentiable (at a within S)"
          "g field_differentiable (at (f a) within f`S)"
    shows "(g o f) field_differentiable (at a within S)"
sorry

lemma field_differentiable_compose:
  "f field_differentiable at z \<Longrightarrow> g field_differentiable at (f z)
          \<Longrightarrow> (g o f) field_differentiable at z"
sorry

lemma field_differentiable_within_open:
     "\<lbrakk>a \<in> S; open S\<rbrakk> \<Longrightarrow> f field_differentiable at a within S \<longleftrightarrow>
                          f field_differentiable at a"
sorry

lemma exp_scaleR_has_vector_derivative_right:
  "((\<lambda>t. exp (t *\<^sub>R A)) has_vector_derivative exp (t *\<^sub>R A) * A) (at t within T)"
sorry

lemma exp_times_scaleR_commute: "exp (t *\<^sub>R A) * A = A * exp (t *\<^sub>R A)"
sorry

lemma exp_scaleR_has_vector_derivative_left: "((\<lambda>t. exp (t *\<^sub>R A)) has_vector_derivative A * exp (t *\<^sub>R A)) (at t)"
sorry

lemma field_differentiable_series:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_field,banach} \<Rightarrow> 'a"
  assumes "convex S" "open S"
  assumes "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
  assumes "uniformly_convergent_on S (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> S" "summable (\<lambda>n. f n x0)" and x: "x \<in> S"
  shows  "(\<lambda>x. \<Sum>n. f n x) field_differentiable (at x)"
sorry

subsubsection\<^marker>\<open>tag unimportant\<close>\<open>Caratheodory characterization\<close>

lemma field_differentiable_caratheodory_at:
  "f field_differentiable (at z) \<longleftrightarrow>
         (\<exists>g. (\<forall>w. f(w) - f(z) = g(w) * (w - z)) \<and> continuous (at z) g)"
sorry

lemma field_differentiable_caratheodory_within:
  "f field_differentiable (at z within s) \<longleftrightarrow>
         (\<exists>g. (\<forall>w. f(w) - f(z) = g(w) * (w - z)) \<and> continuous (at z within s) g)"
sorry

subsection \<open>Field derivative\<close>

definition\<^marker>\<open>tag important\<close> deriv :: "('a \<Rightarrow> 'a::real_normed_field) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "deriv f x \<equiv> SOME D. DERIV f x :> D"

lemma DERIV_imp_deriv: "DERIV f x :> f' \<Longrightarrow> deriv f x = f'"
sorry

lemma DERIV_deriv_iff_has_field_derivative:
  "DERIV f x :> deriv f x \<longleftrightarrow> (\<exists>f'. (f has_field_derivative f') (at x))"
sorry

lemma DERIV_deriv_iff_real_differentiable:
  fixes x :: real
  shows "DERIV f x :> deriv f x \<longleftrightarrow> f differentiable at x"
sorry

lemma DERIV_deriv_iff_field_differentiable:
  "DERIV f x :> deriv f x \<longleftrightarrow> f field_differentiable at x"
sorry

lemma vector_derivative_of_real_left:
  assumes "f differentiable at x"
  shows   "vector_derivative (\<lambda>x. of_real (f x)) (at x) = of_real (deriv f x)"
sorry

lemma vector_derivative_of_real_right:
  assumes "f field_differentiable at (of_real x)"
  shows   "vector_derivative (\<lambda>x. f (of_real x)) (at x) = deriv f (of_real x)"
sorry

lemma deriv_cong_ev:
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)" "x = y"
  shows   "deriv f x = deriv g y"
sorry

lemma higher_deriv_cong_ev:
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)" "x = y"
  shows   "(deriv ^^ n) f x = (deriv ^^ n) g y"
sorry

lemma real_derivative_chain:
  fixes x :: real
  shows "f differentiable at x \<Longrightarrow> g differentiable at (f x)
    \<Longrightarrow> deriv (g o f) x = deriv g (f x) * deriv f x"
sorry

lemma field_derivative_eq_vector_derivative:
   "(deriv f x) = vector_derivative f (at x)"
sorry

proposition field_differentiable_derivI:
    "f field_differentiable (at x) \<Longrightarrow> (f has_field_derivative deriv f x) (at x)"
sorry

lemma vector_derivative_chain_at_general:
  assumes "f differentiable at x" "g field_differentiable at (f x)"
  shows "vector_derivative (g \<circ> f) (at x) = vector_derivative f (at x) * deriv g (f x)"
sorry

lemma deriv_chain:
  "f field_differentiable at x \<Longrightarrow> g field_differentiable at (f x)
    \<Longrightarrow> deriv (g o f) x = deriv g (f x) * deriv f x"
sorry

lemma deriv_linear [simp]: "deriv (\<lambda>w. c * w) = (\<lambda>z. c)"
sorry

lemma deriv_uminus [simp]: "deriv (\<lambda>w. -w) = (\<lambda>z. -1)"
sorry

lemma deriv_ident [simp]: "deriv (\<lambda>w. w) = (\<lambda>z. 1)"
sorry

lemma deriv_id [simp]: "deriv id = (\<lambda>z. 1)"
sorry

lemma deriv_const [simp]: "deriv (\<lambda>w. c) = (\<lambda>z. 0)"
sorry

lemma deriv_add [simp]:
  "\<lbrakk>f field_differentiable at z; g field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
sorry

lemma deriv_minus [simp]:
  "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. - f w) z = - deriv f z"
sorry

lemma deriv_diff [simp]:
  "\<lbrakk>f field_differentiable at z; g field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
sorry

lemma deriv_mult [simp]:
  "\<lbrakk>f field_differentiable at z; g field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w * g w) z = f z * deriv g z + deriv f z * g z"
sorry

lemma deriv_cmult:
  "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. c * f w) z = c * deriv f z"
sorry

lemma deriv_cmult_right:
  "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. f w * c) z = deriv f z * c"
sorry

lemma deriv_inverse [simp]:
  "\<lbrakk>f field_differentiable at z; f z \<noteq> 0\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. inverse (f w)) z = - deriv f z / f z ^ 2"
sorry

lemma deriv_divide [simp]:
  "\<lbrakk>f field_differentiable at z; g field_differentiable at z; g z \<noteq> 0\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w / g w) z = (deriv f z * g z - f z * deriv g z) / g z ^ 2"
sorry

lemma deriv_cdivide_right:
  "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. f w / c) z = deriv f z / c"
sorry

lemma deriv_pow: "\<lbrakk>f field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w ^ n) z = (if n=0 then 0 else n * deriv f z * f z ^ (n - Suc 0))"
sorry

lemma deriv_sum [simp]:
  "\<lbrakk>\<And>i. f i field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. sum (\<lambda>i. f i w) S) z = sum (\<lambda>i. deriv (f i) z) S"
sorry

lemma deriv_compose_linear':
  assumes "f field_differentiable at (c*z + a)"
  shows "deriv (\<lambda>w. f (c*w + a)) z = c * deriv f (c*z + a)"
sorry

lemma deriv_compose_linear:
  assumes "f field_differentiable at (c * z)"
  shows "deriv (\<lambda>w. f (c * w)) z = c * deriv f (c * z)"
sorry

lemma nonzero_deriv_nonconstant:
  assumes df: "DERIV f \<xi> :> df" and S: "open S" "\<xi> \<in> S" and "df \<noteq> 0"
    shows "\<not> f constant_on S"
sorry

subsection \<open>Relation between convexity and derivative\<close>

(* TODO: Generalise to real vector spaces? *)
proposition convex_on_imp_above_tangent:
  assumes convex: "convex_on A f" and connected: "connected A"
  assumes c: "c \<in> interior A" and x : "x \<in> A"
  assumes deriv: "(f has_field_derivative f') (at c within A)"
  shows   "f x - f c \<ge> f' * (x - c)"
sorry


subsection \<open>Partial derivatives\<close>

lemma eventually_at_Pair_within_TimesI1:
  fixes x::"'a::metric_space"
  assumes "\<forall>\<^sub>F x' in at x within X. P x'"
  assumes "P x"
  shows "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. P x'"
sorry

lemma eventually_at_Pair_within_TimesI2:
  fixes x::"'a::metric_space"
  assumes "\<forall>\<^sub>F y' in at y within Y. P y'" "P y"
  shows "\<forall>\<^sub>F (x', y') in at (x, y) within X \<times> Y. P y'"
sorry

proposition has_derivative_partialsI:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
  assumes fx: "((\<lambda>x. f x y) has_derivative fx) (at x within X)"
  assumes fy: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> ((\<lambda>y. f x y) has_derivative blinfun_apply (fy x y)) (at y within Y)"
  assumes fy_cont[unfolded continuous_within]: "continuous (at (x, y) within X \<times> Y) (\<lambda>(x, y). fy x y)"
  assumes "y \<in> Y" "convex Y"
  shows "((\<lambda>(x, y). f x y) has_derivative (\<lambda>(tx, ty). fx tx + fy x y ty)) (at (x, y) within X \<times> Y)"
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Differentiable case distinction\<close>

lemma has_derivative_within_If_eq:
  "((\<lambda>x. if P x then f x else g x) has_derivative f') (at x within S) =
    (bounded_linear f' \<and>
     ((\<lambda>y.(if P y then (f y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)
           else (g y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)))
      \<longlongrightarrow> 0) (at x within S))"
  (is "_ = (_ \<and> (?if \<longlongrightarrow> 0) _)")
sorry

lemma has_derivative_If_within_closures:
  assumes f': "x \<in> S \<union> (closure S \<inter> closure T) \<Longrightarrow>
    (f has_derivative f' x) (at x within S \<union> (closure S \<inter> closure T))"
  assumes g': "x \<in> T \<union> (closure S \<inter> closure T) \<Longrightarrow>
    (g has_derivative g' x) (at x within T \<union> (closure S \<inter> closure T))"
  assumes connect: "x \<in> closure S \<Longrightarrow> x \<in> closure T \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure S \<Longrightarrow> x \<in> closure T \<Longrightarrow> f' x = g' x"
  assumes x_in: "x \<in> S \<union> T"
  shows "((\<lambda>x. if x \<in> S then f x else g x) has_derivative
      (if x \<in> S then f' x else g' x)) (at x within (S \<union> T))"
sorry

lemma has_vector_derivative_If_within_closures:
  assumes x_in: "x \<in> S \<union> T"
  assumes "u = S \<union> T"
  assumes f': "x \<in> S \<union> (closure S \<inter> closure T) \<Longrightarrow>
    (f has_vector_derivative f' x) (at x within S \<union> (closure S \<inter> closure T))"
  assumes g': "x \<in> T \<union> (closure S \<inter> closure T) \<Longrightarrow>
    (g has_vector_derivative g' x) (at x within T \<union> (closure S \<inter> closure T))"
  assumes connect: "x \<in> closure S \<Longrightarrow> x \<in> closure T \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure S \<Longrightarrow> x \<in> closure T \<Longrightarrow> f' x = g' x"
  shows "((\<lambda>x. if x \<in> S then f x else g x) has_vector_derivative
    (if x \<in> S then f' x else g' x)) (at x within u)"
sorry

subsection\<^marker>\<open>tag important\<close>\<open>The Inverse Function Theorem\<close>

lemma linear_injective_contraction:
  assumes "linear f" "c < 1" and le: "\<And>x. norm (f x - x) \<le> c * norm x"
  shows "inj f"
sorry

text\<open>From an online proof by J. Michael Boardman, Department of Mathematics, Johns Hopkins University\<close>
lemma inverse_function_theorem_scaled:
  fixes f::"'a::euclidean_space \<Rightarrow> 'a"
    and f'::"'a \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
  assumes "open U"
    and derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative blinfun_apply (f' x)) (at x)"
    and contf: "continuous_on U f'"
    and "0 \<in> U" and [simp]: "f 0 = 0"
    and id: "f' 0 = id_blinfun"
  obtains U' V g g' where "open U'" "U' \<subseteq> U" "0 \<in> U'" "open V" "0 \<in> V" "homeomorphism U' V f g"
                "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (g' y)) (at y)"
                "\<And>y. y \<in> V \<Longrightarrow> g' y = inv (blinfun_apply (f'(g y)))"
                "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (f'(g y)))"
sorry


text\<open>We need all this to justify the scaling and translations.\<close>
theorem inverse_function_theorem:
  fixes f::"'a::euclidean_space \<Rightarrow> 'a"
    and f'::"'a \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
  assumes "open U"
    and derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative (blinfun_apply (f' x))) (at x)"
    and contf:  "continuous_on U f'"
    and "x0 \<in> U"
    and invf: "invf o\<^sub>L f' x0 = id_blinfun"
  obtains U' V g g' where "open U'" "U' \<subseteq> U" "x0 \<in> U'" "open V" "f x0 \<in> V" "homeomorphism U' V f g"
    "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (g' y)) (at y)"
    "\<And>y. y \<in> V \<Longrightarrow> g' y = inv (blinfun_apply (f'(g y)))"
    "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (f'(g y)))"
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Piecewise differentiable functions\<close>

definition piecewise_differentiable_on
           (infixr \<open>piecewise'_differentiable'_on\<close> 50)
  where "f piecewise_differentiable_on i  \<equiv>
           continuous_on i f \<and>
           (\<exists>S. finite S \<and> (\<forall>x \<in> i - S. f differentiable (at x within i)))"

lemma piecewise_differentiable_on_imp_continuous_on:
    "f piecewise_differentiable_on S \<Longrightarrow> continuous_on S f"
sorry

lemma piecewise_differentiable_on_subset:
    "f piecewise_differentiable_on S \<Longrightarrow> T \<le> S \<Longrightarrow> f piecewise_differentiable_on T"
sorry

lemma differentiable_on_imp_piecewise_differentiable:
  fixes a:: "'a::{linorder_topology,real_normed_vector}"
  shows "f differentiable_on {a..b} \<Longrightarrow> f piecewise_differentiable_on {a..b}"
sorry

lemma differentiable_imp_piecewise_differentiable:
    "(\<And>x. x \<in> S \<Longrightarrow> f differentiable (at x within S))
         \<Longrightarrow> f piecewise_differentiable_on S"
sorry

lemma piecewise_differentiable_const [iff]: "(\<lambda>x. z) piecewise_differentiable_on S"
sorry

lemma piecewise_differentiable_compose:
    "\<lbrakk>f piecewise_differentiable_on S; g piecewise_differentiable_on (f ` S);
      \<And>x. finite (S \<inter> f-`{x})\<rbrakk>
      \<Longrightarrow> (g \<circ> f) piecewise_differentiable_on S"
sorry

lemma piecewise_differentiable_affine:
  fixes m::real
  assumes "f piecewise_differentiable_on ((\<lambda>x. m *\<^sub>R x + c) ` S)"
  shows "(f \<circ> (\<lambda>x. m *\<^sub>R x + c)) piecewise_differentiable_on S"
sorry

lemma piecewise_differentiable_cases:
  fixes c::real
  assumes "f piecewise_differentiable_on {a..c}"
          "g piecewise_differentiable_on {c..b}"
           "a \<le> c" "c \<le> b" "f c = g c"
  shows "(\<lambda>x. if x \<le> c then f x else g x) piecewise_differentiable_on {a..b}"
sorry

lemma piecewise_differentiable_neg:
    "f piecewise_differentiable_on S \<Longrightarrow> (\<lambda>x. -(f x)) piecewise_differentiable_on S"
sorry

lemma piecewise_differentiable_add:
  assumes "f piecewise_differentiable_on i"
          "g piecewise_differentiable_on i"
    shows "(\<lambda>x. f x + g x) piecewise_differentiable_on i"
sorry

lemma piecewise_differentiable_diff:
    "\<lbrakk>f piecewise_differentiable_on S;  g piecewise_differentiable_on S\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f x - g x) piecewise_differentiable_on S"
sorry

subsection\<open>The concept of continuously differentiable\<close>

text \<open>
John Harrison writes as follows:

``The usual assumption in complex analysis texts is that a path \<open>\<gamma>\<close> should be piecewise
continuously differentiable, which ensures that the path integral exists at least for any continuous
f, since all piecewise continuous functions are integrable. However, our notion of validity is
weaker, just piecewise differentiability\ldots{} [namely] continuity plus differentiability except on a
finite set\ldots{} [Our] underlying theory of integration is the Kurzweil-Henstock theory. In contrast to
the Riemann or Lebesgue theory (but in common with a simple notion based on antiderivatives), this
can integrate all derivatives.''

"Formalizing basic complex analysis." From Insight to Proof: Festschrift in Honour of Andrzej Trybulec.
Studies in Logic, Grammar and Rhetoric 10.23 (2007): 151-165.

And indeed he does not assume that his derivatives are continuous, but the penalty is unreasonably
difficult proofs concerning winding numbers. We need a self-contained and straightforward theorem
asserting that all derivatives can be integrated before we can adopt Harrison's choice.\<close>

definition\<^marker>\<open>tag important\<close> C1_differentiable_on :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real set \<Rightarrow> bool"
           (infix \<open>C1'_differentiable'_on\<close> 50)
  where
  "f C1_differentiable_on S \<longleftrightarrow>
   (\<exists>D. (\<forall>x \<in> S. (f has_vector_derivative (D x)) (at x)) \<and> continuous_on S D)"

lemma C1_differentiable_on_eq:
    "f C1_differentiable_on S \<longleftrightarrow>
     (\<forall>x \<in> S. f differentiable at x) \<and> continuous_on S (\<lambda>x. vector_derivative f (at x))"
     (is "?lhs = ?rhs")
sorry

lemma C1_differentiable_on_subset:
  "f C1_differentiable_on T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> f C1_differentiable_on S"
sorry

lemma C1_differentiable_compose:
  assumes fg: "f C1_differentiable_on S" "g C1_differentiable_on (f ` S)" and fin: "\<And>x. finite (S \<inter> f-`{x})"
  shows "(g \<circ> f) C1_differentiable_on S"
sorry

lemma C1_diff_imp_diff: "f C1_differentiable_on S \<Longrightarrow> f differentiable_on S"
sorry

lemma C1_differentiable_on_ident [simp, derivative_intros]: "(\<lambda>x. x) C1_differentiable_on S"
sorry

lemma C1_differentiable_on_const [simp, derivative_intros]: "(\<lambda>z. a) C1_differentiable_on S"
sorry

lemma C1_differentiable_on_add [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x + g x) C1_differentiable_on S"
sorry

lemma C1_differentiable_on_minus [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> (\<lambda>x. - f x) C1_differentiable_on S"
sorry

lemma C1_differentiable_on_diff [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x - g x) C1_differentiable_on S"
sorry

lemma C1_differentiable_on_mult [simp, derivative_intros]:
  fixes f g :: "real \<Rightarrow> 'a :: real_normed_algebra"
  shows "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x * g x) C1_differentiable_on S"
sorry

lemma C1_differentiable_on_scaleR [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x *\<^sub>R g x) C1_differentiable_on S"
sorry

lemma C1_differentiable_on_of_real [derivative_intros]: "of_real C1_differentiable_on S"
sorry

lemma C1_differentiable_on_translation:
  "f C1_differentiable_on U - S \<Longrightarrow> (+) d \<circ> f C1_differentiable_on U - S"
sorry

lemma C1_differentiable_on_translation_eq: 
  fixes d :: "'a::real_normed_vector"
  shows "(+) d \<circ> f C1_differentiable_on i - S \<longleftrightarrow> f C1_differentiable_on i - S"
sorry

definition\<^marker>\<open>tag important\<close> piecewise_C1_differentiable_on
           (infixr \<open>piecewise'_C1'_differentiable'_on\<close> 50)
  where "f piecewise_C1_differentiable_on i  \<equiv>
           continuous_on i f \<and>
           (\<exists>S. finite S \<and> (f C1_differentiable_on (i - S)))"

lemma C1_differentiable_imp_piecewise:
    "f C1_differentiable_on S \<Longrightarrow> f piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_imp_differentiable:
    "f piecewise_C1_differentiable_on i \<Longrightarrow> f piecewise_differentiable_on i"
sorry

lemma piecewise_C1_differentiable_on_translation_eq:
  "((+) d \<circ> f piecewise_C1_differentiable_on i) \<longleftrightarrow> (f piecewise_C1_differentiable_on i)"
sorry

lemma piecewise_C1_differentiable_compose [derivative_intros]:
  assumes fg: "f piecewise_C1_differentiable_on S" "g piecewise_C1_differentiable_on (f ` S)" and fin: "\<And>x. finite (S \<inter> f-`{x})"
  shows "(g \<circ> f) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_on_subset:
    "f piecewise_C1_differentiable_on S \<Longrightarrow> T \<le> S \<Longrightarrow> f piecewise_C1_differentiable_on T"
sorry

lemma C1_differentiable_imp_continuous_on:
  "f C1_differentiable_on S \<Longrightarrow> continuous_on S f"
sorry

lemma C1_differentiable_on_empty [iff,derivative_intros]: "f C1_differentiable_on {}"
sorry

lemma piecewise_C1_differentiable_affine:
  fixes m::real
  assumes "f piecewise_C1_differentiable_on ((\<lambda>x. m * x + c) ` S)"
  shows "(f \<circ> (\<lambda>x. m *\<^sub>R x + c)) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_cases [derivative_intros]:
  fixes c::real
  assumes "f piecewise_C1_differentiable_on {a..c}"
          "g piecewise_C1_differentiable_on {c..b}"
           "a \<le> c" "c \<le> b" "f c = g c"
  shows "(\<lambda>x. if x \<le> c then f x else g x) piecewise_C1_differentiable_on {a..b}"
sorry

lemma piecewise_C1_differentiable_const [derivative_intros]:
  "(\<lambda>x. c) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_scaleR [derivative_intros]:
    "\<lbrakk>f piecewise_C1_differentiable_on S\<rbrakk>
     \<Longrightarrow> (\<lambda>x. c *\<^sub>R f x) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_neg [derivative_intros]:
    "f piecewise_C1_differentiable_on S \<Longrightarrow> (\<lambda>x. -(f x)) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_add [derivative_intros]:
  assumes "f piecewise_C1_differentiable_on i"
          "g piecewise_C1_differentiable_on i"
    shows "(\<lambda>x. f x + g x) piecewise_C1_differentiable_on i"
sorry

lemma piecewise_C1_differentiable_diff [derivative_intros]:
    "\<lbrakk>f piecewise_C1_differentiable_on S;  g piecewise_C1_differentiable_on S\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f x - g x) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_cmult_right [derivative_intros]:
  fixes c::complex
  shows "f piecewise_C1_differentiable_on S
     \<Longrightarrow> (\<lambda>x. f x * c) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_cmult_left [derivative_intros]:
  fixes c::complex
  shows "f piecewise_C1_differentiable_on S
     \<Longrightarrow> (\<lambda>x. c * f x) piecewise_C1_differentiable_on S"
sorry

lemma piecewise_C1_differentiable_on_of_real [derivative_intros]: 
  "of_real piecewise_C1_differentiable_on S"
sorry

end
