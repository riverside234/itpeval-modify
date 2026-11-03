(*  Title:      HOL/Analysis/Linear_Algebra.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Elementary Linear Algebra on Euclidean Spaces\<close>

theory Linear_Algebra
imports
  Euclidean_Space
  "HOL-Library.Infinite_Set"
begin

lemma linear_simps:
  assumes "bounded_linear f"
  shows
    "f (a + b) = f a + f b"
    "f (a - b) = f a - f b"
    "f 0 = 0"
    "f (- a) = - f a"
    "f (s *\<^sub>R v) = s *\<^sub>R (f v)"
  by sorry

lemma finite_Atleast_Atmost_nat[simp]: "finite {f x |x. x \<in> (UNIV::'a::finite set)}"
  by sorry

lemma substdbasis_expansion_unique:
  includes inner_syntax
  assumes d: "d \<subseteq> Basis"
  shows "(\<Sum>i\<in>d. f i *\<^sub>R i) = (x::'a::euclidean_space) \<longleftrightarrow>
    (\<forall>i\<in>Basis. (i \<in> d \<longrightarrow> f i = x \<bullet> i) \<and> (i \<notin> d \<longrightarrow> x \<bullet> i = 0))"
  by sorry

lemma independent_substdbasis: "d \<subseteq> Basis \<Longrightarrow> independent d"
  by sorry

lemma subset_translation_eq [simp]:
    fixes a :: "'a::real_vector" shows "(+) a ` s \<subseteq> (+) a ` t \<longleftrightarrow> s \<subseteq> t"
  by sorry

lemma translate_inj_on:
  fixes A :: "'a::ab_group_add set"
  shows "inj_on (\<lambda>x. a + x) A"
  by sorry

lemma translation_assoc:
  fixes a b :: "'a::ab_group_add"
  shows "(\<lambda>x. b + x) ` ((\<lambda>x. a + x) ` S) = (\<lambda>x. (a + b) + x) ` S"
  by sorry

lemma translation_invert:
  fixes a :: "'a::ab_group_add"
  assumes "(\<lambda>x. a + x) ` A = (\<lambda>x. a + x) ` B"
  shows "A = B"
  by sorry

lemma translation_galois:
  fixes a :: "'a::ab_group_add"
  shows "T = ((\<lambda>x. a + x) ` S) \<longleftrightarrow> S = ((\<lambda>x. (- a) + x) ` T)"
  by sorry

lemma translation_inverse_subset:
  assumes "((\<lambda>x. - a + x) ` V) \<le> (S :: 'n::ab_group_add set)"
  shows "V \<le> ((\<lambda>x. a + x) ` S)"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>More interesting properties of the norm\<close>

unbundle inner_syntax

text\<open>Equality of vectors in terms of \<^term>\<open>(\<bullet>)\<close> products.\<close>

lemma linear_componentwise:
  fixes f:: "'a::euclidean_space \<Rightarrow> 'b::real_inner"
  assumes lf: "linear f"
  shows "(f x) \<bullet> j = (\<Sum>i\<in>Basis. (x\<bullet>i) * (f i\<bullet>j))" (is "?lhs = ?rhs")
  by sorry

lemma vector_eq: "x = y \<longleftrightarrow> x \<bullet> x = x \<bullet> y \<and> y \<bullet> y = x \<bullet> x"
  by sorry

lemma norm_triangle_half_r:
  "norm (y - x1) < e/2 \<Longrightarrow> norm (y - x2) < e/2 \<Longrightarrow> norm (x1 - x2) < e"
  by sorry

lemma norm_triangle_half_l:
  assumes "norm (x - y) < e/2" and "norm (x' - y) < e/2"
  shows "norm (x - x') < e"
  by sorry

lemma abs_triangle_half_r:
  fixes y :: "'a::linordered_field"
  shows "abs (y - x1) < e/2 \<Longrightarrow> abs (y - x2) < e/2 \<Longrightarrow> abs (x1 - x2) < e"
  by sorry

lemma abs_triangle_half_l:
  fixes y :: "'a::linordered_field"
  assumes "abs (x - y) < e/2" and "abs (x' - y) < e/2"
  shows "abs (x - x') < e"
  by sorry

lemma sum_clauses:
  shows "sum f {} = 0"
    and "finite S \<Longrightarrow> sum f (insert x S) = (if x \<in> S then sum f S else f x + sum f S)"
  by sorry

lemma vector_eq_ldot: "(\<forall>x. x \<bullet> y = x \<bullet> z) \<longleftrightarrow> y = z" and vector_eq_rdot: "(\<forall>z. x \<bullet> z = y \<bullet> z) \<longleftrightarrow> x = y"
  by sorry

subsection \<open>Substandard Basis\<close>

lemma ex_card:
  assumes "n \<le> card A"
  shows "\<exists>S\<subseteq>A. card S = n"
  by sorry

lemma subspace_substandard: "subspace {x::'a::euclidean_space. (\<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0)}"
  by sorry

lemma dim_substandard:
  assumes d: "d \<subseteq> Basis"
  shows "dim {x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0} = card d" (is "dim ?A = _")
  by sorry


subsection \<open>Orthogonality\<close>

definition\<^marker>\<open>tag important\<close> (in real_inner) "orthogonal x y \<longleftrightarrow> x \<bullet> y = 0"

context real_inner
begin

lemma orthogonal_self: "orthogonal x x \<longleftrightarrow> x = 0"
  by sorry

lemma orthogonal_clauses:
  "orthogonal a 0"
  "orthogonal a x \<Longrightarrow> orthogonal a (c *\<^sub>R x)"
  "orthogonal a x \<Longrightarrow> orthogonal a (- x)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x + y)"
  "orthogonal a x \<Longrightarrow> orthogonal a y \<Longrightarrow> orthogonal a (x - y)"
  "orthogonal 0 a"
  "orthogonal x a \<Longrightarrow> orthogonal (c *\<^sub>R x) a"
  "orthogonal x a \<Longrightarrow> orthogonal (- x) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x + y) a"
  "orthogonal x a \<Longrightarrow> orthogonal y a \<Longrightarrow> orthogonal (x - y) a"
  by sorry

end

lemma orthogonal_commute: "orthogonal x y \<longleftrightarrow> orthogonal y x"
  by sorry

lemma orthogonal_scaleR [simp]: "c \<noteq> 0 \<Longrightarrow> orthogonal (c *\<^sub>R x) = orthogonal x"
  by sorry

lemma pairwise_ortho_scaleR:
    "pairwise (\<lambda>i j. orthogonal (f i) (g j)) B
    \<Longrightarrow> pairwise (\<lambda>i j. orthogonal (a i *\<^sub>R f i) (a j *\<^sub>R g j)) B"
  by sorry

lemma orthogonal_rvsum:
    "\<lbrakk>finite s; \<And>y. y \<in> s \<Longrightarrow> orthogonal x (f y)\<rbrakk> \<Longrightarrow> orthogonal x (sum f s)"
  by sorry

lemma orthogonal_lvsum:
    "\<lbrakk>finite s; \<And>x. x \<in> s \<Longrightarrow> orthogonal (f x) y\<rbrakk> \<Longrightarrow> orthogonal (sum f s) y"
  by sorry

lemma norm_add_Pythagorean:
  assumes "orthogonal a b"
    shows "(norm (a + b))\<^sup>2 = (norm a)\<^sup>2 + (norm b)\<^sup>2"
  by sorry

lemma norm_sum_Pythagorean:
  assumes "finite I" "pairwise (\<lambda>i j. orthogonal (f i) (f j)) I"
    shows "(norm (sum f I))\<^sup>2 = (\<Sum>i\<in>I. (norm (f i))\<^sup>2)"
  by sorry


subsection  \<open>Orthogonality of a transformation\<close>

definition\<^marker>\<open>tag important\<close>  "orthogonal_transformation f \<longleftrightarrow> linear f \<and> (\<forall>v w. f v \<bullet> f w = v \<bullet> w)"

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation:
  "orthogonal_transformation f \<longleftrightarrow> linear f \<and> (\<forall>v. norm (f v) = norm v)"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_id [simp]: "orthogonal_transformation (\<lambda>x. x)"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_orthogonal_transformation:
    "orthogonal_transformation f \<Longrightarrow> orthogonal (f x) (f y) \<longleftrightarrow> orthogonal x y"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_compose:
   "\<lbrakk>orthogonal_transformation f; orthogonal_transformation g\<rbrakk> \<Longrightarrow> orthogonal_transformation(f \<circ> g)"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_neg:
  "orthogonal_transformation(\<lambda>x. -(f x)) \<longleftrightarrow> orthogonal_transformation f"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_scaleR: "orthogonal_transformation f \<Longrightarrow> f (c *\<^sub>R v) = c *\<^sub>R f v"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_linear:
   "orthogonal_transformation f \<Longrightarrow> linear f"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_inj:
  "orthogonal_transformation f \<Longrightarrow> inj f"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_surj:
  "orthogonal_transformation f \<Longrightarrow> surj f"
  for f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_bij:
  "orthogonal_transformation f \<Longrightarrow> bij f"
  for f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_inv:
  "orthogonal_transformation f \<Longrightarrow> orthogonal_transformation (inv f)"
  for f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  by sorry

lemma\<^marker>\<open>tag unimportant\<close>  orthogonal_transformation_norm:
  "orthogonal_transformation f \<Longrightarrow> norm (f x) = norm x"
  by sorry


subsection \<open>Bilinear functions\<close>

definition\<^marker>\<open>tag important\<close>
bilinear :: "('a::real_vector \<Rightarrow> 'b::real_vector \<Rightarrow> 'c::real_vector) \<Rightarrow> bool" where
"bilinear f \<longleftrightarrow> (\<forall>x. linear (\<lambda>y. f x y)) \<and> (\<forall>y. linear (\<lambda>x. f x y))"

lemma bilinear_ladd: "bilinear h \<Longrightarrow> h (x + y) z = h x z + h y z"
  by sorry

lemma bilinear_radd: "bilinear h \<Longrightarrow> h x (y + z) = h x y + h x z"
  by sorry

lemma bilinear_times:
  fixes c::"'a::real_algebra" shows "bilinear (\<lambda>x y::'a. x*y)"
  by sorry

lemma bilinear_lmul: "bilinear h \<Longrightarrow> h (c *\<^sub>R x) y = c *\<^sub>R h x y"
  by sorry

lemma bilinear_rmul: "bilinear h \<Longrightarrow> h x (c *\<^sub>R y) = c *\<^sub>R h x y"
  by sorry

lemma bilinear_lneg: "bilinear h \<Longrightarrow> h (- x) y = - h x y"
  by sorry

lemma bilinear_rneg: "bilinear h \<Longrightarrow> h x (- y) = - h x y"
  by sorry

lemma (in ab_group_add) eq_add_iff: "x = x + y \<longleftrightarrow> y = 0"
  by sorry

lemma bilinear_lzero:
  assumes "bilinear h"
  shows "h 0 x = 0"
  by sorry

lemma bilinear_rzero:
  assumes "bilinear h"
  shows "h x 0 = 0"
  by sorry

lemma bilinear_lsub: "bilinear h \<Longrightarrow> h (x - y) z = h x z - h y z"
  by sorry

lemma bilinear_rsub: "bilinear h \<Longrightarrow> h z (x - y) = h z x - h z y"
  by sorry

lemma bilinear_sum:
  assumes "bilinear h"
  shows "h (sum f S) (sum g T) = sum (\<lambda>(i,j). h (f i) (g j)) (S \<times> T) "
  by sorry


subsection \<open>Adjoints\<close>

definition\<^marker>\<open>tag important\<close> adjoint :: "(('a::real_inner) \<Rightarrow> ('b::real_inner)) \<Rightarrow> 'b \<Rightarrow> 'a" where
"adjoint f = (SOME f'. \<forall>x y. f x \<bullet> y = x \<bullet> f' y)"

lemma adjoint_unique:
  assumes "\<forall>x y. inner (f x) y = inner x (g y)"
  shows "adjoint f = g"
  by sorry

text \<open>TODO: The following lemmas about adjoints should hold for any
  Hilbert space (i.e. complete inner product space).
  (see \<^url>\<open>https://en.wikipedia.org/wiki/Hermitian_adjoint\<close>)
\<close>

lemma adjoint_works:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
  by sorry

lemma adjoint_clauses:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "x \<bullet> adjoint f y = f x \<bullet> y"
    and "adjoint f y \<bullet> x = y \<bullet> f x"
  by sorry

lemma adjoint_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "linear (adjoint f)"
  by sorry

lemma adjoint_adjoint:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes lf: "linear f"
  shows "adjoint (adjoint f) = f"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Euclidean Spaces as Typeclass\<close>

lemma independent_Basis: "independent Basis"
  by sorry

lemma span_Basis [simp]: "span Basis = UNIV"
  by sorry

lemma in_span_Basis: "x \<in> span Basis"
  by sorry

lemma representation_euclidean_space:
  "representation Basis x = (\<lambda>b. if b \<in> Basis then inner x b else 0)"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Linearity and Bilinearity continued\<close>

lemma linear_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x. norm (f x) \<le> B * norm x"
  by sorry

lemma linear_conv_bounded_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<longleftrightarrow> bounded_linear f"
  by sorry

lemmas linear_linear = linear_conv_bounded_linear[symmetric]

lemma inj_linear_imp_inv_bounded_linear:
  fixes f::"'a::euclidean_space \<Rightarrow> 'a"
  shows "\<lbrakk>bounded_linear f; inj f\<rbrakk> \<Longrightarrow> bounded_linear (inv f)"
  by sorry

lemma linear_bounded_pos:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes lf: "linear f"
 obtains B where "B > 0" "\<And>x. norm (f x) \<le> B * norm x"
  by sorry

lemma linear_invertible_bounded_below_pos:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "linear g" and gf: "g \<circ> f = id"
  obtains B where "B > 0" "\<And>x. B * norm x \<le> norm(f x)"
  by sorry

lemma linear_inj_bounded_below_pos:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  obtains B where "B > 0" "\<And>x. B * norm x \<le> norm(f x)"
  by sorry

lemma bounded_linearI':
  fixes f ::"'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "bounded_linear f"
  by sorry

lemma bilinear_bounded:
  fixes h :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space \<Rightarrow> 'k::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
  by sorry

lemma bilinear_conv_bounded_bilinear:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  shows "bilinear h \<longleftrightarrow> bounded_bilinear h"
  by sorry

lemma bilinear_bounded_pos:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  assumes bh: "bilinear h"
  shows "\<exists>B > 0. \<forall>x y. norm (h x y) \<le> B * norm x * norm y"
  by sorry

lemma bounded_linear_imp_has_derivative: 
  "bounded_linear f \<Longrightarrow> (f has_derivative f) net"
  by sorry

lemma linear_imp_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> (f has_derivative f) net"
  by sorry

lemma bounded_linear_imp_differentiable: "bounded_linear f \<Longrightarrow> f differentiable net"
  by sorry

lemma linear_imp_differentiable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  shows "linear f \<Longrightarrow> f differentiable net"
  by sorry

lemma of_real_differentiable [simp,derivative_intros]: "of_real differentiable F"
  by sorry

lemma bounded_linear_representation:
  fixes B :: "'a :: euclidean_space set"
  assumes "independent B" "span B = UNIV"
  shows   "bounded_linear (\<lambda>v. representation B v b)"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>We continue\<close>

lemma independent_bound:
  fixes S :: "'a::euclidean_space set"
  shows "independent S \<Longrightarrow> finite S \<and> card S \<le> DIM('a)"
  by sorry

lemmas independent_imp_finite = finiteI_independent

corollary\<^marker>\<open>tag unimportant\<close> independent_card_le:
  fixes S :: "'a::euclidean_space set"
  assumes "independent S"
  shows "card S \<le> DIM('a)"
  by sorry

lemma dependent_biggerset:
  fixes S :: "'a::euclidean_space set"
  shows "(finite S \<Longrightarrow> card S > DIM('a)) \<Longrightarrow> dependent S"
  by sorry

text \<open>Picking an orthogonal replacement for a spanning set.\<close>

lemma vector_sub_project_orthogonal:
  fixes b x :: "'a::euclidean_space"
  shows "b \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *\<^sub>R b) = 0"
  by sorry

lemma pairwise_orthogonal_insert:
  assumes "pairwise orthogonal S"
    and "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
  shows "pairwise orthogonal (insert x S)"
  by sorry

lemma basis_orthogonal:
  fixes B :: "'a::real_inner set"
  assumes fB: "finite B"
  shows "\<exists>C. finite C \<and> card C \<le> card B \<and> span C = span B \<and> pairwise orthogonal C"
  (is " \<exists>C. ?P B C")
  by sorry

lemma orthogonal_basis_exists:
  fixes V :: "('a::euclidean_space) set"
  shows "\<exists>B. independent B \<and> B \<subseteq> span V \<and> V \<subseteq> span B \<and> (card B = dim V) \<and> pairwise orthogonal B"
  by sorry

text \<open>Low-dimensional subset is in a hyperplane (weak orthogonal complement).\<close>

lemma span_not_UNIV_orthogonal:
  fixes S :: "'a::euclidean_space set"
  assumes sU: "span S \<noteq> UNIV"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> (\<forall>x \<in> span S. a \<bullet> x = 0)"
  by sorry

lemma span_not_univ_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes SU: "span S \<noteq> UNIV"
  shows "\<exists> a. a \<noteq>0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  by sorry

lemma lowdim_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes d: "dim S < DIM('a)"
  shows "\<exists>a::'a. a \<noteq> 0 \<and> span S \<subseteq> {x. a \<bullet> x = 0}"
  by sorry

lemma linear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> _"
  assumes lf: "linear f"
    and lg: "linear g"
    and fg: "\<And>b. b \<in> Basis \<Longrightarrow> f b = g b"
  shows "f = g"
  by sorry


text \<open>Similar results for bilinear functions.\<close>

lemma bilinear_eq:
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and SB: "S \<subseteq> span B"
    and TC: "T \<subseteq> span C"
    and "x\<in>S" "y\<in>T"
    and fg: "\<And>x y. \<lbrakk>x \<in> B; y\<in> C\<rbrakk> \<Longrightarrow> f x y = g x y"
  shows "f x y = g x y"
  by sorry

lemma bilinear_eq_stdbasis:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> _"
  assumes bf: "bilinear f"
    and bg: "bilinear g"
    and fg: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> f i j = g i j"
  shows "f = g"
  by sorry


subsection \<open>Infinity norm\<close>

definition\<^marker>\<open>tag important\<close> "infnorm (x::'a::euclidean_space) = Sup {\<bar>x \<bullet> b\<bar> |b. b \<in> Basis}"

lemma infnorm_set_image:
  fixes x :: "'a::euclidean_space"
  shows "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} = (\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis"
  by sorry

lemma infnorm_Max:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = Max ((\<lambda>i. \<bar>x \<bullet> i\<bar>) ` Basis)"
  by sorry

lemma infnorm_set_lemma:
  fixes x :: "'a::euclidean_space"
  shows "finite {\<bar>x \<bullet> i\<bar> |i. i \<in> Basis}"
    and "{\<bar>x \<bullet> i\<bar> |i. i \<in> Basis} \<noteq> {}"
  by sorry

lemma infnorm_pos_le:
  fixes x :: "'a::euclidean_space"
  shows "0 \<le> infnorm x"
  by sorry

lemma infnorm_triangle:
  fixes x :: "'a::euclidean_space"
  shows "infnorm (x + y) \<le> infnorm x + infnorm y"
  by sorry

lemma infnorm_eq_0:
  fixes x :: "'a::euclidean_space"
  shows "infnorm x = 0 \<longleftrightarrow> x = 0"
  by sorry

lemma infnorm_0: "infnorm 0 = 0"
  by sorry

lemma infnorm_neg: "infnorm (- x) = infnorm x"
  by sorry

lemma infnorm_sub: "infnorm (x - y) = infnorm (y - x)"
  by sorry

lemma absdiff_infnorm: "\<bar>infnorm x - infnorm y\<bar> \<le> infnorm (x - y)"
  by sorry

lemma real_abs_infnorm: "\<bar>infnorm x\<bar> = infnorm x"
  by sorry

lemma Basis_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "b \<in> Basis \<Longrightarrow> \<bar>x \<bullet> b\<bar> \<le> infnorm x"
  by sorry

lemma infnorm_mul: "infnorm (a *\<^sub>R x) = \<bar>a\<bar> * infnorm x"
  by sorry

lemma infnorm_mul_lemma: "infnorm (a *\<^sub>R x) \<le> \<bar>a\<bar> * infnorm x"
  by sorry

lemma infnorm_pos_lt: "infnorm x > 0 \<longleftrightarrow> x \<noteq> 0"
  by sorry

text \<open>Prove that it differs only up to a bound from Euclidean norm.\<close>

lemma infnorm_le_norm: "infnorm x \<le> norm x"
  by sorry

lemma norm_le_infnorm:
  fixes x :: "'a::euclidean_space"
  shows "norm x \<le> sqrt DIM('a) * infnorm x"
  by sorry

lemma tendsto_infnorm [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F"
  shows "((\<lambda>x. infnorm (f x)) \<longlongrightarrow> infnorm a) F"
  by sorry

text \<open>Equality in Cauchy-Schwarz and triangle inequalities.\<close>

lemma norm_cauchy_schwarz_eq: "x \<bullet> y = norm x * norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
  (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma norm_cauchy_schwarz_abs_eq:
  "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow>
    norm x *\<^sub>R y = norm y *\<^sub>R x \<or> norm x *\<^sub>R y = - norm y *\<^sub>R x"
  by sorry

lemma norm_triangle_eq:
  fixes x y :: "'a::real_inner"
  shows "norm (x + y) = norm x + norm y \<longleftrightarrow> norm x *\<^sub>R y = norm y *\<^sub>R x"
  by sorry

lemma dist_triangle_eq:
  fixes x y z :: "'a::real_inner"
  shows "dist x z = dist x y + dist y z \<longleftrightarrow>
    norm (x - y) *\<^sub>R (y - z) = norm (y - z) *\<^sub>R (x - y)"
  by sorry

subsection \<open>Collinearity\<close>

definition\<^marker>\<open>tag important\<close> collinear :: "'a::real_vector set \<Rightarrow> bool"
  where "collinear S \<longleftrightarrow> (\<exists>u. \<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u)"

lemma collinear_alt:
     "collinear S \<longleftrightarrow> (\<exists>u v. \<forall>x \<in> S. \<exists>c. x = u + c *\<^sub>R v)" (is "?lhs = ?rhs")
  by sorry

lemma collinear:
  fixes S :: "'a::{perfect_space,real_vector} set"
  shows "collinear S \<longleftrightarrow> (\<exists>u. u \<noteq> 0 \<and> (\<forall>x \<in> S. \<forall> y \<in> S. \<exists>c. x - y = c *\<^sub>R u))"
  by sorry

lemma collinear_subset: "\<lbrakk>collinear T; S \<subseteq> T\<rbrakk> \<Longrightarrow> collinear S"
  by sorry

lemma collinear_empty [iff]: "collinear {}"
  by sorry

lemma collinear_sing [iff]: "collinear {x}"
  by sorry

lemma collinear_2 [iff]: "collinear {x, y}"
  by sorry

lemma collinear_lemma: "collinear {0, x, y} \<longleftrightarrow> x = 0 \<or> y = 0 \<or> (\<exists>c. y = c *\<^sub>R x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma collinear_iff_Reals: "collinear {0::complex,w,z} \<longleftrightarrow> z/w \<in> \<real>"
  by sorry

lemma collinear_scaleR_iff: "collinear {0, \<alpha> *\<^sub>R w, \<beta> *\<^sub>R z} \<longleftrightarrow> collinear {0,w,z} \<or> \<alpha>=0 \<or> \<beta>=0"
  (is "?lhs = ?rhs")
  by sorry

lemma norm_cauchy_schwarz_equal: "\<bar>x \<bullet> y\<bar> = norm x * norm y \<longleftrightarrow> collinear {0, x, y}"
  by sorry

lemma norm_triangle_eq_imp_collinear:
  fixes x y :: "'a::real_inner"
  assumes "norm (x + y) = norm x + norm y"
  shows "collinear{0,x,y}"
  by sorry


subsection\<open>Properties of special hyperplanes\<close>

lemma subspace_hyperplane: "subspace {x. a \<bullet> x = 0}"
  by sorry

lemma subspace_hyperplane2: "subspace {x. x \<bullet> a = 0}"
  by sorry

lemma special_hyperplane_span:
  fixes S :: "'n::euclidean_space set"
  assumes "k \<in> Basis"
  shows "{x. k \<bullet> x = 0} = span (Basis - {k})"
  by sorry

lemma dim_special_hyperplane:
  fixes k :: "'n::euclidean_space"
  shows "k \<in> Basis \<Longrightarrow> dim {x. k \<bullet> x = 0} = DIM('n) - 1"
  by sorry

proposition dim_hyperplane:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
    shows "dim {x. a \<bullet> x = 0} = DIM('a) - 1"
  by sorry

lemma lowdim_eq_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "dim S = DIM('a) - 1"
  obtains a where "a \<noteq> 0" and "span S = {x. a \<bullet> x = 0}"
  by sorry

lemma dim_eq_hyperplane:
  fixes S :: "'n::euclidean_space set"
  shows "dim S = DIM('n) - 1 \<longleftrightarrow> (\<exists>a. a \<noteq> 0 \<and> span S = {x. a \<bullet> x = 0})"
  by sorry


subsection\<open> Orthogonal bases and Gram-Schmidt process\<close>

lemma pairwise_orthogonal_independent:
  assumes "pairwise orthogonal S" and "0 \<notin> S"
    shows "independent S"
  by sorry

lemma pairwise_orthogonal_imp_finite:
  fixes S :: "'a::euclidean_space set"
  assumes "pairwise orthogonal S"
    shows "finite S"
  by sorry

lemma subspace_orthogonal_to_vector: "subspace {y. orthogonal x y}"
  by sorry

lemma subspace_orthogonal_to_vectors: "subspace {y. \<forall>x \<in> S. orthogonal x y}"
  by sorry

lemma orthogonal_to_span:
  assumes a: "a \<in> span S" and x: "\<And>y. y \<in> S \<Longrightarrow> orthogonal x y"
    shows "orthogonal x a"
  by sorry

proposition Gram_Schmidt_step:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S" and x: "x \<in> span S"
    shows "orthogonal x (a - (\<Sum>b\<in>S. (b \<bullet> a / (b \<bullet> b)) *\<^sub>R b))"
  by sorry


lemma orthogonal_extension_aux:
  fixes S :: "'a::euclidean_space set"
  assumes "finite T" "finite S" "pairwise orthogonal S"
    shows "\<exists>U. pairwise orthogonal (S \<union> U) \<and> span (S \<union> U) = span (S \<union> T)"
  by sorry


proposition orthogonal_extension:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S"
  obtains U where "pairwise orthogonal (S \<union> U)" "span (S \<union> U) = span (S \<union> T)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> orthogonal_extension_strong:
  fixes S :: "'a::euclidean_space set"
  assumes S: "pairwise orthogonal S"
  obtains U where "U \<inter> (insert 0 S) = {}" "pairwise orthogonal (S \<union> U)"
                  "span (S \<union> U) = span (S \<union> T)"
  by sorry

subsection\<open>Decomposing a vector into parts in orthogonal subspaces\<close>

text\<open>existence of orthonormal basis for a subspace.\<close>

lemma orthogonal_spanningset_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "B \<subseteq> S" "pairwise orthogonal B" "span B = S"
  by sorry

lemma orthogonal_basis_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "0 \<notin> B" "B \<subseteq> S" "pairwise orthogonal B" "independent B"
                  "card B = dim S" "span B = S"
  by sorry

proposition orthonormal_basis_subspace:
  fixes S :: "'a :: euclidean_space set"
  assumes "subspace S"
  obtains B where "B \<subseteq> S" "pairwise orthogonal B"
              and "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
              and "independent B" "card B = dim S" "span B = S"
  by sorry


proposition\<^marker>\<open>tag unimportant\<close> orthogonal_to_subspace_exists_gen:
  fixes S :: "'a :: euclidean_space set"
  assumes "span S \<subset> span T"
  obtains x where "x \<noteq> 0" "x \<in> span T" "\<And>y. y \<in> span S \<Longrightarrow> orthogonal x y"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> orthogonal_to_subspace_exists:
  fixes S :: "'a :: euclidean_space set"
  assumes "dim S < DIM('a)"
  obtains x where "x \<noteq> 0" "\<And>y. y \<in> span S \<Longrightarrow> orthogonal x y"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> orthogonal_to_vector_exists:
  fixes x :: "'a :: euclidean_space"
  assumes "2 \<le> DIM('a)"
  obtains y where "y \<noteq> 0" "orthogonal x y"
  by sorry

proposition\<^marker>\<open>tag unimportant\<close> orthogonal_subspace_decomp_exists:
  fixes S :: "'a :: euclidean_space set"
  obtains y z
  where "y \<in> span S"
    and "\<And>w. w \<in> span S \<Longrightarrow> orthogonal z w"
    and "x = y + z"
  by sorry

lemma orthogonal_subspace_decomp_unique:
  fixes S :: "'a :: euclidean_space set"
  assumes "x + y = x' + y'"
      and ST: "x \<in> span S" "x' \<in> span S" "y \<in> span T" "y' \<in> span T"
      and orth: "\<And>a b. \<lbrakk>a \<in> S; b \<in> T\<rbrakk> \<Longrightarrow> orthogonal a b"
  shows "x = x' \<and> y = y'"
  by sorry

lemma vector_in_orthogonal_spanningset:
  fixes a :: "'a::euclidean_space"
  obtains S where "a \<in> S" "pairwise orthogonal S" "span S = UNIV"
  by sorry

lemma vector_in_orthogonal_basis:
  fixes a :: "'a::euclidean_space"
  assumes "a \<noteq> 0"
  obtains S where "a \<in> S" "0 \<notin> S" "pairwise orthogonal S" "independent S" "finite S"
                  "span S = UNIV" "card S = DIM('a)"
  by sorry

lemma vector_in_orthonormal_basis:
  fixes a :: "'a::euclidean_space"
  assumes "norm a = 1"
  obtains S where "a \<in> S" "pairwise orthogonal S" "\<And>x. x \<in> S \<Longrightarrow> norm x = 1"
    "independent S" "card S = DIM('a)" "span S = UNIV"
  by sorry

proposition dim_orthogonal_sum:
  fixes A :: "'a::euclidean_space set"
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> x \<bullet> y = 0"
    shows "dim(A \<union> B) = dim A + dim B"
  by sorry

lemma dim_subspace_orthogonal_to_vectors:
  fixes A :: "'a::euclidean_space set"
  assumes "subspace A" "subspace B" "A \<subseteq> B"
    shows "dim {y \<in> B. \<forall>x \<in> A. orthogonal x y} + dim A = dim B"
  by sorry

subsection\<open>Linear functions are (uniformly) continuous on any set\<close>

subsection\<^marker>\<open>tag unimportant\<close> \<open>Topological properties of linear functions\<close>

lemma linear_lim_0:
  assumes "bounded_linear f"
  shows "(f \<longlongrightarrow> 0) (at (0))"
  by sorry

lemma linear_continuous_at:
  "bounded_linear f \<Longrightarrow>continuous (at a) f"
  by sorry

lemma linear_continuous_within:
  "bounded_linear f \<Longrightarrow> continuous (at x within s) f"
  by sorry

lemma linear_continuous_on:
  "bounded_linear f \<Longrightarrow> continuous_on s f"
  by sorry

lemma Lim_linear:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and h :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "(f \<longlongrightarrow> l) F" "linear h"
  shows "((\<lambda>x. h(f x)) \<longlongrightarrow> h l) F"
  by sorry

lemma linear_continuous_compose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "continuous F f" "linear g"
  shows "continuous F (\<lambda>x. g(f x))"
  by sorry

lemma linear_continuous_on_compose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space" and g :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "continuous_on S f" "linear g"
  shows "continuous_on S (\<lambda>x. g(f x))"
  by sorry

text\<open>Also bilinear functions, in composition form\<close>

lemma bilinear_continuous_compose:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
  assumes "continuous F f" "continuous F g" "bilinear h"
  shows "continuous F (\<lambda>x. h (f x) (g x))"
  by sorry

lemma bilinear_continuous_on_compose:
  fixes h :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::real_normed_vector"
    and f :: "'d::t2_space \<Rightarrow> 'a"
  assumes "continuous_on S f" "continuous_on S g" "bilinear h"
  shows "continuous_on S (\<lambda>x. h (f x) (g x))"
  by sorry

end
