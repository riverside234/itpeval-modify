section "Affine Sets"

theory Affine
imports Linear_Algebra
begin

lemma if_smult: "(if P then x else (y::real)) *\<^sub>R v = (if P then x *\<^sub>R v else y *\<^sub>R v)"
  by sorry

lemma sum_delta_notmem:
  assumes "x \<notin> s"
  shows "sum (\<lambda>y. if (y = x) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P x else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (y = x) then P y else Q y) s = sum Q s"
    and "sum (\<lambda>y. if (x = y) then P y else Q y) s = sum Q s"
  by sorry

lemma span_substd_basis:
  assumes d: "d \<subseteq> Basis"
  shows "span d = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  (is "_ = ?B")
  by sorry

lemma basis_to_substdbasis_subspace_isomorphism:
  fixes B :: "'a::euclidean_space set"
  assumes "independent B"
  shows "\<exists>f d::'a set. card d = card B \<and> linear f \<and> f ` B = d \<and>
    f ` span B = {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} \<and> inj_on f (span B) \<and> d \<subseteq> Basis"
  by sorry

subsection \<open>Affine set and affine hull\<close>

definition\<^marker>\<open>tag important\<close> affine :: "'a::real_vector set \<Rightarrow> bool"
  where "affine S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u v. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> S)"

lemma affine_alt: "affine S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>u::real. (1 - u) *\<^sub>R x + u *\<^sub>R y \<in> S)"
  by sorry

lemma affine_empty [iff]: "affine {}"
  by sorry

lemma affine_sing [iff]: "affine {x}"
  by sorry

lemma affine_UNIV [iff]: "affine UNIV"
  by sorry

lemma affine_Inter [intro]: "(\<And>S. S\<in>\<F> \<Longrightarrow> affine S) \<Longrightarrow> affine (\<Inter>\<F>)"
  by sorry

lemma affine_Int[intro]: "affine S \<Longrightarrow> affine T \<Longrightarrow> affine (S \<inter> T)"
  by sorry

lemma affine_scaling: "affine S \<Longrightarrow> affine ((*\<^sub>R) c ` S)"
  by sorry

lemma affine_affine_hull [simp]: "affine(affine hull S)"
  by sorry

lemma affine_hull_eq[simp]: "(affine hull s = s) \<longleftrightarrow> affine s"
  by sorry

lemma affine_hyperplane: "affine {x. a \<bullet> x = b}"
  by sorry


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Some explicit formulations\<close>

text "Formalized by Lars Schewe."

lemma affine:
  fixes V::"'a::real_vector set"
  shows "affine V \<longleftrightarrow>
         (\<forall>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> V \<and> sum u S = 1 \<longrightarrow> (\<Sum>x\<in>S. u x *\<^sub>R x) \<in> V)"
  by sorry


lemma affine_hull_explicit:
  "affine hull p = {y. \<exists>S u. finite S \<and> S \<noteq> {} \<and> S \<subseteq> p \<and> sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  (is "_ = ?rhs")
  by sorry

lemma affine_hull_finite:
  assumes "finite S"
  shows "affine hull S = {y. \<exists>u. sum u S = 1 \<and> sum (\<lambda>v. u v *\<^sub>R v) S = y}"
  by sorry


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Stepping theorems and hence small special cases\<close>

lemma affine_hull_empty[simp]: "affine hull {} = {}"
  by sorry

lemma affine_hull_finite_step:
  fixes y :: "'a::real_vector"
  shows "finite S \<Longrightarrow>
      (\<exists>u. sum u (insert a S) = w \<and> sum (\<lambda>x. u x *\<^sub>R x) (insert a S) = y) \<longleftrightarrow>
      (\<exists>v u. sum u S = w - v \<and> sum (\<lambda>x. u x *\<^sub>R x) S = y - v *\<^sub>R a)" (is "_ \<Longrightarrow> ?lhs = ?rhs")
  by sorry

lemma affine_hull_2:
  fixes a b :: "'a::real_vector"
  shows "affine hull {a,b} = {u *\<^sub>R a + v *\<^sub>R b| u v. (u + v = 1)}"
  (is "?lhs = ?rhs")
  by sorry

lemma affine_hull_3:
  fixes a b c :: "'a::real_vector"
  shows "affine hull {a,b,c} = {u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c| u v w. u + v + w = 1}"
  by sorry

lemma mem_affine:
  assumes "affine S" "x \<in> S" "y \<in> S" "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<in> S"
  by sorry

lemma mem_affine_3:
  assumes "affine S" "x \<in> S" "y \<in> S" "z \<in> S" "u + v + w = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y + w *\<^sub>R z \<in> S"
  by sorry

lemma mem_affine_3_minus:
  assumes "affine S" "x \<in> S" "y \<in> S" "z \<in> S"
  shows "x + v *\<^sub>R (y-z) \<in> S"
  by sorry

corollary%unimportant mem_affine_3_minus2:
    "\<lbrakk>affine S; x \<in> S; y \<in> S; z \<in> S\<rbrakk> \<Longrightarrow> x - v *\<^sub>R (y-z) \<in> S"
  by sorry


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Some relations between affine hull and subspaces\<close>

lemma affine_hull_insert_subset_span:
  "affine hull (insert a S) \<subseteq> {a + v| v . v \<in> span {x - a | x . x \<in> S}}"
  by sorry

lemma affine_hull_insert_span:
  assumes "a \<notin> S"
  shows "affine hull (insert a S) = {a + v | v . v \<in> span {x - a | x.  x \<in> S}}"
  by sorry

lemma affine_hull_span:
  assumes "a \<in> S"
  shows "affine hull S = {a + v | v. v \<in> span {x - a | x. x \<in> S - {a}}}"
  by sorry


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Parallel affine sets\<close>

definition affine_parallel :: "'a::real_vector set \<Rightarrow> 'a::real_vector set \<Rightarrow> bool"
  where "affine_parallel S T \<longleftrightarrow> (\<exists>a. T = (\<lambda>x. a + x) ` S)"

lemma affine_parallel_expl_aux:
  fixes S T :: "'a::real_vector set"
  assumes "\<And>x. x \<in> S \<longleftrightarrow> a + x \<in> T"
  shows "T = (\<lambda>x. a + x) ` S"
  by sorry

lemma affine_parallel_expl: "affine_parallel S T \<longleftrightarrow> (\<exists>a. \<forall>x. x \<in> S \<longleftrightarrow> a + x \<in> T)"
  by sorry

lemma affine_parallel_reflex: "affine_parallel S S"
  by sorry

lemma affine_parallel_commute:
  assumes "affine_parallel A B"
  shows "affine_parallel B A"
  by sorry

lemma affine_parallel_assoc:
  assumes "affine_parallel A B"
    and "affine_parallel B C"
  shows "affine_parallel A C"
  by sorry

lemma affine_translation_aux:
  fixes a :: "'a::real_vector"
  assumes "affine ((\<lambda>x. a + x) ` S)"
  shows "affine S"
  by sorry

lemma affine_translation:
  "affine S \<longleftrightarrow> affine ((+) a ` S)" for a :: "'a::real_vector"
  by sorry

lemma parallel_is_affine:
  fixes S T :: "'a::real_vector set"
  assumes "affine S" "affine_parallel S T"
  shows "affine T"
  by sorry

lemma subspace_imp_affine: "subspace s \<Longrightarrow> affine s"
  by sorry

lemma affine_hull_subset_span: "(affine hull s) \<subseteq> (span s)"
  by sorry


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Subspace parallel to an affine set\<close>

lemma subspace_affine: "subspace S \<longleftrightarrow> affine S \<and> 0 \<in> S"
  by sorry

lemma affine_diffs_subspace:
  assumes "affine S" "a \<in> S"
  shows "subspace ((\<lambda>x. (-a)+x) ` S)"
  by sorry

lemma affine_diffs_subspace_subtract:
  "subspace ((\<lambda>x. x - a) ` S)" if "affine S" "a \<in> S"
  by sorry

lemma parallel_subspace_explicit:
  assumes "affine S"
    and "a \<in> S"
  assumes "L \<equiv> {y. \<exists>x \<in> S. (-a) + x = y}"
  shows "subspace L \<and> affine_parallel S L"
  by sorry

lemma parallel_subspace_aux:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A \<supseteq> B"
  by sorry

lemma parallel_subspace:
  assumes "subspace A"
    and "subspace B"
    and "affine_parallel A B"
  shows "A = B"
  by sorry

lemma affine_parallel_subspace:
  assumes "affine S" "S \<noteq> {}"
  shows "\<exists>!L. subspace L \<and> affine_parallel S L"
  by sorry


subsection \<open>Affine Dependence\<close>

text "Formalized by Lars Schewe."

definition\<^marker>\<open>tag important\<close> affine_dependent :: "'a::real_vector set \<Rightarrow> bool"
  where "affine_dependent S \<longleftrightarrow> (\<exists>x\<in>S. x \<in> affine hull (S - {x}))"

lemma affine_dependent_imp_dependent: "affine_dependent S \<Longrightarrow> dependent S"
  by sorry

lemma affine_dependent_subset:
   "\<lbrakk>affine_dependent S; S \<subseteq> T\<rbrakk> \<Longrightarrow> affine_dependent T"
  by sorry

lemma affine_independent_subset:
  shows "\<lbrakk>\<not> affine_dependent T; S \<subseteq> T\<rbrakk> \<Longrightarrow> \<not> affine_dependent S"
  by sorry

lemma affine_independent_Diff:
   "\<not> affine_dependent S \<Longrightarrow> \<not> affine_dependent(S - T)"
  by sorry

proposition affine_dependent_explicit:
  "affine_dependent p \<longleftrightarrow>
    (\<exists>S U. finite S \<and> S \<subseteq> p \<and> sum U S = 0 \<and> (\<exists>v\<in>S. U v \<noteq> 0) \<and> sum (\<lambda>v. U v *\<^sub>R v) S = 0)"
  by sorry

lemma affine_dependent_explicit_finite:
  fixes S :: "'a::real_vector set"
  assumes "finite S"
  shows "affine_dependent S \<longleftrightarrow>
    (\<exists>U. sum U S = 0 \<and> (\<exists>v\<in>S. U v \<noteq> 0) \<and> sum (\<lambda>v. U v *\<^sub>R v) S = 0)"
  (is "?lhs = ?rhs")
  by sorry

lemma dependent_imp_affine_dependent:
  assumes "dependent {x - a| x . x \<in> S}"
    and "a \<notin> S"
  shows "affine_dependent (insert a S)"
  by sorry

lemma affine_dependent_biggerset:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S" "card S \<ge> DIM('a) + 2"
  shows "affine_dependent S"
  by sorry

lemma affine_dependent_biggerset_general:
  assumes "finite (S :: 'a::euclidean_space set)"
    and "card S \<ge> dim S + 2"
  shows "affine_dependent S"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some Properties of Affine Dependent Sets\<close>

lemma affine_independent_0 [simp]: "\<not> affine_dependent {}"
  by sorry

lemma affine_independent_1 [simp]: "\<not> affine_dependent {a}"
  by sorry

lemma affine_independent_2 [simp]: "\<not> affine_dependent {a,b}"
  by sorry

lemma affine_hull_translation: "affine hull ((\<lambda>x. a + x) `  S) = (\<lambda>x. a + x) ` (affine hull S)"
  by sorry

lemma affine_dependent_translation:
  assumes "affine_dependent S"
  shows "affine_dependent ((\<lambda>x. a + x) ` S)"
  by sorry

lemma affine_dependent_translation_eq:
  "affine_dependent S \<longleftrightarrow> affine_dependent ((\<lambda>x. a + x) ` S)"
  by sorry

lemma affine_hull_0_dependent:
  assumes "0 \<in> affine hull S"
  shows "dependent S"
  by sorry

lemma affine_dependent_imp_dependent2:
  assumes "affine_dependent (insert 0 S)"
  shows "dependent S"
  by sorry

lemma affine_dependent_iff_dependent:
  assumes "a \<notin> S"
  shows "affine_dependent (insert a S) \<longleftrightarrow> dependent ((\<lambda>x. -a + x) ` S)"
  by sorry

lemma affine_dependent_iff_dependent2:
  assumes "a \<in> S"
  shows "affine_dependent S \<longleftrightarrow> dependent ((\<lambda>x. -a + x) ` (S-{a}))"
  by sorry

lemma affine_hull_insert_span_gen:
  "affine hull (insert a S) = (\<lambda>x. a + x) ` span ((\<lambda>x. - a + x) ` S)"
  by sorry

lemma affine_hull_span2:
  assumes "a \<in> S"
  shows "affine hull S = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` (S-{a}))"
  by sorry

lemma affine_hull_span_gen:
  assumes "a \<in> affine hull S"
  shows "affine hull S = (\<lambda>x. a+x) ` span ((\<lambda>x. -a+x) ` S)"
  by sorry

lemma affine_hull_span_0:
  assumes "0 \<in> affine hull S"
  shows "affine hull S = span S"
  by sorry

lemma extend_to_affine_basis_nonempty:
  fixes S V :: "'n::real_vector set"
  assumes "\<not> affine_dependent S" "S \<subseteq> V" "S \<noteq> {}"
  shows "\<exists>T. \<not> affine_dependent T \<and> S \<subseteq> T \<and> T \<subseteq> V \<and> affine hull T = affine hull V"
  by sorry

lemma affine_basis_exists:
  fixes V :: "'n::real_vector set"
  shows "\<exists>B. B \<subseteq> V \<and> \<not> affine_dependent B \<and> affine hull V = affine hull B"
  by sorry

proposition extend_to_affine_basis:
  fixes S V :: "'n::real_vector set"
  assumes "\<not> affine_dependent S" "S \<subseteq> V"
  obtains T where "\<not> affine_dependent T" "S \<subseteq> T" "T \<subseteq> V" "affine hull T = affine hull V"
  by sorry


subsection \<open>Affine Dimension of a Set\<close>

definition\<^marker>\<open>tag important\<close> aff_dim :: "('a::euclidean_space) set \<Rightarrow> int"
  where "aff_dim V =
  (SOME d :: int.
    \<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = d + 1)"

lemma aff_dim_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "\<exists>B. affine hull B = affine hull V \<and> \<not> affine_dependent B \<and> of_nat (card B) = aff_dim V + 1"
  by sorry

lemma affine_hull_eq_empty [simp]: "affine hull S = {} \<longleftrightarrow> S = {}"
  by sorry

lemma empty_eq_affine_hull[simp]: "{} = affine hull S \<longleftrightarrow> S = {}"
  by sorry

lemma aff_dim_parallel_subspace_aux:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B" "a \<in> B"
  shows "finite B \<and> ((card B) - 1 = dim (span ((\<lambda>x. -a+x) ` (B-{a}))))"
  by sorry

lemma aff_dim_parallel_subspace:
  fixes V L :: "'n::euclidean_space set"
  assumes "V \<noteq> {}"
    and "subspace L"
    and "affine_parallel (affine hull V) L"
  shows "aff_dim V = int (dim L)"
  by sorry

lemma aff_independent_finite:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B"
  shows "finite B"
  by sorry


lemma aff_dim_empty:
  fixes S :: "'n::euclidean_space set"
  shows "S = {} \<longleftrightarrow> aff_dim S = -1"
  by sorry

lemma aff_dim_empty_eq [simp]: "aff_dim ({}::'a::euclidean_space set) = -1"
  by sorry

lemma aff_dim_affine_hull [simp]: "aff_dim (affine hull S) = aff_dim S"
  by sorry

lemma aff_dim_affine_hull2:
  assumes "affine hull S = affine hull T"
  shows "aff_dim S = aff_dim T"
  by sorry

lemma aff_dim_unique:
  fixes B V :: "'n::euclidean_space set"
  assumes "affine hull B = affine hull V \<and> \<not> affine_dependent B"
  shows "of_nat (card B) = aff_dim V + 1"
  by sorry

lemma aff_dim_affine_independent:
  fixes B :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent B"
  shows "of_nat (card B) = aff_dim B + 1"
  by sorry

lemma affine_independent_iff_card:
    fixes S :: "'a::euclidean_space set"
    shows "\<not> affine_dependent S \<longleftrightarrow> finite S \<and> aff_dim S = int(card S) - 1" (is "?lhs = ?rhs")
  by sorry

lemma aff_dim_sing [simp]:
  fixes a :: "'n::euclidean_space"
  shows "aff_dim {a} = 0"
  by sorry

lemma aff_dim_2 [simp]:
  fixes a :: "'n::euclidean_space"
  shows "aff_dim {a,b} = (if a = b then 0 else 1)"
  by sorry

lemma aff_dim_inner_basis_exists:
  fixes V :: "('n::euclidean_space) set"
  shows "\<exists>B. B \<subseteq> V \<and> affine hull B = affine hull V \<and>
    \<not> affine_dependent B \<and> of_nat (card B) = aff_dim V + 1"
  by sorry

lemma aff_dim_le_card:
  fixes V :: "'n::euclidean_space set"
  assumes "finite V"
  shows "aff_dim V \<le> of_nat (card V) - 1"
  by sorry

lemma aff_dim_parallel_le:
  fixes S T :: "'n::euclidean_space set"
  assumes "affine_parallel (affine hull S) (affine hull T)"
  shows "aff_dim S \<le> aff_dim T"
  by sorry

lemma aff_dim_parallel_eq:
  fixes S T :: "'n::euclidean_space set"
  assumes "affine_parallel (affine hull S) (affine hull T)"
  shows "aff_dim S = aff_dim T"
  by sorry

lemma aff_dim_translation_eq:
  "aff_dim ((+) a ` S) = aff_dim S" for a :: "'n::euclidean_space"
  by sorry

lemma aff_dim_translation_eq_subtract:
  "aff_dim ((\<lambda>x. x - a) ` S) = aff_dim S" for a :: "'n::euclidean_space"
  by sorry

lemma aff_dim_affine:
  fixes S L :: "'n::euclidean_space set"
  assumes "affine S" "subspace L" "affine_parallel S L" "S \<noteq> {}"
  shows "aff_dim S = int (dim L)"
  by sorry

lemma dim_affine_hull [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "dim (affine hull S) = dim S"
  by sorry

lemma aff_dim_subspace:
  fixes S :: "'n::euclidean_space set"
  assumes "subspace S"
  shows "aff_dim S = int (dim S)"
  by sorry

lemma aff_dim_zero:
  fixes S :: "'n::euclidean_space set"
  assumes "0 \<in> affine hull S"
  shows "aff_dim S = int (dim S)"
  by sorry

lemma aff_dim_eq_dim:
  fixes S :: "'n::euclidean_space set"
  assumes "a \<in> affine hull S"
  shows "aff_dim S = int (dim ((+) (- a) ` S))" 
  by sorry

lemma aff_dim_eq_dim_subtract:
  fixes S :: "'n::euclidean_space set"
  assumes "a \<in> affine hull S"
  shows "aff_dim S = int (dim ((\<lambda>x. x - a) ` S))"
  by sorry

lemma aff_dim_UNIV [simp]: "aff_dim (UNIV :: 'n::euclidean_space set) = int(DIM('n))"
  by sorry

lemma aff_dim_geq:
  fixes V :: "'n::euclidean_space set"
  shows "aff_dim V \<ge> -1"
  by sorry

lemma aff_dim_negative_iff [simp]:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S < 0 \<longleftrightarrow> S = {}"
  by sorry

lemma aff_lowdim_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "aff_dim S < DIM('a)"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x = b}"
  by sorry

lemma affine_independent_card_dim_diffs:
  fixes S :: "'a :: euclidean_space set"
  assumes "\<not> affine_dependent S" "a \<in> S"
    shows "card S = dim ((\<lambda>x. x - a) ` S) + 1"
  by sorry

lemma independent_card_le_aff_dim:
  fixes B :: "'n::euclidean_space set"
  assumes "B \<subseteq> V"
  assumes "\<not> affine_dependent B"
  shows "int (card B) \<le> aff_dim V + 1"
  by sorry

lemma aff_dim_subset:
  fixes S T :: "'n::euclidean_space set"
  assumes "S \<subseteq> T"
  shows "aff_dim S \<le> aff_dim T"
  by sorry

lemma aff_dim_le_DIM:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S \<le> int (DIM('n))"
  by sorry

lemma affine_dim_equal:
  fixes S :: "'n::euclidean_space set"
  assumes "affine S" "affine T" "S \<noteq> {}" "S \<subseteq> T" "aff_dim S = aff_dim T"
  shows "S = T"
  by sorry

lemma aff_dim_eq_0:
  fixes S :: "'a::euclidean_space set"
  shows "aff_dim S = 0 \<longleftrightarrow> (\<exists>a. S = {a})"
  by sorry

lemma affine_hull_UNIV:
  fixes S :: "'n::euclidean_space set"
  assumes "aff_dim S = int(DIM('n))"
  shows "affine hull S = (UNIV :: ('n::euclidean_space) set)"
  by sorry

lemma disjoint_affine_hull:
  fixes S :: "'n::euclidean_space set"
  assumes "\<not> affine_dependent S" "T \<subseteq> S" "U \<subseteq> S" "T \<inter> U = {}"
    shows "(affine hull T) \<inter> (affine hull U) = {}"
  by sorry

end