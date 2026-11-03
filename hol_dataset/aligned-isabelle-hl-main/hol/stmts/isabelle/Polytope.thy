section \<open>Faces, Extreme Points, Polytopes, Polyhedra etc\<close>

text\<open>Ported from HOL Light by L C Paulson\<close>

theory Polytope
imports Cartesian_Euclidean_Space Path_Connected
begin

subsection \<open>Faces of a (usually convex) set\<close>

definition\<^marker>\<open>tag important\<close> face_of :: "['a::real_vector set, 'a set] \<Rightarrow> bool" (infixr \<open>(face'_of)\<close> 50)
  where
  "T face_of S \<longleftrightarrow>
        T \<subseteq> S \<and> convex T \<and>
        (\<forall>a \<in> S. \<forall>b \<in> S. \<forall>x \<in> T. x \<in> open_segment a b \<longrightarrow> a \<in> T \<and> b \<in> T)"

lemma face_ofD: "\<lbrakk>T face_of S; x \<in> open_segment a b; a \<in> S; b \<in> S; x \<in> T\<rbrakk> \<Longrightarrow> a \<in> T \<and> b \<in> T"
sorry

lemma face_of_translation_eq [simp]:
    "((+) a ` T face_of (+) a ` S) \<longleftrightarrow> T face_of S"
sorry

lemma face_of_linear_image:
  assumes "linear f" "inj f"
  shows "(f ` c face_of f ` S) \<longleftrightarrow> c face_of S"
sorry

lemma faces_of_linear_image:
   "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> {T. T face_of (f ` S)} = (image f) ` {T. T face_of S}"
sorry

lemma face_of_refl: "convex S \<Longrightarrow> S face_of S"
sorry

lemma face_of_refl_eq: "S face_of S \<longleftrightarrow> convex S"
sorry

lemma empty_face_of [iff]: "{} face_of S"
sorry

lemma face_of_empty [simp]: "S face_of {} \<longleftrightarrow> S = {}"
sorry

lemma face_of_trans [trans]: "\<lbrakk>S face_of T; T face_of u\<rbrakk> \<Longrightarrow> S face_of u"
sorry

lemma face_of_face: "T face_of S \<Longrightarrow> (f face_of T \<longleftrightarrow> f face_of S \<and> f \<subseteq> T)"
sorry

lemma face_of_subset: "\<lbrakk>F face_of S; F \<subseteq> T; T \<subseteq> S\<rbrakk> \<Longrightarrow> F face_of T"
sorry

lemma face_of_slice: "\<lbrakk>F face_of S; convex T\<rbrakk> \<Longrightarrow> (F \<inter> T) face_of (S \<inter> T)"
sorry

lemma face_of_Int: "\<lbrakk>t1 face_of S; t2 face_of S\<rbrakk> \<Longrightarrow> (t1 \<inter> t2) face_of S"
sorry

lemma face_of_Inter: "\<lbrakk>A \<noteq> {}; \<And>T. T \<in> A \<Longrightarrow> T face_of S\<rbrakk> \<Longrightarrow> (\<Inter> A) face_of S"
sorry

lemma face_of_Int_Int: "\<lbrakk>F face_of T; F' face_of t'\<rbrakk> \<Longrightarrow> (F \<inter> F') face_of (T \<inter> t')"
sorry

lemma face_of_imp_subset: "T face_of S \<Longrightarrow> T \<subseteq> S"
sorry

proposition face_of_imp_eq_affine_Int:
  fixes S :: "'a::euclidean_space set"
  assumes S: "convex S"  and T: "T face_of S"
  shows "T = (affine hull T) \<inter> S"
sorry

lemma face_of_imp_closed:
     fixes S :: "'a::euclidean_space set"
     assumes "convex S" "closed S" "T face_of S" shows "closed T"
sorry

lemma face_of_Int_supporting_hyperplane_le_strong:
    assumes "convex(S \<inter> {x. a \<bullet> x = b})" and aleb: "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b"
      shows "(S \<inter> {x. a \<bullet> x = b}) face_of S"
sorry

lemma face_of_Int_supporting_hyperplane_ge_strong:
   "\<lbrakk>convex(S \<inter> {x. a \<bullet> x = b}); \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk>
    \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
sorry

lemma face_of_Int_supporting_hyperplane_le:
    "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
sorry

lemma face_of_Int_supporting_hyperplane_ge:
    "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
sorry

lemma face_of_imp_convex: "T face_of S \<Longrightarrow> convex T"
sorry

lemma face_of_imp_compact:
    fixes S :: "'a::euclidean_space set"
    shows "\<lbrakk>convex S; compact S; T face_of S\<rbrakk> \<Longrightarrow> compact T"
sorry

lemma face_of_Int_subface:
     "\<lbrakk>A \<inter> B face_of A; A \<inter> B face_of B; C face_of A; D face_of B\<rbrakk>
      \<Longrightarrow> (C \<inter> D) face_of C \<and> (C \<inter> D) face_of D"
sorry

lemma subset_of_face_of:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "u \<subseteq> S" "T \<inter> (rel_interior u) \<noteq> {}"
      shows "u \<subseteq> T"
sorry

lemma face_of_eq:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "U face_of S" "(rel_interior T) \<inter> (rel_interior U) \<noteq> {}"
    shows "T = U"
sorry

lemma face_of_disjoint_rel_interior:
      fixes S :: "'a::real_normed_vector set"
      assumes "T face_of S" "T \<noteq> S"
        shows "T \<inter> rel_interior S = {}"
sorry

lemma face_of_disjoint_interior:
      fixes S :: "'a::real_normed_vector set"
      assumes "T face_of S" "T \<noteq> S"
        shows "T \<inter> interior S = {}"
sorry

lemma face_of_subset_rel_boundary:
  fixes S :: "'a::real_normed_vector set"
  assumes "T face_of S" "T \<noteq> S"
    shows "T \<subseteq> (S - rel_interior S)"
sorry

lemma face_of_subset_rel_frontier:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "T \<noteq> S"
      shows "T \<subseteq> rel_frontier S"
sorry

lemma face_of_aff_dim_lt:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "T face_of S" "T \<noteq> S"
    shows "aff_dim T < aff_dim S"
sorry

lemma subset_of_face_of_affine_hull:
    fixes S :: "'a::euclidean_space set"
  assumes T: "T face_of S" and "convex S" "U \<subseteq> S" and dis: "\<not> disjnt (affine hull T) (rel_interior U)"
  shows "U \<subseteq> T"
sorry

lemma affine_hull_face_of_disjoint_rel_interior:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "F face_of S" "F \<noteq> S"
  shows "affine hull F \<inter> rel_interior S = {}"
sorry

lemma affine_diff_divide:
    assumes "affine S" "k \<noteq> 0" "k \<noteq> 1" and xy: "x \<in> S" "y /\<^sub>R (1 - k) \<in> S"
      shows "(x - y) /\<^sub>R k \<in> S"
sorry

proposition face_of_conic:
  assumes "conic S" "f face_of S"
  shows "conic f"
sorry

proposition face_of_convex_hulls:
      assumes S: "finite S" "T \<subseteq> S" and disj: "affine hull T \<inter> convex hull (S - T) = {}"
      shows  "(convex hull T) face_of (convex hull S)"
sorry

proposition face_of_convex_hull_insert:
  assumes "finite S" "a \<notin> affine hull S" and T: "T face_of convex hull S"
  shows "T face_of convex hull insert a S"
sorry

proposition face_of_affine_trivial:
    assumes "affine S" "T face_of S"
    shows "T = {} \<or> T = S"
sorry

lemma face_of_affine_eq:
   "affine S \<Longrightarrow> (T face_of S \<longleftrightarrow> T = {} \<or> T = S)"
sorry

proposition Inter_faces_finite_altbound:
    fixes T :: "'a::euclidean_space set set"
    assumes cfaI: "\<And>c. c \<in> T \<Longrightarrow> c face_of S"
    shows "\<exists>F'. finite F' \<and> F' \<subseteq> T \<and> card F' \<le> DIM('a) + 2 \<and> \<Inter>F' = \<Inter>T"
sorry

lemma faces_of_translation:
   "{F. F face_of (+) a ` S} = (image ((+) a)) ` {F. F face_of S}"
sorry

proposition face_of_Times:
  assumes "F face_of S" and "F' face_of S'"
    shows "(F \<times> F') face_of (S \<times> S')"
sorry

corollary face_of_Times_decomp:
    fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
    shows "C face_of (S \<times> S') \<longleftrightarrow> (\<exists>F F'. F face_of S \<and> F' face_of S' \<and> C = F \<times> F')"
     (is "?lhs = ?rhs")
sorry

lemma face_of_Times_eq:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  shows "(F \<times> F') face_of (S \<times> S') \<longleftrightarrow> F = {} \<or> F' = {} \<or> F face_of S \<and> F' face_of S'"
sorry

lemma hyperplane_face_of_halfspace_le: "{x. a \<bullet> x = b} face_of {x. a \<bullet> x \<le> b}"
sorry

lemma hyperplane_face_of_halfspace_ge: "{x. a \<bullet> x = b} face_of {x. a \<bullet> x \<ge> b}"
sorry

lemma face_of_halfspace_le:
  fixes a :: "'n::euclidean_space"
  shows "F face_of {x. a \<bullet> x \<le> b} \<longleftrightarrow> F = {} \<or> F = {x. a \<bullet> x = b} \<or> F = {x. a \<bullet> x \<le> b}"
     (is "?lhs = ?rhs")
sorry

lemma face_of_halfspace_ge:
  fixes a :: "'n::euclidean_space"
  shows "F face_of {x. a \<bullet> x \<ge> b} \<longleftrightarrow> F = {} \<or> F = {x. a \<bullet> x = b} \<or> F = {x. a \<bullet> x \<ge> b}"
sorry

subsection\<open>Exposed faces\<close>

text\<open>That is, faces that are intersection with supporting hyperplane\<close>

definition\<^marker>\<open>tag important\<close> exposed_face_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"
                               (infixr \<open>(exposed'_face'_of)\<close> 50)
  where "T exposed_face_of S \<longleftrightarrow>
         T face_of S \<and> (\<exists>a b. S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b})"

lemma empty_exposed_face_of [iff]: "{} exposed_face_of S"
sorry

lemma exposed_face_of_refl_eq [simp]: "S exposed_face_of S \<longleftrightarrow> convex S"
sorry

lemma exposed_face_of_refl: "convex S \<Longrightarrow> S exposed_face_of S"
sorry

lemma exposed_face_of:
    "T exposed_face_of S \<longleftrightarrow>
     T face_of S \<and> (T = {} \<or> T = S \<or>
      (\<exists>a b. a \<noteq> 0 \<and> S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b}))"
     (is "?lhs = ?rhs")
sorry

lemma exposed_face_of_Int_supporting_hyperplane_le:
  "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) exposed_face_of S"
sorry

lemma exposed_face_of_Int_supporting_hyperplane_ge:
  "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) exposed_face_of S"
sorry

proposition exposed_face_of_Int:
  assumes "T exposed_face_of S"
      and "U exposed_face_of S"
    shows "(T \<inter> U) exposed_face_of S"
sorry

proposition exposed_face_of_Inter:
    fixes P :: "'a::euclidean_space set set"
  assumes "P \<noteq> {}"
      and "\<And>T. T \<in> P \<Longrightarrow> T exposed_face_of S"
    shows "\<Inter>P exposed_face_of S"
sorry

proposition exposed_face_of_sums:
  assumes "convex S" and "convex T"
      and "F exposed_face_of {x + y | x y. x \<in> S \<and> y \<in> T}"
          (is "F exposed_face_of ?ST")
  obtains k l
    where "k exposed_face_of S" "l exposed_face_of T"
          "F = {x + y | x y. x \<in> k \<and> y \<in> l}"
sorry

proposition exposed_face_of_parallel:
   "T exposed_face_of S \<longleftrightarrow>
         T face_of S \<and>
         (\<exists>a b. S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b} \<and>
                (T \<noteq> {} \<longrightarrow> T \<noteq> S \<longrightarrow> a \<noteq> 0) \<and>
                (T \<noteq> S \<longrightarrow> (\<forall>w \<in> affine hull S. (w + a) \<in> affine hull S)))"
  (is "?lhs = ?rhs")
sorry


subsection\<open>Extreme points of a set: its singleton faces\<close>

definition\<^marker>\<open>tag important\<close> extreme_point_of :: "['a::real_vector, 'a set] \<Rightarrow> bool"
                               (infixr \<open>(extreme'_point'_of)\<close> 50)
  where "x extreme_point_of S \<longleftrightarrow>
         x \<in> S \<and> (\<forall>a \<in> S. \<forall>b \<in> S. x \<notin> open_segment a b)"

lemma extreme_point_of_stillconvex:
   "convex S \<Longrightarrow> (x extreme_point_of S \<longleftrightarrow> x \<in> S \<and> convex(S - {x}))"
sorry

lemma face_of_singleton:
  "{x} face_of S \<longleftrightarrow> x extreme_point_of S"
sorry

lemma extreme_point_not_in_REL_INTERIOR:
    fixes S :: "'a::real_normed_vector set"
    shows "\<lbrakk>x extreme_point_of S; S \<noteq> {x}\<rbrakk> \<Longrightarrow> x \<notin> rel_interior S"
sorry

lemma extreme_point_not_in_interior:
  fixes S :: "'a::{real_normed_vector, perfect_space} set"
  assumes "x extreme_point_of S" shows "x \<notin> interior S"
sorry

lemma extreme_point_of_face:
     "F face_of S \<Longrightarrow> v extreme_point_of F \<longleftrightarrow> v extreme_point_of S \<and> v \<in> F"
sorry

lemma extreme_point_of_convex_hull:
  "x extreme_point_of (convex hull S) \<Longrightarrow> x \<in> S"
sorry

proposition extreme_points_of_convex_hull:
   "{x. x extreme_point_of (convex hull S)} \<subseteq> S"
sorry

lemma extreme_point_of_empty [simp]: "\<not> (x extreme_point_of {})"
sorry

lemma extreme_point_of_singleton [iff]: "x extreme_point_of {a} \<longleftrightarrow> x = a"
sorry

lemma extreme_point_of_translation_eq:
   "(a + x) extreme_point_of (image (\<lambda>x. a + x) S) \<longleftrightarrow> x extreme_point_of S"
sorry

lemma extreme_points_of_translation:
   "{x. x extreme_point_of (image (\<lambda>x. a + x) S)} =
    (\<lambda>x. a + x) ` {x. x extreme_point_of S}"
sorry

lemma extreme_points_of_translation_subtract:
   "{x. x extreme_point_of (image (\<lambda>x. x - a) S)} =
    (\<lambda>x. x - a) ` {x. x extreme_point_of S}"
sorry

lemma extreme_point_of_Int:
  "\<lbrakk>x extreme_point_of S; x extreme_point_of T\<rbrakk> \<Longrightarrow> x extreme_point_of (S \<inter> T)"
sorry

lemma extreme_point_of_Int_supporting_hyperplane_le:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> c extreme_point_of S"
sorry

lemma extreme_point_of_Int_supporting_hyperplane_ge:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> c extreme_point_of S"
sorry

lemma exposed_point_of_Int_supporting_hyperplane_le:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> {c} exposed_face_of S"
sorry

lemma exposed_point_of_Int_supporting_hyperplane_ge:
  "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> {c} exposed_face_of S"
sorry

lemma extreme_point_of_convex_hull_insert:
  assumes "finite S" "a \<notin> convex hull S"
  shows "a extreme_point_of (convex hull (insert a S))"
sorry

lemma extreme_point_of_conic:
  assumes "conic S" and x: "x extreme_point_of S"
  shows "x = 0"
sorry

subsection\<open>Facets\<close>

definition\<^marker>\<open>tag important\<close> facet_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"
                    (infixr \<open>(facet'_of)\<close> 50)
  where "F facet_of S \<longleftrightarrow> F face_of S \<and> F \<noteq> {} \<and> aff_dim F = aff_dim S - 1"

lemma facet_of_empty [simp]: "\<not> S facet_of {}"
sorry

lemma facet_of_irrefl [simp]: "\<not> S facet_of S "
sorry

lemma facet_of_imp_face_of: "F facet_of S \<Longrightarrow> F face_of S"
sorry

lemma facet_of_imp_subset: "F facet_of S \<Longrightarrow> F \<subseteq> S"
sorry

lemma hyperplane_facet_of_halfspace_le:
  "a \<noteq> 0 \<Longrightarrow> {x. a \<bullet> x = b} facet_of {x. a \<bullet> x \<le> b}"
sorry

lemma hyperplane_facet_of_halfspace_ge:
  "a \<noteq> 0 \<Longrightarrow> {x. a \<bullet> x = b} facet_of {x. a \<bullet> x \<ge> b}"
sorry

lemma facet_of_halfspace_le:
    "F facet_of {x. a \<bullet> x \<le> b} \<longleftrightarrow> a \<noteq> 0 \<and> F = {x. a \<bullet> x = b}"
    (is "?lhs = ?rhs")
sorry

lemma facet_of_halfspace_ge:
  "F facet_of {x. a \<bullet> x \<ge> b} \<longleftrightarrow> a \<noteq> 0 \<and> F = {x. a \<bullet> x = b}"
sorry

subsection \<open>Edges: faces of affine dimension 1\<close> (*FIXME too small subsection, rearrange? *)

definition\<^marker>\<open>tag important\<close> edge_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"  (infixr \<open>(edge'_of)\<close> 50)
  where "e edge_of S \<longleftrightarrow> e face_of S \<and> aff_dim e = 1"

lemma edge_of_imp_subset:
   "S edge_of T \<Longrightarrow> S \<subseteq> T"
sorry

subsection\<open>Existence of extreme points\<close>

proposition different_norm_3_collinear_points:
  fixes a :: "'a::euclidean_space"
  assumes "x \<in> open_segment a b" "norm(a) = norm(b)" "norm(x) = norm(b)"
  shows False
sorry

proposition extreme_point_exists_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S" "S \<noteq> {}"
  obtains x where "x extreme_point_of S"
sorry

subsection\<open>Krein-Milman, the weaker form\<close>

proposition Krein_Milman:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S"
    shows "S = closure(convex hull {x. x extreme_point_of S})"
sorry

text\<open>Now the sharper form.\<close>

lemma Krein_Milman_Minkowski_aux:
  fixes S :: "'a::euclidean_space set"
  assumes n: "dim S = n" and S: "compact S" "convex S" "0 \<in> S"
    shows "0 \<in> convex hull {x. x extreme_point_of S}"
sorry

theorem Krein_Milman_Minkowski:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S"
    shows "S = convex hull {x. x extreme_point_of S}"
sorry


subsection\<open>Applying it to convex hulls of explicitly indicated finite sets\<close>

corollary Krein_Milman_polytope:
  fixes S :: "'a::euclidean_space set"
  shows
   "finite S
       \<Longrightarrow> convex hull S =
           convex hull {x. x extreme_point_of (convex hull S)}"
sorry

lemma extreme_points_of_convex_hull_eq:
  fixes S :: "'a::euclidean_space set"
  shows
    "\<lbrakk>compact S; \<And>T. T \<subset> S \<Longrightarrow> convex hull T \<noteq> convex hull S\<rbrakk>
        \<Longrightarrow> {x. x extreme_point_of (convex hull S)} = S"
sorry

lemma extreme_point_of_convex_hull_eq:
  fixes S :: "'a::euclidean_space set"
  shows
   "\<lbrakk>compact S; \<And>T. T \<subset> S \<Longrightarrow> convex hull T \<noteq> convex hull S\<rbrakk>
    \<Longrightarrow> (x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
sorry

lemma extreme_point_of_convex_hull_convex_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and S: "\<And>a. a \<in> S \<Longrightarrow> a \<notin> convex hull (S - {a})"
  shows "(x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
sorry

lemma extreme_point_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  shows
   "\<not> affine_dependent S
         \<Longrightarrow> (x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
sorry
text\<open>Elementary proofs exist, not requiring Euclidean spaces and all this development\<close>
lemma extreme_point_of_convex_hull_2:
  fixes x :: "'a::euclidean_space"
  shows "x extreme_point_of (convex hull {a,b}) \<longleftrightarrow> x = a \<or> x = b"
sorry

lemma extreme_point_of_segment:
  fixes x :: "'a::euclidean_space"
  shows "x extreme_point_of closed_segment a b \<longleftrightarrow> x = a \<or> x = b"
sorry

lemma face_of_convex_hull_subset:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and T: "T face_of (convex hull S)"
  obtains S' where "S' \<subseteq> S" "T = convex hull S'"
sorry

lemma face_of_convex_hull_aux:
  assumes eq: "x *\<^sub>R p = u *\<^sub>R a + v *\<^sub>R b + w *\<^sub>R c"
    and x: "u + v + w = x" "x \<noteq> 0" and S: "affine S" "a \<in> S" "b \<in> S" "c \<in> S"
  shows "p \<in> S"
sorry

proposition face_of_convex_hull_insert_eq:
  fixes a :: "'a :: euclidean_space"
  assumes "finite S" and a: "a \<notin> affine hull S"
  shows "(F face_of (convex hull (insert a S)) \<longleftrightarrow>
          F face_of (convex hull S) \<or>
          (\<exists>F'. F' face_of (convex hull S) \<and> F = convex hull (insert a F')))"
         (is "F face_of ?CAS \<longleftrightarrow> _")
sorry

lemma face_of_convex_hull_insert2:
  fixes a :: "'a :: euclidean_space"
  assumes S: "finite S" and a: "a \<notin> affine hull S" and F: "F face_of convex hull S"
  shows "convex hull (insert a F) face_of convex hull (insert a S)"
sorry

proposition face_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
    shows "(T face_of (convex hull S) \<longleftrightarrow> (\<exists>c. c \<subseteq> S \<and> T = convex hull c))"
          (is "?lhs = ?rhs")
sorry

lemma facet_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
    shows "T facet_of (convex hull S) \<longleftrightarrow>
           T \<noteq> {} \<and> (\<exists>u. u \<in> S \<and> T = convex hull (S - {u}))"
          (is "?lhs = ?rhs")
sorry

lemma facet_of_convex_hull_affine_independent_alt:
  fixes S :: "'a::euclidean_space set"
  assumes "\<not> affine_dependent S"
  shows "(T facet_of (convex hull S) \<longleftrightarrow> 2 \<le> card S \<and> (\<exists>u. u \<in> S \<and> T = convex hull (S - {u})))"
        (is "?lhs = ?rhs")
sorry

lemma segment_face_of:
  assumes "(closed_segment a b) face_of S"
  shows "a extreme_point_of S" "b extreme_point_of S"
sorry

proposition Krein_Milman_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "compact S"
    shows "S = convex hull (frontier S)"
          (is "?lhs = ?rhs")
sorry

subsection\<open>Polytopes\<close>

definition\<^marker>\<open>tag important\<close> polytope where
 "polytope S \<equiv> \<exists>v. finite v \<and> S = convex hull v"

lemma polytope_translation_eq: "polytope ((+) a ` S) \<longleftrightarrow> polytope S"
sorry

lemma polytope_linear_image: "\<lbrakk>linear f; polytope p\<rbrakk> \<Longrightarrow> polytope(image f p)"
sorry

lemma polytope_empty: "polytope {}"
sorry

lemma polytope_convex_hull: "finite S \<Longrightarrow> polytope(convex hull S)"
sorry

lemma polytope_Times: "\<lbrakk>polytope S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<times> T)"
sorry

lemma face_of_polytope_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>polytope S; F face_of S\<rbrakk> \<Longrightarrow> polytope F"
sorry

lemma finite_polytope_faces:
  fixes S :: "'a::euclidean_space set"
  assumes "polytope S"
  shows "finite {F. F face_of S}"
sorry

lemma finite_polytope_facets:
  assumes "polytope S"
  shows "finite {T. T facet_of S}"
sorry

lemma polytope_scaling:
  assumes "polytope S"  shows "polytope (image (\<lambda>x. c *\<^sub>R x) S)"
sorry

lemma polytope_imp_compact:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> compact S"
sorry

lemma polytope_imp_convex: "polytope S \<Longrightarrow> convex S"
sorry

lemma polytope_imp_closed:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> closed S"
sorry

lemma polytope_imp_bounded:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> bounded S"
sorry

lemma polytope_interval: "polytope(cbox a b)"
sorry

lemma polytope_sing: "polytope {a}"
sorry

lemma face_of_polytope_insert:
     "\<lbrakk>polytope S; a \<notin> affine hull S; F face_of S\<rbrakk> \<Longrightarrow> F face_of convex hull (insert a S)"
sorry

proposition face_of_polytope_insert2:
  fixes a :: "'a :: euclidean_space"
  assumes "polytope S" "a \<notin> affine hull S" "F face_of S"
  shows "convex hull (insert a F) face_of convex hull (insert a S)"
sorry


subsection\<open>Polyhedra\<close>

definition\<^marker>\<open>tag important\<close> polyhedron where
 "polyhedron S \<equiv>
        \<exists>F. finite F \<and>
            S = \<Inter> F \<and>
            (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b})"

lemma polyhedron_Int [intro,simp]:
   "\<lbrakk>polyhedron S; polyhedron T\<rbrakk> \<Longrightarrow> polyhedron (S \<inter> T)"
sorry

lemma polyhedron_UNIV [iff]: "polyhedron UNIV"
sorry

lemma polyhedron_Inter [intro,simp]:
  "\<lbrakk>finite F; \<And>S. S \<in> F \<Longrightarrow> polyhedron S\<rbrakk> \<Longrightarrow> polyhedron(\<Inter>F)"
sorry

lemma polyhedron_empty [iff]: "polyhedron ({} :: 'a :: euclidean_space set)"
sorry

lemma polyhedron_halfspace_le:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x \<le> b}"
sorry

lemma polyhedron_halfspace_ge:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x \<ge> b}"
sorry

lemma polyhedron_hyperplane:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x = b}"
sorry

lemma affine_imp_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "affine S \<Longrightarrow> polyhedron S"
sorry

lemma polyhedron_imp_closed:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> closed S"
sorry

lemma polyhedron_imp_convex:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> convex S"
sorry

lemma polyhedron_affine_hull:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron(affine hull S)"
sorry
subsection\<open>Canonical polyhedron representation making facial structure explicit\<close>

proposition polyhedron_Int_affine:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
           (\<exists>F. finite F \<and> S = (affine hull S) \<inter> \<Inter>F \<and>
                (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}))"
sorry

proposition rel_interior_polyhedron_explicit:
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
    shows "rel_interior S = {x \<in> S. \<forall>h \<in> F. a h \<bullet> x < b h}"
sorry

lemma polyhedron_Int_affine_parallel:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and>
              S = (affine hull S) \<inter> (\<Inter>F) \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)))"
    (is "?lhs = ?rhs")
sorry

proposition polyhedron_Int_affine_parallel_minimal:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and>
              S = (affine hull S) \<inter> (\<Inter>F) \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)) \<and>
              (\<forall>F'. F' \<subset> F \<longrightarrow> S \<subset> (affine hull S) \<inter> (\<Inter>F')))"
    (is "?lhs = ?rhs")
sorry

lemma polyhedron_Int_affine_minimal:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and> S = (affine hull S) \<inter> \<Inter>F \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}) \<and>
              (\<forall>F'. F' \<subset> F \<longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'))"
sorry

proposition facet_of_polyhedron_explicit:
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
    shows "C facet_of S \<longleftrightarrow> (\<exists>h. h \<in> F \<and> C = S \<inter> {x. a h \<bullet> x = b h})"
sorry

lemma face_of_polyhedron_subset_explicit:
  fixes S :: "'a :: euclidean_space set"
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
      and C: "C face_of S" and "C \<noteq> {}" "C \<noteq> S"
   obtains h where "h \<in> F" "C \<subseteq> S \<inter> {x. a h \<bullet> x = b h}"
sorry

text\<open>Initial part of proof duplicates that above\<close>
proposition face_of_polyhedron_explicit:
  fixes S :: "'a :: euclidean_space set"
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
      and C: "C face_of S" and "C \<noteq> {}" "C \<noteq> S"
    shows "C = \<Inter>{S \<inter> {x. a h \<bullet> x = b h} | h. h \<in> F \<and> C \<subseteq> S \<inter> {x. a h \<bullet> x = b h}}"
sorry


subsection\<open>More general corollaries from the explicit representation\<close>

corollary facet_of_polyhedron:
  assumes "polyhedron S" and "C facet_of S"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x \<le> b}" "C = S \<inter> {x. a \<bullet> x = b}"
sorry

corollary face_of_polyhedron:
  assumes "polyhedron S" and "C face_of S" and "C \<noteq> {}" and "C \<noteq> S"
    shows "C = \<Inter>{F. F facet_of S \<and> C \<subseteq> F}"
sorry

lemma face_of_polyhedron_subset_facet:
  assumes "polyhedron S" and "C face_of S" and "C \<noteq> {}" and "C \<noteq> S"
  obtains F where "F facet_of S" "C \<subseteq> F"
sorry

lemma exposed_face_of_polyhedron:
  assumes "polyhedron S"
    shows "F exposed_face_of S \<longleftrightarrow> F face_of S"
sorry

lemma face_of_polyhedron_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S" "c face_of S" shows "polyhedron c"
sorry

lemma finite_polyhedron_faces:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "finite {F. F face_of S}"
sorry

lemma finite_polyhedron_exposed_faces:
   "polyhedron S \<Longrightarrow> finite {F. F exposed_face_of S}"
sorry

lemma finite_polyhedron_extreme_points:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S" shows "finite {v. v extreme_point_of S}"
sorry

lemma finite_polyhedron_facets:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> finite {F. F facet_of S}"
sorry

proposition rel_interior_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "rel_interior S = S - \<Union>{F. F facet_of S}"
sorry

lemma rel_boundary_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "S - rel_interior S = \<Union> {F. F facet_of S}"
sorry

lemma rel_frontier_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "rel_frontier S = \<Union> {F. F facet_of S}"
sorry

lemma rel_frontier_of_polyhedron_alt:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
  shows "rel_frontier S = \<Union> {F. F face_of S \<and> F \<noteq> S}"
sorry


text\<open>A characterization of polyhedra as having finitely many faces\<close>

proposition polyhedron_eq_finite_exposed_faces:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow> closed S \<and> convex S \<and> finite {F. F exposed_face_of S}"
         (is "?lhs = ?rhs")
sorry

corollary polyhedron_eq_finite_faces:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow> closed S \<and> convex S \<and> finite {F. F face_of S}"
         (is "?lhs = ?rhs")
sorry

lemma polyhedron_linear_image_eq:
  fixes h :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "linear h" "bij h"
    shows "polyhedron (h ` S) \<longleftrightarrow> polyhedron S"
sorry

lemma polyhedron_negations:
  fixes S :: "'a :: euclidean_space set"
  shows   "polyhedron S \<Longrightarrow> polyhedron(image uminus S)"
sorry
subsection\<open>Relation between polytopes and polyhedra\<close>

proposition polytope_eq_bounded_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "polytope S \<longleftrightarrow> polyhedron S \<and> bounded S"
         (is "?lhs = ?rhs")
sorry

lemma polytope_Int:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polytope S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
sorry

lemma polytope_Int_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polytope S; polyhedron T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
sorry

lemma polyhedron_Int_polytope:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polyhedron S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
sorry

lemma polytope_imp_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron S"
sorry

lemma polytope_facet_exists:
  fixes p :: "'a :: euclidean_space set"
  assumes "polytope p" "0 < aff_dim p"
  obtains F where "F facet_of p"
sorry

lemma polyhedron_interval [iff]: "polyhedron(cbox a b)"
sorry

lemma polyhedron_convex_hull:
  fixes S :: "'a :: euclidean_space set"
  shows "finite S \<Longrightarrow> polyhedron(convex hull S)"
sorry

subsection\<open>Relative and absolute frontier of a polytope\<close>

lemma rel_boundary_of_convex_hull:
    fixes S :: "'a::euclidean_space set"
    assumes "\<not> affine_dependent S"
      shows "(convex hull S) - rel_interior(convex hull S) = (\<Union>a\<in>S. convex hull (S - {a}))"
sorry

proposition frontier_of_convex_hull:
    fixes S :: "'a::euclidean_space set"
    assumes "card S = Suc (DIM('a))"
      shows "frontier(convex hull S) = \<Union> {convex hull (S - {a}) | a. a \<in> S}"
sorry

subsection\<open>Special case of a triangle\<close>

proposition frontier_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "frontier(convex hull {a,b,c}) = closed_segment a b \<union> closed_segment b c \<union> closed_segment c a"
          (is "?lhs = ?rhs")
sorry

corollary inside_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "inside (closed_segment a b \<union> closed_segment b c \<union> closed_segment c a) = interior(convex hull {a,b,c})"
sorry

corollary interior_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "interior(convex hull {a,b,c}) =
           convex hull {a,b,c} - (closed_segment a b \<union> closed_segment b c \<union> closed_segment c a)"
sorry

subsection\<open>Subdividing a cell complex\<close>

lemma subdivide_interval:
  fixes x::real
  assumes "a < \<bar>x - y\<bar>" "0 < a"
  obtains n where "n \<in> \<int>" "x < n * a \<and> n * a < y \<or> y <  n * a \<and> n * a < x"
sorry

lemma cell_subdivision_lemma:
  assumes "finite \<F>"
      and "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> d"
      and "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
      and "finite I"
    shows "\<exists>\<G>. \<Union>\<G> = \<Union>\<F> \<and>
                 finite \<G> \<and>
                 (\<forall>C \<in> \<G>. \<exists>D. D \<in> \<F> \<and> C \<subseteq> D) \<and>
                 (\<forall>C \<in> \<F>. \<forall>x \<in> C. \<exists>D. D \<in> \<G> \<and> x \<in> D \<and> D \<subseteq> C) \<and>
                 (\<forall>X \<in> \<G>. polytope X) \<and>
                 (\<forall>X \<in> \<G>. aff_dim X \<le> d) \<and>
                 (\<forall>X \<in> \<G>. \<forall>Y \<in> \<G>. X \<inter> Y face_of X) \<and>
                 (\<forall>X \<in> \<G>. \<forall>x \<in> X. \<forall>y \<in> X. \<forall>a b.
                          (a,b) \<in> I \<longrightarrow> a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or>
                                        a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b)"
sorry

proposition cell_complex_subdivision_exists:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "0 < e" "finite \<F>"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> d"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
  obtains "\<F>'" where "finite \<F>'" "\<Union>\<F>' = \<Union>\<F>" "\<And>X. X \<in> \<F>' \<Longrightarrow> diameter X < e"
                "\<And>X. X \<in> \<F>' \<Longrightarrow> polytope X" "\<And>X. X \<in> \<F>' \<Longrightarrow> aff_dim X \<le> d"
                "\<And>X Y. \<lbrakk>X \<in> \<F>'; Y \<in> \<F>'\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X"
                "\<And>C. C \<in> \<F>' \<Longrightarrow> \<exists>D. D \<in> \<F> \<and> C \<subseteq> D"
                "\<And>C x. C \<in> \<F> \<and> x \<in> C \<Longrightarrow> \<exists>D. D \<in> \<F>' \<and> x \<in> D \<and> D \<subseteq> C"
sorry


subsection\<open>Simplexes\<close>

text\<open>The notion of n-simplex for integer \<^term>\<open>n \<ge> -1\<close>\<close>

definition\<^marker>\<open>tag important\<close> simplex :: "int \<Rightarrow> 'a::euclidean_space set \<Rightarrow> bool" (infix \<open>simplex\<close> 50)
  where "n simplex S \<equiv> \<exists>C. \<not> affine_dependent C \<and> int(card C) = n + 1 \<and> S = convex hull C"

lemma simplex:
    "n simplex S \<longleftrightarrow> (\<exists>C. finite C \<and>
                       \<not> affine_dependent C \<and>
                       int(card C) = n + 1 \<and>
                       S = convex hull C)"
sorry

lemma simplex_convex_hull:
   "\<not> affine_dependent C \<and> int(card C) = n + 1 \<Longrightarrow> n simplex (convex hull C)"
sorry

lemma convex_simplex: "n simplex S \<Longrightarrow> convex S"
sorry

lemma compact_simplex: "n simplex S \<Longrightarrow> compact S"
sorry

lemma closed_simplex: "n simplex S \<Longrightarrow> closed S"
sorry

lemma simplex_imp_polytope:
   "n simplex S \<Longrightarrow> polytope S"
sorry

lemma simplex_imp_polyhedron:
   "n simplex S \<Longrightarrow> polyhedron S"
sorry

lemma simplex_dim_ge: "n simplex S \<Longrightarrow> -1 \<le> n"
sorry

lemma simplex_empty [simp]: "n simplex {} \<longleftrightarrow> n = -1"
sorry

lemma simplex_minus_1 [simp]: "-1 simplex S \<longleftrightarrow> S = {}"
sorry

lemma aff_dim_simplex:
   "n simplex S \<Longrightarrow> aff_dim S = n"
sorry

lemma zero_simplex_sing: "0 simplex {a}"
sorry

lemma simplex_sing [simp]: "n simplex {a} \<longleftrightarrow> n = 0"
sorry

lemma simplex_zero: "0 simplex S \<longleftrightarrow> (\<exists>a. S = {a})"
sorry

lemma one_simplex_segment: "a \<noteq> b \<Longrightarrow> 1 simplex closed_segment a b"
sorry

lemma simplex_segment_cases:
   "(if a = b then 0 else 1) simplex closed_segment a b"
sorry

lemma simplex_segment:
   "\<exists>n. n simplex closed_segment a b"
sorry

lemma polytope_lowdim_imp_simplex:
  assumes "polytope P" "aff_dim P \<le> 1"
  obtains n where "n simplex P"
sorry

lemma simplex_insert_dimplus1:
  fixes n::int
  assumes "n simplex S" and a: "a \<notin> affine hull S"
  shows "(n+1) simplex (convex hull (insert a S))"
sorry

subsection \<open>Simplicial complexes and triangulations\<close>

definition\<^marker>\<open>tag important\<close> simplicial_complex where
 "simplicial_complex \<C> \<equiv>
        finite \<C> \<and>
        (\<forall>S \<in> \<C>. \<exists>n. n simplex S) \<and>
        (\<forall>F S. S \<in> \<C> \<and> F face_of S \<longrightarrow> F \<in> \<C>) \<and>
        (\<forall>S S'. S \<in> \<C> \<and> S' \<in> \<C> \<longrightarrow> (S \<inter> S') face_of S)"

definition\<^marker>\<open>tag important\<close> triangulation where
 "triangulation \<T> \<equiv>
        finite \<T> \<and>
        (\<forall>T \<in> \<T>. \<exists>n. n simplex T) \<and>
        (\<forall>T T'. T \<in> \<T> \<and> T' \<in> \<T> \<longrightarrow> (T \<inter> T') face_of T)"


subsection\<open>Refining a cell complex to a simplicial complex\<close>

proposition convex_hull_insert_Int_eq:
  fixes z :: "'a :: euclidean_space"
  assumes z: "z \<in> rel_interior S"
      and T: "T \<subseteq> rel_frontier S"
      and U: "U \<subseteq> rel_frontier S"
      and "convex S" "convex T" "convex U"
  shows "convex hull (insert z T) \<inter> convex hull (insert z U) = convex hull (insert z (T \<inter> U))"
    (is "?lhs = ?rhs")
sorry

lemma simplicial_subdivision_aux:
  assumes "finite \<M>"
      and "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C \<le> of_nat n"
      and "\<And>C F. \<lbrakk>C \<in> \<M>; F face_of C\<rbrakk> \<Longrightarrow> F \<in> \<M>"
      and "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
    shows "\<exists>\<T>. simplicial_complex \<T> \<and>
                (\<forall>K \<in> \<T>. aff_dim K \<le> of_nat n) \<and>
                \<Union>\<T> = \<Union>\<M> \<and>
                (\<forall>C \<in> \<M>. \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F) \<and>
                (\<forall>K \<in> \<T>. \<exists>C. C \<in> \<M> \<and> K \<subseteq> C)"
sorry

lemma simplicial_subdivision_of_cell_complex_lowdim:
  assumes "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
      and aff: "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C \<le> d"
  obtains \<T> where "simplicial_complex \<T>" "\<And>K. K \<in> \<T> \<Longrightarrow> aff_dim K \<le> d"
                  "\<Union>\<T> = \<Union>\<M>"
                  "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> K \<subseteq> C"
sorry

proposition simplicial_subdivision_of_cell_complex:
  assumes "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
  obtains \<T> where "simplicial_complex \<T>"
                  "\<Union>\<T> = \<Union>\<M>"
                  "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> K \<subseteq> C"
sorry

corollary fine_simplicial_subdivision_of_cell_complex:
  assumes "0 < e" "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
  obtains \<T> where "simplicial_complex \<T>"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> diameter K < e"
                  "\<Union>\<T> = \<Union>\<M>"
                  "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> \<T> \<and> C = \<Union>F"
                  "\<And>K. K \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> K \<subseteq> C"
sorry

subsection\<open>Some results on cell division with full-dimensional cells only\<close>

lemma convex_Union_fulldim_cells:
  assumes "finite \<S>" and clo: "\<And>C. C \<in> \<S> \<Longrightarrow> closed C" and con: "\<And>C. C \<in> \<S> \<Longrightarrow> convex C"
      and eq: "\<Union>\<S> = U"and  "convex U"
 shows "\<Union>{C \<in> \<S>. aff_dim C = aff_dim U} = U"  (is "?lhs = U")
sorry

proposition fine_triangular_subdivision_of_cell_complex:
  assumes "0 < e" "finite \<M>"
      and poly: "\<And>C. C \<in> \<M> \<Longrightarrow> polytope C"
      and aff: "\<And>C. C \<in> \<M> \<Longrightarrow> aff_dim C = d"
      and face: "\<And>C1 C2. \<lbrakk>C1 \<in> \<M>; C2 \<in> \<M>\<rbrakk> \<Longrightarrow> C1 \<inter> C2 face_of C1"
  obtains \<T> where "triangulation \<T>" "\<And>k. k \<in> \<T> \<Longrightarrow> diameter k < e"
                 "\<And>k. k \<in> \<T> \<Longrightarrow> aff_dim k = d" "\<Union>\<T> = \<Union>\<M>"
                 "\<And>C. C \<in> \<M> \<Longrightarrow> \<exists>f. finite f \<and> f \<subseteq> \<T> \<and> C = \<Union>f"
                 "\<And>k. k \<in> \<T> \<Longrightarrow> \<exists>C. C \<in> \<M> \<and> k \<subseteq> C"
sorry

section \<open>Finitely generated cone is polyhedral, and hence closed\<close>

proposition polyhedron_convex_cone_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S"
  shows "polyhedron(convex_cone hull S)"
sorry

lemma closed_convex_cone_hull:
  fixes S :: "'a::euclidean_space set"
  shows "finite S \<Longrightarrow> closed(convex_cone hull S)"
sorry

lemma polyhedron_convex_cone_hull_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron(convex_cone hull S)"
sorry

lemma polyhedron_conic_hull_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron(conic hull S)"
sorry

lemma closed_conic_hull_strong:
  fixes S :: "'a::euclidean_space set"
  shows "0 \<in> rel_interior S \<or> polytope S \<or> compact S \<and> ~(0 \<in> S) \<Longrightarrow> closed(conic hull S)"
sorry

end
