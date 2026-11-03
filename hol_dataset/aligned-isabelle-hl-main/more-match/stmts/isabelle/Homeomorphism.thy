(*  Title:      HOL/Analysis/Homeomorphism.thy
    Author: LC Paulson (ported from HOL Light)
*)

section \<open>Homeomorphism Theorems\<close>

theory Homeomorphism
imports Homotopy
begin

lemma homeomorphic_spheres':
  fixes a ::"'a::euclidean_space" and b ::"'b::euclidean_space"
  assumes "0 < \<delta>" and dimeq: "DIM('a) = DIM('b)"
  shows "(sphere a \<delta>) homeomorphic (sphere b \<delta>)"
sorry

lemma homeomorphic_spheres_gen:
    fixes a :: "'a::euclidean_space" and b :: "'b::euclidean_space"
  assumes "0 < r" "0 < s" "DIM('a::euclidean_space) = DIM('b::euclidean_space)"
  shows "(sphere a r homeomorphic sphere b s)"
sorry

subsection \<open>Homeomorphism of all convex compact sets with nonempty interior\<close>

proposition
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and 0: "0 \<in> rel_interior S"
      and star: "\<And>x. x \<in> S \<Longrightarrow> open_segment 0 x \<subseteq> rel_interior S"
    shows starlike_compact_projective1_0:
            "S - rel_interior S homeomorphic sphere 0 1 \<inter> affine hull S"
            (is "?SMINUS homeomorphic ?SPHER")
      and starlike_compact_projective2_0:
            "S homeomorphic cball 0 1 \<inter> affine hull S"
            (is "S homeomorphic ?CBALL")
sorry

corollary
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and a: "a \<in> rel_interior S"
      and star: "\<And>x. x \<in> S \<Longrightarrow> open_segment a x \<subseteq> rel_interior S"
    shows starlike_compact_projective1:
            "S - rel_interior S homeomorphic sphere a 1 \<inter> affine hull S"
      and starlike_compact_projective2:
            "S homeomorphic cball a 1 \<inter> affine hull S"
sorry

corollary starlike_compact_projective_special:
  assumes "compact S"
    and cb01: "cball (0::'a::euclidean_space) 1 \<subseteq> S"
    and scale: "\<And>x u. \<lbrakk>x \<in> S; 0 \<le> u; u < 1\<rbrakk> \<Longrightarrow> u *\<^sub>R x \<in> S - frontier S"
  shows "S homeomorphic (cball (0::'a::euclidean_space) 1)"
sorry

lemma homeomorphic_convex_lemma:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "compact S" "convex T" "compact T"
      and affeq: "aff_dim S = aff_dim T"
    shows "(S - rel_interior S) homeomorphic (T - rel_interior T) \<and>
           S homeomorphic T"
sorry

lemma homeomorphic_convex_compact_sets:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "compact S" "convex T" "compact T"
      and affeq: "aff_dim S = aff_dim T"
    shows "S homeomorphic T"
sorry

lemma homeomorphic_rel_frontiers_convex_bounded_sets:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "convex S" "bounded S" "convex T" "bounded T"
      and affeq: "aff_dim S = aff_dim T"
    shows  "rel_frontier S homeomorphic rel_frontier T"
sorry

subsection\<open>Homeomorphisms between punctured spheres and affine sets\<close>
text\<open>Including the famous stereoscopic projection of the 3-D sphere to the complex plane\<close>

text\<open>The special case with centre 0 and radius 1\<close>
lemma homeomorphic_punctured_affine_sphere_affine_01:
  assumes "b \<in> sphere 0 1" "affine T" "0 \<in> T" "b \<in> T" "affine p"
      and affT: "aff_dim T = aff_dim p + 1"
    shows "(sphere 0 1 \<inter> T) - {b} homeomorphic p"
sorry

theorem homeomorphic_punctured_affine_sphere_affine:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" "b \<in> sphere a r" "affine T" "a \<in> T" "b \<in> T" "affine p"
      and aff: "aff_dim T = aff_dim p + 1"
    shows "(sphere a r \<inter> T) - {b} homeomorphic p"
sorry

corollary homeomorphic_punctured_sphere_affine:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" and b: "b \<in> sphere a r"
      and "affine T" and affS: "aff_dim T + 1 = DIM('a)"
    shows "(sphere a r - {b}) homeomorphic T"
sorry

corollary homeomorphic_punctured_sphere_hyperplane:
  fixes a :: "'a :: euclidean_space"
  assumes "0 < r" and b: "b \<in> sphere a r"
    and "c \<noteq> 0"
  shows "(sphere a r - {b}) homeomorphic {x::'a. c \<bullet> x = d}"
sorry

proposition homeomorphic_punctured_sphere_affine_gen:
  fixes a :: "'a :: euclidean_space"
  assumes "convex S" "bounded S" and a: "a \<in> rel_frontier S"
      and "affine T" and affS: "aff_dim S = aff_dim T + 1"
    shows "rel_frontier S - {a} homeomorphic T"
sorry


text\<open> When dealing with AR, ANR and ANR later, it's useful to know that every set
  is homeomorphic to a closed subset of a convex set, and
  if the set is locally compact we can take the convex set to be the universe.\<close>

proposition homeomorphic_closedin_convex:
  fixes S :: "'m::euclidean_space set"
  assumes "aff_dim S < DIM('n)"
  obtains U and T :: "'n::euclidean_space set"
     where "convex U" "U \<noteq> {}" "closedin (top_of_set U) T"
           "S homeomorphic T"
sorry

subsection\<open>Locally compact sets in an open set\<close>

text\<open> Locally compact sets are closed in an open set and are homeomorphic
  to an absolutely closed set if we have one more dimension to play with.\<close>

lemma locally_compact_open_Int_closure:
  fixes S :: "'a :: metric_space set"
  assumes "locally compact S"
  obtains T where "open T" "S = T \<inter> closure S"
sorry

lemma locally_compact_closedin_open:
    fixes S :: "'a :: metric_space set"
    assumes "locally compact S"
    obtains T where "open T" "closedin (top_of_set T) S"
sorry

lemma locally_compact_homeomorphism_projection_closed:
  assumes "locally compact S"
  obtains T and f :: "'a \<Rightarrow> 'a :: euclidean_space \<times> 'b :: euclidean_space"
  where "closed T" "homeomorphism S T f fst"
sorry

lemma locally_compact_closed_Int_open:
  fixes S :: "'a :: euclidean_space set"
  shows "locally compact S \<longleftrightarrow> (\<exists>U V. closed U \<and> open V \<and> S = U \<inter> V)" (is "?lhs = ?rhs")
sorry

lemma lowerdim_embeddings:
  assumes  "DIM('a) < DIM('b)"
  obtains f :: "'a::euclidean_space*real \<Rightarrow> 'b::euclidean_space" 
      and g :: "'b \<Rightarrow> 'a*real"
      and j :: 'b
  where "linear f" "linear g" "\<And>z. g (f z) = z" "j \<in> Basis" "\<And>x. f(x,0) \<bullet> j = 0"
sorry

proposition locally_compact_homeomorphic_closed:
  fixes S :: "'a::euclidean_space set"
  assumes "locally compact S" and dimlt: "DIM('a) < DIM('b)"
  obtains T :: "'b::euclidean_space set" where "closed T" "S homeomorphic T"
sorry

lemma homeomorphic_convex_compact_lemma:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S"
    and "compact S"
    and "cball 0 1 \<subseteq> S"
  shows "S homeomorphic (cball (0::'a) 1)"
sorry

proposition homeomorphic_convex_compact_cball:
  fixes e :: real
    and S :: "'a::euclidean_space set"
  assumes S: "convex S" "compact S" "interior S \<noteq> {}" and "e > 0"
  shows "S homeomorphic (cball (b::'a) e)"
sorry

corollary homeomorphic_convex_compact:
  fixes S :: "'a::euclidean_space set"
    and T :: "'a set"
  assumes "convex S" "compact S" "interior S \<noteq> {}"
    and "convex T" "compact T" "interior T \<noteq> {}"
  shows "S homeomorphic T"
sorry

lemma homeomorphic_closed_intervals:
  fixes a :: "'a::euclidean_space" and b and c :: "'a::euclidean_space" and d
  assumes "box a b \<noteq> {}" and "box c d \<noteq> {}"
    shows "(cbox a b) homeomorphic (cbox c d)"
sorry

lemma homeomorphic_closed_intervals_real:
  fixes a::real and b and c::real and d
  assumes "a<b" and "c<d"
  shows "{a..b} homeomorphic {c..d}"
sorry
subsection\<open>Covering spaces and lifting results for them\<close>

definition\<^marker>\<open>tag important\<close> covering_space
           :: "'a::topological_space set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
  where
  "covering_space c p S \<equiv>
       continuous_on c p \<and> p ` c = S \<and>
       (\<forall>x \<in> S. \<exists>T. x \<in> T \<and> openin (top_of_set S) T \<and>
                    (\<exists>v. \<Union>v = c \<inter> p -` T \<and>
                        (\<forall>u \<in> v. openin (top_of_set c) u) \<and>
                        pairwise disjnt v \<and>
                        (\<forall>u \<in> v. \<exists>q. homeomorphism u T p q)))"

lemma covering_spaceI [intro?]:
  assumes "continuous_on c p" "p ` c = S"
          "\<And>x. x \<in> S \<Longrightarrow> \<exists>T. x \<in> T \<and> openin (top_of_set S) T \<and>
                             (\<exists>v. \<Union>v = c \<inter> p -` T \<and> (\<forall>u \<in> v. openin (top_of_set c) u) \<and>
                             pairwise disjnt v \<and> (\<forall>u \<in> v. \<exists>q. homeomorphism u T p q))"
  shows "covering_space c p S"
sorry

lemma covering_space_imp_continuous: "covering_space c p S \<Longrightarrow> continuous_on c p"
sorry

lemma covering_space_imp_surjective: "covering_space c p S \<Longrightarrow> p ` c = S"
sorry

lemma homeomorphism_imp_covering_space: "homeomorphism S T f g \<Longrightarrow> covering_space S f T"
sorry

lemma covering_space_local_homeomorphism:
  assumes "covering_space c p S" "x \<in> c"
  obtains T u q where "x \<in> T" "openin (top_of_set c) T"
                      "p x \<in> u" "openin (top_of_set S) u"
                      "homeomorphism T u p q"
sorry

lemma covering_space_local_homeomorphism_alt:
  assumes p: "covering_space c p S" and "y \<in> S"
  obtains x T U q where "p x = y"
                        "x \<in> T" "openin (top_of_set c) T"
                        "y \<in> U" "openin (top_of_set S) U"
                          "homeomorphism T U p q"
sorry

proposition covering_space_open_map:
  fixes S :: "'a :: metric_space set" and T :: "'b :: metric_space set"
  assumes p: "covering_space c p S" and T: "openin (top_of_set c) T"
    shows "openin (top_of_set S) (p ` T)"
sorry

lemma covering_space_lift_unique_gen:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  fixes g1 :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes cov: "covering_space c p S"
      and eq: "g1 a = g2 a"
      and f: "continuous_on T f"  "f \<in> T \<rightarrow> S"
      and g1: "continuous_on T g1"  "g1 \<in> T \<rightarrow> c"
      and fg1: "\<And>x. x \<in> T \<Longrightarrow> f x = p(g1 x)"
      and g2: "continuous_on T g2"  "g2 \<in> T \<rightarrow> c"
      and fg2: "\<And>x. x \<in> T \<Longrightarrow> f x = p(g2 x)"
      and u_compt: "U \<in> components T" and "a \<in> U" "x \<in> U"
    shows "g1 x = g2 x"
sorry

proposition covering_space_lift_unique:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  fixes g1 :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "covering_space c p S"
          "g1 a = g2 a"
          "continuous_on T f"  "f \<in> T \<rightarrow> S"
          "continuous_on T g1"  "g1 \<in> T \<rightarrow> c"  "\<And>x. x \<in> T \<Longrightarrow> f x = p(g1 x)"
          "continuous_on T g2"  "g2 \<in> T \<rightarrow> c"  "\<And>x. x \<in> T \<Longrightarrow> f x = p(g2 x)"
          "connected T"  "a \<in> T"   "x \<in> T"
   shows "g1 x = g2 x"
sorry

lemma covering_space_locally:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes loc: "locally \<phi> C" and cov: "covering_space C p S"
      and pim: "\<And>T. \<lbrakk>T \<subseteq> C; \<phi> T\<rbrakk> \<Longrightarrow> \<psi>(p ` T)"
    shows "locally \<psi> S"
sorry

proposition covering_space_locally_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and pim: "\<And>T. \<lbrakk>T \<subseteq> C; \<phi> T\<rbrakk> \<Longrightarrow> \<psi>(p ` T)"
      and qim: "\<And>q U. \<lbrakk>U \<subseteq> S; continuous_on U q; \<psi> U\<rbrakk> \<Longrightarrow> \<phi>(q ` U)"
    shows "locally \<psi> S \<longleftrightarrow> locally \<phi> C"
         (is "?lhs = ?rhs")
sorry

lemma covering_space_locally_compact_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "covering_space C p S"
  shows "locally compact S \<longleftrightarrow> locally compact C"
sorry

lemma covering_space_locally_connected_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "covering_space C p S"
    shows "locally connected S \<longleftrightarrow> locally connected C"
sorry

lemma covering_space_locally_path_connected_eq:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "covering_space C p S"
    shows "locally path_connected S \<longleftrightarrow> locally path_connected C"
sorry

lemma covering_space_locally_compact:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "locally compact C" "covering_space C p S"
  shows "locally compact S"
sorry

lemma covering_space_locally_connected:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "locally connected C" "covering_space C p S"
  shows "locally connected S"
sorry

lemma covering_space_locally_path_connected:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "locally path_connected C" "covering_space C p S"
  shows "locally path_connected S"
sorry

proposition covering_space_lift_homotopy:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and h :: "real \<times> 'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S"
      and conth: "continuous_on ({0..1} \<times> U) h"
      and him: "h \<in> ({0..1} \<times> U) \<rightarrow> S"
      and heq: "\<And>y. y \<in> U \<Longrightarrow> h (0,y) = p(f y)"
      and contf: "continuous_on U f" and fim: "f \<in> U \<rightarrow> C"
    obtains k where "continuous_on ({0..1} \<times> U) k"
                    "k \<in> ({0..1} \<times> U) \<rightarrow> C"
                    "\<And>y. y \<in> U \<Longrightarrow> k(0, y) = f y"
                    "\<And>z. z \<in> {0..1} \<times> U \<Longrightarrow> h z = p(k z)"
sorry

corollary covering_space_lift_homotopy_alt:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and h :: "'c::real_normed_vector \<times> real \<Rightarrow> 'b"
  assumes cov: "covering_space C p S"
      and conth: "continuous_on (U \<times> {0..1}) h"
      and him: "h \<in> (U \<times> {0..1}) \<rightarrow> S"
      and heq: "\<And>y. y \<in> U \<Longrightarrow> h (y,0) = p(f y)"
      and contf: "continuous_on U f" and fim: "f \<in> U \<rightarrow> C"
  obtains k where "continuous_on (U \<times> {0..1}) k"
                  "k \<in> (U \<times> {0..1}) \<rightarrow> C"
                  "\<And>y. y \<in> U \<Longrightarrow> k(y, 0) = f y"
                  "\<And>z. z \<in> U \<times> {0..1} \<Longrightarrow> h z = p(k z)"
sorry

corollary covering_space_lift_homotopic_function:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and g:: "'c::real_normed_vector \<Rightarrow> 'a"
  assumes cov: "covering_space C p S"
      and contg: "continuous_on U g"
      and gim: "g \<in> U \<rightarrow> C"
      and pgeq: "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
      and hom: "homotopic_with_canon (\<lambda>x. True) U S f f'"
    obtains g' where "continuous_on U g'" "image g' U \<subseteq> C" "\<And>y. y \<in> U \<Longrightarrow> p(g' y) = f' y"
sorry

corollary covering_space_lift_inessential_function:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and U :: "'c::real_normed_vector set"
  assumes cov: "covering_space C p S"
      and hom: "homotopic_with_canon (\<lambda>x. True) U S f (\<lambda>x. a)"
  obtains g where "continuous_on U g" "g ` U \<subseteq> C" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
sorry


subsection\<open> Lifting of general functions to covering space\<close>

proposition covering_space_lift_path_strong:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" and "a \<in> C"
      and "path g" and pag: "path_image g \<subseteq> S" and pas: "pathstart g = p a"
    obtains h where "path h" "path_image h \<subseteq> C" "pathstart h = a"
                and "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h t) = g t"
sorry

corollary covering_space_lift_path:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S" and "path g" and pig: "path_image g \<subseteq> S"
  obtains h where "path h" "path_image h \<subseteq> C" "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h t) = g t"
sorry

proposition covering_space_lift_homotopic_paths:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and "path g1" and pig1: "path_image g1 \<subseteq> S"
      and "path g2" and pig2: "path_image g2 \<subseteq> S"
      and hom: "homotopic_paths S g1 g2"
      and "path h1" and pih1: "path_image h1 \<subseteq> C" and ph1: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h1 t) = g1 t"
      and "path h2" and pih2: "path_image h2 \<subseteq> C" and ph2: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h2 t) = g2 t"
      and h1h2: "pathstart h1 = pathstart h2"
    shows "homotopic_paths C h1 h2"
sorry

corollary covering_space_monodromy:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and "path g1" and pig1: "path_image g1 \<subseteq> S"
      and "path g2" and pig2: "path_image g2 \<subseteq> S"
      and hom: "homotopic_paths S g1 g2"
      and "path h1" and pih1: "path_image h1 \<subseteq> C" and ph1: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h1 t) = g1 t"
      and "path h2" and pih2: "path_image h2 \<subseteq> C" and ph2: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(h2 t) = g2 t"
      and h1h2: "pathstart h1 = pathstart h2"
    shows "pathfinish h1 = pathfinish h2"
sorry

corollary covering_space_lift_homotopic_path:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes cov: "covering_space C p S"
      and hom: "homotopic_paths S f f'"
      and "path g" and pig: "path_image g \<subseteq> C"
      and a: "pathstart g = a" and b: "pathfinish g = b"
      and pgeq: "\<And>t. t \<in> {0..1} \<Longrightarrow> p(g t) = f t"
  obtains g' where "path g'" "path_image g' \<subseteq> C"
                   "pathstart g' = a" "pathfinish g' = b" "\<And>t. t \<in> {0..1} \<Longrightarrow> p(g' t) = f' t"
sorry

proposition covering_space_lift_general:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" and "a \<in> C" "z \<in> U"
      and U: "path_connected U" "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f \<in> U \<rightarrow> S"
      and feq: "f z = p a"
      and hom: "\<And>r. \<lbrakk>path r; path_image r \<subseteq> U; pathstart r = z; pathfinish r = z\<rbrakk>
                     \<Longrightarrow> \<exists>q. path q \<and> path_image q \<subseteq> C \<and>
                             pathstart q = a \<and> pathfinish q = a \<and>
                             homotopic_paths S (f \<circ> r) (p \<circ> q)"
  obtains g where "continuous_on U g" "g \<in> U \<rightarrow> C" "g z = a" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
sorry

corollary covering_space_lift_stronger:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" "a \<in> C" "z \<in> U"
      and U: "path_connected U" "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f \<in> U \<rightarrow> S"
      and feq: "f z = p a"
      and hom: "\<And>r. \<lbrakk>path r; path_image r \<subseteq> U; pathstart r = z; pathfinish r = z\<rbrakk>
                     \<Longrightarrow> \<exists>b. homotopic_paths S (f \<circ> r) (linepath b b)"
  obtains g where "continuous_on U g" "g \<in> U \<rightarrow> C" "g z = a" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
sorry

corollary covering_space_lift_strong:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S" "a \<in> C" "z \<in> U"
      and scU: "simply_connected U" and lpcU: "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f \<in> U \<rightarrow> S"
      and feq: "f z = p a"
  obtains g where "continuous_on U g" "g \<in> U \<rightarrow> C" "g z = a" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
sorry

corollary covering_space_lift:
  fixes p :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and f :: "'c::real_normed_vector \<Rightarrow> 'b"
  assumes cov: "covering_space C p S"
      and U: "simply_connected U"  "locally path_connected U"
      and contf: "continuous_on U f" and fim: "f \<in> U \<rightarrow> S"
    obtains g where "continuous_on U g" "g \<in> U \<rightarrow> C" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Homeomorphisms of arc images\<close>

lemma homeomorphism_arc:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  assumes "arc g"
  obtains h where "homeomorphism {0..1} (path_image g) g h"
sorry

lemma homeomorphic_arc_image_interval:
  fixes g :: "real \<Rightarrow> 'a::t2_space" and a::real
  assumes "arc g" "a < b"
  shows "(path_image g) homeomorphic {a..b}"
sorry

lemma homeomorphic_arc_images:
  fixes g :: "real \<Rightarrow> 'a::t2_space" and h :: "real \<Rightarrow> 'b::t2_space"
  assumes "arc g" "arc h"
  shows "(path_image g) homeomorphic (path_image h)"
sorry

end
