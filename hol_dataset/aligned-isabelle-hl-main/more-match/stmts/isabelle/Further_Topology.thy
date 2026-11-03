section \<open>Extending Continous Maps, Invariance of Domain, etc\<close> (*FIX rename? *)

text\<open>Ported from HOL Light (moretop.ml) by L C Paulson\<close>

theory Further_Topology
  imports Weierstrass_Theorems Polytope Complex_Transcendental Equivalence_Lebesgue_Henstock_Integration Retracts
begin

subsection\<open>A map from a sphere to a higher dimensional sphere is nullhomotopic\<close>

lemma spheremap_lemma1:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "subspace S" "subspace T" and dimST: "dim S < dim T"
      and "S \<subseteq> T"
      and diff_f: "f differentiable_on sphere 0 1 \<inter> S"
    shows "f ` (sphere 0 1 \<inter> S) \<noteq> sphere 0 1 \<inter> T"
sorry

lemma spheremap_lemma2:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes ST: "subspace S" "subspace T" "dim S < dim T"
      and "S \<subseteq> T"
      and contf: "continuous_on (sphere 0 1 \<inter> S) f"
      and fim: "f \<in> (sphere 0 1 \<inter> S) \<rightarrow> sphere 0 1 \<inter> T"
    shows "\<exists>c. homotopic_with_canon (\<lambda>x. True) (sphere 0 1 \<inter> S) (sphere 0 1 \<inter> T) f (\<lambda>x. c)"
sorry

lemma spheremap_lemma3:
  assumes "bounded S" "convex S" "subspace U" and affSU: "aff_dim S \<le> dim U"
  obtains T where "subspace T" "T \<subseteq> U" "S \<noteq> {} \<Longrightarrow> aff_dim T = aff_dim S"
                  "(rel_frontier S) homeomorphic (sphere 0 1 \<inter> T)"
sorry

proposition inessential_spheremap_lowdim_gen:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "convex S" "bounded S" "convex T" "bounded T"
      and affST: "aff_dim S < aff_dim T"
      and contf: "continuous_on (rel_frontier S) f"
      and fim: "f \<in> (rel_frontier S) \<rightarrow> rel_frontier T"
  obtains c where "homotopic_with_canon (\<lambda>z. True) (rel_frontier S) (rel_frontier T) f (\<lambda>x. c)"
sorry

lemma inessential_spheremap_lowdim:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes
   "DIM('M) < DIM('a)" and f: "continuous_on (sphere a r) f" "f \<in> (sphere a r) \<rightarrow> (sphere b s)"
   obtains c where "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere b s) f (\<lambda>x. c)"
sorry



subsection\<open> Some technical lemmas about extending maps from cell complexes\<close>

lemma extending_maps_Union_aux:
  assumes fin: "finite \<F>"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
      and "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>; S \<noteq> T\<rbrakk> \<Longrightarrow> S \<inter> T \<subseteq> K"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>g. continuous_on S g \<and> g \<in> S \<rightarrow> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
   shows "\<exists>g. continuous_on (\<Union>\<F>) g \<and> g \<in> (\<Union>\<F>) \<rightarrow> T \<and> (\<forall>x \<in> \<Union>\<F> \<inter> K. g x = h x)"
sorry

lemma extending_maps_Union:
  assumes fin: "finite \<F>"
    and "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>g. continuous_on S g \<and> g \<in> S \<rightarrow> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
    and "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
    and K: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>; \<not> X \<subseteq> Y; \<not> Y \<subseteq> X\<rbrakk> \<Longrightarrow> X \<inter> Y \<subseteq> K"
  shows "\<exists>g. continuous_on (\<Union>\<F>) g \<and> g \<in> (\<Union>\<F>) \<rightarrow> T \<and> (\<forall>x \<in> \<Union>\<F> \<inter> K. g x = h x)"
sorry

lemma extend_map_lemma:
  assumes "finite \<F>" "\<G> \<subseteq> \<F>" "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> - \<G> \<Longrightarrow> aff_dim X < aff_dim T"
      and face: "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>\<rbrakk> \<Longrightarrow> (S \<inter> T) face_of S"
      and contf: "continuous_on (\<Union>\<G>) f" and fim: "f \<in> (\<Union>\<G>) \<rightarrow> rel_frontier T"
  obtains g where "continuous_on (\<Union>\<F>) g" "g \<in> (\<Union>\<F>) \<rightarrow> rel_frontier T" "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> g x = f x"
sorry

lemma extend_map_lemma_cofinite0:
  assumes "finite \<F>"
      and "pairwise (\<lambda>S T. S \<inter> T \<subseteq> K) \<F>"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>a g. a \<notin> U \<and> continuous_on (S - {a}) g \<and> g \<in> (S - {a}) \<rightarrow> T \<and> (\<forall>x \<in> S \<inter> K. g x = h x)"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closed S"
    shows "\<exists>C g. finite C \<and> disjnt C U \<and> card C \<le> card \<F> \<and>
                 continuous_on (\<Union>\<F> - C) g \<and> g \<in> (\<Union>\<F> - C) \<rightarrow> T
                  \<and> (\<forall>x \<in> (\<Union>\<F> - C) \<inter> K. g x = h x)"
sorry

lemma extend_map_lemma_cofinite1:
assumes "finite \<F>"
    and \<F>: "\<And>X. X \<in> \<F> \<Longrightarrow> \<exists>a g. a \<notin> U \<and> continuous_on (X - {a}) g \<and> g \<in> (X - {a}) \<rightarrow> T \<and> (\<forall>x \<in> X \<inter> K. g x = h x)"
    and clo: "\<And>X. X \<in> \<F> \<Longrightarrow> closed X"
    and K: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>; \<not> X \<subseteq> Y; \<not> Y \<subseteq> X\<rbrakk> \<Longrightarrow> X \<inter> Y \<subseteq> K"
  obtains C g where "finite C" "disjnt C U" "card C \<le> card \<F>" "continuous_on (\<Union>\<F> - C) g"
                    "g \<in> (\<Union>\<F> - C) \<rightarrow> T"
                    "\<And>x. x \<in> (\<Union>\<F> - C) \<inter> K \<Longrightarrow> g x = h x"
sorry

lemma extend_map_lemma_cofinite:
  assumes "finite \<F>" "\<G> \<subseteq> \<F>" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and contf: "continuous_on (\<Union>\<G>) f" and fim: "f \<in> (\<Union>\<G>) \<rightarrow> rel_frontier T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
      and aff: "\<And>X. X \<in> \<F> - \<G> \<Longrightarrow> aff_dim X \<le> aff_dim T"
  obtains C g where
     "finite C" "disjnt C (\<Union>\<G>)" "card C \<le> card \<F>" "continuous_on (\<Union>\<F> - C) g"
     "g \<in> (\<Union> \<F> - C) \<rightarrow> rel_frontier T" "\<And>x. x \<in> \<Union>\<G> \<Longrightarrow> g x = f x"
sorry

text\<open>The next two proofs are similar\<close>
theorem extend_map_cell_complex_to_sphere:
  assumes "finite \<F>" and S: "S \<subseteq> \<Union>\<F>" "closed S" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X < aff_dim T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> rel_frontier T"
  obtains g where "continuous_on (\<Union>\<F>) g"
     "g \<in> (\<Union>\<F>) \<rightarrow> rel_frontier T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

theorem extend_map_cell_complex_to_sphere_cofinite:
  assumes "finite \<F>" and S: "S \<subseteq> \<Union>\<F>" "closed S" and T: "convex T" "bounded T"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> aff_dim T"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> rel_frontier T"
  obtains C g where "finite C" "disjnt C S" "continuous_on (\<Union>\<F> - C) g"
     "g \<in> (\<Union>\<F> - C) \<rightarrow> rel_frontier T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry



subsection\<open> Special cases and corollaries involving spheres\<close>

proposition extend_map_affine_to_sphere_cofinite_simple:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact S" "convex U" "bounded U"
      and aff: "aff_dim T \<le> aff_dim U"
      and "S \<subseteq> T" and contf: "continuous_on S f"
      and fim: "f \<in> S \<rightarrow> rel_frontier U"
 obtains K g where "finite K" "K \<subseteq> T" "disjnt K S" "continuous_on (T - K) g"
                   "g \<in> (T - K) \<rightarrow> rel_frontier U"
                   "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

subsection\<open>Extending maps to spheres\<close>

(*Up to extend_map_affine_to_sphere_cofinite_gen*)

lemma extend_map_affine_to_sphere1:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::topological_space"
  assumes "finite K" "affine U" and contf: "continuous_on (U - K) f"
      and fim: "f \<in> (U - K) \<rightarrow> T"
      and comps: "\<And>C. \<lbrakk>C \<in> components(U - S); C \<inter> K \<noteq> {}\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
      and clo: "closedin (top_of_set U) S" and K: "disjnt K S" "K \<subseteq> U"
  obtains g where "continuous_on (U - L) g" "g \<in> (U - L) \<rightarrow> T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

lemma extend_map_affine_to_sphere2:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact S" "convex U" "bounded U" "affine T" "S \<subseteq> T"
      and affTU: "aff_dim T \<le> aff_dim U"
      and contf: "continuous_on S f"
      and fim: "f \<in> S \<rightarrow> rel_frontier U"
      and ovlap: "\<And>C. C \<in> components(T - S) \<Longrightarrow> C \<inter> L \<noteq> {}"
    obtains K g where "finite K" "K \<subseteq> L" "K \<subseteq> T" "disjnt K S"
                      "continuous_on (T - K) g" "g \<in> (T - K) \<rightarrow> rel_frontier U"
                      "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

proposition extend_map_affine_to_sphere_cofinite_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes SUT: "compact S" "convex U" "bounded U" "affine T" "S \<subseteq> T"
      and aff: "aff_dim T \<le> aff_dim U"
      and contf: "continuous_on S f"
      and fim: "f \<in> S \<rightarrow> rel_frontier U"
      and dis: "\<And>C. \<lbrakk>C \<in> components(T - S); bounded C\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
 obtains K g where "finite K" "K \<subseteq> L" "K \<subseteq> T" "disjnt K S" "continuous_on (T - K) g"
                   "g \<in> (T - K) \<rightarrow> rel_frontier U"
                   "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

corollary extend_map_affine_to_sphere_cofinite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes SUT: "compact S" "affine T" "S \<subseteq> T"
      and aff: "aff_dim T \<le> DIM('b)" and "0 \<le> r"
      and contf: "continuous_on S f"
      and fim: "f \<in> S \<rightarrow> sphere a r"
      and dis: "\<And>C. \<lbrakk>C \<in> components(T - S); bounded C\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
  obtains K g where "finite K" "K \<subseteq> L" "K \<subseteq> T" "disjnt K S" "continuous_on (T - K) g"
                    "g \<in> (T - K) \<rightarrow> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

corollary extend_map_UNIV_to_sphere_cofinite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "DIM('a) \<le> DIM('b)" and "0 \<le> r"
      and "compact S"
      and "continuous_on S f"
      and "f \<in> S \<rightarrow> sphere a r"
      and "\<And>C. \<lbrakk>C \<in> components(- S); bounded C\<rbrakk> \<Longrightarrow> C \<inter> L \<noteq> {}"
  obtains K g where "finite K" "K \<subseteq> L" "disjnt K S" "continuous_on (- K) g"
                    "g \<in> (- K) \<rightarrow> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

corollary extend_map_UNIV_to_sphere_no_bounded_component:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes aff: "DIM('a) \<le> DIM('b)" and "0 \<le> r"
      and SUT: "compact S"
      and contf: "continuous_on S f"
      and fim: "f \<in> S \<rightarrow> sphere a r"
      and dis: "\<And>C. C \<in> components(- S) \<Longrightarrow> \<not> bounded C"
  obtains g where "continuous_on UNIV g" "g \<in> UNIV \<rightarrow> sphere a r" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

theorem Borsuk_separation_theorem_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S"
    shows "(\<forall>c \<in> components(- S). \<not>bounded c) \<longleftrightarrow>
           (\<forall>f. continuous_on S f \<and> f \<in> S \<rightarrow> sphere (0::'a) 1
                \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)))"
       (is "?lhs = ?rhs")
sorry

corollary Borsuk_separation_theorem:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and 2: "2 \<le> DIM('a)"
    shows "connected(- S) \<longleftrightarrow>
           (\<forall>f. continuous_on S f \<and> f \<in> S \<rightarrow> sphere (0::'a) 1
                \<longrightarrow> (\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f (\<lambda>x. c)))"
       (is "?lhs = ?rhs")
sorry

lemma homotopy_eqv_separation:
  fixes S :: "'a::euclidean_space set" and T :: "'a set"
  assumes "S homotopy_eqv T" and "compact S" and "compact T"
  shows "connected(- S) \<longleftrightarrow> connected(- T)"
sorry

proposition Jordan_Brouwer_separation:
  fixes S :: "'a::euclidean_space set" and a::'a
  assumes hom: "S homeomorphic sphere a r" and "0 < r"
    shows "\<not> connected(- S)"
sorry

proposition Jordan_Brouwer_frontier:
  fixes S :: "'a::euclidean_space set" and a::'a
  assumes S: "S homeomorphic sphere a r" and T: "T \<in> components(- S)" and 2: "2 \<le> DIM('a)"
    shows "frontier T = S"
sorry

proposition Jordan_Brouwer_nonseparation:
  fixes S :: "'a::euclidean_space set" and a::'a
  assumes S: "S homeomorphic sphere a r" and "T \<subset> S" and 2: "2 \<le> DIM('a)"
    shows "connected(- T)"
sorry

subsection\<open> Invariance of domain and corollaries\<close>

lemma invariance_of_domain_ball:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes contf: "continuous_on (cball a r) f" and "0 < r"
     and inj: "inj_on f (cball a r)"
   shows "open(f ` ball a r)"
sorry


text\<open>Proved by L. E. J. Brouwer (1912)\<close>
theorem invariance_of_domain:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes "continuous_on S f" "open S" "inj_on f S"
    shows "open(f ` S)"
sorry

lemma inv_of_domain_ss0:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes contf: "continuous_on U f" and injf: "inj_on f U" and fim: "f \<in> U \<rightarrow> S"
      and "subspace S" and dimS: "dim S = DIM('b::euclidean_space)"
      and ope: "openin (top_of_set S) U"
    shows "openin (top_of_set S) (f ` U)"
sorry

lemma inv_of_domain_ss1:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes contf: "continuous_on U f" and injf: "inj_on f U" and fim: "f \<in> U \<rightarrow> S"
      and "subspace S"
      and ope: "openin (top_of_set S) U"
    shows "openin (top_of_set S) (f ` U)"
sorry

corollary invariance_of_domain_subspaces:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and "subspace U" "subspace V" and VU: "dim V \<le> dim U"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> V"
      and injf: "inj_on f S"
    shows "openin (top_of_set V) (f ` S)"
sorry

corollary invariance_of_dimension_subspaces:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and "subspace U" "subspace V"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "dim U \<le> dim V"
sorry

corollary invariance_of_domain_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and aff: "affine U" "affine V" "aff_dim V \<le> aff_dim U"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> V"
      and injf: "inj_on f S"
    shows "openin (top_of_set V) (f ` S)"
sorry

corollary invariance_of_dimension_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and aff: "affine U" "affine V"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "aff_dim U \<le> aff_dim V"
sorry

corollary invariance_of_dimension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and "open S"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "DIM('a) \<le> DIM('b)"
sorry

corollary continuous_injective_image_subspace_dim_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "subspace S" "subspace T"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> T"
      and injf: "inj_on f S"
    shows "dim S \<le> dim T"
sorry

lemma invariance_of_dimension_convex_domain:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "convex S"
      and contf: "continuous_on S f" and fim: "f \<in> S \<rightarrow> affine hull T"
      and injf: "inj_on f S"
    shows "aff_dim S \<le> aff_dim T"
sorry

lemma homeomorphic_convex_sets_le:
  assumes "convex S" "S homeomorphic T"
  shows "aff_dim S \<le> aff_dim T"
sorry

lemma homeomorphic_convex_sets:
  assumes "convex S" "convex T" "S homeomorphic T"
  shows "aff_dim S = aff_dim T"
sorry

lemma homeomorphic_convex_compact_sets_eq:
  assumes "convex S" "compact S" "convex T" "compact T"
  shows "S homeomorphic T \<longleftrightarrow> aff_dim S = aff_dim T"
sorry

lemma invariance_of_domain_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "inj_on f S" "DIM('b) \<le> DIM('a)"
    shows "open(f ` S)"
sorry

lemma injective_into_1d_imp_open_map_UNIV:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "open T" "continuous_on S f" "inj_on f S" "T \<subseteq> S"
  shows "open (f ` T)"
sorry

lemma continuous_on_inverse_open:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" and gf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
    shows "continuous_on (f ` S) g"
sorry

lemma invariance_of_domain_homeomorphism:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" "inj_on f S"
  obtains g where "homeomorphism S (f ` S) f g"
sorry

corollary invariance_of_domain_homeomorphic:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" "inj_on f S"
  shows "S homeomorphic (f ` S)"
sorry

lemma continuous_image_subset_interior:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on S f" "inj_on f S" "DIM('b) \<le> DIM('a)"
  shows "f \<in> (interior S) \<rightarrow> interior(f ` S)"
sorry

lemma homeomorphic_interiors_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and dimeq: "DIM('a) = DIM('b)"
  shows "(interior S) homeomorphic (interior T)"
sorry

lemma homeomorphic_open_imp_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "open S" "S \<noteq> {}" "open T" "T \<noteq> {}"
  shows "DIM('a) = DIM('b)"
sorry

proposition homeomorphic_interiors:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "interior S = {} \<longleftrightarrow> interior T = {}"
    shows "(interior S) homeomorphic (interior T)"
sorry

lemma homeomorphic_frontiers_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "closed S" "closed T" and dimeq: "DIM('a) = DIM('b)"
  shows "(frontier S) homeomorphic (frontier T)"
sorry

lemma homeomorphic_frontiers:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "closed S" "closed T"
          "interior S = {} \<longleftrightarrow> interior T = {}"
    shows "(frontier S) homeomorphic (frontier T)"
sorry

lemma continuous_image_subset_rel_interior:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f \<in> S \<rightarrow> T"
      and TS: "aff_dim T \<le> aff_dim S"
    shows "f \<in> (rel_interior S) \<rightarrow> rel_interior(f ` S)"
sorry

lemma homeomorphic_rel_interiors_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and aff: "aff_dim S = aff_dim T"
  shows "(rel_interior S) homeomorphic (rel_interior T)"
sorry

lemma homeomorphic_aff_dim_le:
  fixes S :: "'a::euclidean_space set" 
  assumes "S homeomorphic T" "rel_interior S \<noteq> {}"
    shows "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
sorry

lemma homeomorphic_rel_interiors:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "rel_interior S = {} \<longleftrightarrow> rel_interior T = {}"
    shows "(rel_interior S) homeomorphic (rel_interior T)"
sorry

lemma homeomorphic_rel_boundaries_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and aff: "aff_dim S = aff_dim T"
  shows "(S - rel_interior S) homeomorphic (T - rel_interior T)"
sorry

lemma homeomorphic_rel_boundaries:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "rel_interior S = {} \<longleftrightarrow> rel_interior T = {}"
    shows "(S - rel_interior S) homeomorphic (T - rel_interior T)"
sorry

proposition uniformly_continuous_homeomorphism_UNIV_trivial:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes contf: "uniformly_continuous_on S f" and hom: "homeomorphism S UNIV f g"
  shows "S = UNIV"
sorry

subsection\<open>Formulation of loop homotopy in terms of maps out of type complex\<close>

lemma homotopic_circlemaps_imp_homotopic_loops:
  assumes "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
   shows "homotopic_loops S (f \<circ> exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))
                            (g \<circ> exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))"
sorry

lemma homotopic_loops_imp_homotopic_circlemaps:
  assumes "homotopic_loops S p q"
    shows "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S
                          (p \<circ> (\<lambda>z. (Arg2pi z / (2 * pi))))
                          (q \<circ> (\<lambda>z. (Arg2pi z / (2 * pi))))"
sorry

lemma simply_connected_homotopic_loops:
  "simply_connected S \<longleftrightarrow>
       (\<forall>p q. homotopic_loops S p p \<and> homotopic_loops S q q \<longrightarrow> homotopic_loops S p q)"
sorry

lemma simply_connected_eq_homotopic_circlemaps1:
  fixes f :: "complex \<Rightarrow> 'a::topological_space" and g :: "complex \<Rightarrow> 'a"
  assumes S: "simply_connected S"
      and contf: "continuous_on (sphere 0 1) f" and fim: "f \<in> (sphere 0 1) \<rightarrow> S"
      and contg: "continuous_on (sphere 0 1) g" and gim: "g \<in> (sphere 0 1) \<rightarrow> S"
    shows "homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
sorry

lemma simply_connected_eq_homotopic_circlemaps2a:
  fixes h :: "complex \<Rightarrow> 'a::topological_space"
  assumes conth: "continuous_on (sphere 0 1) h" and him: "h \<in> sphere 0 1 \<rightarrow> S"
      and hom: "\<And>f g::complex \<Rightarrow> 'a.
                \<lbrakk>continuous_on (sphere 0 1) f; f \<in> (sphere 0 1) \<rightarrow> S;
                continuous_on (sphere 0 1) g; g \<in> (sphere 0 1) \<rightarrow> S\<rbrakk>
                \<Longrightarrow> homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
            shows "\<exists>a. homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S h (\<lambda>x. a)"
sorry

lemma simply_connected_eq_homotopic_circlemaps2b:
  fixes S :: "'a::real_normed_vector set"
  assumes "\<And>f g::complex \<Rightarrow> 'a.
                \<lbrakk>continuous_on (sphere 0 1) f; f \<in> (sphere 0 1) \<rightarrow> S;
                continuous_on (sphere 0 1) g; g \<in> (sphere 0 1) \<rightarrow> S\<rbrakk>
                \<Longrightarrow> homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g"
  shows "path_connected S"
sorry

lemma simply_connected_eq_homotopic_circlemaps3:
  fixes h :: "complex \<Rightarrow> 'a::real_normed_vector"
  assumes "path_connected S"
      and hom: "\<And>f::complex \<Rightarrow> 'a.
                  \<lbrakk>continuous_on (sphere 0 1) f; f `(sphere 0 1) \<subseteq> S\<rbrakk>
                  \<Longrightarrow> \<exists>a. homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f (\<lambda>x. a)"
    shows "simply_connected S"
sorry

proposition simply_connected_eq_homotopic_circlemaps:
  fixes S :: "'a::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         (\<forall>f g::complex \<Rightarrow> 'a.
              continuous_on (sphere 0 1) f \<and> f \<in> (sphere 0 1) \<rightarrow> S \<and>
              continuous_on (sphere 0 1) g \<and> g \<in> (sphere 0 1) \<rightarrow> S
              \<longrightarrow> homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f g)"
sorry

proposition simply_connected_eq_contractible_circlemap:
  fixes S :: "'a::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         path_connected S \<and>
         (\<forall>f::complex \<Rightarrow> 'a.
              continuous_on (sphere 0 1) f \<and> f `(sphere 0 1) \<subseteq> S
              \<longrightarrow> (\<exists>a. homotopic_with_canon (\<lambda>h. True) (sphere 0 1) S f (\<lambda>x. a)))"
sorry

corollary homotopy_eqv_simple_connectedness:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "S homotopy_eqv T \<Longrightarrow> simply_connected S \<longleftrightarrow> simply_connected T"
sorry

subsection\<open>Homeomorphism of simple closed curves to circles\<close>

proposition homeomorphic_simple_path_image_circle:
  fixes a :: complex and \<gamma> :: "real \<Rightarrow> 'a::t2_space"
  assumes "simple_path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>" and "0 < r"
  shows "(path_image \<gamma>) homeomorphic sphere a r"
sorry

lemma homeomorphic_simple_path_images:
  fixes \<gamma>1 :: "real \<Rightarrow> 'a::t2_space" and \<gamma>2 :: "real \<Rightarrow> 'b::t2_space"
  assumes "simple_path \<gamma>1" and loop: "pathfinish \<gamma>1 = pathstart \<gamma>1"
  assumes "simple_path \<gamma>2" and loop: "pathfinish \<gamma>2 = pathstart \<gamma>2"
  shows "(path_image \<gamma>1) homeomorphic (path_image \<gamma>2)"
sorry

subsection\<open>Dimension-based conditions for various homeomorphisms\<close>

lemma homeomorphic_subspaces_eq:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "subspace S" "subspace T"
  shows "S homeomorphic T \<longleftrightarrow> dim S = dim T"
sorry

lemma homeomorphic_affine_sets_eq:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "affine S" "affine T"
  shows "S homeomorphic T \<longleftrightarrow> aff_dim S = aff_dim T"
sorry

lemma homeomorphic_hyperplanes_eq:
  fixes a :: "'a::euclidean_space" and c :: "'b::euclidean_space"
  assumes "a \<noteq> 0" "c \<noteq> 0"
  shows "({x. a \<bullet> x = b} homeomorphic {x. c \<bullet> x = d} \<longleftrightarrow> DIM('a) = DIM('b))"
sorry

lemma homeomorphic_UNIV_UNIV:
  shows "(UNIV::'a set) homeomorphic (UNIV::'b set) \<longleftrightarrow>
    DIM('a::euclidean_space) = DIM('b::euclidean_space)"
sorry

lemma simply_connected_sphere_gen:
   assumes "convex S" "bounded S" and 3: "3 \<le> aff_dim S"
   shows "simply_connected(rel_frontier S)"
sorry

subsection\<open>more invariance of domain\<close>  (*FIX ME title? *)

proposition invariance_of_domain_sphere_affine_set_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f \<in> S \<rightarrow> T"
      and U: "bounded U" "convex U"
      and "affine T" and affTU: "aff_dim T < aff_dim U"
      and ope: "openin (top_of_set (rel_frontier U)) S"
   shows "openin (top_of_set T) (f ` S)"
sorry

lemma invariance_of_domain_sphere_affine_set:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f \<in> S \<rightarrow> T"
      and "r \<noteq> 0" "affine T" and affTU: "aff_dim T < DIM('a)"
      and ope: "openin (top_of_set (sphere a r)) S"
   shows "openin (top_of_set T) (f ` S)"
sorry

lemma no_embedding_sphere_lowdim:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on (sphere a r) f" and injf: "inj_on f (sphere a r)" and "r > 0"
   shows "DIM('a) \<le> DIM('b)"
sorry

lemma simply_connected_sphere:
  fixes a :: "'a::euclidean_space"
  assumes "3 \<le> DIM('a)"
    shows "simply_connected(sphere a r)"
sorry

lemma simply_connected_sphere_eq:
  fixes a :: "'a::euclidean_space"
  shows "simply_connected(sphere a r) \<longleftrightarrow> 3 \<le> DIM('a) \<or> r \<le> 0"  (is "?lhs = ?rhs")
sorry

lemma simply_connected_punctured_universe_eq:
  fixes a :: "'a::euclidean_space"
  shows "simply_connected(- {a}) \<longleftrightarrow> 3 \<le> DIM('a)"
sorry

lemma not_simply_connected_circle:
  fixes a :: complex
  shows "0 < r \<Longrightarrow> \<not> simply_connected(sphere a r)"
sorry

proposition simply_connected_punctured_convex:
  fixes a :: "'a::euclidean_space"
  assumes "convex S" and 3: "3 \<le> aff_dim S"
    shows "simply_connected(S - {a})"
sorry

corollary simply_connected_punctured_universe:
  fixes a :: "'a::euclidean_space"
  assumes "3 \<le> DIM('a)"
  shows "simply_connected(- {a})"
sorry


subsection\<open>The power, squaring and exponential functions as covering maps\<close>

proposition covering_space_power_punctured_plane:
  assumes "0 < n"
    shows "covering_space (- {0}) (\<lambda>z::complex. z^n) (- {0})"
sorry

corollary covering_space_square_punctured_plane:
  "covering_space (- {0}) (\<lambda>z::complex. z^2) (- {0})"
sorry

proposition covering_space_exp_punctured_plane:
  "covering_space UNIV (\<lambda>z::complex. exp z) (- {0})"
sorry


subsection\<open>Hence the Borsukian results about mappings into circles\<close>(*FIX ME title *)

lemma inessential_eq_continuous_logarithm:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  shows "(\<exists>a. homotopic_with_canon (\<lambda>h. True) S (-{0}) f (\<lambda>t. a)) \<longleftrightarrow>
         (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(g x)))"
  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

corollary inessential_imp_continuous_logarithm_circle:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "homotopic_with_canon (\<lambda>h. True) S (sphere 0 1) f (\<lambda>t. a)"
  obtains g where "continuous_on S g" and "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
sorry

lemma inessential_eq_continuous_logarithm_circle:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  shows "(\<exists>a. homotopic_with_canon (\<lambda>h. True) S (sphere 0 1) f (\<lambda>t. a)) \<longleftrightarrow>
         (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(\<i> * of_real(g x))))"
  (is "?lhs \<longleftrightarrow> ?rhs")
sorry

proposition homotopic_with_sphere_times:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes hom: "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f g" and conth: "continuous_on S h"
      and hin: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> sphere 0 1"
    shows "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x * h x) (\<lambda>x. g x * h x)"
sorry

proposition homotopic_circlemaps_divide:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
    shows "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) f g \<longleftrightarrow>
           continuous_on S f \<and> f \<in> S \<rightarrow> sphere 0 1 \<and>
           continuous_on S g \<and> g \<in> S \<rightarrow> sphere 0 1 \<and>
           (\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. f x / g x) (\<lambda>x. c))"
sorry

subsection\<open>Upper and lower hemicontinuous functions\<close>

text\<open>And relation in the case of preimage map to open and closed maps, and fact that upper and lower
hemicontinuity together imply continuity in the sense of the Hausdorff metric (at points where the
function gives a bounded and nonempty set).\<close>


text\<open>Many similar proofs below.\<close>
lemma upper_hemicontinuous:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<subseteq> T"
    shows "((\<forall>U. openin (top_of_set T) U
                 \<longrightarrow> openin (top_of_set S) {x \<in> S. f x \<subseteq> U}) \<longleftrightarrow>
            (\<forall>U. closedin (top_of_set T) U
                 \<longrightarrow> closedin (top_of_set S) {x \<in> S. f x \<inter> U \<noteq> {}}))"
          (is "?lhs = ?rhs")
sorry

lemma lower_hemicontinuous:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x \<subseteq> T"
    shows "((\<forall>U. closedin (top_of_set T) U
                 \<longrightarrow> closedin (top_of_set S) {x \<in> S. f x \<subseteq> U}) \<longleftrightarrow>
            (\<forall>U. openin (top_of_set T) U
                 \<longrightarrow> openin (top_of_set S) {x \<in> S. f x \<inter> U \<noteq> {}}))"
          (is "?lhs = ?rhs")
sorry

lemma open_map_iff_lower_hemicontinuous_preimage:
  assumes "f \<in> S \<rightarrow> T"
    shows "((\<forall>U. openin (top_of_set S) U
                 \<longrightarrow> openin (top_of_set T) (f ` U)) \<longleftrightarrow>
            (\<forall>U. closedin (top_of_set S) U
                 \<longrightarrow> closedin (top_of_set T) {y \<in> T. {x. x \<in> S \<and> f x = y} \<subseteq> U}))"
          (is "?lhs = ?rhs")
sorry

lemma closed_map_iff_upper_hemicontinuous_preimage:
  assumes "f \<in> S \<rightarrow> T"
    shows "((\<forall>U. closedin (top_of_set S) U
                 \<longrightarrow> closedin (top_of_set T) (f ` U)) \<longleftrightarrow>
            (\<forall>U. openin (top_of_set S) U
                 \<longrightarrow> openin (top_of_set T) {y \<in> T. {x. x \<in> S \<and> f x = y} \<subseteq> U}))"
          (is "?lhs = ?rhs")
sorry

proposition upper_lower_hemicontinuous_explicit:
  fixes T :: "('b::{real_normed_vector,heine_borel}) set"
  assumes fST: "\<And>x. x \<in> S \<Longrightarrow> f x \<subseteq> T"
      and ope: "\<And>U. openin (top_of_set T) U
                     \<Longrightarrow> openin (top_of_set S) {x \<in> S. f x \<subseteq> U}"
      and clo: "\<And>U. closedin (top_of_set T) U
                     \<Longrightarrow> closedin (top_of_set S) {x \<in> S. f x \<subseteq> U}"
      and "x \<in> S" "0 < e" and bofx: "bounded(f x)" and fx_ne: "f x \<noteq> {}"
  obtains d where "0 < d"
             "\<And>x'. \<lbrakk>x' \<in> S; dist x x' < d\<rbrakk>
                           \<Longrightarrow> (\<forall>y \<in> f x. \<exists>y'. y' \<in> f x' \<and> dist y y' < e) \<and>
                               (\<forall>y' \<in> f x'. \<exists>y. y \<in> f x \<and> dist y' y < e)"
sorry


subsection\<open>Complex logs exist on various "well-behaved" sets\<close>

lemma continuous_logarithm_on_contractible:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on S f" "contractible S" "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
sorry

lemma continuous_logarithm_on_simply_connected:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes contf: "continuous_on S f" and S: "simply_connected S" "locally path_connected S"
      and f: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = exp(g x)"
sorry

lemma continuous_logarithm_on_cball:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on (cball a r) f" and "\<And>z. z \<in> cball a r \<Longrightarrow> f z \<noteq> 0"
    obtains h where "continuous_on (cball a r) h" "\<And>z. z \<in> cball a r \<Longrightarrow> f z = exp(h z)"
sorry

lemma continuous_logarithm_on_ball:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on (ball a r) f" and "\<And>z. z \<in> ball a r \<Longrightarrow> f z \<noteq> 0"
  obtains h where "continuous_on (ball a r) h" "\<And>z. z \<in> ball a r \<Longrightarrow> f z = exp(h z)"
sorry

lemma continuous_sqrt_on_contractible:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes "continuous_on S f" "contractible S"
      and "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = (g x) ^ 2"
sorry

lemma continuous_sqrt_on_simply_connected:
  fixes f :: "'a::real_normed_vector \<Rightarrow> complex"
  assumes contf: "continuous_on S f" and S: "simply_connected S" "locally path_connected S"
      and f: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "continuous_on S g" "\<And>x. x \<in> S \<Longrightarrow> f x = (g x) ^ 2"
sorry


subsection\<open>Another simple case where sphere maps are nullhomotopic\<close>

lemma inessential_spheremap_2_aux:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes 2: "2 < DIM('a)" and contf: "continuous_on (sphere a r) f" 
      and fim: "f \<in> (sphere a r) \<rightarrow> (sphere 0 1)" 
  obtains c where "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere 0 1) f (\<lambda>x. c)"
sorry

lemma inessential_spheremap_2:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes a2: "2 < DIM('a)" and b2: "DIM('b) = 2" 
      and contf: "continuous_on (sphere a r) f" and fim: "f \<in> (sphere a r) \<rightarrow> (sphere b s)"
  obtains c where "homotopic_with_canon (\<lambda>z. True) (sphere a r) (sphere b s) f (\<lambda>x. c)"
sorry


subsection\<open>Holomorphic logarithms and square roots\<close>

lemma g_imp_holomorphic_log:
  assumes holf: "f holomorphic_on S"
      and contg: "continuous_on S g" and feq: "\<And>x. x \<in> S \<Longrightarrow> f x = exp (g x)"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
sorry

lemma contractible_imp_holomorphic_log:
  assumes holf: "f holomorphic_on S"
      and S: "contractible S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
sorry

lemma simply_connected_imp_holomorphic_log:
  assumes holf: "f holomorphic_on S"
      and S: "simply_connected S" "locally path_connected S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = exp(g z)"
sorry

lemma contractible_imp_holomorphic_sqrt:
  assumes holf: "f holomorphic_on S"
      and S: "contractible S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = g z ^ 2"
sorry

lemma simply_connected_imp_holomorphic_sqrt:
  assumes holf: "f holomorphic_on S"
      and S: "simply_connected S" "locally path_connected S"
      and fnz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = g z ^ 2"
sorry

text\<open> Related theorems about holomorphic inverse cosines.\<close>

lemma contractible_imp_holomorphic_arccos:
  assumes holf: "f holomorphic_on S" and S: "contractible S"
      and non1: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 1 \<and> f z \<noteq> -1"
  obtains g where "g holomorphic_on S" "\<And>z. z \<in> S \<Longrightarrow> f z = cos(g z)"
sorry

lemma contractible_imp_holomorphic_arccos_bounded:
  assumes holf: "f holomorphic_on S" and S: "contractible S" and "a \<in> S"
      and non1: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 1 \<and> f z \<noteq> -1"
  obtains g where "g holomorphic_on S" "norm(g a) \<le> pi + norm(f a)" "\<And>z. z \<in> S \<Longrightarrow> f z = cos(g z)"
sorry


subsection\<open>The "Borsukian" property of sets\<close>

text\<open>This doesn't have a standard name. Kuratowski uses ``contractible with respect to \<open>[S\<^sup>1]\<close>''
 while Whyburn uses ``property b''. It's closely related to unicoherence.\<close>

definition\<^marker>\<open>tag important\<close> Borsukian where
    "Borsukian S \<equiv>
        \<forall>f. continuous_on S f \<and> f \<in> S \<rightarrow> (- {0::complex})
            \<longrightarrow> (\<exists>a. homotopic_with_canon (\<lambda>h. True) S (- {0}) f (\<lambda>x. a))"

lemma Borsukian_retraction_gen:
  assumes "Borsukian S" "continuous_on S h" "h ` S = T"
          "continuous_on T k"  "k \<in> T \<rightarrow> S"  "\<And>y. y \<in> T \<Longrightarrow> h(k y) = y"
    shows "Borsukian T"
sorry

lemma retract_of_Borsukian: "\<lbrakk>Borsukian T; S retract_of T\<rbrakk> \<Longrightarrow> Borsukian S"
sorry

lemma homeomorphic_Borsukian: "\<lbrakk>Borsukian S; S homeomorphic T\<rbrakk> \<Longrightarrow> Borsukian T"
sorry

lemma homeomorphic_Borsukian_eq:
   "S homeomorphic T \<Longrightarrow> Borsukian S \<longleftrightarrow> Borsukian T"
sorry

lemma Borsukian_translation:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian (image (\<lambda>x. a + x) S) \<longleftrightarrow> Borsukian S"
sorry

lemma Borsukian_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "Borsukian(f ` S) \<longleftrightarrow> Borsukian S"
sorry

lemma homotopy_eqv_Borsukianness:
  fixes S :: "'a::real_normed_vector set"
    and T :: "'b::real_normed_vector set"
   assumes "S homotopy_eqv T"
     shows "(Borsukian S \<longleftrightarrow> Borsukian T)"
sorry

lemma Borsukian_alt:
  fixes S :: "'a::real_normed_vector set"
  shows
   "Borsukian S \<longleftrightarrow>
        (\<forall>f g. continuous_on S f \<and> f \<in> S \<rightarrow> -{0} \<and>
               continuous_on S g \<and> g \<in> S \<rightarrow> -{0}
               \<longrightarrow> homotopic_with_canon (\<lambda>h. True) S (- {0::complex}) f g)"
sorry

lemma Borsukian_continuous_logarithm:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
            (\<forall>f. continuous_on S f \<and> f \<in> S \<rightarrow> (- {0::complex})
                 \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(g x))))"
sorry

lemma Borsukian_continuous_logarithm_circle:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
             (\<forall>f. continuous_on S f \<and> f \<in> S \<rightarrow> sphere (0::complex) 1
                  \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>x \<in> S. f x = exp(g x))))"
   (is "?lhs = ?rhs")
sorry

lemma Borsukian_continuous_logarithm_circle_real:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
         (\<forall>f. continuous_on S f \<and> f \<in> S \<rightarrow> sphere (0::complex) 1
              \<longrightarrow> (\<exists>g. continuous_on S (complex_of_real \<circ> g) \<and> (\<forall>x \<in> S. f x = exp(\<i> * of_real(g x)))))"
   (is "?lhs = ?rhs")
sorry

lemma Borsukian_circle:
  fixes S :: "'a::real_normed_vector set"
  shows "Borsukian S \<longleftrightarrow>
         (\<forall>f. continuous_on S f \<and> f \<in> S \<rightarrow> sphere (0::complex) 1
              \<longrightarrow> (\<exists>a. homotopic_with_canon (\<lambda>h. True) S (sphere (0::complex) 1) f (\<lambda>x. a)))"
sorry

lemma contractible_imp_Borsukian: "contractible S \<Longrightarrow> Borsukian S"
sorry

lemma simply_connected_imp_Borsukian:
  fixes S :: "'a::real_normed_vector set"
  shows  "\<lbrakk>simply_connected S; locally path_connected S\<rbrakk> \<Longrightarrow> Borsukian S"
sorry

lemma starlike_imp_Borsukian:
  fixes S :: "'a::real_normed_vector set"
  shows "starlike S \<Longrightarrow> Borsukian S"
sorry

lemma Borsukian_empty: "Borsukian {}"
sorry

lemma Borsukian_UNIV: "Borsukian (UNIV :: 'a::real_normed_vector set)"
sorry

lemma convex_imp_Borsukian:
  fixes S :: "'a::real_normed_vector set"
  shows "convex S \<Longrightarrow> Borsukian S"
sorry

proposition Borsukian_sphere:
  fixes a :: "'a::euclidean_space"
  shows "3 \<le> DIM('a) \<Longrightarrow> Borsukian (sphere a r)"
sorry

lemma Borsukian_Un_lemma:
  fixes S :: "'a::real_normed_vector set"
  assumes BS: "Borsukian S" and BT: "Borsukian T" and ST: "connected(S \<inter> T)"
    and *:  "\<And>f g::'a \<Rightarrow> complex. 
                 \<lbrakk>continuous_on S f; continuous_on T g; \<And>x. x \<in> S \<and> x \<in> T \<Longrightarrow> f x = g x\<rbrakk>
           \<Longrightarrow> continuous_on (S \<union> T) (\<lambda>x. if x \<in> S then f x else g x)"
  shows "Borsukian(S \<union> T)"
sorry

proposition Borsukian_open_Un:
  fixes S :: "'a::real_normed_vector set"
  assumes opeS: "openin (top_of_set (S \<union> T)) S"
      and opeT: "openin (top_of_set (S \<union> T)) T"
      and BS: "Borsukian S" and BT: "Borsukian T" and ST: "connected(S \<inter> T)"
    shows "Borsukian(S \<union> T)"
sorry

lemma Borsukian_closed_Un:
  fixes S :: "'a::real_normed_vector set"
  assumes cloS: "closedin (top_of_set (S \<union> T)) S"
      and cloT: "closedin (top_of_set (S \<union> T)) T"
      and BS: "Borsukian S" and BT: "Borsukian T" and ST: "connected(S \<inter> T)"
    shows "Borsukian(S \<union> T)"
sorry

lemma Borsukian_separation_compact:
  fixes S :: "complex set"
  assumes "compact S"
    shows "Borsukian S \<longleftrightarrow> connected(- S)"
sorry

lemma Borsukian_monotone_image_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Borsukian S" and contf: "continuous_on S f" and fim: "f ` S = T"
      and "compact S" and conn: "\<And>y. y \<in> T \<Longrightarrow> connected {x. x \<in> S \<and> f x = y}"
    shows "Borsukian T"
sorry

lemma Borsukian_open_map_image_compact:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Borsukian S" and contf: "continuous_on S f" and fim: "f ` S = T" and "compact S"
      and ope: "\<And>U. openin (top_of_set S) U
                     \<Longrightarrow> openin (top_of_set T) (f ` U)"
    shows "Borsukian T"
sorry


text\<open>If two points are separated by a closed set, there's a minimal one.\<close>
proposition closed_irreducible_separator:
  fixes a :: "'a::real_normed_vector"
  assumes "closed S" and ab: "\<not> connected_component (- S) a b"
  obtains T where "T \<subseteq> S" "closed T" "T \<noteq> {}" "\<not> connected_component (- T) a b"
                  "\<And>U. U \<subset> T \<Longrightarrow> connected_component (- U) a b"
sorry

lemma frontier_minimal_separating_closed_pointwise:
  fixes S :: "'a::real_normed_vector set"
  assumes S: "closed S" "a \<notin> S" and nconn: "\<not> connected_component (- S) a b"
      and conn: "\<And>T. \<lbrakk>closed T; T \<subset> S\<rbrakk> \<Longrightarrow> connected_component (- T) a b"
    shows "frontier(connected_component_set (- S) a) = S" (is "?F = S")
sorry


subsection\<open>Unicoherence (closed)\<close>

definition\<^marker>\<open>tag important\<close> unicoherent where
  "unicoherent U \<equiv>
  \<forall>S T. connected S \<and> connected T \<and> S \<union> T = U \<and>
        closedin (top_of_set U) S \<and> closedin (top_of_set U) T
        \<longrightarrow> connected (S \<inter> T)"

lemma unicoherentI [intro?]:
  assumes "\<And>S T. \<lbrakk>connected S; connected T; U = S \<union> T; closedin (top_of_set U) S; closedin (top_of_set U) T\<rbrakk>
          \<Longrightarrow> connected (S \<inter> T)"
  shows "unicoherent U"
sorry

lemma unicoherentD:
  assumes "unicoherent U" "connected S" "connected T" "U = S \<union> T" "closedin (top_of_set U) S" "closedin (top_of_set U) T"
  shows "connected (S \<inter> T)"
sorry

proposition homeomorphic_unicoherent:
  assumes ST: "S homeomorphic T" and S: "unicoherent S"
  shows "unicoherent T"
sorry

lemma homeomorphic_unicoherent_eq:
   "S homeomorphic T \<Longrightarrow> (unicoherent S \<longleftrightarrow> unicoherent T)"
sorry

lemma unicoherent_translation:
  fixes S :: "'a::real_normed_vector set"
  shows
   "unicoherent (image (\<lambda>x. a + x) S) \<longleftrightarrow> unicoherent S"
sorry

lemma unicoherent_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  shows "(unicoherent(f ` S) \<longleftrightarrow> unicoherent S)"
sorry

lemma Borsukian_imp_unicoherent:
  fixes U :: "'a::euclidean_space set"
  assumes "Borsukian U"  shows "unicoherent U"
sorry

corollary contractible_imp_unicoherent:
  fixes U :: "'a::euclidean_space set"
  assumes "contractible U"  shows "unicoherent U"
sorry

corollary convex_imp_unicoherent:
  fixes U :: "'a::euclidean_space set"
  assumes "convex U"  shows "unicoherent U"
sorry

text\<open>If the type class constraint can be relaxed, I don't know how!\<close>
corollary unicoherent_UNIV: "unicoherent (UNIV :: 'a :: euclidean_space set)"
sorry

lemma unicoherent_monotone_image_compact:
  fixes T :: "'b :: t2_space set"
  assumes S: "unicoherent S" "compact S" and contf: "continuous_on S f" and fim: "f ` S = T"
  and conn: "\<And>y. y \<in> T \<Longrightarrow> connected (S \<inter> f -` {y})"
  shows "unicoherent T"
sorry


subsection\<open>Several common variants of unicoherence\<close>

lemma connected_frontier_simple:
  fixes S :: "'a :: euclidean_space set"
  assumes "connected S" "connected(- S)" shows "connected(frontier S)"
sorry

lemma connected_frontier_component_complement:
  fixes S :: "'a :: euclidean_space set"
  assumes "connected S" "C \<in> components(- S)" shows "connected(frontier C)"
sorry

lemma connected_frontier_disjoint:
  fixes S :: "'a :: euclidean_space set"
  assumes "connected S" "connected T" "disjnt S T" and ST: "frontier S \<subseteq> frontier T"
  shows "connected(frontier S)"
sorry


subsection\<open>Some separation results\<close>

lemma separation_by_component_closed_pointwise:
  fixes S :: "'a :: euclidean_space set"
  assumes "closed S" "\<not> connected_component (- S) a b"
  obtains C where "C \<in> components S" "\<not> connected_component(- C) a b"
sorry

lemma separation_by_component_closed:
  fixes S :: "'a :: euclidean_space set"
  assumes "closed S" "\<not> connected(- S)"
  obtains C where "C \<in> components S" "\<not> connected(- C)"
sorry

lemma separation_by_Un_closed_pointwise:
  fixes S :: "'a :: euclidean_space set"
  assumes ST: "closed S" "closed T" "S \<inter> T = {}"
      and conS: "connected_component (- S) a b" and conT: "connected_component (- T) a b"
    shows "connected_component (- (S \<union> T)) a b"
sorry

lemma separation_by_Un_closed:
  fixes S :: "'a :: euclidean_space set"
  assumes ST: "closed S" "closed T" "S \<inter> T = {}" and conS: "connected(- S)" and conT: "connected(- T)"
  shows "connected(- (S \<union> T))"
sorry

lemma open_unicoherent_UNIV:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "open T" "connected S" "connected T" "S \<union> T = UNIV"
  shows "connected(S \<inter> T)"
sorry

lemma separation_by_component_open_aux:
  fixes S :: "'a :: euclidean_space set"
  assumes ST: "closed S" "closed T" "S \<inter> T = {}"
      and "S \<noteq> {}" "T \<noteq> {}"
  obtains C where "C \<in> components(-(S \<union> T))" "C \<noteq> {}" "frontier C \<inter> S \<noteq> {}" "frontier C \<inter> T \<noteq> {}"
sorry

proposition separation_by_component_open:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" and non: "\<not> connected(- S)"
  obtains C where "C \<in> components S" "\<not> connected(- C)"
sorry

lemma separation_by_Un_open:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "open T" "S \<inter> T = {}" and cS: "connected(-S)" and cT: "connected(-T)"
    shows "connected(- (S \<union> T))"
sorry

lemma nonseparation_by_component_eq:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S \<or> closed S"
  shows "((\<forall>C \<in> components S. connected(-C)) \<longleftrightarrow> connected(- S))"
sorry

text\<open>Another interesting equivalent of an inessential mapping into C-{0}\<close>
proposition inessential_eq_extensible:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes "closed S"
  shows "(\<exists>a. homotopic_with_canon (\<lambda>h. True) S (-{0}) f (\<lambda>t. a)) \<longleftrightarrow>
         (\<exists>g. continuous_on UNIV g \<and> (\<forall>x \<in> S. g x = f x) \<and> (\<forall>x. g x \<noteq> 0))"
     (is "?lhs = ?rhs")
sorry

lemma inessential_on_clopen_Union:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes T: "path_connected T"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> closedin (top_of_set (\<Union>\<F>)) S"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set (\<Union>\<F>)) S"
      and hom: "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>a. homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. a)"
  obtains a where "homotopic_with_canon (\<lambda>x. True) (\<Union>\<F>) T f (\<lambda>x. a)"
sorry

proposition Janiszewski_dual:
  fixes S :: "complex set"
  assumes "compact S" "compact T" "connected S" "connected T" "connected(- (S \<union> T))"
 shows "connected(S \<inter> T)"
sorry

end
