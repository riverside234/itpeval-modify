(*  Title:      HOL/Analysis/Riemann_Mapping.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>Moebius functions, Equivalents of Simply Connected Sets, Riemann Mapping Theorem\<close>

theory Riemann_Mapping
imports Great_Picard
begin

subsection\<open>Moebius functions are biholomorphisms of the unit disc\<close>

definition\<^marker>\<open>tag important\<close> Moebius_function :: "[real,complex,complex] \<Rightarrow> complex" where
  "Moebius_function \<equiv> \<lambda>t w z. exp(\<i> * of_real t) * (z - w) / (1 - cnj w * z)"

lemma Moebius_function_simple:
   "Moebius_function 0 w z = (z - w) / (1 - cnj w * z)"
sorry

lemma Moebius_function_eq_zero:
   "Moebius_function t w w = 0"
sorry

lemma Moebius_function_of_zero:
   "Moebius_function t w 0 = - exp(\<i> * of_real t) * w"
sorry

lemma Moebius_function_norm_lt_1:
  assumes w1: "norm w < 1" and z1: "norm z < 1"
  shows "norm (Moebius_function t w z) < 1"
sorry

lemma Moebius_function_holomorphic:
  assumes "norm w < 1"
  shows "Moebius_function t w holomorphic_on ball 0 1"
sorry

lemma Moebius_function_compose:
  assumes meq: "-w1 = w2" and "norm w1 < 1" "norm z < 1"
  shows "Moebius_function 0 w1 (Moebius_function 0 w2 z) = z"
sorry

lemma ball_biholomorphism_exists:
  assumes "a \<in> ball 0 1"
  obtains f g where "f a = 0"
                "f holomorphic_on ball 0 1" "f ` ball 0 1 \<subseteq> ball 0 1"
                "g holomorphic_on ball 0 1" "g ` ball 0 1 \<subseteq> ball 0 1"
                "\<And>z. z \<in> ball 0 1 \<Longrightarrow> f (g z) = z"
                "\<And>z. z \<in> ball 0 1 \<Longrightarrow> g (f z) = z"
sorry


subsection\<open>A big chain of equivalents of simple connectedness for an open set\<close>

lemma biholomorphic_to_disc_aux:
  assumes "open S" "connected S" "0 \<in> S" and S01: "S \<subseteq> ball 0 1"
      and prev: "\<And>f. \<lbrakk>f holomorphic_on S; \<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0; inj_on f S\<rbrakk>
               \<Longrightarrow> \<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
  shows "\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
               (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
               (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z)"
sorry


locale SC_Chain =
  fixes S :: "complex set"
  assumes openS: "open S"
begin

lemma winding_number_zero:
  assumes "simply_connected S"
  shows "connected S \<and>
         (\<forall>\<gamma> z. path \<gamma> \<and> path_image \<gamma> \<subseteq> S \<and>
                   pathfinish \<gamma> = pathstart \<gamma> \<and> z \<notin> S \<longrightarrow> winding_number \<gamma> z = 0)"
sorry

lemma contour_integral_zero:
  assumes "valid_path g" "path_image g \<subseteq> S" "pathfinish g = pathstart g" "f holomorphic_on S"
         "\<And>\<gamma> z. \<lbrakk>path \<gamma>; path_image \<gamma> \<subseteq> S; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> S\<rbrakk> \<Longrightarrow> winding_number \<gamma> z = 0"
  shows "(f has_contour_integral 0) g"
sorry

lemma global_primitive:
  assumes "connected S" and holf: "f holomorphic_on S"
  and prev: "\<And>\<gamma> f. \<lbrakk>valid_path \<gamma>; path_image \<gamma> \<subseteq> S; pathfinish \<gamma> = pathstart \<gamma>; f holomorphic_on S\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) \<gamma>"
  shows "\<exists>h. \<forall>z \<in> S. (h has_field_derivative f z) (at z)"
sorry

lemma holomorphic_log:
  assumes "connected S" and holf: "f holomorphic_on S" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  and prev: "\<And>f. f holomorphic_on S \<Longrightarrow> \<exists>h. \<forall>z \<in> S. (h has_field_derivative f z) (at z)"
  shows "\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = exp(g z))"
sorry

lemma holomorphic_sqrt:
  assumes holf: "f holomorphic_on S" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  and prev: "\<And>f. \<lbrakk>f holomorphic_on S; \<forall>z \<in> S. f z \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = exp(g z))"
  shows "\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
sorry

lemma biholomorphic_to_disc:
  assumes "connected S" and S: "S \<noteq> {}" "S \<noteq> UNIV"
  and prev: "\<And>f. \<lbrakk>f holomorphic_on S; \<forall>z \<in> S. f z \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
  shows "\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
                   (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
                   (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z)"
sorry

lemma homeomorphic_to_disc:
  assumes "S = UNIV \<or>
               (\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
                      (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
                      (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z))" (is "_ \<or> ?P")
  shows "S homeomorphic ball (0::complex) 1"
sorry

lemma homeomorphic_to_disc_imp_simply_connected:
  assumes "S = {} \<or> S homeomorphic ball (0::complex) 1"
  shows "simply_connected S"
sorry

end

proposition
  assumes "open S"
  shows simply_connected_eq_winding_number_zero:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>g z. path g \<and> path_image g \<subseteq> S \<and>
                 pathfinish g = pathstart g \<and> (z \<notin> S)
                 \<longrightarrow> winding_number g z = 0)" (is "?wn0")
    and simply_connected_eq_contour_integral_zero:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>g f. valid_path g \<and> path_image g \<subseteq> S \<and>
                 pathfinish g = pathstart g \<and> f holomorphic_on S
               \<longrightarrow> (f has_contour_integral 0) g)" (is "?ci0")
    and simply_connected_eq_global_primitive:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>f. f holomorphic_on S \<longrightarrow>
                (\<exists>h. \<forall>z. z \<in> S \<longrightarrow> (h has_field_derivative f z) (at z)))" (is "?gp")
    and simply_connected_eq_holomorphic_log:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>f. f holomorphic_on S \<and> (\<forall>z \<in> S. f z \<noteq> 0)
               \<longrightarrow> (\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S. f z = exp(g z))))" (is "?log")
    and simply_connected_eq_holomorphic_sqrt:
         "simply_connected S \<longleftrightarrow>
           connected S \<and>
           (\<forall>f. f holomorphic_on S \<and> (\<forall>z \<in> S. f z \<noteq> 0)
                \<longrightarrow> (\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S.  f z = (g z)\<^sup>2)))" (is "?sqrt")
    and simply_connected_eq_biholomorphic_to_disc:
         "simply_connected S \<longleftrightarrow>
           S = {} \<or> S = UNIV \<or>
           (\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
                 (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
                 (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z))" (is "?bih")
    and simply_connected_eq_homeomorphic_to_disc:
          "simply_connected S \<longleftrightarrow> S = {} \<or> S homeomorphic ball (0::complex) 1" (is "?disc")
sorry

corollary contractible_eq_simply_connected_2d:
  fixes S :: "complex set"
  assumes "open S"
  shows "contractible S \<longleftrightarrow> simply_connected S"
sorry

subsection\<open>A further chain of equivalences about components of the complement of a simply connected set\<close>

text\<open>(following 1.35 in Burckel'S book)\<close>

context SC_Chain
begin

lemma frontier_properties:
  assumes "simply_connected S"
  shows "if bounded S then connected(frontier S)
         else \<forall>C \<in> components(frontier S). \<not> bounded C"
sorry

lemma unbounded_complement_components:
  assumes C: "C \<in> components (- S)" and S: "connected S"
    and prev: "if bounded S then connected(frontier S)
               else \<forall>C \<in> components(frontier S). \<not> bounded C"
  shows "\<not> bounded C"
sorry

lemma empty_inside:
  assumes "connected S" "\<And>C. C \<in> components (- S) \<Longrightarrow> \<not> bounded C"
  shows "inside S = {}"
sorry

lemma empty_inside_imp_simply_connected:
  "\<lbrakk>connected S; inside S = {}\<rbrakk> \<Longrightarrow> simply_connected S"
sorry

end

proposition
  fixes S :: "complex set"
  assumes "open S"
  shows simply_connected_eq_frontier_properties:
         "simply_connected S \<longleftrightarrow>
          connected S \<and>
             (if bounded S then connected(frontier S)
             else (\<forall>C \<in> components(frontier S). \<not>bounded C))" (is "?fp")
    and simply_connected_eq_unbounded_complement_components:
         "simply_connected S \<longleftrightarrow>
          connected S \<and> (\<forall>C \<in> components(- S). \<not>bounded C)" (is "?ucc")
    and simply_connected_eq_empty_inside:
         "simply_connected S \<longleftrightarrow>
          connected S \<and> inside S = {}" (is "?ei")
sorry

lemma simply_connected_iff_simple:
  fixes S :: "complex set"
  assumes "open S" "bounded S"
  shows "simply_connected S \<longleftrightarrow> connected S \<and> connected(- S)" (is "?lhs = ?rhs")
sorry

lemma subset_simply_connected_imp_inside_subset:
  fixes A :: "complex set"
  assumes "simply_connected A" "open A" "B \<subseteq> A"
  shows   "inside B \<subseteq> A"
sorry

subsection\<open>Further equivalences based on continuous logs and sqrts\<close>

context SC_Chain
begin

lemma continuous_log:
  fixes f :: "complex\<Rightarrow>complex"
  assumes S: "simply_connected S"
    and contf: "continuous_on S f" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
  shows "\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = exp(g z))"
sorry

lemma continuous_sqrt:
  fixes f :: "complex\<Rightarrow>complex"
  assumes contf: "continuous_on S f" and nz: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0"
    and prev: "\<And>f::complex\<Rightarrow>complex.
                \<lbrakk>continuous_on S f; \<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 0\<rbrakk>
                  \<Longrightarrow> \<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = exp(g z))"
  shows "\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
sorry

lemma continuous_sqrt_imp_simply_connected:
  assumes "connected S"
    and prev: "\<And>f::complex\<Rightarrow>complex. \<lbrakk>continuous_on S f; \<forall>z \<in> S. f z \<noteq> 0\<rbrakk>
                \<Longrightarrow> \<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)"
  shows "simply_connected S"
sorry

end

proposition
  fixes S :: "complex set"
  assumes "open S"
  shows simply_connected_eq_continuous_log:
         "simply_connected S \<longleftrightarrow>
          connected S \<and>
          (\<forall>f::complex\<Rightarrow>complex. continuous_on S f \<and> (\<forall>z \<in> S. f z \<noteq> 0)
            \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = exp (g z))))" (is "?log")
    and simply_connected_eq_continuous_sqrt:
         "simply_connected S \<longleftrightarrow>
          connected S \<and>
          (\<forall>f::complex\<Rightarrow>complex. continuous_on S f \<and> (\<forall>z \<in> S. f z \<noteq> 0)
            \<longrightarrow> (\<exists>g. continuous_on S g \<and> (\<forall>z \<in> S. f z = (g z)\<^sup>2)))" (is "?sqrt")
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>More Borsukian results\<close>

lemma Borsukian_componentwise_eq:
  fixes S :: "'a::euclidean_space set"
  assumes S: "locally connected S \<or> compact S"
  shows "Borsukian S \<longleftrightarrow> (\<forall>C \<in> components S. Borsukian C)"
sorry

lemma Borsukian_componentwise:
  fixes S :: "'a::euclidean_space set"
  assumes "locally connected S \<or> compact S" "\<And>C. C \<in> components S \<Longrightarrow> Borsukian C"
  shows "Borsukian S"
sorry

lemma simply_connected_eq_Borsukian:
  fixes S :: "complex set"
  shows "open S \<Longrightarrow> (simply_connected S \<longleftrightarrow> connected S \<and> Borsukian S)"
sorry

lemma Borsukian_eq_simply_connected:
  fixes S :: "complex set"
  shows "open S \<Longrightarrow> Borsukian S \<longleftrightarrow> (\<forall>C \<in> components S. simply_connected C)"
sorry

lemma Borsukian_separation_open_closed:
  fixes S :: "complex set"
  assumes S: "open S \<or> closed S" and "bounded S"
  shows "Borsukian S \<longleftrightarrow> connected(- S)"
sorry

subsection\<open>Finally, the Riemann Mapping Theorem\<close>

theorem Riemann_mapping_theorem:
    "open S \<and> simply_connected S \<longleftrightarrow>
     S = {} \<or> S = UNIV \<or>
     (\<exists>f g. f holomorphic_on S \<and> g holomorphic_on ball 0 1 \<and>
           (\<forall>z \<in> S. f z \<in> ball 0 1 \<and> g(f z) = z) \<and>
           (\<forall>z \<in> ball 0 1. g z \<in> S \<and> f(g z) = z))"
    (is "_ = ?rhs")
sorry


subsection \<open>Applications to Winding Numbers\<close>

lemma simply_connected_inside_simple_path:
  fixes p :: "real \<Rightarrow> complex"
  shows "simple_path p \<Longrightarrow> simply_connected(inside(path_image p))"
sorry

lemma simply_connected_Int:
  fixes S :: "complex set"
  assumes "open S" "open T" "simply_connected S" "simply_connected T" "connected (S \<inter> T)"
  shows "simply_connected (S \<inter> T)"
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>The winding number defines a continuous logarithm for the path itself\<close>

lemma winding_number_as_continuous_log:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  obtains q where "path q"
                  "pathfinish q - pathstart q = 2 * of_real pi * \<i> * winding_number p \<zeta>"
                  "\<And>t. t \<in> {0..1} \<Longrightarrow> p t = \<zeta> + exp(q t)"
sorry

subsection \<open>Winding number equality is the same as path/loop homotopy in C - {0}\<close>

lemma winding_number_homotopic_loops_null_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> (\<exists>a. homotopic_loops (-{\<zeta>}) p (\<lambda>t. a))"
    (is "?lhs = ?rhs")
sorry

lemma winding_number_homotopic_paths_null_explicit_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> homotopic_paths (-{\<zeta>}) p (linepath (pathstart p) (pathstart p))"
        (is "?lhs = ?rhs")
sorry

lemma winding_number_homotopic_paths_null_eq:
  assumes "path p" and \<zeta>: "\<zeta> \<notin> path_image p"
  shows "winding_number p \<zeta> = 0 \<longleftrightarrow> (\<exists>a. homotopic_paths (-{\<zeta>}) p (\<lambda>t. a))"
    (is "?lhs = ?rhs")
sorry

proposition winding_number_homotopic_paths_eq:
  assumes "path p" and \<zeta>p: "\<zeta> \<notin> path_image p"
      and "path q" and \<zeta>q: "\<zeta> \<notin> path_image q"
      and qp: "pathstart q = pathstart p" "pathfinish q = pathfinish p"
    shows "winding_number p \<zeta> = winding_number q \<zeta> \<longleftrightarrow> homotopic_paths (-{\<zeta>}) p q"
    (is "?lhs = ?rhs")
sorry

lemma winding_number_homotopic_loops_eq:
  assumes "path p" and \<zeta>p: "\<zeta> \<notin> path_image p"
      and "path q" and \<zeta>q: "\<zeta> \<notin> path_image q"
      and loops: "pathfinish p = pathstart p" "pathfinish q = pathstart q"
    shows "winding_number p \<zeta> = winding_number q \<zeta> \<longleftrightarrow> homotopic_loops (-{\<zeta>}) p q"
    (is "?lhs = ?rhs")
sorry

end
