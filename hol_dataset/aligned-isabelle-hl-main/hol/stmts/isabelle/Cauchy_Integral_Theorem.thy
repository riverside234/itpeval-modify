section \<open>Complex Path Integrals and Cauchy's Integral Theorem\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2015)\<close>

theory Cauchy_Integral_Theorem
imports
  "HOL-Analysis.Analysis"
  Contour_Integration
begin

lemma leibniz_rule_holomorphic:
  fixes f::"complex \<Rightarrow> 'b::euclidean_space \<Rightarrow> complex"
  assumes "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes "convex U"
  shows "(\<lambda>x. integral (cbox a b) (f x)) holomorphic_on U"
sorry

lemma Ln_measurable [measurable]: "Ln \<in> measurable borel borel"
sorry

lemma powr_complex_measurable [measurable]:
  assumes [measurable]: "f \<in> measurable M borel" "g \<in> measurable M borel"
  shows   "(\<lambda>x. f x powr g x :: complex) \<in> measurable M borel"
sorry
text\<open>The special case of midpoints used in the main quadrisection\<close>

lemma has_contour_integral_midpoint:
  assumes "(f has_contour_integral i) (linepath a (midpoint a b))"
          "(f has_contour_integral j) (linepath (midpoint a b) b)"
    shows "(f has_contour_integral (i + j)) (linepath a b)"
sorry

lemma contour_integral_midpoint:
  assumes "continuous_on (closed_segment a b) f"
  shows "contour_integral (linepath a b) f =
         contour_integral (linepath a (midpoint a b)) f + contour_integral (linepath (midpoint a b) b) f"
sorry


text\<open>A couple of special case lemmas that are useful below\<close>

lemma triangle_linear_has_chain_integral:
    "((\<lambda>x. m*x + d) has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
sorry

lemma has_chain_integral_chain_integral3:
  assumes "(f has_contour_integral i) (linepath a b +++ linepath b c +++ linepath c d)" 
           (is "(f has_contour_integral i) ?g")
  shows "contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c d) f = i"
       (is "?lhs = _")
sorry

lemma has_chain_integral_chain_integral4:
  assumes "(f has_contour_integral i) (linepath a b +++ linepath b c +++ linepath c d +++ linepath d e)" 
           (is "(f has_contour_integral i) ?g")
  shows "contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c d) f + contour_integral (linepath d e) f = i"
       (is "?lhs = _")
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>The key quadrisection step\<close>

lemma norm_sum_half:
  assumes "norm(a + b) \<ge> e"
    shows "norm a \<ge> e/2 \<or> norm b \<ge> e/2"
sorry

lemma norm_sum_lemma:
  assumes "e \<le> norm (a + b + c + d)"
    shows "e / 4 \<le> norm a \<or> e / 4 \<le> norm b \<or> e / 4 \<le> norm c \<or> e / 4 \<le> norm d"
sorry

lemma Cauchy_theorem_quadrisection:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and dist: "dist a b \<le> K" "dist b c \<le> K" "dist c a \<le> K"
      and e: "e * K^2 \<le>
              norm (contour_integral(linepath a b) f + contour_integral(linepath b c) f + contour_integral(linepath c a) f)"
  shows "\<exists>a' b' c'.
           a' \<in> convex hull {a,b,c} \<and> b' \<in> convex hull {a,b,c} \<and> c' \<in> convex hull {a,b,c} \<and>
           dist a' b' \<le> K/2  \<and>  dist b' c' \<le> K/2  \<and>  dist c' a' \<le> K/2  \<and>
           e * (K/2)^2 \<le> norm(contour_integral(linepath a' b') f + contour_integral(linepath b' c') f + contour_integral(linepath c' a') f)"
         (is "\<exists>x y z. ?\<Phi> x y z")
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Cauchy's theorem for triangles\<close>

lemma triangle_points_closer:
  fixes a::complex
  shows "\<lbrakk>x \<in> convex hull {a,b,c};  y \<in> convex hull {a,b,c}\<rbrakk>
         \<Longrightarrow> norm(x - y) \<le> norm(a - b) \<or>
             norm(x - y) \<le> norm(b - c) \<or>
             norm(x - y) \<le> norm(c - a)"
sorry

lemma holomorphic_point_small_triangle:
  assumes x: "x \<in> S"
      and f: "continuous_on S f"
      and cd: "f field_differentiable (at x within S)"
      and e: "0 < e"
    shows "\<exists>k>0. \<forall>a b c. dist a b \<le> k \<and> dist b c \<le> k \<and> dist c a \<le> k \<and>
              x \<in> convex hull {a,b,c} \<and> convex hull {a,b,c} \<subseteq> S
              \<longrightarrow> norm(contour_integral(linepath a b) f + contour_integral(linepath b c) f +
                       contour_integral(linepath c a) f)
                  \<le> e*(dist a b + dist b c + dist c a)^2"
           (is "\<exists>k>0. \<forall>a b c. _ \<longrightarrow> ?normle a b c")
sorry



text\<open>Hence the most basic theorem for a triangle.\<close>

locale Chain =
  fixes x0 At Follows
  assumes At0: "At x0 0"
      and AtSuc: "\<And>x n. At x n \<Longrightarrow> \<exists>x'. At x' (Suc n) \<and> Follows x' x"
begin
  primrec f where
    "f 0 = x0"
  | "f (Suc n) = (SOME x. At x (Suc n) \<and> Follows x (f n))"

  lemma At: "At (f n) n"
sorry

  lemma Follows: "Follows (f(Suc n)) (f n)"
sorry
  declare f.simps(2) [simp del]
end

lemma Chain3:
  assumes At0: "At x0 y0 z0 0"
      and AtSuc: "\<And>x y z n. At x y z n \<Longrightarrow> \<exists>x' y' z'. At x' y' z' (Suc n) \<and> Follows x' y' z' x y z"
  obtains f g h where
    "f 0 = x0" "g 0 = y0" "h 0 = z0"
                      "\<And>n. At (f n) (g n) (h n) n"
                       "\<And>n. Follows (f(Suc n)) (g(Suc n)) (h(Suc n)) (f n) (g n) (h n)"
sorry

proposition\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_triangle:
  assumes "f holomorphic_on (convex hull {a,b,c})"
    shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Version needing function holomorphic in interior only\<close>

lemma Cauchy_theorem_flat_lemma:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
      and k: "0 \<le> k"
    shows "contour_integral (linepath a b) f + contour_integral (linepath b c) f +
          contour_integral (linepath c a) f = 0"
sorry

lemma Cauchy_theorem_flat:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
sorry

proposition Cauchy_theorem_triangle_interior:
  assumes contf: "continuous_on (convex hull {a,b,c}) f"
      and holf:  "f holomorphic_on interior (convex hull {a,b,c})"
     shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Version allowing finite number of exceptional points\<close>

proposition\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_triangle_cofinite:
  assumes "continuous_on (convex hull {a,b,c}) f"
      and "finite S"
      and "(\<And>x. x \<in> interior(convex hull {a,b,c}) - S \<Longrightarrow> f field_differentiable (at x))"
     shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
sorry
subsection\<^marker>\<open>tag unimportant\<close> \<open>Cauchy's theorem for an open starlike set\<close>

lemma starlike_convex_subset:
  assumes S: "a \<in> S" "closed_segment b c \<subseteq> S" and subs: "\<And>x. x \<in> S \<Longrightarrow> closed_segment a x \<subseteq> S"
  shows "convex hull {a,b,c} \<subseteq> S"
sorry

lemma triangle_contour_integrals_starlike_primitive:
  assumes contf: "continuous_on S f"
      and S: "a \<in> S" "open S"
      and x: "x \<in> S"
      and subs: "\<And>y. y \<in> S \<Longrightarrow> closed_segment a y \<subseteq> S"
      and zer: "\<And>b c. closed_segment b c \<subseteq> S
                   \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f +
                       contour_integral (linepath c a) f = 0"
    shows "((\<lambda>x. contour_integral(linepath a x) f) has_field_derivative f x) (at x)"
sorry


text \<open>Existence of a primitive\<close>
lemma holomorphic_starlike_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes contf: "continuous_on S f"
      and S: "starlike S" and os: "open S"
      and k: "finite k"
      and fcd: "\<And>x. x \<in> S - k \<Longrightarrow> f field_differentiable at x"
    shows "\<exists>g. \<forall>x \<in> S. (g has_field_derivative f x) (at x)"
sorry

lemma Cauchy_theorem_starlike:
 "\<lbrakk>open S; starlike S; finite k; continuous_on S f;
   \<And>x. x \<in> S - k \<Longrightarrow> f field_differentiable at x;
   valid_path g; path_image g \<subseteq> S; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_contour_integral 0)  g"
sorry

lemma Cauchy_theorem_starlike_simple:
  "\<lbrakk>open S; starlike S; f holomorphic_on S; valid_path g; path_image g \<subseteq> S; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_contour_integral 0) g"
sorry
subsection\<open>Cauchy's theorem for a convex set\<close>

text\<open>For a convex set we can avoid assuming openness and boundary analyticity\<close>

lemma triangle_contour_integrals_convex_primitive:
  assumes contf: "continuous_on S f"
      and S: "a \<in> S" "convex S"
      and x: "x \<in> S"
      and zer: "\<And>b c. \<lbrakk>b \<in> S; c \<in> S\<rbrakk>
                   \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f +
                       contour_integral (linepath c a) f = 0"
    shows "((\<lambda>x. contour_integral(linepath a x) f) has_field_derivative f x) (at x within S)"
sorry

lemma contour_integral_convex_primitive:
  assumes "convex S" "continuous_on S f"
          "\<And>a b c. \<lbrakk>a \<in> S; b \<in> S; c \<in> S\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
  obtains g where "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative f x) (at x within S)"
sorry

lemma holomorphic_convex_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "convex S" "finite K" and contf: "continuous_on S f"
    and fd: "\<And>x. x \<in> interior S - K \<Longrightarrow> f field_differentiable at x"
  obtains g where "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative f x) (at x within S)"
sorry

lemma holomorphic_convex_primitive':
  fixes f :: "complex \<Rightarrow> complex"
  assumes "convex S" and "open S" and "f holomorphic_on S"
  obtains g where "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative f x) (at x within S)"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_convex:
    "\<lbrakk>continuous_on S f; convex S; finite K;
      \<And>x. x \<in> interior S - K \<Longrightarrow> f field_differentiable at x;
      valid_path g; path_image g \<subseteq> S; pathfinish g = pathstart g\<rbrakk>
     \<Longrightarrow> (f has_contour_integral 0) g"
sorry

corollary Cauchy_theorem_convex_simple:
  assumes holf: "f holomorphic_on S" 
      and "convex S" "valid_path g" "path_image g \<subseteq> S" "pathfinish g = pathstart g"
  shows "(f has_contour_integral 0) g"
sorry


text\<open>In particular for a disc\<close>
corollary\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_disc:
    "\<lbrakk>finite K; continuous_on (cball a e) f;
      \<And>x. x \<in> ball a e - K \<Longrightarrow> f field_differentiable at x;
     valid_path g; path_image g \<subseteq> cball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Cauchy_theorem_disc_simple:
    "\<lbrakk>f holomorphic_on (ball a e); valid_path g; path_image g \<subseteq> ball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
sorry
subsection\<^marker>\<open>tag unimportant\<close> \<open>Generalize integrability to local primitives\<close>

lemma contour_integral_local_primitive_lemma:
  fixes f :: "complex\<Rightarrow>complex"
  assumes gpd: "g piecewise_differentiable_on {a..b}"
      and dh: "\<And>x. x \<in> S \<Longrightarrow> (f has_field_derivative f' x) (at x within S)"
      and gs: "\<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> S"
    shows "(\<lambda>x. f' (g x) * vector_derivative g (at x within {a..b})) integrable_on {a..b}"
sorry

lemma contour_integral_local_primitive_any:
  fixes f :: "complex \<Rightarrow> complex"
  assumes gpd: "g piecewise_differentiable_on {a..b}"
      and dh: "\<And>x. x \<in> S
               \<Longrightarrow> \<exists>d h. 0 < d \<and>
                         (\<forall>y. norm(y - x) < d \<longrightarrow> (h has_field_derivative f y) (at y within S))"
      and gs: "\<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> S"
  shows "(\<lambda>x. f(g x) * vector_derivative g (at x)) integrable_on {a..b}"
sorry

lemma contour_integral_local_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes g: "valid_path g" "path_image g \<subseteq> S"
      and dh: "\<And>x. x \<in> S
               \<Longrightarrow> \<exists>d h. 0 < d \<and>
                         (\<forall>y. norm(y - x) < d \<longrightarrow> (h has_field_derivative f y) (at y within S))"
    shows "f contour_integrable_on g"
sorry



text\<open>In particular if a function is holomorphic\<close>

lemma contour_integrable_holomorphic:
  assumes contf: "continuous_on S f"
      and os: "open S"
      and k: "finite k"
      and g: "valid_path g" "path_image g \<subseteq> S"
      and fcd: "\<And>x. x \<in> S - k \<Longrightarrow> f field_differentiable at x"
    shows "f contour_integrable_on g"
sorry

lemma contour_integrable_holomorphic_simple:
  assumes fh: "f holomorphic_on S"
      and os: "open S"
      and g: "valid_path g" "path_image g \<subseteq> S"
    shows "f contour_integrable_on g"
sorry

lemma analytic_imp_contour_integrable:
  assumes "f analytic_on path_image p" "valid_path p"
  shows   "f contour_integrable_on p"
sorry

lemma continuous_on_inversediff:
  fixes z:: "'a::real_normed_field" shows "z \<notin> S \<Longrightarrow> continuous_on S (\<lambda>w. 1 / (w - z))"
sorry

lemma contour_integrable_inversediff:
  assumes g: "valid_path g"
      and notin: "z \<notin> path_image g"
    shows "(\<lambda>w. 1 / (w-z)) contour_integrable_on g"
sorry


text\<open>Key fact that path integral is the same for a "nearby" path. This is the
 main lemma for the homotopy form of Cauchy's theorem and is also useful
 if we want "without loss of generality" to assume some nice properties of a
 path (e.g. smoothness). It can also be used to define the integrals of
 analytic functions over arbitrary continuous paths. This is just done for
 winding numbers now.
\<close>

text\<open>A technical definition to avoid duplication of similar proofs,
     for paths joined at the ends versus looping paths\<close>
definition linked_paths :: "bool \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "linked_paths atends g h ==
        (if atends then pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                   else pathfinish g = pathstart g \<and> pathfinish h = pathstart h)"

text\<open>This formulation covers two cases: \<^term>\<open>g\<close> and \<^term>\<open>h\<close> share their
      start and end points; \<^term>\<open>g\<close> and \<^term>\<open>h\<close> both loop upon themselves.\<close>
lemma contour_integral_nearby:
  assumes os: "open S" and p: "path p" "path_image p \<subseteq> S"
  shows "\<exists>d. 0 < d \<and>
            (\<forall>g h. valid_path g \<and> valid_path h \<and>
                  (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                  linked_paths atends g h
                  \<longrightarrow> path_image g \<subseteq> S \<and> path_image h \<subseteq> S \<and>
                      (\<forall>f. f holomorphic_on S \<longrightarrow> contour_integral h f = contour_integral g f))"
sorry

lemma
  assumes "open S" "path p" "path_image p \<subseteq> S"
    shows contour_integral_nearby_ends:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                    \<longrightarrow> path_image g \<subseteq> S \<and>
                        path_image h \<subseteq> S \<and>
                        (\<forall>f. f holomorphic_on S
                            \<longrightarrow> contour_integral h f = contour_integral g f))"
    and contour_integral_nearby_loops:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathfinish g = pathstart g \<and> pathfinish h = pathstart h
                    \<longrightarrow> path_image g \<subseteq> S \<and>
                        path_image h \<subseteq> S \<and>
                        (\<forall>f. f holomorphic_on S
                            \<longrightarrow> contour_integral h f = contour_integral g f))"
sorry

lemma contour_integral_bound_exists:
assumes S: "open S"
    and g: "valid_path g"
    and pag: "path_image g \<subseteq> S"
  shows "\<exists>L. 0 < L \<and>
             (\<forall>f B. f holomorphic_on S \<and> (\<forall>z \<in> S. norm(f z) \<le> B)
               \<longrightarrow> norm(contour_integral g f) \<le> L*B)"
sorry



subsection\<open>Homotopy forms of Cauchy's theorem\<close>

lemma Cauchy_theorem_homotopic:
    assumes hom: "if atends then homotopic_paths S g h else homotopic_loops S g h"
        and "open S" and f: "f holomorphic_on S"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
sorry

proposition Cauchy_theorem_homotopic_paths:
    assumes hom: "homotopic_paths S g h"
        and "open S" and f: "f holomorphic_on S"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
sorry

proposition Cauchy_theorem_homotopic_loops:
    assumes hom: "homotopic_loops S g h"
        and "open S" and f: "f holomorphic_on S"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
sorry

lemma has_contour_integral_newpath:
    "\<lbrakk>(f has_contour_integral y) h; f contour_integrable_on g; contour_integral g f = contour_integral h f\<rbrakk>
     \<Longrightarrow> (f has_contour_integral y) g"
sorry

lemma Cauchy_theorem_null_homotopic:
     "\<lbrakk>f holomorphic_on S; open S; valid_path g; homotopic_loops S g (linepath a a)\<rbrakk> 
      \<Longrightarrow> (f has_contour_integral 0) g"
sorry

end
