(*  Title:      HOL/Analysis/Path_Connected.thy
    Authors:    LC Paulson and Robert Himmelmann (TU Muenchen), based on material from HOL Light
*)

section \<open>Path-Connectedness\<close>

theory Path_Connected
imports
  Starlike
  T1_Spaces
begin

subsection \<open>Paths and Arcs\<close>

definition\<^marker>\<open>tag important\<close> path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "path g \<equiv> continuous_on {0..1} g"

definition\<^marker>\<open>tag important\<close> pathstart :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathstart g \<equiv> g 0"

definition\<^marker>\<open>tag important\<close> pathfinish :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a"
  where "pathfinish g \<equiv> g 1"

definition\<^marker>\<open>tag important\<close> path_image :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> 'a set"
  where "path_image g \<equiv> g ` {0 .. 1}"

definition\<^marker>\<open>tag important\<close> reversepath :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> real \<Rightarrow> 'a"
  where "reversepath g \<equiv> (\<lambda>x. g(1 - x))"

definition\<^marker>\<open>tag important\<close> joinpaths :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a"
    (infixr \<open>+++\<close> 75)
  where "g1 +++ g2 \<equiv> (\<lambda>x. if x \<le> 1/2 then g1 (2 * x) else g2 (2 * x - 1))"

definition\<^marker>\<open>tag important\<close> loop_free :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "loop_free g \<equiv> \<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. g x = g y \<longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"

definition\<^marker>\<open>tag important\<close> simple_path :: "(real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "simple_path g \<equiv> path g \<and> loop_free g"

definition\<^marker>\<open>tag important\<close> arc :: "(real \<Rightarrow> 'a :: topological_space) \<Rightarrow> bool"
  where "arc g \<equiv> path g \<and> inj_on g {0..1}"


subsection\<^marker>\<open>tag unimportant\<close>\<open>Invariance theorems\<close>

lemma path_eq: "path p \<Longrightarrow> (\<And>t. t \<in> {0..1} \<Longrightarrow> p t = q t) \<Longrightarrow> path q"
sorry

lemma path_continuous_image: "path g \<Longrightarrow> continuous_on (path_image g) f \<Longrightarrow> path(f \<circ> g)"
sorry

lemma path_translation_eq:
  fixes g :: "real \<Rightarrow> 'a :: real_normed_vector"
  shows "path((\<lambda>x. a + x) \<circ> g) = path g"
sorry

lemma path_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
   assumes "linear f" "inj f"
     shows "path(f \<circ> g) = path g"
sorry

lemma pathstart_translation: "pathstart((\<lambda>x. a + x) \<circ> g) = a + pathstart g"
sorry

lemma pathstart_linear_image_eq: "linear f \<Longrightarrow> pathstart(f \<circ> g) = f(pathstart g)"
sorry

lemma pathfinish_translation: "pathfinish((\<lambda>x. a + x) \<circ> g) = a + pathfinish g"
sorry

lemma pathfinish_linear_image: "linear f \<Longrightarrow> pathfinish(f \<circ> g) = f(pathfinish g)"
sorry

lemma path_image_translation: "path_image((\<lambda>x. a + x) \<circ> g) = (\<lambda>x. a + x) ` (path_image g)"
sorry

lemma path_image_linear_image: "linear f \<Longrightarrow> path_image(f \<circ> g) = f ` (path_image g)"
sorry

lemma reversepath_translation: "reversepath((\<lambda>x. a + x) \<circ> g) = (\<lambda>x. a + x) \<circ> reversepath g"
sorry

lemma reversepath_linear_image: "linear f \<Longrightarrow> reversepath(f \<circ> g) = f \<circ> reversepath g"
sorry

lemma joinpaths_translation:
    "((\<lambda>x. a + x) \<circ> g1) +++ ((\<lambda>x. a + x) \<circ> g2) = (\<lambda>x. a + x) \<circ> (g1 +++ g2)"
sorry

lemma joinpaths_linear_image: "linear f \<Longrightarrow> (f \<circ> g1) +++ (f \<circ> g2) = f \<circ> (g1 +++ g2)"
sorry

lemma loop_free_translation_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  shows "loop_free((\<lambda>x. a + x) \<circ> g) = loop_free g"
sorry

lemma simple_path_translation_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  shows "simple_path((\<lambda>x. a + x) \<circ> g) = simple_path g"
sorry

lemma loop_free_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "loop_free(f \<circ> g) = loop_free g"
sorry

lemma simple_path_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
    shows "simple_path(f \<circ> g) = simple_path g"
sorry

lemma simple_pathI [intro?]:
  assumes "path p"
  assumes "\<And>x y. 0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> p x = p y \<Longrightarrow> x = 0 \<and> y = 1"
  shows   "simple_path p"
sorry

lemma arcD: "arc p \<Longrightarrow> p x = p y \<Longrightarrow> x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> x = y"
sorry

lemma arc_translation_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  shows "arc((\<lambda>x. a + x) \<circ> g) \<longleftrightarrow> arc g"
sorry

lemma arc_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
   assumes "linear f" "inj f"
     shows  "arc(f \<circ> g) = arc g"
sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Basic lemmas about paths\<close>

lemma path_of_real: "path complex_of_real"
sorry

lemma path_const: "path (\<lambda>t. a)" for a::"'a::real_normed_vector"
sorry

lemma path_minus: "path g \<Longrightarrow> path (\<lambda>t. - g t)" for g::"real\<Rightarrow>'a::real_normed_vector"
sorry

lemma path_add: "\<lbrakk>path f; path g\<rbrakk> \<Longrightarrow> path (\<lambda>t. f t + g t)" for f::"real\<Rightarrow>'a::real_normed_vector"
sorry

lemma path_diff: "\<lbrakk>path f; path g\<rbrakk> \<Longrightarrow> path (\<lambda>t. f t - g t)" for f::"real\<Rightarrow>'a::real_normed_vector"
sorry

lemma path_mult: "\<lbrakk>path f; path g\<rbrakk> \<Longrightarrow> path (\<lambda>t. f t * g t)" for f::"real\<Rightarrow>'a::real_normed_field"
sorry

lemma pathin_iff_path_real [simp]: "pathin euclideanreal g \<longleftrightarrow> path g"
sorry

lemma continuous_on_path: "path f \<Longrightarrow> t \<subseteq> {0..1} \<Longrightarrow> continuous_on t f"
sorry

lemma inj_on_imp_loop_free: "inj_on g {0..1} \<Longrightarrow> loop_free g"
sorry

lemma arc_imp_simple_path: "arc g \<Longrightarrow> simple_path g"
sorry

lemma arc_imp_path: "arc g \<Longrightarrow> path g"
sorry

lemma arc_imp_inj_on: "arc g \<Longrightarrow> inj_on g {0..1}"
sorry

lemma simple_path_imp_path: "simple_path g \<Longrightarrow> path g"
sorry

lemma loop_free_cases: "loop_free g \<Longrightarrow> inj_on g {0..1} \<or> pathfinish g = pathstart g"
sorry

lemma simple_path_cases: "simple_path g \<Longrightarrow> arc g \<or> pathfinish g = pathstart g"
sorry

lemma simple_path_imp_arc: "simple_path g \<Longrightarrow> pathfinish g \<noteq> pathstart g \<Longrightarrow> arc g"
sorry

lemma arc_distinct_ends: "arc g \<Longrightarrow> pathfinish g \<noteq> pathstart g"
sorry

lemma arc_simple_path: "arc g \<longleftrightarrow> simple_path g \<and> pathfinish g \<noteq> pathstart g"
sorry

lemma simple_path_eq_arc: "pathfinish g \<noteq> pathstart g \<Longrightarrow> (simple_path g = arc g)"
sorry

lemma path_image_const [simp]: "path_image (\<lambda>t. a) = {a}"
sorry

lemma path_image_nonempty [simp]: "path_image g \<noteq> {}"
sorry

lemma pathstart_in_path_image[intro]: "pathstart g \<in> path_image g"
sorry

lemma pathfinish_in_path_image[intro]: "pathfinish g \<in> path_image g"
sorry

lemma connected_path_image[intro]: "path g \<Longrightarrow> connected (path_image g)"
sorry

lemma compact_path_image[intro]: "path g \<Longrightarrow> compact (path_image g)"
sorry

lemma reversepath_reversepath[simp]: "reversepath (reversepath g) = g"
sorry

lemma pathstart_reversepath[simp]: "pathstart (reversepath g) = pathfinish g"
sorry

lemma pathfinish_reversepath[simp]: "pathfinish (reversepath g) = pathstart g"
sorry

lemma reversepath_o: "reversepath g = g \<circ> (-)1"
sorry

lemma pathstart_join[simp]: "pathstart (g1 +++ g2) = pathstart g1"
sorry

lemma pathfinish_join[simp]: "pathfinish (g1 +++ g2) = pathfinish g2"
sorry

lemma path_image_reversepath[simp]: "path_image (reversepath g) = path_image g"
sorry

lemma path_reversepath [simp]: "path (reversepath g) \<longleftrightarrow> path g"
sorry

lemma arc_reversepath:
  assumes "arc g" shows "arc(reversepath g)"
sorry

lemma loop_free_reversepath:
  assumes "loop_free g" shows "loop_free(reversepath g)"
sorry

lemma simple_path_reversepath: "simple_path g \<Longrightarrow> simple_path (reversepath g)"
sorry

lemmas reversepath_simps =
  path_reversepath path_image_reversepath pathstart_reversepath pathfinish_reversepath

lemma path_join[simp]:
  assumes "pathfinish g1 = pathstart g2"
  shows "path (g1 +++ g2) \<longleftrightarrow> path g1 \<and> path g2"
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Path Images\<close>

lemma bounded_path_image: "path g \<Longrightarrow> bounded(path_image g)"
sorry

lemma closed_path_image:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  shows "path g \<Longrightarrow> closed(path_image g)"
sorry

lemma connected_simple_path_image: "simple_path g \<Longrightarrow> connected(path_image g)"
sorry

lemma compact_simple_path_image: "simple_path g \<Longrightarrow> compact(path_image g)"
sorry

lemma bounded_simple_path_image: "simple_path g \<Longrightarrow> bounded(path_image g)"
sorry

lemma closed_simple_path_image:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  shows "simple_path g \<Longrightarrow> closed(path_image g)"
sorry

lemma connected_arc_image: "arc g \<Longrightarrow> connected(path_image g)"
sorry

lemma compact_arc_image: "arc g \<Longrightarrow> compact(path_image g)"
sorry

lemma bounded_arc_image: "arc g \<Longrightarrow> bounded(path_image g)"
sorry

lemma closed_arc_image:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  shows "arc g \<Longrightarrow> closed(path_image g)"
sorry

lemma path_image_join_subset: "path_image (g1 +++ g2) \<subseteq> path_image g1 \<union> path_image g2"
sorry

lemma subset_path_image_join:
  assumes "path_image g1 \<subseteq> S" and "path_image g2 \<subseteq> S"
  shows "path_image (g1 +++ g2) \<subseteq> S"
sorry

lemma path_image_join:
  assumes "pathfinish g1 = pathstart g2"
  shows "path_image(g1 +++ g2) = path_image g1 \<union> path_image g2"
sorry

lemma not_in_path_image_join:
  assumes "x \<notin> path_image g1" and "x \<notin> path_image g2"
  shows "x \<notin> path_image (g1 +++ g2)"
sorry

lemma pathstart_compose: "pathstart(f \<circ> p) = f(pathstart p)"
sorry

lemma pathfinish_compose: "pathfinish(f \<circ> p) = f(pathfinish p)"
sorry

lemma path_image_compose: "path_image (f \<circ> p) = f ` (path_image p)"
sorry

lemma path_compose_join: "f \<circ> (p +++ q) = (f \<circ> p) +++ (f \<circ> q)"
sorry

lemma path_compose_reversepath: "f \<circ> reversepath p = reversepath(f \<circ> p)"
sorry

lemma joinpaths_eq:
  "(\<And>t. t \<in> {0..1} \<Longrightarrow> p t = p' t) \<Longrightarrow>
   (\<And>t. t \<in> {0..1} \<Longrightarrow> q t = q' t)
   \<Longrightarrow>  t \<in> {0..1} \<Longrightarrow> (p +++ q) t = (p' +++ q') t"
sorry

lemma loop_free_inj_on: "loop_free g \<Longrightarrow> inj_on g {0<..<1}"
sorry

lemma simple_path_inj_on: "simple_path g \<Longrightarrow> inj_on g {0<..<1}"
sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Simple paths with the endpoints removed\<close>

lemma simple_path_endless:
  assumes "simple_path c"
  shows "path_image c - {pathstart c,pathfinish c} = c ` {0<..<1}" (is "?lhs = ?rhs")
sorry

lemma connected_simple_path_endless:
  assumes "simple_path c"
  shows "connected(path_image c - {pathstart c,pathfinish c})"
sorry

lemma nonempty_simple_path_endless:
    "simple_path c \<Longrightarrow> path_image c - {pathstart c,pathfinish c} \<noteq> {}"
sorry

lemma simple_path_continuous_image:
  assumes "simple_path f" "continuous_on (path_image f) g" "inj_on g (path_image f)"
  shows   "simple_path (g \<circ> f)"
sorry
subsection\<^marker>\<open>tag unimportant\<close>\<open>The operations on paths\<close>

lemma path_image_subset_reversepath: "path_image(reversepath g) \<le> path_image g"
sorry

lemma path_imp_reversepath: "path g \<Longrightarrow> path(reversepath g)"
sorry

lemma half_bounded_equal: "1 \<le> x * 2 \<Longrightarrow> x * 2 \<le> 1 \<longleftrightarrow> x = (1/2::real)"
sorry

lemma continuous_on_joinpaths:
  assumes "continuous_on {0..1} g1" "continuous_on {0..1} g2" "pathfinish g1 = pathstart g2"
    shows "continuous_on {0..1} (g1 +++ g2)"
sorry

lemma path_join_imp: "\<lbrakk>path g1; path g2; pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> path(g1 +++ g2)"
sorry

lemma arc_join:
  assumes "arc g1" "arc g2"
          "pathfinish g1 = pathstart g2"
          "path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g2}"
    shows "arc(g1 +++ g2)"
sorry

lemma simple_path_join_loop:
  assumes "arc g1" "arc g2"
          "pathfinish g1 = pathstart g2"  "pathfinish g2 = pathstart g1"
          "path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g1, pathstart g2}"
        shows "simple_path(g1 +++ g2)"
sorry

lemma reversepath_joinpaths:
    "pathfinish g1 = pathstart g2 \<Longrightarrow> reversepath(g1 +++ g2) = reversepath g2 +++ reversepath g1"
sorry
subsection\<^marker>\<open>tag unimportant\<close>\<open>Some reversed and "if and only if" versions of joining theorems\<close>

lemma path_join_path_ends:
  fixes g1 :: "real \<Rightarrow> 'a::metric_space"
  assumes "path(g1 +++ g2)" "path g2"
    shows "pathfinish g1 = pathstart g2"
sorry

lemma path_join_eq [simp]:
  fixes g1 :: "real \<Rightarrow> 'a::metric_space"
  assumes "path g1" "path g2"
    shows "path(g1 +++ g2) \<longleftrightarrow> pathfinish g1 = pathstart g2"
sorry

lemma simple_path_joinE:
  assumes "simple_path(g1 +++ g2)" and "pathfinish g1 = pathstart g2"
  obtains "arc g1" "arc g2"
          "path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g1, pathstart g2}"
sorry

lemma simple_path_join_loop_eq:
  assumes "pathfinish g2 = pathstart g1" "pathfinish g1 = pathstart g2"
  shows "simple_path(g1 +++ g2) \<longleftrightarrow>
             arc g1 \<and> arc g2 \<and> path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g1, pathstart g2}"
sorry

lemma arc_join_eq:
  assumes "pathfinish g1 = pathstart g2"
    shows "arc(g1 +++ g2) \<longleftrightarrow>
           arc g1 \<and> arc g2 \<and> path_image g1 \<inter> path_image g2 \<subseteq> {pathstart g2}"
           (is "?lhs = ?rhs")
sorry

lemma arc_join_eq_alt:
  "pathfinish g1 = pathstart g2
   \<Longrightarrow> arc(g1 +++ g2) \<longleftrightarrow> arc g1 \<and> arc g2 \<and> path_image g1 \<inter> path_image g2 = {pathstart g2}"
sorry

subsubsection\<^marker>\<open>tag unimportant\<close>\<open>Symmetry and loops\<close>

lemma path_sym:
  "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart p\<rbrakk> \<Longrightarrow> path(p +++ q) \<longleftrightarrow> path(q +++ p)"
sorry

lemma simple_path_sym:
  "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart p\<rbrakk>
     \<Longrightarrow> simple_path(p +++ q) \<longleftrightarrow> simple_path(q +++ p)"
sorry

lemma path_image_sym:
  "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart p\<rbrakk>
     \<Longrightarrow> path_image(p +++ q) = path_image(q +++ p)"
sorry

lemma simple_path_joinI:
  assumes "arc p1" "arc p2" "pathfinish p1 = pathstart p2"
  assumes "path_image p1 \<inter> path_image p2 
        \<subseteq> insert (pathstart p2) (if pathstart p1 = pathfinish p2 then {pathstart p1} else {})"
  shows   "simple_path (p1 +++ p2)"
sorry

lemma simple_path_join3I:
  assumes "arc p1" "arc p2" "arc p3"
  assumes "path_image p1 \<inter> path_image p2 \<subseteq> {pathstart p2}"
  assumes "path_image p2 \<inter> path_image p3 \<subseteq> {pathstart p3}"
  assumes "path_image p1 \<inter> path_image p3 \<subseteq> {pathstart p1} \<inter> {pathfinish p3}"
  assumes "pathfinish p1 = pathstart p2" "pathfinish p2 = pathstart p3"
  shows   "simple_path (p1 +++ p2 +++ p3)"
sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>The joining of paths is associative\<close>

lemma path_assoc:
  "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart r\<rbrakk>
     \<Longrightarrow> path(p +++ (q +++ r)) \<longleftrightarrow> path((p +++ q) +++ r)"
sorry

lemma simple_path_assoc:
  assumes "pathfinish p = pathstart q" "pathfinish q = pathstart r"
    shows "simple_path (p +++ (q +++ r)) \<longleftrightarrow> simple_path ((p +++ q) +++ r)"
sorry

lemma arc_assoc:
     "\<lbrakk>pathfinish p = pathstart q; pathfinish q = pathstart r\<rbrakk>
      \<Longrightarrow> arc(p +++ (q +++ r)) \<longleftrightarrow> arc((p +++ q) +++ r)"
sorry

subsection\<open>Subpath\<close>

definition\<^marker>\<open>tag important\<close> subpath :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> 'a::real_normed_vector"
  where "subpath a b g \<equiv> \<lambda>x. g((b - a) * x + a)"

lemma path_image_subpath_gen:
  fixes g :: "_ \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = g ` (closed_segment u v)"
sorry

lemma path_image_subpath:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = (if u \<le> v then g ` {u..v} else g ` {v..u})"
sorry

lemma path_image_subpath_commute:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  shows "path_image(subpath u v g) = path_image(subpath v u g)"
sorry

lemma path_subpath [simp]:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "path(subpath u v g)"
sorry

lemma pathstart_subpath [simp]: "pathstart(subpath u v g) = g(u)"
sorry

lemma pathfinish_subpath [simp]: "pathfinish(subpath u v g) = g(v)"
sorry

lemma subpath_trivial [simp]: "subpath 0 1 g = g"
sorry

lemma subpath_reversepath: "subpath 1 0 g = reversepath g"
sorry

lemma reversepath_subpath: "reversepath(subpath u v g) = subpath v u g"
sorry

lemma subpath_translation: "subpath u v ((\<lambda>x. a + x) \<circ> g) = (\<lambda>x. a + x) \<circ> subpath u v g"
sorry

lemma subpath_image: "subpath u v (f \<circ> g) = f \<circ> subpath u v g"
sorry

lemma affine_ineq:
  fixes x :: "'a::linordered_idom"
  assumes "x \<le> 1" "v \<le> u"
    shows "v + x * u \<le> u + x * v"
sorry

lemma sum_le_prod1:
  fixes a::real shows "\<lbrakk>a \<le> 1; b \<le> 1\<rbrakk> \<Longrightarrow> a + b \<le> 1 + a * b"
sorry

lemma simple_path_subpath_eq:
  "simple_path(subpath u v g) \<longleftrightarrow>
     path(subpath u v g) \<and> u\<noteq>v \<and>
     (\<forall>x y. x \<in> closed_segment u v \<and> y \<in> closed_segment u v \<and> g x = g y
                \<longrightarrow> x = y \<or> x = u \<and> y = v \<or> x = v \<and> y = u)"
    (is "?lhs = ?rhs")
sorry

lemma arc_subpath_eq:
  "arc(subpath u v g) \<longleftrightarrow> path(subpath u v g) \<and> u\<noteq>v \<and> inj_on g (closed_segment u v)"
sorry

lemma simple_path_subpath:
  assumes "simple_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<noteq> v"
  shows "simple_path(subpath u v g)"
sorry

lemma arc_simple_path_subpath:
    "\<lbrakk>simple_path g; u \<in> {0..1}; v \<in> {0..1}; g u \<noteq> g v\<rbrakk> \<Longrightarrow> arc(subpath u v g)"
sorry

lemma arc_subpath_arc:
    "\<lbrakk>arc g; u \<in> {0..1}; v \<in> {0..1}; u \<noteq> v\<rbrakk> \<Longrightarrow> arc(subpath u v g)"
sorry

lemma arc_simple_path_subpath_interior:
    "\<lbrakk>simple_path g; u \<in> {0..1}; v \<in> {0..1}; u \<noteq> v; \<bar>u-v\<bar> < 1\<rbrakk> \<Longrightarrow> arc(subpath u v g)"
sorry

lemma path_image_subpath_subset:
    "\<lbrakk>u \<in> {0..1}; v \<in> {0..1}\<rbrakk> \<Longrightarrow> path_image(subpath u v g) \<subseteq> path_image g"
sorry

lemma join_subpaths_middle: "subpath (0) ((1 / 2)) p +++ subpath ((1 / 2)) 1 p = p"
sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>There is a subpath to the frontier\<close>

lemma subpath_to_frontier_explicit:
    fixes S :: "'a::metric_space set"
    assumes g: "path g" and "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1"
                "\<And>x. 0 \<le> x \<and> x < u \<Longrightarrow> g x \<in> interior S"
                "(g u \<notin> interior S)" "(u = 0 \<or> g u \<in> closure S)"
sorry

lemma subpath_to_frontier_strong:
    assumes g: "path g" and "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1" "g u \<notin> interior S"
                    "u = 0 \<or> (\<forall>x. 0 \<le> x \<and> x < 1 \<longrightarrow> subpath 0 u g x \<in> interior S)  \<and>  g u \<in> closure S"
sorry

lemma subpath_to_frontier:
    assumes g: "path g" and g0: "pathstart g \<in> closure S" and g1: "pathfinish g \<notin> S"
    obtains u where "0 \<le> u" "u \<le> 1" "g u \<in> frontier S" "path_image(subpath 0 u g) - {g u} \<subseteq> interior S"
sorry

lemma exists_path_subpath_to_frontier:
    fixes S :: "'a::real_normed_vector set"
    assumes "path g" "pathstart g \<in> closure S" "pathfinish g \<notin> S"
    obtains h where "path h" "pathstart h = pathstart g" "path_image h \<subseteq> path_image g"
                    "path_image h - {pathfinish h} \<subseteq> interior S"
                    "pathfinish h \<in> frontier S"
sorry

lemma exists_path_subpath_to_frontier_closed:
    fixes S :: "'a::real_normed_vector set"
    assumes S: "closed S" and g: "path g" and g0: "pathstart g \<in> S" and g1: "pathfinish g \<notin> S"
    obtains h where "path h" "pathstart h = pathstart g" "path_image h \<subseteq> path_image g \<inter> S"
                    "pathfinish h \<in> frontier S"
sorry

subsection \<open>Shift Path to Start at Some Given Point\<close>

definition\<^marker>\<open>tag important\<close> shiftpath :: "real \<Rightarrow> (real \<Rightarrow> 'a::topological_space) \<Rightarrow> real \<Rightarrow> 'a"
  where "shiftpath a f = (\<lambda>x. if (a + x) \<le> 1 then f (a + x) else f (a + x - 1))"

lemma shiftpath_alt_def: "shiftpath a f = (\<lambda>x. if x \<le> 1-a then f (a + x) else f (a + x - 1))"
sorry

lemma pathstart_shiftpath: "a \<le> 1 \<Longrightarrow> pathstart (shiftpath a g) = g a"
sorry

lemma pathfinish_shiftpath:
  assumes "0 \<le> a"
    and "pathfinish g = pathstart g"
  shows "pathfinish (shiftpath a g) = g a"
sorry

lemma endpoints_shiftpath:
  assumes "pathfinish g = pathstart g"
    and "a \<in> {0 .. 1}"
  shows "pathfinish (shiftpath a g) = g a"
    and "pathstart (shiftpath a g) = g a"
sorry

lemma closed_shiftpath:
  assumes "pathfinish g = pathstart g"
    and "a \<in> {0..1}"
  shows "pathfinish (shiftpath a g) = pathstart (shiftpath a g)"
sorry

lemma path_shiftpath:
  assumes "path g"
    and "pathfinish g = pathstart g"
    and "a \<in> {0..1}"
  shows "path (shiftpath a g)"
sorry

lemma shiftpath_shiftpath:
  assumes "pathfinish g = pathstart g"
    and "a \<in> {0..1}"
    and "x \<in> {0..1}"
  shows "shiftpath (1 - a) (shiftpath a g) x = g x"
sorry

lemma path_image_shiftpath:
  assumes a: "a \<in> {0..1}"
    and "pathfinish g = pathstart g"
  shows "path_image (shiftpath a g) = path_image g"
sorry

lemma loop_free_shiftpath:
  assumes "loop_free g" "pathfinish g = pathstart g" and a: "0 \<le> a" "a \<le> 1"
    shows "loop_free (shiftpath a g)"
sorry

lemma simple_path_shiftpath:
  assumes "simple_path g" "pathfinish g = pathstart g" and a: "0 \<le> a" "a \<le> 1"
  shows "simple_path (shiftpath a g)"
sorry

subsection \<open>Straight-Line Paths\<close>

definition\<^marker>\<open>tag important\<close> linepath :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  where "linepath a b = (\<lambda>x. (1 - x) *\<^sub>R a + x *\<^sub>R b)"

lemma pathstart_linepath[simp]: "pathstart (linepath a b) = a"
sorry

lemma pathfinish_linepath[simp]: "pathfinish (linepath a b) = b"
sorry

lemma linepath_inner: "linepath a b x \<bullet> v = linepath (a \<bullet> v) (b \<bullet> v) x"
sorry

lemma Re_linepath': "Re (linepath a b x) = linepath (Re a) (Re b) x"
sorry

lemma Im_linepath': "Im (linepath a b x) = linepath (Im a) (Im b) x"
sorry

lemma linepath_0': "linepath a b 0 = a"
sorry

lemma linepath_1': "linepath a b 1 = b"
sorry

lemma continuous_linepath_at[intro]: "continuous (at x) (linepath a b)"
sorry

lemma continuous_on_linepath [intro,continuous_intros]: "continuous_on s (linepath a b)"
sorry

lemma path_linepath[iff]: "path (linepath a b)"
sorry

lemma path_image_linepath[simp]: "path_image (linepath a b) = closed_segment a b"
sorry

lemma reversepath_linepath[simp]: "reversepath (linepath a b) = linepath b a"
sorry

lemma linepath_0 [simp]: "linepath 0 b x = x *\<^sub>R b"
sorry

lemma linepath_cnj: "cnj (linepath a b x) = linepath (cnj a) (cnj b) x"
sorry

lemma arc_linepath:
  assumes "a \<noteq> b" shows [simp]: "arc (linepath a b)"
sorry

lemma simple_path_linepath[intro]: "a \<noteq> b \<Longrightarrow> simple_path (linepath a b)"
sorry

lemma linepath_trivial [simp]: "linepath a a x = a"
sorry

lemma linepath_refl: "linepath a a = (\<lambda>x. a)"
sorry

lemma subpath_refl: "subpath a a g = linepath (g a) (g a)"
sorry

lemma linepath_of_real: "(linepath (of_real a) (of_real b) x) = of_real ((1 - x)*a + x*b)"
sorry

lemma of_real_linepath: "of_real (linepath a b x) = linepath (of_real a) (of_real b) x"
sorry

lemma inj_on_linepath:
  assumes "a \<noteq> b" shows "inj_on (linepath a b) {0..1}"
sorry

lemma linepath_le_1:
  fixes a::"'a::linordered_idom" shows "\<lbrakk>a \<le> 1; b \<le> 1; 0 \<le> u; u \<le> 1\<rbrakk> \<Longrightarrow> (1 - u) * a + u * b \<le> 1"
sorry

lemma linepath_in_path:
  shows "x \<in> {0..1} \<Longrightarrow> linepath a b x \<in> closed_segment a b"
sorry

lemma linepath_image_01: "linepath a b ` {0..1} = closed_segment a b"
sorry

lemma linepath_in_convex_hull:
  fixes x::real
  assumes "a \<in> convex hull S"
    and "b \<in> convex hull S"
    and "0\<le>x" "x\<le>1"
  shows "linepath a b x \<in> convex hull S"
sorry

lemma Re_linepath: "Re(linepath (of_real a) (of_real b) x) = (1 - x)*a + x*b"
sorry

lemma Im_linepath: "Im(linepath (of_real a) (of_real b) x) = 0"
sorry

lemma bounded_linear_linepath:
  assumes "bounded_linear f"
  shows   "f (linepath a b x) = linepath (f a) (f b) x"
sorry

lemma bounded_linear_linepath':
  assumes "bounded_linear f"
  shows   "f \<circ> linepath a b = linepath (f a) (f b)"
sorry

lemma linepath_cnj': "cnj \<circ> linepath a b = linepath (cnj a) (cnj b)"
sorry

lemma differentiable_linepath [intro]: "linepath a b differentiable at x within A"
sorry

lemma has_vector_derivative_linepath_within:
    "(linepath a b has_vector_derivative (b - a)) (at x within S)"
sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Segments via convex hulls\<close>

lemma segments_subset_convex_hull:
    "closed_segment a b \<subseteq> (convex hull {a,b,c})"
    "closed_segment a c \<subseteq> (convex hull {a,b,c})"
    "closed_segment b c \<subseteq> (convex hull {a,b,c})"
    "closed_segment b a \<subseteq> (convex hull {a,b,c})"
    "closed_segment c a \<subseteq> (convex hull {a,b,c})"
    "closed_segment c b \<subseteq> (convex hull {a,b,c})"
sorry

lemma midpoints_in_convex_hull:
  assumes "x \<in> convex hull s" "y \<in> convex hull s"
    shows "midpoint x y \<in> convex hull s"
sorry

lemma not_in_interior_convex_hull_3:
  fixes a :: "complex"
  shows "a \<notin> interior(convex hull {a,b,c})"
        "b \<notin> interior(convex hull {a,b,c})"
        "c \<notin> interior(convex hull {a,b,c})"
sorry

lemma midpoint_in_closed_segment [simp]: "midpoint a b \<in> closed_segment a b"
sorry

lemma midpoint_in_open_segment [simp]: "midpoint a b \<in> open_segment a b \<longleftrightarrow> a \<noteq> b"
sorry

lemma continuous_IVT_local_extremum:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes contf: "continuous_on (closed_segment a b) f"
      and ab: "a \<noteq> b" "f a = f b"
  obtains z where "z \<in> open_segment a b"
                  "(\<forall>w \<in> closed_segment a b. (f w) \<le> (f z)) \<or>
                   (\<forall>w \<in> closed_segment a b. (f z) \<le> (f w))"
sorry

text\<open>An injective map into R is also an open map w.r.T. the universe, and conversely. \<close>
proposition injective_eq_1d_open_map_UNIV:
  fixes f :: "real \<Rightarrow> real"
  assumes contf: "continuous_on S f" and S: "is_interval S"
    shows "inj_on f S \<longleftrightarrow> (\<forall>T. open T \<and> T \<subseteq> S \<longrightarrow> open(f ` T))"
          (is "?lhs = ?rhs")
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounding a point away from a path\<close>

lemma not_on_path_ball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g"
    and z: "z \<notin> path_image g"
  shows "\<exists>e > 0. ball z e \<inter> path_image g = {}"
sorry

lemma not_on_path_cball:
  fixes g :: "real \<Rightarrow> 'a::heine_borel"
  assumes "path g"
    and "z \<notin> path_image g"
  shows "\<exists>e>0. cball z e \<inter> (path_image g) = {}"
sorry
subsection \<open>Path component\<close>

text \<open>Original formalization by Tom Hales\<close>

definition\<^marker>\<open>tag important\<close> "path_component S x y \<equiv>
  (\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y)"

abbreviation\<^marker>\<open>tag important\<close>
  "path_component_set S x \<equiv> Collect (path_component S x)"

lemmas path_defs = path_def pathstart_def pathfinish_def path_image_def path_component_def

lemma path_component_mem:
  assumes "path_component S x y"
  shows "x \<in> S" and "y \<in> S"
sorry

lemma path_component_refl:
  assumes "x \<in> S"
  shows "path_component S x x"
sorry

lemma path_component_refl_eq: "path_component S x x \<longleftrightarrow> x \<in> S"
sorry

lemma path_component_sym: "path_component S x y \<Longrightarrow> path_component S y x"
sorry

lemma path_component_trans:
  assumes "path_component S x y" and "path_component S y z"
  shows "path_component S x z"
sorry

lemma path_component_of_subset: "S \<subseteq> T \<Longrightarrow> path_component S x y \<Longrightarrow> path_component T x y"
sorry

lemma path_component_linepath:
    fixes S :: "'a::real_normed_vector set"
    shows "closed_segment a b \<subseteq> S \<Longrightarrow> path_component S a b"
sorry

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Path components as sets\<close>

lemma path_component_set:
  "path_component_set S x =
    {y. (\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y)}"
sorry

lemma path_component_subset: "path_component_set S x \<subseteq> S"
sorry

lemma path_component_eq_empty: "path_component_set S x = {} \<longleftrightarrow> x \<notin> S"
sorry

lemma path_component_mono:
     "S \<subseteq> T \<Longrightarrow> (path_component_set S x) \<subseteq> (path_component_set T x)"
sorry

lemma path_component_eq:
   "y \<in> path_component_set S x \<Longrightarrow> path_component_set S y = path_component_set S x"
sorry

subsection \<open>Path connectedness of a space\<close>

definition\<^marker>\<open>tag important\<close> "path_connected S \<longleftrightarrow>
  (\<forall>x\<in>S. \<forall>y\<in>S. \<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y)"

lemma path_connectedin_iff_path_connected_real [simp]:
     "path_connectedin euclideanreal S \<longleftrightarrow> path_connected S"
sorry

lemma path_connected_component: "path_connected S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. path_component S x y)"
sorry

lemma path_connected_component_set: "path_connected S \<longleftrightarrow> (\<forall>x\<in>S. path_component_set S x = S)"
sorry

lemma path_component_maximal:
     "\<lbrakk>x \<in> T; path_connected T; T \<subseteq> S\<rbrakk> \<Longrightarrow> T \<subseteq> (path_component_set S x)"
sorry

lemma convex_imp_path_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "convex S"
  shows "path_connected S"
sorry

lemma path_connected_UNIV [iff]: "path_connected (UNIV :: 'a::real_normed_vector set)"
sorry

lemma path_component_UNIV: "path_component_set UNIV x = (UNIV :: 'a::real_normed_vector set)"
sorry

lemma path_connected_imp_connected:
  assumes "path_connected S"
  shows "connected S"
sorry

lemma open_path_component:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (path_component_set S x)"
sorry

lemma open_non_path_component:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (S - path_component_set S x)"
sorry

lemma connected_open_path_connected:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
    and "connected S"
  shows "path_connected S"
sorry

lemma path_connected_continuous_image:
  assumes contf: "continuous_on S f"
    and "path_connected S"
  shows "path_connected (f ` S)"
sorry

lemma path_connected_translationI:
  fixes a :: "'a :: topological_group_add"
  assumes "path_connected S" shows "path_connected ((\<lambda>x. a + x) ` S)"
sorry

lemma path_connected_translation:
  fixes a :: "'a :: topological_group_add"
  shows "path_connected ((\<lambda>x. a + x) ` S) = path_connected S"
sorry

lemma path_connected_segment [simp]:
    fixes a :: "'a::real_normed_vector"
    shows "path_connected (closed_segment a b)"
sorry

lemma path_connected_open_segment [simp]:
    fixes a :: "'a::real_normed_vector"
    shows "path_connected (open_segment a b)"
sorry

lemma homeomorphic_path_connectedness:
  "S homeomorphic T \<Longrightarrow> path_connected S \<longleftrightarrow> path_connected T"
sorry

lemma path_connected_empty [simp]: "path_connected {}"
sorry

lemma path_connected_singleton [simp]: "path_connected {a}"
sorry

lemma path_connected_Un:
  assumes "path_connected S"
    and "path_connected T"
    and "S \<inter> T \<noteq> {}"
  shows "path_connected (S \<union> T)"
sorry

lemma path_connected_UNION:
  assumes "\<And>i. i \<in> A \<Longrightarrow> path_connected (S i)"
    and "\<And>i. i \<in> A \<Longrightarrow> z \<in> S i"
  shows "path_connected (\<Union>i\<in>A. S i)"
sorry

lemma path_component_path_image_pathstart:
  assumes p: "path p" and x: "x \<in> path_image p"
  shows "path_component (path_image p) (pathstart p) x"
sorry

lemma path_connected_path_image: "path p \<Longrightarrow> path_connected(path_image p)"
sorry

lemma path_connected_path_component [simp]:
  "path_connected (path_component_set S x)"
sorry

lemma path_component: 
  "path_component S x y \<longleftrightarrow> (\<exists>t. path_connected t \<and> t \<subseteq> S \<and> x \<in> t \<and> y \<in> t)"
    (is "?lhs = ?rhs")
sorry

lemma path_component_path_component [simp]:
   "path_component_set (path_component_set S x) x = path_component_set S x"
sorry

lemma path_component_subset_connected_component:
   "(path_component_set S x) \<subseteq> (connected_component_set S x)"
sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Lemmas about path-connectedness\<close>

lemma path_connected_linear_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "path_connected S" "bounded_linear f"
  shows "path_connected(f ` S)"
sorry

lemma is_interval_path_connected: "is_interval S \<Longrightarrow> path_connected S"
sorry

lemma path_connected_Ioi[simp]: "path_connected {a<..}" for a :: real
sorry

lemma path_connected_Ici[simp]: "path_connected {a..}" for a :: real
sorry

lemma path_connected_Iio[simp]: "path_connected {..<a}" for a :: real
sorry

lemma path_connected_Iic[simp]: "path_connected {..a}" for a :: real
sorry

lemma path_connected_Ioo[simp]: "path_connected {a<..<b}" for a b :: real
sorry

lemma path_connected_Ioc[simp]: "path_connected {a<..b}" for a b :: real
sorry

lemma path_connected_Ico[simp]: "path_connected {a..<b}" for a b :: real
sorry

lemma path_connectedin_path_image:
  assumes "pathin X g" shows "path_connectedin X (g ` ({0..1}))"
sorry

lemma path_connected_space_subconnected:
     "path_connected_space X \<longleftrightarrow>
      (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. \<exists>S. path_connectedin X S \<and> x \<in> S \<and> y \<in> S)"
sorry

lemma connectedin_path_image: "pathin X g \<Longrightarrow> connectedin X (g ` ({0..1}))"
sorry

lemma compactin_path_image: "pathin X g \<Longrightarrow> compactin X (g ` ({0..1}))"
sorry

lemma linear_homeomorphism_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  obtains g where "homeomorphism (f ` S) S g f"
sorry

lemma linear_homeomorphic_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  shows "S homeomorphic f ` S"
sorry

lemma path_connected_Times:
  assumes "path_connected s" "path_connected t"
    shows "path_connected (s \<times> t)"
sorry

lemma is_interval_path_connected_1:
  fixes s :: "real set"
  shows "is_interval s \<longleftrightarrow> path_connected s"
sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Path components\<close>

lemma Union_path_component [simp]:
   "Union {path_component_set S x |x. x \<in> S} = S"
sorry

lemma path_component_disjoint:
   "disjnt (path_component_set S a) (path_component_set S b) \<longleftrightarrow>
    (a \<notin> path_component_set S b)"
sorry

lemma path_component_eq_eq:
   "path_component S x = path_component S y \<longleftrightarrow>
        (x \<notin> S) \<and> (y \<notin> S) \<or> x \<in> S \<and> y \<in> S \<and> path_component S x y"
    (is "?lhs = ?rhs")
sorry

lemma path_component_unique:
  assumes "x \<in> C" "C \<subseteq> S" "path_connected C"
          "\<And>C'. \<lbrakk>x \<in> C'; C' \<subseteq> S; path_connected C'\<rbrakk> \<Longrightarrow> C' \<subseteq> C"
        shows "path_component_set S x = C"
sorry

lemma path_component_intermediate_subset:
  "path_component_set U a \<subseteq> T \<and> T \<subseteq> U
        \<Longrightarrow> path_component_set T a = path_component_set U a"
sorry

lemma complement_path_component_Union:
  fixes x :: "'a :: topological_space"
  shows "S - path_component_set S x =
         \<Union>({path_component_set S y| y. y \<in> S} - {path_component_set S x})"
sorry


subsection\<open>Path components\<close>

definition path_component_of
  where "path_component_of X x y \<equiv> \<exists>g. pathin X g \<and> g 0 = x \<and> g 1 = y"

abbreviation path_component_of_set
  where "path_component_of_set X x \<equiv> Collect (path_component_of X x)"

definition path_components_of :: "'a topology \<Rightarrow> 'a set set"
  where "path_components_of X \<equiv> path_component_of_set X ` topspace X"

lemma pathin_canon_iff: "pathin (top_of_set T) g \<longleftrightarrow> path g \<and> g \<in> {0..1} \<rightarrow> T"
sorry

lemma path_component_of_canon_iff [simp]:
  "path_component_of (top_of_set T) a b \<longleftrightarrow> path_component T a b"
sorry

lemma path_component_in_topspace:
   "path_component_of X x y \<Longrightarrow> x \<in> topspace X \<and> y \<in> topspace X"
sorry

lemma path_component_of_refl:
   "path_component_of X x x \<longleftrightarrow> x \<in> topspace X"
sorry

lemma path_component_of_sym:
  assumes "path_component_of X x y"
  shows "path_component_of X y x"
sorry

lemma path_component_of_sym_iff:
   "path_component_of X x y \<longleftrightarrow> path_component_of X y x"
sorry

lemma continuous_map_cases_le:
  assumes contp: "continuous_map X euclideanreal p"
    and contq: "continuous_map X euclideanreal q"
    and contf: "continuous_map (subtopology X {x. x \<in> topspace X \<and> p x \<le> q x}) Y f"
    and contg: "continuous_map (subtopology X {x. x \<in> topspace X \<and> q x \<le> p x}) Y g"
    and fg: "\<And>x. \<lbrakk>x \<in> topspace X; p x = q x\<rbrakk> \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if p x \<le> q x then f x else g x)"
sorry

lemma continuous_map_cases_lt:
  assumes contp: "continuous_map X euclideanreal p"
    and contq: "continuous_map X euclideanreal q"
    and contf: "continuous_map (subtopology X {x. x \<in> topspace X \<and> p x \<le> q x}) Y f"
    and contg: "continuous_map (subtopology X {x. x \<in> topspace X \<and> q x \<le> p x}) Y g"
    and fg: "\<And>x. \<lbrakk>x \<in> topspace X; p x = q x\<rbrakk> \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if p x < q x then f x else g x)"
sorry

lemma path_component_of_trans:
  assumes "path_component_of X x y" and "path_component_of X y z"
  shows "path_component_of X x z"
sorry

lemma path_component_of_mono:
   "\<lbrakk>path_component_of (subtopology X S) x y; S \<subseteq> T\<rbrakk> \<Longrightarrow> path_component_of (subtopology X T) x y"
sorry

lemma path_component_of:
  "path_component_of X x y \<longleftrightarrow> (\<exists>T. path_connectedin X T \<and> x \<in> T \<and> y \<in> T)"
    (is "?lhs = ?rhs")
sorry

lemma path_component_of_set:
   "path_component_of X x y \<longleftrightarrow> (\<exists>g. pathin X g \<and> g 0 = x \<and> g 1 = y)"
sorry

lemma path_component_of_subset_topspace:
   "Collect(path_component_of X x) \<subseteq> topspace X"
sorry

lemma path_component_of_eq_empty:
   "Collect(path_component_of X x) = {} \<longleftrightarrow> (x \<notin> topspace X)"
sorry

lemma path_connected_space_iff_path_component:
   "path_connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. path_component_of X x y)"
sorry

lemma path_connected_space_imp_path_component_of:
   "\<lbrakk>path_connected_space X; a \<in> topspace X; b \<in> topspace X\<rbrakk>
        \<Longrightarrow> path_component_of X a b"
sorry

lemma path_connected_space_path_component_set:
   "path_connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. Collect(path_component_of X x) = topspace X)"
sorry

lemma path_component_of_maximal:
   "\<lbrakk>path_connectedin X s; x \<in> s\<rbrakk> \<Longrightarrow> s \<subseteq> Collect(path_component_of X x)"
sorry

lemma path_component_of_equiv:
   "path_component_of X x y \<longleftrightarrow> x \<in> topspace X \<and> y \<in> topspace X \<and> path_component_of X x = path_component_of X y"
    (is "?lhs = ?rhs")
sorry

lemma path_component_of_disjoint:
     "disjnt (Collect (path_component_of X x)) (Collect (path_component_of X y)) \<longleftrightarrow>
      ~(path_component_of X x y)"
sorry

lemma path_component_of_eq:
   "path_component_of X x = path_component_of X y \<longleftrightarrow>
        (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
        x \<in> topspace X \<and> y \<in> topspace X \<and> path_component_of X x y"
sorry

lemma path_component_of_aux:
  "path_component_of X x y
        \<Longrightarrow> path_component_of (subtopology X (Collect (path_component_of X x))) x y"
sorry

lemma path_connectedin_path_component_of:
  "path_connectedin X (Collect (path_component_of X x))"
sorry

lemma path_connectedin_euclidean [simp]:
   "path_connectedin euclidean S \<longleftrightarrow> path_connected S"
sorry

lemma path_connected_space_euclidean_subtopology [simp]:
   "path_connected_space(subtopology euclidean S) \<longleftrightarrow> path_connected S"
sorry

lemma Union_path_components_of:
     "\<Union>(path_components_of X) = topspace X"
sorry

lemma path_components_of_maximal:
   "\<lbrakk>C \<in> path_components_of X; path_connectedin X S; ~disjnt C S\<rbrakk> \<Longrightarrow> S \<subseteq> C"
sorry

lemma pairwise_disjoint_path_components_of:
     "pairwise disjnt (path_components_of X)"
sorry

lemma complement_path_components_of_Union:
   "C \<in> path_components_of X \<Longrightarrow> topspace X - C = \<Union>(path_components_of X - {C})"
sorry

lemma nonempty_path_components_of:
  assumes "C \<in> path_components_of X" shows "C \<noteq> {}"
sorry

lemma path_components_of_subset: "C \<in> path_components_of X \<Longrightarrow> C \<subseteq> topspace X"
sorry

lemma path_connectedin_path_components_of:
   "C \<in> path_components_of X \<Longrightarrow> path_connectedin X C"
sorry

lemma path_component_in_path_components_of:
  "Collect (path_component_of X a) \<in> path_components_of X \<longleftrightarrow> a \<in> topspace X"
sorry

lemma path_connectedin_Union:
  assumes \<A>: "\<And>S. S \<in> \<A> \<Longrightarrow> path_connectedin X S" and "\<Inter>\<A> \<noteq> {}"
  shows "path_connectedin X (\<Union>\<A>)"
sorry

lemma path_connectedin_Un:
   "\<lbrakk>path_connectedin X S; path_connectedin X T; S \<inter> T \<noteq> {}\<rbrakk>
    \<Longrightarrow> path_connectedin X (S \<union> T)"
sorry

lemma path_connected_space_iff_components_eq:
  "path_connected_space X \<longleftrightarrow>
    (\<forall>C \<in> path_components_of X. \<forall>C' \<in> path_components_of X. C = C')"
sorry

lemma path_components_of_eq_empty:
   "path_components_of X = {} \<longleftrightarrow> X = trivial_topology"
sorry

lemma path_components_of_empty_space:
   "path_components_of trivial_topology = {}"
sorry

lemma path_components_of_subset_singleton:
  "path_components_of X \<subseteq> {S} \<longleftrightarrow>
        path_connected_space X \<and> (topspace X = {} \<or> topspace X = S)"
sorry

lemma path_connected_space_iff_components_subset_singleton:
   "path_connected_space X \<longleftrightarrow> (\<exists>a. path_components_of X \<subseteq> {a})"
sorry

lemma path_components_of_eq_singleton:
   "path_components_of X = {S} \<longleftrightarrow> path_connected_space X \<and> topspace X \<noteq> {} \<and> S = topspace X"
sorry

lemma path_components_of_path_connected_space:
   "path_connected_space X \<Longrightarrow> path_components_of X = (if topspace X = {} then {} else {topspace X})"
sorry

lemma path_component_subset_connected_component_of:
   "path_component_of_set X x \<subseteq> connected_component_of_set X x"
sorry

lemma exists_path_component_of_superset:
  assumes S: "path_connectedin X S" and ne: "topspace X \<noteq> {}"
  obtains C where "C \<in> path_components_of X" "S \<subseteq> C"
sorry

lemma path_component_of_eq_overlap:
   "path_component_of X x = path_component_of X y \<longleftrightarrow>
      (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
      Collect (path_component_of X x) \<inter> Collect (path_component_of X y) \<noteq> {}"
sorry

lemma path_component_of_nonoverlap:
   "Collect (path_component_of X x) \<inter> Collect (path_component_of X y) = {} \<longleftrightarrow>
    (x \<notin> topspace X) \<or> (y \<notin> topspace X) \<or>
    path_component_of X x \<noteq> path_component_of X y"
sorry

lemma path_component_of_overlap:
   "Collect (path_component_of X x) \<inter> Collect (path_component_of X y) \<noteq> {} \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> path_component_of X x = path_component_of X y"
sorry

lemma path_components_of_disjoint:
     "\<lbrakk>C \<in> path_components_of X; C' \<in> path_components_of X\<rbrakk> \<Longrightarrow> disjnt C C' \<longleftrightarrow> C \<noteq> C'"
sorry

lemma path_components_of_overlap:
    "\<lbrakk>C \<in> path_components_of X; C' \<in> path_components_of X\<rbrakk> \<Longrightarrow> C \<inter> C' \<noteq> {} \<longleftrightarrow> C = C'"
sorry

lemma path_component_of_unique:
   "\<lbrakk>x \<in> C; path_connectedin X C; \<And>C'. \<lbrakk>x \<in> C'; path_connectedin X C'\<rbrakk> \<Longrightarrow> C' \<subseteq> C\<rbrakk>
        \<Longrightarrow> Collect (path_component_of X x) = C"
sorry

lemma path_component_of_discrete_topology [simp]:
  "Collect (path_component_of (discrete_topology U) x) = (if x \<in> U then {x} else {})"
sorry

lemma path_component_of_discrete_topology_iff [simp]:
  "path_component_of (discrete_topology U) x y \<longleftrightarrow> x \<in> U \<and> y=x"
sorry

lemma path_components_of_discrete_topology [simp]:
   "path_components_of (discrete_topology U) = (\<lambda>x. {x}) ` U"
sorry

lemma homeomorphic_map_path_component_of:
  assumes f: "homeomorphic_map X Y f" and x: "x \<in> topspace X"
  shows "Collect (path_component_of Y (f x)) = f ` Collect(path_component_of X x)"
sorry

lemma homeomorphic_map_path_components_of:
  assumes "homeomorphic_map X Y f"
  shows "path_components_of Y = (image f) ` (path_components_of X)"
sorry

subsection\<open>Paths and path-connectedness\<close>

lemma path_connected_space_quotient_map_image:
   "\<lbrakk>quotient_map X Y q; path_connected_space X\<rbrakk> \<Longrightarrow> path_connected_space Y"
sorry

lemma path_connected_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; path_connected_space X\<rbrakk> \<Longrightarrow> path_connected_space Y"
sorry

lemma path_connected_space_prod_topology:
  "path_connected_space(prod_topology X Y) \<longleftrightarrow>
        topspace(prod_topology X Y) = {} \<or> path_connected_space X \<and> path_connected_space Y"
sorry

lemma path_connectedin_Times:
   "path_connectedin (prod_topology X Y) (S \<times> T) \<longleftrightarrow>
        S = {} \<or> T = {} \<or> path_connectedin X S \<and> path_connectedin Y T"
sorry

subsection\<open>Path components\<close>

lemma path_component_of_subtopology_eq:
  "path_component_of (subtopology X U) x = path_component_of X x \<longleftrightarrow> path_component_of_set X x \<subseteq> U"  
  (is "?lhs = ?rhs")
sorry

lemma path_components_of_subtopology:
  assumes "C \<in> path_components_of X" "C \<subseteq> U"
  shows "C \<in> path_components_of (subtopology X U)"
sorry

lemma path_imp_connected_component_of:
   "path_component_of X x y \<Longrightarrow> connected_component_of X x y"
sorry

lemma finite_path_components_of_finite:
   "finite(topspace X) \<Longrightarrow> finite(path_components_of X)"
sorry

lemma path_component_of_continuous_image:
  "\<lbrakk>continuous_map X X' f; path_component_of X x y\<rbrakk> \<Longrightarrow> path_component_of X' (f x) (f y)"
sorry

lemma path_component_of_pair [simp]:
   "path_component_of_set (prod_topology X Y) (x,y) =
    path_component_of_set X x \<times> path_component_of_set Y y"   (is "?lhs = ?rhs")
sorry

lemma path_components_of_prod_topology:
   "path_components_of (prod_topology X Y) =
    (\<lambda>(C,D). C \<times> D) ` (path_components_of X \<times> path_components_of Y)"
sorry

lemma path_components_of_prod_topology':
   "path_components_of (prod_topology X Y) =
    {C \<times> D |C D. C \<in> path_components_of X \<and> D \<in> path_components_of Y}"
sorry

lemma path_component_of_product_topology:
   "path_component_of_set (product_topology X I) f =
    (if f \<in> extensional I then PiE I (\<lambda>i. path_component_of_set (X i) (f i)) else {})"
    (is "?lhs = ?rhs")
sorry

lemma path_components_of_product_topology:
  "path_components_of (product_topology X I) =
    {PiE I B |B. \<forall>i \<in> I. B i \<in> path_components_of(X i)}"  (is "?lhs=?rhs")
sorry

subsection \<open>Sphere is path-connected\<close>

lemma path_connected_punctured_universe:
  assumes "2 \<le> DIM('a::euclidean_space)"
  shows "path_connected (- {a::'a})"
sorry

corollary connected_punctured_universe:
  "2 \<le> DIM('N::euclidean_space) \<Longrightarrow> connected(- {a::'N})"
sorry

proposition path_connected_sphere:
  fixes a :: "'a :: euclidean_space"
  assumes "2 \<le> DIM('a)"
  shows "path_connected(sphere a r)"
sorry

lemma connected_sphere:
    fixes a :: "'a :: euclidean_space"
    assumes "2 \<le> DIM('a)"
      shows "connected(sphere a r)"
sorry

corollary path_connected_complement_bounded_convex:
    fixes S :: "'a :: euclidean_space set"
    assumes "bounded S" "convex S" and 2: "2 \<le> DIM('a)"
    shows "path_connected (- S)"
sorry

lemma connected_complement_bounded_convex:
    fixes S :: "'a :: euclidean_space set"
    assumes "bounded S" "convex S" "2 \<le> DIM('a)"
      shows  "connected (- S)"
sorry

lemma connected_diff_ball:
    fixes S :: "'a :: euclidean_space set"
    assumes "connected S" "cball a r \<subseteq> S" "2 \<le> DIM('a)"
      shows "connected (S - ball a r)"
sorry

proposition connected_open_delete:
  assumes "open S" "connected S" and 2: "2 \<le> DIM('N::euclidean_space)"
    shows "connected(S - {a::'N})"
sorry

corollary path_connected_open_delete:
  assumes "open S" "connected S" and 2: "2 \<le> DIM('N::euclidean_space)"
  shows "path_connected(S - {a::'N})"
sorry

corollary path_connected_punctured_ball:
  "2 \<le> DIM('N::euclidean_space) \<Longrightarrow> path_connected(ball a r - {a::'N})"
sorry

corollary connected_punctured_ball:
  "2 \<le> DIM('N::euclidean_space) \<Longrightarrow> connected(ball a r - {a::'N})"
sorry

corollary connected_open_delete_finite:
  fixes S T::"'a::euclidean_space set"
  assumes S: "open S" "connected S" and 2: "2 \<le> DIM('a)" and "finite T"
  shows "connected(S - T)"
sorry

lemma sphere_1D_doubleton_zero:
  assumes 1: "DIM('a) = 1" and "r > 0"
  obtains x y::"'a::euclidean_space"
    where "sphere 0 r = {x,y} \<and> dist x y = 2*r"
sorry

lemma sphere_1D_doubleton:
  fixes a :: "'a :: euclidean_space"
  assumes "DIM('a) = 1" and "r > 0"
  obtains x y where "sphere a r = {x,y} \<and> dist x y = 2*r"
sorry

lemma psubset_sphere_Compl_connected:
  fixes S :: "'a::euclidean_space set"
  assumes S: "S \<subset> sphere a r" and "0 < r" and 2: "2 \<le> DIM('a)"
  shows "connected(- S)"
sorry


subsection\<open>Every annulus is a connected set\<close>

lemma path_connected_2DIM_I:
  fixes a :: "'N::euclidean_space"
  assumes 2: "2 \<le> DIM('N)" and pc: "path_connected {r. 0 \<le> r \<and> P r}"
  shows "path_connected {x. P(norm(x - a))}"
sorry

proposition path_connected_annulus:
  fixes a :: "'N::euclidean_space"
  assumes "2 \<le> DIM('N)"
  shows "path_connected {x. r1 < norm(x - a) \<and> norm(x - a) < r2}"
        "path_connected {x. r1 < norm(x - a) \<and> norm(x - a) \<le> r2}"
        "path_connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) < r2}"
        "path_connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) \<le> r2}"
sorry

proposition connected_annulus:
  fixes a :: "'N::euclidean_space"
  assumes "2 \<le> DIM('N::euclidean_space)"
  shows "connected {x. r1 < norm(x - a) \<and> norm(x - a) < r2}"
        "connected {x. r1 < norm(x - a) \<and> norm(x - a) \<le> r2}"
        "connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) < r2}"
        "connected {x. r1 \<le> norm(x - a) \<and> norm(x - a) \<le> r2}"
sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Relations between components and path components\<close>

lemma open_connected_component:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open (connected_component_set S x)"
sorry

corollary open_components:
    fixes S :: "'a::real_normed_vector set"
    shows "\<lbrakk>open u; S \<in> components u\<rbrakk> \<Longrightarrow> open S"
sorry

lemma in_closure_connected_component:
  fixes S :: "'a::real_normed_vector set"
  assumes x: "x \<in> S" and S: "open S"
  shows "x \<in> closure (connected_component_set S y) \<longleftrightarrow>  x \<in> connected_component_set S y"
sorry

lemma connected_disjoint_Union_open_pick:
  assumes "pairwise disjnt B"
          "\<And>S. S \<in> A \<Longrightarrow> connected S \<and> S \<noteq> {}"
          "\<And>S. S \<in> B \<Longrightarrow> open S"
          "\<Union>A \<subseteq> \<Union>B"
          "S \<in> A"
  obtains T where "T \<in> B" "S \<subseteq> T" "S \<inter> \<Union>(B - {T}) = {}"
sorry

lemma connected_disjoint_Union_open_subset:
  assumes A: "pairwise disjnt A" and B: "pairwise disjnt B"
      and SA: "\<And>S. S \<in> A \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and SB: "\<And>S. S \<in> B \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and eq [simp]: "\<Union>A = \<Union>B"
    shows "A \<subseteq> B"
sorry

lemma connected_disjoint_Union_open_unique:
  assumes A: "pairwise disjnt A" and B: "pairwise disjnt B"
      and SA: "\<And>S. S \<in> A \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and SB: "\<And>S. S \<in> B \<Longrightarrow> open S \<and> connected S \<and> S \<noteq> {}"
      and eq [simp]: "\<Union>A = \<Union>B"
    shows "A = B"
sorry

proposition components_open_unique:
 fixes S :: "'a::real_normed_vector set"
  assumes "pairwise disjnt A" "\<Union>A = S"
          "\<And>X. X \<in> A \<Longrightarrow> open X \<and> connected X \<and> X \<noteq> {}"
    shows "components S = A"
sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Existence of unbounded components\<close>

lemma cobounded_unbounded_component:
    fixes S :: "'a :: euclidean_space set"
    assumes "bounded (-S)"
      shows "\<exists>x. x \<in> S \<and> \<not> bounded (connected_component_set S x)"
sorry

lemma cobounded_unique_unbounded_component:
    fixes S :: "'a :: euclidean_space set"
    assumes bs: "bounded (-S)" and "2 \<le> DIM('a)"
        and bo: "\<not> bounded(connected_component_set S x)"
                "\<not> bounded(connected_component_set S y)"
      shows "connected_component_set S x = connected_component_set S y"
sorry

lemma cobounded_unbounded_components:
    fixes S :: "'a :: euclidean_space set"
    shows "bounded (-S) \<Longrightarrow> \<exists>c. c \<in> components S \<and> \<not>bounded c"
sorry

lemma cobounded_unique_unbounded_components:
    fixes S :: "'a :: euclidean_space set"
    shows  "\<lbrakk>bounded (- S); c \<in> components S; \<not> bounded c; c' \<in> components S; \<not> bounded c'; 2 \<le> DIM('a)\<rbrakk> \<Longrightarrow> c' = c"
sorry

lemma cobounded_has_bounded_component:
  fixes S :: "'a :: euclidean_space set"
  assumes "bounded (- S)" "\<not> connected S" "2 \<le> DIM('a)"
  obtains C where "C \<in> components S" "bounded C"
sorry

subsection\<open>The \<open>inside\<close> and \<open>outside\<close> of a Set\<close>

text\<^marker>\<open>tag important\<close>\<open>The inside comprises the points in a bounded connected component of the set's complement.
  The outside comprises the points in unbounded connected component of the complement.\<close>

definition\<^marker>\<open>tag important\<close> inside where
  "inside S \<equiv> {x. (x \<notin> S) \<and> bounded(connected_component_set ( - S) x)}"

definition\<^marker>\<open>tag important\<close> outside where
  "outside S \<equiv> -S \<inter> {x. \<not> bounded(connected_component_set (- S) x)}"

lemma outside: "outside S = {x. \<not> bounded(connected_component_set (- S) x)}"
sorry

lemma inside_no_overlap [simp]: "inside S \<inter> S = {}"
sorry

lemma outside_no_overlap [simp]:
   "outside S \<inter> S = {}"
sorry

lemma inside_Int_outside [simp]: "inside S \<inter> outside S = {}"
sorry

lemma inside_Un_outside [simp]: "inside S \<union> outside S = (- S)"
sorry

lemma inside_eq_outside:
   "inside S = outside S \<longleftrightarrow> S = UNIV"
sorry

lemma inside_outside: "inside S = (- (S \<union> outside S))"
sorry

lemma outside_inside: "outside S = (- (S \<union> inside S))"
sorry

lemma union_with_inside: "S \<union> inside S = - outside S"
sorry

lemma union_with_outside: "S \<union> outside S = - inside S"
sorry

lemma outside_mono: "S \<subseteq> T \<Longrightarrow> outside T \<subseteq> outside S"
sorry

lemma inside_mono: "S \<subseteq> T \<Longrightarrow> inside S - T \<subseteq> inside T"
sorry

lemma segment_bound_lemma:
  fixes u::real
  assumes "x \<ge> B" "y \<ge> B" "0 \<le> u" "u \<le> 1"
  shows "(1 - u) * x + u * y \<ge> B"
sorry

lemma cobounded_outside:
  fixes S :: "'a :: real_normed_vector set"
  assumes "bounded S" shows "bounded (- outside S)"
sorry

lemma unbounded_outside:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded S \<Longrightarrow> \<not> bounded(outside S)"
sorry

lemma bounded_inside:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded S \<Longrightarrow> bounded(inside S)"
sorry

lemma connected_outside:
    fixes S :: "'a::euclidean_space set"
    assumes "bounded S" "2 \<le> DIM('a)"
    shows "connected(outside S)"
sorry

lemma outside_connected_component_lt:
  "outside S = {x. \<forall>B. \<exists>y. B < norm(y) \<and> connected_component (- S) x y}"
sorry

lemma outside_connected_component_le:
  "outside S = {x. \<forall>B. \<exists>y. B \<le> norm(y) \<and> connected_component (- S) x y}"
sorry

lemma not_outside_connected_component_lt:
    fixes S :: "'a::euclidean_space set"
    assumes S: "bounded S" and "2 \<le> DIM('a)"
      shows "- (outside S) = {x. \<forall>B. \<exists>y. B < norm(y) \<and> \<not> connected_component (- S) x y}"
sorry

lemma not_outside_connected_component_le:
  fixes S :: "'a::euclidean_space set"
  assumes S: "bounded S"  "2 \<le> DIM('a)"
  shows "- (outside S) = {x. \<forall>B. \<exists>y. B \<le> norm(y) \<and> \<not> connected_component (- S) x y}"
sorry

lemma inside_connected_component_lt:
    fixes S :: "'a::euclidean_space set"
    assumes S: "bounded S"  "2 \<le> DIM('a)"
      shows "inside S = {x. (x \<notin> S) \<and> (\<forall>B. \<exists>y. B < norm(y) \<and> \<not> connected_component (- S) x y)}"
sorry

lemma inside_connected_component_le:
    fixes S :: "'a::euclidean_space set"
    assumes S: "bounded S"  "2 \<le> DIM('a)"
      shows "inside S = {x. (x \<notin> S) \<and> (\<forall>B. \<exists>y. B \<le> norm(y) \<and> \<not> connected_component (- S) x y)}"
sorry

lemma inside_subset:
  assumes "connected U" and "\<not> bounded U" and "T \<union> U = - S"
  shows "inside S \<subseteq> T"
sorry

lemma frontier_not_empty:
  fixes S :: "'a :: real_normed_vector set"
  shows "\<lbrakk>S \<noteq> {}; S \<noteq> UNIV\<rbrakk> \<Longrightarrow> frontier S \<noteq> {}"
sorry

lemma frontier_eq_empty:
  fixes S :: "'a :: real_normed_vector set"
  shows "frontier S = {} \<longleftrightarrow> S = {} \<or> S = UNIV"
sorry

lemma frontier_of_connected_component_subset:
  fixes S :: "'a::real_normed_vector set"
  shows "frontier(connected_component_set S x) \<subseteq> frontier S"
sorry

lemma frontier_Union_subset_closure:
  fixes F :: "'a::real_normed_vector set set"
  shows "frontier(\<Union>F) \<subseteq> closure(\<Union>t \<in> F. frontier t)"
sorry

lemma frontier_Union_subset:
  fixes F :: "'a::real_normed_vector set set"
  shows "finite F \<Longrightarrow> frontier(\<Union>F) \<subseteq> (\<Union>t \<in> F. frontier t)"
sorry

lemma frontier_of_components_subset:
  fixes S :: "'a::real_normed_vector set"
  shows "C \<in> components S \<Longrightarrow> frontier C \<subseteq> frontier S"
sorry

lemma frontier_of_components_closed_complement:
  fixes S :: "'a::real_normed_vector set"
  shows "\<lbrakk>closed S; C \<in> components (- S)\<rbrakk> \<Longrightarrow> frontier C \<subseteq> S"
sorry

lemma frontier_minimal_separating_closed:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
      and nconn: "\<not> connected(- S)"
      and C: "C \<in> components (- S)"
      and conn: "\<And>T. \<lbrakk>closed T; T \<subset> S\<rbrakk> \<Longrightarrow> connected(- T)"
    shows "frontier C = S"
sorry

lemma connected_component_UNIV [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "connected_component_set UNIV x = UNIV"
sorry

lemma connected_component_eq_UNIV:
    fixes x :: "'a::real_normed_vector"
    shows "connected_component_set s x = UNIV \<longleftrightarrow> s = UNIV"
sorry

lemma components_UNIV [simp]: "components UNIV = {UNIV :: 'a::real_normed_vector set}"
sorry

lemma interior_inside_frontier:
    fixes S :: "'a::real_normed_vector set"
    assumes "bounded S"
      shows "interior S \<subseteq> inside (frontier S)"
sorry

lemma inside_empty [simp]: "inside {} = ({} :: 'a :: {real_normed_vector, perfect_space} set)"
sorry

lemma outside_empty [simp]: "outside {} = (UNIV :: 'a :: {real_normed_vector, perfect_space} set)"
sorry

lemma inside_same_component:
   "\<lbrakk>connected_component (- S) x y; x \<in> inside S\<rbrakk> \<Longrightarrow> y \<in> inside S"
sorry

lemma outside_same_component:
   "\<lbrakk>connected_component (- S) x y; x \<in> outside S\<rbrakk> \<Longrightarrow> y \<in> outside S"
sorry

lemma convex_in_outside:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  assumes S: "convex S" and z: "z \<notin> S"
    shows "z \<in> outside S"
sorry

lemma outside_convex:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  assumes "convex S"
    shows "outside S = - S"
sorry

lemma outside_singleton [simp]:
  fixes x :: "'a :: {real_normed_vector, perfect_space}"
  shows "outside {x} = -{x}"
sorry

lemma inside_convex:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  shows "convex S \<Longrightarrow> inside S = {}"
sorry

lemma inside_singleton [simp]:
  fixes x :: "'a :: {real_normed_vector, perfect_space}"
  shows "inside {x} = {}"
sorry

lemma outside_subset_convex:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  shows "\<lbrakk>convex T; S \<subseteq> T\<rbrakk> \<Longrightarrow> - T \<subseteq> outside S"
sorry

lemma outside_Un_outside_Un:
  fixes S :: "'a::real_normed_vector set"
  assumes "S \<inter> outside(T \<union> U) = {}"
  shows "outside(T \<union> U) \<subseteq> outside(T \<union> S)"
sorry

lemma outside_frontier_misses_closure:
    fixes S :: "'a::real_normed_vector set"
    assumes "bounded S"
    shows  "outside(frontier S) \<subseteq> - closure S"
sorry

lemma outside_frontier_eq_complement_closure:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
    assumes "bounded S" "convex S"
      shows "outside(frontier S) = - closure S"
sorry

lemma inside_frontier_eq_interior:
     fixes S :: "'a :: {real_normed_vector, perfect_space} set"
     shows "\<lbrakk>bounded S; convex S\<rbrakk> \<Longrightarrow> inside(frontier S) = interior S"
sorry

lemma open_inside:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "open (inside S)"
sorry

lemma open_outside:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "open (outside S)"
sorry

lemma closure_inside_subset:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "closure(inside S) \<subseteq> S \<union> inside S"
sorry

lemma frontier_inside_subset:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "frontier(inside S) \<subseteq> S"
sorry

lemma closure_outside_subset:
    fixes S :: "'a::real_normed_vector set"
    assumes "closed S"
      shows "closure(outside S) \<subseteq> S \<union> outside S"
sorry

lemma closed_path_image_Un_inside:
  fixes g :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "path g"
  shows   "closed (path_image g \<union> inside (path_image g))"
sorry

lemma frontier_outside_subset:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "frontier(outside S) \<subseteq> S"
sorry

lemma inside_complement_unbounded_connected_empty:
     "\<lbrakk>connected (- S); \<not> bounded (- S)\<rbrakk> \<Longrightarrow> inside S = {}"
sorry

lemma inside_bounded_complement_connected_empty:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "\<lbrakk>connected (- S); bounded S\<rbrakk> \<Longrightarrow> inside S = {}"
sorry

lemma inside_inside:
    assumes "S \<subseteq> inside T"
    shows "inside S - T \<subseteq> inside T"
sorry

lemma inside_inside_subset: "inside(inside S) \<subseteq> S"
sorry

lemma inside_outside_intersect_connected:
      "\<lbrakk>connected T; inside S \<inter> T \<noteq> {}; outside S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> S \<inter> T \<noteq> {}"
sorry

lemma outside_bounded_nonempty:
  fixes S :: "'a :: {real_normed_vector, perfect_space} set"
  assumes "bounded S" shows "outside S \<noteq> {}"
sorry

lemma outside_compact_in_open:
    fixes S :: "'a :: {real_normed_vector,perfect_space} set"
    assumes S: "compact S" and T: "open T" and "S \<subseteq> T" "T \<noteq> {}"
      shows "outside S \<inter> T \<noteq> {}"
sorry

lemma inside_inside_compact_connected:
    fixes S :: "'a :: euclidean_space set"
    assumes S: "closed S" and T: "compact T" and "connected T" "S \<subseteq> inside T"
      shows "inside S \<subseteq> inside T"
sorry

lemma connected_with_inside:
    fixes S :: "'a :: real_normed_vector set"
    assumes S: "closed S" and cons: "connected S"
      shows "connected(S \<union> inside S)"
sorry

text\<open>The proof is virtually the same as that above.\<close>
lemma connected_with_outside:
    fixes S :: "'a :: real_normed_vector set"
    assumes S: "closed S" and cons: "connected S"
      shows "connected(S \<union> outside S)"
sorry

lemma inside_inside_eq_empty [simp]:
    fixes S :: "'a :: {real_normed_vector, perfect_space} set"
    assumes S: "closed S" and cons: "connected S"
    shows "inside (inside S) = {}"
sorry

lemma inside_in_components:
     "inside S \<in> components (- S) \<longleftrightarrow> connected(inside S) \<and> inside S \<noteq> {}" (is "?lhs = ?rhs")
sorry

text\<open>The proof is like that above.\<close>
lemma outside_in_components:
     "outside S \<in> components (- S) \<longleftrightarrow> connected(outside S) \<and> outside S \<noteq> {}" (is "?lhs = ?rhs")
sorry

lemma bounded_unique_outside:
  fixes S :: "'a :: euclidean_space set"
  assumes "bounded S" "DIM('a) \<ge> 2"
  shows "(c \<in> components (- S) \<and> \<not> bounded c) \<longleftrightarrow> c = outside S"
sorry

subsection\<open>Condition for an open map's image to contain a ball\<close>

proposition ball_subset_open_map_image:
  fixes f :: "'a::heine_borel \<Rightarrow> 'b :: {real_normed_vector,heine_borel}"
  assumes contf: "continuous_on (closure S) f"
      and oint: "open (f ` interior S)"
      and le_no: "\<And>z. z \<in> frontier S \<Longrightarrow> r \<le> norm(f z - f a)"
      and "bounded S" "a \<in> S" "0 < r"
    shows "ball (f a) r \<subseteq> f ` S"
sorry


subsubsection\<open>Special characterizations of classes of functions into and out of R.\<close>

lemma Hausdorff_space_euclidean [simp]: "Hausdorff_space (euclidean :: 'a::metric_space topology)"
sorry

proposition embedding_map_into_euclideanreal:
  assumes "path_connected_space X"
  shows "embedding_map X euclideanreal f \<longleftrightarrow>
         continuous_map X euclideanreal f \<and> inj_on f (topspace X)"
sorry

subsubsection \<open>An injective function into R is a homeomorphism and so an open map.\<close>

lemma injective_into_1d_eq_homeomorphism:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  assumes f: "continuous_on S f" and S: "path_connected S"
  shows "inj_on f S \<longleftrightarrow> (\<exists>g. homeomorphism S (f ` S) f g)"
sorry

lemma injective_into_1d_imp_open_map:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  assumes "continuous_on S f" "path_connected S" "inj_on f S" "openin (subtopology euclidean S) T"
  shows "openin (subtopology euclidean (f ` S)) (f ` T)"
sorry

lemma homeomorphism_into_1d:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  assumes "path_connected S" "continuous_on S f" "f ` S = T" "inj_on f S"
  shows "\<exists>g. homeomorphism S T f g"
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Rectangular paths\<close>

definition\<^marker>\<open>tag unimportant\<close> rectpath where
  "rectpath a1 a3 = (let a2 = Complex (Re a3) (Im a1); a4 = Complex (Re a1) (Im a3)
                      in linepath a1 a2 +++ linepath a2 a3 +++ linepath a3 a4 +++ linepath a4 a1)"

lemma path_rectpath [simp, intro]: "path (rectpath a b)"
sorry

lemma pathstart_rectpath [simp]: "pathstart (rectpath a1 a3) = a1"
sorry

lemma pathfinish_rectpath [simp]: "pathfinish (rectpath a1 a3) = a1"
sorry

lemma simple_path_rectpath [simp, intro]:
  assumes "Re a1 \<noteq> Re a3" "Im a1 \<noteq> Im a3"
  shows   "simple_path (rectpath a1 a3)"
sorry

lemma path_image_rectpath:
  assumes "Re a1 \<le> Re a3" "Im a1 \<le> Im a3"
  shows "path_image (rectpath a1 a3) =
           {z. Re z \<in> {Re a1, Re a3} \<and> Im z \<in> {Im a1..Im a3}} \<union>
           {z. Im z \<in> {Im a1, Im a3} \<and> Re z \<in> {Re a1..Re a3}}" (is "?lhs = ?rhs")
sorry

lemma path_image_rectpath_subset_cbox:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) \<subseteq> cbox a b"
sorry

lemma path_image_rectpath_inter_box:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) \<inter> box a b = {}"
sorry

lemma path_image_rectpath_cbox_minus_box:
  assumes "Re a \<le> Re b" "Im a \<le> Im b"
  shows   "path_image (rectpath a b) = cbox a b - box a b"
sorry

end
