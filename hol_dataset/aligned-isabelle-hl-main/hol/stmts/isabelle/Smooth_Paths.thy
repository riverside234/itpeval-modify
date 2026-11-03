(*
  Material originally from HOL Light, ported by Larry Paulson, moved here by Manuel Eberl
*)
section\<^marker>\<open>tag unimportant\<close> \<open>Smooth paths\<close>
theory Smooth_Paths
  imports Retracts
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Homeomorphisms of arc images\<close>

lemma path_connected_arc_complement:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>" "2 \<le> DIM('a)"
  shows "path_connected(- path_image \<gamma>)"
sorry

lemma connected_arc_complement:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>" "2 \<le> DIM('a)"
  shows "connected(- path_image \<gamma>)"
sorry

lemma inside_arc_empty:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>"
    shows "inside(path_image \<gamma>) = {}"
sorry

lemma inside_simple_curve_imp_closed:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
    shows "\<lbrakk>simple_path \<gamma>; x \<in> inside(path_image \<gamma>)\<rbrakk> \<Longrightarrow> pathfinish \<gamma> = pathstart \<gamma>"
sorry

subsection \<open>Piecewise differentiability of paths\<close>

lemma continuous_on_joinpaths_D1:
  assumes "continuous_on {0..1} (g1 +++ g2)"
  shows "continuous_on {0..1} g1"
sorry

lemma continuous_on_joinpaths_D2:
    "\<lbrakk>continuous_on {0..1} (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> continuous_on {0..1} g2"
sorry

lemma piecewise_differentiable_D1:
  assumes "(g1 +++ g2) piecewise_differentiable_on {0..1}"
  shows "g1 piecewise_differentiable_on {0..1}"
sorry

lemma piecewise_differentiable_D2:
  assumes "(g1 +++ g2) piecewise_differentiable_on {0..1}" and eq: "pathfinish g1 = pathstart g2"
  shows "g2 piecewise_differentiable_on {0..1}"
sorry

lemma piecewise_C1_differentiable_D1:
  fixes g1 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}"
    shows "g1 piecewise_C1_differentiable_on {0..1}"
sorry

lemma piecewise_C1_differentiable_D2:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}" "pathfinish g1 = pathstart g2"
    shows "g2 piecewise_C1_differentiable_on {0..1}"
sorry


subsection \<open>Valid paths, and their start and finish\<close>

definition\<^marker>\<open>tag important\<close> valid_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "valid_path f \<equiv> f piecewise_C1_differentiable_on {0..1::real}"

definition closed_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "closed_path g \<equiv> g 0 = g 1"

text\<open>In particular, all results for paths apply\<close>

lemma valid_path_imp_path: "valid_path g \<Longrightarrow> path g"
sorry

lemma connected_valid_path_image: "valid_path g \<Longrightarrow> connected(path_image g)"
sorry

lemma compact_valid_path_image: "valid_path g \<Longrightarrow> compact(path_image g)"
sorry

lemma bounded_valid_path_image: "valid_path g \<Longrightarrow> bounded(path_image g)"
sorry

lemma closed_valid_path_image: "valid_path g \<Longrightarrow> closed(path_image g)"
sorry

lemma valid_path_translation_eq: "valid_path ((+)d \<circ> p) \<longleftrightarrow> valid_path p"
sorry

lemma valid_path_compose:
  assumes "valid_path g"
      and der: "\<And>x. x \<in> path_image g \<Longrightarrow> f field_differentiable (at x)"
      and con: "continuous_on (path_image g) (deriv f)"
    shows "valid_path (f \<circ> g)"
sorry

lemma valid_path_uminus_comp[simp]:
  fixes g::"real \<Rightarrow> 'a ::real_normed_field"
  shows "valid_path (uminus \<circ> g) \<longleftrightarrow> valid_path g"
sorry

lemma valid_path_offset[simp]:
  shows "valid_path (\<lambda>t. g t - z) \<longleftrightarrow> valid_path g"
sorry

lemma valid_path_imp_reverse:
  assumes "valid_path g"
    shows "valid_path(reversepath g)"
sorry

lemma valid_path_reversepath [simp]: "valid_path(reversepath g) \<longleftrightarrow> valid_path g"
sorry

lemma valid_path_join:
  assumes "valid_path g1" "valid_path g2" "pathfinish g1 = pathstart g2"
    shows "valid_path(g1 +++ g2)"
sorry

lemma valid_path_join_D1:
  fixes g1 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "valid_path (g1 +++ g2) \<Longrightarrow> valid_path g1"
sorry

lemma valid_path_join_D2:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>valid_path (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> valid_path g2"
sorry

lemma valid_path_join_eq [simp]:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "pathfinish g1 = pathstart g2 \<Longrightarrow> (valid_path(g1 +++ g2) \<longleftrightarrow> valid_path g1 \<and> valid_path g2)"
sorry

lemma valid_path_shiftpath [intro]:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "valid_path(shiftpath a g)"
sorry

lemma vector_derivative_linepath_within:
    "x \<in> {0..1} \<Longrightarrow> vector_derivative (linepath a b) (at x within {0..1}) = b - a"
sorry

lemma vector_derivative_linepath_at [simp]: "vector_derivative (linepath a b) (at x) = b - a"
sorry

lemma valid_path_linepath [iff]: "valid_path (linepath a b)"
sorry

lemma valid_path_subpath:
  fixes g :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "valid_path(subpath u v g)"
sorry

lemma valid_path_rectpath [simp, intro]: "valid_path (rectpath a b)"
sorry

lemma linear_image_valid_path:
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes  "valid_path p" "linear f"
  shows    "valid_path (f \<circ> p)"
sorry

lemma valid_path_times:
  fixes \<gamma>::"real \<Rightarrow> 'a ::real_normed_field"
  assumes "c\<noteq>0"
  shows "valid_path ((*) c \<circ> \<gamma>) = valid_path \<gamma>"
sorry

lemma path_compose_cnj_iff [simp]: "path (cnj \<circ> p) \<longleftrightarrow> path p"
sorry

lemma valid_path_cnj:
  fixes g::"real \<Rightarrow> complex"
    shows "valid_path (cnj \<circ> g) = valid_path g"
sorry

end
