(*  Title:      HOL/Analysis/Inner_Product.thy
    Author:     Brian Huffman
*)

section \<open>Inner Product Spaces and Gradient Derivative\<close>

theory Inner_Product
imports Complex_Main
begin
declare [[quick_and_dirty = true]]


subsection \<open>Real inner product spaces\<close>

text \<open>
  Temporarily relax type constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::open set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::dist \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::norm \<Rightarrow> real\<close>)\<close>

class real_inner = real_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  fixes inner :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes inner_commute: "inner x y = inner y x"
  and inner_add_left: "inner (x + y) z = inner x z + inner y z"
  and inner_scaleR_left [simp]: "inner (scaleR r x) y = r * (inner x y)"
  and inner_ge_zero [simp]: "0 \<le> inner x x"
  and inner_eq_zero_iff [simp]: "inner x x = 0 \<longleftrightarrow> x = 0"
  and norm_eq_sqrt_inner: "norm x = sqrt (inner x x)"
begin

lemma inner_zero_left [simp]: "inner 0 x = 0"
  
  sorry


lemma inner_minus_left [simp]: "inner (- x) y = - inner x y"
  
  sorry


lemma inner_diff_left: "inner (x - y) z = inner x z - inner y z"
  
  sorry


lemma inner_sum_left: "inner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. inner (f x) y)"
  
  sorry


lemma all_zero_iff [simp]: "(\<forall>u. inner x u = 0) \<longleftrightarrow> (x = 0)"
  
  sorry


text \<open>Transfer distributivity rules to right argument.\<close>

lemma inner_add_right: "inner x (y + z) = inner x y + inner x z"
  
  sorry


lemma inner_scaleR_right [simp]: "inner x (scaleR r y) = r * (inner x y)"
  
  sorry


lemma inner_zero_right [simp]: "inner x 0 = 0"
  
  sorry


lemma inner_minus_right [simp]: "inner x (- y) = - inner x y"
  
  sorry


lemma inner_diff_right: "inner x (y - z) = inner x y - inner x z"
  
  sorry


lemma inner_sum_right: "inner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. inner x (f y))"
  
  sorry


lemmas inner_add [algebra_simps] = inner_add_left inner_add_right
lemmas inner_diff [algebra_simps]  = inner_diff_left inner_diff_right
lemmas inner_scaleR = inner_scaleR_left inner_scaleR_right

text \<open>Legacy theorem names\<close>
lemmas inner_left_distrib = inner_add_left
lemmas inner_right_distrib = inner_add_right
lemmas inner_distrib = inner_left_distrib inner_right_distrib

lemma inner_gt_zero_iff [simp]: "0 < inner x x \<longleftrightarrow> x \<noteq> 0"
  
  sorry


lemma power2_norm_eq_inner: "(norm x)\<^sup>2 = inner x x"
  
  sorry


lemma dot_square_norm: "inner x x = (norm x)\<^sup>2"
  
  sorry


text \<open>Identities involving real multiplication and division.\<close>

lemma inner_mult_left: "inner (of_real m * a) b = m * (inner a b)"
  
  sorry


lemma inner_mult_right: "inner a (of_real m * b) = m * (inner a b)"
  
  sorry


lemma inner_mult_left': "inner (a * of_real m) b = m * (inner a b)"
  
  sorry


lemma inner_mult_right': "inner a (b * of_real m) = (inner a b) * m"
  
  sorry


lemma Cauchy_Schwarz_ineq:
  "(inner x y)\<^sup>2 \<le> inner x x * inner y y"
  
  sorry


lemma Cauchy_Schwarz_ineq2:
  "\<bar>inner x y\<bar> \<le> norm x * norm y"
  
  sorry


lemma norm_cauchy_schwarz: "inner x y \<le> norm x * norm y"
  
  sorry


subclass real_normed_vector

  sorry


end

lemma square_bound_lemma:
  fixes x :: real
  shows "x < (1 + x) * (1 + x)"
  
  sorry


lemma square_continuous:
  fixes e :: real
  shows "e > 0 \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>y. \<bar>y - x\<bar> < d \<longrightarrow> \<bar>y * y - x * x\<bar> < e)"
  
  sorry


lemma norm_le: "norm x \<le> norm y \<longleftrightarrow> inner x x \<le> inner y y"
  
  sorry


lemma norm_lt: "norm x < norm y \<longleftrightarrow> inner x x < inner y y"
  
  sorry



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma norm_eq: "norm x = norm y \<longleftrightarrow> inner x x = inner y y"
  
  