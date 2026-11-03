(* Title:      HOL/Analysis/Cross3.thy
   Author:     L C Paulson, University of Cambridge

Ported from HOL Light
*)

section\<open>Vector Cross Products in 3 Dimensions\<close>

theory "Cross3"
  imports Determinants Cartesian_Euclidean_Space
begin

context includes no set_product_syntax
begin \<comment>\<open>locally disable syntax for set product, to avoid warnings\<close>

definition\<^marker>\<open>tag important\<close> cross3 :: "[real^3, real^3] \<Rightarrow> real^3"  (infixr \<open>\<times>\<close> 80)
  where "a \<times> b \<equiv>
    vector [a$2 * b$3 - a$3 * b$2,
            a$3 * b$1 - a$1 * b$3,
            a$1 * b$2 - a$2 * b$1]"

end

open_bundle cross3_syntax
begin
notation cross3 (infixr \<open>\<times>\<close> 80)
unbundle no set_product_syntax
end


subsection\<open> Basic lemmas\<close>

lemmas cross3_simps = cross3_def inner_vec_def sum_3 det_3 vec_eq_iff vector_def algebra_simps

lemma dot_cross_self: "x \<bullet> (x \<times> y) = 0" "x \<bullet> (y \<times> x) = 0" "(x \<times> y) \<bullet> y = 0" "(y \<times> x) \<bullet> y = 0"
sorry

lemma  orthogonal_cross: "orthogonal (x \<times> y) x" "orthogonal (x \<times> y) y"  
                        "orthogonal y (x \<times> y)" "orthogonal (x \<times> y) x"
sorry

lemma  cross_zero_left [simp]: "0 \<times> x = 0" and cross_zero_right [simp]: "x \<times> 0 = 0" for x::"real^3"
sorry

lemma  cross_skew: "(x \<times> y) = -(y \<times> x)" for x::"real^3"
sorry

lemma  cross_refl [simp]: "x \<times> x = 0" for x::"real^3"
sorry

lemma  cross_add_left: "(x + y) \<times> z = (x \<times> z) + (y \<times> z)" for x::"real^3"
sorry

lemma  cross_add_right: "x \<times> (y + z) = (x \<times> y) + (x \<times> z)" for x::"real^3"
sorry

lemma  cross_mult_left: "(c *\<^sub>R x) \<times> y = c *\<^sub>R (x \<times> y)" for x::"real^3"
sorry

lemma  cross_mult_right: "x \<times> (c *\<^sub>R y) = c *\<^sub>R (x \<times> y)" for x::"real^3"
sorry

lemma  cross_minus_left [simp]: "(-x) \<times> y = - (x \<times> y)" for x::"real^3"
sorry

lemma  cross_minus_right [simp]: "x \<times> -y = - (x \<times> y)" for x::"real^3"
sorry

lemma  left_diff_distrib: "(x - y) \<times> z = x \<times> z - y \<times> z" for x::"real^3"
sorry

lemma  right_diff_distrib: "x \<times> (y - z) = x \<times> y - x \<times> z" for x::"real^3"
sorry

hide_fact (open) left_diff_distrib right_diff_distrib

proposition Jacobi: "x \<times> (y \<times> z) + y \<times> (z \<times> x) + z \<times> (x \<times> y) = 0" for x::"real^3"
sorry

proposition Lagrange: "x \<times> (y \<times> z) = (x \<bullet> z) *\<^sub>R y - (x \<bullet> y) *\<^sub>R z"
sorry

proposition cross_triple: "(x \<times> y) \<bullet> z = (y \<times> z) \<bullet> x"
sorry

lemma  cross_components:
   "(x \<times> y)$1 = x$2 * y$3 - y$2 * x$3" "(x \<times> y)$2 = x$3 * y$1 - y$3 * x$1" "(x \<times> y)$3 = x$1 * y$2 - y$1 * x$2"
sorry

lemma  cross_basis: "(axis 1 1) \<times> (axis 2 1) = axis 3 1" "(axis 2 1) \<times> (axis 1 1) = -(axis 3 1)" 
                   "(axis 2 1) \<times> (axis 3 1) = axis 1 1" "(axis 3 1) \<times> (axis 2 1) = -(axis 1 1)" 
                   "(axis 3 1) \<times> (axis 1 1) = axis 2 1" "(axis 1 1) \<times> (axis 3 1) = -(axis 2 1)"
sorry

lemma  cross_basis_nonzero:
  "u \<noteq> 0 \<Longrightarrow> u \<times> axis 1 1 \<noteq> 0 \<or> u \<times> axis 2 1 \<noteq> 0 \<or> u \<times> axis 3 1 \<noteq> 0"
sorry

lemma  cross_dot_cancel:
  fixes x::"real^3"
  assumes deq: "x \<bullet> y = x \<bullet> z" and veq: "x \<times> y = x \<times> z" and x: "x \<noteq> 0"
  shows "y = z"
sorry

lemma  norm_cross_dot: "(norm (x \<times> y))\<^sup>2 + (x \<bullet> y)\<^sup>2 = (norm x * norm y)\<^sup>2"
sorry

lemma  dot_cross_det: "x \<bullet> (y \<times> z) = det(vector[x,y,z])"
sorry

lemma  cross_cross_det: "(w \<times> x) \<times> (y \<times> z) = det(vector[w,x,z]) *\<^sub>R y - det(vector[w,x,y]) *\<^sub>R z"
sorry

proposition  dot_cross: "(w \<times> x) \<bullet> (y \<times> z) = (w \<bullet> y) * (x \<bullet> z) - (w \<bullet> z) * (x \<bullet> y)"
sorry

proposition  norm_cross: "(norm (x \<times> y))\<^sup>2 = (norm x)\<^sup>2 * (norm y)\<^sup>2 - (x \<bullet> y)\<^sup>2"
sorry

lemma  cross_eq_0: "x \<times> y = 0 \<longleftrightarrow> collinear{0,x,y}"
sorry

lemma  cross_eq_self: "x \<times> y = x \<longleftrightarrow> x = 0" "x \<times> y = y \<longleftrightarrow> y = 0"
sorry

lemma  norm_and_cross_eq_0:
   "x \<bullet> y = 0 \<and> x \<times> y = 0 \<longleftrightarrow> x = 0 \<or> y = 0" (is "?lhs = ?rhs")
sorry

lemma  bilinear_cross: "bilinear(\<times>)"
sorry

subsection   \<open>Preservation by rotation, or other orthogonal transformation up to sign\<close>

lemma  cross_matrix_mult: "transpose A *v ((A *v x) \<times> (A *v y)) = det A *\<^sub>R (x \<times> y)"
sorry

lemma  cross_orthogonal_matrix:
  assumes "orthogonal_matrix A"
  shows "(A *v x) \<times> (A *v y) = det A *\<^sub>R (A *v (x \<times> y))"
sorry

lemma  cross_rotation_matrix: "rotation_matrix A \<Longrightarrow> (A *v x) \<times> (A *v y) =  A *v (x \<times> y)"
sorry

lemma  cross_rotoinversion_matrix: "rotoinversion_matrix A \<Longrightarrow> (A *v x) \<times> (A *v y) = - A *v (x \<times> y)"
sorry

lemma  cross_orthogonal_transformation:
  assumes "orthogonal_transformation f"
  shows   "(f x) \<times> (f y) = det(matrix f) *\<^sub>R f(x \<times> y)"
sorry

lemma  cross_linear_image:
   "\<lbrakk>linear f; \<And>x. norm(f x) = norm x; det(matrix f) = 1\<rbrakk>
           \<Longrightarrow> (f x) \<times> (f y) = f(x \<times> y)"
sorry
subsection \<open>Continuity\<close>

lemma  continuous_cross: "\<lbrakk>continuous F f; continuous F g\<rbrakk> \<Longrightarrow> continuous F (\<lambda>x. (f x) \<times> (g x))"
sorry

lemma  continuous_on_cross:
  fixes f :: "'a::t2_space \<Rightarrow> real^3"
  shows "\<lbrakk>continuous_on S f; continuous_on S g\<rbrakk> \<Longrightarrow> continuous_on S (\<lambda>x. (f x) \<times> (g x))"
sorry

unbundle no cross3_syntax

end
