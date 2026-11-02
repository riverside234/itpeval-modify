(*  Title:      Cayley_Hamilton/Cayley_Hamilton.thy
    Author:     Johannes Hölzl, TU München
    Author:     Stefan Hetzl, TU Wien
    Author:     Stephan Adelsberge, WU Wien
    Author:     Florian Pollak, TU Wien
*)

(*<*)
theory Cayley_Hamilton
imports
  Square_Matrix
  "HOL-Computational_Algebra.Polynomial"  
begin
declare [[quick_and_dirty = true]]


definition C :: "'a \<Rightarrow> 'a::ring_1 poly" where "C c = [:c:]"
abbreviation CC (\<open>\<^bold>C\<close>) where "\<^bold>C \<equiv> map_sq_matrix C"

lemma degree_C[simp]: "degree (C a) = 0"
  
  sorry


lemma coeff_C_0[simp]: "coeff (C x) 0 = x"
  
  sorry


lemma coeff_C_gt0[simp]: "0 < n \<Longrightarrow> coeff (C x) n = 0"
  
  sorry


lemma coeff_C_eq: "coeff (C x) n = (if n = 0 then x else 0)"
  
  sorry


lemma coeff_mult_C[simp]: "coeff (a * C x) n = coeff a n * x"
  
  sorry


lemma coeff_C_mult[simp]: "coeff (C x * a) n = x * coeff a n"
  
  sorry


lemma C_0[simp]: "C 0 = 0"
  
  sorry


lemma C_1[simp]: "C 1 = 1"
  
  sorry


lemma C_linear:
  shows C_mult: "C (a * b) = C b * C a"
    and C_add: "C (a + b) = C a + C b"
    and C_minus: "C (- a) = - C a"
    and C_diff: "C (a - b) = C a - C b"
  
  sorry


definition X :: "'a::ring_1 poly" where "X = [:0, 1:]"
abbreviation XX (\<open>\<^bold>X\<close>) where "\<^bold>X \<equiv> diag X"

lemma degree_X[simp]: "degree X = 1"
  
  sorry


lemma coeff_X_Suc_0[simp]: "coeff X (Suc 0) = 1"
  
  sorry


lemma coeff_X_mult[simp]: "coeff (X * p) (Suc i) = coeff p i"
  
  sorry


lemma coeff_mult_X[simp]: "coeff (p * X) (Suc i) = coeff p i"
  
  sorry


lemma coeff_X_mult_0[simp]: "coeff (X * p) 0 = 0"
  
  sorry


lemma coeff_mult_X_0[simp]: "coeff (p * X) 0 = 0"
  
  sorry


lemma coeff_X: "coeff X i = (if i = 1 then 1 else 0)"
  
  sorry


lemma coeff_pow_X: "coeff (X ^ i) n = (if i = n then 1 else 0)"
  
  sorry


lemma coeff_pow_X_eq[simp]: "coeff (X^i) i = 1"
  
  sorry


lemma (in monoid_mult) power_ac: "a * (a^n * x) = a^n * (a * x)"
  
  sorry


text\<open>This theory contains auxiliary lemmas on polynomials.\<close>

lemma degree_prod_le: "degree (\<Prod>i\<in>S. f i) \<le> (\<Sum>i\<in>S. degree (f i))"
  
  sorry


lemma coeff_mult_sum:
  "degree p \<le> m \<Longrightarrow> degree q \<le> n \<Longrightarrow> coeff (p * q) (m + n) = coeff p m * coeff q n"
  
  sorry


lemma coeff_mult_prod_sum:
  "coeff (\<Prod>i\<in>S. f i) (\<Sum>i\<in>S. degree (f i)) = (\<Prod>i\<in>S. coeff (f i) (degree (f i)))"
  
  sorry


lemma degree_sum_less:
  "0 < n \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> degree (f x) < n) \<Longrightarrow> degree (\<Sum>x\<in>A. f x) < n" 
  
  sorry


lemma degree_sum_le:
  shows "(\<And>x. x \<in> A \<Longrightarrow> degree (f x) \<le> n) \<Longrightarrow> degree (\<Sum>x\<in>A. f x) \<le> n"
  
  sorry


lemma degree_sum_le_Max:
  "finite F \<Longrightarrow> degree (sum f F) \<le> Max ((\<lambda>x. degree (f x))`F)"
  
  sorry


lemma poly_as_sum_of_monoms': assumes n: "degree p \<le> n" shows "(\<Sum>i\<le>n. X^i * C (coeff p i)) = p"
  
  sorry


lemma poly_as_sum_of_monoms: "(\<Sum>i\<le>degree p. X^i * C (coeff p i)) = p"
  
  sorry


lemma degree_sum_unique':
  assumes I: "finite I" "i \<notin> I" "\<And>j. j \<in> I \<Longrightarrow> degree (p j) < degree (p i)"
  shows "degree (\<Sum>i\<in>insert i I. p i) = degree (p i)"
  
  sorry


lemma degree_sum_unique:
  "finite I \<Longrightarrow> i \<in> I \<Longrightarrow> (\<And>j. j \<in> I \<Longrightarrow> j \<noteq> i \<Longrightarrow> degree (p j) < degree (p i)) \<Longrightarrow>
    degree (\<Sum>i\<in>I. p i) = degree (p i)"
  
  sorry


lemma coeff_sum_unique:
  fixes p :: "'a \<Rightarrow> 'b::semiring_0 poly"
  assumes I: "finite I" "i \<in> I" "\<And>j. j \<in> I \<Longrightarrow> j \<noteq> i \<Longrightarrow> degree (p j) < degree (p i)"
  shows "coeff (\<Sum>i\<in>I. p i) (degree (p i)) = coeff (p i) (degree (p i))"
  
  sorry


lemma diag_coeff: "diag (coeff x i) = map_sq_matrix (\<lambda>x. coeff x i) (diag x)"
  
  sorry


lemma smult_one: "x *\<^sub>S 1 = diag x"
  
  sorry


lemma sum_telescope_Ico: "a \<le> b \<Longrightarrow> (\<Sum>i=a ..< b. f i - f (Suc i) ::_::ab_group_add) = f a - f b"
  
  sorry


lemmas map_sq_matrix = map_sq_matrix_diff map_sq_matrix_add map_sq_matrix_smult map_sq_matrix_sum

lemma sign_permut: "degree (of_int (sign p) * q) = degree q" 
  
  sorry


lemma degree_det:
  assumes "\<And>j. j permutes UNIV \<Longrightarrow> j \<noteq> id \<Longrightarrow> degree (\<Prod>i\<in>UNIV. to_fun A i (j i)) < degree (\<Prod>i\<in>UNIV. to_fun A i i)"
  shows "degree (det A) = degree (\<Prod>i\<in>UNIV. to_fun A i i)"
  
  sorry


definition max_degree :: "'a::zero poly^^'n \<Rightarrow> nat" where
  "max_degree A = Max (range (\<lambda>(i, j). degree (to_fun A i j)))"

lemma degree_le_max_degree: "degree (to_fun A i j) \<le> max_degree A"
  
  sorry


definition "charpoly A = det (\<^bold>X - \<^bold>C A)"

lemma degree_diff_cancel: "degree q < degree p \<Longrightarrow> degree (p - q::_::ab_group_add poly) = degree p"
  
  sorry


lemma
  fixes A :: "'a::comm_ring_1^^'n"
  shows degree_charpoly: "degree (charpoly A) = CARD('n)"
    and coeff_charpoly: "coeff (charpoly A) (degree (charpoly A)) = 1"
  
  sorry


definition "max_perm_degree A = Max ((\<lambda>p. \<Sum>i\<in>UNIV. degree (to_fun A i (p i)))`{p. p permutes UNIV})"

lemma max_perm_degree_eqI:
  "(\<And>p. p permutes (UNIV::'a::finite set) \<Longrightarrow> (\<Sum>i\<in>UNIV. degree (to_fun A i (p i))) \<le> x) \<Longrightarrow>
    (\<exists>p. p permutes UNIV \<and> (\<Sum>i\<in>UNIV. degree (to_fun A i (p i))) = x) \<Longrightarrow>
    max_perm_degree A = x"
  
  sorry


lemma degree_prod_le_max_perm_degree:
  "j permutes (UNIV::'a::finite set) \<Longrightarrow> degree (\<Prod>i\<in>UNIV. to_fun A i (j i)) \<le> max_perm_degree A"
  
  sorry


lemma degree_le_max_perm_degree: "degree (det A) \<le> max_perm_degree A"
  
  sorry


lemma max_degree_adjugate:
  fixes A :: "_^^'n"
  shows "max_degree (adjugate (\<^bold>X - \<^bold>C A)) = CARD('n) - 1"
    (is "?R = _")
  
  sorry


definition poly_mat :: "'a::ring_1 poly \<Rightarrow> 'a^^'n \<Rightarrow> 'a^^'n" where
  "poly_mat p A = (\<Sum>i\<le>degree p. coeff p i *\<^sub>S A^i)"

lemma zero_smult[simp]: "0 *\<^sub>S M = (0::'a::semiring_1^^'n)"
  
  sorry


lemma smult_smult: "a *\<^sub>S b *\<^sub>S M = (a * b::'a::monoid_mult) *\<^sub>S M"
  
  sorry


lemma map_sq_matrix_mult_eq_smult[simp]: "map_sq_matrix ((*) a) M = a *\<^sub>S M"
  
  sorry


lemma coeff_smult_1: "coeff p i *\<^sub>S m = m * map_sq_matrix (\<lambda>p. coeff p i) (p *\<^sub>S 1::_::comm_ring_1 ^^ 'n)"
  
  sorry


lemma map_sq_matrix_if_distrib[simp]:
  "map_sq_matrix (\<lambda>x. if P then f x else g x) = (if P then map_sq_matrix f else map_sq_matrix g)"
  
  sorry



declare [[quick_and_dirty = false, smt_oracle = false]]
theorem Cayley_Hamilton:
  fixes A :: "'a::comm_ring_1 ^^ 'n"
  shows "poly_mat (charpoly A) A = 0"
  
  