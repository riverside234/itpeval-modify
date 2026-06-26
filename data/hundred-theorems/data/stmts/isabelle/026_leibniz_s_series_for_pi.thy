section \<open>Complex Transcendental Functions\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2015)\<close>

theory Complex_Transcendental
imports
  Complex_Analysis_Basics Summation_Tests "HOL-Library.Periodic_Fun"
begin

subsection\<open>Möbius transformations\<close>

(* TODO: Figure out what to do with Möbius transformations *)
definition\<^marker>\<open>tag important\<close> "moebius a b c d \<equiv> (\<lambda>z. (a*z+b) / (c*z+d :: 'a :: field))"

theorem moebius_inverse:
  assumes "a * d \<noteq> b * c" "c * z + d \<noteq> 0"
  shows   "moebius d (-b) (-c) a (moebius a b c d z) = z"
  by sorry

lemma moebius_inverse':
  assumes "a * d \<noteq> b * c" "c * z - a \<noteq> 0"
  shows   "moebius a b c d (moebius d (-b) (-c) a z) = z"
  by sorry

lemma cmod_add_real_less:
  assumes "Im z \<noteq> 0" "r\<noteq>0"
    shows "cmod (z + r) < cmod z + \<bar>r\<bar>"
  by sorry

lemma cmod_diff_real_less: "Im z \<noteq> 0 \<Longrightarrow> x\<noteq>0 \<Longrightarrow> cmod (z - x) < cmod z + \<bar>x\<bar>"
  by sorry

lemma cmod_square_less_1_plus:
  assumes "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
    shows "(cmod z)\<^sup>2 < 1 + cmod (1 - z\<^sup>2)"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>The Exponential Function\<close>

lemma exp_npi_numeral: "exp (\<i> * pi * Num.numeral n)  = (-1) ^ Num.numeral n"
  by sorry

lemma norm_exp_i_times [simp]: "norm (exp(\<i> * of_real y)) = 1"
  by sorry

lemma norm_exp_imaginary: "norm(exp z) = 1 \<Longrightarrow> Re z = 0"
  by sorry

lemma field_differentiable_within_exp: "exp field_differentiable (at z within s)"
  by sorry

lemma continuous_within_exp:
  fixes z::"'a::{real_normed_field,banach}"
  shows "continuous (at z within s) exp"
  by sorry

lemma holomorphic_on_exp [holomorphic_intros]: "exp holomorphic_on s"
  by sorry

lemma holomorphic_on_exp' [holomorphic_intros]:
  "f holomorphic_on s \<Longrightarrow> (\<lambda>x. exp (f x)) holomorphic_on s"
  by sorry

lemma exp_analytic_on [analytic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>z. exp (f z)) analytic_on A"
  by sorry

lemma
  assumes "\<And>w. w \<in> A \<Longrightarrow> exp (f w) = w"
  assumes "f holomorphic_on A" "z \<in> A" "open A"
  shows   deriv_complex_logarithm: "deriv f z = 1 / z"
    and   has_field_derivative_complex_logarithm: "(f has_field_derivative 1 / z) (at z)"
  by sorry
  
subsection\<open>Euler and de Moivre formulas\<close>

text\<open>The sine series times \<^term>\<open>i\<close>\<close>
lemma sin_i_eq: "(\<lambda>n. (\<i> * sin_coeff n) * z^n) sums (\<i> * sin z)"
  by sorry

theorem exp_Euler: "exp(\<i> * z) = cos(z) + \<i> * sin(z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> exp_minus_Euler: "exp(-(\<i> * z)) = cos(z) - \<i> * sin(z)"
  by sorry

lemma sin_exp_eq: "sin z = (exp(\<i> * z) - exp(-(\<i> * z))) / (2*\<i>)"
  by sorry

lemma sin_exp_eq': "sin z = \<i> * (exp(-(\<i> * z)) - exp(\<i> * z)) / 2"
  by sorry

lemma cos_exp_eq:  "cos z = (exp(\<i> * z) + exp(-(\<i> * z))) / 2"
  by sorry

theorem Euler: "exp(z) = of_real(exp(Re z)) *
              (of_real(cos(Im z)) + \<i> * of_real(sin(Im z)))"
  by sorry

lemma Re_sin: "Re(sin z) = sin(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by sorry

lemma Im_sin: "Im(sin z) = cos(Re z) * (exp(Im z) - exp(-(Im z))) / 2"
  by sorry

lemma Re_cos: "Re(cos z) = cos(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by sorry

lemma Im_cos: "Im(cos z) = sin(Re z) * (exp(-(Im z)) - exp(Im z)) / 2"
  by sorry

lemma Re_sin_pos: "0 < Re z \<Longrightarrow> Re z < pi \<Longrightarrow> Re (sin z) > 0"
  by sorry

lemma Im_sin_nonneg: "Re z = 0 \<Longrightarrow> 0 \<le> Im z \<Longrightarrow> 0 \<le> Im (sin z)"
  by sorry

lemma Im_sin_nonneg2: "Re z = pi \<Longrightarrow> Im z \<le> 0 \<Longrightarrow> 0 \<le> Im (sin z)"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Relationships between real and complex trigonometric and hyperbolic functions\<close>

lemma real_sin_eq [simp]: "Re(sin(of_real x)) = sin x"
  by sorry

lemma real_cos_eq [simp]: "Re(cos(of_real x)) = cos x"
  by sorry

lemma DeMoivre: "(cos z + \<i> * sin z) ^ n = cos(n * z) + \<i> * sin(n * z)"
  by sorry

lemma exp_cnj: "cnj (exp z) = exp (cnj z)"
  by sorry

lemma cnj_sin: "cnj(sin z) = sin(cnj z)"
  by sorry

lemma cnj_cos: "cnj(cos z) = cos(cnj z)"
  by sorry

lemma field_differentiable_at_sin: "sin field_differentiable at z"
  by sorry

lemma field_differentiable_within_sin: "sin field_differentiable (at z within S)"
  by sorry

lemma field_differentiable_at_cos: "cos field_differentiable at z"
  by sorry

lemma field_differentiable_within_cos: "cos field_differentiable (at z within S)"
  by sorry

lemma holomorphic_on_sin: "sin holomorphic_on S"
  by sorry

lemma holomorphic_on_cos: "cos holomorphic_on S"
  by sorry

lemma holomorphic_on_sin' [holomorphic_intros]:
  assumes "f holomorphic_on A"
  shows   "(\<lambda>x. sin (f x)) holomorphic_on A"
  by sorry

lemma holomorphic_on_cos' [holomorphic_intros]:
  assumes "f holomorphic_on A"
  shows   "(\<lambda>x. cos (f x)) holomorphic_on A"
  by sorry

lemma analytic_on_sin [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. sin (f w)) analytic_on A"
  and analytic_on_cos [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. cos (f w)) analytic_on A"
  and analytic_on_sinh [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. sinh (f w)) analytic_on A"
  and analytic_on_cosh [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. cosh (f w)) analytic_on A"
  by sorry

lemma analytic_on_tan [analytic_intros]:
        "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> cos (f z) \<noteq> 0) \<Longrightarrow> (\<lambda>w. tan (f w)) analytic_on A"
  and analytic_on_cot [analytic_intros]:
        "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> sin (f z) \<noteq> 0) \<Longrightarrow> (\<lambda>w. cot (f w)) analytic_on A"
  and analytic_on_tanh [analytic_intros]:
        "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> cosh (f z) \<noteq> 0) \<Longrightarrow> (\<lambda>w. tanh (f w)) analytic_on A"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>More on the Polar Representation of Complex Numbers\<close>

lemma exp_Complex: "exp(Complex r t) = of_real(exp r) * Complex (cos t) (sin t)"
  by sorry

lemma exp_eq_1: "exp z = 1 \<longleftrightarrow> Re(z) = 0 \<and> (\<exists>n::int. Im(z) = of_int (2 * n) * pi)"
                 (is "?lhs = ?rhs")
  by sorry

lemma exp_eq: "exp w = exp z \<longleftrightarrow> (\<exists>n::int. w = z + (of_int (2 * n) * pi) * \<i>)"
                (is "?lhs = ?rhs")
  by sorry

lemma exp_complex_eqI: "\<bar>Im w - Im z\<bar> < 2*pi \<Longrightarrow> exp w = exp z \<Longrightarrow> w = z"
  by sorry

lemma exp_integer_2pi:
  assumes "n \<in> \<int>"
  shows "exp((2 * n * pi) * \<i>) = 1"
  by sorry

lemma exp_plus_2pin [simp]: "exp (z + \<i> * (of_int n * (of_real pi * 2))) = exp z"
  by sorry

lemma exp_2pi_1_int [simp]: "exp (\<i> * (of_int j * (of_real pi * 2))) = 1"
  by sorry

lemma exp_2pi_1_nat [simp]: "exp (\<i> * (of_nat j * (of_real pi * 2))) = 1"
  by sorry

lemma exp_integer_2pi_plus1:
  assumes "n \<in> \<int>"
  shows "exp(((2 * n + 1) * pi) * \<i>) = - 1"
  by sorry

lemma inj_on_exp_pi:
  fixes z::complex shows "inj_on exp (ball z pi)"
  by sorry

lemma cmod_add_squared:
  fixes r1 r2::real
  shows "(cmod (r1 * exp (\<i> * \<theta>1) + r2 * exp (\<i> * \<theta>2)))\<^sup>2 = r1\<^sup>2 + r2\<^sup>2 + 2 * r1 * r2 * cos (\<theta>1 - \<theta>2)" (is "(cmod (?z1 + ?z2))\<^sup>2 = ?rhs")
  by sorry

lemma cmod_diff_squared:
  fixes r1 r2::real
  shows "(cmod (r1 * exp (\<i> * \<theta>1) - r2 * exp (\<i> * \<theta>2)))\<^sup>2 = r1\<^sup>2 + r2\<^sup>2 - 2*r1*r2*cos (\<theta>1 - \<theta>2)" 
  by sorry

lemma polar_convergence:
  fixes R::real
  assumes "\<And>j. r j > 0" "R > 0"
  shows "((\<lambda>j. r j * exp (\<i> * \<theta> j)) \<longlonglongrightarrow> (R * exp (\<i> * \<Theta>))) \<longleftrightarrow>
         (r \<longlonglongrightarrow> R) \<and> (\<exists>k. (\<lambda>j. \<theta> j - of_int (k j) * (2 * pi)) \<longlonglongrightarrow> \<Theta>)"    (is "(?z \<longlonglongrightarrow> ?Z) = ?rhs")
  by sorry

lemma exp_i_ne_1:
  assumes "0 < x" "x < 2*pi"
  shows "exp(\<i> * of_real x) \<noteq> 1"
  by sorry

lemma sin_eq_0:
  fixes z::complex
  shows "sin z = 0 \<longleftrightarrow> (\<exists>n::int. z = of_real(n * pi))"
  by sorry

lemma cos_eq_0:
  fixes z::complex
  shows "cos z = 0 \<longleftrightarrow> (\<exists>n::int. z = complex_of_real(n * pi) + of_real pi/2)"
  by sorry

lemma cos_eq_1:
  fixes z::complex
  shows "cos z = 1 \<longleftrightarrow> (\<exists>n::int. z = complex_of_real(2 * n * pi))"
  by sorry

lemma csin_eq_1:
  fixes z::complex
  shows "sin z = 1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi) + of_real pi/2)"
  by sorry

lemma csin_eq_minus1:
  fixes z::complex
  shows "sin z = -1 \<longleftrightarrow> (\<exists>n::int. z = complex_of_real(2 * n * pi) + 3/2*pi)"
        (is "_ = ?rhs")
  by sorry

lemma ccos_eq_minus1:
  fixes z::complex
  shows "cos z = -1 \<longleftrightarrow> (\<exists>n::int. z = complex_of_real(2 * n * pi) + pi)"
  by sorry

lemma sin_eq_1: "sin x = 1 \<longleftrightarrow> (\<exists>n::int. x = (2 * n + 1 / 2) * pi)"
                (is "_ = ?rhs")
  by sorry

lemma sin_eq_minus1: "sin x = -1 \<longleftrightarrow> (\<exists>n::int. x = (2*n + 3/2) * pi)"  (is "_ = ?rhs")
  by sorry

lemma cos_eq_minus1: "cos x = -1 \<longleftrightarrow> (\<exists>n::int. x = (2*n + 1) * pi)"
                      (is "_ = ?rhs")
  by sorry

lemma cos_gt_neg1:
  assumes "(t::real) \<in> {-pi<..<pi}"
  shows   "cos t > -1"
  by sorry

lemma dist_exp_i_1: "norm(exp(\<i> * of_real t) - 1) = 2 * \<bar>sin(t / 2)\<bar>"
  by sorry

lemma sin_cx_2pi [simp]: "\<lbrakk>z = of_int m; even m\<rbrakk> \<Longrightarrow> sin (z * complex_of_real pi) = 0"
  by sorry

lemma cos_cx_2pi [simp]: "\<lbrakk>z = of_int m; even m\<rbrakk> \<Longrightarrow> cos (z * complex_of_real pi) = 1"
  by sorry

lemma complex_sin_eq:
  fixes w :: complex
  shows "sin w = sin z \<longleftrightarrow> (\<exists>n \<in> \<int>. w = z + of_real(2*n*pi) \<or> w = -z + of_real((2*n + 1)*pi))"
        (is "?lhs = ?rhs")
  by sorry

lemma complex_cos_eq:
  fixes w :: complex
  shows "cos w = cos z \<longleftrightarrow> (\<exists>n \<in> \<int>. w = z + of_real(2*n*pi) \<or> w = -z + of_real(2*n*pi))"
        (is "?lhs = ?rhs")
  by sorry

lemma sin_eq:
   "sin x = sin y \<longleftrightarrow> (\<exists>n \<in> \<int>. x = y + 2*n*pi \<or> x = -y + (2*n + 1)*pi)"
  by sorry

lemma cos_eq:
   "cos x = cos y \<longleftrightarrow> (\<exists>n \<in> \<int>. x = y + 2*n*pi \<or> x = -y + 2*n*pi)"
  by sorry

lemma sinh_complex:
  fixes z :: complex
  shows "(exp z - inverse (exp z)) / 2 = -\<i> * sin(\<i> * z)"
  by sorry

lemma sin_i_times:
  fixes z :: complex
  shows "sin(\<i> * z) = \<i> * ((exp z - inverse (exp z)) / 2)"
  by sorry

lemma sinh_real:
  fixes x :: real
  shows "of_real((exp x - inverse (exp x)) / 2) = -\<i> * sin(\<i> * of_real x)"
  by sorry

lemma cosh_complex:
  fixes z :: complex
  shows "(exp z + inverse (exp z)) / 2 = cos(\<i> * z)"
  by sorry

lemma cosh_real:
  fixes x :: real
  shows "of_real((exp x + inverse (exp x)) / 2) = cos(\<i> * of_real x)"
  by sorry

lemmas cos_i_times = cosh_complex [symmetric]

lemma norm_cos_squared:
  "norm(cos z) ^ 2 = cos(Re z) ^ 2 + (exp(Im z) - inverse(exp(Im z))) ^ 2 / 4"
  by sorry

lemma norm_sin_squared:
  "norm(sin z) ^ 2 = (exp(2 * Im z) + inverse(exp(2 * Im z)) - 2 * cos(2 * Re z)) / 4"
  by sorry

lemma exp_uminus_Im: "exp (- Im z) \<le> exp (cmod z)"
  by sorry

lemma norm_cos_le:
  fixes z::complex
  shows "norm(cos z) \<le> exp(norm z)"
  by sorry

lemma norm_cos_plus1_le:
  fixes z::complex
  shows "norm(1 + cos z) \<le> 2 * exp(norm z)"
  by sorry

lemma sinh_conv_sin: "sinh z = -\<i> * sin (\<i>*z)"
  by sorry

lemma cosh_conv_cos: "cosh z = cos (\<i>*z)"
  by sorry

lemma tanh_conv_tan: "tanh z = -\<i> * tan (\<i>*z)"
  by sorry

lemma sin_conv_sinh: "sin z = -\<i> * sinh (\<i>*z)"
  by sorry

lemma cos_conv_cosh: "cos z = cosh (\<i>*z)"
  by sorry

lemma tan_conv_tanh: "tan z = -\<i> * tanh (\<i>*z)"
  by sorry

lemma sinh_complex_eq_iff:
  "sinh (z :: complex) = sinh w \<longleftrightarrow>
      (\<exists>n\<in>\<int>. z = w - 2 * \<i> * of_real n * of_real pi \<or>
              z = -(2 * complex_of_real n + 1) * \<i> * complex_of_real pi - w)" (is "_ = ?rhs")
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Taylor series for complex exponential, sine and cosine\<close>

declare power_Suc [simp del]

lemma Taylor_exp_field:
  fixes z::"'a::{banach,real_normed_field}"
  shows "norm (exp z - (\<Sum>i\<le>n. z ^ i / fact i)) \<le> exp (norm z) * (norm z ^ Suc n) / fact n"
  by sorry

text \<open>For complex @{term z}, a tighter bound than in the previous result\<close>
lemma Taylor_exp:
  "norm(exp z - (\<Sum>k\<le>n. z ^ k / (fact k))) \<le> exp\<bar>Re z\<bar> * (norm z) ^ (Suc n) / (fact n)"
  by sorry

lemma
  assumes "0 \<le> u" "u \<le> 1"
  shows cmod_sin_le_exp: "cmod (sin (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>"
    and cmod_cos_le_exp: "cmod (cos (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>"
  by sorry

lemma Taylor_sin:
  "norm(sin z - (\<Sum>k\<le>n. complex_of_real (sin_coeff k) * z ^ k))
   \<le> exp\<bar>Im z\<bar> * (norm z) ^ (Suc n) / (fact n)"
  by sorry

lemma Taylor_cos:
  "norm(cos z - (\<Sum>k\<le>n. complex_of_real (cos_coeff k) * z ^ k))
   \<le> exp\<bar>Im z\<bar> * (norm z) ^ Suc n / (fact n)"
  by sorry

declare power_Suc [simp]

text\<open>32-bit Approximation to e\<close>
lemma e_approx_32: "\<bar>exp(1) - 5837465777 / 2147483648\<bar> \<le> (inverse(2 ^ 32)::real)"
  by sorry

lemma e_less_272: "exp 1 < (272/100::real)"
  by sorry

lemma ln_272_gt_1: "ln (272/100) > (1::real)"
  by sorry

text\<open>Apparently redundant. But many arguments involve integers.\<close>
lemma ln3_gt_1: "ln 3 > (1::real)"
  by sorry

subsection\<open>The argument of a complex number (HOL Light version)\<close>

definition\<^marker>\<open>tag important\<close> is_Arg :: "[complex,real] \<Rightarrow> bool"
  where "is_Arg z r \<equiv> z = of_real(norm z) * exp(\<i> * of_real r)"

definition\<^marker>\<open>tag important\<close> Arg2pi :: "complex \<Rightarrow> real"
  where "Arg2pi z \<equiv> if z = 0 then 0 else THE t. 0 \<le> t \<and> t < 2*pi \<and> is_Arg z t"

lemma is_Arg_2pi_iff: "is_Arg z (r + of_int k * (2 * pi)) \<longleftrightarrow> is_Arg z r"
  by sorry

lemma is_Arg_eqI:
  assumes "is_Arg z r" and "is_Arg z s" and "abs (r-s) < 2*pi" and "z \<noteq> 0"
  shows "r = s"
  by sorry

text\<open>This function returns the angle of a complex number from its representation in polar coordinates.
Due to periodicity, its range is arbitrary. \<^term>\<open>Arg2pi\<close> follows HOL Light in adopting the interval \<open>[0,2\<pi>)\<close>.
But we have the same periodicity issue with logarithms, and it is usual to adopt the same interval
for the complex logarithm and argument functions. Further on down, we shall define both functions for the interval \<open>(-\<pi>,\<pi>]\<close>.
The present version is provided for compatibility.\<close>

lemma Arg2pi_0 [simp]: "Arg2pi(0) = 0"
  by sorry

lemma Arg2pi_unique_lemma:
  assumes "is_Arg z t"
      and "is_Arg z t'"
      and "0 \<le> t"  "t < 2*pi"
      and "0 \<le> t'" "t' < 2*pi"
      and "z \<noteq> 0"
  shows "t' = t"
  by sorry

lemma Arg2pi: "0 \<le> Arg2pi z \<and> Arg2pi z < 2*pi \<and> is_Arg z (Arg2pi z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close>
  shows Arg2pi_ge_0: "0 \<le> Arg2pi z"
    and Arg2pi_lt_2pi: "Arg2pi z < 2*pi"
    and Arg2pi_eq: "z = of_real(norm z) * exp(\<i> * of_real(Arg2pi z))"
  by sorry

lemma complex_norm_eq_1_exp: "norm z = 1 \<longleftrightarrow> exp(\<i> * of_real (Arg2pi z)) = z"
  by sorry

lemma Arg2pi_unique: "\<lbrakk>of_real r * exp(\<i> * of_real a) = z; 0 < r; 0 \<le> a; a < 2*pi\<rbrakk> \<Longrightarrow> Arg2pi z = a"
  by sorry

lemma cos_Arg2pi: "cmod z * cos (Arg2pi z) = Re z" and sin_Arg2pi: "cmod z * sin (Arg2pi z) = Im z"
  by sorry

lemma Arg2pi_minus:
  assumes "z \<noteq> 0" shows "Arg2pi (-z) = (if Arg2pi z < pi then Arg2pi z + pi else Arg2pi z - pi)"
  by sorry

lemma Arg2pi_times_of_real [simp]:
  assumes "0 < r" shows "Arg2pi (of_real r * z) = Arg2pi z"
  by sorry

lemma Arg2pi_times_of_real2 [simp]: "0 < r \<Longrightarrow> Arg2pi (z * of_real r) = Arg2pi z"
  by sorry

lemma Arg2pi_divide_of_real [simp]: "0 < r \<Longrightarrow> Arg2pi (z / of_real r) = Arg2pi z"
  by sorry

lemma Arg2pi_le_pi: "Arg2pi z \<le> pi \<longleftrightarrow> 0 \<le> Im z"
  by sorry

lemma Arg2pi_lt_pi: "0 < Arg2pi z \<and> Arg2pi z < pi \<longleftrightarrow> 0 < Im z"
  by sorry

lemma Arg2pi_eq_0: "Arg2pi z = 0 \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re z"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Arg2pi_gt_0:
  assumes "z \<notin> \<real>\<^sub>\<ge>\<^sub>0"
    shows "Arg2pi z > 0"
  by sorry

lemma Arg2pi_eq_pi: "Arg2pi z = pi \<longleftrightarrow> z \<in> \<real> \<and> Re z < 0"
  by sorry

lemma Arg2pi_eq_0_pi: "Arg2pi z = 0 \<or> Arg2pi z = pi \<longleftrightarrow> z \<in> \<real>"
  by sorry

lemma Arg2pi_of_real: "Arg2pi (of_real r) = (if r<0 then pi else 0)"
  by sorry

lemma Arg2pi_real: "z \<in> \<real> \<Longrightarrow> Arg2pi z = (if 0 \<le> Re z then 0 else pi)"
  by sorry

lemma Arg2pi_inverse: "Arg2pi(inverse z) = (if z \<in> \<real> then Arg2pi z else 2*pi - Arg2pi z)"
  by sorry

lemma Arg2pi_eq_iff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
  shows "Arg2pi w = Arg2pi z \<longleftrightarrow> (\<exists>x. 0 < x \<and> w = of_real x * z)" (is "?lhs = ?rhs")
  by sorry

lemma Arg2pi_inverse_eq_0: "Arg2pi(inverse z) = 0 \<longleftrightarrow> Arg2pi z = 0"
  by sorry

lemma Arg2pi_divide:
  assumes "w \<noteq> 0" "z \<noteq> 0" "Arg2pi w \<le> Arg2pi z"
    shows "Arg2pi(z / w) = Arg2pi z - Arg2pi w"
  by sorry

lemma Arg2pi_le_div_sum:
  assumes "w \<noteq> 0" "z \<noteq> 0" "Arg2pi w \<le> Arg2pi z"
    shows "Arg2pi z = Arg2pi w + Arg2pi(z / w)"
  by sorry

lemma Arg2pi_le_div_sum_eq:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi w \<le> Arg2pi z \<longleftrightarrow> Arg2pi z = Arg2pi w + Arg2pi(z / w)"
  by sorry

lemma Arg2pi_diff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi w - Arg2pi z = (if Arg2pi z \<le> Arg2pi w then Arg2pi(w / z) else Arg2pi(w/z) - 2*pi)"
  by sorry

lemma Arg2pi_add:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi w + Arg2pi z = (if Arg2pi w + Arg2pi z < 2*pi then Arg2pi(w * z) else Arg2pi(w * z) + 2*pi)"
  by sorry

lemma Arg2pi_times:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg2pi (w * z) = (if Arg2pi w + Arg2pi z < 2*pi then Arg2pi w + Arg2pi z
                            else (Arg2pi w + Arg2pi z) - 2*pi)"
  by sorry

lemma Arg2pi_cnj_eq_inverse:
  assumes "z \<noteq> 0" shows "Arg2pi (cnj z) = Arg2pi (inverse z)"
  by sorry

lemma Arg2pi_cnj: "Arg2pi(cnj z) = (if z \<in> \<real> then Arg2pi z else 2*pi - Arg2pi z)"
  by sorry

lemma Arg2pi_exp: "0 \<le> Im z \<Longrightarrow> Im z < 2*pi \<Longrightarrow> Arg2pi(exp z) = Im z"
  by sorry

lemma complex_split_polar:
  obtains r a::real where "z = complex_of_real r * (cos a + \<i> * sin a)" "0 \<le> r" "0 \<le> a" "a < 2*pi"
  by sorry

lemma Re_Im_le_cmod: "Im w * sin \<phi> + Re w * cos \<phi> \<le> cmod w"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Analytic properties of tangent function\<close>

lemma cnj_tan: "cnj(tan z) = tan(cnj z)"
  by sorry

lemma field_differentiable_at_tan: "cos z \<noteq> 0 \<Longrightarrow> tan field_differentiable at z"
  by sorry

lemma field_differentiable_within_tan: "cos z \<noteq> 0
         \<Longrightarrow> tan field_differentiable (at z within s)"
  by sorry

lemma continuous_within_tan: "cos z \<noteq> 0 \<Longrightarrow> continuous (at z within s) tan"
  by sorry

lemma continuous_on_tan [continuous_intros]: "(\<And>z. z \<in> s \<Longrightarrow> cos z \<noteq> 0) \<Longrightarrow> continuous_on s tan"
  by sorry

lemma holomorphic_on_tan: "(\<And>z. z \<in> s \<Longrightarrow> cos z \<noteq> 0) \<Longrightarrow> tan holomorphic_on s"
  by sorry


subsection\<open>The principal branch of the Complex logarithm\<close>

instantiation complex :: ln
begin

definition\<^marker>\<open>tag important\<close> ln_complex :: "complex \<Rightarrow> complex"
  where "ln_complex \<equiv> \<lambda>z. THE w. exp w = z & -pi < Im(w) & Im(w) \<le> pi"

text\<open>NOTE: within this scope, the constant Ln is not yet available!\<close>
lemma
  assumes "z \<noteq> 0"
    shows exp_Ln [simp]:  "exp(ln z) = z"
      and mpi_less_Im_Ln: "-pi < Im(ln z)"
      and Im_Ln_le_pi:    "Im(ln z) \<le> pi"
  by sorry

lemma Ln_exp [simp]:
  assumes "-pi < Im(z)" "Im(z) \<le> pi"
    shows "ln(exp z) = z"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Relation to Real Logarithm\<close>

lemma Ln_of_real:
  assumes "0 < z"
    shows "ln(of_real z::complex) = of_real(ln z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Ln_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> Re z > 0 \<Longrightarrow> ln z \<in> \<real>"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Im_Ln_of_real [simp]: "r > 0 \<Longrightarrow> Im (ln (of_real r)) = 0"
  by sorry

lemma cmod_Ln_Reals [simp]: "z \<in> \<real> \<Longrightarrow> 0 < Re z \<Longrightarrow> cmod (ln z) = norm (ln (Re z))"
  by sorry

lemma Ln_Reals_eq: "\<lbrakk>x \<in> \<real>; Re x > 0\<rbrakk> \<Longrightarrow> ln x = of_real (ln (Re x))"
  by sorry

lemma Ln_1 [simp]: "ln 1 = (0::complex)"
  by sorry

lemma Ln_eq_zero_iff [simp]: "x \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> ln x = 0 \<longleftrightarrow> x = 1" for x::complex
  by sorry

instance
  by intro_classes (rule ln_complex_def Ln_1)

end

abbreviation Ln :: "complex \<Rightarrow> complex"
  where "Ln \<equiv> ln"

lemma Ln_eq_iff: "w \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> (Ln w = Ln z \<longleftrightarrow> w = z)"
  by sorry

lemma Ln_unique: "exp(z) = w \<Longrightarrow> -pi < Im(z) \<Longrightarrow> Im(z) \<le> pi \<Longrightarrow> Ln w = z"
  by sorry

lemma Re_Ln [simp]: "z \<noteq> 0 \<Longrightarrow> Re(Ln z) = ln(norm z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> ln_cmod_le:
  assumes z: "z \<noteq> 0"
    shows "ln (cmod z) \<le> cmod (Ln z)"
  by sorry

proposition\<^marker>\<open>tag unimportant\<close> exists_complex_root:
  fixes z :: complex
  assumes "n \<noteq> 0"  obtains w where "z = w ^ n"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> exists_complex_root_nonzero:
  fixes z::complex
  assumes "z \<noteq> 0" "n \<noteq> 0"
  obtains w where "w \<noteq> 0" "z = w ^ n"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Derivative of Ln away from the branch cut\<close>

lemma Im_Ln_less_pi: 
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"shows "Im (Ln z) < pi"
  by sorry

lemma has_field_derivative_Ln: 
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows "(Ln has_field_derivative inverse(z)) (at z)"
  by sorry

declare has_field_derivative_Ln [derivative_intros]
declare has_field_derivative_Ln [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Ln field_differentiable at z"
  by sorry

lemma field_differentiable_within_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0
         \<Longrightarrow> Ln field_differentiable (at z within S)"
  by sorry

lemma continuous_at_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z) Ln"
  by sorry

lemma isCont_Ln' [simp,continuous_intros]:
   "\<lbrakk>isCont f z; f z \<notin> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. Ln (f x)) z"
  by sorry

lemma continuous_within_Ln [continuous_intros]: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within S) Ln"
  by sorry

lemma continuous_on_Ln [continuous_intros]: "(\<And>z. z \<in> S \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> continuous_on S Ln"
  by sorry

lemma continuous_on_Ln' [continuous_intros]:
  "continuous_on S f \<Longrightarrow> (\<And>z. z \<in> S \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> continuous_on S (\<lambda>x. Ln (f x))"
  by sorry

lemma holomorphic_on_Ln [holomorphic_intros]: "S \<inter> \<real>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> Ln holomorphic_on S"
  by sorry

lemma holomorphic_on_Ln' [holomorphic_intros]:
  "(\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> f holomorphic_on A \<Longrightarrow> (\<lambda>z. Ln (f z)) holomorphic_on A"
  by sorry

lemma analytic_on_ln [analytic_intros]:
  assumes "f analytic_on A" "f ` A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {}"
  shows   "(\<lambda>w. ln (f w)) analytic_on A"
  by sorry

lemma tendsto_Ln [tendsto_intros]:
  assumes "(f \<longlongrightarrow> L) F" "L \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Ln (f x)) \<longlongrightarrow> Ln L) F"
  by sorry

lemma divide_ln_mono:
  fixes x y::real
  assumes "3 \<le> x" "x \<le> y"
  shows "x / ln x \<le> y / ln y"
  by sorry

theorem Ln_series:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "(\<lambda>n. (-1)^Suc n / of_nat n * z^n) sums ln (1 + z)" (is "(\<lambda>n. ?f n * z^n) sums _")
  by sorry

lemma Ln_series': "cmod z < 1 \<Longrightarrow> (\<lambda>n. - ((-z)^n) / of_nat n) sums ln (1 + z)"
  by sorry

lemma ln_series':
  fixes x::real
  assumes "\<bar>x\<bar> < 1"
  shows   "(\<lambda>n. - ((-x)^n) / of_nat n) sums ln (1 + x)"
  by sorry

lemma Ln_approx_linear:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "norm (ln (1 + z) - z) \<le> norm z^2 / (1 - norm z)"
  by sorry


lemma norm_Ln_le:
  fixes z :: complex
  assumes "norm z < 1/2"
  shows   "norm (Ln(1+z)) \<le> 2 * norm z"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Quadrant-type results for Ln\<close>

lemma cos_lt_zero_pi: "pi/2 < x \<Longrightarrow> x < 3*pi/2 \<Longrightarrow> cos x < 0"
  by sorry

lemma Re_Ln_pos_le:
  assumes "z \<noteq> 0"
  shows "\<bar>Im(Ln z)\<bar> \<le> pi/2 \<longleftrightarrow> 0 \<le> Re(z)"
  by sorry

lemma Re_Ln_pos_lt:
  assumes "z \<noteq> 0"
  shows "\<bar>Im(Ln z)\<bar> < pi/2 \<longleftrightarrow> 0 < Re(z)"
  by sorry

lemma Im_Ln_pos_le:
  assumes "z \<noteq> 0"
  shows "0 \<le> Im(Ln z) \<and> Im(Ln z) \<le> pi \<longleftrightarrow> 0 \<le> Im(z)"
  by sorry

lemma Im_Ln_pos_lt:
  assumes "z \<noteq> 0"
  shows "0 < Im(Ln z) \<and> Im(Ln z) < pi \<longleftrightarrow> 0 < Im(z)"
  by sorry

lemma Re_Ln_pos_lt_imp: "0 < Re(z) \<Longrightarrow> \<bar>Im(Ln z)\<bar> < pi/2"
  by sorry

lemma Im_Ln_pos_lt_imp: "0 < Im(z) \<Longrightarrow> 0 < Im(Ln z) \<and> Im(Ln z) < pi"
  by sorry

text\<open>A reference to the set of positive real numbers\<close>
lemma Im_Ln_eq_0: "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = 0 \<longleftrightarrow> 0 < Re(z) \<and> Im(z) = 0)"
  by sorry

lemma Im_Ln_eq_pi: "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = pi \<longleftrightarrow> Re(z) < 0 \<and> Im(z) = 0)"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>More Properties of Ln\<close>

lemma cnj_Ln: assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0" shows "cnj(Ln z) = Ln(cnj z)"
  by sorry


lemma Ln_inverse: assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0" shows "Ln(inverse z) = -(Ln z)"
  by sorry

lemma Ln_minus1 [simp]: "Ln(-1) = \<i> * pi"
  by sorry

lemma Ln_ii [simp]: "Ln \<i> = \<i> * of_real pi/2"
  by sorry

lemma Ln_minus_ii [simp]: "Ln(-\<i>) = - (\<i> * pi/2)"
  by sorry

lemma Ln_times:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Ln(w * z) =
           (if Im(Ln w + Ln z) \<le> -pi then (Ln(w) + Ln(z)) + \<i> * of_real(2*pi)
            else if Im(Ln w + Ln z) > pi then (Ln(w) + Ln(z)) - \<i> * of_real(2*pi)
            else Ln(w) + Ln(z))"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Ln_times_simple:
    "\<lbrakk>w \<noteq> 0; z \<noteq> 0; -pi < Im(Ln w) + Im(Ln z); Im(Ln w) + Im(Ln z) \<le> pi\<rbrakk>
         \<Longrightarrow> Ln(w * z) = Ln(w) + Ln(z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Ln_times_of_real:
    "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(of_real r * z) = ln r + Ln(z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Ln_times_of_nat:
    "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(of_nat r * z :: complex) = ln (of_nat r) + Ln(z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Ln_times_Reals:
    "\<lbrakk>r \<in> Reals; Re r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(r * z) = ln (Re r) + Ln(z)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Ln_divide_of_real:
  "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(z / of_real r) = Ln(z) - ln r"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Ln_prod:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows "\<exists>n. Ln (prod f A) = (\<Sum>x \<in> A. Ln (f x) + (of_int (n x) * (2 * pi)) * \<i>)"
  by sorry

lemma Ln_minus:
  assumes "z \<noteq> 0"
    shows "Ln(-z) = (if Im(z) \<le> 0 \<and> \<not>(Re(z) < 0 \<and> Im(z) = 0)
                     then Ln(z) + \<i> * pi
                     else Ln(z) - \<i> * pi)" 
  by sorry

lemma Ln_inverse_if:
  assumes "z \<noteq> 0"
    shows "Ln (inverse z) = (if z \<in> \<real>\<^sub>\<le>\<^sub>0 then -(Ln z) + \<i> * 2 * complex_of_real pi else -(Ln z))"
  by sorry

lemma Ln_times_ii:
  assumes "z \<noteq> 0"
    shows  "Ln(\<i> * z) = (if 0 \<le> Re(z) | Im(z) < 0
                          then Ln(z) + \<i> * of_real pi/2
                          else Ln(z) - \<i> * of_real(3 * pi/2))"
  by sorry

lemma Ln_of_nat [simp]: "0 < n \<Longrightarrow> Ln (of_nat n) = of_real (ln (of_nat n))"
  by sorry

lemma Ln_of_nat_over_of_nat:
  assumes "m > 0" "n > 0"
  shows   "Ln (of_nat m / of_nat n) = of_real (ln (of_nat m) - ln (of_nat n))"
  by sorry

lemma norm_Ln_times_le:
  assumes "w \<noteq> 0" "z \<noteq> 0"
  shows  "cmod (Ln(w * z)) \<le> cmod (Ln(w) + Ln(z))"
  by sorry

corollary norm_Ln_prod_le:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows "cmod (Ln (prod f A)) \<le> (\<Sum>x \<in> A. cmod (Ln (f x)))"
  by sorry

lemma norm_Ln_exp_le: "norm (Ln (exp z)) \<le> norm z"
  by sorry

lemma Ln_cis: "x \<in> {-pi<..pi} \<Longrightarrow> Ln (cis x) = x * \<i>"
  by sorry

lemma Ln_rcis:
  assumes "r > 0" "x \<in> {-pi<..pi}"
  shows   "Ln (rcis r x) = Complex (ln r) x"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Uniform convergence and products\<close>

(* TODO: could be generalised perhaps, but then one would have to do without the ln *)
lemma uniformly_convergent_on_prod_aux:
  fixes f :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes norm_f: "\<And>n x. x \<in> A \<Longrightarrow> norm (f n x) < 1"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes conv: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. ln (1 + f n x))"
  assumes A: "compact A"
  shows "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + f n x)"
  by sorry

text \<open>Theorem 17.6 by Bak and Newman, Complex Analysis [roughly]\<close>
lemma uniformly_convergent_on_prod:
  fixes f :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes A: "compact A"
  assumes conv_sum: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. norm (f n x))"
  shows   "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + f n x)"
  by sorry

lemma uniformly_convergent_on_prod':
  fixes f :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes A: "compact A"
  assumes conv_sum: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. norm (f n x - 1))"
  shows "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. f n x)"
  by sorry

text\<open>Prop 17.6 of Bak and Newman, Complex Analysis, p. 243. 
     Only this version is for the reals. Can the two proofs be consolidated?\<close>
lemma uniformly_convergent_on_prod_real:
  fixes u :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes contu: "\<And>k. continuous_on K (u k)" 
     and uconv: "uniformly_convergent_on K (\<lambda>n x. \<Sum>k<n. \<bar>u k x\<bar>)"
     and K: "compact K"
   shows "uniformly_convergent_on K (\<lambda>n x. \<Prod>k<n. 1 + u k x)"
  by sorry


subsection\<open>The Argument of a Complex Number\<close>

text\<open>Unlike in HOL Light, it's defined for the same interval as the complex logarithm: \<open>(-\<pi>,\<pi>]\<close>.\<close>

lemma Arg_eq_Im_Ln:
  assumes "z \<noteq> 0" shows "Arg z = Im (Ln z)"
  by sorry

text \<open>The 1990s definition of argument coincides with the more recent one\<close>
lemma\<^marker>\<open>tag important\<close> Arg_def:
  shows "Arg z = (if z = 0 then 0 else Im (Ln z))"
  by sorry

lemma Arg_of_real [simp]: "Arg (of_real r) = (if r<0 then pi else 0)"
  by sorry

lemma mpi_less_Arg: "-pi < Arg z" and Arg_le_pi: "Arg z \<le> pi"
  by sorry

lemma Arg_eq: 
  assumes "z \<noteq> 0"
  shows "z = of_real(norm z) * exp(\<i> * Arg z)"
  by sorry

lemma is_Arg_Arg: "z \<noteq> 0 \<Longrightarrow> is_Arg z (Arg z)"
  by sorry

lemma Argument_exists:
  assumes "z \<noteq> 0" and R: "R = {r-pi<..r+pi}"
  obtains s where "is_Arg z s" "s\<in>R"
  by sorry

lemma Argument_exists_unique:
  assumes "z \<noteq> 0" and R: "R = {r-pi<..r+pi}"
  obtains s where "is_Arg z s" "s\<in>R" "\<And>t. \<lbrakk>is_Arg z t; t\<in>R\<rbrakk> \<Longrightarrow> s=t"
  by sorry

lemma Argument_Ex1:
  assumes "z \<noteq> 0" and R: "R = {r-pi<..r+pi}"
  shows "\<exists>!s. is_Arg z s \<and> s \<in> R"
  by sorry

lemma Arg_divide:
  assumes "w \<noteq> 0" "z \<noteq> 0"
  shows "is_Arg (z / w) (Arg z - Arg w)"
  by sorry

lemma Arg_unique_lemma:
  assumes "is_Arg z t" "is_Arg z t'"
      and "- pi < t"  "t \<le> pi"
      and "- pi < t'" "t' \<le> pi"
      and "z \<noteq> 0"
    shows "t' = t"
  by sorry

lemma complex_norm_eq_1_exp_eq: "norm z = 1 \<longleftrightarrow> exp(\<i> * (Arg z)) = z"
  by sorry

lemma Arg_unique: "\<lbrakk>of_real r * exp(\<i> * a) = z; 0 < r; -pi < a; a \<le> pi\<rbrakk> \<Longrightarrow> Arg z = a"
  by sorry

lemma Arg_minus:
  assumes "z \<noteq> 0"
  shows "Arg (-z) = (if Arg z \<le> 0 then Arg z + pi else Arg z - pi)"
  by sorry

lemma Arg_1 [simp]: "Arg 1 = 0"
  by sorry

lemma Arg_numeral [simp]: "Arg (numeral n) = 0"
  by sorry
  
lemma Arg_times_of_real [simp]:
  assumes "0 < r" shows "Arg (of_real r * z) = Arg z"
  by sorry

lemma Arg_times_of_real2 [simp]: "0 < r \<Longrightarrow> Arg (z * of_real r) = Arg z"
  by sorry

lemma Arg_divide_of_real [simp]: "0 < r \<Longrightarrow> Arg (z / of_real r) = Arg z"
  by sorry

lemma Arg_less_0: "0 \<le> Arg z \<longleftrightarrow> 0 \<le> Im z"
  by sorry

text \<open>converse fails because the argument can equal $\pi$.\<close> 
lemma Arg_uminus: "Arg z < 0 \<Longrightarrow> Arg (-z) > 0"
  by sorry

lemma Arg_eq_pi: "Arg z = pi \<longleftrightarrow> Re z < 0 \<and> Im z = 0"
  by sorry

lemma Arg_lt_pi: "0 < Arg z \<and> Arg z < pi \<longleftrightarrow> 0 < Im z"
  by sorry

lemma Arg_eq_0: "Arg z = 0 \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re z"
  by sorry

lemma Arg_neg_iff: "Arg x < 0 \<longleftrightarrow> Im x < 0"
  by sorry

lemma Arg_pos_iff: "Arg x > 0 \<longleftrightarrow> Im x > 0 \<or> (Im x = 0 \<and> Re x < 0)"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Arg_ne_0: assumes "z \<notin> \<real>\<^sub>\<ge>\<^sub>0" shows "Arg z \<noteq> 0"
  by sorry

lemma Arg_eq_pi_iff: "Arg z = pi \<longleftrightarrow> z \<in> \<real> \<and> Re z < 0"
  by sorry

lemma Arg_eq_0_iff: "Arg z = 0 \<longleftrightarrow> z \<in> \<real> \<and> Re z \<ge> 0"
  by sorry

lemma Arg_eq_0_pi: "Arg z = 0 \<or> Arg z = pi \<longleftrightarrow> z \<in> \<real>"
  by sorry

lemma Arg_real: "z \<in> \<real> \<Longrightarrow> Arg z = (if 0 \<le> Re z then 0 else pi)"
  by sorry

lemma Arg_inverse: "Arg(inverse z) = (if z \<in> \<real> then Arg z else - Arg z)"
  by sorry

lemma Arg_eq_iff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
  shows "Arg w = Arg z \<longleftrightarrow> (\<exists>x. 0 < x \<and> w = of_real x * z)" (is "?lhs = ?rhs")
  by sorry

lemma Arg_inverse_eq_0: "Arg(inverse z) = 0 \<longleftrightarrow> Arg z = 0"
  by sorry

lemma Arg_cnj_eq_inverse: "z\<noteq>0 \<Longrightarrow> Arg (cnj z) = Arg (inverse z)"
  by sorry

lemma Arg_cnj: "Arg(cnj z) = (if z \<in> \<real> then Arg z else - Arg z)"
  by sorry

lemma Arg_exp: "-pi < Im z \<Longrightarrow> Im z \<le> pi \<Longrightarrow> Arg(exp z) = Im z"
  by sorry

lemma Arg_cis: "x \<in> {-pi<..pi} \<Longrightarrow> Arg (cis x) = x"
  by sorry

lemma Arg_rcis: "x \<in> {-pi<..pi} \<Longrightarrow> r > 0 \<Longrightarrow> Arg (rcis r x) = x"
  by sorry

lemma Ln_Arg: "z\<noteq>0 \<Longrightarrow> Ln(z) = ln(norm z) + \<i> * Arg(z)"
  by sorry

lemma Ln_of_real':
  assumes "x \<noteq> 0"
  shows   "Ln (of_real x) = of_real (ln \<bar>x\<bar>) + (if x < 0 then pi else 0) * \<i>"
  by sorry

lemma continuous_at_Arg:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "continuous (at z) Arg"
  by sorry

lemma continuous_within_Arg: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within S) Arg"
  by sorry


lemma continuous_on_Arg: "continuous_on (-\<real>\<^sub>\<le>\<^sub>0) Arg"
  by sorry

lemma continuous_on_Arg' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "continuous_on A (\<lambda>x. Arg (f x))"
  by sorry

lemma tendsto_Arg [tendsto_intros]:
  assumes "(f \<longlongrightarrow> z) F" "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Arg (f x)) \<longlongrightarrow> Arg z) F"
  by sorry

lemma Arg_Re_pos: "\<bar>Arg z\<bar> < pi / 2 \<longleftrightarrow> Re z > 0 \<or> z = 0"
  by sorry

lemma Arg_Re_nonneg: "\<bar>Arg z\<bar> \<le> pi / 2 \<longleftrightarrow> Re z \<ge> 0"
  by sorry

lemma Arg_times:
  assumes "Arg z + Arg w \<in> {-pi<..pi}" "z \<noteq> 0" "w \<noteq> 0"
  shows   "Arg (z * w) = Arg z + Arg w"
  by sorry

lemma Arg_unique': "r > 0 \<Longrightarrow> \<phi> \<in> {-pi<..pi} \<Longrightarrow> x = rcis r \<phi> \<Longrightarrow> Arg x = \<phi>"
  by sorry

lemma Arg_times':
  assumes "w \<noteq> 0" "z \<noteq> 0"
  defines "x \<equiv> Arg w + Arg z"
  shows   "Arg (w * z) = x + (if x \<in> {-pi<..pi} then 0 else if x > pi then -2*pi else 2*pi)"
  by sorry

lemma Arg_divide':
  assumes [simp]: "z \<noteq> 0" "w \<noteq> 0"
  shows   "Arg (z / w) = Arg z - Arg w +
             (if Arg z - Arg w > pi then -2 * pi else if Arg z - Arg w \<le> -pi then 2 * pi else 0)"
    (is "_ = ?rhs")
  by sorry
  
subsection\<open>The Unwinding Number and the Ln product Formula\<close>

text\<open>Note that in this special case the unwinding number is -1, 0 or 1. But it's always an integer.\<close>

lemma is_Arg_exp_Im: "is_Arg (exp z) (Im z)"
  by sorry

lemma is_Arg_exp_diff_2pi:
  assumes "is_Arg (exp z) \<theta>"
  shows "\<exists>k. Im z - of_int k * (2 * pi) = \<theta>"
  by sorry

lemma Arg_exp_diff_2pi: "\<exists>k. Im z - of_int k * (2 * pi) = Arg (exp z)"
  by sorry

lemma unwinding_in_Ints: "(z - Ln(exp z)) / (of_real(2*pi) * \<i>) \<in> \<int>"
  by sorry

definition\<^marker>\<open>tag important\<close> unwinding :: "complex \<Rightarrow> int" where
   "unwinding z \<equiv> THE k. of_int k = (z - Ln(exp z)) / (of_real(2*pi) * \<i>)"

lemma unwinding: "of_int (unwinding z) = (z - Ln(exp z)) / (of_real(2*pi) * \<i>)"
  by sorry

lemma unwinding_2pi: "(2*pi) * \<i> * unwinding(z) = z - Ln(exp z)"
  by sorry

lemma Ln_times_unwinding:
    "w \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> Ln(w * z) = Ln(w) + Ln(z) - (2*pi) * \<i> * unwinding(Ln w + Ln z)"
  by sorry


lemma arg_conv_arctan:
  assumes "Re z > 0"
  shows   "Arg z = arctan (Im z / Re z)"
  by sorry


subsection \<open>Characterisation of @{term "Im (Ln z)"} (Wenda Li)\<close>

lemma Im_Ln_eq_pi_half:
    "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = pi/2 \<longleftrightarrow> 0 < Im(z) \<and> Re(z) = 0)"
    "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = -pi/2 \<longleftrightarrow> Im(z) < 0 \<and> Re(z) = 0)"
  by sorry

lemma Im_Ln_eq:
  assumes "z\<noteq>0"
  shows "Im (Ln z) = (if Re z\<noteq>0 then
                        if Re z>0 then
                           arctan (Im z/Re z)
                        else if Im z\<ge>0 then
                           arctan (Im z/Re z) + pi
                        else
                           arctan (Im z/Re z) - pi
                      else
                        if Im z>0 then pi/2 else -pi/2)"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Relation between Ln and Arg2pi, and hence continuity of Arg2pi\<close>

lemma Arg2pi_Ln: "0 < Arg2pi z \<Longrightarrow> Arg2pi z = Im(Ln(-z)) + pi"
  by sorry

lemma continuous_at_Arg2pi:
  assumes "z \<notin> \<real>\<^sub>\<ge>\<^sub>0"
    shows "continuous (at z) Arg2pi"
  by sorry


text\<open>Relation between Arg2pi and arctangent in upper halfplane\<close>
lemma Arg2pi_arctan_upperhalf:
  assumes "0 < Im z"
    shows "Arg2pi z = pi/2 - arctan(Re z / Im z)"
  by sorry

lemma Arg2pi_eq_Im_Ln:
  assumes "0 \<le> Im z" "0 < Re z"
    shows "Arg2pi z = Im (Ln z)"
  by sorry

lemma continuous_within_upperhalf_Arg2pi:
  assumes "z \<noteq> 0"
    shows "continuous (at z within {z. 0 \<le> Im z}) Arg2pi"
  by sorry

lemma continuous_on_upperhalf_Arg2pi: "continuous_on ({z. 0 \<le> Im z} - {0}) Arg2pi"
  by sorry

lemma open_Arg2pi2pi_less_Int:
  assumes "0 \<le> s" "t \<le> 2*pi"
    shows "open ({y. s < Arg2pi y} \<inter> {y. Arg2pi y < t})"
  by sorry

lemma open_Arg2pi2pi_gt: "open {z. t < Arg2pi z}"
  by sorry

lemma closed_Arg2pi2pi_le: "closed {z. Arg2pi z \<le> t}"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Complex Powers\<close>

lemma powr_to_1 [simp]: "z powr 1 = (z::complex)"
  by sorry

lemma powr_nat:
  fixes n::nat and z::complex shows "z powr n = (if z = 0 then 0 else z^n)"
  by sorry

lemma powr_nat': "(z :: complex) \<noteq> 0 \<or> n \<noteq> 0 \<Longrightarrow> z powr of_nat n = z ^ n"
  by sorry

lemma norm_powr_complex: "norm (x powr y) = norm x powr Re y * exp (-Im y * Arg x)"
  by sorry

lemma norm_powr_real: "w \<in> \<real> \<Longrightarrow> 0 < Re w \<Longrightarrow> norm(w powr z) = exp(Re z * ln(Re w))"
  by sorry

lemma norm_powr_real_powr:
  "w \<in> \<real> \<Longrightarrow> 0 \<le> Re w \<Longrightarrow> cmod (w powr z) = Re w powr Re z"
  by sorry

lemma norm_powr_real_powr': "w \<in> \<real> \<Longrightarrow> norm (z powr w) = norm z powr Re w"
  by sorry

lemma powr_complexpow [simp]:
  fixes x::complex shows "x \<noteq> 0 \<Longrightarrow> x powr (of_nat n) = x^n"
  by sorry

lemma powr_complexnumeral [simp]:
  fixes x::complex shows "x powr (numeral n) = x ^ (numeral n)"
  by sorry

lemma powr_times_real_left:
  assumes "x \<in> \<real>" "Re x \<ge> 0"
  shows   "(x * y) powr z = x powr z * y powr z"
  by sorry

lemma cnj_powr:
  assumes "Im a = 0 \<Longrightarrow> Re a \<ge> 0"
  shows   "cnj (a powr b) = cnj a powr cnj b"
  by sorry

lemma powr_real_real:
  assumes "w \<in> \<real>" "z \<in> \<real>" "0 < Re w"
  shows "w powr z = exp(Re z * ln(Re w))"
  by sorry

lemma powr_of_real:
  fixes x::real and y::real
  shows "0 \<le> x \<Longrightarrow> of_real x powr (of_real y::complex) = of_real (x powr y)"
  by sorry

lemma powr_of_int:
  fixes z::complex and n::int
  assumes "z\<noteq>(0::complex)"
  shows "z powr of_int n = (if n\<ge>0 then z^nat n else inverse (z^nat (-n)))"
  by sorry

lemma complex_powr_of_int: "z \<noteq> 0 \<or> n \<noteq> 0 \<Longrightarrow> z powr of_int n = (z :: complex) powi n"
  by sorry

lemma powr_of_neg_real:
  fixes x::real and y::real
  assumes "x<0"
  shows "(complex_of_real x) powr (complex_of_real y) = of_real (\<bar>x\<bar> powr y) * exp (\<i> * pi * y)"
  by sorry

lemma powr_of_real_if:
  fixes x::real and y::real
  shows "complex_of_real x powr (complex_of_real y) = 
           (if x<0 then of_real (\<bar>x\<bar> powr y) * exp (\<i> * pi * y) else of_real (x powr y))"
  by sorry

lemma powr_Reals_eq: "\<lbrakk>x \<in> \<real>; y \<in> \<real>; Re x \<ge> 0\<rbrakk> \<Longrightarrow> x powr y = of_real (Re x powr Re y)"
  by sorry

lemma norm_powr_real_mono:
    "\<lbrakk>w \<in> \<real>; 1 < Re w\<rbrakk> \<Longrightarrow> cmod(w powr z1) \<le> cmod(w powr z2) \<longleftrightarrow> Re z1 \<le> Re z2"
  by sorry

lemma powr_times_real:
    "\<lbrakk>x \<in> \<real>; y \<in> \<real>; 0 \<le> Re x; 0 \<le> Re y\<rbrakk> \<Longrightarrow> (x * y) powr z = x powr z * y powr z"
  by sorry

lemma Re_powr_le: "r \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> Re (r powr z) \<le> Re r powr Re z"
  by sorry

lemma
  fixes w::complex
  assumes "w \<in> \<real>\<^sub>\<ge>\<^sub>0" "z \<in> \<real>"
  shows Reals_powr [simp]: "w powr z \<in> \<real>" and nonneg_Reals_powr [simp]: "w powr z \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by sorry

lemma exp_powr_complex:
  fixes x::complex 
  assumes "-pi < Im(x)" "Im(x) \<le> pi"
  shows "exp x powr y = exp (x*y)"
  by sorry

lemma powr_neg_real_complex:
  fixes w::complex
  shows "(- of_real x) powr w = (-1) powr (of_real (sgn x) * w) * of_real x powr w"
  by sorry

lemma has_field_derivative_powr:
  fixes z :: complex
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows "((\<lambda>z. z powr s) has_field_derivative (s * z powr (s - 1))) (at z)"
  by sorry

declare has_field_derivative_powr[THEN DERIV_chain2, derivative_intros]

(*Seemingly impossible to use DERIV_power_int without introducing the assumption z\<in>S*)
lemma has_field_derivative_powr_of_int:
  fixes z :: complex
  assumes gderiv: "(g has_field_derivative gd) (at z within S)" and "g z \<noteq> 0"
  shows "((\<lambda>z. g z powr of_int n) has_field_derivative (n * g z powr (of_int n - 1) * gd)) (at z within S)"
  by sorry

lemma field_differentiable_powr_of_int:
  fixes z :: complex
  assumes "g field_differentiable (at z within S)" and "g z \<noteq> 0"
  shows "(\<lambda>z. g z powr of_int n) field_differentiable (at z within S)"
  by sorry

lemma holomorphic_on_powr_of_int [holomorphic_intros]:
  assumes "f holomorphic_on S" and "\<And>z. z\<in>S \<Longrightarrow> f z \<noteq> 0"
  shows "(\<lambda>z. (f z) powr of_int n) holomorphic_on S"
  by sorry

lemma has_field_derivative_powr_right [derivative_intros]:
    "w \<noteq> 0 \<Longrightarrow> ((\<lambda>z. w powr z) has_field_derivative Ln w * w powr z) (at z)"
  by sorry

lemma field_differentiable_powr_right [derivative_intros]:
  fixes w::complex
  shows "w \<noteq> 0 \<Longrightarrow> (\<lambda>z. w powr z) field_differentiable (at z)"
  by sorry

lemma holomorphic_on_powr_right [holomorphic_intros]:
  assumes "f holomorphic_on S"
  shows "(\<lambda>z. w powr (f z)) holomorphic_on S"
  by sorry

lemma holomorphic_on_divide_gen [holomorphic_intros]:
  assumes "f holomorphic_on S" "g holomorphic_on S" and "\<And>z z'. \<lbrakk>z \<in> S; z' \<in> S\<rbrakk> \<Longrightarrow> g z = 0 \<longleftrightarrow> g z' = 0"
  shows "(\<lambda>z. f z / g z) holomorphic_on S"
  by sorry

lemma tendsto_powr_complex:
  fixes f g :: "_ \<Rightarrow> complex"
  assumes a: "a \<notin> \<real>\<^sub>\<le>\<^sub>0"
  assumes f: "(f \<longlongrightarrow> a) F" and g: "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
  by sorry

lemma tendsto_powr_complex_0:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f: "(f \<longlongrightarrow> 0) F" and g: "(g \<longlongrightarrow> b) F" and b: "Re b > 0"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> 0) F"
  by sorry

lemma tendsto_powr_complex' [tendsto_intros]:
  fixes f g :: "_ \<Rightarrow> complex"
  assumes "a \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> (a = 0 \<and> Re b > 0)" and "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
  by sorry

lemma tendsto_neg_powr_complex_of_real:
  assumes "filterlim f at_top F" and "Re s < 0"
  shows   "((\<lambda>x. complex_of_real (f x) powr s) \<longlongrightarrow> 0) F"
  by sorry

lemma tendsto_neg_powr_complex_of_nat:
  assumes "filterlim f at_top F" and "Re s < 0"
  shows   "((\<lambda>x. of_nat (f x) powr s) \<longlongrightarrow> 0) F"
  by sorry

lemma continuous_powr_complex [continuous_intros]: 
  assumes "continuous F f" "continuous F g"
  assumes "Re (f (netlimit F)) \<ge> 0 \<or> Im (f (netlimit F)) \<noteq> 0"
  assumes "f (netlimit F) = 0 \<longrightarrow> Re (g (netlimit F)) > 0"
  shows   "continuous F (\<lambda>z. f z powr g z :: complex)"
  by sorry

lemma continuous_powr_real [continuous_intros]: 
  assumes "continuous F f" "continuous F g"
  assumes "f (netlimit F) = 0 \<longrightarrow> g (netlimit F) > 0 \<and> (\<forall>\<^sub>F z in F. 0 \<le> f z)"
  shows   "continuous F (\<lambda>z. f z powr g z :: real)"
  by sorry

lemma isCont_powr_complex [continuous_intros]:
  assumes "f z \<notin> \<real>\<^sub>\<le>\<^sub>0" "isCont f z" "isCont g z"
  shows   "isCont (\<lambda>z. f z powr g z :: complex) z"
  by sorry

lemma continuous_on_powr_complex [continuous_intros]:
  assumes "A \<subseteq> {z. Re (f z) \<ge> 0 \<or> Im (f z) \<noteq> 0}"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z = 0 \<Longrightarrow> Re (g z) > 0"
  assumes "continuous_on A f" "continuous_on A g"
  shows   "continuous_on A (\<lambda>z. f z powr g z)"
  by sorry

lemma analytic_on_powr [analytic_intros]:
  assumes "f analytic_on X" "g analytic_on X" "\<And>x. x \<in> X \<Longrightarrow> f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. f x powr g x) analytic_on X"
  by sorry

lemma holomorphic_on_powr [holomorphic_intros]:
  assumes "f holomorphic_on X" "g holomorphic_on X" "\<And>x. x \<in> X \<Longrightarrow> f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. f x powr g x) holomorphic_on X"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Some Limits involving Logarithms\<close>

lemma lim_Ln_over_power:
  fixes s::complex
  assumes "0 < Re s"
    shows "(\<lambda>n. Ln (of_nat n) / of_nat n powr s) \<longlonglongrightarrow> 0"
  by sorry

lemma lim_Ln_over_n: "((\<lambda>n. Ln(of_nat n) / of_nat n) \<longlongrightarrow> 0) sequentially"
  by sorry

lemma lim_ln_over_power:
  fixes s :: real
  assumes "0 < s"
  shows "(\<lambda>n. ln (real n) / real n powr s) \<longlonglongrightarrow> 0"
  by sorry

lemma lim_ln_over_n [tendsto_intros]: "((\<lambda>n. ln(real_of_nat n) / of_nat n) \<longlongrightarrow> 0) sequentially"
  by sorry

lemma lim_log_over_n [tendsto_intros]:
  "(\<lambda>n. log k n/n) \<longlonglongrightarrow> 0"
  by sorry

lemma lim_1_over_complex_power:
  assumes "0 < Re s"
  shows "(\<lambda>n. 1 / of_nat n powr s) \<longlonglongrightarrow> 0"
  by sorry

lemma lim_1_over_real_power:
  fixes s :: real
  assumes "0 < s"
  shows "((\<lambda>n. 1 / (of_nat n powr s)) \<longlongrightarrow> 0) sequentially"
  by sorry

lemma lim_1_over_Ln: "(\<lambda>n. 1 / Ln (complex_of_nat n)) \<longlonglongrightarrow> 0"
  by sorry

lemma lim_1_over_ln: "(\<lambda>n. 1 / ln (real n)) \<longlonglongrightarrow> 0"
  by sorry

lemma lim_ln1_over_ln: "(\<lambda>n. ln(Suc n) / ln n) \<longlonglongrightarrow> 1"
  by sorry

lemma lim_ln_over_ln1: "(\<lambda>n. ln n / ln(Suc n)) \<longlonglongrightarrow> 1"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relation between Square Root and exp/ln, hence its derivative\<close>

lemma csqrt_exp_Ln:
  assumes "z \<noteq> 0"
    shows "csqrt z = exp(Ln z / 2)"
  by sorry

lemma csqrt_in_nonpos_Reals_iff [simp]: "csqrt z \<in> \<real>\<^sub>\<le>\<^sub>0 \<longleftrightarrow> z = 0"
  by sorry

lemma Im_csqrt_eq_0_iff: "Im (csqrt z) = 0 \<longleftrightarrow> z \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by sorry

lemma csqrt_conv_powr: "csqrt z = z powr (1/2)"
  by sorry

lemma csqrt_mult:
  assumes "Arg z + Arg w \<in> {-pi<..pi}"
  shows   "csqrt (z * w) = csqrt z * csqrt w"
  by sorry

lemma Arg_csqrt [simp]: "Arg (csqrt z) = Arg z / 2"
  by sorry

lemma csqrt_inverse:
  "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> csqrt (inverse z) = inverse (csqrt z)"
  by sorry

lemma cnj_csqrt: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> cnj(csqrt z) = csqrt(cnj z)"
  by sorry

lemma has_field_derivative_csqrt:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "(csqrt has_field_derivative inverse(2 * csqrt z)) (at z)"
  by sorry

lemma has_field_derivative_csqrt' [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)" "f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. csqrt (f x)) has_field_derivative (f' / (2 * csqrt (f x)))) (at x within A)"
  by sorry

lemma field_differentiable_at_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> csqrt field_differentiable at z"
  by sorry

lemma field_differentiable_within_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> csqrt field_differentiable (at z within s)"
  by sorry

lemma continuous_at_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z) csqrt"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> isCont_csqrt' [simp]:
   "\<lbrakk>isCont f z; f z \<notin> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. csqrt (f x)) z"
  by sorry

lemma continuous_within_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within s) csqrt"
  by sorry

lemma continuous_on_csqrt [continuous_intros]:
    "continuous_on (-\<real>\<^sub>\<le>\<^sub>0) csqrt"
  by sorry

lemma holomorphic_on_csqrt [holomorphic_intros]: "csqrt holomorphic_on -\<real>\<^sub>\<le>\<^sub>0"
  by sorry

lemma holomorphic_on_csqrt' [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> (\<lambda>z. csqrt (f z)) holomorphic_on A"
  by sorry

lemma analytic_on_csqrt [analytic_intros]: "csqrt analytic_on -\<real>\<^sub>\<le>\<^sub>0"
  by sorry

lemma analytic_on_csqrt' [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> (\<lambda>z. csqrt (f z)) analytic_on A"
  by sorry

lemma continuous_within_closed_nontrivial:
    "closed s \<Longrightarrow> a \<notin> s ==> continuous (at a within s) f"
  by sorry

lemma continuous_within_csqrt_posreal:
    "continuous (at z within (\<real> \<inter> {w. 0 \<le> Re(w)})) csqrt"
  by sorry

subsection\<open>Complex arctangent\<close>

text\<open>The branch cut gives standard bounds in the real case.\<close>

definition\<^marker>\<open>tag important\<close> Arctan :: "complex \<Rightarrow> complex" where
    "Arctan \<equiv> \<lambda>z. (\<i>/2) * Ln((1 - \<i>*z) / (1 + \<i>*z))"

lemma Arctan_def_moebius: "Arctan z = \<i>/2 * Ln (moebius (-\<i>) 1 \<i> 1 z)"
  by sorry

lemma Ln_conv_Arctan:
  assumes "z \<noteq> -1"
  shows   "Ln z = -2*\<i> * Arctan (moebius 1 (- 1) (- \<i>) (- \<i>) z)"
  by sorry

lemma Arctan_0 [simp]: "Arctan 0 = 0"
  by sorry

lemma Im_complex_div_lemma: "Im((1 - \<i>*z) / (1 + \<i>*z)) = 0 \<longleftrightarrow> Re z = 0"
  by sorry

lemma Re_complex_div_lemma: "0 < Re((1 - \<i>*z) / (1 + \<i>*z)) \<longleftrightarrow> norm z < 1"
  by sorry

lemma tan_Arctan:
  assumes "z\<^sup>2 \<noteq> -1"
  shows [simp]: "tan(Arctan z) = z"
  by sorry

lemma Arctan_tan [simp]:
  assumes "\<bar>Re z\<bar> < pi/2"
    shows "Arctan(tan z) = z"
  by sorry

lemma
  assumes "Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1"
  shows Re_Arctan_bounds: "\<bar>Re(Arctan z)\<bar> < pi/2"
    and has_field_derivative_Arctan: "(Arctan has_field_derivative inverse(1 + z\<^sup>2)) (at z)"
  by sorry

lemma field_differentiable_at_Arctan: "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan field_differentiable at z"
  by sorry

lemma field_differentiable_within_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan field_differentiable (at z within s)"
  by sorry

declare has_field_derivative_Arctan [derivative_intros]
declare has_field_derivative_Arctan [THEN DERIV_chain2, derivative_intros]

lemma continuous_at_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous (at z) Arctan"
  by sorry

lemma continuous_within_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arctan"
  by sorry

lemma continuous_on_Arctan [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous_on s Arctan"
  by sorry

lemma holomorphic_on_Arctan:
    "(\<And>z. z \<in> s \<Longrightarrow> Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan holomorphic_on s"
  by sorry

theorem Arctan_series:
  assumes z: "norm (z :: complex) < 1"
  defines "g \<equiv> \<lambda>n. if odd n then -\<i>*\<i>^n / n else 0"
  defines "h \<equiv> \<lambda>z n. (-1)^n / of_nat (2*n+1) * (z::complex)^(2*n+1)"
  shows   "(\<lambda>n. g n * z^n) sums Arctan z"
  and     "h z sums Arctan z"
  by sorry

text \<open>A quickly-converging series for the logarithm, based on the arctangent.\<close>
theorem ln_series_quadratic:
  assumes x: "x > (0::real)"
  shows "(\<lambda>n. (2*((x - 1) / (x + 1)) ^ (2*n+1) / of_nat (2*n+1))) sums ln x"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Real arctangent\<close>

lemma Im_Arctan_of_real [simp]: "Im (Arctan (of_real x)) = 0"
  by sorry

lemma arctan_eq_Re_Arctan: "arctan x = Re (Arctan (of_real x))"
  by sorry

lemma Arctan_of_real: "Arctan (of_real x) = of_real (arctan x)"
  by sorry

lemma Arctan_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> Arctan z \<in> \<real>"
  by sorry

declare arctan_one [simp]

lemma arctan_less_pi4_pos: "x < 1 \<Longrightarrow> arctan x < pi/4"
  by sorry

lemma arctan_less_pi4_neg: "-1 < x \<Longrightarrow> -(pi/4) < arctan x"
  by sorry

lemma arctan_less_pi4: "\<bar>x\<bar> < 1 \<Longrightarrow> \<bar>arctan x\<bar> < pi/4"
  by sorry

lemma arctan_le_pi4: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>arctan x\<bar> \<le> pi/4"
  by sorry

lemma abs_arctan: "\<bar>arctan x\<bar> = arctan \<bar>x\<bar>"
  by sorry

lemma arctan_add_raw:
  assumes "\<bar>arctan x + arctan y\<bar> < pi/2"
    shows "arctan x + arctan y = arctan((x + y) / (1 - x * y))"
  by sorry

lemma arctan_inverse:
  "0 < x \<Longrightarrow>arctan(inverse x) = pi/2 - arctan x"
  by sorry

lemma arctan_add_small:
  assumes "\<bar>x * y\<bar> < 1"
    shows "(arctan x + arctan y = arctan((x + y) / (1 - x * y)))"
  by sorry

lemma abs_arctan_le:
  fixes x::real shows "\<bar>arctan x\<bar> \<le> \<bar>x\<bar>"
  by sorry

lemma arctan_le_self: "0 \<le> x \<Longrightarrow> arctan x \<le> x"
  by sorry

lemma abs_tan_ge: "\<bar>x\<bar> < pi/2 \<Longrightarrow> \<bar>x\<bar> \<le> \<bar>tan x\<bar>"
  by sorry

lemma arctan_bounds:
  assumes "0 \<le> x" "x < 1"
  shows arctan_lower_bound:
    "(\<Sum>k<2 * n. (- 1) ^ k * (1 / real (k * 2 + 1) * x ^ (k * 2 + 1))) \<le> arctan x" (is "(\<Sum>k<_. _ * ?a k) \<le> _")
    and arctan_upper_bound:
    "arctan x \<le> (\<Sum>k<2 * n + 1. (- 1) ^ k * (1 / real (k * 2 + 1) * x ^ (k * 2 + 1)))"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounds on pi using real arctangent\<close>

lemma pi_machin: "pi = 16 * arctan (1 / 5) - 4 * arctan (1 / 239)"
  by sorry

lemma pi_approx: "3.141592653588 \<le> pi" "pi \<le> 3.1415926535899"
  by sorry

lemma pi_gt3: "pi > 3"
  by sorry


subsection\<open>Inverse Sine\<close>

definition\<^marker>\<open>tag important\<close> Arcsin :: "complex \<Rightarrow> complex" where
   "Arcsin \<equiv> \<lambda>z. -\<i> * Ln(\<i> * z + csqrt(1 - z\<^sup>2))"

lemma Arcsin_body_lemma: "\<i> * z + csqrt(1 - z\<^sup>2) \<noteq> 0"
  by sorry

lemma Arcsin_range_lemma: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Re(\<i> * z + csqrt(1 - z\<^sup>2))"
  by sorry

lemma Re_Arcsin: "Re(Arcsin z) = Im (Ln (\<i> * z + csqrt(1 - z\<^sup>2)))"
  by sorry

lemma Im_Arcsin: "Im(Arcsin z) = - ln (cmod (\<i> * z + csqrt (1 - z\<^sup>2)))"
  by sorry

lemma one_minus_z2_notin_nonpos_Reals:
  assumes "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
  shows "1 - z\<^sup>2 \<notin> \<real>\<^sub>\<le>\<^sub>0"
  by sorry

lemma isCont_Arcsin_lemma:
  assumes le0: "Re (\<i> * z + csqrt (1 - z\<^sup>2)) \<le> 0" and "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows False
  by sorry

lemma isCont_Arcsin:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "isCont Arcsin z"
  by sorry

lemma isCont_Arcsin' [simp]:
  shows "isCont f z \<Longrightarrow> (Im (f z) = 0 \<Longrightarrow> \<bar>Re (f z)\<bar> < 1) \<Longrightarrow> isCont (\<lambda>x. Arcsin (f x)) z"
  by sorry

lemma sin_Arcsin [simp]: "sin(Arcsin z) = z"
  by sorry

lemma Re_eq_pihalf_lemma:
    "\<bar>Re z\<bar> = pi/2 \<Longrightarrow> Im z = 0 \<Longrightarrow>
      Re ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2) = 0 \<and> 0 \<le> Im ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2)"
  by sorry

lemma Re_less_pihalf_lemma:
  assumes "\<bar>Re z\<bar> < pi / 2"
    shows "0 < Re ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2)"
  by sorry

lemma Arcsin_sin:
    assumes "\<bar>Re z\<bar> < pi/2 \<or> (\<bar>Re z\<bar> = pi/2 \<and> Im z = 0)"
      shows "Arcsin(sin z) = z"
  by sorry

lemma Arcsin_unique:
    "\<lbrakk>sin z = w; \<bar>Re z\<bar> < pi/2 \<or> (\<bar>Re z\<bar> = pi/2 \<and> Im z = 0)\<rbrakk> \<Longrightarrow> Arcsin w = z"
  by sorry

lemma Arcsin_0 [simp]: "Arcsin 0 = 0"
  by sorry

lemma Arcsin_1 [simp]: "Arcsin 1 = pi/2"
  by sorry

lemma Arcsin_minus_1 [simp]: "Arcsin(-1) = - (pi/2)"
  by sorry

lemma has_field_derivative_Arcsin:
  assumes "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
    shows "(Arcsin has_field_derivative inverse(cos(Arcsin z))) (at z)"
  by sorry

declare has_field_derivative_Arcsin [derivative_intros]
declare has_field_derivative_Arcsin [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin field_differentiable at z"
  by sorry

lemma field_differentiable_within_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin field_differentiable (at z within s)"
  by sorry

lemma continuous_within_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arcsin"
  by sorry

lemma continuous_on_Arcsin [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous_on s Arcsin"
  by sorry

lemma holomorphic_on_Arcsin: "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin holomorphic_on s"
  by sorry


subsection\<open>Inverse Cosine\<close>

definition\<^marker>\<open>tag important\<close> Arccos :: "complex \<Rightarrow> complex" where
   "Arccos \<equiv> \<lambda>z. -\<i> * Ln(z + \<i> * csqrt(1 - z\<^sup>2))"

lemma Arccos_range_lemma: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Im(z + \<i> * csqrt(1 - z\<^sup>2))"
  by sorry

lemma Arccos_body_lemma: "z + \<i> * csqrt(1 - z\<^sup>2) \<noteq> 0"
  by sorry

lemma Re_Arccos: "Re(Arccos z) = Im (Ln (z + \<i> * csqrt(1 - z\<^sup>2)))"
  by sorry

lemma Im_Arccos: "Im(Arccos z) = - ln (cmod (z + \<i> * csqrt (1 - z\<^sup>2)))"
  by sorry

text\<open>A very tricky argument to find!\<close>
lemma isCont_Arccos_lemma:
  assumes eq0: "Im (z + \<i> * csqrt (1 - z\<^sup>2)) = 0" and "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
    shows False
  by sorry

lemma isCont_Arccos:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "isCont Arccos z"
  by sorry

lemma isCont_Arccos' [simp]:
  "isCont f z \<Longrightarrow> (Im (f z) = 0 \<Longrightarrow> \<bar>Re (f z)\<bar> < 1) \<Longrightarrow> isCont (\<lambda>x. Arccos (f x)) z"
  by sorry

lemma cos_Arccos [simp]: "cos(Arccos z) = z"
  by sorry

lemma Arccos_cos:
    assumes "0 < Re z \<and> Re z < pi \<or>
             Re z = 0 \<and> 0 \<le> Im z \<or>
             Re z = pi \<and> Im z \<le> 0"
      shows "Arccos(cos z) = z"
  by sorry

lemma Arccos_unique:
    "\<lbrakk>cos z = w;
      0 < Re z \<and> Re z < pi \<or>
      Re z = 0 \<and> 0 \<le> Im z \<or>
      Re z = pi \<and> Im z \<le> 0\<rbrakk> \<Longrightarrow> Arccos w = z"
  by sorry

lemma Arccos_0 [simp]: "Arccos 0 = pi/2"
  by sorry

lemma Arccos_1 [simp]: "Arccos 1 = 0"
  by sorry

lemma Arccos_minus1: "Arccos(-1) = pi"
  by sorry

lemma has_field_derivative_Arccos:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "(Arccos has_field_derivative - inverse(sin(Arccos z))) (at z)"
  by sorry

declare has_field_derivative_Arcsin [derivative_intros]
declare has_field_derivative_Arcsin [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos field_differentiable at z"
  by sorry

lemma field_differentiable_within_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos field_differentiable (at z within s)"
  by sorry

lemma continuous_within_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arccos"
  by sorry

lemma continuous_on_Arccos [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous_on s Arccos"
  by sorry

lemma holomorphic_on_Arccos: "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos holomorphic_on s"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Upper and Lower Bounds for Inverse Sine and Cosine\<close>

lemma Arcsin_bounds: "\<bar>Re z\<bar> < 1 \<Longrightarrow> \<bar>Re(Arcsin z)\<bar> < pi/2"
  by sorry

lemma Arccos_bounds: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Re(Arccos z) \<and> Re(Arccos z) < pi"
  by sorry

lemma Re_Arccos_bounds: "-pi < Re(Arccos z) \<and> Re(Arccos z) \<le> pi"
  by sorry

lemma Re_Arccos_bound: "\<bar>Re(Arccos z)\<bar> \<le> pi"
  by sorry

lemma Im_Arccos_bound: "\<bar>Im (Arccos w)\<bar> \<le> cmod w"
  by sorry

lemma Re_Arcsin_bounds: "-pi < Re(Arcsin z) & Re(Arcsin z) \<le> pi"
  by sorry

lemma Re_Arcsin_bound: "\<bar>Re(Arcsin z)\<bar> \<le> pi"
  by sorry

lemma norm_Arccos_bounded:
  fixes w :: complex
  shows "norm (Arccos w) \<le> pi + norm w"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Interrelations between Arcsin and Arccos\<close>

lemma cos_Arcsin_nonzero: "z\<^sup>2 \<noteq> 1 \<Longrightarrow>cos(Arcsin z) \<noteq> 0"
  by sorry

lemma sin_Arccos_nonzero: "z\<^sup>2 \<noteq> 1 \<Longrightarrow>sin(Arccos z) \<noteq> 0"
  by sorry

lemma cos_sin_csqrt:
  assumes "0 < cos(Re z)  \<or>  cos(Re z) = 0 \<and> Im z * sin(Re z) \<le> 0"
    shows "cos z = csqrt(1 - (sin z)\<^sup>2)"
  by sorry

lemma sin_cos_csqrt:
  assumes "0 < sin(Re z)  \<or>  sin(Re z) = 0 \<and> 0 \<le> Im z * cos(Re z)"
    shows "sin z = csqrt(1 - (cos z)\<^sup>2)"
  by sorry

lemma Arcsin_Arccos_csqrt_pos:
    "(0 < Re z \<or> Re z = 0 \<and> 0 \<le> Im z) \<Longrightarrow> Arcsin z = Arccos(csqrt(1 - z\<^sup>2))"
  by sorry

lemma Arccos_Arcsin_csqrt_pos:
    "(0 < Re z \<or> Re z = 0 \<and> 0 \<le> Im z) \<Longrightarrow> Arccos z = Arcsin(csqrt(1 - z\<^sup>2))"
  by sorry

lemma sin_Arccos:
    "0 < Re z \<or> Re z = 0 \<and> 0 \<le> Im z \<Longrightarrow> sin(Arccos z) = csqrt(1 - z\<^sup>2)"
  by sorry

lemma cos_Arcsin:
    "0 < Re z \<or> Re z = 0 \<and> 0 \<le> Im z \<Longrightarrow> cos(Arcsin z) = csqrt(1 - z\<^sup>2)"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relationship with Arcsin on the Real Numbers\<close>

lemma of_real_arcsin: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> of_real(arcsin x) = Arcsin(of_real x)"
  by sorry

lemma Im_Arcsin_of_real: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> Im (Arcsin (of_real x)) = 0"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Arcsin_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> \<bar>Re z\<bar> \<le> 1 \<Longrightarrow> Arcsin z \<in> \<real>"
  by sorry

lemma arcsin_eq_Re_Arcsin: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> arcsin x = Re (Arcsin (of_real x))"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relationship with Arccos on the Real Numbers\<close>

lemma of_real_arccos: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> of_real(arccos x) = Arccos(of_real x)"
  by sorry

lemma Im_Arccos_of_real: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> Im (Arccos (of_real x)) = 0"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Arccos_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> \<bar>Re z\<bar> \<le> 1 \<Longrightarrow> Arccos z \<in> \<real>"
  by sorry

lemma arccos_eq_Re_Arccos: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> arccos x = Re (Arccos (of_real x))"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Continuity results for arcsin and arccos\<close>

lemma continuous_on_Arcsin_real [continuous_intros]:
    "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} Arcsin"
  by sorry

lemma continuous_within_Arcsin_real:
    "continuous (at z within {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}) Arcsin"
  by sorry

lemma continuous_on_Arccos_real:
    "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} Arccos"
  by sorry

lemma continuous_within_Arccos_real:
    "continuous (at z within {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}) Arccos"
  by sorry

lemma sinh_ln_complex: "x \<noteq> 0 \<Longrightarrow> sinh (ln x :: complex) = (x - inverse x) / 2"
  by sorry

lemma cosh_ln_complex: "x \<noteq> 0 \<Longrightarrow> cosh (ln x :: complex) = (x + inverse x) / 2"
  by sorry

lemma tanh_ln_complex: "x \<noteq> 0 \<Longrightarrow> tanh (ln x :: complex) = (x ^ 2 - 1) / (x ^ 2 + 1)"
  by sorry


subsection\<open>Roots of unity\<close>

theorem complex_root_unity:
  fixes j::nat
  assumes "n \<noteq> 0"
    shows "exp(2 * of_real pi * \<i> * of_nat j / of_nat n)^n = 1"
  by sorry

lemma complex_root_unity_eq:
  fixes j::nat and k::nat
  assumes "1 \<le> n"
    shows "(exp(2 * of_real pi * \<i> * of_nat j / of_nat n) = exp(2 * of_real pi * \<i> * of_nat k / of_nat n)
           \<longleftrightarrow> j mod n = k mod n)"
  by sorry

corollary bij_betw_roots_unity:
    "bij_betw (\<lambda>j. exp(2 * of_real pi * \<i> * of_nat j / of_nat n))
              {..<n}  {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j. j < n}"
  by sorry

lemma complex_root_unity_eq_1:
  fixes j::nat and k::nat
  assumes "1 \<le> n"
    shows "exp(2 * of_real pi * \<i> * of_nat j / of_nat n) = 1 \<longleftrightarrow> n dvd j"
  by sorry

lemma finite_complex_roots_unity_explicit:
  "finite {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j::nat. j < n}"
  by sorry

lemma card_complex_roots_unity_explicit:
     "card {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j::nat. j < n} = n"
  by sorry

lemma complex_roots_unity:
  assumes "1 \<le> n"
    shows "{z::complex. z^n = 1} = {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j. j < n}"
  by sorry

lemma card_complex_roots_unity: "1 \<le> n \<Longrightarrow> card {z::complex. z^n = 1} = n"
  by sorry

lemma complex_not_root_unity:
    "1 \<le> n \<Longrightarrow> \<exists>u::complex. norm u = 1 \<and> u^n \<noteq> 1"
  by sorry


subsection \<open>Normalisation of angles\<close>

text \<open>
  The following operation normalises an angle $\varphi$, i.e.\ returns the unique
  $\psi$ in the range $(-\pi, \pi]$ such that
  $\varphi\equiv\psi\hskip.5em(\text{mod}\ 2\pi)$.
  This is the same convention used by the \<^const>\<open>Arg\<close> function.
\<close>
definition normalize_angle :: "real \<Rightarrow> real" where
  "normalize_angle x = x - \<lceil>x / (2 * pi) - 1 / 2\<rceil> * (2 * pi)"

lemma normalize_angle_id [simp]:
  assumes "x \<in> {-pi<..pi}"
  shows   "normalize_angle x = x"
  by sorry

lemma normalize_angle_normalized: "normalize_angle x \<in> {-pi<..pi}"
  by sorry

lemma cis_normalize_angle [simp]: "cis (normalize_angle x) = cis x"
  by sorry

lemma rcis_normalize_angle [simp]: "rcis r (normalize_angle x) = rcis r x"
  by sorry

lemma normalize_angle_lbound [intro]: "normalize_angle x > -pi"
  and normalize_angle_ubound [intro]: "normalize_angle x \<le> pi"
  by sorry

lemma normalize_angle_idem [simp]: "normalize_angle (normalize_angle x) = normalize_angle x"
  by sorry

lemma Arg_rcis': "r > 0 \<Longrightarrow> Arg (rcis r \<phi>) = normalize_angle \<phi>"
  by sorry


subsection \<open>Convexity of circular sectors in the complex plane\<close>

text \<open>
  In this section we will show that if we have two non-zero points $w$ and $z$ in the complex plane
  whose arguments differ by less than $\pi$, then the argument of any point on the line connecting
  $w$ and $z$ lies between the arguments of $w$ and $z$. Moreover, the norm of any such point is
  no greater than the norms of $w$ and $z$.

  Geometrically, this means that if we have a sector around the origin with a central angle
  less than $\pi$ (minus the origin itself) then that region is convex.
\<close>

lemma Arg_closed_segment_aux1:
  assumes "x \<noteq> 0" "y \<noteq> 0" "Re x > 0" "Re x = Re y"
  assumes "z \<in> closed_segment x y"
  shows   "Arg z \<in> closed_segment (Arg x) (Arg y)"
  by sorry

lemma Arg_closed_segment_aux1':
  fixes r1 r2 \<phi>1 \<phi>2 :: real
  defines "x \<equiv> rcis r1 \<phi>1" and "y \<equiv> rcis r2 \<phi>2"
  assumes "z \<in> closed_segment x y"
  assumes "r1 > 0" "r2 > 0" "Re x = Re y" "Re x \<ge> 0" "Re x = 0 \<longrightarrow> Im x * Im y > 0"
  assumes "dist \<phi>1 \<phi>2 < pi"
  obtains r \<phi> where "r \<in> {0<..max r1 r2}" "\<phi> \<in> closed_segment \<phi>1 \<phi>2" "z = rcis r \<phi>"
  by sorry

lemma Arg_closed_segment':
  fixes r1 r2 \<phi>1 \<phi>2 :: real
  defines "x \<equiv> rcis r1 \<phi>1" and "y \<equiv> rcis r2 \<phi>2"
  assumes "r1 > 0" "r2 > 0" "dist \<phi>1 \<phi>2 < pi" "z \<in> closed_segment x y"
  obtains r \<phi> where "r \<in> {0<..max r1 r2}" "\<phi> \<in> closed_segment \<phi>1 \<phi>2" "z = rcis r \<phi>"
  by sorry

lemma Arg_closed_segment:
  assumes "x \<noteq> 0" "y \<noteq> 0" "dist (Arg x) (Arg y) < pi" "z \<in> closed_segment x y"
  shows   "Arg z \<in> closed_segment (Arg x) (Arg y)"
  by sorry


subsection \<open>Complex cones\<close>

text \<open>
  We introduce the following notation to describe the set of all complex numbers of the form
  $c e^{ix}$ where $c\geq 0$ and $x\in [a, b]$.
\<close>
definition complex_cone :: "real \<Rightarrow> real \<Rightarrow> complex set" where
  "complex_cone a b = (\<lambda>(r,a). rcis r a) ` ({0..} \<times> closed_segment a b)"

lemma in_complex_cone_iff: "z \<in> complex_cone a b \<longleftrightarrow> (\<exists>x\<in>closed_segment a b. z = rcis (norm z) x)"
  by sorry

lemma zero_in_complex_cone [simp, intro]: "0 \<in> complex_cone a b"
  by sorry

lemma in_complex_cone_iff_Arg: 
  assumes "a \<in> {-pi<..pi}" "b \<in> {-pi<..pi}"
  shows   "z \<in> complex_cone a b \<longleftrightarrow> z = 0 \<or> Arg z \<in> closed_segment a b"
  by sorry

lemma complex_cone_rotate: "complex_cone (c + a) (c + b) = (*) (cis c) ` complex_cone a b"
  by sorry

lemma complex_cone_subset: 
  "a \<in> closed_segment a' b' \<Longrightarrow> b \<in> closed_segment a' b' \<Longrightarrow> complex_cone a b \<subseteq> complex_cone a' b'"
  by sorry

lemma complex_cone_commute: "complex_cone a b = complex_cone b a"
  by sorry

lemma complex_cone_eq_UNIV:
  assumes "dist a b \<ge> 2*pi"
  shows   "complex_cone a b = UNIV"
  by sorry


text \<open>
  A surprisingly tough argument: cones in the complex plane are closed.
\<close>
lemma closed_complex_cone [continuous_intros, intro]: "closed (complex_cone a b)"
  by sorry

lemma norm_eq_Re_iff: "norm z = Re z \<longleftrightarrow> z \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by sorry

end
