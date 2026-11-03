(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light)
                Huge cleanup by LCP
*)

section \<open>Henstock-Kurzweil Gauge Integration in Many Dimensions\<close>

theory Henstock_Kurzweil_Integration
imports
  Lebesgue_Measure Tagged_Division
begin

lemma norm_diff2: "\<lbrakk>y = y1 + y2; x = x1 + x2; e = e1 + e2; norm(y1 - x1) \<le> e1; norm(y2 - x2) \<le> e2\<rbrakk>
  \<Longrightarrow> norm(y-x) \<le> e"
sorry

lemma setcomp_dot1: "{z. P (z \<bullet> (i,0))} = {(x,y). P(x \<bullet> i)}"
sorry

lemma setcomp_dot2: "{z. P (z \<bullet> (0,i))} = {(x,y). P(y \<bullet> i)}"
sorry

lemma Sigma_Int_Paircomp1: "(Sigma A B) \<inter> {(x, y). P x} = Sigma (A \<inter> {x. P x}) B"
sorry

lemma Sigma_Int_Paircomp2: "(Sigma A B) \<inter> {(x, y). P y} = Sigma A (\<lambda>z. B z \<inter> {y. P y})"
sorry
subsection \<open>Content (length, area, volume...) of an interval\<close>

abbreviation content :: "'a::euclidean_space set \<Rightarrow> real"
  where "content s \<equiv> measure lborel s"

lemma content_cbox_cases:
  "content (cbox a b) = (if \<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i then prod (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis else 0)"
sorry

lemma content_cbox: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
sorry

lemma content_cbox': "cbox a b \<noteq> {} \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
sorry

lemma content_cbox_if: "content (cbox a b) = (if cbox a b = {} then 0 else \<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
sorry

lemma content_cbox_cart:
   "cbox a b \<noteq> {} \<Longrightarrow> content(cbox a b) = prod (\<lambda>i. b$i - a$i) UNIV"
sorry

lemma content_cbox_if_cart:
   "content(cbox a b) = (if cbox a b = {} then 0 else prod (\<lambda>i. b$i - a$i) UNIV)"
sorry

lemma content_division_of:
  assumes "K \<in> \<D>" "\<D> division_of S"
  shows "content K = (\<Prod>i \<in> Basis. interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i)"
sorry

lemma content_real: "a \<le> b \<Longrightarrow> content {a..b} = b - a"
sorry

lemma abs_eq_content: "\<bar>y - x\<bar> = (if x\<le>y then content {x..y} else content {y..x})"
sorry

lemma content_singleton: "content {a} = 0"
sorry

lemma content_unit[iff]: "content (cbox 0 (One::'a::euclidean_space)) = 1"
sorry

lemma content_pos_le [iff]: "0 \<le> content X"
sorry

corollary\<^marker>\<open>tag unimportant\<close> content_nonneg [simp]: "\<not> content (cbox a b) < 0"
sorry

lemma content_pos_lt: "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i \<Longrightarrow> 0 < content (cbox a b)"
sorry

lemma content_eq_0: "content (cbox a b) = 0 \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i)"
sorry

lemma content_eq_0_interior: "content (cbox a b) = 0 \<longleftrightarrow> interior(cbox a b) = {}"
sorry

lemma content_pos_lt_eq: "0 < content (cbox a (b::'a::euclidean_space)) \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
sorry

lemma content_empty [simp]: "content {} = 0"
sorry

lemma content_real_if [simp]: "content {a..b} = (if a \<le> b then b - a else 0)"
sorry

lemma content_subset: "cbox a b \<subseteq> cbox c d \<Longrightarrow> content (cbox a b) \<le> content (cbox c d)"
sorry

lemma content_lt_nz: "0 < content (cbox a b) \<longleftrightarrow> content (cbox a b) \<noteq> 0"
sorry

lemma content_Pair: "content (cbox (a,c) (b,d)) = content (cbox a b) * content (cbox c d)"
sorry

lemma content_cbox_pair_eq0_D:
   "content (cbox (a,c) (b,d)) = 0 \<Longrightarrow> content (cbox a b) = 0 \<or> content (cbox c d) = 0"
sorry

lemma content_cbox_plus:
  fixes x :: "'a::euclidean_space"
  shows "content(cbox x (x + h *\<^sub>R One)) = (if h \<ge> 0 then h ^ DIM('a) else 0)"
sorry

lemma content_0_subset: "content(cbox a b) = 0 \<Longrightarrow> s \<subseteq> cbox a b \<Longrightarrow> content s = 0"
sorry

lemma content_ball_pos:
  assumes "r > 0"
  shows   "content (ball c r) > 0"
sorry

lemma content_cball_pos:
  assumes "r > 0"
  shows   "content (cball c r) > 0"
sorry

lemma content_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "content (cbox a b) = content(cbox a b \<inter> {x. x\<bullet>k \<le> c}) + content(cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
  \<comment> \<open>Prove using measure theory\<close>
sorry

lemma division_of_content_0:
  assumes "content (cbox a b) = 0" "d division_of (cbox a b)" "K \<in> d"
  shows "content K = 0"
sorry

lemma sum_content_null:
  assumes "content (cbox a b) = 0"
    and "p tagged_division_of (cbox a b)"
  shows "(\<Sum>(x,K)\<in>p. content K *\<^sub>R f x) = (0::'a::real_normed_vector)"
sorry


global_interpretation sum_content: operative plus 0 content
  rewrites "comm_monoid_set.F plus 0 = sum"
proof -
  interpret operative plus 0 content
    by standard (auto simp add: content_split [symmetric] content_eq_0_interior)
  show "operative plus 0 content"
    by standard
  show "comm_monoid_set.F plus 0 = sum"
    by (simp add: sum_def)
qed

lemma additive_content_division: "d division_of (cbox a b) \<Longrightarrow> sum content d = content (cbox a b)"
sorry

lemma additive_content_tagged_division:
  "d tagged_division_of (cbox a b) \<Longrightarrow> sum (\<lambda>(x,l). content l) d = content (cbox a b)"
sorry

lemma subadditive_content_division:
  assumes "\<D> division_of S" "S \<subseteq> cbox a b"
  shows "sum content \<D> \<le> content(cbox a b)"
sorry

lemma content_real_eq_0: "content {a..b::real} = 0 \<longleftrightarrow> a \<ge> b"
sorry

lemma property_empty_interval: "\<forall>a b. content (cbox a b) = 0 \<longrightarrow> P (cbox a b) \<Longrightarrow> P {}"
sorry

lemma interval_bounds_nz_content [simp]:
  assumes "content (cbox a b) \<noteq> 0"
  shows "interval_upperbound (cbox a b) = b"
    and "interval_lowerbound (cbox a b) = a"
sorry
subsection \<open>Gauge integral\<close>

text \<open>Case distinction to define it first on compact intervals first, then use a limit. This is only
much later unified. In Fremlin: Measure Theory, Volume 4I this is generalized using residual sets.\<close>

definition has_integral :: "('n::euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> 'n set \<Rightarrow> bool"
  (infixr \<open>has'_integral\<close> 46)
  where "(f has_integral I) s \<longleftrightarrow>
    (if \<exists>a b. s = cbox a b
      then ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R f x) \<longlongrightarrow> I) (division_filter s)
      else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
        (\<exists>z. ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R (if x \<in> s then f x else 0)) \<longlongrightarrow> z) (division_filter (cbox a b)) \<and>
          norm (z - I) < e)))"

lemma has_integral_cbox:
  "(f has_integral I) (cbox a b) \<longleftrightarrow> ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R f x) \<longlongrightarrow> I) (division_filter (cbox a b))"
sorry

lemma has_integral:
  "(f has_integral y) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
      (\<forall>\<D>. \<D> tagged_division_of (cbox a b) \<and> \<gamma> fine \<D> \<longrightarrow>
        norm (sum (\<lambda>(x,k). content(k) *\<^sub>R f x) \<D> - y) < e))"
sorry

lemma has_integral_real:
  "(f has_integral y) {a..b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
      (\<forall>\<D>. \<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D> \<longrightarrow>
        norm (sum (\<lambda>(x,k). content(k) *\<^sub>R f x) \<D> - y) < e))"
sorry

lemma has_integralD[dest]:
  assumes "(f has_integral y) (cbox a b)"
    and "e > 0"
  obtains \<gamma>
    where "gauge \<gamma>"
      and "\<And>\<D>. \<D> tagged_division_of (cbox a b) \<Longrightarrow> \<gamma> fine \<D> \<Longrightarrow>
        norm ((\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R f x) - y) < e"
sorry

lemma has_integral_alt:
  "(f has_integral y) i \<longleftrightarrow>
    (if \<exists>a b. i = cbox a b
     then (f has_integral y) i
     else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e)))"
sorry

lemma has_integral_altD:
  assumes "(f has_integral y) i"
    and "\<not> (\<exists>a b. i = cbox a b)"
    and "e>0"
  obtains B where "B > 0"
    and "\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - y) < e)"
sorry
definition integrable_on (infixr \<open>integrable'_on\<close> 46)
  where "f integrable_on i \<longleftrightarrow> (\<exists>y. (f has_integral y) i)"

definition "integral i f = (SOME y. (f has_integral y) i \<or> \<not> f integrable_on i \<and> y=0)"

lemma integrable_integral[intro]: "f integrable_on i \<Longrightarrow> (f has_integral (integral i f)) i"
sorry

lemma not_integrable_integral: "\<not> f integrable_on i \<Longrightarrow> integral i f = 0"
sorry

lemma has_integral_integrable[dest]: "(f has_integral i) s \<Longrightarrow> f integrable_on s"
sorry

lemma has_integral_integral: "f integrable_on s \<longleftrightarrow> (f has_integral (integral s f)) s"
sorry
subsection \<open>Basic theorems about integrals\<close>

lemma has_integral_eq_rhs: "(f has_integral j) S \<Longrightarrow> i = j \<Longrightarrow> (f has_integral i) S"
sorry

lemma has_integral_unique_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  shows "(f has_integral k1) (cbox a b) \<Longrightarrow> (f has_integral k2) (cbox a b) \<Longrightarrow> k1 = k2"
sorry

lemma has_integral_unique:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k1) i" "(f has_integral k2) i"
  shows "k1 = k2"
sorry

lemma integral_unique [intro]: "(f has_integral y) k \<Longrightarrow> integral k f = y"
sorry

lemma has_integral_iff: "(f has_integral i) S \<longleftrightarrow> (f integrable_on S \<and> integral S f = i)"
sorry

lemma eq_integralD: "integral k f = y \<Longrightarrow> (f has_integral y) k \<or> \<not> f integrable_on k \<and> y=0"
sorry

lemma has_integral_const [intro]:
  fixes a b :: "'a::euclidean_space"
  shows "((\<lambda>x. c) has_integral (content (cbox a b) *\<^sub>R c)) (cbox a b)"
sorry

lemma has_integral_const_real [intro]:
  fixes a b :: real
  shows "((\<lambda>x. c) has_integral (content {a..b} *\<^sub>R c)) {a..b}"
sorry

lemma has_integral_integrable_integral: "(f has_integral i) s \<longleftrightarrow> f integrable_on s \<and> integral s f = i"
sorry

lemma integral_const [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "integral (cbox a b) (\<lambda>x. c) = content (cbox a b) *\<^sub>R c"
sorry

lemma integral_const_real [simp]:
  fixes a b :: real
  shows "integral {a..b} (\<lambda>x. c) = content {a..b} *\<^sub>R c"
sorry

lemma has_integral_is_0_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<And>x. x \<in> cbox a b \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) (cbox a b)"
sorry

lemma has_integral_is_0:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) S"
sorry

lemma has_integral_0[simp]: "((\<lambda>x::'n::euclidean_space. 0) has_integral 0) S"
sorry

lemma has_integral_0_eq[simp]: "((\<lambda>x. 0) has_integral i) S \<longleftrightarrow> i = 0"
sorry

lemma has_integral_linear_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral y) (cbox a b)"
    and h: "bounded_linear h"
  shows "((h \<circ> f) has_integral (h y)) (cbox a b)"
sorry

lemma has_integral_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral y) S"
    and h: "bounded_linear h"
  shows "((h \<circ> f) has_integral (h y)) S"
sorry

lemma has_integral_scaleR_left:
  "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x *\<^sub>R c) has_integral (y *\<^sub>R c)) S"
sorry

lemma integrable_on_scaleR_left:
  assumes "f integrable_on A"
  shows "(\<lambda>x. f x *\<^sub>R y) integrable_on A"
sorry

lemma has_integral_mult_left:
  fixes c :: "_ :: real_normed_algebra"
  shows "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x * c) has_integral (y * c)) S"
sorry

lemma integrable_on_mult_left:
  fixes c :: "'a :: real_normed_algebra"
  assumes "f integrable_on A"
  shows   "(\<lambda>x. f x * c) integrable_on A"
sorry

lemma has_integral_divide:
  fixes c :: "_ :: real_normed_div_algebra"
  shows "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x / c) has_integral (y / c)) S"
sorry

lemma integrable_on_divide:
  fixes c :: "'a :: real_normed_div_algebra"
  assumes "f integrable_on A"
  shows   "(\<lambda>x. f x / c) integrable_on A"
sorry
text\<open>The case analysis eliminates the condition \<^term>\<open>f integrable_on S\<close> at the cost
     of the type class constraint \<open>division_ring\<close>\<close>
corollary integral_mult_left [simp]:
  fixes c:: "'a::{real_normed_algebra,division_ring}"
  shows "integral S (\<lambda>x. f x * c) = integral S f * c"
sorry

corollary integral_mult_right [simp]:
  fixes c:: "'a::{real_normed_field}"
  shows "integral S (\<lambda>x. c * f x) = c * integral S f"
sorry

corollary integral_divide [simp]:
  fixes z :: "'a::real_normed_field"
  shows "integral S (\<lambda>x. f x / z) = integral S (\<lambda>x. f x) / z"
sorry

lemma has_integral_mult_right:
  fixes c :: "'a :: real_normed_algebra"
  shows "(f has_integral y) A \<Longrightarrow> ((\<lambda>x. c * f x) has_integral (c * y)) A"
sorry

lemma integrable_on_mult_right:
  fixes c :: "'a :: real_normed_algebra"
  assumes "f integrable_on A"
  shows   "(\<lambda>x. c * f x) integrable_on A"
sorry

lemma integrable_on_mult_right_iff [simp]:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. c * f x) integrable_on A \<longleftrightarrow> f integrable_on A"
sorry

lemma integrable_on_mult_left_iff [simp]:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. f x * c) integrable_on A \<longleftrightarrow> f integrable_on A"
sorry

lemma integrable_on_div_iff [simp]:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. f x / c) integrable_on A \<longleftrightarrow> f integrable_on A"
sorry

lemma has_integral_cmul: "(f has_integral k) S \<Longrightarrow> ((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R k)) S"
sorry

lemma has_integral_cmult_real:
  fixes c :: real
  assumes "c \<noteq> 0 \<Longrightarrow> (f has_integral x) A"
  shows "((\<lambda>x. c * f x) has_integral c * x) A"
sorry

lemma has_integral_neg: "(f has_integral k) S \<Longrightarrow> ((\<lambda>x. -(f x)) has_integral -k) S"
sorry

lemma has_integral_neg_iff: "((\<lambda>x. - f x) has_integral k) S \<longleftrightarrow> (f has_integral - k) S"
sorry

lemma has_integral_add_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k) (cbox a b)" "(g has_integral l) (cbox a b)"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) (cbox a b)"
sorry

lemma has_integral_add:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral k) S" and g: "(g has_integral l) S"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) S"
sorry

lemma has_integral_diff:
  "(f has_integral k) S \<Longrightarrow> (g has_integral l) S \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_integral (k - l)) S"
sorry

lemma integral_0 [simp]:
  "integral S (\<lambda>x::'n::euclidean_space. 0::'m::real_normed_vector) = 0"
sorry

lemma integral_add: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow>
    integral S (\<lambda>x. f x + g x) = integral S f + integral S g"
sorry

lemma integral_cmul [simp]: "integral S (\<lambda>x. c *\<^sub>R f x) = c *\<^sub>R integral S f"
sorry

lemma integral_mult:
  fixes K::real
  shows "f integrable_on X \<Longrightarrow> K * integral X f = integral X (\<lambda>x. K * f x)"
sorry

lemma integral_neg [simp]: "integral S (\<lambda>x. - f x) = - integral S f"
sorry

lemma integral_diff: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow>
    integral S (\<lambda>x. f x - g x) = integral S f - integral S g"
sorry

lemma integrable_0: "(\<lambda>x. 0) integrable_on S"
sorry

lemma integrable_add: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow> (\<lambda>x. f x + g x) integrable_on S"
sorry

lemma integrable_cmul: "f integrable_on S \<Longrightarrow> (\<lambda>x. c *\<^sub>R f(x)) integrable_on S"
sorry

lemma integrable_on_scaleR_iff [simp]:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c *\<^sub>R f x) integrable_on S \<longleftrightarrow> f integrable_on S"
sorry

lemma integrable_on_cmult_iff [simp]:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c * f x) integrable_on S \<longleftrightarrow> f integrable_on S"
sorry

lemma integrable_on_cmult_left:
  assumes "f integrable_on S"
  shows "(\<lambda>x. of_real c * f x) integrable_on S"
sorry

lemma integrable_neg: "f integrable_on S \<Longrightarrow> (\<lambda>x. -f(x)) integrable_on S"
sorry

lemma integrable_neg_iff: "(\<lambda>x. -f(x)) integrable_on S \<longleftrightarrow> f integrable_on S"
sorry

lemma integrable_diff:
  "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow> (\<lambda>x. f x - g x) integrable_on S"
sorry

lemma integrable_linear:
  "f integrable_on S \<Longrightarrow> bounded_linear h \<Longrightarrow> (h \<circ> f) integrable_on S"
sorry

lemma integral_linear:
  "f integrable_on S \<Longrightarrow> bounded_linear h \<Longrightarrow> integral S (h \<circ> f) = h (integral S f)"
sorry

lemma integrable_on_cnj_iff:
  "(\<lambda>x. cnj (f x)) integrable_on A \<longleftrightarrow> f integrable_on A"
sorry

lemma integral_cnj: "cnj (integral A f) = integral A (\<lambda>x. cnj (f x))"
sorry

lemma has_integral_cnj: "(cnj \<circ> f has_integral (cnj I)) A  = (f has_integral I) A"
sorry

lemma integral_component_eq[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on S"
  shows "integral S (\<lambda>x. f x \<bullet> k) = integral S f \<bullet> k"
sorry

lemma has_integral_sum:
  assumes "finite T"
    and "\<And>a. a \<in> T \<Longrightarrow> ((f a) has_integral (i a)) S"
  shows "((\<lambda>x. sum (\<lambda>a. f a x) T) has_integral (sum i T)) S"
sorry

lemma integral_sum:
  "\<lbrakk>finite I;  \<And>a. a \<in> I \<Longrightarrow> f a integrable_on S\<rbrakk> \<Longrightarrow>
   integral S (\<lambda>x. \<Sum>a\<in>I. f a x) = (\<Sum>a\<in>I. integral S (f a))"
sorry

lemma integrable_sum:
  "\<lbrakk>finite I;  \<And>a. a \<in> I \<Longrightarrow> f a integrable_on S\<rbrakk> \<Longrightarrow> (\<lambda>x. \<Sum>a\<in>I. f a x) integrable_on S"
sorry

lemma has_integral_eq:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
    and f: "(f has_integral k) s"
  shows "(g has_integral k) s"
sorry

lemma integrable_eq: "\<lbrakk>f integrable_on s; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g integrable_on s"
sorry

lemma has_integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(f has_integral i) s = (g has_integral i) s"
sorry

lemma integrable_cong:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows   "f integrable_on A \<longleftrightarrow> g integrable_on A"
sorry

lemma integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "integral s f = integral s g"
sorry

lemma integrable_on_cmult_left_iff [simp]:
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. of_real c * f x) integrable_on s \<longleftrightarrow> f integrable_on s"
        (is "?lhs = ?rhs")
sorry

lemma integrable_on_cmult_right:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "f integrable_on s"
  shows "(\<lambda>x. f x * of_real c) integrable_on s"
sorry

lemma integrable_on_cmult_right_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x * of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
sorry

lemma integrable_on_cdivide_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_field"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x / of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
sorry

lemma has_integral_null [intro]: "content(cbox a b) = 0 \<Longrightarrow> (f has_integral 0) (cbox a b)"
sorry

lemma has_integral_null_real [intro]: "content {a..b::real} = 0 \<Longrightarrow> (f has_integral 0) {a..b}"
sorry

lemma has_integral_null_eq[simp]: "content (cbox a b) = 0 \<Longrightarrow> (f has_integral i) (cbox a b) \<longleftrightarrow> i = 0"
sorry

lemma integral_null [simp]: "content (cbox a b) = 0 \<Longrightarrow> integral (cbox a b) f = 0"
sorry

lemma integrable_on_null [intro]: "content (cbox a b) = 0 \<Longrightarrow> f integrable_on (cbox a b)"
sorry

lemma has_integral_empty[intro]: "(f has_integral 0) {}"
sorry

lemma has_integral_empty_eq[simp]: "(f has_integral i) {} \<longleftrightarrow> i = 0"
sorry

lemma integrable_on_empty[intro]: "f integrable_on {}"
sorry

lemma integral_empty[simp]: "integral {} f = 0"
sorry

lemma has_integral_refl[intro]:
  fixes a :: "'a::euclidean_space"
  shows "(f has_integral 0) (cbox a a)"
    and "(f has_integral 0) {a}"
sorry

lemma integrable_on_refl[intro]: "f integrable_on cbox a a"
sorry

lemma integral_refl [simp]: "integral (cbox a a) f = 0"
sorry

lemma integral_singleton [simp]: "integral {a} f = 0"
sorry

lemma integral_blinfun_apply:
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. blinfun_apply h (f x)) = blinfun_apply h (integral s f)"
sorry

lemma blinfun_apply_integral:
  assumes "f integrable_on s"
  shows "blinfun_apply (integral s f) x = integral s (\<lambda>y. blinfun_apply (f y) x)"
sorry

lemma has_integral_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(f has_integral y) A \<longleftrightarrow> (\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
sorry

lemma has_integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A) \<Longrightarrow> (f has_integral y) A"
sorry

lemma integrable_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "f integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)"
sorry

lemma integrable_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> b) integrable_on A) \<Longrightarrow> f integrable_on A"
sorry

lemma integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A"
  shows "integral A f = (\<Sum>b\<in>Basis. integral A (\<lambda>x. (f x \<bullet> b) *\<^sub>R b))"
sorry

lemma integrable_component:
  "f integrable_on A \<Longrightarrow> (\<lambda>x. f x \<bullet> (y :: 'b :: euclidean_space)) integrable_on A"
sorry
subsection \<open>Cauchy-type criterion for integrability\<close>

proposition integrable_Cauchy:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::{real_normed_vector,complete_space}"
  shows "f integrable_on cbox a b \<longleftrightarrow>
        (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
          (\<forall>\<D>1 \<D>2. \<D>1 tagged_division_of (cbox a b) \<and> \<gamma> fine \<D>1 \<and>
            \<D>2 tagged_division_of (cbox a b) \<and> \<gamma> fine \<D>2 \<longrightarrow>
            norm ((\<Sum>(x,K)\<in>\<D>1. content K *\<^sub>R f x) - (\<Sum>(x,K)\<in>\<D>2. content K *\<^sub>R f x)) < e))"
  (is "?l = (\<forall>e>0. \<exists>\<gamma>. ?P e \<gamma>)")
sorry



subsection \<open>Additivity of integral on abutting intervals\<close>

lemma tagged_division_split_left_inj_content:
  assumes \<D>: "\<D> tagged_division_of S"
    and "(x1, K1) \<in> \<D>" "(x2, K2) \<in> \<D>" "K1 \<noteq> K2" "K1 \<inter> {x. x\<bullet>k \<le> c} = K2 \<inter> {x. x\<bullet>k \<le> c}" "k \<in> Basis"
  shows "content (K1 \<inter> {x. x\<bullet>k \<le> c}) = 0"
sorry

lemma tagged_division_split_right_inj_content:
  assumes \<D>: "\<D> tagged_division_of S"
    and "(x1, K1) \<in> \<D>" "(x2, K2) \<in> \<D>" "K1 \<noteq> K2" "K1 \<inter> {x. x\<bullet>k \<ge> c} = K2 \<inter> {x. x\<bullet>k \<ge> c}" "k \<in> Basis"
  shows "content (K1 \<inter> {x. x\<bullet>k \<ge> c}) = 0"
sorry

proposition has_integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes fi: "(f has_integral i) (cbox a b \<inter> {x. x\<bullet>k \<le> c})"
      and fj: "(f has_integral j) (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
      and k: "k \<in> Basis"
shows "(f has_integral (i + j)) (cbox a b)"
sorry
subsection \<open>A sort of converse, integrability on subintervals\<close>

lemma has_integral_separate_sides:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes f: "(f has_integral i) (cbox a b)"
    and "e > 0"
    and k: "k \<in> Basis"
  obtains d where "gauge d"
    "\<forall>p1 p2. p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) \<and> d fine p2 \<longrightarrow>
        norm ((sum (\<lambda>(x,k). content k *\<^sub>R f x) p1 + sum (\<lambda>(x,k). content k *\<^sub>R f x) p2) - i) < e"
sorry

lemma integrable_split [intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes f: "f integrable_on cbox a b"
      and k: "k \<in> Basis"
    shows "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<le> c})"   (is ?thesis1)
    and   "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"   (is ?thesis2)
sorry

lemma operative_integralI:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows "operative (lift_option (+)) (Some 0)
    (\<lambda>i. if f integrable_on i then Some (integral i f) else None)"
sorry


subsection \<open>Bounds on the norm of Riemann sums and the integral itself\<close>

lemma dsum_bound:
  assumes p: "p division_of (cbox a b)"
    and "norm c \<le> e"
  shows "norm (sum (\<lambda>l. content l *\<^sub>R c) p) \<le> e * content(cbox a b)"
sorry

lemma rsum_bound:
  assumes p: "p tagged_division_of (cbox a b)"
      and "\<forall>x\<in>cbox a b. norm (f x) \<le> e"
    shows "norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p) \<le> e * content (cbox a b)"
sorry

lemma rsum_diff_bound:
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e"
  shows "norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - sum (\<lambda>(x,k). content k *\<^sub>R g x) p) \<le>
         e * content (cbox a b)"
sorry

lemma has_integral_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
      and f: "(f has_integral i) (cbox a b)"
      and "\<And>x. x\<in>cbox a b \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content (cbox a b)"
sorry

corollary integrable_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
    and "f integrable_on (cbox a b)"
    and "\<And>x. x\<in>cbox a b \<Longrightarrow> norm (f x) \<le> B"
  shows "norm (integral (cbox a b) f) \<le> B * content (cbox a b)"
sorry
subsection \<open>Similar theorems about relationship among components\<close>

lemma rsum_component_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes p: "p tagged_division_of (cbox a b)"
      and "\<And>x. x \<in> cbox a b \<Longrightarrow> (f x)\<bullet>i \<le> (g x)\<bullet>i"
    shows "(\<Sum>(x, K)\<in>p. content K *\<^sub>R f x) \<bullet> i \<le> (\<Sum>(x, K)\<in>p. content K *\<^sub>R g x) \<bullet> i"
sorry

lemma has_integral_component_le:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k \<in> Basis"
  assumes "(f has_integral i) S" "(g has_integral j) S"
    and f_le_g: "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
sorry

lemma integral_component_le:
  fixes g f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "f integrable_on S" "g integrable_on S"
    and "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "(integral S f)\<bullet>k \<le> (integral S g)\<bullet>k"
sorry

lemma has_integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) S"
    and "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> i\<bullet>k"
sorry

lemma integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> (integral S f)\<bullet>k"
sorry

lemma has_integral_component_neg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) S"
    and "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> 0"
  shows "i\<bullet>k \<le> 0"
sorry

lemma has_integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> i\<bullet>k"
sorry

lemma has_integral_component_ubound:
  fixes f::"'a::euclidean_space => 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "i\<bullet>k \<le> B * content (cbox a b)"
sorry

lemma integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> (integral(cbox a b) f)\<bullet>k"
sorry

lemma integral_component_lbound_real:
  assumes "f integrable_on {a ::real..b}"
    and "\<forall>x\<in>{a..b}. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content {a..b} \<le> (integral {a..b} f)\<bullet>k"
sorry

lemma integral_component_ubound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral (cbox a b) f)\<bullet>k \<le> B * content (cbox a b)"
sorry

lemma integral_component_ubound_real:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "f integrable_on {a..b}"
    and "\<forall>x\<in>{a..b}. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral {a..b} f)\<bullet>k \<le> B * content {a..b}"
sorry
subsection \<open>Uniform limit of integrable functions is integrable\<close>

lemma real_arch_invD:
  "0 < (e::real) \<Longrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
sorry

lemma integrable_uniform_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
  shows "f integrable_on cbox a b"
sorry


lemmas integrable_uniform_limit_real = integrable_uniform_limit [where 'a=real, simplified]


subsection \<open>Negligible sets\<close>

definition "negligible (s:: 'a::euclidean_space set) \<longleftrightarrow>
  (\<forall>a b. ((indicator s :: 'a\<Rightarrow>real) has_integral 0) (cbox a b))"


subsubsection \<open>Negligibility of hyperplane\<close>

lemma content_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "0 < e"
    and k: "k \<in> Basis"
  obtains d where "0 < d" and "content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d}) < e"
sorry

proposition negligible_standard_hyperplane[intro]:
  fixes k :: "'a::euclidean_space"
  assumes k: "k \<in> Basis"
  shows "negligible {x. x\<bullet>k = c}"
sorry

corollary negligible_standard_hyperplane_cart:
  fixes k :: "'a::finite"
  shows "negligible {x. x$k = (0::real)}"
sorry
subsubsection \<open>Hence the main theorem about negligible sets\<close>


lemma has_integral_negligible_cbox:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes negs: "negligible S"
    and 0: "\<And>x. x \<notin> S \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) (cbox a b)"
sorry

proposition has_integral_negligible:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes negs: "negligible S"
    and "\<And>x. x \<in> (T - S) \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) T"
sorry

lemma
  assumes "negligible S"
  shows integrable_negligible: "f integrable_on S" and integral_negligible: "integral S f = 0"
sorry

lemma has_integral_spike:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible S"
    and gf: "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and fint: "(f has_integral y) T"
  shows "(g has_integral y) T"
sorry

lemma has_integral_spike_eq:
  assumes "negligible S" and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "(f has_integral y) T \<longleftrightarrow> (g has_integral y) T"
sorry

lemma integrable_spike:
  assumes "f integrable_on T" "negligible S" "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    shows "g integrable_on T"
sorry

lemma integral_spike:
  assumes "negligible S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "integral T f = integral T g"
sorry
subsection \<open>Some other trivialities about negligible sets\<close>

lemma negligible_subset:
  assumes "negligible s" "t \<subseteq> s"
  shows "negligible t"
sorry

lemma negligible_diff[intro?]:
  assumes "negligible s"
  shows "negligible (s - t)"
sorry

lemma negligible_Int:
  assumes "negligible s \<or> negligible t"
  shows "negligible (s \<inter> t)"
sorry

lemma negligible_Un:
  assumes "negligible S" and T: "negligible T"
  shows "negligible (S \<union> T)"
sorry

lemma negligible_Un_eq[simp]: "negligible (s \<union> t) \<longleftrightarrow> negligible s \<and> negligible t"
sorry

lemma negligible_sing[intro]: "negligible {a::'a::euclidean_space}"
sorry

lemma negligible_insert[simp]: "negligible (insert a s) \<longleftrightarrow> negligible s"
sorry

lemma negligible_empty[iff]: "negligible {}"
sorry
text\<open>Useful in this form for backchaining\<close>
lemma empty_imp_negligible: "S = {} \<Longrightarrow> negligible S"
sorry

lemma negligible_finite[intro]:
  assumes "finite s"
  shows "negligible s"
sorry

lemma negligible_Union[intro]:
  assumes "finite \<T>"
    and "\<And>t. t \<in> \<T> \<Longrightarrow> negligible t"
  shows "negligible(\<Union>\<T>)"
sorry

lemma negligible: "negligible S \<longleftrightarrow> (\<forall>T. (indicat_real S has_integral 0) T)"
sorry


subsection \<open>Finite case of the spike theorem is quite commonly needed\<close>

lemma has_integral_spike_finite:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and "(f has_integral y) T"
  shows "(g has_integral y) T"
sorry

lemma has_integral_spike_finite_eq:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "((f has_integral y) T \<longleftrightarrow> (g has_integral y) T)"
sorry

lemma integrable_spike_finite:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and "f integrable_on T"
  shows "g integrable_on T"
sorry

lemma integrable_spike_finite_eq:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> f x = g x"
  shows "f integrable_on T \<longleftrightarrow> g integrable_on T"
sorry

lemma has_integral_bound_spike_finite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B" "finite S"
      and f: "(f has_integral i) (cbox a b)"
      and leB: "\<And>x. x \<in> cbox a b - S \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content (cbox a b)"
sorry

corollary has_integral_bound_real:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B" "finite S"
      and "(f has_integral i) {a..b}"
      and "\<And>x. x \<in> {a..b} - S \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content {a..b}"
sorry
subsection \<open>In particular, the boundary of an interval is negligible\<close>

lemma negligible_frontier_interval: "negligible(cbox (a::'a::euclidean_space) b - box a b)"
sorry

lemma has_integral_spike_interior:
  assumes f: "(f has_integral y) (cbox a b)" and gf: "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
  shows "(g has_integral y) (cbox a b)"
sorry

lemma has_integral_spike_interior_eq:
  assumes "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
  shows "(f has_integral y) (cbox a b) \<longleftrightarrow> (g has_integral y) (cbox a b)"
sorry

lemma integrable_spike_interior:
  assumes "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
    and "f integrable_on cbox a b"
  shows "g integrable_on cbox a b"
sorry
subsection \<open>Integrability of continuous functions\<close>

lemma operative_approximableI:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "operative conj True (\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::'b)) \<le> e) \<and> g integrable_on i)"
sorry

lemma comm_monoid_set_F_and: "comm_monoid_set.F (\<and>) True f s \<longleftrightarrow> (finite s \<longrightarrow> (\<forall>x\<in>s. f x))"
sorry

lemma approximable_on_division:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
    and d: "d division_of (cbox a b)"
    and f: "\<forall>i\<in>d. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  obtains g where "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" "g integrable_on cbox a b"
sorry

lemma integrable_continuous:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on (cbox a b) f"
  shows "f integrable_on cbox a b"
sorry

lemma integrable_continuous_interval:
  fixes f :: "'b::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
  shows "f integrable_on {a..b}"
sorry
lemmas integrable_continuous_real = integrable_continuous_interval[where 'b=real]

lemma integrable_continuous_closed_segment:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
  shows "f integrable_on (closed_segment a b)"
sorry
subsection \<open>Specialization of additivity to one dimension\<close>


subsection \<open>A useful lemma allowing us to factor out the content size\<close>

lemma has_integral_factor_content:
  "(f has_integral i) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content (cbox a b)))"
sorry

lemma has_integral_factor_content_real:
  "(f has_integral i) {a..b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b}  \<and> d fine p \<longrightarrow>
      norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content {a..b} ))"
sorry
subsection \<open>Fundamental theorem of calculus\<close>

lemma interval_bounds_real:
  fixes q b :: real
  assumes "a \<le> b"
  shows "Sup {a..b} = b"
    and "Inf {a..b} = a"
sorry

theorem fundamental_theorem_of_calculus:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> b" 
      and vecd: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
sorry

lemma has_complex_derivative_imp_has_vector_derivative:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "(f has_field_derivative f') (at (of_real a) within (cbox (of_real x) (of_real y)))"
  shows "((f o of_real) has_vector_derivative f') (at a within {x..y})"
sorry

lemma ident_has_integral:
  fixes a::real
  assumes "a \<le> b"
  shows "((\<lambda>x. x) has_integral (b\<^sup>2 - a\<^sup>2)/2) {a..b}"
sorry

lemma integral_ident [simp]:
  fixes a::real
  assumes "a \<le> b"
  shows "integral {a..b} (\<lambda>x. x) = (if a \<le> b then (b\<^sup>2 - a\<^sup>2)/2 else 0)"
sorry

lemma ident_integrable_on:
  fixes a::real
  shows "(\<lambda>x. x) integrable_on {a..b}"
sorry

lemma integral_sin [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} sin = cos a - cos b"
sorry

lemma integral_cos [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} cos = sin b - sin a"
sorry

lemma integral_exp [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} exp = exp b - exp a"
sorry

lemma has_integral_sin_nx: "((\<lambda>x. sin(real_of_int n * x)) has_integral 0) {-pi..pi}"
sorry

lemma integral_sin_nx:
   "integral {-pi..pi} (\<lambda>x. sin(x * real_of_int n)) = 0"
sorry

lemma has_integral_cos_nx:
  "((\<lambda>x. cos(real_of_int n * x)) has_integral (if n = 0 then 2 * pi else 0)) {-pi..pi}"
sorry

lemma integral_cos_nx:
   "integral {-pi..pi} (\<lambda>x. cos(x * real_of_int n)) = (if n = 0 then 2 * pi else 0)"
sorry
subsection \<open>Taylor series expansion\<close>

lemma mvt_integral:
  fixes f::"'a::real_normed_vector\<Rightarrow>'b::banach"
  assumes f'[derivative_intros]:
    "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes line_in: "\<And>t. t \<in> {0..1} \<Longrightarrow> x + t *\<^sub>R y \<in> S"
  shows "f (x + y) - f x = integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) y)"
sorry

lemma (in bounded_bilinear) sum_prod_derivatives_has_vector_derivative:
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a..b})"
  and g0: "Dg 0 = g"
  and Dg: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Dg m has_vector_derivative Dg (Suc m) t) (at t within {a..b})"
  and ivl: "a \<le> t" "t \<le> b"
  shows "((\<lambda>t. \<Sum>i<p. (-1)^i *\<^sub>R prod (Df i t) (Dg (p - Suc i) t))
    has_vector_derivative
      prod (f t) (Dg p t) - (-1)^p *\<^sub>R prod (Df p t) (g t))
    (at t within {a..b})"
sorry

lemma
  fixes f::"real\<Rightarrow>'a::banach"
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a..b})"
  and ivl: "a \<le> b"
  defines "i \<equiv> \<lambda>x. ((b - x) ^ (p - 1) / fact (p - 1)) *\<^sub>R Df p x"
  shows Taylor_has_integral:
    "(i has_integral f b - (\<Sum>i<p. ((b-a) ^ i / fact i) *\<^sub>R Df i a)) {a..b}"
  and Taylor_integral:
    "f b = (\<Sum>i<p. ((b-a) ^ i / fact i) *\<^sub>R Df i a) + integral {a..b} i"
  and Taylor_integrable:
    "i integrable_on {a..b}"
sorry



subsection \<open>Only need trivial subintervals if the interval itself is trivial\<close>

proposition division_of_nontrivial:
  fixes \<D> :: "'a::euclidean_space set set"
  assumes sdiv: "\<D> division_of (cbox a b)"
     and cont0: "content (cbox a b) \<noteq> 0"
  shows "{k. k \<in> \<D> \<and> content k \<noteq> 0} division_of (cbox a b)"
sorry
subsection \<open>Integrability on subintervals\<close>

lemma operative_integrableI:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "operative conj True (\<lambda>i. f integrable_on i)"
sorry

lemma integrable_subinterval:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on cbox a b"
    and cd: "cbox c d \<subseteq> cbox a b"
  shows "f integrable_on cbox c d"
sorry

lemma integrable_subinterval_real:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
    and "{c..d} \<subseteq> {a..b}"
  shows "f integrable_on {c..d}"
sorry
subsection \<open>Combining adjacent intervals in 1 dimension\<close>

lemma has_integral_combine:
  fixes a b c :: real and j :: "'a::banach"
  assumes "a \<le> c"
      and "c \<le> b"
      and ac: "(f has_integral i) {a..c}"
      and cb: "(f has_integral j) {c..b}"
  shows "(f has_integral (i + j)) {a..b}"
sorry

lemma integral_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and ab: "f integrable_on {a..b}"
  shows "integral {a..c} f + integral {c..b} f = integral {a..b} f"
sorry

lemma integrable_combine:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> c"
    and "c \<le> b"
    and "f integrable_on {a..c}"
    and "f integrable_on {c..b}"
  shows "f integrable_on {a..b}"
sorry

lemma integral_minus_sets:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "c \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> f integrable_on {c .. max a b} \<Longrightarrow>
    integral {c .. a} f - integral {c .. b} f =
    (if a \<le> b then - integral {a .. b} f else integral {b .. a} f)"
sorry

lemma integral_minus_sets':
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "c \<ge> a \<Longrightarrow> c \<ge> b \<Longrightarrow> f integrable_on {min a b .. c} \<Longrightarrow>
    integral {a .. c} f - integral {b .. c} f =
    (if a \<le> b then integral {a .. b} f else - integral {b .. a} f)"
sorry
subsection \<open>Reduce integrability to "local" integrability\<close>

lemma integrable_on_little_subintervals:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<forall>x\<in>cbox a b. \<exists>d>0. \<forall>u v. x \<in> cbox u v \<and> cbox u v \<subseteq> ball x d \<and> cbox u v \<subseteq> cbox a b \<longrightarrow>
    f integrable_on cbox u v"
  shows "f integrable_on cbox a b"
sorry



subsection \<open>Second FTC or existence of antiderivative\<close>

lemma integrable_const[intro]: "(\<lambda>x. c) integrable_on cbox a b"
sorry

lemma integral_has_vector_derivative_continuous_at:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on {a..b}"
     and x: "x \<in> {a..b} - S"
     and "finite S"
     and fx: "continuous (at x within ({a..b} - S)) f"
 shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f x) (at x within ({a..b} - S))"
sorry

lemma integral_has_vector_derivative:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
    and "x \<in> {a..b}"
  shows "((\<lambda>u. integral {a..u} f) has_vector_derivative f(x)) (at x within {a..b})"
sorry

lemma integral_has_real_derivative:
  assumes "continuous_on {a..b} g"
  assumes "t \<in> {a..b}"
  shows "((\<lambda>x. integral {a..x} g) has_real_derivative g t) (at t within {a..b})"
sorry

lemma antiderivative_continuous:
  fixes q b :: real
  assumes "continuous_on {a..b} f"
  obtains g where "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative (f x::_::banach)) (at x within {a..b})"
sorry
subsection \<open>Combined fundamental theorem of calculus\<close>

lemma antiderivative_integral_continuous:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
  obtains g where "\<forall>u\<in>{a..b}. \<forall>v \<in> {a..b}. u \<le> v \<longrightarrow> (f has_integral (g v - g u)) {u..v}"
sorry



subsection \<open>General "twiddling" for interval-to-interval function image\<close>

lemma has_integral_twiddle:
  assumes "0 < r"
    and hg: "\<And>x. h(g x) = x"
    and gh: "\<And>x. g(h x) = x"
    and contg: "\<And>x. continuous (at x) g"
    and g: "\<And>u v. \<exists>w z. g ` cbox u v = cbox w z"
    and h: "\<And>u v. \<exists>w z. h ` cbox u v = cbox w z"
    and r: "\<And>u v. content(g ` cbox u v) = r * content (cbox u v)"
    and intfi: "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(g x)) has_integral (1 / r) *\<^sub>R i) (h ` cbox a b)"
sorry



subsection \<open>Special case of a basic affine transformation\<close>

lemma AE_lborel_inner_neq:
  assumes k: "k \<in> Basis"
  shows "AE x in lborel. x \<bullet> k \<noteq> c"
sorry

lemma content_image_stretch_interval:
  fixes m :: "'a::euclidean_space \<Rightarrow> real"
  defines "s f x \<equiv> (\<Sum>k::'a\<in>Basis. (f k * (x\<bullet>k)) *\<^sub>R k)"
  shows "content (s m ` cbox a b) = \<bar>\<Prod>k\<in>Basis. m k\<bar> * content (cbox a b)"
sorry

lemma interval_image_affinity_interval:
  "\<exists>u v. (\<lambda>x. m *\<^sub>R (x::'a::euclidean_space) + c) ` cbox a b = cbox u v"
sorry

lemma content_image_affinity_cbox:
  "content((\<lambda>x::'a::euclidean_space. m *\<^sub>R x + c) ` cbox a b) =
    \<bar>m\<bar> ^ DIM('a) * content (cbox a b)" (is "?l = ?r")
sorry

lemma has_integral_affinity:
  fixes a :: "'a::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
      and "m \<noteq> 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral (1 / (\<bar>m\<bar> ^ DIM('a))) *\<^sub>R i) ((\<lambda>x. (1 / m) *\<^sub>R x + -((1 / m) *\<^sub>R c)) ` cbox a b)"
sorry

lemma integrable_affinity:
  assumes "f integrable_on cbox a b"
    and "m \<noteq> 0"
  shows "(\<lambda>x. f(m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x + -((1/m) *\<^sub>R c)) ` cbox a b)"
sorry
lemmas has_integral_affinity01 = has_integral_affinity [of _ _ 0 "1::real", simplified]

lemma integrable_on_affinity:
  assumes "m \<noteq> 0" "f integrable_on (cbox a b)"
  shows   "(\<lambda>x. f (m *\<^sub>R x + c)) integrable_on ((\<lambda>x. (1 / m) *\<^sub>R x - ((1 / m) *\<^sub>R c)) ` cbox a b)"
sorry

lemma has_integral_cmul_iff:
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R I)) A \<longleftrightarrow> (f has_integral I) A"
sorry

lemma has_integral_cmul_iff':
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_integral I) A \<longleftrightarrow> (f has_integral I /\<^sub>R c) A"
sorry

lemma has_integral_affinity':
  fixes a :: "'a::euclidean_space"
  assumes "(f has_integral i) (cbox a b)" and "m > 0"
  shows "((\<lambda>x. f(m *\<^sub>R x + c)) has_integral (i /\<^sub>R m ^ DIM('a)))
           (cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m))"
sorry

lemma has_integral_affinity_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: real_normed_vector"
  assumes "m > 0"
  shows   "((\<lambda>x. f (m *\<^sub>R x + c)) has_integral (I /\<^sub>R m ^ DIM('a)))
               (cbox ((a - c) /\<^sub>R m) ((b - c) /\<^sub>R m)) \<longleftrightarrow>
           (f has_integral I) (cbox a b)" (is "?lhs = ?rhs")
sorry



subsection \<open>Special case of stretching coordinate axes separately\<close>

lemma has_integral_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "((\<lambda>x. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) has_integral
         ((1/ \<bar>prod m Basis\<bar>) *\<^sub>R i)) ((\<lambda>x. (\<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k)) ` cbox a b)"
sorry

lemma has_integral_stretch_real:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "(f has_integral i) {a..b}" and "m \<noteq> 0"
  shows "((\<lambda>x. f (m * x)) has_integral (1 / \<bar>m\<bar>) *\<^sub>R i) ((\<lambda>x. x / m) ` {a..b})"
sorry

lemma integrable_stretch:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "f integrable_on cbox a b"
    and "\<forall>k\<in>Basis. m k \<noteq> 0"
  shows "(\<lambda>x::'a. f (\<Sum>k\<in>Basis. (m k * (x\<bullet>k))*\<^sub>R k)) integrable_on
    ((\<lambda>x. \<Sum>k\<in>Basis. (1 / m k * (x\<bullet>k))*\<^sub>R k) ` cbox a b)"
sorry

lemma vec_lambda_eq_sum:
     "(\<chi> k. f k (x $ k)) = (\<Sum>k\<in>Basis. (f (axis_index k) (x \<bullet> k)) *\<^sub>R k)" (is "?lhs = ?rhs")
sorry

lemma has_integral_stretch_cart:
  fixes m :: "'n::finite \<Rightarrow> real"
  assumes f: "(f has_integral i) (cbox a b)" and m: "\<And>k. m k \<noteq> 0"
  shows "((\<lambda>x. f(\<chi> k. m k * x$k)) has_integral i /\<^sub>R \<bar>prod m UNIV\<bar>)
            ((\<lambda>x. \<chi> k. x$k / m k) ` (cbox a b))"
sorry

lemma image_stretch_interval_cart:
  fixes m :: "'n::finite \<Rightarrow> real"
  shows "(\<lambda>x. \<chi> k. m k * x$k) ` cbox a b =
            (if cbox a b = {} then {}
            else cbox (\<chi> k. min (m k * a$k) (m k * b$k)) (\<chi> k. max (m k * a$k) (m k * b$k)))"
sorry



subsection \<open>even more special cases\<close>

lemma uminus_interval_vector[simp]:
  fixes a b :: "'a::euclidean_space"
  shows "uminus ` cbox a b = cbox (-b) (-a)"
sorry

lemma has_integral_reflect_lemma[intro]:
  assumes "(f has_integral i) (cbox a b)"
  shows "((\<lambda>x. f(-x)) has_integral i) (cbox (-b) (-a))"
sorry

lemma has_integral_reflect_lemma_real[intro]:
  assumes "(f has_integral i) {a..b::real}"
  shows "((\<lambda>x. f(-x)) has_integral i) {-b .. -a}"
sorry

lemma has_integral_reflect[simp]:
  "((\<lambda>x. f (-x)) has_integral i) (cbox (-b) (-a)) \<longleftrightarrow> (f has_integral i) (cbox a b)"
sorry

lemma has_integral_reflect_real[simp]:
  fixes a b::real
  shows "((\<lambda>x. f (-x)) has_integral i) {-b..-a} \<longleftrightarrow> (f has_integral i) {a..b}"
sorry

lemma integrable_reflect[simp]: "(\<lambda>x. f(-x)) integrable_on cbox (-b) (-a) \<longleftrightarrow> f integrable_on cbox a b"
sorry

lemma integrable_reflect_real[simp]: "(\<lambda>x. f(-x)) integrable_on {-b .. -a} \<longleftrightarrow> f integrable_on {a..b::real}"
sorry

lemma integral_reflect[simp]: "integral (cbox (-b) (-a)) (\<lambda>x. f (-x)) = integral (cbox a b) f"
sorry

lemma integral_reflect_real[simp]: "integral {-b .. -a} (\<lambda>x. f (-x)) = integral {a..b::real} f"
sorry
subsection \<open>Stronger form of FCT; quite a tedious proof\<close>

lemma split_minus[simp]: "(\<lambda>(x, k). f x k) x - (\<lambda>(x, k). g x k) x = (\<lambda>(x, k). f x k - g x k) x"
sorry

theorem fundamental_theorem_of_calculus_interior:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and contf: "continuous_on {a..b} f"
    and derf: "\<And>x. x \<in> {a <..< b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
  shows "(f' has_integral (f b - f a)) {a..b}"
sorry



subsection \<open>Stronger form with finite number of exceptional points\<close>

lemma fundamental_theorem_of_calculus_interior_strong:
 fixes f :: "real \<Rightarrow> 'a::banach"
 assumes "finite S"
   and "a \<le> b" "\<And>x. x \<in> {a <..< b} - S \<Longrightarrow> (f has_vector_derivative f'(x)) (at x)"
   and "continuous_on {a .. b} f"
 shows "(f' has_integral (f b - f a)) {a .. b}"
sorry

corollary fundamental_theorem_of_calculus_strong:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite S"
    and "a \<le> b"
    and vec: "\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f'(x)) (at x)"
    and "continuous_on {a..b} f"
  shows "(f' has_integral (f b - f a)) {a..b}"
sorry

proposition indefinite_integral_continuous_left:
  fixes f:: "real \<Rightarrow> 'a::banach"
  assumes intf: "f integrable_on {a..b}" and "a < c" "c \<le> b" "e > 0"
  obtains d where "d > 0"
    and "\<forall>t. c - d < t \<and> t \<le> c \<longrightarrow> norm (integral {a..c} f - integral {a..t} f) < e"
sorry

lemma indefinite_integral_continuous_right:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
    and "a \<le> c"
    and "c < b"
    and "e > 0"
  obtains d where "0 < d"
    and "\<forall>t. c \<le> t \<and> t < c + d \<longrightarrow> norm (integral {a..c} f - integral {a..t} f) < e"
sorry

lemma indefinite_integral_continuous_1:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
  shows "continuous_on {a..b} (\<lambda>x. integral {a..x} f)"
sorry

lemma indefinite_integral_continuous_1':
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "f integrable_on {a..b}"
  shows "continuous_on {a..b} (\<lambda>x. integral {x..b} f)"
sorry

theorem integral_has_vector_derivative':
  fixes f :: "real \<Rightarrow> 'b::banach"
  assumes "continuous_on {a..b} f"
    and "x \<in> {a..b}"
  shows "((\<lambda>u. integral {u..b} f) has_vector_derivative - f x) (at x within {a..b})"
sorry

lemma integral_has_real_derivative':
  assumes "continuous_on {a..b} g"
  assumes "t \<in> {a..b}"
  shows "((\<lambda>x. integral {x..b} g) has_real_derivative -g t) (at t within {a..b})"
sorry
subsection \<open>This doesn't directly involve integration, but that gives an easy proof\<close>

lemma has_derivative_zero_unique_strong_interval:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "finite k"
    and contf: "continuous_on {a..b} f"
    and "f a = y"
    and fder: "\<And>x. x \<in> {a..b} - k \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within {a..b})"
    and x: "x \<in> {a..b}"
  shows "f x = y"
sorry



subsection \<open>Generalize a bit to any convex set\<close>

lemma has_derivative_zero_unique_strong_convex:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "convex S" "finite K"
    and contf: "continuous_on S f"
    and "c \<in> S" "f c = y"
    and derf: "\<And>x. x \<in> S - K \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within S)"
    and "x \<in> S"
  shows "f x = y"
sorry



text \<open>Also to any open connected set with finite set of exceptions. Could
 generalize to locally convex set with limpt-free set of exceptions.\<close>

lemma has_derivative_zero_unique_strong_connected:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected S"
    and "open S"
    and "finite K"
    and contf: "continuous_on S f"
    and "c \<in> S"
    and "f c = y"
    and derf: "\<And>x. x \<in> S - K \<Longrightarrow> (f has_derivative (\<lambda>h. 0)) (at x within S)"
    and "x \<in> S"
  shows "f x = y"
sorry

lemma has_derivative_zero_connected_constant_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "connected S" "open S" "finite K" "continuous_on S f"
      and "\<forall>x\<in>S-K. (f has_derivative (\<lambda>h. 0)) (at x within S)"
  shows   "f constant_on S"
sorry

lemma DERIV_zero_connected_constant_on:
  fixes f :: "'a::{real_normed_field,euclidean_space} \<Rightarrow> 'a"
  assumes *: "connected S" "open S" "finite K" "continuous_on S f"
      and 0: "\<forall>x\<in>S-K. DERIV f x :> 0"
  shows   "f constant_on S"
sorry

lemma DERIV_zero_connected_constant:
  fixes f :: "'a::{real_normed_field,euclidean_space} \<Rightarrow> 'a"
  assumes "connected S" and "open S" and "finite K" and "continuous_on S f"
      and "\<forall>x\<in>S-K. DERIV f x :> 0"
    obtains c where "\<And>x. x \<in> S \<Longrightarrow> f(x) = c"
sorry

lemma has_field_derivative_0_imp_constant_on:
  fixes f :: "'a::{real_normed_field,euclidean_space} \<Rightarrow> 'a"
  assumes "\<And>z. z \<in> S \<Longrightarrow> (f has_field_derivative 0) (at z)" and S: "connected S" "open S"
  shows   "f constant_on S"
sorry
subsection \<open>Integrating characteristic function of an interval\<close>

lemma has_integral_restrict_open_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes intf: "(f has_integral i) (cbox c d)"
    and cb: "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> box c d then f x else 0) has_integral i) (cbox a b)"
sorry

lemma has_integral_restrict_closed_subinterval:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) (cbox c d)"
    and "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b)"
sorry

lemma has_integral_restrict_closed_subintervals_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "cbox c d \<subseteq> cbox a b"
  shows "((\<lambda>x. if x \<in> cbox c d then f x else 0) has_integral i) (cbox a b) \<longleftrightarrow> (f has_integral i) (cbox c d)"
  (is "?l = ?r")
sorry



text \<open>Hence we can apply the limit process uniformly to all integrals.\<close>

lemma has_integral':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) S \<longleftrightarrow>
    (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> S then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - i) < e))"
  (is "?l \<longleftrightarrow> (\<forall>e>0. ?r e)")
sorry

lemma has_integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes fg: "(f has_integral i) S" "(g has_integral j) S"
    and le: "\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x"
  shows "i \<le> j"
sorry

lemma integral_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "f integrable_on S"
    and "g integrable_on S"
    and "\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x"
  shows "integral S f \<le> integral S g"
sorry

lemma has_integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "(f has_integral i) S" and "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> i"
sorry

lemma integral_nonneg:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes f: "f integrable_on S" and 0: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> integral S f"
sorry
text \<open>Hence a general restriction property.\<close>

lemma has_integral_restrict [simp]:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  assumes "S \<subseteq> T"
  shows "((\<lambda>x. if x \<in> S then f x else 0) has_integral i) T \<longleftrightarrow> (f has_integral i) S"
sorry

corollary has_integral_restrict_UNIV:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "((\<lambda>x. if x \<in> s then f x else 0) has_integral i) UNIV \<longleftrightarrow> (f has_integral i) s"
sorry

lemma has_integral_restrict_Int:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "((\<lambda>x. if x \<in> S then f x else 0) has_integral i) T \<longleftrightarrow> (f has_integral i) (S \<inter> T)"
sorry

lemma integral_restrict_Int:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "integral T (\<lambda>x. if x \<in> S then f x else 0) = integral (S \<inter> T) f"
sorry

lemma integrable_restrict_Int:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "(\<lambda>x. if x \<in> S then f x else 0) integrable_on T \<longleftrightarrow> f integrable_on (S \<inter> T)"
sorry

lemma has_integral_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "(f has_integral i) S"
      and "\<And>x. x \<notin> S \<Longrightarrow> f x = 0"
      and "S \<subseteq> T"
    shows "(f has_integral i) T"
sorry

lemma integrable_on_superset:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S" and "\<And>x. x \<notin> S \<Longrightarrow> f x = 0" and "S \<subseteq> t"
  shows "f integrable_on t"
sorry

lemma integral_subset_negligible:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  assumes "S \<subseteq> T" "negligible (T - S)"
  shows   "integral S f = integral T f"
sorry

lemma integral_restrict_UNIV:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "integral UNIV (\<lambda>x. if x \<in> S then f x else 0) = integral S f"
sorry

lemma integrable_restrict_UNIV:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(\<lambda>x. if x \<in> s then f x else 0) integrable_on UNIV \<longleftrightarrow> f integrable_on s"
sorry

lemma has_integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes k: "k \<in> Basis"
    and "S \<subseteq> T" "(f has_integral i) S" "(f has_integral j) T" "\<And>x. x\<in>T \<Longrightarrow> 0 \<le> f(x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
sorry


subsection\<open>Integrals on set differences\<close>

lemma has_integral_setdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes S: "(f has_integral i) S" and T: "(f has_integral j) T"
    and neg: "negligible (T - S)"
  shows "(f has_integral (i - j)) (S - T)"
sorry

lemma integral_setdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "f integrable_on S" "f integrable_on T" "negligible(T - S)"
 shows "integral (S - T) f = integral S f - integral T f"
sorry

lemma integrable_setdiff:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "(f has_integral i) S" "(f has_integral j) T" "negligible (T - S)"
  shows "f integrable_on (S - T)"
sorry

lemma negligible_setdiff [simp]: "T \<subseteq> S \<Longrightarrow> negligible (T - S)"
sorry

lemma negligible_on_intervals: "negligible s \<longleftrightarrow> (\<forall>a b. negligible(s \<inter> cbox a b))" (is "?l \<longleftrightarrow> ?r")
sorry

lemma negligible_translation:
  assumes "negligible S"
    shows "negligible ((+) c ` S)"
sorry

lemma negligible_translation_rev:
  assumes "negligible ((+) c ` S)"
  shows "negligible S"
sorry

lemma negligible_atLeastAtMostI: "b \<le> a \<Longrightarrow> negligible {a..(b::real)}"
sorry

lemma has_integral_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "(f has_integral y) S \<longleftrightarrow> (f has_integral y) T"
sorry

corollary integral_spike_set:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "integral S f = integral T f"
sorry

lemma integrable_spike_set:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on S" and neg: "negligible {x \<in> S - T. f x \<noteq> 0}" "negligible {x \<in> T - S. f x \<noteq> 0}"
  shows "f integrable_on T"
sorry

lemma integrable_spike_set_eq:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "negligible ((S - T) \<union> (T - S))"
  shows "f integrable_on S \<longleftrightarrow> f integrable_on T"
sorry

lemma integrable_on_insert_iff: "f integrable_on (insert x X) \<longleftrightarrow> f integrable_on X"
  for f::"_ \<Rightarrow> 'a::banach"
sorry

lemma has_integral_interior:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "negligible(frontier S) \<Longrightarrow> (f has_integral y) (interior S) \<longleftrightarrow> (f has_integral y) S"
sorry

lemma has_integral_closure:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "negligible(frontier S) \<Longrightarrow> (f has_integral y) (closure S) \<longleftrightarrow> (f has_integral y) S"
sorry

lemma has_integral_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "(f has_integral y) (box a b) \<longleftrightarrow> (f has_integral y) (cbox a b)"
sorry

lemma integrable_on_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "f integrable_on box a b \<longleftrightarrow> f integrable_on cbox a b"
sorry

lemma integral_open_interval:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  shows "integral(box a b) f = integral(cbox a b) f"
sorry

lemma integrable_on_open_interval_real:
  fixes f :: "real \<Rightarrow> 'b :: banach"
  shows "f integrable_on {a<..<b} \<longleftrightarrow> f integrable_on {a..b}"
sorry

lemma integral_open_interval_real:
  "integral {a..b} (f :: real \<Rightarrow> 'a :: banach) = integral {a<..<(b::real)} f"
sorry

lemma has_integral_Icc_iff_Ioo:
  fixes f :: "real \<Rightarrow> 'a :: banach"
  shows "(f has_integral I) {a..b} \<longleftrightarrow> (f has_integral I) {a<..<b}"
sorry

lemma integrable_on_Icc_iff_Ioo:
  fixes f :: "real \<Rightarrow> 'a :: banach"
  shows "f integrable_on {a..b} \<longleftrightarrow> f integrable_on {a<..<b}"
sorry
subsection \<open>More lemmas that are useful later\<close>

lemma has_integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "(f has_integral i) s"
    and "(f has_integral j) t"
    and "\<forall>x\<in>t. 0 \<le> f x"
  shows "i \<le> j"
sorry

lemma integral_subset_component_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "k \<in> Basis"
    and "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x \<bullet> k"
  shows "(integral s f)\<bullet>k \<le> (integral t f)\<bullet>k"
sorry

lemma integral_subset_le:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "s \<subseteq> t"
    and "f integrable_on s"
    and "f integrable_on t"
    and "\<forall>x \<in> t. 0 \<le> f x"
  shows "integral s f \<le> integral t f"
sorry

lemma has_integral_alt':
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "(f has_integral i) s \<longleftrightarrow> 
          (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
          (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
            norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - i) < e)"
  (is "?l = ?r")
sorry



subsection \<open>Continuity of the integral (for a 1-dimensional interval)\<close>

lemma integrable_alt:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  shows "f integrable_on s \<longleftrightarrow>
    (\<forall>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b) \<and>
    (\<forall>e>0. \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
    norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) -
      integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e)"
  (is "?l = ?r")
sorry

lemma integrable_altD:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on s"
  shows "\<And>a b. (\<lambda>x. if x \<in> s then f x else 0) integrable_on cbox a b"
    and "\<And>e. e > 0 \<Longrightarrow> \<exists>B>0. \<forall>a b c d. ball 0 B \<subseteq> cbox a b \<and> ball 0 B \<subseteq> cbox c d \<longrightarrow>
      norm (integral (cbox a b) (\<lambda>x. if x \<in> s then f x else 0) - integral (cbox c d)  (\<lambda>x. if x \<in> s then f x else 0)) < e"
sorry

lemma integrable_alt_subset:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows
     "f integrable_on S \<longleftrightarrow>
      (\<forall>a b. (\<lambda>x. if x \<in> S then f x else 0) integrable_on cbox a b) \<and>
      (\<forall>e>0. \<exists>B>0. \<forall>a b c d.
                      ball 0 B \<subseteq> cbox a b \<and> cbox a b \<subseteq> cbox c d
                      \<longrightarrow> norm(integral (cbox a b) (\<lambda>x. if x \<in> S then f x else 0) -
                               integral (cbox c d) (\<lambda>x. if x \<in> S then f x else 0)) < e)"
      (is "_ = ?rhs")
sorry

lemma integrable_on_subcbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes intf: "f integrable_on S"
    and sub: "cbox a b \<subseteq> S"
  shows "f integrable_on cbox a b"
sorry



subsection \<open>A straddling criterion for integrability\<close>

lemma integrable_straddle_interval:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>g h i j. (g has_integral i) (cbox a b) \<and> (h has_integral j) (cbox a b) \<and>
                            \<bar>i - j\<bar> < e \<and> (\<forall>x\<in>cbox a b. (g x) \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on cbox a b"
sorry

lemma integrable_straddle:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>g h i j. (g has_integral i) s \<and> (h has_integral j) s \<and>
                     \<bar>i - j\<bar> < e \<and> (\<forall>x\<in>s. g x \<le> f x \<and> f x \<le> h x)"
  shows "f integrable_on s"
sorry



subsection \<open>Adding integrals over several sets\<close>

lemma has_integral_Un:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "(f has_integral i) S" "(f has_integral j) T"
    and neg: "negligible (S \<inter> T)"
  shows "(f has_integral (i + j)) (S \<union> T)"
sorry

lemma integral_Un [simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S" "f integrable_on T" "negligible (S \<inter> T)"
  shows "integral (S \<union> T) f = integral S f + integral T f"
sorry

lemma integrable_Un:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: banach"
  assumes "negligible (A \<inter> B)" "f integrable_on A" "f integrable_on B"
  shows   "f integrable_on (A \<union> B)"
sorry

lemma integrable_Un':
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: banach"
  assumes "f integrable_on A" "f integrable_on B" "negligible (A \<inter> B)" "C = A \<union> B"
  shows   "f integrable_on C"
sorry

lemma has_integral_UN:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "finite I"
    and int: "\<And>i. i \<in> I \<Longrightarrow> (f has_integral (g i)) (\<T> i)"
    and neg: "pairwise (\<lambda>i i'. negligible (\<T> i \<inter> \<T> i')) I"
  shows "(f has_integral (sum g I)) (\<Union>i\<in>I. \<T> i)"
sorry

lemma has_integral_Union:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "finite \<T>"
    and "\<And>S. S \<in> \<T> \<Longrightarrow> (f has_integral (i S)) S"
    and "pairwise (\<lambda>S S'. negligible (S \<inter> S')) \<T>"
  shows "(f has_integral (sum i \<T>)) (\<Union>\<T>)"
sorry


text \<open>In particular adding integrals over a division, maybe not of an interval.\<close>

lemma has_integral_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<D> division_of S"
    and "\<And>k. k \<in> \<D> \<Longrightarrow> (f has_integral (i k)) k"
  shows "(f has_integral (sum i \<D>)) S"
sorry

lemma integral_combine_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "\<D> division_of S" "\<And>k. k \<in> \<D> \<Longrightarrow> f integrable_on k"
  shows "integral S f = sum (\<lambda>i. integral i f) \<D>"
sorry

lemma has_integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on S"
    and \<D>: "\<D> division_of K"
    and "K \<subseteq> S"
  shows "(f has_integral (sum (\<lambda>i. integral i f) \<D>)) K"
sorry

lemma integral_combine_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S"
    and "\<D> division_of S"
  shows "integral S f = sum (\<lambda>i. integral i f) \<D>"
sorry

lemma integrable_combine_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes \<D>: "\<D> division_of S"
    and f: "\<And>i. i \<in> \<D> \<Longrightarrow> f integrable_on i"
  shows "f integrable_on S"
sorry

lemma integrable_on_subdivision:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes \<D>: "\<D> division_of i"
    and f: "f integrable_on S"
    and "i \<subseteq> S"
  shows "f integrable_on i"
sorry



subsection \<open>Also tagged divisions\<close>

lemma has_integral_combine_tagged_division:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "p tagged_division_of S"
    and "\<And>x k. (x,k) \<in> p \<Longrightarrow> (f has_integral (i k)) k"
  shows "(f has_integral (\<Sum>(x,k)\<in>p. i k)) S"
sorry

lemma integral_combine_tagged_division_bottomup:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes p: "p tagged_division_of (cbox a b)"
    and f: "\<And>x k. (x,k)\<in>p \<Longrightarrow> f integrable_on k"
  shows "integral (cbox a b) f = sum (\<lambda>(x,k). integral k f) p"
sorry

lemma has_integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes f: "f integrable_on cbox a b"
    and p: "p tagged_division_of (cbox a b)"
  shows "(f has_integral (sum (\<lambda>(x,K). integral K f) p)) (cbox a b)"
sorry

lemma integral_combine_tagged_division_topdown:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on cbox a b"
    and "p tagged_division_of (cbox a b)"
  shows "integral (cbox a b) f = sum (\<lambda>(x,k). integral k f) p"
sorry
subsection \<open>Henstock's lemma\<close>

lemma Henstock_lemma_part1:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes intf: "f integrable_on cbox a b"
    and "e > 0"
    and "gauge d"
    and less_e: "\<And>p. \<lbrakk>p tagged_division_of (cbox a b); d fine p\<rbrakk> \<Longrightarrow>
                     norm (sum (\<lambda>(x,K). content K *\<^sub>R f x) p - integral(cbox a b) f) < e"
    and p: "p tagged_partial_division_of (cbox a b)" "d fine p"
  shows "norm (sum (\<lambda>(x,K). content K *\<^sub>R f x - integral K f) p) \<le> e" (is "?lhs \<le> e")
sorry

lemma Henstock_lemma_part2:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes fed: "f integrable_on cbox a b" "e > 0" "gauge d"
    and less_e: "\<And>\<D>. \<lbrakk>\<D> tagged_division_of (cbox a b); d fine \<D>\<rbrakk> \<Longrightarrow>
                     norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) \<D> - integral (cbox a b) f) < e"
    and tag: "p tagged_partial_division_of (cbox a b)"
    and "d fine p"
  shows "sum (\<lambda>(x,k). norm (content k *\<^sub>R f x - integral k f)) p \<le> 2 * real (DIM('n)) * e"
sorry

lemma Henstock_lemma:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::euclidean_space"
  assumes intf: "f integrable_on cbox a b"
    and "e > 0"
  obtains \<gamma> where "gauge \<gamma>"
    and "\<And>p. \<lbrakk>p tagged_partial_division_of (cbox a b); \<gamma> fine p\<rbrakk> \<Longrightarrow>
             sum (\<lambda>(x,k). norm(content k *\<^sub>R f x - integral k f)) p < e"
sorry



subsection \<open>Monotone convergence (bounded interval first)\<close>

lemma bounded_increasing_convergent:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>bounded (range f); \<And>n. f n \<le> f (Suc n)\<rbrakk> \<Longrightarrow> \<exists>l. f \<longlonglongrightarrow> l"
sorry

lemma monotone_convergence_interval:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes intf: "\<And>k. (f k) integrable_on cbox a b"
    and le: "\<And>k x. x \<in> cbox a b \<Longrightarrow> (f k x) \<le> f (Suc k) x"
    and fg: "\<And>x. x \<in> cbox a b \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and bou: "bounded (range (\<lambda>k. integral (cbox a b) (f k)))"
  shows "g integrable_on cbox a b \<and> ((\<lambda>k. integral (cbox a b) (f k)) \<longlongrightarrow> integral (cbox a b) g) sequentially"
sorry

lemma monotone_convergence_increasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes int_f: "\<And>k. (f k) integrable_on S"
    and "\<And>k x. x \<in> S \<Longrightarrow> (f k x) \<le> (f (Suc k) x)"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and bou: "bounded (range (\<lambda>k. integral S (f k)))"
  shows "g integrable_on S \<and> ((\<lambda>k. integral S (f k)) \<longlongrightarrow> integral S g) sequentially"
sorry

lemma has_integral_monotone_convergence_increasing:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes f: "\<And>k. (f k has_integral x k) s"
  assumes "\<And>k x. x \<in> s \<Longrightarrow> f k x \<le> f (Suc k) x"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (\<lambda>k. f k x) \<longlonglongrightarrow> g x"
  assumes "x \<longlonglongrightarrow> x'"
  shows "(g has_integral x') s"
sorry

lemma monotone_convergence_decreasing:
  fixes f :: "nat \<Rightarrow> 'n::euclidean_space \<Rightarrow> real"
  assumes intf: "\<And>k. (f k) integrable_on S"
    and le: "\<And>k x. x \<in> S \<Longrightarrow> f (Suc k) x \<le> f k x"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>k. f k x) \<longlongrightarrow> g x) sequentially"
    and bou: "bounded (range(\<lambda>k. integral S (f k)))"
  shows "g integrable_on S \<and> (\<lambda>k. integral S (f k)) \<longlonglongrightarrow> integral S g"
sorry

lemma integral_norm_bound_integral:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  assumes int_f: "f integrable_on S"
    and int_g: "g integrable_on S"
    and le_g: "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> g x"
  shows "norm (integral S f) \<le> integral S g"
sorry

lemma continuous_on_imp_absolutely_integrable_on:
  fixes f::"real \<Rightarrow> 'a::banach"
  shows "continuous_on {a..b} f \<Longrightarrow>
    norm (integral {a..b} f) \<le> integral {a..b} (\<lambda>x. norm (f x))"
sorry

lemma integral_bound:
  fixes f::"real \<Rightarrow> 'a::banach"
  assumes "a \<le> b"
  assumes "continuous_on {a .. b} f"
  assumes "\<And>t. t \<in> {a .. b} \<Longrightarrow> norm (f t) \<le> B"
  shows "norm (integral {a .. b} f) \<le> B * (b - a)"
sorry

lemma integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes f: "f integrable_on S" and g: "g integrable_on S"
    and fg: "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> (g x)\<bullet>k"
  shows "norm (integral S f) \<le> (integral S g)\<bullet>k"
sorry

lemma has_integral_norm_bound_integral_component:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
  fixes g :: "'n \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) S" and "(g has_integral j) S"
    and "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> (g x)\<bullet>k"
  shows "norm i \<le> j\<bullet>k"
sorry

lemma uniformly_convergent_improper_integral:
  fixes f :: "'b \<Rightarrow> real \<Rightarrow> 'a :: {banach}"
  assumes deriv: "\<And>x. x \<ge> a \<Longrightarrow> (G has_field_derivative g x) (at x within {a..})"
  assumes integrable: "\<And>a' b x. x \<in> A \<Longrightarrow> a' \<ge> a \<Longrightarrow> b \<ge> a' \<Longrightarrow> f x integrable_on {a'..b}"
  assumes G: "convergent G"
  assumes le: "\<And>y x. y \<in> A \<Longrightarrow> x \<ge> a \<Longrightarrow> norm (f y x) \<le> g x"
  shows   "uniformly_convergent_on A (\<lambda>b x. integral {a..b} (f x))"
sorry

lemma uniformly_convergent_improper_integral':
  fixes f :: "'b \<Rightarrow> real \<Rightarrow> 'a :: {banach, real_normed_algebra}"
  assumes deriv: "\<And>x. x \<ge> a \<Longrightarrow> (G has_field_derivative g x) (at x within {a..})"
  assumes integrable: "\<And>a' b x. x \<in> A \<Longrightarrow> a' \<ge> a \<Longrightarrow> b \<ge> a' \<Longrightarrow> f x integrable_on {a'..b}"
  assumes G: "convergent G"
  assumes le: "eventually (\<lambda>x. \<forall>y\<in>A. norm (f y x) \<le> g x) at_top"
  shows   "uniformly_convergent_on A (\<lambda>b x. integral {a..b} (f x))"
sorry


subsection \<open>differentiation under the integral sign\<close>

lemma integral_continuous_on_param:
  fixes f::"'a::topological_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes cont_fx: "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). f x t)"
  shows "continuous_on U (\<lambda>x. integral (cbox a b) (f x))"
sorry

lemma leibniz_rule:
  fixes f::"'a::banach \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow>
    ((\<lambda>x. f x t) has_derivative blinfun_apply (fx x t)) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> f x integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes [intro]: "x0 \<in> U"
  assumes "convex U"
  shows
    "((\<lambda>x. integral (cbox a b) (f x)) has_derivative integral (cbox a b) (fx x0)) (at x0 within U)"
    (is "(?F has_derivative ?dF) _")
sorry

lemma has_vector_derivative_eq_has_derivative_blinfun:
  "(f has_vector_derivative f') (at x within U) \<longleftrightarrow>
    (f has_derivative blinfun_scaleR_left f') (at x within U)"
sorry

lemma leibniz_rule_vector_derivative:
  fixes f::"real \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow>
      ((\<lambda>x. f x t) has_vector_derivative (fx x t)) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> cbox a b) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral (cbox a b) (f x)) has_vector_derivative integral (cbox a b) (fx x0))
      (at x0 within U)"
sorry

lemma has_field_derivative_eq_has_derivative_blinfun:
  "(f has_field_derivative f') (at x within U) \<longleftrightarrow> (f has_derivative blinfun_mult_right f') (at x within U)"
sorry

lemma leibniz_rule_field_derivative:
  fixes f::"'a::{real_normed_field, banach} \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'a"
  assumes fx: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes integrable_f2: "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes cont_fx: "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes U: "x0 \<in> U" "convex U"
  shows "((\<lambda>x. integral (cbox a b) (f x)) has_field_derivative integral (cbox a b) (fx x0)) (at x0 within U)"
sorry

lemma leibniz_rule_field_differentiable:
  fixes f::"'a::{real_normed_field, banach} \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'a"
  assumes "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_field_derivative fx x t) (at x within U)"
  assumes "\<And>x. x \<in> U \<Longrightarrow> (f x) integrable_on cbox a b"
  assumes "continuous_on (U \<times> (cbox a b)) (\<lambda>(x, t). fx x t)"
  assumes "x0 \<in> U" "convex U"
  shows "(\<lambda>x. integral (cbox a b) (f x)) field_differentiable at x0 within U"
sorry
subsection \<open>Exchange uniform limit and integral\<close>

lemma uniform_limit_integral_cbox:
  fixes f::"'a \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::banach"
  assumes u: "uniform_limit (cbox a b) f g F"
  assumes c: "\<And>n. continuous_on (cbox a b) (f n)"
  assumes [simp]: "F \<noteq> bot"
  obtains I J where
    "\<And>n. (f n has_integral I n) (cbox a b)"
    "(g has_integral J) (cbox a b)"
    "(I \<longlongrightarrow> J) F"
sorry

lemma uniform_limit_integral:
  fixes f::"'a \<Rightarrow> 'b::ordered_euclidean_space \<Rightarrow> 'c::banach"
  assumes u: "uniform_limit {a..b} f g F"
  assumes c: "\<And>n. continuous_on {a..b} (f n)"
  assumes [simp]: "F \<noteq> bot"
  obtains I J where
    "\<And>n. (f n has_integral I n) {a..b}"
    "(g has_integral J) {a..b}"
    "(I \<longlongrightarrow> J) F"
sorry
subsection \<open>Integration by parts\<close>

lemma integration_by_parts_interior_strong:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes bilinear: "bounded_bilinear (prod)"
  assumes s: "finite s" and le: "a \<le> b"
  assumes cont [continuous_intros]: "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes deriv: "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
                 "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes int: "((\<lambda>x. prod (f x) (g' x)) has_integral
                  (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
sorry

lemma integration_by_parts_interior:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
sorry

lemma integration_by_parts:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "((\<lambda>x. prod (f x) (g' x)) has_integral (prod (f b) (g b) - prod (f a) (g a) - y)) {a..b}"
  shows   "((\<lambda>x. prod (f' x) (g x)) has_integral y) {a..b}"
sorry

lemma integrable_by_parts_interior_strong:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes bilinear: "bounded_bilinear (prod)"
  assumes s: "finite s" and le: "a \<le> b"
  assumes cont [continuous_intros]: "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes deriv: "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
                 "\<And>x. x\<in>{a<..<b} - s \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes int: "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
sorry

lemma integrable_by_parts_interior:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a<..<b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
sorry

lemma integrable_by_parts:
  fixes prod :: "_ \<Rightarrow> _ \<Rightarrow> 'b :: banach"
  assumes "bounded_bilinear (prod)" "a \<le> b"
          "continuous_on {a..b} f" "continuous_on {a..b} g"
  assumes "\<And>x. x\<in>{a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
          "\<And>x. x\<in>{a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
  assumes "(\<lambda>x. prod (f x) (g' x)) integrable_on {a..b}"
  shows   "(\<lambda>x. prod (f' x) (g x)) integrable_on {a..b}"
sorry
subsection \<open>Integration by substitution\<close>

lemma has_integral_substitution_general:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b"
      and subset: "g ` {a..b} \<subseteq> {c..d}"
      and f [continuous_intros]: "continuous_on {c..d} f"
      and g [continuous_intros]: "continuous_on {a..b} g"
      and deriv [derivative_intros]:
              "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
    shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f - integral {g b..g a} f)) {a..b}"
sorry

lemma has_integral_substitution_strong:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes s: "finite s" and le: "a \<le> b" "g a \<le> g b"
    and subset: "g ` {a..b} \<subseteq> {c..d}"
    and f [continuous_intros]: "continuous_on {c..d} f"
    and g [continuous_intros]: "continuous_on {a..b} g"
    and deriv [derivative_intros]:
    "\<And>x. x \<in> {a..b} - s \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
  shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f)) {a..b}"
sorry

lemma has_integral_substitution:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space" and g :: "real \<Rightarrow> real"
  assumes "a \<le> b" "g a \<le> g b" "g ` {a..b} \<subseteq> {c..d}"
      and "continuous_on {c..d} f"
      and "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_field_derivative g' x) (at x within {a..b})"
    shows "((\<lambda>x. g' x *\<^sub>R f (g x)) has_integral (integral {g a..g b} f)) {a..b}"
sorry

lemma integral_shift:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes cont: "continuous_on {a + c..b + c} f"
  shows "integral {a..b} (f \<circ> (\<lambda>x. x + c)) = integral {a + c..b + c} f"
sorry



subsection \<open>Compute a double integral using iterated integrals and switching the order of integration\<close>

lemma continuous_on_imp_integrable_on_Pair1:
  fixes f :: "_ \<Rightarrow> 'b::banach"
  assumes con: "continuous_on (cbox (a,c) (b,d)) f" and x: "x \<in> cbox a b"
  shows "(\<lambda>y. f (x, y)) integrable_on (cbox c d)"
sorry

lemma integral_integrable_2dim:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) f"
    shows "(\<lambda>x. integral (cbox c d) (\<lambda>y. f (x,y))) integrable_on cbox a b"
sorry

lemma integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes f: "f integrable_on (cbox a b)"
      and k: "k \<in> Basis"
  shows "integral (cbox a b) f =
           integral (cbox a b \<inter> {x. x\<bullet>k \<le> c}) f +
           integral (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) f"
sorry

lemma integral_swap_operativeI:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes f: "continuous_on s f" and e: "0 < e"
    shows "operative conj True
           (\<lambda>k. \<forall>a b c d.
                cbox (a,c) (b,d) \<subseteq> k \<and> cbox (a,c) (b,d) \<subseteq> s
                \<longrightarrow> norm(integral (cbox (a,c) (b,d)) f -
                         integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f((x,y)))))
                    \<le> e * content (cbox (a,c) (b,d)))"
sorry

lemma integral_Pair_const:
    "integral (cbox (a,c) (b,d)) (\<lambda>x. k) =
     integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. k))"
sorry

lemma integral_prod_continuous:
  fixes f :: "('a::euclidean_space * 'b::euclidean_space) \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a, c) (b, d)) f" (is "continuous_on ?CBOX f")
    shows "integral (cbox (a, c) (b, d)) f = integral (cbox a b) (\<lambda>x. integral (cbox c d) (\<lambda>y. f (x, y)))"
sorry

lemma integral_swap_2dim:
  fixes f :: "['a::euclidean_space, 'b::euclidean_space] \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "integral (cbox (a, c) (b, d)) (\<lambda>(x, y). f x y) = integral (cbox (c, a) (d, b)) (\<lambda>(x, y). f y x)"
sorry

theorem integral_swap_continuous:
  fixes f :: "['a::euclidean_space, 'b::euclidean_space] \<Rightarrow> 'c::banach"
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "integral (cbox a b) (\<lambda>x. integral (cbox c d) (f x)) =
           integral (cbox c d) (\<lambda>y. integral (cbox a b) (\<lambda>x. f x y))"
sorry



subsection \<open>Definite integrals for exponential and power function\<close>

lemma has_integral_exp_minus_to_infinity:
  assumes a: "a > 0"
  shows   "((\<lambda>x::real. exp (-a*x)) has_integral exp (-a*c)/a) {c..}"
sorry

lemma integrable_on_exp_minus_to_infinity: "a > 0 \<Longrightarrow> (\<lambda>x. exp (-a*x) :: real) integrable_on {c..}"
sorry

lemma has_integral_powr_from_0:
  assumes a: "a > (-1::real)" and c: "c \<ge> 0"
  shows   "((\<lambda>x. x powr a) has_integral (c powr (a+1) / (a+1))) {0..c}"
sorry

lemma integrable_on_powr_from_0:
  assumes a: "a > (-1::real)" and c: "c \<ge> 0"
  shows   "(\<lambda>x. x powr a) integrable_on {0..c}"
sorry

lemma has_integral_powr_to_inf:
  fixes a e :: real
  assumes "e < -1" "a > 0"
  shows   "((\<lambda>x. x powr e) has_integral -(a powr (e + 1)) / (e + 1)) {a..}"
sorry

lemma has_integral_inverse_power_to_inf:
  fixes a :: real and n :: nat
  assumes "n > 1" "a > 0"
  shows   "((\<lambda>x. 1 / x ^ n) has_integral 1 / (real (n - 1) * a ^ (n - 1))) {a..}"
sorry


subsubsection \<open>Adaption to ordered Euclidean spaces and the Cartesian Euclidean space\<close>

lemma integral_component_eq_cart[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> real^'m"
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. f x $ k) = integral s f $ k"
sorry

lemma content_closed_interval:
  fixes a :: "'a::ordered_euclidean_space"
  assumes "a \<le> b"
  shows "content {a..b} = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
sorry

lemma integrable_const_ivl[intro]:
  fixes a::"'a::ordered_euclidean_space"
  shows "(\<lambda>x. c) integrable_on {a..b}"
sorry

lemma integrable_on_subinterval:
  fixes f :: "'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "f integrable_on S" "{a..b} \<subseteq> S"
  shows "f integrable_on {a..b}"
sorry

end
