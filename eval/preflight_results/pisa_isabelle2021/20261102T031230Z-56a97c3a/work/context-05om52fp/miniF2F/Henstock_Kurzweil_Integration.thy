(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light)
                Huge cleanup by LCP
*)

section \<open>Henstock-Kurzweil Gauge Integration in Many Dimensions\<close>

theory Henstock_Kurzweil_Integration
imports
  "HOL-Analysis.Lebesgue_Measure" "HOL-Analysis.Tagged_Division" "HOL-Real_Asymp.Real_Asymp"

begin
declare [[quick_and_dirty = true]]


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


subsection \<open>Content (length, area, volume, etc.) of an interval\<close>

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

  sorry


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
        norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R f x) - y) < e))"
  
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


lemma has_integral_of_real:
  "(f has_integral I) A \<Longrightarrow>
     ((\<lambda>x::'a::euclidean_space. of_real (f x) :: 'b :: {real_normed_vector,real_normed_algebra_1}) 
        has_integral of_real I) A"
  
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


lemma has_integral_mult_right_iff:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows "((\<lambda>x. c * f x) has_integral y) A \<longleftrightarrow> (f has_integral (y / c)) A"
  
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


lemma integral_eq_iff_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A"
  shows "integral A f = I \<longleftrightarrow> (\<forall>b\<in>Basis. integral A (\<lambda>x. f x \<bullet> b) = I \<bullet> b)"
  
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



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma integral_null [simp]: "content (cbox a b) = 0 \<Longrightarrow> integral (cbox a b) f = 0"
  
  