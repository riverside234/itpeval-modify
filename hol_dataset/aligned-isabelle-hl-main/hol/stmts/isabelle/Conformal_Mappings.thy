section \<open>Conformal Mappings and Consequences of Cauchy's Integral Theorem\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2016)\<close>

text\<open>Also Cauchy's residue theorem by Wenda Li (2016)\<close>

theory Conformal_Mappings
imports Cauchy_Integral_Formula

begin

subsection \<open>Analytic continuation\<close>

proposition isolated_zeros:
  assumes holf: "f holomorphic_on S"
      and "open S" "connected S" "\<xi> \<in> S" "f \<xi> = 0" "\<beta> \<in> S" "f \<beta> \<noteq> 0"
    obtains r where "0 < r" and "ball \<xi> r \<subseteq> S" and
        "\<And>z. z \<in> ball \<xi> r - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
sorry

proposition analytic_continuation:
  assumes holf: "f holomorphic_on S"
      and "open S" and "connected S"
      and "U \<subseteq> S" and "\<xi> \<in> S"
      and "\<xi> islimpt U"
      and fU0 [simp]: "\<And>z. z \<in> U \<Longrightarrow> f z = 0"
      and "w \<in> S"
    shows "f w = 0"
sorry

corollary analytic_continuation_open:
  assumes "open s" and "open s'" and "s \<noteq> {}" and "connected s'"
      and "s \<subseteq> s'"
  assumes "f holomorphic_on s'" and "g holomorphic_on s'"
      and "\<And>z. z \<in> s \<Longrightarrow> f z = g z"
  assumes "z \<in> s'"
  shows   "f z = g z"
sorry

corollary analytic_continuation':
  assumes "f holomorphic_on S" "open S" "connected S"
      and "U \<subseteq> S" "\<xi> \<in> S" "\<xi> islimpt U"
      and "f constant_on U"
    shows "f constant_on S"
sorry

lemma holomorphic_compact_finite_zeros:
  assumes S: "f holomorphic_on S" "open S" "connected S"
      and "compact K" "K \<subseteq> S"
      and "\<not> f constant_on S"
    shows "finite {z\<in>K. f z = 0}"
sorry

lemma holomorphic_countable_zeros:
  assumes S: "f holomorphic_on S" "open S" "connected S" and "fsigma S"
      and "\<not> f constant_on S"
    shows "countable {z\<in>S. f z = 0}"
sorry

lemma holomorphic_countable_equal:
  assumes "f holomorphic_on S" "g holomorphic_on S" "open S" "connected S" and "fsigma S"
    and eq: "uncountable {z\<in>S. f z = g z}"
  shows "S \<subseteq> {z\<in>S. f z = g z}"
sorry

lemma holomorphic_countable_equal_UNIV:
  assumes fg: "f holomorphic_on UNIV" "g holomorphic_on UNIV"
    and eq: "uncountable {z. f z = g z}"
  shows "f=g"
sorry

subsection\<open>Open mapping theorem\<close>

lemma holomorphic_contract_to_zero:
  assumes contf: "continuous_on (cball \<xi> r) f"
      and holf: "f holomorphic_on ball \<xi> r"
      and "0 < r"
      and norm_less: "\<And>z. norm(\<xi> - z) = r \<Longrightarrow> norm(f \<xi>) < norm(f z)"
  obtains z where "z \<in> ball \<xi> r" "f z = 0"
sorry

theorem open_mapping_thm:
  assumes holf: "f holomorphic_on S"
      and S: "open S" and "connected S"
      and "open U" and "U \<subseteq> S"
      and fne: "\<not> f constant_on S"
    shows "open (f ` U)"
sorry


text\<open>No need for \<^term>\<open>S\<close> to be connected. But the nonconstant condition is stronger.\<close>
corollary\<^marker>\<open>tag unimportant\<close> open_mapping_thm2:
  assumes holf: "f holomorphic_on S"
      and S: "open S"
      and "open U" "U \<subseteq> S"
      and fnc: "\<And>X. \<lbrakk>open X; X \<subseteq> S; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<not> f constant_on X"
    shows "open (f ` U)"
sorry

corollary\<^marker>\<open>tag unimportant\<close> open_mapping_thm3:
  assumes "f holomorphic_on S"
      and "open S" and  "inj_on f S"
    shows  "open (f ` S)"
sorry

subsection\<open>Maximum modulus principle\<close>

text\<open>If \<^term>\<open>f\<close> is holomorphic, then its norm (modulus) cannot exhibit a true local maximum that is
   properly within the domain of \<^term>\<open>f\<close>.\<close>

proposition maximum_modulus_principle:
  assumes holf: "f holomorphic_on S"
      and S: "open S" and "connected S"
      and "open U" and "U \<subseteq> S" and "\<xi> \<in> U"
      and no: "\<And>z. z \<in> U \<Longrightarrow> norm(f z) \<le> norm(f \<xi>)"
    shows "f constant_on S"
sorry

proposition maximum_modulus_frontier:
  assumes holf: "f holomorphic_on (interior S)"
      and contf: "continuous_on (closure S) f"
      and bos: "bounded S"
      and leB: "\<And>z. z \<in> frontier S \<Longrightarrow> norm(f z) \<le> B"
      and "\<xi> \<in> S"
    shows "norm(f \<xi>) \<le> B"
sorry

corollary\<^marker>\<open>tag unimportant\<close> maximum_real_frontier:
  assumes holf: "f holomorphic_on (interior S)"
    and contf: "continuous_on (closure S) f"
    and bos: "bounded S"
    and leB: "\<And>z. z \<in> frontier S \<Longrightarrow> Re(f z) \<le> B"
    and "\<xi> \<in> S"
  shows "Re(f \<xi>) \<le> B"
sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Factoring out a zero according to its order\<close>

lemma holomorphic_factor_order_of_zero:
  assumes holf: "f holomorphic_on S"
      and os: "open S"
      and "\<xi> \<in> S" "0 < n"
      and dnz: "(deriv ^^ n) f \<xi> \<noteq> 0"
      and dfz: "\<And>i. \<lbrakk>0 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f \<xi> = 0"
   obtains g r where "0 < r"
                "g holomorphic_on ball \<xi> r"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = (w - \<xi>)^n * g w"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
sorry

lemma holomorphic_factor_order_of_zero_strong:
  assumes holf: "f holomorphic_on S" "open S"  "\<xi> \<in> S" "0 < n"
      and "(deriv ^^ n) f \<xi> \<noteq> 0"
      and "\<And>i. \<lbrakk>0 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f \<xi> = 0"
   obtains g r where "0 < r"
                "g holomorphic_on ball \<xi> r"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = ((w - \<xi>) * g w) ^ n"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
sorry

lemma
  fixes k :: "'a::wellorder"
  assumes a_def: "a == LEAST x. P x" and P: "P k"
  shows def_LeastI: "P a" and def_Least_le: "a \<le> k"
sorry

lemma holomorphic_factor_zero_nonconstant:
  assumes holf: "f holomorphic_on S" and S: "open S" "connected S"
      and "\<xi> \<in> S" "f \<xi> = 0"
      and nonconst: "\<not> f constant_on S"
   obtains g r n
      where "0 < n"  "0 < r"  "ball \<xi> r \<subseteq> S"
            "g holomorphic_on ball \<xi> r"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w = (w - \<xi>)^n * g w"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
sorry

lemma holomorphic_lower_bound_difference:
  assumes holf: "f holomorphic_on S" and S: "open S" "connected S"
      and "\<xi> \<in> S" and "\<phi> \<in> S"
      and fne: "f \<phi> \<noteq> f \<xi>"
   obtains k n r
      where "0 < k"  "0 < r"
            "ball \<xi> r \<subseteq> S"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> k * norm(w - \<xi>)^n \<le> norm(f w - f \<xi>)"
sorry

lemma
  assumes holf: "f holomorphic_on (S - {\<xi>})" and \<xi>: "\<xi> \<in> interior S"
    shows holomorphic_on_extend_lim:
          "(\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S - {\<xi>}. g z = f z)) \<longleftrightarrow>
           ((\<lambda>z. (z - \<xi>) * f z) \<longlongrightarrow> 0) (at \<xi>)"
          (is "?P = ?Q")
     and holomorphic_on_extend_bounded:
          "(\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S - {\<xi>}. g z = f z)) \<longleftrightarrow>
           (\<exists>B. eventually (\<lambda>z. norm(f z) \<le> B) (at \<xi>))"
          (is "?P = ?R")
sorry

lemma pole_at_infinity:
  assumes holf: "f holomorphic_on UNIV" and lim: "((inverse o f) \<longlongrightarrow> l) at_infinity"
  obtains a n where "\<And>z. f z = (\<Sum>i\<le>n. a i * z^i)"
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Entire proper functions are precisely the non-trivial polynomials\<close>

lemma proper_map_polyfun:
    fixes c :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,heine_borel}"
  assumes "closed S" and "compact K" and c: "c i \<noteq> 0" "1 \<le> i" "i \<le> n"
    shows "compact (S \<inter> {z. (\<Sum>i\<le>n. c i * z^i) \<in> K})"
sorry

lemma proper_map_polyfun_univ:
    fixes c :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,heine_borel}"
  assumes "compact K" "c i \<noteq> 0" "1 \<le> i" "i \<le> n"
    shows "compact ({z. (\<Sum>i\<le>n. c i * z^i) \<in> K})"
sorry

lemma proper_map_polyfun_eq:
  assumes "f holomorphic_on UNIV"
    shows "(\<forall>k. compact k \<longrightarrow> compact {z. f z \<in> k}) \<longleftrightarrow>
           (\<exists>c n. 0 < n \<and> (c n \<noteq> 0) \<and> f = (\<lambda>z. \<Sum>i\<le>n. c i * z^i))"
          (is "?lhs = ?rhs")
sorry

subsection \<open>Relating invertibility and nonvanishing of derivative\<close>

lemma has_complex_derivative_locally_injective:
  assumes holf: "f holomorphic_on S"
      and S: "\<xi> \<in> S" "open S"
      and dnz: "deriv f \<xi> \<noteq> 0"
  obtains r where "r > 0" "ball \<xi> r \<subseteq> S" "inj_on f (ball \<xi> r)"
sorry

lemma has_complex_derivative_locally_invertible:
  assumes holf: "f holomorphic_on S"
      and S: "\<xi> \<in> S" "open S"
      and dnz: "deriv f \<xi> \<noteq> 0"
  obtains r where "r > 0" "ball \<xi> r \<subseteq> S" "open (f `  (ball \<xi> r))" "inj_on f (ball \<xi> r)"
sorry

lemma holomorphic_injective_imp_regular:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
      and "\<xi> \<in> S"
    shows "deriv f \<xi> \<noteq> 0"
sorry

subsubsection \<open>Hence a nice clean inverse function theorem\<close>

lemma has_field_derivative_inverse_strong:
  fixes f :: "'a::{euclidean_space,real_normed_field} \<Rightarrow> 'a"
  shows "\<lbrakk>DERIV f x :> f'; f' \<noteq> 0; open S; x \<in> S; continuous_on S f;
         \<And>z. z \<in> S \<Longrightarrow> g (f z) = z\<rbrakk>
         \<Longrightarrow> DERIV g (f x) :> inverse (f')"
sorry

lemma has_field_derivative_inverse_strong_x:
  fixes f :: "'a::{euclidean_space,real_normed_field} \<Rightarrow> 'a"
  shows  "\<lbrakk>DERIV f (g y) :> f'; f' \<noteq> 0; open S; continuous_on S f; g y \<in> S; f(g y) = y;
           \<And>z. z \<in> S \<Longrightarrow> g (f z) = z\<rbrakk>
          \<Longrightarrow> DERIV g y :> inverse (f')"
sorry

proposition holomorphic_has_inverse:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
  obtains g where "g holomorphic_on (f ` S)"
                  "\<And>z. z \<in> S \<Longrightarrow> deriv f z * deriv g (f z) = 1"
                  "\<And>z. z \<in> S \<Longrightarrow> g(f z) = z"
sorry

subsubsection \<open> Holomorphism of covering maps and lifts.\<close>

lemma covering_space_lift_is_holomorphic:
  assumes cov: "covering_space C p S"
      and C: "open C" "p holomorphic_on C"
      and holf: "f holomorphic_on U" and fim: "f \<in> U \<rightarrow> S" and gim: "g \<in> U \<rightarrow> C"
      and contg: "continuous_on U g" and pg_f: "\<And>x. x \<in> U \<Longrightarrow> p(g x) = f x"
    shows "g holomorphic_on U"
sorry

lemma covering_space_lift_holomorphic:
  assumes cov: "covering_space C p S"
      and C: "open C" "p holomorphic_on C"
      and f: "f holomorphic_on U" "f \<in> U \<rightarrow> S" 
      and U: "simply_connected U" "locally path_connected U"
  obtains g where "g holomorphic_on U" "g \<in> U \<rightarrow> C" "\<And>y. y \<in> U \<Longrightarrow> p(g y) = f y"
sorry

subsection\<open>The Schwarz Lemma\<close>

lemma Schwarz1:
  assumes holf: "f holomorphic_on S"
      and contf: "continuous_on (closure S) f"
      and S: "open S" "connected S"
      and boS: "bounded S"
      and "S \<noteq> {}"
  obtains w where "w \<in> frontier S"
       "\<And>z. z \<in> closure S \<Longrightarrow> norm (f z) \<le> norm (f w)"
sorry

lemma Schwarz2:
 "\<lbrakk>f holomorphic_on ball 0 r;
    0 < s; ball w s \<subseteq> ball 0 r;
    \<And>z. norm (w-z) < s \<Longrightarrow> norm(f z) \<le> norm(f w)\<rbrakk>
    \<Longrightarrow> f constant_on ball 0 r"
sorry

lemma Schwarz3:
  assumes holf: "f holomorphic_on (ball 0 r)" and [simp]: "f 0 = 0"
  obtains h where "h holomorphic_on (ball 0 r)" and "\<And>z. norm z < r \<Longrightarrow> f z = z * (h z)" and "deriv f 0 = h 0"
sorry

proposition Schwarz_Lemma:
  assumes holf: "f holomorphic_on (ball 0 1)" and [simp]: "f 0 = 0"
      and no: "\<And>z. norm z < 1 \<Longrightarrow> norm (f z) < 1"
      and \<xi>: "norm \<xi> < 1"
    shows "norm (f \<xi>) \<le> norm \<xi>" and "norm(deriv f 0) \<le> 1"
      and "((\<exists>z. norm z < 1 \<and> z \<noteq> 0 \<and> norm(f z) = norm z)
            \<or> norm(deriv f 0) = 1)
           \<Longrightarrow> \<exists>\<alpha>. (\<forall>z. norm z < 1 \<longrightarrow> f z = \<alpha> * z) \<and> norm \<alpha> = 1"
      (is "?P \<Longrightarrow> ?Q")
sorry

corollary Schwarz_Lemma':
  assumes holf: "f holomorphic_on (ball 0 1)" and [simp]: "f 0 = 0"
      and no: "\<And>z. norm z < 1 \<Longrightarrow> norm (f z) < 1"
    shows "((\<forall>\<xi>. norm \<xi> < 1 \<longrightarrow> norm (f \<xi>) \<le> norm \<xi>)
            \<and> norm(deriv f 0) \<le> 1)
            \<and> (((\<exists>z. norm z < 1 \<and> z \<noteq> 0 \<and> norm(f z) = norm z)
              \<or> norm(deriv f 0) = 1)
              \<longrightarrow> (\<exists>\<alpha>. (\<forall>z. norm z < 1 \<longrightarrow> f z = \<alpha> * z) \<and> norm \<alpha> = 1))"
sorry

subsection\<open>The Schwarz reflection principle\<close>

lemma hol_pal_lem0:
  assumes "d \<bullet> a \<le> k" "k \<le> d \<bullet> b"
  obtains c where
     "c \<in> closed_segment a b" "d \<bullet> c = k"
     "\<And>z. z \<in> closed_segment a c \<Longrightarrow> d \<bullet> z \<le> k"
     "\<And>z. z \<in> closed_segment c b \<Longrightarrow> k \<le> d \<bullet> z"
sorry

lemma hol_pal_lem1:
  assumes "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
          "d \<noteq> 0" and lek: "d \<bullet> a \<le> k" "d \<bullet> b \<le> k" "d \<bullet> c \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
sorry

lemma hol_pal_lem2:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
      and "d \<noteq> 0" and lek: "d \<bullet> a \<le> k" "d \<bullet> b \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
sorry

lemma hol_pal_lem3:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
      and "d \<noteq> 0" and lek: "d \<bullet> a \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
sorry

lemma hol_pal_lem4:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S" and "d \<noteq> 0"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
sorry

lemma holomorphic_on_paste_across_line:
  assumes S: "open S" and "d \<noteq> 0"
      and holf1: "f holomorphic_on (S \<inter> {z. d \<bullet> z < k})"
      and holf2: "f holomorphic_on (S \<inter> {z. k < d \<bullet> z})"
      and contf: "continuous_on S f"
    shows "f holomorphic_on S"
sorry

proposition Schwarz_reflection:
  assumes "open S" and cnjs: "cnj ` S \<subseteq> S"
      and  holf: "f holomorphic_on (S \<inter> {z. 0 < Im z})"
      and contf: "continuous_on (S \<inter> {z. 0 \<le> Im z}) f"
      and f: "\<And>z. \<lbrakk>z \<in> S; z \<in> \<real>\<rbrakk> \<Longrightarrow> (f z) \<in> \<real>"
    shows "(\<lambda>z. if 0 \<le> Im z then f z else cnj(f(cnj z))) holomorphic_on S"
sorry

subsection\<open>Bloch's theorem\<close>

lemma Bloch_lemma_0:
  assumes holf: "f holomorphic_on cball 0 r" and "0 < r"
      and [simp]: "f 0 = 0"
      and le: "\<And>z. norm z < r \<Longrightarrow> norm(deriv f z) \<le> 2 * norm(deriv f 0)"
    shows "ball 0 ((3 - 2 * sqrt 2) * r * norm(deriv f 0)) \<subseteq> f ` ball 0 r"
sorry

lemma Bloch_lemma:
  assumes holf: "f holomorphic_on cball a r" and "0 < r"
    and le: "\<And>z. z \<in> ball a r \<Longrightarrow> norm(deriv f z) \<le> 2 * norm(deriv f a)"
  shows "ball (f a) ((3 - 2 * sqrt 2) * r * norm(deriv f a)) \<subseteq> f ` ball a r" (is "?lhs \<subseteq> ?rhs")
sorry

proposition Bloch_unit:
  assumes holf: "f holomorphic_on ball a 1" and [simp]: "deriv f a = 1"
  obtains b r where "1/12 < r" and "ball b r \<subseteq> f ` (ball a 1)"
sorry

theorem Bloch:
  assumes holf: "f holomorphic_on ball a r" and "0 < r"
      and r': "r' \<le> r * norm (deriv f a) / 12"
  obtains b where "ball b r' \<subseteq> f ` (ball a r)"
sorry

corollary Bloch_general:
  assumes holf: "f holomorphic_on S" and "a \<in> S"
      and tle: "\<And>z. z \<in> frontier S \<Longrightarrow> t \<le> dist a z"
      and rle: "r \<le> t * norm(deriv f a) / 12"
  obtains b where "ball b r \<subseteq> f ` S"
sorry

end
