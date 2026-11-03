(*  Title:      HOL/Analysis/Improper_Integral.thy
    Author: LC Paulson (ported from HOL Light)
*)

section \<open>Continuity of the indefinite integral; improper integral theorem\<close>

theory "Improper_Integral"
  imports Equivalence_Lebesgue_Henstock_Integration
begin

subsection \<open>Equiintegrability\<close>

text\<open>The definition here only really makes sense for an elementary set.
     We just use compact intervals in applications below.\<close>

definition\<^marker>\<open>tag important\<close> equiintegrable_on (infixr \<open>equiintegrable'_on\<close> 46)
  where "F equiintegrable_on I \<equiv>
         (\<forall>f \<in> F. f integrable_on I) \<and>
         (\<forall>e > 0. \<exists>\<gamma>. gauge \<gamma> \<and>
                    (\<forall>f \<D>. f \<in> F \<and> \<D> tagged_division_of I \<and> \<gamma> fine \<D>
                          \<longrightarrow> norm ((\<Sum>(x,K) \<in> \<D>. content K *\<^sub>R f x) - integral I f) < e))"

lemma equiintegrable_on_integrable:
     "\<lbrakk>F equiintegrable_on I; f \<in> F\<rbrakk> \<Longrightarrow> f integrable_on I"
sorry

lemma equiintegrable_on_sing [simp]:
     "{f} equiintegrable_on cbox a b \<longleftrightarrow> f integrable_on cbox a b"
sorry

lemma equiintegrable_on_subset: "\<lbrakk>F equiintegrable_on I; G \<subseteq> F\<rbrakk> \<Longrightarrow> G equiintegrable_on I"
sorry

lemma equiintegrable_on_Un:
  assumes "F equiintegrable_on I" "G equiintegrable_on I"
  shows "(F \<union> G) equiintegrable_on I"
sorry

lemma equiintegrable_on_insert:
  assumes "f integrable_on cbox a b" "F equiintegrable_on cbox a b"
  shows "(insert f F) equiintegrable_on cbox a b"
sorry

lemma equiintegrable_cmul:
  assumes F: "F equiintegrable_on I"
  shows "(\<Union>c \<in> {-k..k}. \<Union>f \<in> F. {(\<lambda>x. c *\<^sub>R f x)}) equiintegrable_on I"
sorry

lemma equiintegrable_add:
  assumes F: "F equiintegrable_on I" and G: "G equiintegrable_on I"
  shows "(\<Union>f \<in> F. \<Union>g \<in> G. {(\<lambda>x. f x + g x)}) equiintegrable_on I"
sorry

lemma equiintegrable_minus:
  assumes "F equiintegrable_on I"
  shows "(\<Union>f \<in> F. {(\<lambda>x. - f x)}) equiintegrable_on I"
sorry

lemma equiintegrable_diff:
  assumes F: "F equiintegrable_on I" and G: "G equiintegrable_on I"
  shows "(\<Union>f \<in> F. \<Union>g \<in> G. {(\<lambda>x. f x - g x)}) equiintegrable_on I"
sorry

lemma equiintegrable_sum:
  fixes F :: "('a::euclidean_space \<Rightarrow> 'b::euclidean_space) set"
  assumes "F equiintegrable_on cbox a b"
  shows "(\<Union>I \<in> Collect finite. \<Union>c \<in> {c. (\<forall>i \<in> I. c i \<ge> 0) \<and> sum c I = 1}.
          \<Union>f \<in> I \<rightarrow> F. {(\<lambda>x. sum (\<lambda>i::'j. c i *\<^sub>R f i x) I)}) equiintegrable_on cbox a b"
    (is "?G equiintegrable_on _")
sorry

corollary equiintegrable_sum_real:
  fixes F :: "(real \<Rightarrow> 'b::euclidean_space) set"
  assumes "F equiintegrable_on {a..b}"
  shows "(\<Union>I \<in> Collect finite. \<Union>c \<in> {c. (\<forall>i \<in> I. c i \<ge> 0) \<and> sum c I = 1}.
          \<Union>f \<in> I \<rightarrow> F. {(\<lambda>x. sum (\<lambda>i. c i *\<^sub>R f i x) I)})
         equiintegrable_on {a..b}"
sorry

text\<open> Basic combining theorems for the interval of integration.\<close>

lemma equiintegrable_on_null [simp]:
   "content(cbox a b) = 0 \<Longrightarrow> F equiintegrable_on cbox a b"
sorry

text\<open> Main limit theorem for an equiintegrable sequence.\<close>

theorem equiintegrable_limit:
  fixes g :: "'a :: euclidean_space \<Rightarrow> 'b :: banach"
  assumes feq: "range f equiintegrable_on cbox a b"
      and to_g: "\<And>x. x \<in> cbox a b \<Longrightarrow> (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
    shows "g integrable_on cbox a b \<and> (\<lambda>n. integral (cbox a b) (f n)) \<longlonglongrightarrow> integral (cbox a b) g"
sorry

lemma equiintegrable_reflect:
  assumes "F equiintegrable_on cbox a b"
  shows "(\<lambda>f. f \<circ> uminus) ` F equiintegrable_on cbox (-b) (-a)"
sorry

subsection\<open>Subinterval restrictions for equiintegrable families\<close>

text\<open>First, some technical lemmas about minimizing a "flat" part of a sum over a division.\<close>

lemma lemma0:
  assumes "i \<in> Basis"
    shows "content (cbox u v) / (interval_upperbound (cbox u v) \<bullet> i - interval_lowerbound (cbox u v) \<bullet> i) =
           (if content (cbox u v) = 0 then 0
            else \<Prod>j \<in> Basis - {i}. interval_upperbound (cbox u v) \<bullet> j - interval_lowerbound (cbox u v) \<bullet> j)"
sorry

lemma content_division_lemma1:
  assumes div: "\<D> division_of S" and S: "S \<subseteq> cbox a b" and i: "i \<in> Basis"
      and mt: "\<And>K. K \<in> \<D> \<Longrightarrow> content K \<noteq> 0"
      and disj: "(\<forall>K \<in> \<D>. K \<inter> {x. x \<bullet> i = a \<bullet> i} \<noteq> {}) \<or> (\<forall>K \<in> \<D>. K \<inter> {x. x \<bullet> i = b \<bullet> i} \<noteq> {})"
   shows "(b \<bullet> i - a \<bullet> i) * (\<Sum>K\<in>\<D>. content K / (interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i))
          \<le> content(cbox a b)"   (is "?lhs \<le> ?rhs")
sorry

proposition sum_content_area_over_thin_division:
  assumes div: "\<D> division_of S" and S: "S \<subseteq> cbox a b" and i: "i \<in> Basis"
    and "a \<bullet> i \<le> c" "c \<le> b \<bullet> i"
    and nonmt: "\<And>K. K \<in> \<D> \<Longrightarrow> K \<inter> {x. x \<bullet> i = c} \<noteq> {}"
  shows "(b \<bullet> i - a \<bullet> i) * (\<Sum>K\<in>\<D>. content K / (interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i))
          \<le> 2 * content(cbox a b)"
sorry

proposition bounded_equiintegral_over_thin_tagged_partial_division:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F" and "0 < \<epsilon>"
      and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  obtains \<gamma> where "gauge \<gamma>"
             "\<And>c i S h. \<lbrakk>c \<in> cbox a b; i \<in> Basis; S tagged_partial_division_of cbox a b;
                         \<gamma> fine S; h \<in> F; \<And>x K. (x,K) \<in> S \<Longrightarrow> (K \<inter> {x. x \<bullet> i = c \<bullet> i} \<noteq> {})\<rbrakk>
                        \<Longrightarrow> (\<Sum>(x,K) \<in> S. norm (integral K h)) < \<epsilon>"
sorry

proposition equiintegrable_halfspace_restrictions_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i \<le> c then h x else 0)})
         equiintegrable_on cbox a b"
sorry

corollary equiintegrable_halfspace_restrictions_ge:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i \<ge> c then h x else 0)})
         equiintegrable_on cbox a b"
sorry

corollary equiintegrable_halfspace_restrictions_lt:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i < c then h x else 0)}) equiintegrable_on cbox a b"
         (is "?G equiintegrable_on cbox a b")
sorry

corollary equiintegrable_halfspace_restrictions_gt:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "F equiintegrable_on cbox a b" and f: "f \<in> F"
    and norm_f: "\<And>h x. \<lbrakk>h \<in> F; x \<in> cbox a b\<rbrakk> \<Longrightarrow> norm(h x) \<le> norm(f x)"
  shows "(\<Union>i \<in> Basis. \<Union>c. \<Union>h \<in> F. {(\<lambda>x. if x \<bullet> i > c then h x else 0)}) equiintegrable_on cbox a b"
         (is "?G equiintegrable_on cbox a b")
sorry

proposition equiintegrable_closed_interval_restrictions:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f integrable_on cbox a b"
  shows "(\<Union>c d. {(\<lambda>x. if x \<in> cbox c d then f x else 0)}) equiintegrable_on cbox a b"
sorry


subsection\<open>Continuity of the indefinite integral\<close>

proposition indefinite_integral_continuous:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes int_f: "f integrable_on cbox a b"
      and c: "c \<in> cbox a b" and d: "d \<in> cbox a b" "0 < \<epsilon>"
  obtains \<delta> where "0 < \<delta>"
              "\<And>c' d'. \<lbrakk>c' \<in> cbox a b; d' \<in> cbox a b; norm(c' - c) \<le> \<delta>; norm(d' - d) \<le> \<delta>\<rbrakk>
                        \<Longrightarrow> norm(integral(cbox c' d') f - integral(cbox c d) f) < \<epsilon>"
sorry

corollary indefinite_integral_uniformly_continuous:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on cbox a b"
  shows "uniformly_continuous_on (cbox (Pair a a) (Pair b b)) (\<lambda>y. integral (cbox (fst y) (snd y)) f)"
sorry

corollary bounded_integrals_over_subintervals:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on cbox a b"
  shows "bounded {integral (cbox c d) f |c d. cbox c d \<subseteq> cbox a b}"
sorry


text\<open>An existence theorem for "improper" integrals.
Hake's theorem implies that if the integrals over subintervals have a limit, the integral exists.
We only need to assume that the integrals are bounded, and we get absolute integrability,
but we also need a (rather weak) bound assumption on the function.\<close>

theorem absolutely_integrable_improper:
  fixes f :: "'M::euclidean_space \<Rightarrow> 'N::euclidean_space"
  assumes int_f: "\<And>c d. cbox c d \<subseteq> box a b \<Longrightarrow> f integrable_on cbox c d"
      and bo: "bounded {integral (cbox c d) f |c d. cbox c d \<subseteq> box a b}"
      and absi: "\<And>i. i \<in> Basis
          \<Longrightarrow> \<exists>g. g absolutely_integrable_on cbox a b \<and>
                  ((\<forall>x \<in> cbox a b. f x \<bullet> i \<le> g x) \<or> (\<forall>x \<in> cbox a b. f x \<bullet> i \<ge> g x))"
      shows "f absolutely_integrable_on cbox a b"
sorry

subsection\<open>Second mean value theorem and corollaries\<close>

lemma level_approx:
  fixes f :: "real \<Rightarrow> real" and n::nat
  assumes f: "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> f x \<and> f x \<le> 1" and "x \<in> S" "n \<noteq> 0"
  shows "\<bar>f x - (\<Sum>k = Suc 0..n. if k / n \<le> f x then inverse n else 0)\<bar> < inverse n"
        (is "?lhs < _")
sorry

lemma SMVT_lemma2:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}"
    and g: "\<And>x y. x \<le> y \<Longrightarrow> g x \<le> g y"
  shows "(\<Union>y::real. {\<lambda>x. if g x \<ge> y then f x else 0}) equiintegrable_on {a..b}"
sorry

lemma SMVT_lemma4:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}"
    and "a \<le> b"
    and g: "\<And>x y. x \<le> y \<Longrightarrow> g x \<le> g y"
    and 01: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> 0 \<le> g x \<and> g x \<le> 1"
  obtains c where "a \<le> c" "c \<le> b" "((\<lambda>x. g x *\<^sub>R f x) has_integral integral {c..b} f) {a..b}"
sorry

theorem second_mean_value_theorem_full:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}" and "a \<le> b"
    and g: "\<And>x y. \<lbrakk>a \<le> x; x \<le> y; y \<le> b\<rbrakk> \<Longrightarrow> g x \<le> g y"
  obtains c where "c \<in> {a..b}"
    and "((\<lambda>x. g x * f x) has_integral (g a * integral {a..c} f + g b * integral {c..b} f)) {a..b}"
sorry

corollary second_mean_value_theorem:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f integrable_on {a..b}" and "a \<le> b"
   and g: "\<And>x y. \<lbrakk>a \<le> x; x \<le> y; y \<le> b\<rbrakk> \<Longrightarrow> g x \<le> g y"
 obtains c where "c \<in> {a..b}"
                 "integral {a..b} (\<lambda>x. g x * f x) = g a * integral {a..c} f + g b * integral {c..b} f"
sorry
end

