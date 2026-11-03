(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (translation from HOL light)
*)

section \<open>Fashoda Meet Theorem\<close>

theory Fashoda_Theorem
imports Brouwer_Fixpoint Path_Connected Cartesian_Euclidean_Space
begin

subsection \<open>Bijections between intervals\<close>

definition\<^marker>\<open>tag important\<close> interval_bij :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> 'a::euclidean_space"
  where "interval_bij =
    (\<lambda>(a, b) (u, v) x. (\<Sum>i\<in>Basis. (u\<bullet>i + (x\<bullet>i - a\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (v\<bullet>i - u\<bullet>i)) *\<^sub>R i))"

lemma interval_bij_affine:
  "interval_bij (a,b) (u,v) = (\<lambda>x. (\<Sum>i\<in>Basis. ((v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (x\<bullet>i)) *\<^sub>R i) +
    (\<Sum>i\<in>Basis. (u\<bullet>i - (v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (a\<bullet>i)) *\<^sub>R i))"
sorry

lemma continuous_interval_bij:
  fixes a b :: "'a::euclidean_space"
  shows "continuous (at x) (interval_bij (a, b) (u, v))"
sorry

lemma continuous_on_interval_bij: "continuous_on s (interval_bij (a, b) (u, v))"
sorry

lemma in_interval_interval_bij:
  fixes a b u v x :: "'a::euclidean_space"
  assumes "x \<in> cbox a b"
    and "cbox u v \<noteq> {}"
  shows "interval_bij (a, b) (u, v) x \<in> cbox u v"
sorry

lemma interval_bij_bij:
  "\<forall>(i::'a::euclidean_space)\<in>Basis. a\<bullet>i < b\<bullet>i \<and> u\<bullet>i < v\<bullet>i \<Longrightarrow>
    interval_bij (a, b) (u, v) (interval_bij (u, v) (a, b) x) = x"
sorry

lemma interval_bij_bij_cart: fixes x::"real^'n" assumes "\<forall>i. a$i < b$i \<and> u$i < v$i"
  shows "interval_bij (a,b) (u,v) (interval_bij (u,v) (a,b) x) = x"
sorry

subsection \<open>Fashoda meet theorem\<close>

lemma infnorm_2:
  fixes x :: "real^2"
  shows "infnorm x = max \<bar>x$1\<bar> \<bar>x$2\<bar>"
sorry

lemma infnorm_eq_1_2:
  fixes x :: "real^2"
  shows "infnorm x = 1 \<longleftrightarrow>
    \<bar>x$1\<bar> \<le> 1 \<and> \<bar>x$2\<bar> \<le> 1 \<and> (x$1 = -1 \<or> x$1 = 1 \<or> x$2 = -1 \<or> x$2 = 1)"
sorry

lemma infnorm_eq_1_imp:
  fixes x :: "real^2"
  assumes "infnorm x = 1"
  shows "\<bar>x$1\<bar> \<le> 1" and "\<bar>x$2\<bar> \<le> 1"
sorry

proposition fashoda_unit:
  fixes f g :: "real \<Rightarrow> real^2"
  assumes "f ` {-1 .. 1} \<subseteq> cbox (-1) 1"
    and "g ` {-1 .. 1} \<subseteq> cbox (-1) 1"
    and "continuous_on {-1 .. 1} f"
    and "continuous_on {-1 .. 1} g"
    and "f (- 1)$1 = - 1"
    and "f 1$1 = 1" "g (- 1) $2 = -1"
    and "g 1 $2 = 1"
  shows "\<exists>s\<in>{-1 .. 1}. \<exists>t\<in>{-1 .. 1}. f s = g t"
sorry

proposition fashoda_unit_path:
  fixes f g :: "real \<Rightarrow> real^2"
  assumes "path f"
    and "path g"
    and "path_image f \<subseteq> cbox (-1) 1"
    and "path_image g \<subseteq> cbox (-1) 1"
    and "(pathstart f)$1 = -1"
    and "(pathfinish f)$1 = 1"
    and "(pathstart g)$2 = -1"
    and "(pathfinish g)$2 = 1"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
sorry

theorem fashoda:
  fixes b :: "real^2"
  assumes "path f"
    and "path g"
    and "path_image f \<subseteq> cbox a b"
    and "path_image g \<subseteq> cbox a b"
    and "(pathstart f)$1 = a$1"
    and "(pathfinish f)$1 = b$1"
    and "(pathstart g)$2 = a$2"
    and "(pathfinish g)$2 = b$2"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some slightly ad hoc lemmas I use below\<close>

lemma segment_vertical:
  fixes a :: "real^2"
  assumes "a$1 = b$1"
  shows "x \<in> closed_segment a b \<longleftrightarrow>
    x$1 = a$1 \<and> x$1 = b$1 \<and> (a$2 \<le> x$2 \<and> x$2 \<le> b$2 \<or> b$2 \<le> x$2 \<and> x$2 \<le> a$2)"
  (is "_ = ?R")
sorry

text \<open>Essentially duplicate proof that could be done by swapping co-ordinates\<close>
lemma segment_horizontal:
  fixes a :: "real^2"
  assumes "a$2 = b$2"
  shows "x \<in> closed_segment a b \<longleftrightarrow>
    x$2 = a$2 \<and> x$2 = b$2 \<and> (a$1 \<le> x$1 \<and> x$1 \<le> b$1 \<or> b$1 \<le> x$1 \<and> x$1 \<le> a$1)"
  (is "_ = ?R")
sorry


subsection \<open>Useful Fashoda corollary pointed out to me by Tom Hales\<close>(*FIXME change title? *)

corollary fashoda_interlace:
  fixes a :: "real^2"
  assumes "path f"
    and "path g"
    and paf: "path_image f \<subseteq> cbox a b"
    and pag: "path_image g \<subseteq> cbox a b"
    and "(pathstart f)$2 = a$2"
    and "(pathfinish f)$2 = a$2"
    and "(pathstart g)$2 = a$2"
    and "(pathfinish g)$2 = a$2"
    and "(pathstart f)$1 < (pathstart g)$1"
    and "(pathstart g)$1 < (pathfinish f)$1"
    and "(pathfinish f)$1 < (pathfinish g)$1"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
sorry

end
