theory Cartan
imports "HOL-Complex_Analysis.Complex_Analysis"

begin

section\<open>First Cartan Theorem\<close>

text\<open>Ported from HOL Light. See
      Gianni Ciolli, Graziano Gentili, Marco Maggesi.
      A Certified Proof of the Cartan Fixed Point Theorems.
      J Automated Reasoning (2011) 47:319--336    DOI 10.1007/s10817-010-9198-6\<close>

lemma deriv_left_inverse:
  assumes "f holomorphic_on S" and "g holomorphic_on T"
      and "open S" and "open T"
      and "f ` S \<subseteq> T"
      and [simp]: "\<And>z. z \<in> S \<Longrightarrow> g (f z) = z"
      and "w \<in> S"
    shows "deriv f w * deriv g (f w) = 1"
sorry

lemma Cauchy_higher_deriv_bound:
    assumes holf: "f holomorphic_on (ball z r)"
        and contf: "continuous_on (cball z r) f"
        and "0 < r" and "0 < n"
        and fin : "\<And>w. w \<in> ball z r \<Longrightarrow> f w \<in> ball y B0"
      shows "norm ((deriv ^^ n) f z) \<le> (fact n) * B0 / r^n"
sorry

lemma higher_deriv_comp_lemma:
    assumes s: "open s" and holf: "f holomorphic_on s"
        and "z \<in> s"
        and t: "open t" and holg: "g holomorphic_on t"
        and fst: "f ` s \<subseteq> t"
        and n: "i \<le> n"
        and dfz: "deriv f z = 1" and zero: "\<And>i. \<lbrakk>1 < i; i \<le> n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f z = 0"
      shows "(deriv ^^ i) (g o f) z = (deriv ^^ i) g (f z)"
sorry

lemma higher_deriv_comp_iter_lemma:
    assumes s: "open s" and holf: "f holomorphic_on s"
        and fss: "f ` s \<subseteq> s"
        and "z \<in> s" and [simp]: "f z = z"
        and n: "i \<le> n"
        and dfz: "deriv f z = 1" and zero: "\<And>i. \<lbrakk>1 < i; i \<le> n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f z = 0"
      shows "(deriv ^^ i) (f^^m) z = (deriv ^^ i) f z"
sorry

lemma higher_deriv_iter_top_lemma:
    assumes s: "open s" and holf: "f holomorphic_on s"
        and fss: "f ` s \<subseteq> s"
        and "z \<in> s" and [simp]: "f z = z"
        and dfz [simp]: "deriv f z = 1"
        and n: "1 < n" "\<And>i. \<lbrakk>1 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f z = 0"
      shows "(deriv ^^ n) (f ^^ m) z = m * (deriv ^^ n) f z"
sorry

text\<open>Should be proved for n-dimensional vectors of complex numbers\<close>
theorem first_Cartan_dim_1:
    assumes holf: "f holomorphic_on s"
        and "open s" "connected s" "bounded s"
        and fss: "f ` s \<subseteq> s"
        and "z \<in> s" and [simp]: "f z = z"
        and dfz [simp]: "deriv f z = 1"
        and "w \<in> s"
      shows "f w = w"
sorry


text\<open>Second Cartan Theorem.\<close>

lemma Cartan_is_linear:
  assumes holf: "f holomorphic_on s"
      and "open s" and "connected s"
      and "0 \<in> s"
      and ins: "\<And>u z. \<lbrakk>norm u = 1; z \<in> s\<rbrakk> \<Longrightarrow> u * z \<in> s"
      and feq: "\<And>u z. \<lbrakk>norm u = 1; z \<in> s\<rbrakk> \<Longrightarrow> f (u * z) = u * f z"
    shows "\<exists>c. \<forall>z \<in> s. f z = c * z"
sorry

text\<open>Should be proved for n-dimensional vectors of complex numbers\<close>
theorem second_Cartan_dim_1:
  assumes holf: "f holomorphic_on ball 0 r"
      and holg: "g holomorphic_on ball 0 r"
      and [simp]: "f 0 = 0" and [simp]: "g 0 = 0"
      and ballf: "\<And>z. z \<in> ball 0 r \<Longrightarrow> f z \<in> ball 0 r"
      and ballg: "\<And>z. z \<in> ball 0 r \<Longrightarrow> g z \<in> ball 0 r"
      and fg: "\<And>z. z \<in> ball 0 r \<Longrightarrow> f (g z) = z"
      and gf: "\<And>z. z \<in> ball 0 r \<Longrightarrow> g (f z) = z"
      and "0 < r"
    shows "\<exists>t. \<forall>z \<in> ball 0 r. g z = exp(\<i> * of_real t) * z"
sorry

end
