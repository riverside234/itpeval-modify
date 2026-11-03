section \<open>The Great Picard Theorem and its Applications\<close>

text\<open>Ported from HOL Light (cauchy.ml) by L C Paulson, 2017\<close>

theory Great_Picard
  imports Conformal_Mappings
begin
  
subsection\<open>Schottky's theorem\<close>

lemma Schottky_lemma0:
  assumes holf: "f holomorphic_on S" and cons: "contractible S" and "a \<in> S"
      and f: "\<And>z. z \<in> S \<Longrightarrow> f z \<noteq> 1 \<and> f z \<noteq> -1"
  obtains g where "g holomorphic_on S"
                  "norm(g a) \<le> 1 + norm(f a) / 3"
                  "\<And>z. z \<in> S \<Longrightarrow> f z = cos(of_real pi * g z)"
sorry

lemma Schottky_lemma1:
  fixes n::nat
  assumes "0 < n"
  shows "0 < n + sqrt(real n ^ 2 - 1)"
sorry

lemma Schottky_lemma2:
  fixes x::real
  assumes "0 \<le> x"
  obtains n where "0 < n" "\<bar>x - ln (real n + sqrt ((real n)\<^sup>2 - 1)) / pi\<bar> < 1/2"
sorry

lemma Schottky_lemma3:
  fixes z::complex
  assumes "z \<in> (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (ln(n + sqrt(real n ^ 2 - 1)) / pi)})
             \<union> (\<Union>m \<in> Ints. \<Union>n \<in> {0<..}. {Complex m (-ln(n + sqrt(real n ^ 2 - 1)) / pi)})"
  shows "cos(pi * cos(pi * z)) = 1 \<or> cos(pi * cos(pi * z)) = -1"
sorry

theorem Schottky:
  assumes holf: "f holomorphic_on cball 0 1"
      and nof0: "norm(f 0) \<le> r"
      and not01: "\<And>z. z \<in> cball 0 1 \<Longrightarrow> \<not>(f z = 0 \<or> f z = 1)"
      and "0 < t" "t < 1" "norm z \<le> t"
    shows "norm(f z) \<le> exp(pi * exp(pi * (2 + 2 * r + 12 * t / (1 - t))))"
sorry

  
subsection\<open>The Little Picard Theorem\<close>

theorem Landau_Picard:
  obtains R
    where "\<And>z. 0 < R z"
          "\<And>f. \<lbrakk>f holomorphic_on cball 0 (R(f 0));
                 \<And>z. norm z \<le> R(f 0) \<Longrightarrow> f z \<noteq> 0 \<and> f z \<noteq> 1\<rbrakk> \<Longrightarrow> norm(deriv f 0) < 1"
sorry

lemma little_Picard_01:
  assumes holf: "f holomorphic_on UNIV" and f01: "\<And>z. f z \<noteq> 0 \<and> f z \<noteq> 1"
  obtains c where "f = (\<lambda>x. c)"
sorry

theorem little_Picard:
  assumes holf: "f holomorphic_on UNIV"
      and "a \<noteq> b" "range f \<inter> {a,b} = {}"
    obtains c where "f = (\<lambda>x. c)"
sorry


text\<open>A couple of little applications of Little Picard\<close>

lemma holomorphic_periodic_fixpoint:
  assumes holf: "f holomorphic_on UNIV"
      and "p \<noteq> 0" and per: "\<And>z. f(z + p) = f z"
  obtains x where "f x = x"
sorry

lemma holomorphic_involution_point:
  assumes holfU: "f holomorphic_on UNIV" and non: "\<And>a. f \<noteq> (\<lambda>x. a + x)"
  obtains x where "f(f x) = x"
sorry


subsection\<open>The Arzelà--Ascoli theorem\<close>

lemma subsequence_diagonalization_lemma:
  fixes P :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  assumes sub: "\<And>i r. \<exists>k. strict_mono (k :: nat \<Rightarrow> nat) \<and> P i (r \<circ> k)"
      and P_P:  "\<And>i r::nat \<Rightarrow> 'a. \<And>k1 k2 N.
                   \<lbrakk>P i (r \<circ> k1); \<And>j. N \<le> j \<Longrightarrow> \<exists>j'. j \<le> j' \<and> k2 j = k1 j'\<rbrakk> \<Longrightarrow> P i (r \<circ> k2)"
   obtains k where "strict_mono (k :: nat \<Rightarrow> nat)" "\<And>i. P i (r \<circ> k)"
sorry

lemma function_convergent_subsequence:
  fixes f :: "[nat,'a] \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes "countable S" and M: "\<And>n::nat. \<And>x. x \<in> S \<Longrightarrow> norm(f n x) \<le> M"
   obtains k where "strict_mono (k::nat\<Rightarrow>nat)" "\<And>x. x \<in> S \<Longrightarrow> \<exists>l. (\<lambda>n. f (k n) x) \<longlonglongrightarrow> l"
sorry

theorem Arzela_Ascoli:
  fixes \<F> :: "[nat,'a::euclidean_space] \<Rightarrow> 'b::{real_normed_vector,heine_borel}"
  assumes "compact S"
      and M: "\<And>n x. x \<in> S \<Longrightarrow> norm(\<F> n x) \<le> M"
      and equicont:
          "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk>
                 \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>n y. y \<in> S \<and> norm(x - y) < d \<longrightarrow> norm(\<F> n x - \<F> n y) < e)"
  obtains g k where "continuous_on S g" "strict_mono (k :: nat \<Rightarrow> nat)"
                    "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<and> x \<in> S \<longrightarrow> norm(\<F>(k n) x - g x) < e"
sorry


subsubsection\<^marker>\<open>tag important\<close>\<open>Montel's theorem\<close>

text\<open>a sequence of holomorphic functions uniformly bounded
on compact subsets of an open set S has a subsequence that converges to a
holomorphic function, and converges \emph{uniformly} on compact subsets of S.\<close>


theorem Montel:
  fixes \<F> :: "[nat,complex] \<Rightarrow> complex"
  assumes "open S"
      and \<H>: "\<And>h. h \<in> \<H> \<Longrightarrow> h holomorphic_on S"
      and bounded: "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>B. \<forall>h \<in> \<H>. \<forall> z \<in> K. norm(h z) \<le> B"
      and rng_f: "range \<F> \<subseteq> \<H>"
  obtains g r
    where "g holomorphic_on S" "strict_mono (r :: nat \<Rightarrow> nat)"
          "\<And>x. x \<in> S \<Longrightarrow> ((\<lambda>n. \<F> (r n) x) \<longlongrightarrow> g x) sequentially"
          "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K (\<F> \<circ> r) g sequentially"
sorry



subsection\<open>Some simple but useful cases of Hurwitz's theorem\<close>

proposition Hurwitz_no_zeros:
  assumes S: "open S" "connected S"
      and holf: "\<And>n::nat. \<F> n holomorphic_on S"
      and holg: "g holomorphic_on S"
      and ul_g: "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K \<F> g sequentially"
      and nonconst: "\<not> g constant_on S"
      and nz: "\<And>n z. z \<in> S \<Longrightarrow> \<F> n z \<noteq> 0"
      and "z0 \<in> S"
      shows "g z0 \<noteq> 0"
sorry

corollary Hurwitz_injective:
  assumes S: "open S" "connected S"
      and holf: "\<And>n::nat. \<F> n holomorphic_on S"
      and holg: "g holomorphic_on S"
      and ul_g: "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> uniform_limit K \<F> g sequentially"
      and nonconst: "\<not> g constant_on S"
      and inj: "\<And>n. inj_on (\<F> n) S"
    shows "inj_on g S"
sorry



subsection\<open>The Great Picard theorem\<close>

lemma GPicard1:
  assumes S: "open S" "connected S" and "w \<in> S" "0 < r" "Y \<subseteq> X"
      and holX: "\<And>h. h \<in> X \<Longrightarrow> h holomorphic_on S"
      and X01:  "\<And>h z. \<lbrakk>h \<in> X; z \<in> S\<rbrakk> \<Longrightarrow> h z \<noteq> 0 \<and> h z \<noteq> 1"
      and r:    "\<And>h. h \<in> Y \<Longrightarrow> norm(h w) \<le> r"
  obtains B Z where "0 < B" "open Z" "w \<in> Z" "Z \<subseteq> S" "\<And>h z. \<lbrakk>h \<in> Y; z \<in> Z\<rbrakk> \<Longrightarrow> norm(h z) \<le> B"
sorry

lemma GPicard2:
  assumes "S \<subseteq> T" "connected T" "S \<noteq> {}" "open S" "\<And>x. \<lbrakk>x islimpt S; x \<in> T\<rbrakk> \<Longrightarrow> x \<in> S"
    shows "S = T"
sorry

lemma GPicard3:
  assumes S: "open S" "connected S" "w \<in> S" and "Y \<subseteq> X"
      and holX: "\<And>h. h \<in> X \<Longrightarrow> h holomorphic_on S"
      and X01:  "\<And>h z. \<lbrakk>h \<in> X; z \<in> S\<rbrakk> \<Longrightarrow> h z \<noteq> 0 \<and> h z \<noteq> 1"
      and no_hw_le1: "\<And>h. h \<in> Y \<Longrightarrow> norm(h w) \<le> 1"
      and "compact K" "K \<subseteq> S"
  obtains B where "\<And>h z. \<lbrakk>h \<in> Y; z \<in> K\<rbrakk> \<Longrightarrow> norm(h z) \<le> B"
sorry

lemma GPicard4:
  assumes "0 < k" and holf: "f holomorphic_on (ball 0 k - {0})" 
      and AE: "\<And>e. \<lbrakk>0 < e; e < k\<rbrakk> \<Longrightarrow> \<exists>d. 0 < d \<and> d < e \<and> (\<forall>z \<in> sphere 0 d. norm(f z) \<le> B)"
  obtains \<epsilon> where "0 < \<epsilon>" "\<epsilon> < k" "\<And>z. z \<in> ball 0 \<epsilon> - {0} \<Longrightarrow> norm(f z) \<le> B"
sorry

lemma GPicard5:
  assumes holf: "f holomorphic_on (ball 0 1 - {0})"
      and f01:  "\<And>z. z \<in> ball 0 1 - {0} \<Longrightarrow> f z \<noteq> 0 \<and> f z \<noteq> 1"
  obtains e B where "0 < e" "e < 1" "0 < B" 
                    "(\<forall>z \<in> ball 0 e - {0}. norm(f z) \<le> B) \<or>
                     (\<forall>z \<in> ball 0 e - {0}. norm(f z) \<ge> B)"
sorry

lemma GPicard6:
  assumes "open M" "z \<in> M" "a \<noteq> 0" and holf: "f holomorphic_on (M - {z})"
      and f0a: "\<And>w. w \<in> M - {z} \<Longrightarrow> f w \<noteq> 0 \<and> f w \<noteq> a"
  obtains r where "0 < r" "ball z r \<subseteq> M" 
                  "bounded(f ` (ball z r - {z})) \<or>
                   bounded((inverse \<circ> f) ` (ball z r - {z}))"
sorry

theorem great_Picard:
  assumes "open M" "z \<in> M" "a \<noteq> b" and holf: "f holomorphic_on (M - {z})"
      and fab: "\<And>w. w \<in> M - {z} \<Longrightarrow> f w \<noteq> a \<and> f w \<noteq> b"
  obtains l where "(f \<longlongrightarrow> l) (at z) \<or> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
sorry

corollary great_Picard_alt:
  assumes M: "open M" "z \<in> M" and holf: "f holomorphic_on (M - {z})"
    and non: "\<And>l. \<not> (f \<longlongrightarrow> l) (at z)" "\<And>l. \<not> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
  obtains a where "- {a} \<subseteq> f ` (M - {z})"
sorry

corollary great_Picard_infinite:
  assumes M: "open M" "z \<in> M" and holf: "f holomorphic_on (M - {z})"
    and non: "\<And>l. \<not> (f \<longlongrightarrow> l) (at z)" "\<And>l. \<not> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
  obtains a where "\<And>w. w \<noteq> a \<Longrightarrow> infinite {x. x \<in> M - {z} \<and> f x = w}"
sorry

theorem Casorati_Weierstrass:
  assumes "open M" "z \<in> M" "f holomorphic_on (M - {z})"
      and "\<And>l. \<not> (f \<longlongrightarrow> l) (at z)" "\<And>l. \<not> ((inverse \<circ> f) \<longlongrightarrow> l) (at z)"
  shows "closure(f ` (M - {z})) = UNIV"
sorry
  
end
