(*  Title:      HOL/Analysis/Vitali_Covering_Theorem.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section  \<open>Vitali Covering Theorem and an Application to Negligibility\<close>

theory Vitali_Covering_Theorem
imports
  "HOL-Combinatorics.Permutations"
  Equivalence_Lebesgue_Henstock_Integration
begin

lemma stretch_Galois:
  fixes x :: "real^'n"
  shows "(\<And>k. m k \<noteq> 0) \<Longrightarrow> ((y = (\<chi> k. m k * x$k)) \<longleftrightarrow> (\<chi> k. y$k / m k) = x)"
sorry

lemma lambda_swap_Galois:
   "(x = (\<chi> i. y $ Transposition.transpose m n i) \<longleftrightarrow> (\<chi> i. x $ Transposition.transpose m n i) = y)"
sorry

lemma lambda_add_Galois:
  fixes x :: "real^'n"
  shows "m \<noteq> n \<Longrightarrow> (x = (\<chi> i. if i = m then y$m + y$n else y$i) \<longleftrightarrow> (\<chi> i. if i = m then x$m - x$n else x$i) = y)"
sorry

lemma Vitali_covering_lemma_cballs_balls:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "\<And>i. i \<in> K \<Longrightarrow> 0 < r i \<and> r i \<le> B"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
     "\<And>i. i \<in> K \<Longrightarrow> \<exists>j. j \<in> C \<and>
                        \<not> disjnt (cball (a i) (r i)) (cball (a j) (r j)) \<and>
                        cball (a i) (r i) \<subseteq> ball (a j) (5 * r j)"
sorry

subsection\<open>Vitali covering theorem\<close>

lemma Vitali_covering_lemma_cballs:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<subseteq> (\<Union>i\<in>K. cball (a i) (r i))"
      and r: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i \<and> r i \<le> B"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
     "S \<subseteq> (\<Union>i\<in>C. cball (a i) (5 * r i))"
sorry

lemma Vitali_covering_lemma_balls:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes S: "S \<subseteq> (\<Union>i\<in>K. ball (a i) (r i))"
      and r: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i \<and> r i \<le> B"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (ball (a i) (r i)) (ball (a j) (r j))) C"
     "S \<subseteq> (\<Union>i\<in>C. ball (a i) (5 * r i))"
sorry

theorem Vitali_covering_theorem_cballs:
  fixes a :: "'a \<Rightarrow> 'n::euclidean_space"
  assumes r: "\<And>i. i \<in> K \<Longrightarrow> 0 < r i"
      and S: "\<And>x d. \<lbrakk>x \<in> S; 0 < d\<rbrakk>
                     \<Longrightarrow> \<exists>i. i \<in> K \<and> x \<in> cball (a i) (r i) \<and> r i < d"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (cball (a i) (r i)) (cball (a j) (r j))) C"
     "negligible(S - (\<Union>i \<in> C. cball (a i) (r i)))"
sorry

theorem Vitali_covering_theorem_balls:
  fixes a :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes S: "\<And>x d. \<lbrakk>x \<in> S; 0 < d\<rbrakk> \<Longrightarrow> \<exists>i. i \<in> K \<and> x \<in> ball (a i) (r i) \<and> r i < d"
  obtains C where "countable C" "C \<subseteq> K"
     "pairwise (\<lambda>i j. disjnt (ball (a i) (r i)) (ball (a j) (r j))) C"
     "negligible(S - (\<Union>i \<in> C. ball (a i) (r i)))"
sorry

lemma negligible_eq_zero_density_alt:
     "negligible S \<longleftrightarrow>
      (\<forall>x \<in> S. \<forall>e > 0.
        \<exists>d U. 0 < d \<and> d \<le> e \<and> S \<inter> ball x d \<subseteq> U \<and>
              U \<in> lmeasurable \<and> measure lebesgue U < e * measure lebesgue (ball x d))"
     (is "_ = (\<forall>x \<in> S. \<forall>e > 0. ?Q x e)")
sorry

proposition negligible_eq_zero_density:
   "negligible S \<longleftrightarrow>
    (\<forall>x\<in>S. \<forall>r>0. \<forall>e>0. \<exists>d. 0 < d \<and> d \<le> r \<and>
                   (\<exists>U. S \<inter> ball x d \<subseteq> U \<and> U \<in> lmeasurable \<and> measure lebesgue U < e * measure lebesgue (ball x d)))"
sorry

end
