(*  Title:      HOL/Analysis/Continuous_Extension.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>Continuous Extensions of Functions\<close>

theory Continuous_Extension
imports Starlike 
begin

subsection\<open>Partitions of unity subordinate to locally finite open coverings\<close>

text\<open>A difference from HOL Light: all summations over infinite sets equal zero,
   so the "support" must be made explicit in the summation below!\<close>

proposition subordinate_partition_of_unity:
  fixes S :: "'a::metric_space set"
  assumes "S \<subseteq> \<Union>\<C>" and opC: "\<And>T. T \<in> \<C> \<Longrightarrow> open T"
      and fin: "\<And>x. x \<in> S \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<C>. U \<inter> V \<noteq> {}}"
  obtains F :: "['a set, 'a] \<Rightarrow> real"
    where "\<And>U. U \<in> \<C> \<Longrightarrow> continuous_on S (F U) \<and> (\<forall>x \<in> S. 0 \<le> F U x)"
      and "\<And>x U. \<lbrakk>U \<in> \<C>; x \<in> S; x \<notin> U\<rbrakk> \<Longrightarrow> F U x = 0"
      and "\<And>x. x \<in> S \<Longrightarrow> supp_sum (\<lambda>W. F W x) \<C> = 1"
      and "\<And>x. x \<in> S \<Longrightarrow> \<exists>V. open V \<and> x \<in> V \<and> finite {U \<in> \<C>. \<exists>x\<in>V. F U x \<noteq> 0}"
sorry


subsection\<open>Urysohn's Lemma for Euclidean Spaces\<close>

text \<open>For Euclidean spaces the proof is easy using distances.\<close>

lemma Urysohn_both_ne:
  assumes US: "closedin (top_of_set U) S"
      and UT: "closedin (top_of_set U) T"
      and "S \<inter> T = {}" "S \<noteq> {}" "T \<noteq> {}" "a \<noteq> b"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
    where "continuous_on U f"
          "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a b"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = a \<longleftrightarrow> x \<in> S)"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = b \<longleftrightarrow> x \<in> T)"
sorry

lemma Urysohn_local_strong_aux:
  assumes US: "closedin (top_of_set U) S"
      and UT: "closedin (top_of_set U) T"
      and "S \<inter> T = {}" "a \<noteq> b" "S \<noteq> {}"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on U f"
          "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a b"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = a \<longleftrightarrow> x \<in> S)"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = b \<longleftrightarrow> x \<in> T)"
sorry

proposition Urysohn_local_strong:
  assumes US: "closedin (top_of_set U) S"
      and UT: "closedin (top_of_set U) T"
      and "S \<inter> T = {}" "a \<noteq> b"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on U f"
          "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a b"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = a \<longleftrightarrow> x \<in> S)"
          "\<And>x. x \<in> U \<Longrightarrow> (f x = b \<longleftrightarrow> x \<in> T)"
sorry

lemma Urysohn_local:
  assumes US: "closedin (top_of_set U) S"
      and UT: "closedin (top_of_set U) T"
      and "S \<inter> T = {}"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on U f"
          "\<And>x. x \<in> U \<Longrightarrow> f x \<in> closed_segment a b"
          "\<And>x. x \<in> S \<Longrightarrow> f x = a"
          "\<And>x. x \<in> T \<Longrightarrow> f x = b"
sorry

lemma Urysohn_strong:
  assumes US: "closed S"
      and UT: "closed T"
      and "S \<inter> T = {}" "a \<noteq> b"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on UNIV f"
          "\<And>x. f x \<in> closed_segment a b"
          "\<And>x. f x = a \<longleftrightarrow> x \<in> S"
          "\<And>x. f x = b \<longleftrightarrow> x \<in> T"
sorry

proposition Urysohn:
  assumes US: "closed S"
      and UT: "closed T"
      and "S \<inter> T = {}"
  obtains f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    where "continuous_on UNIV f"
          "\<And>x. f x \<in> closed_segment a b"
          "\<And>x. x \<in> S \<Longrightarrow> f x = a"
          "\<And>x. x \<in> T \<Longrightarrow> f x = b"
sorry

subsection\<open>Dugundji's Extension Theorem and Tietze Variants\<close>

text \<open>See \<^cite>\<open>"dugundji"\<close>.\<close>

theorem Dugundji:
  fixes f :: "'a::{metric_space,second_countable_topology} \<Rightarrow> 'b::real_inner"
  assumes "convex C" "C \<noteq> {}"
      and cloin: "closedin (top_of_set U) S"
      and contf: "continuous_on S f" and "f ` S \<subseteq> C"
  obtains g where "continuous_on U g" "g ` U \<subseteq> C"
                  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

corollary Tietze:
  fixes f :: "'a::{metric_space,second_countable_topology} \<Rightarrow> 'b::real_inner"
  assumes "continuous_on S f"
    and "closedin (top_of_set U) S"
    and "0 \<le> B"
    and "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> B"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    "\<And>x. x \<in> U \<Longrightarrow> norm(g x) \<le> B"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Tietze_closed_interval:
  fixes f :: "'a::{metric_space,second_countable_topology} \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on S f"
    and "closedin (top_of_set U) S"
    and "cbox a b \<noteq> {}"
    and "\<And>x. x \<in> S \<Longrightarrow> f x \<in> cbox a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    "\<And>x. x \<in> U \<Longrightarrow> g x \<in> cbox a b"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Tietze_closed_interval_1:
  fixes f :: "'a::{metric_space,second_countable_topology} \<Rightarrow> real"
  assumes "continuous_on S f"
    and "closedin (top_of_set U) S"
    and "a \<le> b"
    and "\<And>x. x \<in> S \<Longrightarrow> f x \<in> cbox a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    "\<And>x. x \<in> U \<Longrightarrow> g x \<in> cbox a b"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Tietze_open_interval:
  fixes f :: "'a::{metric_space,second_countable_topology} \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on S f"
    and "closedin (top_of_set U) S"
    and "box a b \<noteq> {}"
    and "\<And>x. x \<in> S \<Longrightarrow> f x \<in> box a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    "\<And>x. x \<in> U \<Longrightarrow> g x \<in> box a b"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Tietze_open_interval_1:
  fixes f :: "'a::{metric_space,second_countable_topology} \<Rightarrow> real"
  assumes "continuous_on S f"
    and "closedin (top_of_set U) S"
    and "a < b"
    and no: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> box a b"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    "\<And>x. x \<in> U \<Longrightarrow> g x \<in> box a b"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Tietze_unbounded:
  fixes f :: "'a::{metric_space,second_countable_topology} \<Rightarrow> 'b::real_inner"
  assumes "continuous_on S f"
    and "closedin (top_of_set U) S"
  obtains g where "continuous_on U g" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
sorry

end
