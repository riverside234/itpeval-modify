(*  Title:      HOL/Analysis/Tagged_Division.thy
    Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light); proofs reworked by LCP
*)

section \<open>Tagged Divisions for Henstock-Kurzweil Integration\<close>

theory Tagged_Division
  imports Topology_Euclidean_Space
begin

lemma sum_Sigma_product:
  assumes "finite S"
    and "\<And>i. i \<in> S \<Longrightarrow> finite (T i)"
  shows "(\<Sum>i\<in>S. sum (x i) (T i)) = (\<Sum>(i, j)\<in>Sigma S T. x i j)"
sorry

lemmas scaleR_simps = scaleR_zero_left scaleR_minus_left scaleR_left_diff_distrib
  scaleR_zero_right scaleR_minus_right scaleR_right_diff_distrib scaleR_eq_0_iff
  scaleR_cancel_left scaleR_cancel_right scaleR_add_right scaleR_add_left real_vector_class.scaleR_one


subsection \<open>Some useful lemmas about intervals\<close>

lemma interior_subset_union_intervals:
  fixes a b c d
  defines "i \<equiv> cbox a b"
  defines "j \<equiv> cbox c d"
  assumes "interior j \<noteq> {}"
    and "i \<subseteq> j \<union> S"
    and "interior i \<inter> interior j = {}"
  shows "interior i \<subseteq> interior S"
sorry

lemma interior_Union_subset_cbox:
  assumes "finite \<F>"
  assumes \<F>: "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>a b. S = cbox a b" "\<And>S. S \<in> \<F> \<Longrightarrow> interior S \<subseteq> T"
    and T: "closed T"
  shows "interior (\<Union>\<F>) \<subseteq> T"
sorry

lemma Int_interior_Union_intervals:
    "\<lbrakk>finite \<F>; open S; \<And>T. T\<in>\<F> \<Longrightarrow> \<exists>a b. T = cbox a b; \<And>T. T\<in>\<F> \<Longrightarrow> S \<inter> (interior T) = {}\<rbrakk> 
    \<Longrightarrow> S \<inter> interior (\<Union>\<F>) = {}"
sorry

lemma interval_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows
    "cbox a b \<inter> {x. x\<bullet>k \<le> c} = cbox a (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) c else b\<bullet>i) *\<^sub>R i)"
    "cbox a b \<inter> {x. x\<bullet>k \<ge> c} = cbox (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) c else a\<bullet>i) *\<^sub>R i) b"
sorry

lemma interval_not_empty: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> cbox a b \<noteq> {}"
sorry

subsection \<open>Bounds on intervals where they exist\<close>

definition\<^marker>\<open>tag important\<close> interval_upperbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
  where "interval_upperbound s = (\<Sum>i\<in>Basis. (SUP x\<in>s. x\<bullet>i) *\<^sub>R i)"

definition\<^marker>\<open>tag important\<close> interval_lowerbound :: "('a::euclidean_space) set \<Rightarrow> 'a"
  where "interval_lowerbound s = (\<Sum>i\<in>Basis. (INF x\<in>s. x\<bullet>i) *\<^sub>R i)"

lemma interval_upperbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_upperbound (cbox a b) = (b::'a::euclidean_space)"
sorry

lemma interval_lowerbound[simp]:
  "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow>
    interval_lowerbound (cbox a b) = (a::'a::euclidean_space)"
sorry

lemmas interval_bounds = interval_upperbound interval_lowerbound

lemma
  fixes X::"real set"
  shows interval_upperbound_real[simp]: "interval_upperbound X = Sup X"
    and interval_lowerbound_real[simp]: "interval_lowerbound X = Inf X"
sorry

lemma interval_bounds'[simp]:
  assumes "cbox a b \<noteq> {}"
  shows "interval_upperbound (cbox a b) = b"
    and "interval_lowerbound (cbox a b) = a"
sorry

lemma interval_upperbound_Times:
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "interval_upperbound (A \<times> B) = (interval_upperbound A, interval_upperbound B)"
sorry

lemma interval_lowerbound_Times:
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "interval_lowerbound (A \<times> B) = (interval_lowerbound A, interval_lowerbound B)"
sorry

subsection \<open>The notion of a gauge --- simply an open set containing the point\<close>

definition\<^marker>\<open>tag important\<close> "gauge \<gamma> \<longleftrightarrow> (\<forall>x. x \<in> \<gamma> x \<and> open (\<gamma> x))"

lemma gaugeI:
  assumes "\<And>x. x \<in> \<gamma> x" and "\<And>x. open (\<gamma> x)"
  shows "gauge \<gamma>"
sorry

lemma gaugeD[dest]:
  assumes "gauge \<gamma>" shows "x \<in> \<gamma> x"
    and "open (\<gamma> x)"
sorry

lemma gauge_ball_dependent: "\<forall>x. 0 < e x \<Longrightarrow> gauge (\<lambda>x. ball x (e x))"
sorry

lemma gauge_ball[intro]: "0 < e \<Longrightarrow> gauge (\<lambda>x. ball x e)"
sorry

lemma gauge_trivial[intro!]: "gauge (\<lambda>x. ball x 1)"
sorry

lemma gauge_Int[intro]: "gauge \<gamma>1 \<Longrightarrow> gauge \<gamma>2 \<Longrightarrow> gauge (\<lambda>x. \<gamma>1 x \<inter> \<gamma>2 x)"
sorry

lemma gauge_reflect:
  fixes \<gamma> :: "'a::euclidean_space \<Rightarrow> 'a set"
  shows "gauge \<gamma> \<Longrightarrow> gauge (\<lambda>x. uminus ` \<gamma> (- x))"
sorry

lemma gauge_Inter:
  assumes "finite S"
    and "\<And>u. u\<in>S \<Longrightarrow> gauge (f u)"
  shows "gauge (\<lambda>x. \<Inter>{f u x | u. u \<in> S})"
sorry

lemma gauge_existence_lemma:
  "(\<forall>x. \<exists>d :: real. p x \<longrightarrow> 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. p x \<longrightarrow> q d x)"
sorry

subsection \<open>Attempt a systematic general set of "offset" results for components\<close>
(*FIXME Restructure, the subsection consists only of 1 lemma *)
lemma gauge_modify:
  assumes "(\<forall>S. open S \<longrightarrow> open {x. f(x) \<in> S})" "gauge d"
  shows "gauge (\<lambda>x. {y. f y \<in> d (f x)})"
sorry

subsection \<open>Divisions\<close>

definition\<^marker>\<open>tag important\<close> division_of (infixl \<open>division'_of\<close> 40)
where
  "s division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>K\<in>s. K \<subseteq> i \<and> K \<noteq> {} \<and> (\<exists>a b. K = cbox a b)) \<and>
    (\<forall>K1\<in>s. \<forall>K2\<in>s. K1 \<noteq> K2 \<longrightarrow> interior(K1) \<inter> interior(K2) = {}) \<and>
    (\<Union>s = i)"

lemma division_ofD[dest]:
  assumes "s division_of i"
  shows "finite s"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<noteq> {}"
    and "\<And>K. K \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>K1 K2. K1 \<in> s \<Longrightarrow> K2 \<in> s \<Longrightarrow> K1 \<noteq> K2 \<Longrightarrow> interior(K1) \<inter> interior(K2) = {}"
    and "\<Union>s = i"
sorry

lemma division_ofI:
  assumes "finite s"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>K. K \<in> s \<Longrightarrow> K \<noteq> {}"
    and "\<And>K. K \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>K1 K2. K1 \<in> s \<Longrightarrow> K2 \<in> s \<Longrightarrow> K1 \<noteq> K2 \<Longrightarrow> interior K1 \<inter> interior K2 = {}"
    and "\<Union>s = i"
  shows "s division_of i"
sorry

lemma division_of_finite: "s division_of i \<Longrightarrow> finite s"
sorry

lemma division_of_self[intro]: "cbox a b \<noteq> {} \<Longrightarrow> {cbox a b} division_of (cbox a b)"
sorry

lemma division_of_trivial[simp]: "s division_of {} \<longleftrightarrow> s = {}"
sorry

lemma division_of_sing[simp]:
  "s division_of cbox a (a::'a::euclidean_space) \<longleftrightarrow> s = {cbox a a}"
  (is "?l = ?r")
sorry

lemma elementary_empty: obtains p where "p division_of {}"
sorry

lemma elementary_interval: obtains p where "p division_of (cbox a b)"
sorry

lemma division_contains: "s division_of i \<Longrightarrow> \<forall>x\<in>i. \<exists>k\<in>s. x \<in> k"
sorry

lemma forall_in_division:
  "d division_of i \<Longrightarrow> (\<forall>x\<in>d. P x) \<longleftrightarrow> (\<forall>a b. cbox a b \<in> d \<longrightarrow> P (cbox a b))"
sorry

lemma cbox_division_memE:
  assumes \<D>: "K \<in> \<D>" "\<D> division_of S"
  obtains a b where "K = cbox a b" "K \<noteq> {}" "K \<subseteq> S"
sorry

lemma division_of_subset:
  assumes "p division_of (\<Union>p)"
    and "q \<subseteq> p"
  shows "q division_of (\<Union>q)"
sorry

lemma division_of_union_self[intro]: "p division_of s \<Longrightarrow> p division_of (\<Union>p)"
sorry

lemma division_inter:
  fixes s1 s2 :: "'a::euclidean_space set"
  assumes "p1 division_of s1"
    and "p2 division_of s2"
  shows "{k1 \<inter> k2 | k1 k2. k1 \<in> p1 \<and> k2 \<in> p2 \<and> k1 \<inter> k2 \<noteq> {}} division_of (s1 \<inter> s2)"
  (is "?A' division_of _")
sorry

lemma division_inter_1:
  assumes "d division_of i"
    and "cbox a (b::'a::euclidean_space) \<subseteq> i"
  shows "{cbox a b \<inter> k | k. k \<in> d \<and> cbox a b \<inter> k \<noteq> {}} division_of (cbox a b)"
sorry

lemma elementary_Int:
  fixes s t :: "'a::euclidean_space set"
  assumes "p1 division_of s" and "p2 division_of t"
  shows "\<exists>p. p division_of (s \<inter> t)"
sorry

lemma elementary_Inter:
  assumes "finite \<F>"
    and "\<F> \<noteq> {}"
    and "\<forall>s\<in>\<F>. \<exists>p. p division_of (s::('a::euclidean_space) set)"
  shows "\<exists>p. p division_of (\<Inter>\<F>)"
sorry

lemma division_disjoint_union:
  assumes "p1 division_of s1"
    and "p2 division_of s2"
    and "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) division_of (s1 \<union> s2)"
sorry

lemma partial_division_extend_1:
  fixes a b c d :: "'a::euclidean_space"
  assumes incl: "cbox c d \<subseteq> cbox a b"
    and nonempty: "cbox c d \<noteq> {}"
  obtains p where "p division_of (cbox a b)" "cbox c d \<in> p"
sorry

proposition partial_division_extend_interval:
  assumes "p division_of (\<Union>p)" "(\<Union>p) \<subseteq> cbox a b"
  obtains q where "p \<subseteq> q" "q division_of cbox a (b::'a::euclidean_space)"
sorry

lemma elementary_bounded[dest]:
  shows "p division_of S \<Longrightarrow> bounded S"
sorry

lemma elementary_subset_cbox:
  "p division_of S \<Longrightarrow> \<exists>a b. S \<subseteq> cbox a b"
sorry

proposition division_union_intervals_exists:
  assumes "cbox a b \<noteq> {}"
  obtains p where "(insert (cbox a b) p) division_of (cbox a b \<union> cbox c d)"
sorry

lemma division_of_Union:
  assumes "finite f"
    and "\<And>p. p \<in> f \<Longrightarrow> p division_of (\<Union>p)"
    and "\<And>k1 k2. k1 \<in> \<Union>f \<Longrightarrow> k2 \<in> \<Union>f \<Longrightarrow> k1 \<noteq> k2 \<Longrightarrow> interior k1 \<inter> interior k2 = {}"
  shows "\<Union>f division_of \<Union>(\<Union>f)"
sorry

lemma elementary_union_interval:
  fixes a b :: "'a::euclidean_space"
  assumes "p division_of \<Union>p"
  obtains q where "q division_of (cbox a b \<union> \<Union>p)"
sorry

lemma elementary_unions_intervals:
  assumes fin: "finite \<F>"
    and "\<And>s. s \<in> \<F> \<Longrightarrow> \<exists>a b. s = cbox a (b::'a::euclidean_space)"
  obtains p where "p division_of (\<Union>\<F>)"
sorry

lemma elementary_union:
  assumes "ps division_of S" "pt division_of T"
  obtains p where "p division_of (S \<union> T)"
sorry

lemma partial_division_extend:
  fixes T :: "'a::euclidean_space set"
  assumes "p division_of S"
    and "q division_of T"
    and "S \<subseteq> T"
  obtains r where "p \<subseteq> r" and "r division_of T"
sorry

lemma division_split:
  assumes "p division_of (cbox a b)"
    and k: "k\<in>Basis"
  shows "{l \<inter> {x. x\<bullet>k \<le> c} | l. l \<in> p \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} division_of(cbox a b \<inter> {x. x\<bullet>k \<le> c})"
      (is "?p1 division_of ?I1")
    and "{l \<inter> {x. x\<bullet>k \<ge> c} | l. l \<in> p \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}} division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
      (is "?p2 division_of ?I2")
sorry

subsection \<open>Tagged (partial) divisions\<close>

definition\<^marker>\<open>tag important\<close> tagged_partial_division_of (infixr \<open>tagged'_partial'_division'_of\<close> 40)
  where "s tagged_partial_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x K. (x, K) \<in> s \<longrightarrow> x \<in> K \<and> K \<subseteq> i \<and> (\<exists>a b. K = cbox a b)) \<and>
    (\<forall>x1 K1 x2 K2. (x1, K1) \<in> s \<and> (x2, K2) \<in> s \<and> (x1, K1) \<noteq> (x2, K2) \<longrightarrow>
      interior K1 \<inter> interior K2 = {})"

lemma tagged_partial_division_ofD:
  assumes "s tagged_partial_division_of i"
  shows "finite s"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> x \<in> K"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>x1 K1 x2 K2. (x1,K1) \<in> s \<Longrightarrow>
      (x2, K2) \<in> s \<Longrightarrow> (x1, K1) \<noteq> (x2, K2) \<Longrightarrow> interior K1 \<inter> interior K2 = {}"
sorry

definition\<^marker>\<open>tag important\<close> tagged_division_of (infixr \<open>tagged'_division'_of\<close> 40)
  where "s tagged_division_of i \<longleftrightarrow> s tagged_partial_division_of i \<and> (\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"

lemma tagged_division_of_finite: "s tagged_division_of i \<Longrightarrow> finite s"
sorry

lemma tagged_division_of:
  "s tagged_division_of i \<longleftrightarrow>
    finite s \<and>
    (\<forall>x K. (x, K) \<in> s \<longrightarrow> x \<in> K \<and> K \<subseteq> i \<and> (\<exists>a b. K = cbox a b)) \<and>
    (\<forall>x1 K1 x2 K2. (x1, K1) \<in> s \<and> (x2, K2) \<in> s \<and> (x1, K1) \<noteq> (x2, K2) \<longrightarrow>
      interior K1 \<inter> interior K2 = {}) \<and>
    (\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"
sorry

lemma tagged_division_ofI:
  assumes "finite s"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> x \<in> K"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>x1 K1 x2 K2. (x1,K1) \<in> s \<Longrightarrow> (x2, K2) \<in> s \<Longrightarrow> (x1, K1) \<noteq> (x2, K2) \<Longrightarrow>
      interior K1 \<inter> interior K2 = {}"
    and "(\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"
  shows "s tagged_division_of i"
sorry

lemma tagged_division_ofD[dest]: 
  assumes "s tagged_division_of i"
  shows "finite s"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> x \<in> K"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> K \<subseteq> i"
    and "\<And>x K. (x,K) \<in> s \<Longrightarrow> \<exists>a b. K = cbox a b"
    and "\<And>x1 K1 x2 K2. (x1, K1) \<in> s \<Longrightarrow> (x2, K2) \<in> s \<Longrightarrow> (x1, K1) \<noteq> (x2, K2) \<Longrightarrow>
      interior K1 \<inter> interior K2 = {}"
    and "(\<Union>{K. \<exists>x. (x,K) \<in> s} = i)"
sorry

lemma division_of_tagged_division:
  assumes "s tagged_division_of i"
  shows "(snd ` s) division_of i"
sorry

lemma partial_division_of_tagged_division:
  assumes "s tagged_partial_division_of i"
  shows "(snd ` s) division_of \<Union>(snd ` s)"
sorry

lemma tagged_partial_division_subset:
  assumes "s tagged_partial_division_of i" and "t \<subseteq> s"
  shows "t tagged_partial_division_of i"
sorry

lemma tag_in_interval: "p tagged_division_of i \<Longrightarrow> (x, k) \<in> p \<Longrightarrow> x \<in> i"
sorry

lemma tagged_division_of_empty: "{} tagged_division_of {}"
sorry

lemma tagged_partial_division_of_trivial[simp]: "p tagged_partial_division_of {} \<longleftrightarrow> p = {}"
sorry

lemma tagged_division_of_trivial[simp]: "p tagged_division_of {} \<longleftrightarrow> p = {}"
sorry

lemma tagged_division_of_self: "x \<in> cbox a b \<Longrightarrow> {(x,cbox a b)} tagged_division_of (cbox a b)"
sorry

lemma tagged_division_of_self_real: "x \<in> {a .. b::real} \<Longrightarrow> {(x,{a .. b})} tagged_division_of {a .. b}"
sorry

lemma tagged_division_Un:
  assumes "p1 tagged_division_of s1"
    and "p2 tagged_division_of s2"
    and "interior s1 \<inter> interior s2 = {}"
  shows "(p1 \<union> p2) tagged_division_of (s1 \<union> s2)"
sorry

lemma tagged_division_Union:
  assumes "finite I"
    and tag: "\<And>i. i\<in>I \<Longrightarrow> pfn i tagged_division_of i"
    and disj: "\<And>i1 i2. \<lbrakk>i1 \<in> I; i2 \<in> I; i1 \<noteq> i2\<rbrakk> \<Longrightarrow> interior(i1) \<inter> interior(i2) = {}"
  shows "\<Union>(pfn ` I) tagged_division_of (\<Union>I)"
sorry

lemma tagged_partial_division_of_Union_self:
  assumes "p tagged_partial_division_of s"
  shows "p tagged_division_of (\<Union>(snd ` p))"
sorry

lemma tagged_division_of_union_self:
  assumes "p tagged_division_of s"
  shows "p tagged_division_of (\<Union>(snd ` p))"
sorry

lemma tagged_division_Un_interval:
  assumes "p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> (c::real)})"
    and "p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(p1 \<union> p2) tagged_division_of (cbox a b)"
sorry

lemma tagged_division_Un_interval_real:
  fixes a :: real
  assumes "p1 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<le> (c::real)})"
    and "p2 tagged_division_of ({a .. b} \<inter> {x. x\<bullet>k \<ge> c})"
    and k: "k \<in> Basis"
  shows "(p1 \<union> p2) tagged_division_of {a .. b}"
sorry

lemma tagged_division_split_left_inj:
  assumes d: "d tagged_division_of i"
    and tags: "(x1, K1) \<in> d" "(x2, K2) \<in> d"
    and "K1 \<noteq> K2"
    and eq: "K1 \<inter> {x. x \<bullet> k \<le> c} = K2 \<inter> {x. x \<bullet> k \<le> c}"
  shows "interior (K1 \<inter> {x. x\<bullet>k \<le> c}) = {}"
sorry

lemma tagged_division_split_right_inj:
  assumes d: "d tagged_division_of i"
    and tags: "(x1, K1) \<in> d" "(x2, K2) \<in> d"
    and "K1 \<noteq> K2"
    and eq: "K1 \<inter> {x. x\<bullet>k \<ge> c} = K2 \<inter> {x. x\<bullet>k \<ge> c}"
  shows "interior (K1 \<inter> {x. x\<bullet>k \<ge> c}) = {}"
sorry

lemma (in comm_monoid_set) over_tagged_division_lemma:
  assumes "p tagged_division_of i"
    and "\<And>u v. box u v = {} \<Longrightarrow> d (cbox u v) = \<^bold>1"
  shows "F (\<lambda>(_, k). d k) p = F d (snd ` p)"
sorry


subsection \<open>Functions closed on boxes: morphisms from boxes to monoids\<close>

text \<open>This auxiliary structure is used to sum up over the elements of a division. Main theorem is
  \<open>operative_division\<close>. Instances for the monoid are \<^typ>\<open>'a option\<close>, \<^typ>\<open>real\<close>, and
  \<^typ>\<open>bool\<close>.\<close>

paragraph\<^marker>\<open>tag important\<close> \<open>Using additivity of lifted function to encode definedness.\<close>
text \<open>%whitespace\<close>
definition\<^marker>\<open>tag important\<close> lift_option :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option"
where
  "lift_option f a' b' = Option.bind a' (\<lambda>a. Option.bind b' (\<lambda>b. Some (f a b)))"

lemma lift_option_simps[simp]:
  "lift_option f (Some a) (Some b) = Some (f a b)"
  "lift_option f None b' = None"
  "lift_option f a' None = None"
sorry

lemma\<^marker>\<open>tag important\<close> comm_monoid_lift_option:
  assumes "comm_monoid f z"
  shows "comm_monoid (lift_option f) (Some z)"
sorry

lemma comm_monoid_set_and: "comm_monoid_set HOL.conj True"
sorry

paragraph \<open>Misc\<close>

lemma interval_real_split:
  "{a .. b::real} \<inter> {x. x \<le> c} = {a .. min b c}"
  "{a .. b} \<inter> {x. c \<le> x} = {max a c .. b}"
sorry

lemma bgauge_existence_lemma: "(\<forall>x\<in>s. \<exists>d::real. 0 < d \<and> q d x) \<longleftrightarrow> (\<forall>x. \<exists>d>0. x\<in>s \<longrightarrow> q d x)"
sorry

paragraph \<open>Division points\<close>
text \<open>%whitespace\<close>
definition\<^marker>\<open>tag important\<close> "division_points (k::('a::euclidean_space) set) d =
   {(j,x). j \<in> Basis \<and> (interval_lowerbound k)\<bullet>j < x \<and> x < (interval_upperbound k)\<bullet>j \<and>
     (\<exists>i\<in>d. (interval_lowerbound i)\<bullet>j = x \<or> (interval_upperbound i)\<bullet>j = x)}"

lemma division_points_finite:
  fixes i :: "'a::euclidean_space set"
  assumes "d division_of i"
  shows "finite (division_points i d)"
sorry

lemma division_points_subset:
  fixes a :: "'a::euclidean_space"
  assumes "d division_of (cbox a b)"
    and "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"  "a\<bullet>k < c" "c < b\<bullet>k"
    and k: "k \<in> Basis"
  shows "division_points (cbox a b \<inter> {x. x\<bullet>k \<le> c}) {l \<inter> {x. x\<bullet>k \<le> c} | l . l \<in> d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} \<subseteq>
      division_points (cbox a b) d" (is ?t1)
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l . l \<in> d \<and> \<not>(l \<inter> {x. x\<bullet>k \<ge> c} = {})} \<subseteq>
      division_points (cbox a b) d" (is ?t2)
sorry

lemma division_points_psubset:
  fixes a :: "'a::euclidean_space"
  assumes d: "d division_of (cbox a b)"
      and altb: "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i"  "a\<bullet>k < c" "c < b\<bullet>k"
      and "l \<in> d"
      and disj: "interval_lowerbound l\<bullet>k = c \<or> interval_upperbound l\<bullet>k = c"
      and k: "k \<in> Basis"
  shows "division_points (cbox a b \<inter> {x. x\<bullet>k \<le> c}) {l \<inter> {x. x\<bullet>k \<le> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<le> c} \<noteq> {}} \<subset>
         division_points (cbox a b) d" (is "?D1 \<subset> ?D")
    and "division_points (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) {l \<inter> {x. x\<bullet>k \<ge> c} | l. l\<in>d \<and> l \<inter> {x. x\<bullet>k \<ge> c} \<noteq> {}} \<subset>
         division_points (cbox a b) d" (is "?D2 \<subset> ?D")
sorry

lemma division_split_left_inj:
  fixes S :: "'a::euclidean_space set"
  assumes div: "\<D> division_of S"
    and eq: "K1 \<inter> {x::'a. x\<bullet>k \<le> c} = K2 \<inter> {x. x\<bullet>k \<le> c}"
    and "K1 \<in> \<D>" "K2 \<in> \<D>" "K1 \<noteq> K2"
  shows "interior (K1 \<inter> {x. x\<bullet>k \<le> c}) = {}"
sorry

lemma division_split_right_inj:
  fixes S :: "'a::euclidean_space set"
  assumes div: "\<D> division_of S"
    and eq: "K1 \<inter> {x::'a. x\<bullet>k \<ge> c} = K2 \<inter> {x. x\<bullet>k \<ge> c}"
    and "K1 \<in> \<D>" "K2 \<in> \<D>" "K1 \<noteq> K2"
  shows "interior (K1 \<inter> {x. x\<bullet>k \<ge> c}) = {}"
sorry

lemma interval_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "cbox a b \<inter> {x . \<bar>x\<bullet>k - c\<bar> \<le> (e::real)} =
    cbox (\<Sum>i\<in>Basis. (if i = k then max (a\<bullet>k) (c - e) else a\<bullet>i) *\<^sub>R i)
     (\<Sum>i\<in>Basis. (if i = k then min (b\<bullet>k) (c + e) else b\<bullet>i) *\<^sub>R i)"
sorry

lemma division_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "p division_of (cbox a b)"
    and k: "k \<in> Basis"
  shows "(\<lambda>l. l \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> e}) ` {l\<in>p. l \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> e} \<noteq> {}}
         division_of  (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> e})"
sorry

              
paragraph \<open>Operative\<close>

locale operative = comm_monoid_set +
  fixes g :: "'b::euclidean_space set \<Rightarrow> 'a"
  assumes box_empty_imp: "\<And>a b. box a b = {} \<Longrightarrow> g (cbox a b) = \<^bold>1"
    and Basis_imp: "\<And>a b c k. k \<in> Basis \<Longrightarrow> g (cbox a b) = g (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
begin

lemma empty [simp]: "g {} = \<^bold>1"
sorry

lemma division:
  "F g d = g (cbox a b)" if "d division_of (cbox a b)"
sorry

proposition tagged_division:
  assumes "d tagged_division_of (cbox a b)"
  shows "F (\<lambda>(_, l). g l) d = g (cbox a b)"
sorry
end

locale operative_real = comm_monoid_set +
  fixes g :: "real set \<Rightarrow> 'a"
  assumes neutral: "b \<le> a \<Longrightarrow> g {a..b} = \<^bold>1"
  assumes coalesce_less: "a < c \<Longrightarrow> c < b \<Longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}"
begin

sublocale operative where g = g
  rewrites "box = (greaterThanLessThan :: real \<Rightarrow> _)"
    and "cbox = (atLeastAtMost :: real \<Rightarrow> _)"
    and "\<And>x::real. x \<in> Basis \<longleftrightarrow> x = 1"
proof -
  show "operative f z g"
  proof
    show "g (cbox a b) = \<^bold>1" if "box a b = {}" for a b
      using that by (simp add: neutral)
    show "g (cbox a b) = g (cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. c \<le> x \<bullet> k})"
      if "k \<in> Basis" for a b c k
    proof -
      from that have [simp]: "k = 1"
        by simp
      from neutral [of 0 1] neutral [of a a for a] coalesce_less
      have [simp]: "g {} = \<^bold>1" "\<And>a. g {a} = \<^bold>1"
        "\<And>a b c. a < c \<Longrightarrow> c < b \<Longrightarrow> g {a..c} \<^bold>* g {c..b} = g {a..b}"
        by auto
      have "g {a..b} = g {a..min b c} \<^bold>* g {max a c..b}"
        by (auto simp: min_def max_def le_less)
      then show "g (cbox a b) = g (cbox a b \<inter> {x. x \<bullet> k \<le> c}) \<^bold>* g (cbox a b \<inter> {x. c \<le> x \<bullet> k})"
        by (simp add: atMost_def [symmetric] atLeast_def [symmetric])
    qed
  qed
  show "box = (greaterThanLessThan :: real \<Rightarrow> _)"
    and "cbox = (atLeastAtMost :: real \<Rightarrow> _)"
    and "\<And>x::real. x \<in> Basis \<longleftrightarrow> x = 1"
    by (simp_all add: fun_eq_iff)
qed

lemma coalesce_less_eq:
  "g {a..c} \<^bold>* g {c..b} = g {a..b}" if "a \<le> c" "c \<le> b"
sorry

end

lemma operative_realI:
  "operative_real f z g" if "operative f z g"
sorry


subsection \<open>Special case of additivity we need for the FTC\<close>
(*fix add explanation here *)

lemma additive_tagged_division_1:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "a \<le> b"
    and "p tagged_division_of {a..b}"
  shows "sum (\<lambda>(x,K). f(Sup K) - f(Inf K)) p = f b - f a"
sorry


subsection \<open>Fine-ness of a partition w.r.t. a gauge\<close>

definition\<^marker>\<open>tag important\<close> fine  (infixr \<open>fine\<close> 46)
  where "d fine s \<longleftrightarrow> (\<forall>(x,k) \<in> s. k \<subseteq> d x)"

lemma fineI:
  assumes "\<And>x k. (x, k) \<in> s \<Longrightarrow> k \<subseteq> d x"
  shows "d fine s"
sorry

lemma fineD[dest]:
  assumes "d fine s"
  shows "\<And>x k. (x,k) \<in> s \<Longrightarrow> k \<subseteq> d x"
sorry

lemma fine_Int: "(\<lambda>x. d1 x \<inter> d2 x) fine p \<longleftrightarrow> d1 fine p \<and> d2 fine p"
sorry

lemma fine_Inter:
 "(\<lambda>x. \<Inter>{f d x | d.  d \<in> s}) fine p \<longleftrightarrow> (\<forall>d\<in>s. (f d) fine p)"
sorry

lemma fine_Un: "d fine p1 \<Longrightarrow> d fine p2 \<Longrightarrow> d fine (p1 \<union> p2)"
sorry

lemma fine_Union: "(\<And>p. p \<in> ps \<Longrightarrow> d fine p) \<Longrightarrow> d fine (\<Union>ps)"
sorry

lemma fine_subset: "p \<subseteq> q \<Longrightarrow> d fine q \<Longrightarrow> d fine p"
sorry

subsection \<open>Some basic combining lemmas\<close>

lemma tagged_division_Union_exists:
  assumes "finite I"
    and "\<forall>i\<in>I. \<exists>p. p tagged_division_of i \<and> d fine p"
    and "\<forall>i1\<in>I. \<forall>i2\<in>I. i1 \<noteq> i2 \<longrightarrow> interior i1 \<inter> interior i2 = {}"
    and "\<Union>I = i"
   obtains p where "p tagged_division_of i" and "d fine p"
sorry

(* FIXME structure here, do not have one lemma in each subsection *)

subsection\<^marker>\<open>tag unimportant\<close> \<open>The set we're concerned with must be closed\<close>

lemma division_of_closed:
  fixes i :: "'n::euclidean_space set"
  shows "s division_of i \<Longrightarrow> closed i"
sorry

(* FIXME structure here, do not have one lemma in each subsection *)

subsection \<open>General bisection principle for intervals; might be useful elsewhere\<close>

(* FIXME  move? *)
lemma interval_bisection_step:
  fixes type :: "'a::euclidean_space"
  assumes emp: "P {}"
    and Un: "\<And>S T. \<lbrakk>P S; P T; interior(S) \<inter> interior(T) = {}\<rbrakk> \<Longrightarrow> P (S \<union> T)"
    and non: "\<not> P (cbox a (b::'a))"
  obtains c d where "\<not> P (cbox c d)"
    and "\<And>i. i \<in> Basis \<Longrightarrow> a\<bullet>i \<le> c\<bullet>i \<and> c\<bullet>i \<le> d\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i \<and> 2 * (d\<bullet>i - c\<bullet>i) \<le> b\<bullet>i - a\<bullet>i"
sorry

lemma interval_bisection:
  fixes type :: "'a::euclidean_space"
  assumes "P {}"
    and Un: "\<And>S T. \<lbrakk>P S; P T; interior(S) \<inter> interior(T) = {}\<rbrakk> \<Longrightarrow> P (S \<union> T)"
    and "\<not> P (cbox a (b::'a))"
  obtains x where "x \<in> cbox a b"
    and "\<forall>e>0. \<exists>c d. x \<in> cbox c d \<and> cbox c d \<subseteq> ball x e \<and> cbox c d \<subseteq> cbox a b \<and> \<not> P (cbox c d)"
sorry


subsection \<open>Cousin's lemma\<close>

lemma fine_division_exists: 
  fixes a b :: "'a::euclidean_space"
  assumes "gauge g"
  obtains p where "p tagged_division_of (cbox a b)" "g fine p"
sorry

lemma fine_division_exists_real:
  fixes a b :: real
  assumes "gauge g"
  obtains p where "p tagged_division_of {a .. b}" "g fine p"
sorry

subsection \<open>A technical lemma about "refinement" of division\<close>

lemma tagged_division_finer:
  fixes p :: "('a::euclidean_space \<times> ('a::euclidean_space set)) set"
  assumes ptag: "p tagged_division_of (cbox a b)"
    and "gauge d"
  obtains q where "q tagged_division_of (cbox a b)"
    and "d fine q"
    and "\<forall>(x,K) \<in> p. K \<subseteq> d(x) \<longrightarrow> (x,K) \<in> q"
sorry

subsubsection\<^marker>\<open>tag important\<close> \<open>Covering lemma\<close>

text\<open> Some technical lemmas used in the approximation results that follow. Proof of the covering
  lemma is an obvious multidimensional generalization of Lemma 3, p65 of Swartz's
  "Introduction to Gauge Integrals". \<close>

proposition covering_lemma:
  assumes "S \<subseteq> cbox a b" "box a b \<noteq> {}" "gauge g"
  obtains \<D> where
    "countable \<D>"  "\<Union>\<D> \<subseteq> cbox a b"
    "\<And>K. K \<in> \<D> \<Longrightarrow> interior K \<noteq> {} \<and> (\<exists>c d. K = cbox c d)"
    "pairwise (\<lambda>A B. interior A \<inter> interior B = {}) \<D>"
    "\<And>K. K \<in> \<D> \<Longrightarrow> \<exists>x \<in> S \<inter> K. K \<subseteq> g x"
    "\<And>u v. cbox u v \<in> \<D> \<Longrightarrow> \<exists>n. \<forall>i \<in> Basis. v \<bullet> i - u \<bullet> i = (b \<bullet> i - a \<bullet> i) / 2^n"
    "S \<subseteq> \<Union>\<D>"
sorry

subsection \<open>Division filter\<close>

text \<open>Divisions over all gauges towards finer divisions.\<close>

definition\<^marker>\<open>tag important\<close> division_filter :: "'a::euclidean_space set \<Rightarrow> ('a \<times> 'a set) set filter"
  where "division_filter s = (INF g\<in>{g. gauge g}. principal {p. p tagged_division_of s \<and> g fine p})"

proposition eventually_division_filter:
  "(\<forall>\<^sub>F p in division_filter s. P p) \<longleftrightarrow>
    (\<exists>g. gauge g \<and> (\<forall>p. p tagged_division_of s \<and> g fine p \<longrightarrow> P p))"
sorry

lemma division_filter_not_empty: "division_filter (cbox a b) \<noteq> bot"
sorry

lemma eventually_division_filter_tagged_division:
  "eventually (\<lambda>p. p tagged_division_of s) (division_filter s)"
sorry

end
