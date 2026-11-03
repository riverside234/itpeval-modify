(*  Title:      HOL/Algebra/Exact_Sequence.thy
    Author:     Martin Baillon (first part) and LC Paulson (material ported from HOL Light)
*)

section \<open>Exact Sequences\<close>

theory Exact_Sequence
  imports Elementary_Groups Solvable_Groups
begin



subsection \<open>Definitions\<close>

inductive exact_seq :: "'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow> bool"  where
unity:     " group_hom G1 G2 f \<Longrightarrow> exact_seq ([G2, G1], [f])" |
extension: "\<lbrakk> exact_seq ((G # K # l), (g # q)); group H ; h \<in> hom G H ;
              kernel G H h = image g (carrier K) \<rbrakk> \<Longrightarrow> exact_seq (H # G # K # l, h # g # q)"

inductive_simps exact_seq_end_iff [simp]: "exact_seq ([G,H], (g # q))"
inductive_simps exact_seq_cons_iff [simp]: "exact_seq ((G # K # H # l), (g # h # q))"

abbreviation exact_seq_arrow ::
  "('a \<Rightarrow> 'a) \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow>  'a monoid \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list"
  (\<open>(\<open>indent=3 notation=\<open>mixfix exact_seq\<close>\<close>_ / \<longlongrightarrow>\<index> _)\<close> [1000, 60])
  where "exact_seq_arrow  f t G \<equiv> (G # (fst t), f # (snd t))"


subsection \<open>Basic Properties\<close>

lemma exact_seq_length1: "exact_seq t \<Longrightarrow> length (fst t) = Suc (length (snd t))"
sorry

lemma exact_seq_length2: "exact_seq t \<Longrightarrow> length (snd t) \<ge> Suc 0"
sorry

lemma dropped_seq_is_exact_seq:
  assumes "exact_seq (G, F)" and "(i :: nat) < length F"
  shows "exact_seq (drop i G, drop i F)"
sorry

lemma truncated_seq_is_exact_seq:
  assumes "exact_seq (l, q)" and "length l \<ge> 3"
  shows "exact_seq (tl l, tl q)"
sorry

lemma exact_seq_imp_exact_hom:
   assumes "exact_seq (G1 # l,q) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
   shows "g1 ` (carrier G1) = kernel G2 G3 g2"
sorry

lemma exact_seq_imp_exact_hom_arbitrary:
   assumes "exact_seq (G, F)"
     and "Suc i < length F"
   shows "(F ! (Suc i)) ` (carrier (G ! (Suc (Suc i)))) = kernel (G ! (Suc i)) (G ! i) (F ! i)"
sorry

lemma exact_seq_imp_group_hom :
  assumes "exact_seq ((G # l, q)) \<longlongrightarrow>\<^bsub>g\<^esub> H"
  shows "group_hom G H g"
sorry

lemma exact_seq_imp_group_hom_arbitrary:
  assumes "exact_seq (G, F)" and "(i :: nat) < length F"
  shows "group_hom (G ! (Suc i)) (G ! i) (F ! i)"
sorry


subsection \<open>Link Between Exact Sequences and Solvable Conditions\<close>

lemma exact_seq_solvable_imp :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "solvable G2 \<Longrightarrow> (solvable G1) \<and> (solvable G3)"
sorry

lemma exact_seq_solvable_recip :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<Longrightarrow> solvable G2"
sorry

proposition exact_seq_solvable_iff :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<longleftrightarrow>  solvable G2"
sorry

lemma exact_seq_eq_triviality:
  assumes "exact_seq ([E,D,C,B,A], [k,h,g,f])"
  shows "trivial_group C \<longleftrightarrow> f ` carrier A = carrier B \<and> inj_on k (carrier D)" (is "_ = ?rhs")
sorry

lemma exact_seq_imp_triviality:
   "\<lbrakk>exact_seq ([E,D,C,B,A], [k,h,g,f]); f \<in> iso A B; k \<in> iso D E\<rbrakk> \<Longrightarrow> trivial_group C"
sorry

lemma exact_seq_epi_eq_triviality:
   "exact_seq ([D,C,B,A], [h,g,f]) \<Longrightarrow> (f ` carrier A = carrier B) \<longleftrightarrow> trivial_homomorphism B C g"
sorry

lemma exact_seq_mon_eq_triviality:
   "exact_seq ([D,C,B,A], [h,g,f]) \<Longrightarrow> inj_on h (carrier C) \<longleftrightarrow> trivial_homomorphism B C g"
sorry

lemma exact_sequence_sum_lemma:
  assumes "comm_group G" and h: "h \<in> iso A C" and k: "k \<in> iso B D"
    and ex: "exact_seq ([D,G,A], [g,i])" "exact_seq ([C,G,B], [f,j])"
    and fih: "\<And>x. x \<in> carrier A \<Longrightarrow> f(i x) = h x"
    and gjk: "\<And>x. x \<in> carrier B \<Longrightarrow> g(j x) = k x"
  shows "(\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) \<in> Group.iso (A \<times>\<times> B) G \<and> (\<lambda>z. (f z, g z)) \<in> Group.iso G (C \<times>\<times> D)"
    (is "?ij \<in> _ \<and> ?gf \<in> _")
sorry

subsection \<open>Splitting lemmas and Short exact sequences\<close>
text\<open>Ported from HOL Light by LCP\<close>

definition short_exact_sequence
  where "short_exact_sequence A B C f g \<equiv> \<exists>T1 T2 e1 e2. exact_seq ([T1,A,B,C,T2], [e1,f,g,e2]) \<and> trivial_group T1 \<and> trivial_group T2"

lemma short_exact_sequenceD:
  assumes "short_exact_sequence A B C f g" shows "exact_seq ([A,B,C], [f,g]) \<and> f \<in> epi B A \<and> g \<in> mon C B"
sorry

lemma short_exact_sequence_iff:
  "short_exact_sequence A B C f g \<longleftrightarrow> exact_seq ([A,B,C], [f,g]) \<and> f \<in> epi B A \<and> g \<in> mon C B"
sorry

lemma very_short_exact_sequence:
  assumes "exact_seq ([D,C,B,A], [h,g,f])" "trivial_group A" "trivial_group D"
  shows "g \<in> iso B C"
sorry

lemma splitting_sublemma_gen:
  assumes ex: "exact_seq ([C,B,A], [g,f])" and fim: "f ` carrier A = H"
      and "subgroup K B" and 1: "H \<inter> K \<subseteq> {one B}" and eq: "set_mult B H K = carrier B"
  shows "g \<in> iso (subgroup_generated B K) (subgroup_generated C(g ` carrier B))"
sorry

lemma splitting_sublemma:
  assumes ex: "short_exact_sequence C B A g f" and fim: "f ` carrier A = H"
      and "subgroup K B" and 1: "H \<inter> K \<subseteq> {one B}" and eq: "set_mult B H K = carrier B"
    shows "f \<in> iso A (subgroup_generated B H)" (is ?f)
          "g \<in> iso (subgroup_generated B K) C" (is ?g)
sorry

lemma splitting_lemma_left_gen:
  assumes ex: "exact_seq ([C,B,A], [g,f])" and f': "f' \<in> hom B A" and iso: "(f' \<circ> f) \<in> iso A A"
    and injf: "inj_on f (carrier A)" and surj: "g ` carrier B = carrier C"
 obtains H K where "H \<lhd> B" "K \<lhd> B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
sorry

lemma splitting_lemma_left:
  assumes ex: "exact_seq ([C,B,A], [g,f])" and f': "f' \<in> hom B A"
    and inv: "(\<And>x. x \<in> carrier A \<Longrightarrow> f'(f x) = x)"
    and injf: "inj_on f (carrier A)" and surj: "g ` carrier B = carrier C"
 obtains H K where "H \<lhd> B" "K \<lhd> B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
sorry

lemma splitting_lemma_right_gen:
  assumes ex: "short_exact_sequence C B A g f" and g': "g' \<in> hom C B" and iso: "(g \<circ> g') \<in> iso C C"
 obtains H K where "H \<lhd> B" "subgroup K B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
sorry

lemma splitting_lemma_right:
  assumes ex: "short_exact_sequence C B A g f" and g': "g' \<in> hom C B" and gg': "\<And>z. z \<in> carrier C \<Longrightarrow> g(g' z) = z"
 obtains H K where "H \<lhd> B" "subgroup K B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
sorry


end
