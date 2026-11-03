(* Author: Fabian Immler, TUM *)

section \<open>Sequence of Properties on Subsequences\<close>

theory Diagonal_Subsequence
imports Complex_Main
begin

locale subseqs =
  fixes P::"nat\<Rightarrow>(nat\<Rightarrow>nat)\<Rightarrow>bool"
  assumes ex_subseq: "\<And>n s. strict_mono (s::nat\<Rightarrow>nat) \<Longrightarrow> \<exists>r'. strict_mono r' \<and> P n (s \<circ> r')"
begin

definition reduce where "reduce s n = (SOME r'::nat\<Rightarrow>nat. strict_mono r' \<and> P n (s \<circ> r'))"

lemma subseq_reduce[intro, simp]:
  "strict_mono s \<Longrightarrow> strict_mono (reduce s n)"
  by sorry

lemma reduce_holds:
  "strict_mono s \<Longrightarrow> P n (s \<circ> reduce s n)"
  by sorry

primrec seqseq :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "seqseq 0 = id"
| "seqseq (Suc n) = seqseq n \<circ> reduce (seqseq n) n"

lemma subseq_seqseq[intro, simp]: "strict_mono (seqseq n)"
  by sorry

lemma seqseq_holds:
  "P n (seqseq (Suc n))"
  by sorry

definition diagseq :: "nat \<Rightarrow> nat" where "diagseq i = seqseq i i"

lemma diagseq_mono: "diagseq n < diagseq (Suc n)"
  by sorry

lemma subseq_diagseq: "strict_mono diagseq"
  by sorry

primrec fold_reduce where
  "fold_reduce n 0 = id"
| "fold_reduce n (Suc k) = fold_reduce n k \<circ> reduce (seqseq (n + k)) (n + k)"

lemma subseq_fold_reduce[intro, simp]: "strict_mono (fold_reduce n k)"
  by sorry

lemma ex_subseq_reduce_index: "seqseq (n + k) = seqseq n \<circ> fold_reduce n k"
  by sorry

lemma seqseq_fold_reduce: "seqseq n = fold_reduce 0 n"
  by sorry

lemma diagseq_fold_reduce: "diagseq n = fold_reduce 0 n n"
  by sorry

lemma fold_reduce_add: "fold_reduce 0 (m + n) = fold_reduce 0 m \<circ> fold_reduce m n"
  by sorry

lemma diagseq_add: "diagseq (k + n) = (seqseq k \<circ> (fold_reduce k n)) (k + n)"
  by sorry

lemma diagseq_sub:
  assumes "m \<le> n" shows "diagseq n = (seqseq m \<circ> (fold_reduce m (n - m))) n"
  by sorry

lemma subseq_diagonal_rest: "strict_mono (\<lambda>x. fold_reduce k x (k + x))"
  by sorry

lemma diagseq_seqseq: "diagseq \<circ> ((+) k) = (seqseq k \<circ> (\<lambda>x. fold_reduce k x (k + x)))"
  by sorry

lemma diagseq_holds:
  assumes subseq_stable: "\<And>r s n. strict_mono r \<Longrightarrow> P n s \<Longrightarrow> P n (s \<circ> r)"
  shows "P k (diagseq \<circ> ((+) (Suc k)))"
  by sorry

end

end
