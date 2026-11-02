theory V2Control imports Main begin
declare [[quick_and_dirty = true]]


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  
proof -
 define t where "t = True"
 have ht: t unfolding t_def by simp
 show True using ht by simp
qed