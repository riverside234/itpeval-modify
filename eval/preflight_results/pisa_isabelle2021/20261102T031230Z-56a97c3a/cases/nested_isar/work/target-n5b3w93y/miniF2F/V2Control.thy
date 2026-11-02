theory V2Control imports Main begin
declare [[quick_and_dirty = true]]


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  
proof -
 have both: "True \<and> True"
 proof
  show True by simp
  show True by simp
 qed
 show True using both by simp
qed