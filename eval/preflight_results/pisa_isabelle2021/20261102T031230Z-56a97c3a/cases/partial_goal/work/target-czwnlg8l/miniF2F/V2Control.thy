theory V2Control imports Main begin
declare [[quick_and_dirty = true]]


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  
proof -
 have impossible: "True \<and> False"
 apply (rule conjI)
 sledgehammer
 then show True by simp
qed