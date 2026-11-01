theory V2Control imports Main begin
declare [[quick_and_dirty = true]]


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  proof -
 have first: True
 by auto

 have both: \<open>True \<and> True\<close>
 proof
  show True using first
  by auto

  show True using first
  by auto

 qed
 show True using both
 by auto

qed
end
