theory V2Control imports Main begin
declare [[quick_and_dirty = true]]


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  proof -
 have both: "True \<and> True"
 apply (rule conjI)
 apply simp
by simp

 from both show "True" by simp
qed
end
