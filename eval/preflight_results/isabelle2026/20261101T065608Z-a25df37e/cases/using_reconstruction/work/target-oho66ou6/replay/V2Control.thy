theory V2Control imports Main begin
declare [[quick_and_dirty = true]]


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  proof -
 have h: "True" by simp
 show "True"
 using h by metis

qed
end
