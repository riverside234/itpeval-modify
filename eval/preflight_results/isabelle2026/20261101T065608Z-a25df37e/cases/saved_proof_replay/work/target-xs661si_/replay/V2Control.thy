theory V2Control imports Main begin
declare [[quick_and_dirty = true]]

declare [[smt_oracle = true]]

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  by simp
end
