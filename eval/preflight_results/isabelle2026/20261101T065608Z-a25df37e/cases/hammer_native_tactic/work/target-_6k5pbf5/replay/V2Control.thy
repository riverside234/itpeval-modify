theory V2Control imports Main begin
declare [[quick_and_dirty = true]]

sledgehammer_params [falsify = true, abduce = 1]

declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "True"
  proof -
 show "True"
 by simp

qed
end
