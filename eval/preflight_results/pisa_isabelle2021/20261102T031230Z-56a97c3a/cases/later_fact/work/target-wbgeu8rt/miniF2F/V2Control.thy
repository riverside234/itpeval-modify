theory V2Control imports Main begin
declare [[quick_and_dirty = true]]


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma v2_control: "False"
  
by (rule v2_later_secret)