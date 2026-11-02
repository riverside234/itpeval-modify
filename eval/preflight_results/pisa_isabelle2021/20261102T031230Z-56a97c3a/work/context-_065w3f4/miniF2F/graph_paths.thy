theory graph_paths
  imports Main
begin
declare [[quick_and_dirty = true]]


inductive Path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  Pnil:  "Path E v v"
| Pstep: "Path E u v \<Longrightarrow> E v w \<Longrightarrow> Path E u w"

definition undirected :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "undirected E \<equiv> \<forall>x y. E x y \<longrightarrow> E y x"

definition Erev :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Erev E x y \<equiv> E y x"


declare [[quick_and_dirty = false, smt_oracle = false]]
lemma path_refl: "Path E v v"
  