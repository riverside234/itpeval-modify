theory graph_paths
  imports Main
begin

inductive Path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  Pnil:  "Path E v v"
| Pstep: "Path E u v \<Longrightarrow> E v w \<Longrightarrow> Path E u w"

definition undirected :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "undirected E \<equiv> \<forall>x y. E x y \<longrightarrow> E y x"

definition Erev :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Erev E x y \<equiv> E y x"

lemma path_refl: "Path E v v"
  by (rule Pnil)

lemma path_trans:
  assumes "Path E u v" "Path E v w" shows "Path E u w"
  using assms(2) assms(1)
proof (induction arbitrary: u)
  case Pnil then show ?case .
next
  case Pstep then show ?case by (blast intro: Path.Pstep)
qed

lemma trans: "Path E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E u w"
  by (rule path_trans)


lemma edge_path: "E u v \<Longrightarrow> Path E u v"
  apply (rule Pstep)
  apply (rule Pnil)
  apply assumption
  done

lemma concat_edge_right: "Path E u v \<Longrightarrow> E v w \<Longrightarrow> Path E u w"
  by (rule Pstep)

lemma concat: "Path E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E u w"
  by (rule path_trans)

lemma concat_edge_left: "E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E u w"
  by (rule path_trans[OF edge_path])

lemma concat3:
  "Path E u v \<Longrightarrow> Path E v w \<Longrightarrow> Path E w t \<Longrightarrow> Path E u t"
  by (rule path_trans[OF path_trans])


lemma reverse_cons:
  assumes hE: "undirected E" and e: "E m v" and ih: "Path E m u"
  shows "Path E v u"
proof -
  have evm: "E v m" using hE e unfolding undirected_def by blast
  have pvm: "Path E v m"
    apply (rule Pstep)
    apply (rule Pnil)
    apply (rule evm)
    done
  show ?thesis by (rule path_trans[OF pvm ih])
qed

lemma reverse_path:
  assumes hE: "undirected E" and p: "Path E u v"
  shows "Path E v u"
  using p
proof (induction rule: Path.induct)
  case Pnil show ?case by (rule Pnil)
next
  case Pstep

  then show ?case using hE by (blast intro: reverse_cons)
qed


lemma reverse_cons_Erev:
  assumes e: "E m v" and ih: "Path (Erev E) m u"
  shows "Path (Erev E) v u"
proof -
  have evm: "Erev E v m" unfolding Erev_def using e by simp
  have pvm: "Path (Erev E) v m"
    apply (rule Pstep)
    apply (rule Pnil)
    apply (rule evm)
    done
  show ?thesis by (rule path_trans[OF pvm ih])
qed

lemma reverse_in_Erev:
  assumes p: "Path E u v"
  shows "Path (Erev E) v u"
  using p
proof (induction rule: Path.induct)
  case Pnil show ?case by (rule Pnil)
next
  case Pstep

  then show ?case by (blast intro: reverse_cons_Erev)
qed

lemma cycle_refl:
  "Path E v w \<Longrightarrow> Path E w v \<Longrightarrow> Path E v v"
  by (rule path_trans)

end
