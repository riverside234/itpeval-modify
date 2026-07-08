theory comp_commute
  imports Main
begin

definition myComp :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "myComp g f \<equiv> \<lambda>x. g (f x)"

definition myId :: "'a \<Rightarrow> 'a"
  where "myId \<equiv> \<lambda>x. x"



lemma comp_assoc:
  "myComp h (myComp g f) = myComp (myComp h g) f"
  unfolding myComp_def by simp

lemma comp_id_l:
  "myComp myId f = f"
  unfolding myComp_def myId_def by simp

lemma comp_id_r:
  "myComp f myId = f"
  unfolding myComp_def myId_def by simp



definition commute :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "commute f g \<equiv> myComp f g = myComp g f"

lemma commute_symm:
  "commute f g \<Longrightarrow> commute g f"
  unfolding commute_def by simp

lemma commute_with_id_l:
  "commute f myId"
  unfolding commute_def
  by (simp add: comp_id_r comp_id_l)

lemma commute_with_id_r:
  "commute myId f"
  unfolding commute_def
  by (simp add: comp_id_l comp_id_r)

lemma commute_refl:
  "commute f f"
  unfolding commute_def by simp

lemma commute_congr:
  "f1 = f2 \<Longrightarrow> g1 = g2 \<Longrightarrow> commute f1 g1 \<Longrightarrow> commute f2 g2"
  by simp

lemma commute_transport_left_id:
  "commute f g \<Longrightarrow> commute (myComp myId f) g"
  unfolding commute_def
  by (simp add: comp_id_l)

lemma commute_transport_right_id:
  "commute f g \<Longrightarrow> commute f (myComp myId g)"
  unfolding commute_def
  by (simp add: comp_id_l)

end
