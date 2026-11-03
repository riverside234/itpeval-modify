(*  Title:      HOL/Analysis/Jordan_Curve.thy
    Authors:    LC Paulson, based on material from HOL Light
*)

section \<open>The Jordan Curve Theorem and Applications\<close>

theory Jordan_Curve
  imports Arcwise_Connected Further_Topology
begin

subsection\<open>Janiszewski's theorem\<close>

lemma Janiszewski_weak:
  fixes a b::complex
  assumes "compact S" "compact T" and conST: "connected(S \<inter> T)"
      and ccS: "connected_component (- S) a b" and ccT: "connected_component (- T) a b"
    shows "connected_component (- (S \<union> T)) a b"
sorry

theorem Janiszewski:
  fixes a b :: complex
  assumes "compact S" "closed T" and conST: "connected (S \<inter> T)"
      and ccS: "connected_component (- S) a b" and ccT: "connected_component (- T) a b"
    shows "connected_component (- (S \<union> T)) a b"
sorry

lemma Janiszewski_connected:
  fixes S :: "complex set"
  assumes ST: "compact S" "closed T" "connected(S \<inter> T)"
    and notST: "connected (- S)" "connected (- T)"
  shows "connected(- (S \<union> T))"
sorry

subsection\<open>The Jordan Curve theorem\<close>

lemma exists_double_arc:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes "simple_path g" "pathfinish g = pathstart g" "a \<in> path_image g" "b \<in> path_image g" "a \<noteq> b"
  obtains u d where "arc u" "arc d" "pathstart u = a" "pathfinish u = b"
                    "pathstart d = b" "pathfinish d = a"
                    "(path_image u) \<inter> (path_image d) = {a,b}"
                    "(path_image u) \<union> (path_image d) = path_image g"
sorry

theorem\<^marker>\<open>tag unimportant\<close> Jordan_curve:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c" and loop: "pathfinish c = pathstart c"
  obtains inner outer where
                "inner \<noteq> {}" "open inner" "connected inner"
                "outer \<noteq> {}" "open outer" "connected outer"
                "bounded inner" "\<not> bounded outer" "inner \<inter> outer = {}"
                "inner \<union> outer = - path_image c"
                "frontier inner = path_image c"
                "frontier outer = path_image c"
sorry

corollary\<^marker>\<open>tag unimportant\<close> Jordan_disconnected:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c" "pathfinish c = pathstart c"
  shows "\<not> connected(- path_image c)"
sorry

corollary Jordan_inside_outside:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c" "pathfinish c = pathstart c"
    shows "inside(path_image c) \<noteq> {} \<and>
          open(inside(path_image c)) \<and>
          connected(inside(path_image c)) \<and>
          outside(path_image c) \<noteq> {} \<and>
          open(outside(path_image c)) \<and>
          connected(outside(path_image c)) \<and>
          bounded(inside(path_image c)) \<and>
          \<not> bounded(outside(path_image c)) \<and>
          inside(path_image c) \<inter> outside(path_image c) = {} \<and>
          inside(path_image c) \<union> outside(path_image c) =
          - path_image c \<and>
          frontier(inside(path_image c)) = path_image c \<and>
          frontier(outside(path_image c)) = path_image c"
sorry

subsubsection\<open>Triple-curve or "theta-curve" theorem\<close>

text\<open>Proof that there is no fourth component taken from
     Kuratowski's Topology vol 2, para 61, II.\<close>

theorem split_inside_simple_closed_curve:
  fixes c :: "real \<Rightarrow> complex"
  assumes "simple_path c1" and c1: "pathstart c1 = a" "pathfinish c1 = b"
      and "simple_path c2" and c2: "pathstart c2 = a" "pathfinish c2 = b"
      and "simple_path c"  and c: "pathstart c = a" "pathfinish c = b"
      and "a \<noteq> b"
      and c1c2: "path_image c1 \<inter> path_image c2 = {a,b}"
      and c1c: "path_image c1 \<inter> path_image c = {a,b}"
      and c2c: "path_image c2 \<inter> path_image c = {a,b}"
      and ne_12: "path_image c \<inter> inside(path_image c1 \<union> path_image c2) \<noteq> {}"
  obtains "inside(path_image c1 \<union> path_image c) \<inter> inside(path_image c2 \<union> path_image c) = {}"
          "inside(path_image c1 \<union> path_image c) \<union> inside(path_image c2 \<union> path_image c) \<union>
           (path_image c - {a,b}) = inside(path_image c1 \<union> path_image c2)"
sorry

end
