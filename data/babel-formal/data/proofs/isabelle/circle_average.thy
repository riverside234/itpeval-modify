theory circle_average
  imports Main
begin

locale circle_average_setup =
  fixes zero     :: "'r"
    and add      :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"     (infixl "+C" 65)
    and integral :: "('r \<Rightarrow> 'r) \<Rightarrow> 'r"
  assumes add_zero      : "\<And>x. x +C zero = x"
    and   add_comm      : "\<And>x y. x +C y = y +C x"
    and   add_assoc     : "\<And>x y z. (x +C y) +C z = x +C (y +C z)"
    and   integral_ext  : "\<And>g h. (\<forall>\<theta>. g \<theta> = h \<theta>) \<Longrightarrow> integral g = integral h"
    and   integral_const: "\<And>c. integral (\<lambda>_. c) = c"
    and   integral_add  : "\<And>f g. integral (\<lambda>\<theta>. f \<theta> +C g \<theta>) = integral f +C integral g"
    and   integral_shift: "\<And>f c. integral (\<lambda>\<theta>. f (\<theta> +C c)) = integral f"
begin





definition circleMap :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
  where "circleMap c \<theta> \<equiv> \<theta> +C c"

definition circleAverage :: "('r \<Rightarrow> 'r) \<Rightarrow> 'r \<Rightarrow> 'r"
  where "circleAverage f c \<equiv> integral (\<lambda>\<theta>. f (circleMap c \<theta>))"





lemma circleMap_zero: "circleMap zero \<theta> = \<theta>"
  unfolding circleMap_def by (rule add_zero)

lemma circleAverage_zero: "circleAverage f zero = integral f"
  unfolding circleAverage_def
  by (rule integral_ext) (simp add: circleMap_def add_zero)

lemma circleAverage_add:
  "circleAverage (\<lambda>z. f z +C g z) c =
   circleAverage f c +C circleAverage g c"
  unfolding circleAverage_def
  by (simp add: integral_add)

lemma circleAverage_fun_add:
  "circleAverage (\<lambda>z. f (z +C c)) zero = circleAverage f c"
  unfolding circleAverage_def circleMap_def
  by (rule integral_ext) (simp add: add_zero)

lemma circleMap_add:
  "circleMap (c +C d) \<theta> = circleMap c (circleMap d \<theta>)"
  unfolding circleMap_def
  by (simp only: add_comm[of c d] add_assoc[symmetric])

lemma circleAverage_shift:
  "circleAverage f (c +C d) = circleAverage (\<lambda>z. f (z +C d)) c"
  unfolding circleAverage_def circleMap_def
  by (rule integral_ext) (simp add: add_assoc)

lemma circleAverage_const:
  "circleAverage (\<lambda>_. k) c = k"
  unfolding circleAverage_def
  by (simp add: integral_const)

lemma circleAverage_add_const:
  "circleAverage (\<lambda>z. f z +C k) c = circleAverage f c +C k"
  unfolding circleAverage_def
  by (simp add: integral_add integral_const)

lemma circleAverage_comm_add:
  "circleAverage (\<lambda>z. f z +C g z) c =
   circleAverage (\<lambda>z. g z +C f z) c"
  unfolding circleAverage_def
  by (rule integral_ext) (simp add: add_comm)

lemma circleAverage_add_assoc:
  "circleAverage (\<lambda>z. (f z +C g z) +C h z) c =
   circleAverage f c +C (circleAverage g c +C circleAverage h c)"
  unfolding circleAverage_def
  by (simp add: integral_add add_assoc)

lemma circleAverage_center_comm:
  "circleAverage f (c +C d) = circleAverage f (d +C c)"
  unfolding circleAverage_def circleMap_def
  by (simp only: add_comm[of c d])

lemma circleAverage_center_independent:
  "circleAverage f c = integral f"
  unfolding circleAverage_def circleMap_def
  by (rule integral_shift)

lemma circleAverage_center_eq:
  "circleAverage f c = circleAverage f d"
  by (simp add: circleAverage_center_independent)

lemma circleAverage_idempotent:
  "circleAverage (\<lambda>z. circleAverage f z) c = circleAverage f c"
  by (simp add: circleAverage_center_independent integral_const)

lemma circleAverage_of_zero_integral:
  "integral f = zero \<Longrightarrow> circleAverage f c = zero"
  by (simp add: circleAverage_center_independent)

lemma circleAverage_linear:
  "circleAverage (\<lambda>z. f z +C g z) c =
   circleAverage f c +C circleAverage g c"
  by (rule circleAverage_add)

lemma circleAverage_shift_commute:
  "circleAverage (\<lambda>z. f (circleMap d z)) c =
   circleAverage f (c +C d)"
  unfolding circleAverage_def circleMap_def
  by (rule integral_ext) (simp add: add_assoc)

end

end
