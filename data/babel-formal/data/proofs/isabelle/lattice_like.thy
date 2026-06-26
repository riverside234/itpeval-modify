theory lattice_like
  imports Main
begin

locale lattice_like =
  fixes le  :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<preceq>" 50)
    and inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<sqinter>" 60)
    and sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<squnion>" 65)
  assumes le_refl   : "\<And>x. x \<preceq> x"
    and   le_trans  : "\<And>x y z. x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
    and   le_antisym: "\<And>x y. x \<preceq> y \<Longrightarrow> y \<preceq> x \<Longrightarrow> x = y"
    and   le_inf_left  : "\<And>a b. inf a b \<preceq> a"
    and   le_inf_right : "\<And>a b. inf a b \<preceq> b"
    and   le_inf_intro : "\<And>c a b. c \<preceq> a \<Longrightarrow> c \<preceq> b \<Longrightarrow> c \<preceq> inf a b"
    and   le_sup_left  : "\<And>a b. a \<preceq> sup a b"
    and   le_sup_right : "\<And>a b. b \<preceq> sup a b"
    and   sup_le_intro : "\<And>a b c. a \<preceq> c \<Longrightarrow> b \<preceq> c \<Longrightarrow> sup a b \<preceq> c"
begin

lemma inf_comm: "a \<sqinter> b = b \<sqinter> a"
  by (rule le_antisym)
     (auto intro: le_inf_intro le_inf_left le_inf_right)

lemma sup_comm: "a \<squnion> b = b \<squnion> a"
  by (rule le_antisym)
     (auto intro: sup_le_intro le_sup_left le_sup_right)

lemma inf_assoc: "(a \<sqinter> b) \<sqinter> c = a \<sqinter> (b \<sqinter> c)"
proof (rule le_antisym)
  show "(a \<sqinter> b) \<sqinter> c \<preceq> a \<sqinter> (b \<sqinter> c)"
    by (intro le_inf_intro)
       (blast intro: le_trans le_inf_left le_inf_right)+
  show "a \<sqinter> (b \<sqinter> c) \<preceq> (a \<sqinter> b) \<sqinter> c"
    by (intro le_inf_intro)
       (blast intro: le_trans le_inf_left le_inf_right)+
qed

lemma sup_assoc: "(a \<squnion> b) \<squnion> c = a \<squnion> (b \<squnion> c)"
proof (rule le_antisym)
  show "(a \<squnion> b) \<squnion> c \<preceq> a \<squnion> (b \<squnion> c)"
    by (intro sup_le_intro)
       (blast intro: le_trans le_sup_left le_sup_right)+
  show "a \<squnion> (b \<squnion> c) \<preceq> (a \<squnion> b) \<squnion> c"
    by (intro sup_le_intro)
       (blast intro: le_trans le_sup_left le_sup_right)+
qed

lemma inf_absorption: "a \<sqinter> (a \<squnion> b) = a"
  by (rule le_antisym)
     (auto intro: le_inf_intro le_inf_left le_refl le_sup_left)

lemma sup_absorption: "a \<squnion> (a \<sqinter> b) = a"
  by (rule le_antisym)
     (auto intro: sup_le_intro le_sup_left le_refl le_inf_left)

end

end
