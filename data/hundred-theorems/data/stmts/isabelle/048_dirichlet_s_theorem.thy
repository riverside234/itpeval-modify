(*
    File:      Dirichlet_Series.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Formal Dirichlet series\<close>
theory Dirichlet_Series
imports 
  Complex_Main
  Dirichlet_Product
  Multiplicative_Function
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Number_Theory.Number_Theory"
  "HOL-Library.FuncSet"
begin

text \<open>
  A formal Dirichlet series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  is represented its coefficient sequence starting from 1. For simplicity, we represent this
  in Isabelle with a function of type @{typ "nat \<Rightarrow> 'a"} whose value for $n$ is the $n+1$-th 
  coefficient.
\<close>  
typedef 'a fds = "UNIV :: (nat \<Rightarrow> 'a) set"
  by simp

setup_lifting type_definition_fds

lift_definition fds_nth :: "'a fds \<Rightarrow> nat \<Rightarrow> 'a :: zero" is
  "\<lambda>f::nat \<Rightarrow> 'a. case_nat 0 f" .
    
lift_definition fds :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a fds" is
  "\<lambda>f. f \<circ> Suc" .
    
lemma fds_nth_fds: "fds_nth (fds f) n = (if n = 0 then 0 else f n)"
  by sorry
    
lemma fds_nth_fds': "f 0 = 0 \<Longrightarrow> fds_nth (fds f) = f"
  by sorry
    
lemma fds_nth_0 [simp]: "fds_nth f 0 = 0"
  by sorry
    
lemma fds_nth_fds_pos [simp]: "n > 0 \<Longrightarrow> fds_nth (fds f) n = f n"
  by sorry
    
lemma fds_fds_nth [simp]: "fds (fds_nth f) = f"
  by sorry
    
lemma fds_eq_fds_iff:
  "fds f = fds g \<longleftrightarrow> (\<forall>n>0. f n = g n)"
  by sorry

lemma fds_eq_fds_iff': "f 0 = g 0 \<Longrightarrow> fds f = fds g \<longleftrightarrow> f = g"
  by sorry

lemma fds_eqI [intro?]:
  assumes "(\<And>n. n > 0 \<Longrightarrow> fds_nth f n = fds_nth g n)"
  shows   "f = g"
  by sorry
  
lemma fds_cong [cong]: "(\<And>n. n > 0 \<Longrightarrow> f n = (g n :: 'a :: zero)) \<Longrightarrow> fds f = fds g"
  by sorry

lemma fds_eq_iff: "f = g \<longleftrightarrow> (\<forall>n>0. fds_nth f n = fds_nth g n)"
  by sorry

lemma dirichlet_prod_fds_nth_fds_left [simp]:
  "dirichlet_prod (fds_nth (fds f)) g = dirichlet_prod f g"
  by sorry
  
lemma dirichlet_prod_fds_nth_fds_right [simp]:
  "dirichlet_prod f (fds_nth (fds g)) = dirichlet_prod f g"
  by sorry


definition fds_const :: "'a :: zero \<Rightarrow> 'a fds" where
  "fds_const c = fds (\<lambda>n. if n = 1 then c else 0)"
  
abbreviation fds_ind where "fds_ind P \<equiv> fds (ind P)"


bundle fds_syntax
begin
  
notation fds_nth (infixl \<open>$\<close> 75)
notation fds (binder \<open>\<chi>\<close> 10)
notation dirichlet_prod (infixl \<open>\<star>\<close> 70)
 
end

instantiation fds :: (zero) zero
begin
definition zero_fds :: "'a fds" where "zero_fds = fds (\<lambda>_. 0)"
instance ..
end

instantiation fds :: ("{zero,one}") one
begin
definition one_fds :: "'a fds" where "one_fds = fds (\<lambda>n. if n = 1 then 1 else 0)"
instance ..
end

instantiation fds :: ("{plus,zero}") plus
begin
definition plus_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds" 
  where "plus_fds f g = fds (\<lambda>n. fds_nth f n + fds_nth g n)"
instance ..
end

instantiation fds :: (semiring_0) times
begin
definition times_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds" 
  where "times_fds f g = fds (dirichlet_prod (fds_nth f) (fds_nth g))"
instance ..
end
  
instantiation fds :: ("{uminus,zero}") uminus
begin
definition uminus_fds :: "'a fds \<Rightarrow> 'a fds"
  where "uminus_fds f = fds (\<lambda>n. -fds_nth f n)"
instance ..
end
  
instantiation fds :: ("{minus,zero}") minus
begin
definition minus_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds"
  where "minus_fds f g = fds (\<lambda>n. fds_nth f n - fds_nth g n)"
instance ..
end


subsection \<open>General properties\<close>
  
lemma fds_nth_zero [simp]: "fds_nth 0 = (\<lambda>_. 0)"
  by sorry

lemma fds_nth_one: "fds_nth 1 = (\<lambda>n. if n = 1 then 1 else 0)"
  by sorry

lemma fds_nth_one_Suc_0 [simp]: "fds_nth 1 (Suc 0) = 1"
  by sorry
    
lemma fds_nth_one_not_Suc_0 [simp]: "n \<noteq> Suc 0 \<Longrightarrow> fds_nth 1 n = 0"
  by sorry
    
lemma fds_nth_plus [simp]: 
  "fds_nth (f + g) = (\<lambda>n. fds_nth f n + fds_nth g n :: 'a :: monoid_add)"
  by sorry

lemma fds_nth_minus [simp]: 
  "fds_nth (f - g) = (\<lambda>n. fds_nth f n - fds_nth g n :: 'a :: {cancel_comm_monoid_add})"
  by sorry

lemma fds_nth_uminus [simp]: "fds_nth (-g) = (\<lambda>n. - fds_nth g n :: 'a :: group_add)"
  by sorry

lemma fds_nth_mult: "fds_nth (f * g) = dirichlet_prod (fds_nth f) (fds_nth g)"
  by sorry

lemma fds_nth_mult_const_left [simp]: "fds_nth (fds_const c * f) n = c * fds_nth f n"
  by sorry

lemma fds_nth_mult_const_right [simp]: "fds_nth (f * fds_const c) n = fds_nth f n * c"
  by sorry


instance fds :: ("{semigroup_add, zero}") semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def)

instance fds :: ("{ab_semigroup_add, zero}") ab_semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def)

instance fds :: ("{cancel_semigroup_add, zero}") cancel_semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def)
    
instance fds :: ("{cancel_ab_semigroup_add, zero}") cancel_ab_semigroup_add
  by standard (simp_all add: fds_eq_iff algebra_simps plus_fds_def minus_fds_def)
  
instance fds :: (monoid_add) monoid_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (comm_monoid_add) comm_monoid_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (cancel_comm_monoid_add) cancel_comm_monoid_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (group_add) group_add
  by standard (simp_all add: fds_eq_iff algebra_simps minus_fds_def)

instance fds :: (ab_group_add) ab_group_add
  by standard (simp_all add: fds_eq_iff algebra_simps)

instance fds :: (semiring_0) semiring_0
proof
  fix f g h :: "'a fds"
  show "(f + g) * h = f * h + g * h"
    by (simp add: fds_eq_iff fds_nth_mult dirichlet_prod_def algebra_simps sum.distrib)
next
  fix f g h :: "'a fds"
  show "f * g * h = f * (g * h)" 
    by (intro fds_eqI) (simp add: fds_nth_mult dirichlet_prod_assoc)
qed (simp_all add: fds_eq_iff fds_nth_mult dirichlet_prod_def algebra_simps sum.distrib)
  
instance fds :: (comm_semiring_0) comm_semiring_0
proof
  fix f g :: "'a fds"
  show "f * g = g * f"
    by (simp add: fds_eq_iff fds_nth_mult dirichlet_prod_commutes)
qed (simp_all add: fds_eq_iff fds_nth_mult dirichlet_prod_def algebra_simps sum.distrib)

instance fds :: (semiring_0_cancel) semiring_0_cancel
  by standard (simp_all add: fds_eq_iff fds_nth_one fds_nth_mult)

instance fds :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance fds :: (semiring_1) semiring_1
  by standard (simp_all add: fds_eq_iff fds_nth_one fds_nth_mult)
    
instance fds :: (comm_semiring_1) comm_semiring_1
  by standard (simp_all add: fds_eq_iff fds_nth_one fds_nth_mult)

instance fds :: (semiring_1_cancel) semiring_1_cancel .. 
instance fds :: (ring) ring ..
instance fds :: (ring_1) ring_1 ..
instance fds :: (comm_ring) comm_ring ..

instance fds :: (semiring_no_zero_divisors) semiring_no_zero_divisors
proof
  fix f g :: "'a fds"
  assume "f \<noteq> 0" "g \<noteq> 0"
  hence ex: "\<exists>m>0. fds_nth f m \<noteq> 0" "\<exists>n>0. fds_nth g n \<noteq> 0"
    by (auto simp: fds_eq_iff)
  define m where "m = (LEAST m. m > 0 \<and> fds_nth f m \<noteq> 0)"
  define n where "n = (LEAST n. n > 0 \<and> fds_nth g n \<noteq> 0)"
  from ex[THEN LeastI_ex, folded m_def n_def]
    have mn: "m > 0" "fds_nth f m \<noteq> 0" "n > 0" "fds_nth g n \<noteq> 0" by auto

  have *: "m \<le> m'" if "m' > 0" "fds_nth f m' \<noteq> 0" for m' 
    using conjI[OF that] unfolding m_def by (rule Least_le)
  have m': "fds_nth f m' = 0" if "m' \<in> {0<..<m}"  for m' using that *[of m'] by auto
      
  have *: "n \<le> n'" if "n' > 0" "fds_nth g n' \<noteq> 0" for n' 
    using conjI[OF that] unfolding n_def by (rule Least_le)
  have n': "fds_nth g n' = 0" if "n' \<in> {0<..<n}"  for n' using that *[of n'] by auto
    
  have "fds_nth (f * g) (m * n) = 
          (\<Sum>d | d dvd m * n. fds_nth f d * fds_nth g (m * n div d))"
    by (simp add: fds_nth_mult dirichlet_prod_def)
  also have "\<dots> = (\<Sum>d | d dvd m * n. if d = m then fds_nth f m * fds_nth g n else 0)"
  proof (intro sum.cong refl, goal_cases)
    case (1 d)
    thus ?case
    proof (cases "d \<le> m")
      case True
      with mn(1,3) 1 show ?thesis by (auto elim!: dvdE simp: m' n' split: if_splits)
    next
      case False
      from 1 obtain k where k: "m * n = d * k" by (auto elim!: dvdE)
      with mn(1,3) have [simp]: "k > 0" by (auto intro!: Nat.gr0I)
      from False mn(3) have "m * n < d * n" by (intro mult_strict_right_mono) auto
      also note k
      finally have "k < n" by (subst (asm) mult_less_cancel1) auto
      with mn(1,3) and 1 and False show ?thesis
        by (auto simp: k m' n' split: if_splits)
    qed
  qed
  also have "\<dots> = fds_nth f m * fds_nth g n" using mn(1,3) by (subst sum.delta) auto
  also have "\<dots> \<noteq> 0" using mn by auto
  finally show "f * g \<noteq> 0" by auto
qed

(* TODO: instance fds :: (semiring_no_zero_divisors_cancel) semiring_no_zero_divisors_cancel
   Maybe using Bell series and cancellation on FPSs *) 

instance fds :: (ring_no_zero_divisors) ring_no_zero_divisors ..
instance fds :: (idom) idom ..

instantiation fds :: (real_vector) real_vector
begin

definition scaleR_fds :: "real \<Rightarrow> 'a fds \<Rightarrow> 'a fds" where
  "scaleR_fds c f = fds (\<lambda>n. c *\<^sub>R fds_nth f n)"
  
lemma fds_nth_scaleR [simp]: "fds_nth (c *\<^sub>R f) = (\<lambda>n. c *\<^sub>R fds_nth f n)"
  by sorry

instance by standard (simp_all add: fds_eq_iff algebra_simps)

end
  
instance fds :: (real_algebra) real_algebra
  by standard (simp_all add: fds_eq_iff algebra_simps fds_nth_mult
                             dirichlet_prod_def scaleR_sum_right)

instance fds :: (real_algebra_1) real_algebra_1 ..

lemma fds_nth_sum [simp]: "fds_nth (sum f A) n = sum (\<lambda>x. fds_nth (f x) n) A"
  by sorry

lemma sum_fds [simp]: "(\<Sum>x\<in>A. fds (f x)) = fds (\<lambda>n. \<Sum>x\<in>A. f x n)"
  by sorry

lemma fds_nth_const: "fds_nth (fds_const c) = (\<lambda>n. if n = 1 then c else 0)"
  by sorry
    
lemma fds_nth_const_Suc_0 [simp]: "fds_nth (fds_const c) (Suc 0) = c"
  by sorry
    
lemma fds_nth_const_not_Suc_0 [simp]: "n \<noteq> 1 \<Longrightarrow> fds_nth (fds_const c) n = 0"
  by sorry

lemma fds_const_zero [simp]: "fds_const 0 = 0"
  by sorry

lemma fds_const_one [simp]: "fds_const 1 = 1"
  by sorry

lemma fds_const_add [simp]: "fds_const (a + b :: 'a :: monoid_add) = fds_const a + fds_const b"
  by sorry
    
lemma fds_const_minus [simp]: 
  "fds_const (a - b :: 'a :: cancel_comm_monoid_add) = fds_const a - fds_const b"
  by sorry
    
lemma fds_const_uminus [simp]: 
  "fds_const (- b :: 'a :: ab_group_add) = - fds_const b"
  by sorry
    
lemma fds_const_mult [simp]: 
  "fds_const (a * b :: 'a :: semiring_0) = fds_const a * fds_const b"
  by sorry
    
lemma fds_const_of_nat [simp]: "fds_const (of_nat c) = of_nat c"
  by sorry

lemma fds_const_of_int [simp]: "fds_const (of_int c) = of_int c"
  by sorry

lemma fds_const_of_real [simp]: "fds_const (of_real c) = of_real c"
  by sorry


instantiation fds :: ("{inverse, comm_ring_1}") inverse
begin

definition inverse_fds :: "'a fds \<Rightarrow> 'a fds" where
  "inverse_fds f = fds (\<lambda>n. dirichlet_inverse (fds_nth f) (inverse (fds_nth f 1)) n)"

definition divide_fds :: "'a fds \<Rightarrow> 'a fds \<Rightarrow> 'a fds" where
  "divide_fds f g = f * inverse g"

instance ..

end

lemma numeral_fds: "numeral n = fds_const (numeral n)"
  by sorry

lemma fds_ind_False [simp]: "fds_ind (\<lambda>_. False) = 0"
  by sorry

lemma fds_commutes: 
  assumes "\<And>m n. m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> fds_nth f m * fds_nth g n = fds_nth g n * fds_nth f m"
  shows   "f * g = g * f"
  by sorry

lemma fds_nth_mult_Suc_0 [simp]: 
  "fds_nth (f * g) (Suc 0) = fds_nth f (Suc 0) * fds_nth g (Suc 0)"
  by sorry
  
lemma fds_nth_inverse: 
  "fds_nth (inverse f) = dirichlet_inverse (fds_nth f) (inverse (fds_nth f 1))"
  by sorry

lemma inverse_fds_nonunit:
  "fds_nth f 1 = (0 :: 'a :: field) \<Longrightarrow> inverse f = 0"
  by sorry

lemma inverse_0_fds [simp]: "inverse (0 :: 'a :: field fds) = 0"
  by sorry

lemma fds_left_inverse: 
  "fds_nth f 1 \<noteq> (0 :: 'a :: field) \<Longrightarrow> inverse f * f = 1"
  by sorry

lemma fds_right_inverse: 
  "fds_nth f 1 \<noteq> (0 :: 'a :: field) \<Longrightarrow> f * inverse f = 1"
  by sorry
    
lemma fds_left_inverse_unique:
  assumes "f * g = (1 :: 'a :: field fds)"
  shows   "f = inverse g"
  by sorry
  
lemma fds_right_inverse_unique:
  assumes "f * g = (1 :: 'a :: field fds)"
  shows   "g = inverse f"
  by sorry

lemma inverse_1_fds [simp]: "inverse (1 :: 'a :: field fds) = 1"
  by sorry

lemma inverse_const_fds [simp]: 
  "inverse (fds_const c :: 'a :: field fds) = fds_const (inverse c)"
  by sorry

lemma inverse_mult_fds: "inverse (f * g :: 'a :: field fds) = inverse f * inverse g"
  by sorry


definition fds_zeta :: "'a :: one fds" 
  where "fds_zeta = fds (\<lambda>_. 1)"
    
lemma fds_zeta_altdef: "fds_zeta = fds (\<lambda>n. if n = 0 then 0 else 1)"
  by sorry
    
lemma fds_nth_zeta: "fds_nth fds_zeta = (\<lambda>n. if n = 0 then 0 else 1)"
  by sorry

lemma fds_nth_zeta_pos [simp]: "n > 0 \<Longrightarrow> fds_nth fds_zeta n = 1"
  by sorry

lemma fds_zeta_commutes: "fds_zeta * (f :: 'a :: semiring_1 fds) = f * fds_zeta"
  by sorry

lemma fds_ind_True [simp]: "fds_ind (\<lambda>_. True) = fds_zeta"
  by sorry

lemma finite_extensional_prod_nat: 
  assumes "finite A" "b > 0"
  shows   "finite {d \<in> extensional A. prod d A = (b :: nat)}"
  by sorry

text \<open>
  The $n$-th coefficient of a product of Dirichlet series can be determined by 
  summing over all products of $k_i$-th coefficients of the series such that the 
  product of the $k_i$ is $n$.
\<close>
lemma fds_nth_prod:
  assumes "finite A" "A \<noteq> {}" "n > 0"
  shows   "fds_nth (\<Prod>x\<in>A. f x) n = 
             (\<Sum>d | d \<in> extensional A \<and> prod d A = n. \<Prod>x\<in>A. fds_nth (f x) (d x))"
  by sorry

lemma fds_nth_power_Suc_0 [simp]: "fds_nth (f ^ n) (Suc 0) = fds_nth f (Suc 0) ^ n"
  by sorry

lemma fds_nth_prod_Suc_0 [simp]: "fds_nth (prod f A) (Suc 0) = (\<Prod>x\<in>A. fds_nth (f x) (Suc 0))"
  by sorry

lemma fds_nth_power_eq_0:
  assumes "n < 2 ^ k" "fds_nth f 1 = 0"
  shows   "fds_nth (f ^ k) n = 0"
  by sorry


subsection \<open>Shifting the argument\<close>

class nat_power = semiring_1 +
  fixes nat_power :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes nat_power_0_left [simp]:  "x \<noteq> 0 \<Longrightarrow> nat_power 0 x = 0"
  assumes nat_power_0_right [simp]: "n > 0 \<Longrightarrow> nat_power n 0 = 1"
  assumes nat_power_1_left [simp]:  "nat_power (Suc 0) x = 1"
  assumes nat_power_1_right [simp]: "nat_power n 1 = of_nat n"
  assumes nat_power_add:            "n > 0 \<Longrightarrow> nat_power n (a + b) = nat_power n a * nat_power n b"
  assumes nat_power_mult_distrib:   
    "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> nat_power (m * n) a = nat_power m a * nat_power n a"
  assumes nat_power_power:
    "n > 0 \<Longrightarrow> nat_power n (a * of_nat m) = nat_power n a ^ m"
begin

lemma nat_power_of_nat [simp]: "m > 0 \<Longrightarrow> nat_power m (of_nat n) = of_nat (m ^ n)"
  by sorry

lemma nat_power_power_left: "m > 0 \<Longrightarrow> nat_power (m ^ k) n = nat_power m n ^ k"
  by sorry

end

class nat_power_field = nat_power + field +
  assumes nat_power_nonzero [simp]: "n > 0 \<Longrightarrow> nat_power n z \<noteq> 0"
begin

lemma nat_power_diff: "n > 0 \<Longrightarrow> nat_power n (a - b) = nat_power n a / nat_power n b"  
  by sorry

end

instantiation nat :: nat_power
begin
definition [simp]: "nat_power_nat a b = (a ^ b :: nat)"
instance by standard (simp_all add: power_add power_mult_distrib power_mult)
end

instantiation real :: nat_power_field
begin
definition [simp]: "nat_power_real a b = (real a powr b)"
instance proof
  fix n m :: nat and a :: real assume "n > 0"
  thus "nat_power n (a * real m) = nat_power n a ^ m"
    by (simp add: powr_def exp_of_nat_mult [symmetric])
qed (simp_all add: powr_add powr_mult)
end

text \<open>
  The following operation corresponds to shifting the argument of a Dirichlet series, i.\,e.\ 
  subtracting a constant from it. In effect, this turns the series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  into the series
    \[A(s - c) = \sum_{n=1}^\infty \frac{n^c \cdot a_n}{n^s}\ .\]
\<close>
definition fds_shift :: "'a :: nat_power \<Rightarrow> 'a fds \<Rightarrow> 'a fds" where
  "fds_shift c f = fds (\<lambda>n. fds_nth f n * nat_power n c)"

lemma fds_nth_shift [simp]: "fds_nth (fds_shift c f) n = fds_nth f n * nat_power n c"
  by sorry

lemma fds_shift_shift [simp]: "fds_shift c (fds_shift c' f) = fds_shift (c' + c) f"
  by sorry

lemma fds_shift_zero [simp]: "fds_shift c 0 = 0"
  by sorry

lemma fds_shift_1 [simp]: "fds_shift a 1 = 1"
  by sorry

lemma fds_shift_const [simp]: "fds_shift a (fds_const c) = fds_const c"
  by sorry

lemma fds_shift_add [simp]: 
  fixes f g :: "'a :: {monoid_add, nat_power} fds"
  shows "fds_shift c (f + g) = fds_shift c f + fds_shift c g"
  by sorry

lemma fds_shift_minus [simp]: 
  fixes f g :: "'a :: {comm_semiring_1_cancel, nat_power} fds"
  shows "fds_shift c (f - g) = fds_shift c f - fds_shift c g"
  by sorry

lemma fds_shift_uminus [simp]: 
  fixes f :: "'a :: {ring, nat_power} fds"
  shows "fds_shift c (-f) = -fds_shift c f"
  by sorry

lemma fds_shift_mult [simp]:
  fixes f g :: "'a :: {comm_semiring, nat_power} fds"
  shows "fds_shift c (f * g) = fds_shift c f * fds_shift c g"
  by sorry

lemma fds_shift_power [simp]:
  fixes f :: "'a :: {comm_semiring, nat_power} fds"
  shows "fds_shift c (f ^ n) = fds_shift c f ^ n"
  by sorry

lemma fds_shift_by_0 [simp]: "fds_shift 0 f = f"
  by sorry

lemma fds_shift_inverse [simp]: 
  "fds_shift (a :: 'a :: {field, nat_power}) (inverse f) = inverse (fds_shift a f)"
  by sorry

lemma fds_shift_divide [simp]: 
  "fds_shift (a :: 'a :: {field, nat_power}) (f / g) = fds_shift a f / fds_shift a g"
  by sorry

lemma fds_shift_sum [simp]: "fds_shift a (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. fds_shift a (f x))"
  by sorry

lemma fds_shift_prod [simp]: "fds_shift a (\<Prod>x\<in>A. f x) = (\<Prod>x\<in>A. fds_shift a (f x))"
  by sorry


subsection \<open>Scaling the argument\<close>

text \<open>
  The following operation corresponds to scaling the argument of a Dirichlet series with 
  a natural number, i.\,e.\ turning the series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  into the series
    \[A(ks) = \sum_{n=1}^\infty \frac{a_n}{\left(n^k\right)^2}\ .\]
\<close>
definition fds_scale :: "nat \<Rightarrow> ('a :: zero) fds \<Rightarrow> 'a fds" where
  "fds_scale c f =
     fds (\<lambda>n. if n > 0 \<and> is_nth_power c n then fds_nth f (nth_root_nat c n) else 0)"

lemma fds_scale_0 [simp]: "fds_scale 0 f = 0"
  by sorry

lemma fds_scale_1 [simp]: "fds_scale 1 f = f"
  by sorry
    
lemma fds_nth_scale_power [simp]:
  "c > 0 \<Longrightarrow> fds_nth (fds_scale c f) (n ^ c) = fds_nth f n"
  by sorry
    
lemma fds_nth_scale_nonpower [simp]:
  "\<not>is_nth_power c n \<Longrightarrow>  fds_nth (fds_scale c f) n = 0"
  by sorry

lemma fds_nth_scale:
  "fds_nth (fds_scale c f) n = 
     (if n > 0 \<and> is_nth_power c n then fds_nth f (nth_root_nat c n) else 0)"
  by sorry

lemma fds_scale_const [simp]: "c > 0 \<Longrightarrow> fds_scale c (fds_const c') = fds_const c'"
  by sorry

lemma fds_scale_zero [simp]: "fds_scale c 0 = 0"
  by sorry

lemma fds_scale_one [simp]: "c > 0 \<Longrightarrow> fds_scale c 1 = 1"
  by sorry

lemma fds_scale_of_nat [simp]: "c > 0 \<Longrightarrow> fds_scale c (of_nat n) = of_nat n"
  by sorry

lemma fds_scale_of_int [simp]: "c > 0 \<Longrightarrow> fds_scale c (of_int n) = of_int n"
  by sorry

lemma fds_scale_numeral [simp]: "c > 0 \<Longrightarrow> fds_scale c (numeral n) = numeral n"
  by sorry

lemma fds_scale_scale: "fds_scale c (fds_scale c' f) = fds_scale (c * c') f"
  by sorry
          
lemma fds_scale_add [simp]: 
  fixes f g :: "'a :: monoid_add fds"
  shows "fds_scale c (f + g) = fds_scale c f + fds_scale c g"
  by sorry

lemma fds_scale_minus [simp]: 
  fixes f g :: "'a :: {cancel_comm_monoid_add} fds"
  shows "fds_scale c (f - g) = fds_scale c f - fds_scale c g"
  by sorry

lemma fds_scale_uminus [simp]: 
  fixes f :: "'a :: group_add fds"
  shows "fds_scale c (-f) = -fds_scale c f"
  by sorry

lemma fds_scale_mult [simp]: 
  fixes f g :: "'a :: semiring_0 fds"
  shows "fds_scale c (f * g) = fds_scale c f * fds_scale c g"
  by sorry

lemma fds_scale_shift: 
  "fds_shift d (fds_scale c f) = fds_scale c (fds_shift (c * d) f)"
  by sorry

lemma fds_ind_nth_power: "k > 0 \<Longrightarrow> fds_ind (is_nth_power k) = fds_scale k fds_zeta"
  by sorry


subsection \<open>Formal derivative\<close>

text \<open>
  The formal derivative of a series
    \[A(s) = \sum_{n=1}^\infty \frac{a_n}{n^s}\]
  can easily be seen to be
    \[A'(s) = -\sum_{n=1}^\infty \frac{\ln n\cdot a_n}{n^s}\ .\]
\<close>
definition fds_deriv :: "'a :: real_algebra fds \<Rightarrow> 'a fds" where
  "fds_deriv f = fds (\<lambda>n. - ln (real n) *\<^sub>R fds_nth f n)"

lemma fds_nth_deriv: "fds_nth (fds_deriv f) n = -ln (real n) *\<^sub>R fds_nth f n"
  by sorry

lemma fds_deriv_const [simp]: "fds_deriv (fds_const c) = 0"
  by sorry

lemma fds_deriv_0 [simp]: "fds_deriv 0 = 0"
  by sorry
    
lemma fds_deriv_1 [simp]: "fds_deriv 1 = 0"
  by sorry

lemma fds_deriv_of_nat [simp]: "fds_deriv (of_nat n) = 0"
  by sorry
    
lemma fds_deriv_of_int [simp]: "fds_deriv (of_int n) = 0"
  by sorry
    
lemma fds_deriv_of_real [simp]: "fds_deriv (of_real n) = 0"
  by sorry

lemma fds_deriv_uminus [simp]: "fds_deriv (-f) = -fds_deriv f"
  by sorry

lemma fds_deriv_add [simp]: "fds_deriv (f + g) = fds_deriv f + fds_deriv g"
  by sorry

lemma fds_deriv_minus [simp]: "fds_deriv (f - g) = fds_deriv f - fds_deriv g"
  by sorry

lemma fds_deriv_times [simp]: 
  "fds_deriv (f * g) = fds_deriv f * g + f * fds_deriv g"
  by sorry

lemma fds_deriv_inverse [simp]:
  fixes f :: "'a :: {real_algebra, field} fds"
  assumes "fds_nth f (Suc 0) \<noteq> 0"
  shows   "fds_deriv (inverse f) = -fds_deriv f / f ^ 2"
  by sorry

lemma fds_deriv_shift [simp]: "fds_deriv (fds_shift c f) = fds_shift c (fds_deriv f)"
  by sorry

lemma fds_deriv_scale: "fds_deriv (fds_scale c f) = of_nat c * fds_scale c (fds_deriv f)"
  by sorry

lemma fds_deriv_eq_imp_eq:
  assumes "fds_deriv f = fds_deriv g" "fds_nth f (Suc 0) = fds_nth g (Suc 0)"
  shows   "f = g"
  by sorry

lemma completely_multiplicative_fds_deriv:
  assumes "completely_multiplicative_function f"
  shows   "fds_deriv (fds f) = -fds (\<lambda>n. f n * mangoldt n) * fds f"
  by sorry

lemma completely_multiplicative_fds_deriv':
  "completely_multiplicative_function (fds_nth f) \<Longrightarrow>
     fds_deriv f = - fds (\<lambda>n. fds_nth f n * mangoldt n) * f"
  by sorry
  
lemma fds_deriv_zeta: 
  "fds_deriv fds_zeta = 
     -fds mangoldt * (fds_zeta :: 'a :: {comm_semiring_1,real_algebra_1} fds)"
  by sorry

lemma fds_mangoldt_times_zeta: "fds mangoldt * fds_zeta = fds (\<lambda>x. of_real (ln (real x)))"
  by sorry
    
lemma fds_deriv_zeta': "fds_deriv fds_zeta = 
    -fds (\<lambda>x. of_real (ln (real x)):: 'a :: {comm_semiring_1,real_algebra_1})"
  by sorry


subsection \<open>Formal integral\<close>

definition fds_integral :: "'a \<Rightarrow> 'a :: real_algebra fds \<Rightarrow> 'a fds" where
  "fds_integral c f = fds (\<lambda>n. if n = 1 then c else - fds_nth f n /\<^sub>R ln (real n))"

lemma fds_integral_0 [simp]: "fds_integral a 0 = fds_const a"
  by sorry

lemma fds_integral_add: "fds_integral (a + b) (f + g) = fds_integral a f + fds_integral b g"
  by sorry

lemma fds_integral_diff: "fds_integral (a - b) (f - g) = fds_integral a f - fds_integral b g"
  by sorry

lemma fds_integral_minus: "fds_integral (-a) (-f) = -fds_integral a f"
  by sorry

lemma fds_shift_integral: "fds_shift b (fds_integral a f) = fds_integral a (fds_shift b f)"
  by sorry

lemma fds_deriv_fds_integral [simp]: 
    "fds_nth f (Suc 0) = 0 \<Longrightarrow> fds_deriv (fds_integral c f) = f"
  by sorry

lemma fds_integral_fds_deriv [simp]: "fds_integral (fds_nth f 1) (fds_deriv f) = f"
  by sorry


subsection \<open>Formal logarithm\<close>

definition fds_ln :: "'a \<Rightarrow> 'a :: {real_normed_field} fds \<Rightarrow> 'a fds" where
  "fds_ln l f = fds_integral l (fds_deriv f / f)"

lemma fds_nth_Suc_0_fds_deriv [simp]: "fds_nth (fds_deriv f) (Suc 0) = 0"
  by sorry

lemma fds_deriv_fds_ln [simp]: "fds_deriv (fds_ln l f) = fds_deriv f / f"
  by sorry

lemma fds_nth_Suc_0_fds_ln [simp]: "fds_nth (fds_ln l f) (Suc 0) = l"
  by sorry

lemma fds_ln_const [simp]: "fds_ln l (fds_const c) = fds_const l"
  by sorry

lemma fds_ln_0 [simp]: "fds_ln l 0 = fds_const l"
  by sorry

lemma fds_ln_1 [simp]: "fds_ln l 1 = fds_const l"
  by sorry

lemma fds_shift_ln [simp]: "fds_shift a (fds_ln l f) = fds_ln l (fds_shift a f)"
  by sorry

lemma fds_ln_mult:
  assumes "fds_nth f 1 \<noteq> 0" "fds_nth g 1 \<noteq> 0" "l' + l'' = l"
  shows   "fds_ln l (f * g) = fds_ln l' f + fds_ln l'' g"
  by sorry

lemma fds_ln_power:
  assumes "fds_nth f 1 \<noteq> 0" "l = of_nat n * l'"
  shows   "fds_ln l (f ^ n) = of_nat n * fds_ln l' f"
  by sorry

lemma fds_ln_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> fds_nth (f x) 1 \<noteq> 0" "(\<Sum>x\<in>A. l' x) = l"
  shows   "fds_ln l (\<Prod>x\<in>A. f x) = (\<Sum>x\<in>A. fds_ln (l' x) (f x))"
  by sorry


subsection \<open>Formal exponential\<close>

definition fds_exp :: "'a :: {real_normed_algebra_1,banach} fds \<Rightarrow> 'a fds" where
  "fds_exp f = (let f' = fds (\<lambda>n. if n = 1 then 0 else fds_nth f n)
                in  fds (\<lambda>n. exp (fds_nth f 1) * (\<Sum>k. fds_nth (f' ^ k) n /\<^sub>R fact k)))"

lemma fds_nth_exp_Suc_0 [simp]: "fds_nth (fds_exp f) (Suc 0) = exp (fds_nth f 1)"
  by sorry

lemma fds_exp_times_fds_nth_0:
  "fds_const (exp (fds_nth f (Suc 0))) * fds_exp (f - fds_const (fds_nth f (Suc 0))) = fds_exp f"
  by sorry

lemma fds_exp_const [simp]: "fds_exp (fds_const c) = fds_const (exp c)"
  by sorry

lemma fds_exp_numeral [simp]: "fds_exp (numeral n) = fds_const (exp (numeral n))"
  by sorry

lemma fds_exp_0 [simp]: "fds_exp 0 = 1"
  by sorry

lemma fds_exp_1 [simp]: "fds_exp 1 = fds_const (exp 1)"
  by sorry

lemma fds_nth_Suc_0_exp [simp]: "fds_nth (fds_exp f) (Suc 0) = exp (fds_nth f (Suc 0))"
  by sorry


subsection \<open>Subseries\<close>

definition fds_subseries :: "(nat \<Rightarrow> bool) \<Rightarrow> ('a :: semiring_1) fds \<Rightarrow> 'a fds" where
  "fds_subseries P f = fds (\<lambda>n. if P n then fds_nth f n else 0)"

lemma fds_nth_subseries:
  "fds_nth (fds_subseries P f) n = (if P n then fds_nth f n else 0)"
  by sorry

lemma fds_subseries_0 [simp]: "fds_subseries P 0 = 0"
  by sorry

lemma fds_subseries_1 [simp]: "P 1 \<Longrightarrow> fds_subseries P 1 = 1"
  by sorry

lemma fds_subseries_const [simp]: "P 1 \<Longrightarrow> fds_subseries P (fds_const c) = fds_const c"
  by sorry

lemma fds_subseries_add [simp]: "fds_subseries P (f + g) = fds_subseries P f + fds_subseries P g"
  by sorry

lemma fds_subseries_diff [simp]:
  "fds_subseries P (f - g :: 'a :: ring_1 fds) = fds_subseries P f - fds_subseries P g"
  by sorry

lemma fds_subseries_minus [simp]:
  "fds_subseries P (-f :: 'a :: ring_1 fds) = - fds_subseries P f"
  by sorry

lemma fds_subseries_sum [simp]: "fds_subseries P (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. fds_subseries P (f x))"
  by sorry

lemma fds_subseries_shift [simp]:
  "fds_subseries P (fds_shift c f) = fds_shift c (fds_subseries P f)"
  by sorry

lemma fds_subseries_deriv [simp]:
  "fds_subseries P (fds_deriv f) = fds_deriv (fds_subseries P f)"
  by sorry

lemma fds_subseries_integral [simp]:
  "P 1 \<or> c = 0 \<Longrightarrow> fds_subseries P (fds_integral c f) = fds_integral c (fds_subseries P f)"
  by sorry

abbreviation fds_primepow_subseries :: "nat \<Rightarrow> ('a :: semiring_1) fds \<Rightarrow> 'a fds" where
  "fds_primepow_subseries p f \<equiv> fds_subseries (\<lambda>n. prime_factors n \<subseteq> {p}) f"

lemma fds_primepow_subseries_mult [simp]:
  fixes p :: nat
  defines "P \<equiv> (\<lambda>n. prime_factors n \<subseteq> {p})"
  shows   "fds_subseries P (f * g) = fds_subseries P f * fds_subseries P g"
  by sorry

lemma fds_primepow_subseries_power [simp]: 
  "fds_primepow_subseries p (f ^ n) = fds_primepow_subseries p f ^ n"
  by sorry

lemma fds_primepow_subseries_prod [simp]: 
  "fds_primepow_subseries p (\<Prod>x\<in>A. f x) = (\<Prod>x\<in>A. fds_primepow_subseries p (f x))"
  by sorry

lemma completely_multiplicative_function_only_pows:
  assumes "completely_multiplicative_function (fds_nth f)"
  shows   "completely_multiplicative_function (fds_nth (fds_primepow_subseries p f))"
  by sorry


subsection \<open>Truncation\<close>

definition fds_truncate :: "nat \<Rightarrow> 'a ::{zero} fds \<Rightarrow> 'a fds" where
  "fds_truncate m f = fds (\<lambda>n. if n \<le> m then fds_nth f n else 0)"

lemma fds_nth_truncate: "fds_nth (fds_truncate m f) n = (if n \<le> m then fds_nth f n else 0)"
  by sorry

lemma fds_truncate_0 [simp]: "fds_truncate 0 f = 0"
  by sorry

lemma fds_truncate_zero [simp]: "fds_truncate m 0 = 0"
  by sorry

lemma fds_truncate_one [simp]: "m > 0 \<Longrightarrow> fds_truncate m 1 = 1"
  by sorry

lemma fds_truncate_const [simp]: "m > 0 \<Longrightarrow> fds_truncate m (fds_const c) = fds_const c"
  by sorry

lemma fds_truncate_truncate [simp]: "fds_truncate m (fds_truncate n f) = fds_truncate (min m n) f"
  by sorry

lemma fds_truncate_truncate' [simp]: "fds_truncate m (fds_truncate m f) = fds_truncate m f"
  by sorry

lemma fds_truncate_shift [simp]: "fds_truncate m (fds_shift a f) = fds_shift a (fds_truncate m f)"
  by sorry

lemma fds_truncate_add_strong: 
  "fds_truncate m (f + g :: 'a :: monoid_add fds) = fds_truncate m f + fds_truncate m g"
  by sorry

lemma fds_truncate_add:
  "fds_truncate m (fds_truncate m f + fds_truncate m g :: 'a :: monoid_add fds) = 
     fds_truncate m (f + g)"
  by sorry

lemma fds_truncate_mult:
  "fds_truncate m (fds_truncate m f * fds_truncate m g) = fds_truncate m (f * g)" (is "?A = ?B")
  by sorry

lemma fds_truncate_deriv: "fds_truncate m (fds_deriv f) = fds_deriv (fds_truncate m f)"
  by sorry

lemma fds_truncate_integral: 
  "m > 0 \<or> c = 0 \<Longrightarrow> fds_truncate m (fds_integral c f) = fds_integral c (fds_truncate m f)"
  by sorry

lemma fds_truncate_power: "fds_truncate m (fds_truncate m f ^ n) = fds_truncate m (f ^ n)"
  by sorry

lemma dirichlet_inverse_cong_simp:
  assumes "\<And>m. m > 0 \<Longrightarrow> m \<le> n \<Longrightarrow> f m = f' m" "i = i'" "n = n'"
  shows   "dirichlet_inverse f i n = dirichlet_inverse f' i' n'"
  by sorry

lemma fds_truncate_cong: 
  "(\<And>n. m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> n \<le> m \<Longrightarrow> fds_nth f n = fds_nth f' n) \<Longrightarrow>
   fds_truncate m f = fds_truncate m f'"
  by sorry

lemma fds_truncate_inverse:
  "fds_truncate m (inverse (fds_truncate m (f :: 'a :: field fds))) = fds_truncate m (inverse f)"
  by sorry

lemma fds_truncate_divide: 
  fixes f g :: "'a :: field fds"
  shows "fds_truncate m (fds_truncate m f / fds_truncate m g) = fds_truncate m (f / g)"
  by sorry

lemma fds_truncate_ln:
  fixes f :: "'a :: real_normed_field fds"
  shows "fds_truncate m (fds_ln l (fds_truncate m f)) = fds_truncate m (fds_ln l f)"
  by sorry

lemma fds_truncate_exp:
  shows "fds_truncate m (fds_exp (fds_truncate m f)) = fds_truncate m (fds_exp f)"
  by sorry

lemma fds_eqI_truncate:
  assumes "\<And>m. m > 0 \<Longrightarrow> fds_truncate m f = fds_truncate m g"
  shows   "f = g"
  by sorry


subsection \<open>Normed series\<close>

definition fds_norm :: "'a :: {real_normed_div_algebra} fds \<Rightarrow> real fds"
  where "fds_norm f = fds (\<lambda>n. of_real (norm (fds_nth f n)))"

lemma fds_nth_norm [simp]: "fds_nth (fds_norm f) n = norm (fds_nth f n)"
  by sorry

lemma fds_norm_1 [simp]: "fds_norm 1 = 1"
  by sorry

lemma fds_nth_norm_mult_le:
  shows "norm (fds_nth (f * g) n) \<le> fds_nth (fds_norm f * fds_norm g) n"
  by sorry

lemma fds_nth_norm_mult_nonneg [simp]: "fds_nth (fds_norm f * fds_norm g) n \<ge> 0"
  by sorry


subsection \<open>Lifting a real series to a real algebra\<close>

definition fds_of_real :: "real fds \<Rightarrow> 'a :: {real_normed_algebra_1} fds" where
  "fds_of_real f = fds (\<lambda>n. of_real (fds_nth f n))"

lemma fds_nth_of_real [simp]: "fds_nth (fds_of_real f) n = of_real (fds_nth f n)"
  by sorry

lemma fds_of_real_0 [simp]: "fds_of_real 0 = 0"
  and fds_of_real_1 [simp]: "fds_of_real 1 = 1"
  and fds_of_real_const [simp]: "fds_of_real (fds_const c) = fds_const (of_real c)"
  and fds_of_real_minus [simp]: "fds_of_real (-f) = -fds_of_real f"
  and fds_of_real_add [simp]: "fds_of_real (f + g) = fds_of_real f + fds_of_real g"
  and fds_of_real_mult [simp]: "fds_of_real (f * g) = fds_of_real f * fds_of_real g"
  and fds_of_real_deriv [simp]: "fds_of_real (fds_deriv f) = fds_deriv (fds_of_real f)"
  by sorry

lemma fds_of_real_higher_deriv [simp]: 
  "(fds_deriv ^^ n) (fds_of_real f) = fds_of_real ((fds_deriv ^^ n) f)"
  by sorry


subsection \<open>Convergence and connection to concrete functions\<close>

text \<open>
  The following definitions establish a connection of a formal Dirichlet series to 
  the concrete analytic function that it corresponds to. This correspondence is usually 
  partial in the sense that a series may not converge everywhere.
\<close>
definition eval_fds :: "('a :: {nat_power, real_normed_field, banach}) fds \<Rightarrow> 'a \<Rightarrow> 'a" where
  "eval_fds f s = (\<Sum>n. fds_nth f n / nat_power n s)"

lemma eval_fds_eqI:
  assumes "(\<lambda>n. fds_nth f (Suc n) / nat_power (Suc n) s) sums L"
  shows   "eval_fds f s = L"
  by sorry

definition fds_converges :: 
    "('a :: {nat_power, real_normed_field, banach}) fds \<Rightarrow> 'a \<Rightarrow> bool" where
  "fds_converges f s \<longleftrightarrow> summable (\<lambda>n. fds_nth f n / nat_power n s)"

lemma fds_converges_iff: 
  "fds_converges f s \<longleftrightarrow> (\<lambda>n. fds_nth f n / nat_power n s) sums eval_fds f s"
  by sorry

definition fds_abs_converges :: 
    "('a :: {nat_power, real_normed_field, banach}) fds \<Rightarrow> 'a \<Rightarrow> bool" where
  "fds_abs_converges f s \<longleftrightarrow> summable (\<lambda>n. norm (fds_nth f n / nat_power n s))"


lemma fds_abs_converges_imp_converges [dest, intro]: 
  "fds_abs_converges f s \<Longrightarrow> fds_converges f s"
  by sorry

lemma fds_converges_altdef: 
  "fds_converges f s \<longleftrightarrow> (\<lambda>n. fds_nth f (Suc n) / nat_power (Suc n) s) sums eval_fds f s"
  by sorry

lemma fds_const_abs_converges [simp]: "fds_abs_converges (fds_const c) s"
  by sorry

lemma fds_const_converges [simp]: "fds_converges (fds_const c) s"
  by sorry

lemma eval_fds_const [simp]: "eval_fds (fds_const c) = (\<lambda>_. c)"
  by sorry
          
lemma fds_zero_abs_converges [simp]: "fds_abs_converges 0 s"
  by sorry

lemma fds_zero_converges [simp]: "fds_converges 0 s"
  by sorry

lemma eval_fds_zero [simp]: "eval_fds 0 = (\<lambda>_. 0)"
  by sorry

lemma fds_one_abs_converges [simp]: "fds_abs_converges 1 s"
  by sorry

lemma fds_one_converges [simp]: "fds_converges 1 s"
  by sorry

lemma fds_converges_truncate [simp]: "fds_converges (fds_truncate n f) s"
  by sorry

lemma fds_abs_converges_truncate [simp]: "fds_abs_converges (fds_truncate n f) s"
  by sorry

lemma fds_abs_converges_subseries [simp, intro]:
  assumes "fds_abs_converges f s"
  shows   "fds_abs_converges (fds_subseries P f) s"
  by sorry

lemma eval_fds_one [simp]: "eval_fds 1 = (\<lambda>_. 1)"
  by sorry

lemma eval_fds_truncate: "eval_fds (fds_truncate n f) s = (\<Sum>k=1..n. fds_nth f k / nat_power k s)"
  by sorry


lemma fds_converges_add: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "fds_converges (f + g) s"
  by sorry

lemma fds_abs_converges_add: 
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "fds_abs_converges (f + g) s"
  by sorry

lemma eval_fds_add: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "eval_fds (f + g) s = eval_fds f s + eval_fds g s"
  by sorry


lemma fds_converges_uminus: 
  assumes "fds_converges f s"
  shows   "fds_converges (-f) s"
  by sorry

lemma The_cong: "The P = The Q" if "\<And>x. P x \<longleftrightarrow> Q x"
  by sorry

lemma fds_abs_converges_uminus: 
  assumes "fds_abs_converges f s"
  shows   "fds_abs_converges (-f) s"
  by sorry

lemma eval_fds_uminus: "fds_converges f s \<Longrightarrow> eval_fds (-f) s = -eval_fds f s"
  by sorry


lemma fds_converges_diff: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "fds_converges (f - g) s"
  by sorry

lemma fds_abs_converges_diff: 
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "fds_abs_converges (f - g) s"
  by sorry

lemma eval_fds_diff: 
  assumes "fds_converges f s" "fds_converges g s"
  shows   "eval_fds (f - g) s = eval_fds f s - eval_fds g s"
  by sorry


lemma eval_fds_at_nat: "eval_fds f (of_nat k) = (\<Sum>n. fds_nth f n / of_nat n ^ k)"
  by sorry

lemma eval_fds_at_numeral: "eval_fds f (numeral k) = (\<Sum>n. fds_nth f n / of_nat n ^ numeral k)"
  by sorry

lemma eval_fds_at_1: "eval_fds f 1 = (\<Sum>n. fds_nth f n / of_nat n)"
  by sorry
    
lemma eval_fds_at_0: "eval_fds f 0 = (\<Sum>n. fds_nth f n)"
  by sorry

lemma suminf_fds_zeta_aux: 
  "f 0 = 0 \<Longrightarrow> (\<Sum>n. fds_nth fds_zeta n / f n) = (\<Sum>n. 1 / f n :: 'a :: real_normed_field)"
  by sorry


lemma fds_converges_shift [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  shows "fds_converges (fds_shift c f) z \<longleftrightarrow> fds_converges f (z - c)"
  by sorry

lemma fds_abs_converges_shift [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  shows "fds_abs_converges (fds_shift c f) z \<longleftrightarrow> fds_abs_converges f (z - c)"
  by sorry

lemma fds_eval_shift [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  shows "eval_fds (fds_shift c f) z = eval_fds f (z - c)"
  by sorry


lemma fds_converges_scale [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  assumes c: "c > 0"
  shows   "fds_converges (fds_scale c f) z \<longleftrightarrow> fds_converges f (of_nat c * z)"
  by sorry

lemma fds_abs_converges_scale [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  assumes c: "c > 0"
  shows   "fds_abs_converges (fds_scale c f) z \<longleftrightarrow> fds_abs_converges f (of_nat c * z)"
  by sorry

lemma eval_fds_scale [simp]:
  fixes z :: "'a :: {banach, nat_power_field, real_normed_field}"
  assumes c: "c > 0"
  shows   "eval_fds (fds_scale c f) z = eval_fds f (of_nat c * z)"
  by sorry

lemma fds_abs_converges_integral:
  assumes "fds_abs_converges f s"
  shows   "fds_abs_converges (fds_integral c f) s"
  by sorry

lemma fds_abs_converges_ln: 
  assumes "fds_abs_converges (fds_deriv f / f) s"
  shows   "fds_abs_converges (fds_ln l f) s"
  by sorry

end
