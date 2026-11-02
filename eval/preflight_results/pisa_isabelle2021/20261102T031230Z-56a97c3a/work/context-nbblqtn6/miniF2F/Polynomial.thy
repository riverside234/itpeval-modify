(*  Title:      HOL/Computational_Algebra/Polynomial.thy
    Author:     Brian Huffman
    Author:     Clemens Ballarin
    Author:     Amine Chaieb
    Author:     Florian Haftmann
*)

section \<open>Polynomials as type over a ring structure\<close>

theory Polynomial
imports
  Complex_Main
  "HOL-Library.More_List"
  "HOL-Library.Infinite_Set"
  Primes
begin
declare [[quick_and_dirty = true]]


context semidom_modulo
begin

lemma not_dvd_imp_mod_neq_0:
  \<open>a mod b \<noteq> 0\<close> if \<open>\<not> b dvd a\<close>
  
  sorry


end

subsection \<open>Auxiliary: operations for lists (later) representing coefficients\<close>

definition cCons :: "'a::zero \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixr \<open>##\<close> 65)
  where "x ## xs = (if xs = [] \<and> x = 0 then [] else x # xs)"

lemma cCons_0_Nil_eq [simp]: "0 ## [] = []"
  
  sorry


lemma cCons_Cons_eq [simp]: "x ## y # ys = x # y # ys"
  
  sorry


lemma cCons_append_Cons_eq [simp]: "x ## xs @ y # ys = x # xs @ y # ys"
  
  sorry


lemma cCons_not_0_eq [simp]: "x \<noteq> 0 \<Longrightarrow> x ## xs = x # xs"
  
  sorry


lemma strip_while_not_0_Cons_eq [simp]:
  "strip_while (\<lambda>x. x = 0) (x # xs) = x ## strip_while (\<lambda>x. x = 0) xs"
  
  sorry


lemma tl_cCons [simp]: "tl (x ## xs) = xs"
  
  sorry



subsection \<open>Definition of type \<open>poly\<close>\<close>

typedef (overloaded) 'a poly = "{f :: nat \<Rightarrow> 'a::zero. \<forall>\<^sub>\<infinity> n. f n = 0}"
  morphisms coeff Abs_poly
  
  sorry


lemma poly_eq_iff: "p = q \<longleftrightarrow> (\<forall>n. coeff p n = coeff q n)"
  
  sorry


lemma poly_eqI: "(\<And>n. coeff p n = coeff q n) \<Longrightarrow> p = q"
  
  sorry


lemma MOST_coeff_eq_0: "\<forall>\<^sub>\<infinity> n. coeff p n = 0"
  
  sorry


lemma coeff_Abs_poly:
  assumes "\<And>i. i > n \<Longrightarrow> f i = 0"
  shows   "coeff (Abs_poly f) = f"
  
  sorry



subsection \<open>Degree of a polynomial\<close>

definition degree :: "'a::zero poly \<Rightarrow> nat"
  where "degree p = (LEAST n. \<forall>i>n. coeff p i = 0)"

lemma degree_cong:
  assumes "\<And>i. coeff p i = 0 \<longleftrightarrow> coeff q i = 0"
  shows   "degree p = degree q"
  
  sorry


lemma coeff_Abs_poly_If_le:
  "coeff (Abs_poly (\<lambda>i. if i \<le> n then f i else 0)) = (\<lambda>i. if i \<le> n then f i else 0)"
  
  sorry


lemma coeff_eq_0:
  assumes "degree p < n"
  shows "coeff p n = 0"
  
  sorry


lemma le_degree: "coeff p n \<noteq> 0 \<Longrightarrow> n \<le> degree p"
  
  sorry


lemma degree_le: "\<forall>i>n. coeff p i = 0 \<Longrightarrow> degree p \<le> n"
  
  sorry


lemma less_degree_imp: "n < degree p \<Longrightarrow> \<exists>i>n. coeff p i \<noteq> 0"
  
  sorry


lemma poly_eqI2:
  assumes "degree p = degree q" and "\<And>i. i \<le> degree p \<Longrightarrow> coeff p i = coeff q i"
  shows "p = q"
  
  sorry



subsection \<open>The zero polynomial\<close>

instantiation poly :: (zero) zero
begin

lift_definition zero_poly :: "'a poly"
  is "\<lambda>_. 0"
  
  sorry


instance 
  sorry


end

lemma coeff_0 [simp]: "coeff 0 n = 0"
  
  sorry


lemma degree_0 [simp]: "degree 0 = 0"
  
  sorry


lemma leading_coeff_neq_0:
  assumes "p \<noteq> 0"
  shows "coeff p (degree p) \<noteq> 0"
  
  sorry


lemma leading_coeff_0_iff [simp]: "coeff p (degree p) = 0 \<longleftrightarrow> p = 0"
  
  sorry


lemma degree_lessI:
  assumes "p \<noteq> 0 \<or> n > 0" "\<forall>k\<ge>n. coeff p k = 0"
  shows   "degree p < n"
  
  sorry


lemma eq_zero_or_degree_less:            
  assumes "degree p \<le> n" and "coeff p n = 0"
  shows "p = 0 \<or> degree p < n"
  
  sorry


lemma coeff_0_degree_minus_1: "coeff rrr dr = 0 \<Longrightarrow> degree rrr \<le> dr \<Longrightarrow> degree rrr \<le> dr - 1"
  
  sorry



subsection \<open>List-style constructor for polynomials\<close>

lift_definition pCons :: "'a::zero \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p. case_nat a (coeff p)"
  
  sorry


lemmas coeff_pCons = pCons.rep_eq

lemma coeff_pCons': "poly.coeff (pCons c p) n = (if n = 0 then c else poly.coeff p (n - 1))"
  
  sorry


lemma coeff_pCons_0 [simp]: "coeff (pCons a p) 0 = a"
  
  sorry


lemma coeff_pCons_Suc [simp]: "coeff (pCons a p) (Suc n) = coeff p n"
  
  sorry


lemma degree_pCons_le: "degree (pCons a p) \<le> Suc (degree p)"
  
  sorry


lemma degree_pCons_eq: "p \<noteq> 0 \<Longrightarrow> degree (pCons a p) = Suc (degree p)"
  
  sorry


lemma degree_pCons_0: "degree (pCons a 0) = 0"
  
  sorry


lemma degree_pCons_eq_if [simp]: "degree (pCons a p) = (if p = 0 then 0 else Suc (degree p))"
  
  sorry


lemma pCons_0_0 [simp]: "pCons 0 0 = 0"
  
  sorry


lemma pCons_eq_iff [simp]: "pCons a p = pCons b q \<longleftrightarrow> a = b \<and> p = q"
  
  sorry


lemma pCons_eq_0_iff [simp]: "pCons a p = 0 \<longleftrightarrow> a = 0 \<and> p = 0"
  
  sorry


lemma pCons_cases [cases type: poly]:
  obtains (pCons) a q where "p = pCons a q"
  
  sorry


lemma pCons_induct [case_names 0 pCons, induct type: poly]:
  assumes zero: "P 0"
  assumes pCons: "\<And>a p. a \<noteq> 0 \<or> p \<noteq> 0 \<Longrightarrow> P p \<Longrightarrow> P (pCons a p)"
  shows "P p"
  
  sorry


lemma degree_eq_zeroE:
  fixes p :: "'a::zero poly"
  assumes "degree p = 0"
  obtains a where "p = pCons a 0"
  
  sorry



subsection \<open>Quickcheck generator for polynomials\<close>

quickcheck_generator poly constructors: "0 :: _ poly", pCons


subsection \<open>List-style syntax for polynomials\<close>

syntax
  "_poly" :: "args \<Rightarrow> 'a poly"  (\<open>(\<open>indent=2 notation=\<open>mixfix polynomial enumeration\<close>\<close>[:_:])\<close>)
syntax_consts
  "_poly" \<rightleftharpoons> pCons
translations
  "[:x, xs:]" \<rightleftharpoons> "CONST pCons x [:xs:]"
  "[:x:]" \<rightleftharpoons> "CONST pCons x 0"

lemma degree_0_id: 
  assumes "degree p = 0"
  shows "[: coeff p 0 :] = p"
  
  sorry


lemma degree0_coeffs: "degree p = 0 \<Longrightarrow> \<exists> a. p = [: a :]"
  
  sorry


lemma degree1_coeffs:
  fixes p :: "'a::zero poly"
  assumes "degree p = 1"
  obtains a b where "p = [: b, a :]" "a \<noteq> 0"
  
  sorry


lemma degree2_coeffs:
  fixes p :: "'a::zero poly"
  assumes "degree p = 2"
  obtains a b c where "p = [: c, b, a :]" "a \<noteq> 0"
  
  sorry



subsection \<open>Representation of polynomials by lists of coefficients\<close>

primrec Poly :: "'a::zero list \<Rightarrow> 'a poly"
  where
    [code_post]: "Poly [] = 0"
  | [code_post]: "Poly (a # as) = pCons a (Poly as)"

lemma Poly_replicate_0 [simp]: "Poly (replicate n 0) = 0"
  
  sorry


lemma Poly_eq_0: "Poly as = 0 \<longleftrightarrow> (\<exists>n. as = replicate n 0)"
  
  sorry


lemma Poly_append_replicate_0 [simp]: "Poly (as @ replicate n 0) = Poly as"
  
  sorry


lemma Poly_snoc_zero [simp]: "Poly (as @ [0]) = Poly as"
  
  sorry


lemma Poly_cCons_eq_pCons_Poly [simp]: "Poly (a ## p) = pCons a (Poly p)"
  
  sorry


lemma Poly_on_rev_starting_with_0 [simp]: "hd as = 0 \<Longrightarrow> Poly (rev (tl as)) = Poly (rev as)"
  
  sorry


lemma degree_Poly: "degree (Poly xs) \<le> length xs"
  
  sorry


lemma coeff_Poly_eq [simp]: "coeff (Poly xs) = nth_default 0 xs"
  
  sorry


definition coeffs :: "'a poly \<Rightarrow> 'a::zero list"
  where "coeffs p = (if p = 0 then [] else map (\<lambda>i. coeff p i) [0 ..< Suc (degree p)])"

lemma coeffs_eq_Nil [simp]: "coeffs p = [] \<longleftrightarrow> p = 0"
  
  sorry


lemma not_0_coeffs_not_Nil: "p \<noteq> 0 \<Longrightarrow> coeffs p \<noteq> []"
  
  sorry


lemma coeffs_0_eq_Nil [simp]: "coeffs 0 = []"
  
  sorry


lemma coeffs_pCons_eq_cCons [simp]: "coeffs (pCons a p) = a ## coeffs p"
  
  sorry


lemma length_coeffs: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = degree p + 1"
  
  sorry


lemma coeffs_nth: "p \<noteq> 0 \<Longrightarrow> n \<le> degree p \<Longrightarrow> coeffs p ! n = coeff p n"
  
  sorry


lemma coeff_in_coeffs: "p \<noteq> 0 \<Longrightarrow> n \<le> degree p \<Longrightarrow> coeff p n \<in> set (coeffs p)"
  
  sorry


lemma not_0_cCons_eq [simp]: "p \<noteq> 0 \<Longrightarrow> a ## coeffs p = a # coeffs p"
  
  sorry


lemma Poly_coeffs [simp, code abstype]: "Poly (coeffs p) = p"
  
  sorry


lemma coeffs_Poly [simp]: "coeffs (Poly as) = strip_while (HOL.eq 0) as"
  
  sorry


lemma no_trailing_coeffs [simp]:
  "no_trailing (HOL.eq 0) (coeffs p)"
  
  sorry


lemma strip_while_coeffs [simp]:
  "strip_while (HOL.eq 0) (coeffs p) = coeffs p"
  
  sorry


lemma coeffs_eq_iff: "p = q \<longleftrightarrow> coeffs p = coeffs q"
  (is "?P \<longleftrightarrow> ?Q")
  
  sorry


lemma nth_default_coeffs_eq: "nth_default 0 (coeffs p) = coeff p"
  
  sorry


lemma range_coeff: "range (coeff p) = insert 0 (set (coeffs p))" 
  
  sorry


lemma [code]: "coeff p = nth_default 0 (coeffs p)"
  
  sorry


lemma coeffs_eqI:
  assumes coeff: "\<And>n. coeff p n = nth_default 0 xs n"
  assumes zero: "no_trailing (HOL.eq 0) xs"
  shows "coeffs p = xs"
  
  sorry


lemma degree_eq_length_coeffs [code]: "degree p = length (coeffs p) - 1"
  
  sorry


lemma length_coeffs_degree: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = Suc (degree p)"
  
  sorry


lemma [code abstract]: "coeffs 0 = []"
  
  sorry


lemma [code abstract]: "coeffs (pCons a p) = a ## coeffs p"
  
  sorry


lemma set_coeffs_subset_singleton_0_iff [simp]:
  "set (coeffs p) \<subseteq> {0} \<longleftrightarrow> p = 0"
  
  sorry


lemma set_coeffs_not_only_0 [simp]:
  "set (coeffs p) \<noteq> {0}"
  
  sorry


lemma forall_coeffs_conv:
  "(\<forall>n. P (coeff p n)) \<longleftrightarrow> (\<forall>c \<in> set (coeffs p). P c)" if "P 0"
  
  sorry


instantiation poly :: ("{zero, equal}") equal
begin

definition [code]: "HOL.equal (p::'a poly) q \<longleftrightarrow> HOL.equal (coeffs p) (coeffs q)"

instance
  
  sorry


end

lemma [code nbe]: "HOL.equal (p :: _ poly) p \<longleftrightarrow> True"
  
  sorry


definition is_zero :: "'a::zero poly \<Rightarrow> bool"
  where [code]: "is_zero p \<longleftrightarrow> List.null (coeffs p)"

lemma is_zero_null [code_abbrev]: "is_zero p \<longleftrightarrow> p = 0"
  
  sorry



text \<open>Reconstructing the polynomial from the list\<close>
  \<comment> \<open>contributed by Sebastiaan J.C. Joosten and René Thiemann\<close>

definition poly_of_list :: "'a::comm_monoid_add list \<Rightarrow> 'a poly"
  where [simp]: "poly_of_list = Poly"

lemma poly_of_list_impl [code abstract]: "coeffs (poly_of_list as) = strip_while (HOL.eq 0) as"
  
  sorry



subsection \<open>Fold combinator for polynomials\<close>

definition fold_coeffs :: "('a::zero \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a poly \<Rightarrow> 'b \<Rightarrow> 'b"
  where "fold_coeffs f p = foldr f (coeffs p)"

lemma fold_coeffs_0_eq [simp]: "fold_coeffs f 0 = id"
  
  sorry


lemma fold_coeffs_pCons_eq [simp]: "f 0 = id \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  
  sorry


lemma fold_coeffs_pCons_0_0_eq [simp]: "fold_coeffs f (pCons 0 0) = id"
  
  sorry


lemma fold_coeffs_pCons_coeff_not_0_eq [simp]:
  "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  
  sorry


lemma fold_coeffs_pCons_not_0_0_eq [simp]:
  "p \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  
  sorry



subsection \<open>Canonical morphism on polynomials -- evaluation\<close>

definition poly :: \<open>'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>poly p a = horner_sum id a (coeffs p)\<close>

lemma poly_eq_fold_coeffs:
  \<open>poly p = fold_coeffs (\<lambda>a f x. a + x * f x) p (\<lambda>x. 0)\<close>
  
  sorry


lemma poly_0 [simp]: "poly 0 x = 0"
  
  sorry


lemma poly_pCons [simp]: "poly (pCons a p) x = a + x * poly p x"
  
  sorry


lemma poly_altdef: "poly p x = (\<Sum>i\<le>degree p. coeff p i * x ^ i)"
  for x :: "'a::{comm_semiring_0,semiring_1}"
  
  sorry


lemma poly_as_sum:
  fixes p :: "'a::comm_semiring_1 poly"
  shows "poly p x = (\<Sum>i\<le>degree p. x ^ i * coeff p i)"
  
  sorry


lemma poly_0_coeff_0: "poly p 0 = coeff p 0"
  
  sorry


lemma poly_zero:
  fixes p :: "'a :: comm_ring_1 poly"
  assumes x: "poly p x = 0" shows "p = 0 \<longleftrightarrow> degree p = 0"
  
  sorry



subsection \<open>Monomials\<close>

lift_definition monom :: "'a \<Rightarrow> nat \<Rightarrow> 'a::zero poly"
  is "\<lambda>a m n. if m = n then a else 0"
  
  sorry


lemma coeff_monom [simp]: "coeff (monom a m) n = (if m = n then a else 0)"
  
  sorry


lemma monom_0: "monom a 0 = [:a:]"
  
  sorry


lemma monom_Suc: "monom a (Suc n) = pCons 0 (monom a n)"
  
  sorry


lemma monom_eq_0 [simp]: "monom 0 n = 0"
  
  sorry


lemma monom_eq_0_iff [simp]: "monom a n = 0 \<longleftrightarrow> a = 0"
  
  sorry


lemma monom_eq_iff [simp]: "monom a n = monom b n \<longleftrightarrow> a = b"
  
  sorry


lemma degree_monom_le: "degree (monom a n) \<le> n"
  
  sorry


lemma degree_monom_eq: "a \<noteq> 0 \<Longrightarrow> degree (monom a n) = n"
  
  sorry


lemma coeffs_monom [code abstract]:
  "coeffs (monom a n) = (if a = 0 then [] else replicate n 0 @ [a])"
  
  sorry


lemma fold_coeffs_monom [simp]: "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (monom a n) = f 0 ^^ n \<circ> f a"
  
  sorry


lemma poly_monom: "poly (monom a n) x = a * x ^ n"
  for a x :: "'a::comm_semiring_1"
  
  sorry


lemma monom_eq_iff': "monom c n = monom d m \<longleftrightarrow>  c = d \<and> (c = 0 \<or> n = m)"
  
  sorry


lemma monom_eq_const_iff: "monom c n = [:d:] \<longleftrightarrow> c = d \<and> (c = 0 \<or> n = 0)"
  
  sorry



subsection \<open>Leading coefficient\<close>

abbreviation lead_coeff:: "'a::zero poly \<Rightarrow> 'a"
  where "lead_coeff p \<equiv> coeff p (degree p)"

lemma lead_coeff_pCons[simp]:
  "p \<noteq> 0 \<Longrightarrow> lead_coeff (pCons a p) = lead_coeff p"
  "p = 0 \<Longrightarrow> lead_coeff (pCons a p) = a"
  
  sorry


lemma lead_coeff_monom [simp]: "lead_coeff (monom c n) = c"
  
  sorry


lemma last_coeffs_eq_coeff_degree:
  "last (coeffs p) = lead_coeff p" if "p \<noteq> 0"
  
  sorry


lemma lead_coeff_list_def:
  "lead_coeff p = (if coeffs p=[] then 0 else last (coeffs p))"
  
  sorry


subsection \<open>Addition and subtraction\<close>

instantiation poly :: (comm_monoid_add) comm_monoid_add
begin

lift_definition plus_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p q n. coeff p n + coeff q n"

  sorry


lemma coeff_add [simp]: "coeff (p + q) n = coeff p n + coeff q n"
  
  sorry


instance

  sorry


end

instantiation poly :: (cancel_comm_monoid_add) cancel_comm_monoid_add
begin

lift_definition minus_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p q n. coeff p n - coeff q n"

  sorry


lemma coeff_diff [simp]: "coeff (p - q) n = coeff p n - coeff q n"
  
  sorry


instance

  sorry


end

instantiation poly :: (ab_group_add) ab_group_add
begin

lift_definition uminus_poly :: "'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p n. - coeff p n"

  sorry


lemma coeff_minus [simp]: "coeff (- p) n = - coeff p n"
  
  sorry


instance

  sorry


end

lemma add_pCons [simp]: "pCons a p + pCons b q = pCons (a + b) (p + q)"
  
  sorry


lemma minus_pCons [simp]: "- pCons a p = pCons (- a) (- p)"
  
  sorry


lemma diff_pCons [simp]: "pCons a p - pCons b q = pCons (a - b) (p - q)"
  
  sorry


lemma degree_add_le_max: "degree (p + q) \<le> max (degree p) (degree q)"
  
  sorry


lemma degree_add_le: "degree p \<le> n \<Longrightarrow> degree q \<le> n \<Longrightarrow> degree (p + q) \<le> n"
  
  sorry


lemma degree_add_less: "degree p < n \<Longrightarrow> degree q < n \<Longrightarrow> degree (p + q) < n"
  
  sorry


lemma degree_add_eq_right: assumes "degree p < degree q" shows "degree (p + q) = degree q"
  
  sorry


lemma degree_add_eq_left: "degree q < degree p \<Longrightarrow> degree (p + q) = degree p"
  
  sorry


lemma degree_minus [simp]: "degree (- p) = degree p"
  
  sorry


lemma lead_coeff_add_le: "degree p < degree q \<Longrightarrow> lead_coeff (p + q) = lead_coeff q"
  
  sorry


lemma lead_coeff_minus: "lead_coeff (- p) = - lead_coeff p"
  
  sorry


lemma degree_diff_le_max: "degree (p - q) \<le> max (degree p) (degree q)"
  for p q :: "'a::ab_group_add poly"
  
  sorry


lemma degree_diff_le: "degree p \<le> n \<Longrightarrow> degree q \<le> n \<Longrightarrow> degree (p - q) \<le> n"
  for p q :: "'a::ab_group_add poly"
  
  sorry


lemma degree_diff_less: "degree p < n \<Longrightarrow> degree q < n \<Longrightarrow> degree (p - q) < n"
  for p q :: "'a::ab_group_add poly"
  
  sorry


lemma add_monom: "monom a n + monom b n = monom (a + b) n"
  
  sorry


lemma diff_monom: "monom a n - monom b n = monom (a - b) n"
  
  sorry


lemma minus_monom: "- monom a n = monom (- a) n"
  
  sorry


lemma coeff_sum: "coeff (\<Sum>x\<in>A. p x) i = (\<Sum>x\<in>A. coeff (p x) i)"
  
  sorry


lemma monom_sum: "monom (\<Sum>x\<in>A. a x) n = (\<Sum>x\<in>A. monom (a x) n)"
  
  sorry


fun plus_coeffs :: "'a::comm_monoid_add list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "plus_coeffs xs [] = xs"
  | "plus_coeffs [] ys = ys"
  | "plus_coeffs (x # xs) (y # ys) = (x + y) ## plus_coeffs xs ys"

lemma coeffs_plus_eq_plus_coeffs [code abstract]:
  "coeffs (p + q) = plus_coeffs (coeffs p) (coeffs q)"
  
  sorry


lemma coeffs_uminus [code abstract]:
  "coeffs (- p) = map uminus (coeffs p)"
  
  sorry


lemma [code]: "p - q = p + - q"
  for p q :: "'a::ab_group_add poly"
  
  sorry


lemma poly_add [simp]: "poly (p + q) x = poly p x + poly q x"
  
  sorry


lemma poly_minus [simp]: "poly (- p) x = - poly p x"
  for x :: "'a::comm_ring"
  
  sorry


lemma poly_diff [simp]: "poly (p - q) x = poly p x - poly q x"
  for x :: "'a::comm_ring"
  
  sorry


lemma poly_sum: "poly (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. poly (p k) x)"
  
  sorry


lemma poly_sum_list: "poly (\<Sum>p\<leftarrow>ps. p) y = (\<Sum>p\<leftarrow>ps. poly p y)"
  
  sorry


lemma poly_sum_mset: "poly (\<Sum>x\<in>#A. p x) y = (\<Sum>x\<in>#A. poly (p x) y)"
  
  sorry


lemma degree_sum_le: "finite S \<Longrightarrow> (\<And>p. p \<in> S \<Longrightarrow> degree (f p) \<le> n) \<Longrightarrow> degree (sum f S) \<le> n"
  
  sorry


lemma degree_sum_less:
  assumes "\<And>x. x \<in> A \<Longrightarrow> degree (f x) < n" "n > 0"
  shows   "degree (sum f A) < n"
  
  sorry


lemma poly_as_sum_of_monoms':
  assumes "degree p \<le> n"
  shows "(\<Sum>i\<le>n. monom (coeff p i) i) = p"
  
  sorry


lemma poly_as_sum_of_monoms: "(\<Sum>i\<le>degree p. monom (coeff p i) i) = p"
  
  sorry


lemma Poly_snoc: "Poly (xs @ [x]) = Poly xs + monom x (length xs)"
  
  sorry



subsection \<open>Multiplication by a constant, polynomial multiplication and the unit polynomial\<close>

lift_definition smult :: "'a::comm_semiring_0 \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p n. a * coeff p n"

  sorry


lemma coeff_smult [simp]: "coeff (smult a p) n = a * coeff p n"
  
  sorry


lemma degree_smult_le: "degree (smult a p) \<le> degree p"
  
  sorry


lemma smult_smult [simp]: "smult a (smult b p) = smult (a * b) p"
  
  sorry


lemma smult_0_right [simp]: "smult a 0 = 0"
  
  sorry


lemma smult_0_left [simp]: "smult 0 p = 0"
  
  sorry


lemma smult_1_left [simp]: "smult (1::'a::comm_semiring_1) p = p"
  
  sorry


lemma smult_add_right: "smult a (p + q) = smult a p + smult a q"
  
  sorry


lemma smult_add_left: "smult (a + b) p = smult a p + smult b p"
  
  sorry


lemma smult_minus_right [simp]: "smult a (- p) = - smult a p"
  for a :: "'a::comm_ring"
  
  sorry


lemma smult_minus_left [simp]: "smult (- a) p = - smult a p"
  for a :: "'a::comm_ring"
  
  sorry


lemma smult_diff_right: "smult a (p - q) = smult a p - smult a q"
  for a :: "'a::comm_ring"
  
  sorry


lemma smult_diff_left: "smult (a - b) p = smult a p - smult b p"
  for a b :: "'a::comm_ring"
  
  sorry


lemmas smult_distribs =
  smult_add_left smult_add_right
  smult_diff_left smult_diff_right

lemma smult_pCons [simp]: "smult a (pCons b p) = pCons (a * b) (smult a p)"
  
  sorry


lemma smult_monom: "smult a (monom b n) = monom (a * b) n"
  
  sorry


lemma smult_Poly: "smult c (Poly xs) = Poly (map ((*) c) xs)"
  
  sorry


lemma degree_smult_eq [simp]: "degree (smult a p) = (if a = 0 then 0 else degree p)"
  for a :: "'a::{comm_semiring_0,semiring_no_zero_divisors}"
  
  sorry


lemma smult_eq_0_iff [simp]: "smult a p = 0 \<longleftrightarrow> a = 0 \<or> p = 0"
  for a :: "'a::{comm_semiring_0,semiring_no_zero_divisors}"
  
  sorry


lemma coeffs_smult [code abstract]:
  "coeffs (smult a p) = (if a = 0 then [] else map (Groups.times a) (coeffs p))"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  
  sorry


lemma smult_eq_iff:
  fixes b :: "'a :: field"
  assumes "b \<noteq> 0"
  shows "smult a p = smult b q \<longleftrightarrow> smult (a / b) p = q"
    (is "?lhs \<longleftrightarrow> ?rhs")
  
  sorry


lemma smult_cancel:
  fixes p::"'a::idom poly"
  assumes "c\<noteq>0" and smult: "smult c p = smult c q" 
  shows "p=q" 
  
  sorry

  
instantiation poly :: (comm_semiring_0) comm_semiring_0
begin

definition "p * q = fold_coeffs (\<lambda>a p. smult a q + pCons 0 p) p 0"

lemma mult_poly_0_left: "(0::'a poly) * q = 0"
  
  sorry


lemma mult_pCons_left [simp]: "pCons a p * q = smult a q + pCons 0 (p * q)"
  
  sorry


lemma mult_poly_0_right: "p * (0::'a poly) = 0"
  
  sorry


lemma mult_pCons_right [simp]: "p * pCons a q = smult a p + pCons 0 (p * q)"
  
  sorry


lemmas mult_poly_0 = mult_poly_0_left mult_poly_0_right

lemma mult_smult_left [simp]: "smult a p * q = smult a (p * q)"
  
  sorry


lemma mult_smult_right [simp]: "p * smult a q = smult a (p * q)"
  
  sorry


lemma mult_poly_add_left: "(p + q) * r = p * r + q * r"
  for p q r :: "'a poly"
  
  sorry


instance

  sorry


end

lemma coeff_mult_degree_sum:
  "coeff (p * q) (degree p + degree q) = coeff p (degree p) * coeff q (degree q)"
  
  sorry


instance poly :: ("{comm_semiring_0,semiring_no_zero_divisors}") semiring_no_zero_divisors

  sorry


instance poly :: (comm_semiring_0_cancel) comm_semiring_0_cancel 
  sorry


lemma coeff_mult: "coeff (p * q) n = (\<Sum>i\<le>n. coeff p i * coeff q (n-i))"
  
  sorry


lemma coeff_mult_0: "coeff (p * q) 0 = coeff p 0 * coeff q 0"
  
  sorry


lemma degree_mult_le: "degree (p * q) \<le> degree p + degree q"
  
  sorry


lemma mult_monom: "monom a m * monom b n = monom (a * b) (m + n)"
  
  sorry


instantiation poly :: (comm_semiring_1) comm_semiring_1
begin

lift_definition one_poly :: "'a poly"
  is "\<lambda>n. of_bool (n = 0)"
  
  sorry


lemma coeff_1 [simp]:
  "coeff 1 n = of_bool (n = 0)"
  
  sorry


lemma one_pCons:
  "1 = [:1:]"
  
  sorry


lemma pCons_one:
  "[:1:] = 1"
  
  sorry


instance
  
  sorry


end

lemma poly_1 [simp]:
  "poly 1 x = 1"
  
  sorry


lemma one_poly_eq_simps [simp]:
  "1 = [:1:] \<longleftrightarrow> True"
  "[:1:] = 1 \<longleftrightarrow> True"
  
  sorry


lemma degree_1 [simp]:
  "degree 1 = 0"
  
  sorry


lemma coeffs_1_eq [simp, code abstract]:
  "coeffs 1 = [1]"
  
  sorry


lemma smult_one [simp]:
  "smult c 1 = [:c:]"
  
  sorry


lemma smult_sum: "smult (\<Sum>i \<in> S. f i) p = (\<Sum>i \<in> S. smult (f i) p)"
  
  sorry


lemma smult_power: "(smult a p) ^ n = smult (a ^ n) (p ^ n)"
  
  sorry


lemma monom_eq_1 [simp]:
  "monom 1 0 = 1"
  
  sorry


lemma monom_eq_1_iff:
  "monom c n = 1 \<longleftrightarrow> c = 1 \<and> n = 0"
  
  sorry


lemma monom_altdef:
  "monom c n = smult c ([:0, 1:] ^ n)"
  
  sorry


lemma degree_sum_list_le: "(\<And> p . p \<in> set ps \<Longrightarrow> degree p \<le> n)
  \<Longrightarrow> degree (sum_list ps) \<le> n"
  
  sorry


lemma degree_prod_list_le: "degree (prod_list ps) \<le> sum_list (map degree ps)"
  
  sorry


instance poly :: ("{comm_semiring_1,semiring_1_no_zero_divisors}") semiring_1_no_zero_divisors 
  sorry

instance poly :: (comm_ring) comm_ring 
  sorry

instance poly :: (comm_ring_1) comm_ring_1 
  sorry

instance poly :: (comm_ring_1) comm_semiring_1_cancel 
  sorry


lemma prod_smult: "(\<Prod>x\<in>A. smult (c x) (p x)) = smult (prod c A) (prod p A)"
  
  sorry


lemma degree_power_le: "degree (p ^ n) \<le> degree p * n"
  
  sorry


lemma coeff_0_power: "coeff (p ^ n) 0 = coeff p 0 ^ n"
  
  sorry


lemma poly_smult [simp]: "poly (smult a p) x = a * poly p x"
  
  sorry


lemma poly_mult [simp]: "poly (p * q) x = poly p x * poly q x"
  
  sorry


lemma poly_power [simp]: "poly (p ^ n) x = poly p x ^ n"
  for p :: "'a::comm_semiring_1 poly"
  
  sorry


lemma poly_prod: "poly (\<Prod>k\<in>A. p k) x = (\<Prod>k\<in>A. poly (p k) x)"
  
  sorry


lemma poly_prod_list: "poly (\<Prod>p\<leftarrow>ps. p) y = (\<Prod>p\<leftarrow>ps. poly p y)"
  
  sorry


lemma poly_prod_mset: "poly (\<Prod>x\<in>#A. p x) y = (\<Prod>x\<in>#A. poly (p x) y)"
  
  sorry


lemma poly_const_pow: "[: c :] ^ n = [: c ^ n :]"
  
  sorry


lemma monom_power: "monom c n ^ k = monom (c ^ k) (n * k)"
  
  sorry


lemma degree_prod_sum_le: "finite S \<Longrightarrow> degree (prod f S) \<le> sum (degree \<circ> f) S"
  
  sorry


lemma coeff_0_prod_list: "coeff (prod_list xs) 0 = prod_list (map (\<lambda>p. coeff p 0) xs)"
  
  sorry


lemma coeff_monom_mult: "coeff (monom c n * p) k = (if k < n then 0 else c * coeff p (k - n))"
  
  sorry


lemma coeff_monom_Suc: "coeff (monom a (Suc d) * p) (Suc i) = coeff (monom a d * p) i"
  
  sorry


lemma monom_1_dvd_iff': "monom 1 n dvd p \<longleftrightarrow> (\<forall>k<n. coeff p k = 0)"
  
  sorry


lemma coeff_sum_monom:
  assumes n: "n \<le> d"
  shows "coeff (\<Sum>i\<le>d. monom (f i) i) n = f n" (is "?l = _")
  
  sorry


subsection \<open>Mapping polynomials\<close>

definition map_poly :: "('a :: zero \<Rightarrow> 'b :: zero) \<Rightarrow> 'a poly \<Rightarrow> 'b poly"
  where "map_poly f p = Poly (map f (coeffs p))"

lemma map_poly_0 [simp]: "map_poly f 0 = 0"
  
  sorry


lemma map_poly_1: "map_poly f 1 = [:f 1:]"
  
  sorry


lemma map_poly_1' [simp]: "f 1 = 1 \<Longrightarrow> map_poly f 1 = 1"
  
  sorry


lemma coeff_map_poly:
  assumes "f 0 = 0"
  shows "coeff (map_poly f p) n = f (coeff p n)"
  
  sorry


lemma lead_coeff_map_poly_nz:
  assumes "f (lead_coeff p) \<noteq> 0" "f 0 = 0"
  shows "lead_coeff (map_poly f p) = f (lead_coeff p)"
  
  sorry

        
lemma coeffs_map_poly [code abstract]:
  "coeffs (map_poly f p) = strip_while ((=) 0) (map f (coeffs p))"
  
  sorry


lemma coeffs_map_poly':
  assumes "\<And>x. x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "coeffs (map_poly f p) = map f (coeffs p)"
  
  sorry


lemma set_coeffs_map_poly:
  "(\<And>x. f x = 0 \<longleftrightarrow> x = 0) \<Longrightarrow> set (coeffs (map_poly f p)) = f ` set (coeffs p)"
  
  sorry


lemma degree_map_poly:
  assumes "\<And>x. x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "degree (map_poly f p) = degree p"
  
  sorry


lemma map_poly_eq_0_iff:
  assumes "f 0 = 0" "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "map_poly f p = 0 \<longleftrightarrow> p = 0"
  
  sorry


lemma map_poly_smult:
  assumes "f 0 = 0""\<And>c x. f (c * x) = f c * f x"
  shows "map_poly f (smult c p) = smult (f c) (map_poly f p)"
  
  sorry


lemma map_poly_pCons:
  assumes "f 0 = 0"
  shows "map_poly f (pCons c p) = pCons (f c) (map_poly f p)"
  
  sorry


lemma map_poly_map_poly:
  assumes "f 0 = 0" "g 0 = 0"
  shows "map_poly f (map_poly g p) = map_poly (f \<circ> g) p"
  
  sorry


lemma map_poly_id [simp]: "map_poly id p = p"
  
  sorry


lemma map_poly_id' [simp]: "map_poly (\<lambda>x. x) p = p"
  
  sorry


lemma map_poly_cong:
  assumes "(\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = g x)"
  shows "map_poly f p = map_poly g p"
  
  sorry


lemma map_poly_monom: "f 0 = 0 \<Longrightarrow> map_poly f (monom c n) = monom (f c) n"
  
  sorry


lemma map_poly_idI:
  assumes "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = x"
  shows "map_poly f p = p"
  
  sorry


lemma map_poly_idI':
  assumes "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = x"
  shows "p = map_poly f p"
  
  sorry


lemma smult_conv_map_poly: "smult c p = map_poly (\<lambda>x. c * x) p"
  
  sorry


lemma poly_cnj: "cnj (poly p z) = poly (map_poly cnj p) (cnj z)"
  
  sorry


lemma monom_pCons_0_monom:
  "monom (pCons 0 (monom a n)) d = map_poly (pCons 0) (monom (monom a n) d)"
  
  sorry


lemma pCons_0_add: "pCons 0 (p + q) = pCons 0 p + pCons 0 q" 
  
  sorry


lemma sum_pCons_0_commute:
  "sum (\<lambda>i. pCons 0 (f i)) S = pCons 0 (sum f S)"
  
  sorry


lemma pCons_0_as_mult:
  fixes p:: "'a :: comm_semiring_1 poly"
  shows "pCons 0 p = [:0,1:] * p" 
  
  sorry


lemma poly_cnj_real:
  assumes "\<And>n. poly.coeff p n \<in> \<real>"
  shows   "cnj (poly p z) = poly p (cnj z)"
  
  sorry


lemma real_poly_cnj_root_iff:
  assumes "\<And>n. poly.coeff p n \<in> \<real>"
  shows   "poly p (cnj z) = 0 \<longleftrightarrow> poly p z = 0"
  
  sorry


lemma sum_to_poly: "(\<Sum>x\<in>A. [:f x:]) = [:\<Sum>x\<in>A. f x:]"
  
  sorry


lemma diff_to_poly: "[:c:] - [:d:] = [:c - d:]"
  
  sorry


lemma mult_to_poly: "[:c:] * [:d:] = [:c * d:]"
  
  sorry


lemma prod_to_poly: "(\<Prod>x\<in>A. [:f x:]) = [:\<Prod>x\<in>A. f x:]"
  
  sorry


lemma poly_map_poly_cnj [simp]: "poly (map_poly cnj p) x = cnj (poly p (cnj x))"
  
  sorry


lemma map_poly_degree_eq:
  assumes "f (lead_coeff p) \<noteq> 0"
  shows "degree (map_poly f p) = degree p"  
  
  sorry

  
lemma map_poly_degree_less:
  assumes "f (lead_coeff p) =0" "degree p\<noteq>0"
  shows "degree (map_poly f p) < degree p" 
  
  sorry

  
lemma map_poly_degree_leq:
  shows "degree (map_poly f p) \<le> degree p"
  
  sorry


subsection \<open>Conversions\<close>

lemma of_nat_poly: "of_nat n = [:of_nat n:]"
  
  sorry


lemma of_nat_monom: "of_nat n = monom (of_nat n) 0"
  
  sorry


lemma degree_of_nat [simp]: "degree (of_nat n) = 0"
  
  sorry


lemma lead_coeff_of_nat [simp]: "lead_coeff (of_nat n) = of_nat n"
  
  sorry


lemma of_int_poly: "of_int k = [:of_int k:]"
  
  sorry


lemma of_int_monom: "of_int k = monom (of_int k) 0"
  
  sorry


lemma degree_of_int [simp]: "degree (of_int k) = 0"
  
  sorry


lemma lead_coeff_of_int [simp]: "lead_coeff (of_int k) = of_int k"
  
  sorry


lemma poly_of_nat [simp]: "poly (of_nat n) x = of_nat n"
  
  sorry


lemma poly_of_int [simp]: "poly (of_int n) x = of_int n"
  
  sorry


lemma poly_numeral [simp]: "poly (numeral n) x = numeral n"
  
  sorry


lemma numeral_poly: "numeral n = [:numeral n:]"
  
  sorry


lemma numeral_monom:
  "numeral n = monom (numeral n) 0"
  
  sorry


lemma degree_numeral [simp]:
  "degree (numeral n) = 0"
  
  sorry


lemma lead_coeff_numeral [simp]:
  "lead_coeff (numeral n) = numeral n"
  
  sorry


lemma coeff_linear_poly_power:
  fixes c :: "'a :: semiring_1"
  assumes "i \<le> n"
  shows   "coeff ([:a, b:] ^ n) i = of_nat (n choose i) * b ^ i * a ^ (n - i)"
  
  sorry




subsection \<open>Lemmas about divisibility\<close>

lemma dvd_smult:
  assumes "p dvd q"
  shows "p dvd smult a q"
  
  sorry


lemma dvd_smult_cancel: "p dvd smult a q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> p dvd q"
  for a :: "'a::field"
  
  sorry


lemma dvd_smult_iff: "a \<noteq> 0 \<Longrightarrow> p dvd smult a q \<longleftrightarrow> p dvd q"
  for a :: "'a::field"
  
  sorry


lemma smult_dvd_cancel:
  assumes "smult a p dvd q"
  shows "p dvd q"
  
  sorry


lemma smult_dvd: "p dvd q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> smult a p dvd q"
  for a :: "'a::field"
  
  sorry


lemma smult_dvd_iff: "smult a p dvd q \<longleftrightarrow> (if a = 0 then q = 0 else p dvd q)"
  for a :: "'a::field"
  
  sorry


lemma is_unit_smult_iff: "smult c p dvd 1 \<longleftrightarrow> c dvd 1 \<and> p dvd 1"
  
  sorry



subsection \<open>Polynomials form an integral domain\<close>

instance poly :: (idom) idom 
  sorry


instance poly :: ("{ring_char_0, comm_ring_1}") ring_char_0
  
  sorry


lemma semiring_char_poly [simp]: "CHAR('a :: comm_semiring_1 poly) = CHAR('a)"
  
  sorry


instance poly :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  
  sorry

instance poly :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  
  sorry

instance poly :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  
  sorry

instance poly :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  
  sorry


lemma linear_poly_root: 
  "(a :: 'a :: comm_ring_1) \<in> set as \<Longrightarrow> poly (\<Prod> a \<leftarrow> as. [: - a, 1:]) a = 0"
  
  sorry


lemma poly_sum_list_eq: "poly (sum_list ps) x = sum_list (map (\<lambda> p. poly p x) ps)"
  
  sorry


lemma poly_prod_list_eq: "poly (prod_list ps) x = prod_list (map (\<lambda> p. poly p x) ps)"
  
  sorry


lemma sum_list_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list xs = 0"
  
  sorry


lemma prod_list_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 1) \<Longrightarrow> prod_list xs = 1"
  
  sorry


lemma (in comm_monoid_mult) prod_list_map_remove1:
  "x \<in> set xs \<Longrightarrow> prod_list (map f xs) = f x * prod_list (map f (remove1 x xs))"
  
  sorry


lemma poly_prod_0: "finite ps \<Longrightarrow> poly (prod f ps) x = (0 :: 'a :: field) \<longleftrightarrow> (\<exists> p \<in> ps. poly (f p) x = 0)"
  
  sorry


lemma degree_mult_eq: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> degree (p * q) = degree p + degree q"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  
  sorry


lemma degree_prod_sum_eq:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow>
     degree (prod f A :: 'a :: idom poly) = (\<Sum>x\<in>A. degree (f x))"
  
  sorry


lemma dvd_imp_degree:
  \<open>degree x \<le> degree y\<close> if \<open>x dvd y\<close> \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
    for x y :: \<open>'a::{comm_semiring_1,semiring_no_zero_divisors} poly\<close>
  
  sorry


lemma degree_prod_eq_sum_degree:
  fixes A :: "'a set"
  and f :: "'a \<Rightarrow> 'b::idom poly"
  assumes f0: "\<forall>i\<in>A. f i \<noteq> 0"
  shows "degree (\<Prod>i\<in>A. (f i)) = (\<Sum>i\<in>A. degree (f i))"
  
  sorry


lemma degree_mult_eq_0:
  "degree (p * q) = 0 \<longleftrightarrow> p = 0 \<or> q = 0 \<or> (p \<noteq> 0 \<and> q \<noteq> 0 \<and> degree p = 0 \<and> degree q = 0)"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  
  sorry


lemma degree_power_eq: "p \<noteq> 0 \<Longrightarrow> degree ((p :: 'a :: idom poly) ^ n) = n * degree p"
  
  sorry


lemma degree_mult_right_le:
  fixes p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  assumes "q \<noteq> 0"
  shows "degree p \<le> degree (p * q)"
  
  sorry


lemma coeff_degree_mult: "coeff (p * q) (degree (p * q)) = coeff q (degree q) * coeff p (degree p)"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  
  sorry


lemma dvd_imp_degree_le: "p dvd q \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> degree p \<le> degree q"
  for p q :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  
  sorry


lemma divides_degree:
  fixes p q :: "'a ::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "p dvd q"
  shows "degree p \<le> degree q \<or> q = 0"
  
  sorry


lemma const_poly_dvd_iff:
  fixes c :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  shows "[:c:] dvd p \<longleftrightarrow> (\<forall>n. c dvd coeff p n)"
  
  sorry


lemma const_poly_dvd_const_poly_iff [simp]: "[:a:] dvd [:b:] \<longleftrightarrow> a dvd b"
  for a b :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  
  sorry


lemma lead_coeff_mult: "lead_coeff (p * q) = lead_coeff p * lead_coeff q"
  for p q :: "'a::{comm_semiring_0, semiring_no_zero_divisors} poly"
  
  sorry


lemma lead_coeff_prod: "lead_coeff (prod f A) = (\<Prod>x\<in>A. lead_coeff (f x))"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1, semiring_no_zero_divisors} poly"
  
  sorry


lemma lead_coeff_smult: "lead_coeff (smult c p) = c * lead_coeff p"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  
  sorry


lemma lead_coeff_1 [simp]: "lead_coeff 1 = 1"
  
  sorry


lemma lead_coeff_power: "lead_coeff (p ^ n) = lead_coeff p ^ n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  
  sorry



subsection \<open>Polynomials form an ordered integral domain\<close>

definition pos_poly :: "'a::linordered_semidom poly \<Rightarrow> bool"
  where "pos_poly p \<longleftrightarrow> 0 < coeff p (degree p)"

lemma pos_poly_pCons: "pos_poly (pCons a p) \<longleftrightarrow> pos_poly p \<or> (p = 0 \<and> 0 < a)"
  
  sorry


lemma not_pos_poly_0 [simp]: "\<not> pos_poly 0"
  
  sorry


lemma pos_poly_add: "pos_poly p \<Longrightarrow> pos_poly q \<Longrightarrow> pos_poly (p + q)"
  
  sorry


lemma pos_poly_mult: "pos_poly p \<Longrightarrow> pos_poly q \<Longrightarrow> pos_poly (p * q)"
  
  sorry


lemma pos_poly_total: "p = 0 \<or> pos_poly p \<or> pos_poly (- p)"
  for p :: "'a::linordered_idom poly"
  
  sorry


lemma pos_poly_coeffs [code]: "pos_poly p \<longleftrightarrow> (let as = coeffs p in as \<noteq> [] \<and> last as > 0)"
  (is "?lhs \<longleftrightarrow> ?rhs")
  
  sorry


instantiation poly :: (linordered_idom) linordered_idom
begin

definition "x < y \<longleftrightarrow> pos_poly (y - x)"

definition "x \<le> y \<longleftrightarrow> x = y \<or> pos_poly (y - x)"

definition "\<bar>x::'a poly\<bar> = (if x < 0 then - x else x)"

definition "sgn (x::'a poly) = (if x = 0 then 0 else if 0 < x then 1 else - 1)"

instance

  sorry


end

text \<open>TODO: Simplification rules for comparisons\<close>


subsection \<open>Synthetic division and polynomial roots\<close>

subsubsection \<open>Synthetic division\<close>

text \<open>Synthetic division is simply division by the linear polynomial \<^term>\<open>x - c\<close>.\<close>

definition synthetic_divmod :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly \<times> 'a"
  where "synthetic_divmod p c = fold_coeffs (\<lambda>a (q, r). (pCons r q, a + c * r)) p (0, 0)"

definition synthetic_div :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly"
  where "synthetic_div p c = fst (synthetic_divmod p c)"

lemma synthetic_divmod_0 [simp]: "synthetic_divmod 0 c = (0, 0)"
  
  sorry


lemma synthetic_divmod_pCons [simp]:
  "synthetic_divmod (pCons a p) c = (\<lambda>(q, r). (pCons r q, a + c * r)) (synthetic_divmod p c)"
  
  sorry


lemma synthetic_div_0 [simp]: "synthetic_div 0 c = 0"
  
  sorry


lemma synthetic_div_unique_lemma: "smult c p = pCons a p \<Longrightarrow> p = 0"
  
  sorry


lemma snd_synthetic_divmod: "snd (synthetic_divmod p c) = poly p c"
  
  sorry


lemma synthetic_div_pCons [simp]:
  "synthetic_div (pCons a p) c = pCons (poly p c) (synthetic_div p c)"
  
  sorry


lemma synthetic_div_eq_0_iff: "synthetic_div p c = 0 \<longleftrightarrow> degree p = 0"
  
  sorry


lemma degree_synthetic_div: "degree (synthetic_div p c) = degree p - 1"
  
  sorry


lemma synthetic_div_correct:
  "p + smult c (synthetic_div p c) = pCons (poly p c) (synthetic_div p c)"
  
  sorry


lemma synthetic_div_unique: "p + smult c q = pCons r q \<Longrightarrow> r = poly p c \<and> q = synthetic_div p c"
  
  sorry


lemma synthetic_div_correct': "[:-c, 1:] * synthetic_div p c + [:poly p c:] = p"
  for c :: "'a::comm_ring_1"
  
  sorry



subsubsection \<open>Polynomial roots\<close>

lemma poly_eq_0_iff_dvd: "poly p c = 0 \<longleftrightarrow> [:- c, 1:] dvd p"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for c :: "'a::comm_ring_1"
  
  sorry


lemma dvd_iff_poly_eq_0: "[:c, 1:] dvd p \<longleftrightarrow> poly p (- c) = 0"
  for c :: "'a::comm_ring_1"
  
  sorry


lemma poly_roots_finite: "p \<noteq> 0 \<Longrightarrow> finite {x. poly p x = 0}"
  for p :: "'a::{comm_ring_1,ring_no_zero_divisors} poly"
  
  sorry


lemma poly_eq_poly_eq_iff: "poly p = poly q \<longleftrightarrow> p = q"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for p q :: "'a::{comm_ring_1,ring_no_zero_divisors,ring_char_0} poly"
  
  sorry


text \<open>A nice extension rule for polynomials.\<close>
lemma poly_ext:
  fixes p q :: "'a :: {ring_char_0, idom} poly"
  assumes "\<And>x. poly p x = poly q x" shows "p = q"
  
  sorry


text \<open>Copied from non-negative variants.\<close>
lemma coeff_linear_power_neg[simp]:
  fixes a :: "'a::comm_ring_1"
  shows "coeff ([:a, -1:] ^ n) n = (-1)^n"
  
  sorry


lemma degree_linear_power_neg[simp]:
  fixes a :: "'a::{idom,comm_ring_1}"
  shows "degree ([:a, -1:] ^ n) = n"
  
  sorry


lemma poly_all_0_iff_0: "(\<forall>x. poly p x = 0) \<longleftrightarrow> p = 0"
  for p :: "'a::{ring_char_0,comm_ring_1,ring_no_zero_divisors} poly"
  
  sorry


lemma poly_roots_degree:
  fixes p :: "'a::{comm_ring_1,ring_no_zero_divisors} poly"
  assumes "p \<noteq> 0"
  shows   "card {x. poly p x = 0} \<le> degree p"
  
  sorry


lemma poly_eqI_degree:
  fixes p q :: "'a :: {comm_ring_1, ring_no_zero_divisors} poly"
  assumes "\<And>x. x \<in> A \<Longrightarrow> poly p x = poly q x"
  assumes "card A > degree p" "card A > degree q"
  shows   "p = q"
  
  sorry


lemma poly_eqI_degree_lead_coeff:
  fixes p q :: "'a :: {comm_ring_1, ring_no_zero_divisors} poly"
  assumes "poly.coeff p n = poly.coeff q n" "card A \<ge> n" "degree p \<le> n" "degree q \<le> n"
  assumes "\<And>z. z \<in> A \<Longrightarrow> poly p z = poly q z"
  shows   "p = q"
  
  sorry



subsubsection \<open>Order of polynomial roots\<close>

definition order :: "'a::idom \<Rightarrow> 'a poly \<Rightarrow> nat"
  where "order a p = (LEAST n. \<not> [:-a, 1:] ^ Suc n dvd p)"

lemma coeff_linear_power: "coeff ([:a, 1:] ^ n) n = 1"
  for a :: "'a::comm_semiring_1"
  
  sorry


lemma degree_linear_power: "degree ([:a, 1:] ^ n) = n"
  for a :: "'a::comm_semiring_1"
  
  sorry


lemma order_1: "[:-a, 1:] ^ order a p dvd p"
  
  sorry


lemma order_2:
  assumes "p \<noteq> 0"
  shows "\<not> [:-a, 1:] ^ Suc (order a p) dvd p"
  
  sorry


lemma order: "p \<noteq> 0 \<Longrightarrow> [:-a, 1:] ^ order a p dvd p \<and> \<not> [:-a, 1:] ^ Suc (order a p) dvd p"
  
  sorry


lemma order_degree:
  assumes p: "p \<noteq> 0"
  shows "order a p \<le> degree p"
  
  sorry


lemma order_root: "poly p a = 0 \<longleftrightarrow> p = 0 \<or> order a p \<noteq> 0" (is "?lhs = ?rhs")
  
  sorry


lemma order_0I: "poly p a \<noteq> 0 \<Longrightarrow> order a p = 0"
  
  sorry


lemma order_unique_lemma:
  fixes p :: "'a::idom poly"
  assumes "[:-a, 1:] ^ n dvd p" "\<not> [:-a, 1:] ^ Suc n dvd p"
  shows "order a p = n"
  
  sorry


lemma order_mult:
  assumes "p * q \<noteq> 0" shows "order a (p * q) = order a p + order a q"
  
  sorry



lemma order_smult:
  assumes "c \<noteq> 0"
  shows "order x (smult c p) = order x p"
  
  sorry


lemma order_gt_0_iff: "p \<noteq> 0 \<Longrightarrow> order x p > 0 \<longleftrightarrow> poly p x = 0"
  
  sorry


lemma order_eq_0_iff: "p \<noteq> 0 \<Longrightarrow> order x p = 0 \<longleftrightarrow> poly p x \<noteq> 0"
  
  sorry


text \<open>Next three lemmas contributed by Wenda Li\<close>
lemma order_1_eq_0 [simp]:"order x 1 = 0"
  
  sorry


lemma order_uminus[simp]: "order x (-p) = order x p"
  
  sorry


lemma order_power_n_n: "order a ([:-a,1:]^n)=n"
  
  sorry


lemma order_linear[simp]: "order x [:-y, 1:] = (if x=y then 1 else 0)"
  
  sorry


lemma order_0_monom [simp]: "c \<noteq> 0 \<Longrightarrow> order 0 (monom c n) = n"
  
  sorry


lemma dvd_imp_order_le: "q \<noteq> 0 \<Longrightarrow> p dvd q \<Longrightarrow> Polynomial.order a p \<le> Polynomial.order a q"
  
  sorry


text \<open>Now justify the standard squarefree decomposition, i.e. \<open>f / gcd f f'\<close>.\<close>

lemma order_divides: "[:-a, 1:] ^ n dvd p \<longleftrightarrow> p = 0 \<or> n \<le> order a p"
  
  sorry



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma order_decomp:
  assumes "p \<noteq> 0"
  shows "\<exists>q. p = [:- a, 1:] ^ order a p * q \<and> \<not> [:- a, 1:] dvd q"
  
  