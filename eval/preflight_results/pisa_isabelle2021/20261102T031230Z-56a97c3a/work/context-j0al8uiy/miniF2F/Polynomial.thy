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



declare [[quick_and_dirty = false, smt_oracle = false]]
lemma poly_diff [simp]: "poly (p - q) x = poly p x - poly q x"
  for x :: "'a::comm_ring"
  
  