(* Author: Lei Yu, University of Cambridge
   Author: Fabian Hellauer
           Fabian Immler
*)

section \<open>Proofs of Properties about Floating Point Arithmetic\<close>

theory IEEE_Properties
imports IEEE
begin

subsection \<open>Theorems derived from definitions\<close>

lemma valof_eq:
  "valof x =
    (if exponent x = 0
       then (- 1) ^ sign x * (2 / 2 ^ bias TYPE(('a, 'b) float)) *
            (real (fraction x) / 2 ^ LENGTH('b))
       else (- 1) ^ sign x * (2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float)) *
            (1 + real (fraction x) / 2 ^ LENGTH('b)))"
  for x::"('a, 'b) float"
sorry

lemma exponent_le [simp]:
  \<open>exponent a \<le> mask LENGTH('a)\<close> for a :: \<open>('a, _) float\<close>
sorry

lemma exponent_not_less [simp]:
  \<open>\<not> mask LENGTH('a) < IEEE.exponent a\<close> for a :: \<open>('a, _) float\<close>
sorry

lemma infinity_simps:
  "sign (plus_infinity::('e, 'f)float) = 0"
  "sign (minus_infinity::('e, 'f)float) = 1"
  "exponent (plus_infinity::('e, 'f)float) = emax TYPE(('e, 'f)float)"
  "exponent (minus_infinity::('e, 'f)float) = emax TYPE(('e, 'f)float)"
  "fraction (plus_infinity::('e, 'f)float) = 0"
  "fraction (minus_infinity::('e, 'f)float) = 0"
sorry

lemma zero_simps:
  "sign (0::('e, 'f)float) = 0"
  "sign (- 0::('e, 'f)float) = 1"
  "exponent (0::('e, 'f)float) = 0"
  "exponent (- 0::('e, 'f)float) = 0"
  "fraction (0::('e, 'f)float) = 0"
  "fraction (- 0::('e, 'f)float) = 0"
sorry

lemma emax_eq: "emax x = 2 ^ LENGTH('e) - 1"
  for x::"('e, 'f)float itself"
sorry

lemma topfloat_simps:
  "sign (topfloat::('e, 'f)float) = 0"
  "exponent (topfloat::('e, 'f)float) = emax TYPE(('e, 'f)float) - 1"
  "fraction (topfloat::('e, 'f)float) = 2 ^ (fracwidth TYPE(('e, 'f)float)) - 1"
  and bottomfloat_simps:
  "sign (bottomfloat::('e, 'f)float) = 1"
  "exponent (bottomfloat::('e, 'f)float) = emax TYPE(('e, 'f)float) - 1"
  "fraction (bottomfloat::('e, 'f)float) = 2 ^ (fracwidth TYPE(('e, 'f)float)) - 1"
sorry

lemmas float_defs =
  is_finite_def is_infinity_def is_zero_def is_nan_def
  is_normal_def is_denormal_def valof_eq
  less_eq_float_def less_float_def
  flt_def fgt_def fle_def fge_def feq_def
  fcompare_def
  infinity_simps
  zero_simps
  topfloat_simps
  bottomfloat_simps
  float_eq_def

lemma float_cases: "is_nan a \<or> is_infinity a \<or> is_normal a \<or> is_denormal a \<or> is_zero a"
sorry

lemma float_cases_finite: "is_nan a \<or> is_infinity a \<or> is_finite a"
sorry

lemma float_zero1 [simp]: "is_zero 0"
sorry

lemma float_zero2 [simp]: "is_zero (- x) \<longleftrightarrow> is_zero x"
sorry

lemma emax_pos [simp]: "0 < emax x" "emax x \<noteq> 0"
sorry

text \<open>The types of floating-point numbers are mutually distinct.\<close>
lemma float_distinct:
  "\<not> (is_nan a \<and> is_infinity a)"
  "\<not> (is_nan a \<and> is_normal a)"
  "\<not> (is_nan a \<and> is_denormal a)"
  "\<not> (is_nan a \<and> is_zero a)"
  "\<not> (is_infinity a \<and> is_normal a)"
  "\<not> (is_infinity a \<and> is_denormal a)"
  "\<not> (is_infinity a \<and> is_zero a)"
  "\<not> (is_normal a \<and> is_denormal a)"
  "\<not> (is_denormal a \<and> is_zero a)"
sorry

lemma denormal_imp_not_zero: "is_denormal f \<Longrightarrow> \<not>is_zero f"
sorry

lemma normal_imp_not_zero: "is_normal f \<Longrightarrow> \<not>is_zero f"
sorry

lemma normal_imp_not_denormal: "is_normal f \<Longrightarrow> \<not>is_denormal f"
sorry

lemma denormal_zero [simp]: "\<not>is_denormal 0" "\<not>is_denormal minus_zero"
sorry

lemma normal_zero [simp]: "\<not>is_normal 0" "\<not>is_normal minus_zero"
sorry

lemma float_distinct_finite: "\<not> (is_nan a \<and> is_finite a)" "\<not>(is_infinity a \<and> is_finite a)"
sorry

lemma finite_infinity: "is_finite a \<Longrightarrow> \<not> is_infinity a"
sorry

lemma finite_nan: "is_finite a \<Longrightarrow> \<not> is_nan a"
sorry
text \<open>For every real number, the floating-point numbers closest to it always exists.\<close>
lemma is_closest_exists:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
    and s :: "('e, 'f)float set"
  assumes finite: "finite s"
    and non_empty: "s \<noteq> {}"
  shows "\<exists>a. is_closest v s x a"
sorry

lemma closest_is_everything:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
    and s :: "('e, 'f)float set"
  assumes finite: "finite s"
    and non_empty: "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x) \<and>
    ((\<exists>b. is_closest v s x b \<and> p b) \<longrightarrow> p (closest v p s x))"
sorry

lemma closest_in_set:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
  assumes "finite s" and "s \<noteq> {}"
  shows "closest v p s x \<in> s"
sorry

lemma closest_is_closest_finite:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
  assumes "finite s" and "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x)"
sorry

instance float::(len, len) finite proof qed (transfer, simp)

lemma is_finite_nonempty: "{a. is_finite a} \<noteq> {}"
sorry

lemma closest_is_closest:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
  assumes "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x)"
sorry

subsection \<open>Properties about ordering and bounding\<close>

text \<open>Lifting of non-exceptional comparisons.\<close>
lemma float_lt [simp]:
  assumes "is_finite a" "is_finite b"
  shows "a < b \<longleftrightarrow> valof a < valof b"
sorry

lemma float_eq [simp]:
  assumes "is_finite a" "is_finite b"
  shows "a \<doteq> b \<longleftrightarrow> valof a = valof b"
sorry

lemma float_le [simp]:
  assumes "is_finite a" "is_finite b"
  shows "a \<le> b \<longleftrightarrow> valof a \<le> valof b"
sorry


text \<open>Reflexivity of equality for non-NaNs.\<close>
lemma float_eq_refl [simp]: "a \<doteq> a \<longleftrightarrow> \<not> is_nan a"
sorry

text \<open>Properties about ordering.\<close>
lemma float_lt_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a < b \<Longrightarrow> b < c \<Longrightarrow> a < c"
sorry

lemma float_le_less_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b < c \<Longrightarrow> a < c"
sorry

lemma float_le_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
sorry

lemma float_le_neg: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> \<not> a < b \<longleftrightarrow> b \<le> a"
sorry

text \<open>Properties about bounding.\<close>

lemma float_le_plus_infinity [simp]: "\<not> is_nan a \<Longrightarrow> a \<le> plus_infinity"
sorry

lemma minus_infinity_le_float [simp]: "\<not> is_nan a \<Longrightarrow> minus_infinity \<le> a"
sorry

lemma zero_le_topfloat [simp]: "0 \<le> topfloat" "- 0 \<le> topfloat"
sorry

lemma LENGTH_contr:
  "Suc 0 < LENGTH('e) \<Longrightarrow> 2 ^ LENGTH('e::len) \<le> Suc (Suc 0) \<Longrightarrow> False"
sorry

lemma valof_topfloat: "valof (topfloat::('e, 'f)float) = largest TYPE(('e, 'f)float)"
  if "LENGTH('e) > 1"
sorry

lemma float_frac_le: "fraction a \<le> 2^LENGTH('f) - 1"
  for a::"('e, 'f)float"
sorry

lemma float_exp_le: "is_finite a \<Longrightarrow> exponent a \<le> emax TYPE(('e, 'f)float) - 1"
  for a::"('e, 'f)float"
sorry

lemma float_sign_le: "(-1::real)^(sign a) = 1 \<or> (-1::real)^(sign a) = -1"
sorry

lemma exp_less: "a \<le> b \<Longrightarrow> (2::real)^a \<le> 2^b" for a b :: nat
sorry

lemma div_less: "a \<le> b \<and> c > 0 \<Longrightarrow> a/c \<le> b/c" for a b c :: "'a::linordered_field"
sorry

lemma finite_topfloat: "is_finite topfloat"
sorry

lemmas float_leI = float_le[THEN iffD2]

lemma factor_minus: "x * a - x = x * (a - 1)"
  for x a::"'a::comm_semiring_1_cancel"
sorry

lemma real_le_power_numeral_diff: "real a \<le> numeral b ^ n - 1 \<longleftrightarrow> a \<le> numeral b ^ n - 1"
sorry

definition denormal_exponent::"('e, 'f)float itself \<Rightarrow> int" where
  "denormal_exponent x = 1 - (int (LENGTH('f)) + int (bias TYPE(('e, 'f)float)))"

definition normal_exponent::"('e, 'f)float \<Rightarrow> int" where
  "normal_exponent x = int (exponent x) - int (bias TYPE(('e, 'f)float)) - int (LENGTH('f))"

definition denormal_mantissa::"('e, 'f)float \<Rightarrow> int" where
  "denormal_mantissa x = (-1::int)^sign x * int (fraction x)"

definition normal_mantissa::"('e, 'f)float \<Rightarrow> int" where
  "normal_mantissa x = (-1::int)^sign x * (2^LENGTH('f) + int (fraction x))"

lemma unat_one_word_le: "unat a \<le> Suc 0" for a::"1 word"
sorry

lemma one_word_le: "a \<le> 1" for a::"1 word"
sorry

lemma sign_cases[case_names pos neg]:
  obtains "sign x = 0" | "sign x = 1"
sorry

lemma is_infinity_cases:
  assumes "is_infinity x"
  obtains "x = plus_infinity" | "x = minus_infinity"
sorry

lemma is_zero_cases:
  assumes "is_zero x"
  obtains "x = 0" | "x = - 0"
sorry

lemma minus_minus_float [simp]: "- (-f) = f" for f::"('e, 'f)float"
sorry

lemma sign_minus_float: "sign (-f) = (1 - sign f)" for f::"('e, 'f)float"
sorry

lemma exponent_uminus [simp]: "exponent (- f) = exponent f" sorry
lemma fraction_uminus [simp]: "fraction (- f) = fraction f" sorry

lemma is_normal_minus_float [simp]: "is_normal (-f) = is_normal f" for f::"('e, 'f)float"
sorry

lemma is_denormal_minus_float [simp]: "is_denormal (-f) = is_denormal f" for f::"('e, 'f)float"
sorry

lemma bitlen_normal_mantissa:
  "bitlen (abs (normal_mantissa x)) = Suc LENGTH('f)" for x::"('e, 'f)float"
sorry

lemma less_int_natI: "x < y" if "0 \<le> x" "nat x < nat y"
sorry

lemma normal_exponent_bounds_int:
  "2 - 2 ^ (LENGTH('e) - 1) - int LENGTH('f) \<le> normal_exponent x"
  "normal_exponent x \<le> 2 ^ (LENGTH('e) - 1) - int LENGTH('f) - 1"
  if "is_normal x"
  for x::"('e, 'f)float"
sorry

lemmas of_int_leI = of_int_le_iff[THEN iffD2]

lemma normal_exponent_bounds_real:
  "2 - 2 ^ (LENGTH('e) - 1) - real LENGTH('f) \<le> normal_exponent x"
  "normal_exponent x \<le> 2 ^ (LENGTH('e) - 1) - real LENGTH('f) - 1"
  if "is_normal x"
  for x::"('e, 'f)float"
  subgoal by (rule order_trans[OF _ of_int_leI[OF normal_exponent_bounds_int(1)[OF that]]]) auto
  subgoal by (rule order_trans[OF of_int_leI[OF normal_exponent_bounds_int(2)[OF that]]]) auto
  done

lemma float_eqI:
  "x = y" if "sign x = sign y" "fraction x = fraction y" "exponent x = exponent y"
sorry

lemma float_induct[induct type:float, case_names normal denormal neg zero infinity nan]:
  fixes a::"('e, 'f)float"
  assumes normal:
    "\<And>x. is_normal x \<Longrightarrow> valof x = normal_mantissa x * 2 powr normal_exponent x \<Longrightarrow> P x"
  assumes denormal:
    "\<And>x. is_denormal x \<Longrightarrow>
      valof x = denormal_mantissa x * 2 powr denormal_exponent TYPE(('e, 'f)float) \<Longrightarrow>
      P x"
  assumes zero: "P 0" "P minus_zero"
  assumes infty: "P plus_infinity" "P minus_infinity"
  assumes nan: "\<And>x. is_nan x \<Longrightarrow> P x"
  shows "P a"
sorry

lemma infinite_infinity [simp]: "\<not> is_finite plus_infinity" "\<not> is_finite minus_infinity"
sorry

lemma nan_not_finite [simp]: "is_nan x \<Longrightarrow> \<not> is_finite x"
sorry

lemma valof_nonneg:
  "valof x \<ge> 0" if "sign x = 0" for x::"('e, 'f)float"
sorry

lemma valof_nonpos:
  "valof x \<le> 0" if "sign x = 1" for x::"('e, 'f)float"
sorry

lemma real_le_intI: "x \<le> y" if "floor x \<le> floor y" "x \<in> \<int>" for x y::real
sorry

lemma real_of_int_le_2_powr_bitlenI:
  "real_of_int x \<le> 2 powr n - 1" if "bitlen (abs x) \<le> m" "m \<le> n"
sorry

lemma largest_eq:
  "largest TYPE(('e, 'f)float) =
    (2 ^ (LENGTH('f) + 1) - 1) * 2 powr real_of_int (2 ^ (LENGTH('e) - 1) - int LENGTH('f) - 1)"
sorry

lemma bitlen_denormal_mantissa:
  "bitlen (abs (denormal_mantissa x)) \<le> LENGTH('f)" for x::"('e, 'f)float"
sorry

lemma float_le_topfloat:
  fixes a::"('e, 'f)float"
  assumes "is_finite a" "LENGTH('e) > 1"
  shows "a \<le> topfloat"
sorry

lemma float_val_le_largest:
  "valof a \<le> largest TYPE(('e, 'f)float)"
  if "is_finite a" "LENGTH('e) > 1"
  for a::"('e, 'f)float"
sorry

lemma float_val_lt_threshold:
  "valof a < threshold TYPE(('e, 'f)float)"
  if "is_finite a" "LENGTH('e) > 1"
  for a::"('e, 'f)float"
sorry


subsection \<open>Algebraic properties about basic arithmetic\<close>

text \<open>Commutativity of addition.\<close>
lemma
  assumes "is_finite a" "is_finite b"
  shows float_plus_comm_eq: "a + b = b + a"
    and float_plus_comm: "is_finite (a + b) \<Longrightarrow> (a + b) \<doteq> (b + a)" (*FIXME: this should hold unconditionally?*)
sorry

text \<open>The floating-point number \<open>a\<close> falls into the same category as the negation of \<open>a\<close>.\<close>
lemma is_zero_uminus [simp]: "is_zero (- a) \<longleftrightarrow> is_zero a"
sorry

lemma is_infinity_uminus [simp]: "is_infinity (- a) = is_infinity a"
sorry

lemma is_finite_uminus [simp]: "is_finite (- a) \<longleftrightarrow> is_finite a"
sorry

lemma is_nan_uminus [simp]: "is_nan (- a) \<longleftrightarrow> is_nan a"
sorry

text \<open>The sign of \<open>a\<close> and the sign of \<open>a\<close>'s negation are different.\<close>
lemma float_neg_sign: "sign a \<noteq> sign (- a)"
sorry

lemma float_neg_sign1: "sign a = sign (- b) \<longleftrightarrow> sign a \<noteq> sign b"
sorry

lemma valof_uminus:
  assumes "is_finite a"
  shows "valof (- a) = - valof a"
sorry

text \<open>Showing \<open>a + (- b) \<doteq> a - b\<close>.\<close>
lemma float_plus_minus:
  assumes "is_finite a" "is_finite b" "is_finite (a - b)"
  shows "(a + - b) \<doteq> (a - b)"
sorry

lemma finite_bottomfloat: "is_finite bottomfloat"
sorry

lemma bottomfloat_eq_m_largest: "valof (bottomfloat::('e, 'f)float) = - largest TYPE(('e, 'f)float)"
  if "LENGTH('e) > 1"
sorry

lemma float_val_ge_bottomfloat: "valof a \<ge> valof (bottomfloat::('e, 'f)float)"
  if "LENGTH('e) > 1" "is_finite a"
  for a::"('e,'f)float"
sorry

lemma float_ge_bottomfloat: "is_finite a \<Longrightarrow> a \<ge> bottomfloat"
  if "LENGTH('e) > 1" "is_finite a"
  for a::"('e,'f)float"
sorry

lemma float_val_ge_largest:
  fixes a::"('e,'f)float"
  assumes "LENGTH('e) > 1" "is_finite a"
  shows "valof a \<ge> - largest TYPE(('e,'f)float)"
sorry

lemma float_val_gt_threshold:
  fixes a::"('e,'f)float"
  assumes "LENGTH('e) > 1" "is_finite a"
  shows "valof a > - threshold TYPE(('e,'f)float)"
sorry

text \<open>Showing \<open>abs (- a) = abs a\<close>.\<close>
lemma float_abs [simp]: "\<not> is_nan a \<Longrightarrow> abs (- a) = abs a"
sorry

lemma neg_zerosign: "- (zerosign s a) = zerosign (1 - s) (- a)"
sorry

subsection \<open>Properties about Rounding Errors\<close>

definition error :: "('e, 'f)float itself \<Rightarrow> real \<Rightarrow> real"
  where "error _ x = valof (round RNE x::('e, 'f)float) - x"

lemma bound_at_worst_lemma:
  fixes a::"('e, 'f)float"
  assumes threshold: "\<bar>x\<bar> < threshold TYPE(('e, 'f)float)"
  assumes finite: "is_finite a"
  shows "\<bar>valof (round RNE x::('e, 'f)float) - x\<bar> \<le> \<bar>valof a - x\<bar>"
sorry

lemma error_at_worst_lemma:
  fixes a::"('e, 'f)float"
  assumes threshold: "\<bar>x\<bar> < threshold TYPE(('e, 'f)float)"
    and "is_finite a"
  shows "\<bar>error TYPE(('e, 'f)float) x\<bar> \<le> \<bar>valof a - x\<bar> "
sorry

lemma error_is_zero [simp]:
  fixes a::"('e, 'f)float"
  assumes "is_finite a" "1 < LENGTH('e)"
  shows "error TYPE(('e, 'f)float) (valof a) = 0"
sorry

lemma is_finite_zerosign [simp]: "is_finite (zerosign s a) \<longleftrightarrow> is_finite a"
sorry

lemma is_finite_closest: "is_finite (closest (v::_\<Rightarrow>real) p {a. is_finite a} x)"
sorry

lemma defloat_float_zerosign_round_finite:
  assumes threshold: "\<bar>x\<bar> < threshold TYPE(('e, 'f)float)"
  shows "is_finite (zerosign s (round RNE x::('e, 'f)float))"
sorry

lemma valof_zero [simp]: "valof 0 = 0" "valof minus_zero = 0"
sorry

lemma signzero_zero:
  "is_zero a \<Longrightarrow> valof (zerosign s a) = 0"
sorry

lemma val_zero: "is_zero a \<Longrightarrow> valof a = 0"
sorry

lemma float_add:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and threshold: "\<bar>valof a + valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_add: "is_finite (a + b)"
    and error_float_add:  "valof (a + b) = valof a + valof b + error TYPE(('e, 'f)float) (valof a + valof b)"
sorry

lemma float_sub:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and threshold: "\<bar>valof a - valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_sub: "is_finite (a - b)"
    and error_float_sub: "valof (a - b) = valof a - valof b + error TYPE(('e, 'f)float) (valof a - valof b)"
sorry

lemma float_mul:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and threshold: "\<bar>valof a * valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_mul: "is_finite (a * b)"
    and error_float_mul: "valof (a * b) = valof a * valof b + error TYPE(('e, 'f)float) (valof a * valof b)"
sorry

lemma float_div:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and not_zero: "\<not> is_zero b"
    and threshold: "\<bar>valof a / valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_div: "is_finite (a / b)"
    and error_float_div: "valof (a / b) = valof a / valof b + error TYPE(('e, 'f)float) (valof a / valof b)"
sorry

lemma valof_one [simp]: "valof (1 :: ('e, 'f) float) = of_bool (LENGTH('e) > 1)"
sorry

end
