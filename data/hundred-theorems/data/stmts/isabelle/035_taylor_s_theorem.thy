theory Taylor_Models
  imports
    "Horner_Eval"
    "Polynomial_Expression_Additional"
    "Taylor_Models_Misc"
    "HOL-Decision_Procs.Approximation"
    "HOL-Library.Function_Algebras"
    "HOL-Library.Set_Algebras"
    "Affine_Arithmetic.Straight_Line_Program"
    "Affine_Arithmetic.Affine_Approximation"
begin

text \<open>TODO: get rid of float poly/float inteval and use real poly/real interval
  and data refinement?\<close>

section \<open>Multivariate Taylor Models\<close>

subsection \<open>Computing interval bounds on arithmetic expressions\<close>

text \<open>This is a wrapper around the "approx" function.
  It computes range bounds on floatarith expressions.\<close>
fun compute_bound_fa :: "nat \<Rightarrow> floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
  where "compute_bound_fa prec f I = approx prec f (map Some I)"

lemma compute_bound_fa_correct:
  "interpret_floatarith f i \<in>\<^sub>r ivl"
  if "compute_bound_fa prec f I = Some ivl"
    "i all_in I"
  for i::"real list"
  by sorry


subsection \<open>Definition of Taylor models and notion of rangeity\<close>

text \<open>Taylor models are a pair of a polynomial and an absolute error bound.\<close>
datatype taylor_model = TaylorModel (tm_poly: "float poly") (tm_bound: "float interval")

text \<open>Taylor model for a real valuation of variables\<close>

primrec insertion :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a poly \<Rightarrow> 'a::{plus,zero,minus,uminus,times,one,power}"
where
  "insertion bs (C c) = c"
| "insertion bs (poly.Bound n) = bs n"
| "insertion bs (Neg a) = - insertion bs a"
| "insertion bs (poly.Add a b) = insertion bs a + insertion bs b"
| "insertion bs (Sub a b) = insertion bs a - insertion bs b"
| "insertion bs (Mul a b) = insertion bs a * insertion bs b"
| "insertion bs (Pw t n) = insertion bs t ^ n"
| "insertion bs (CN c n p) = insertion bs c + (bs n) * insertion bs p"

definition range_tm :: "(nat \<Rightarrow> real) \<Rightarrow> taylor_model \<Rightarrow> real interval" where
"range_tm e tm = interval_of (insertion e (tm_poly tm)) + real_interval (tm_bound tm)"

lemma Ipoly_num_params_cong: "Ipoly xs p = Ipoly ys p"
  if "\<And>i. i < num_params p \<Longrightarrow> xs ! i = ys ! i"
  by sorry

lemma insertion_num_params_cong: "insertion e p = insertion f p"
  if "\<And>i. i < num_params p \<Longrightarrow> e i = f i"
  by sorry

lemma insertion_eq_IpolyI: "insertion xs p = Ipoly ys p"
  if "\<And>i. i < num_params p \<Longrightarrow> xs i = ys ! i"
  by sorry

lemma Ipoly_eq_insertionI: "Ipoly ys p = insertion xs p"
  if "\<And>i. i < num_params p \<Longrightarrow> xs i = ys ! i"
  by sorry

lemma range_tmI:
  "x \<in>\<^sub>i range_tm e tm"
  if x: "x \<in>\<^sub>i interval_of (insertion e ((tm_poly tm))) + real_interval (tm_bound tm)"
  for e::"nat\<Rightarrow>real"
  by sorry

lemma range_tmD:
  "x \<in>\<^sub>i interval_of (insertion e (tm_poly tm)) + real_interval (tm_bound tm)"
  if "x \<in>\<^sub>i range_tm e tm"
  for e::"nat\<Rightarrow>real"
  by sorry


subsection \<open>Interval bounds for Taylor models\<close>

text \<open>Bound a polynomial by simply approximating it with interval arguments.\<close>
fun compute_bound_poly :: "nat \<Rightarrow> float interval poly \<Rightarrow> (float interval list) \<Rightarrow> (float interval list) \<Rightarrow> float interval" where
  "compute_bound_poly prec (poly.C f) I a = f"
| "compute_bound_poly prec (poly.Bound n) I a = round_interval prec (I ! n - (a ! n))"
| "compute_bound_poly prec (poly.Add p q) I a =
    round_interval prec (compute_bound_poly prec p I a + compute_bound_poly prec q I a)"
| "compute_bound_poly prec (poly.Sub p q) I a =
    round_interval prec (compute_bound_poly prec p I a - compute_bound_poly prec q I a)"
| "compute_bound_poly prec (poly.Mul p q) I a =
    mult_float_interval prec (compute_bound_poly prec p I a) (compute_bound_poly prec q I a)"
| "compute_bound_poly prec (poly.Neg p) I a = -compute_bound_poly prec p I a"
| "compute_bound_poly prec (poly.Pw p n) I a = power_float_interval prec n (compute_bound_poly prec p I a)"
| "compute_bound_poly prec (poly.CN p n q) I a =
    round_interval prec (compute_bound_poly prec p I a +
      mult_float_interval prec (round_interval prec (I ! n - (a ! n))) (compute_bound_poly prec q I a))"

text \<open>Bounds on Taylor models are simply a bound on its polynomial, widened by the approximation error.\<close>
fun compute_bound_tm :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> float interval"
  where "compute_bound_tm prec I a (TaylorModel p e) = compute_bound_poly prec p I a + e"

lemma compute_bound_tm_def:
  "compute_bound_tm prec I a tm = compute_bound_poly prec (tm_poly tm) I a + (tm_bound tm)"
  by sorry

lemma real_of_float_in_real_interval_of[intro, simp]: "real_of_float x \<in>\<^sub>r X" if "x \<in>\<^sub>i X"
  by sorry

lemma in_set_of_round_interval[intro, simp]:
  "x \<in>\<^sub>r round_interval prec X" if "x \<in>\<^sub>r X"
  by sorry

lemma in_set_real_minus_interval[intro, simp]:
  "x - y \<in>\<^sub>r X - Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  by sorry

lemma real_interval_plus: "real_interval (a + b) = real_interval a + real_interval b"
  by sorry

lemma real_interval_uminus: "real_interval (- b) = - real_interval b"
  by sorry

lemma real_interval_of: "real_interval (interval_of b) = interval_of b"
  by sorry

lemma real_interval_minus: "real_interval (a - b) = real_interval a - real_interval b"
  by sorry

lemma in_set_real_plus_interval[intro, simp]:
  "x + y \<in>\<^sub>r X + Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  by sorry

lemma in_set_neg_plus_interval[intro, simp]:
  "- y \<in>\<^sub>r - Y" if "y \<in>\<^sub>r Y"
  by sorry

lemma in_set_real_times_interval[intro, simp]:
  "x * y \<in>\<^sub>r X * Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  by sorry

lemma real_interval_one: "real_interval 1 = 1"
  by sorry

lemma real_interval_zero: "real_interval 0 = 0"
  by sorry

lemma real_interval_power: "real_interval (a ^ b) = real_interval a ^ b"
  by sorry

lemma in_set_real_power_interval[intro, simp]:
  "x ^ n \<in>\<^sub>r X ^ n" if "x \<in>\<^sub>r X"
  by sorry

lemma power_float_interval_real_interval[intro, simp]:
  "x ^ n \<in>\<^sub>r power_float_interval prec n X" if "x \<in>\<^sub>r X"
  by sorry

lemma in_set_mult_float_interval[intro, simp]:
  "x * y \<in>\<^sub>r mult_float_interval prec X Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  by sorry

lemma in_set_real_minus_swapI: "e i \<in>\<^sub>r I ! i - a ! i"
  if "x - e i \<in>\<^sub>r a ! i" "x \<in>\<^sub>r I ! i"
  by sorry

definition develops_at_within::"(nat \<Rightarrow> real) \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> bool"
  where "develops_at_within e a I \<longleftrightarrow> (a all_subset I) \<and> (\<forall>i < length I. e i \<in>\<^sub>r I ! i - a ! i)"

lemma develops_at_withinI:
  assumes all_in: "a all_subset I"
  assumes e: "\<And>i. i < length I \<Longrightarrow> e i \<in>\<^sub>r I ! i - a ! i"
  shows "develops_at_within e a I"
  by sorry

lemma develops_at_withinD:
  assumes "develops_at_within e a I"
  shows "a all_subset I"
    "\<And>i. i < length I \<Longrightarrow> e i \<in>\<^sub>r I ! i - a ! i"
  by sorry

lemma compute_bound_poly_correct:
  fixes p::"float poly"
  assumes "num_params p \<le> length I"
  assumes dev: "develops_at_within e a I"
  shows "insertion e (p::real poly) \<in>\<^sub>r compute_bound_poly prec (map_poly interval_of p) I a"
  by sorry

lemma compute_bound_tm_correct:
  fixes I :: "float interval list" and f :: "real list \<Rightarrow> real"
  assumes n: "num_params (tm_poly t) \<le> length I"
  assumes dev: "develops_at_within e a I"
  assumes x0: "x0 \<in>\<^sub>i range_tm e t"
  shows "x0 \<in>\<^sub>r compute_bound_tm prec I a t"
  by sorry

lemma compute_bound_tm_correct_subset:
  fixes I :: "float interval list" and f :: "real list \<Rightarrow> real"
  assumes n: "num_params (tm_poly t) \<le> length I"
  assumes dev: "develops_at_within e a I"
  shows "set_of (range_tm e t) \<subseteq> set_of (real_interval (compute_bound_tm prec I a t))"
  by sorry

lemma compute_bound_poly_mono:
  assumes "num_params p \<le> length I"
  assumes mem: "I all_subset J" "a all_subset I"
  shows "set_of (compute_bound_poly prec p I a) \<subseteq> set_of (compute_bound_poly prec p J a)"
  by sorry

lemma compute_bound_tm_mono:
  fixes I :: "float interval list" and f :: "real list \<Rightarrow> real"
  assumes "num_params (tm_poly t) \<le> length I"
  assumes "I all_subset J"
  assumes "a all_subset I"
  shows "set_of (compute_bound_tm prec I a t) \<subseteq> set_of (compute_bound_tm prec J a t)"
  by sorry


subsection \<open>Computing taylor models for basic, univariate functions\<close>

definition tm_const :: "float \<Rightarrow> taylor_model"
  where "tm_const c = TaylorModel (poly.C c) 0"

context includes floatarith_syntax begin

definition tm_pi :: "nat \<Rightarrow> taylor_model"
  where "tm_pi prec = (
  let pi_ivl = the (compute_bound_fa prec Pi [])
  in TaylorModel (poly.C (mid pi_ivl)) (centered pi_ivl)
)"

lemma zero_real_interval[intro,simp]: "0 \<in>\<^sub>r 0"
  by sorry

lemma range_TM_tm_const[simp]: "range_tm e (tm_const c) = interval_of c"
  by sorry

lemma num_params_tm_const[simp]: "num_params (tm_poly (tm_const c)) = 0"
  by sorry

lemma num_params_tm_pi[simp]: "num_params (tm_poly (tm_pi prec)) = 0"
  by sorry

lemma range_tm_tm_pi: "pi \<in>\<^sub>i range_tm e (tm_pi prec)"
  by sorry


subsubsection \<open>Derivations of floatarith expressions\<close>

text \<open>Compute the nth derivative of a floatarith expression\<close>
fun deriv :: "nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
  where "deriv v f 0 = f"
  | "deriv v f (Suc n) = DERIV_floatarith v (deriv v f n)"

lemma isDERIV_DERIV_floatarith:
  assumes "isDERIV v f vs"
  shows "isDERIV v (DERIV_floatarith v f) vs"
  by sorry

lemma isDERIV_is_analytic:
  "isDERIV i (Taylor_Models.deriv i f n) xs"
  if "isDERIV i f xs"
  by sorry

lemma deriv_correct:
  assumes "isDERIV i f (xs[i:=t])" "i < length xs"
  shows "((\<lambda>x. interpret_floatarith (deriv i f n) (xs[i:=x])) has_real_derivative interpret_floatarith (deriv i f (Suc n)) (xs[i:=t]))
    (at t within S)"
  by sorry

text \<open>Faster derivation for univariate functions, producing smaller terms and thus less over-approximation.\<close>
text \<open>TODO: Extend to Arctan, Log!\<close>
fun deriv_rec :: "floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
  where "deriv_rec (Exp (Var 0)) _ = Exp (Var 0)"
  | "deriv_rec (Cos (Var 0)) n = (case n mod 4
         of 0 \<Rightarrow> Cos (Var 0)
         | Suc 0 \<Rightarrow> Minus (Sin (Var 0))
         | Suc (Suc 0) \<Rightarrow> Minus (Cos (Var 0))
         | Suc (Suc (Suc 0)) \<Rightarrow> Sin (Var 0))"
  | "deriv_rec (Inverse (Var 0)) n = (if n = 0 then Inverse (Var 0) else Mult (Num (fact n * (if n mod 2 = 0 then 1 else -1))) (Inverse (Power (Var 0) (Suc n))))"
  | "deriv_rec f n = deriv 0 f n"

lemma deriv_rec_correct:
  assumes "isDERIV 0 f (xs[0:=t])" "0 < length xs"
  shows "((\<lambda>x. interpret_floatarith (deriv_rec f n) (xs[0:=x])) has_real_derivative interpret_floatarith (deriv_rec f (Suc n)) (xs[0:=t])) (at t within S)"
  by sorry

lemma deriv_rec_0_idem[simp]:
  shows "deriv_rec f 0 = f"
  by sorry


subsubsection \<open>Computing Taylor models for arbitrary univariate expressions\<close> 

fun tmf_c :: "nat \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> float interval option"
  where "tmf_c prec I f i = compute_bound_fa prec (Mult (deriv_rec f i) (Inverse (Num (fact i)))) I"
    \<comment> \<open>The interval coefficients of the Taylor polynomial,
   i.e. the real coefficients approximated by a float interval.\<close>

fun tmf_ivl_cs :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> floatarith \<Rightarrow> float interval list option"
  where "tmf_ivl_cs prec ord I a f = those (map (tmf_c prec a f) [0..<ord] @ [tmf_c prec I f ord])"
    \<comment> \<open>Make a list of bounds on the n+1 coefficients, with the n+1-th coefficient bounding
   the remainder term of the Taylor-Lagrange formula.\<close>

fun tmf_polys :: "float interval list \<Rightarrow> float poly \<times> float interval poly"
  where "tmf_polys [] = (poly.C 0, poly.C 0)"
  | "tmf_polys (c # cs) = (
         let (pf, pi) = tmf_polys cs
         in (poly.CN (poly.C (mid c)) 0 pf, poly.CN (poly.C (centered c)) 0 pi)
       )"

fun tm_floatarith :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
  where "tm_floatarith prec ord I a f = (
  map_option (\<lambda>cs. 
    let (pf, pi) = tmf_polys cs;
        _ = compute_bound_tm prec (List.map2 (-) I a);
        e = round_interval prec (Ipoly (List.map2 (-) I a) pi) \<comment> \<open>TODO: use \<open>compute_bound_tm\<close> here?!\<close>
    in TaylorModel pf e
  ) (tmf_ivl_cs prec ord I a f)
)" \<comment> \<open>Compute a Taylor model from an arbitrary, univariate floatarith expression, if possible.
   This is used to compute Taylor models for elemental functions like sin, cos, exp, etc.\<close>

term compute_bound_poly
lemma tmf_c_correct:
  fixes A::"float interval list" and I::"float interval" and f::floatarith and a::"real list"
  assumes "a all_in A"
  assumes "tmf_c prec A f i = Some I"
  shows "interpret_floatarith (deriv_rec f i) a / fact i \<in>\<^sub>r I"
  by sorry

lemma tmf_ivl_cs_length:
  assumes "tmf_ivl_cs prec n A a f = Some cs"
  shows "length cs = n + 1"
  by sorry

lemma tmf_ivl_cs_correct:
  fixes A::"float interval list" and f::floatarith
  assumes "a all_in I"
  assumes "tmf_ivl_cs prec ord I a f = Some cs"
  shows "\<And>i. i < ord \<Longrightarrow> tmf_c prec (map interval_of a) f i = Some (cs!i)"
    and "tmf_c prec I f ord = Some (cs!ord)"
    and "length cs = Suc ord"
  by sorry

lemma Ipoly_fst_tmf_polys:
  "Ipoly xs (fst (tmf_polys z)) = (\<Sum>i<length z. xs ! 0 ^ i * (mid (z ! i)))"
  for xs::"real list"
  by sorry

lemma insertion_fst_tmf_polys:
  "insertion e (fst (tmf_polys z)) = (\<Sum>i<length z. e 0 ^ i * (mid (z ! i)))"
  for e::"nat \<Rightarrow> real"
  by sorry

lemma Ipoly_snd_tmf_polys:
  "set_of (horner_eval (real_interval o centered o nth z) x (length z)) \<subseteq> set_of (Ipoly [x] (map_poly real_interval (snd (tmf_polys z))))"
  by sorry

lemma zero_interval[intro,simp]: "0 \<in>\<^sub>i 0"
  by sorry

lemma sum_in_intervalI: "sum f X \<in>\<^sub>i sum g X" if "\<And>x. x \<in> X \<Longrightarrow> f x \<in>\<^sub>i g x"
  for f :: "_ \<Rightarrow> 'a :: ordered_comm_monoid_add"
  by sorry

lemma set_of_sum_subset: "set_of (sum f X) \<subseteq> set_of (sum g X)"
  if "\<And>x. x \<in> X \<Longrightarrow> set_of (f x) \<subseteq> set_of (g x)"
  for f :: "_\<Rightarrow>'a::linordered_ab_group_add interval"
  by sorry

lemma interval_of_plus: "interval_of (a + b) = interval_of a + interval_of b"
  by sorry

lemma interval_of_uminus: "interval_of (- a) = - interval_of a"
  by sorry

lemma interval_of_zero: "interval_of 0 = 0"
  by sorry

lemma interval_of_sum: "interval_of (sum f X) = sum (\<lambda>x. interval_of (f x)) X"
  by sorry

lemma interval_of_prod: "interval_of (a * b) = interval_of a * interval_of b"
  by sorry

lemma in_set_of_interval_of[simp]: "x \<in>\<^sub>i (interval_of y) \<longleftrightarrow> x = y" for x y::"'a::order"
  by sorry

lemma real_interval_Ipoly: "real_interval (Ipoly xs p) = Ipoly (map real_interval xs) (map_poly real_interval p)"
  if "num_params p \<le> length xs"
  by sorry

lemma num_params_tmf_polys1: "num_params (fst (tmf_polys z)) \<le> Suc 0"
  by sorry

lemma num_params_tmf_polys2: "num_params (snd (tmf_polys z)) \<le> Suc 0"
  by sorry

lemma set_of_real_interval_subset: "set_of (real_interval x) \<subseteq> set_of (real_interval y)"
  if "set_of x \<subseteq> set_of y"
  by sorry

theorem tm_floatarith:
  assumes t: "tm_floatarith prec ord I xs f = Some t"
  assumes a: "xs all_in I" and x: "x \<in>\<^sub>r I ! 0"
  assumes xs_ne: "xs \<noteq> []"
  assumes deriv: "\<And>x. x \<in>\<^sub>r I ! 0 \<Longrightarrow> isDERIV 0 f (xs[0 := x])"
  assumes "\<And>i. 0 < i \<Longrightarrow> i < length xs \<Longrightarrow> e i = real_of_float (xs ! i)"
  assumes diff_e: "(x - real_of_float (xs ! 0)) = e 0"
  shows "interpret_floatarith f (xs[0:=x]) \<in>\<^sub>i range_tm e t"
  by sorry


subsection \<open>Operations on Taylor models\<close>

fun tm_norm_poly :: "taylor_model \<Rightarrow> taylor_model"
  where "tm_norm_poly (TaylorModel p e) = TaylorModel (polynate p) e"
\<comment> \<open>Normalizes the Taylor model by transforming its polynomial into horner form.\<close>

fun tm_lower_order tm_lower_order_of_normed :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_lower_order prec ord I a t = tm_lower_order_of_normed prec ord I a (tm_norm_poly t)"
  |  "tm_lower_order_of_normed prec ord I a (TaylorModel p e) = (
         let (l, r) = split_by_degree ord p
         in TaylorModel l (round_interval prec (e + compute_bound_poly prec r I a))
       )"
\<comment> \<open>Reduces the degree of a Taylor model's polynomial to n and keeps it range by increasing the error bound.\<close>

fun tm_round_floats tm_round_floats_of_normed :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_round_floats prec I a t = tm_round_floats_of_normed prec I a (tm_norm_poly t)"
  | "tm_round_floats_of_normed prec I a (TaylorModel p e) = (
         let (l, r) = split_by_prec prec p
         in TaylorModel l (round_interval prec (e + compute_bound_poly prec r I a))
       )"
\<comment> \<open>Rounding of Taylor models. Rounds both the coefficients of the polynomial and the floats in the error bound.\<close>

fun tm_norm tm_norm' :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_norm prec ord I a t = tm_norm' prec ord I a (tm_norm_poly t)"
  | "tm_norm' prec ord I a t = tm_round_floats_of_normed prec I a (tm_lower_order_of_normed prec ord I a t)" 
\<comment> \<open>Normalization of taylor models. Performs order lowering and rounding on tayor models,
   also converts the polynomial into horner form.\<close>

fun tm_neg :: "taylor_model \<Rightarrow> taylor_model"
  where "tm_neg (TaylorModel p e) = TaylorModel (~\<^sub>p p) (-e)"

fun tm_add :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_add (TaylorModel p1 e1) (TaylorModel p2 e2) = TaylorModel (p1 +\<^sub>p p2) (e1 + e2)"

fun tm_sub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_sub t1 t2 = tm_add t1 (tm_neg t2)"

fun tm_mul :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_mul prec ord I a (TaylorModel p1 e1) (TaylorModel p2 e2) = (
         let d1 = compute_bound_poly prec p1 I a;
             d2 = compute_bound_poly prec p2 I a;
             p = p1 *\<^sub>p p2;
             e = e1*d2 + d1*e2 + e1*e2
         in tm_norm' prec ord I a (TaylorModel p e)
       )"
lemmas [simp del] = tm_norm'.simps

fun tm_pow :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> nat \<Rightarrow> taylor_model"
  where "tm_pow prec ord I a t 0 = tm_const 1"
  | "tm_pow prec ord I a t (Suc n) = (
         if odd (Suc n)
         then tm_mul prec ord I a t (tm_pow prec ord I a t n)
         else let t' = tm_pow prec ord I a t ((Suc n) div 2)
              in tm_mul prec ord I a t' t'
       )"

text \<open>Evaluates a float polynomial, using a Taylor model as the parameter. This is used to compose Taylor models.\<close>
fun eval_poly_at_tm :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> float poly \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "eval_poly_at_tm prec ord I a (poly.C c) t = tm_const c"
  | "eval_poly_at_tm prec ord I a (poly.Bound n) t = t"
  | "eval_poly_at_tm prec ord I a (poly.Add p1 p2) t
         = tm_add (eval_poly_at_tm prec ord I a p1 t)
                  (eval_poly_at_tm prec ord I a p2 t)"
  | "eval_poly_at_tm prec ord I a (poly.Sub p1 p2) t
         = tm_sub (eval_poly_at_tm prec ord I a p1 t)
                  (eval_poly_at_tm prec ord I a p2 t)"
  | "eval_poly_at_tm prec ord I a (poly.Mul p1 p2) t
         = tm_mul prec ord I a (eval_poly_at_tm prec ord I a  p1 t)
                               (eval_poly_at_tm prec ord I a p2 t)"
  | "eval_poly_at_tm prec ord I a (poly.Neg p) t
         = tm_neg (eval_poly_at_tm prec ord I a p t)"
  | "eval_poly_at_tm prec ord I a (poly.Pw p n) t
         = tm_pow prec ord I a (eval_poly_at_tm prec ord I a p t) n"
  | "eval_poly_at_tm prec ord I a (poly.CN c n p) t = (
         let pt = eval_poly_at_tm prec ord I a p t;
             t_mul_pt = tm_mul prec ord I a t pt 
         in tm_add (eval_poly_at_tm prec ord I a c t) t_mul_pt
       )"

fun tm_inc_err :: "float interval \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_inc_err i (TaylorModel p e) = TaylorModel p (e + i)"

fun tm_comp :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> float \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_comp prec ord I a ta (TaylorModel p e) t = (
         let t_sub_ta = tm_sub t (tm_const ta);
             pt = eval_poly_at_tm prec ord I a p t_sub_ta
         in tm_inc_err e pt
       )"

text \<open>\<open>tm_max\<close>, \<open>tm_min\<close> and \<open>tm_abs\<close> are implemented extremely naively, because I don't expect them to be very useful.
   But the implementation is fairly modular, i.e. \<open>tm_{abs,min,max}\<close> all can easily be swapped out,
   as long as the corresponding correctness lemmas \<open>tm_{abs,min,max}_range\<close> are updated as well.\<close>
fun tm_abs :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_abs prec I a t = (
  let bound = compute_bound_tm prec I a t; abs_bound=Ivl (0::float) (max (abs (lower bound)) (abs (upper bound)))
  in TaylorModel (poly.C (mid abs_bound)) (centered abs_bound))"

fun tm_union :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_union prec I a t1 t2 = (
  let b1 = compute_bound_tm prec I a t1; b2 = compute_bound_tm prec I a t2;
      b_combined = sup b1 b2
  in TaylorModel (poly.C (mid b_combined)) (centered b_combined))"

fun tm_min :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_min prec I a t1 t2 = tm_union prec I a t1 t2"

fun tm_max :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_max  prec I a t1 t2 = tm_union prec I a t1 t2"

text \<open>Rangeity of is preserved by our operations on Taylor models.\<close>

lemma insertion_polyadd[simp]: "insertion e (a +\<^sub>p b) = insertion e a + insertion e b"
  for a b::"'a::ring_1 poly"
  by sorry


lemma insertion_polyneg[simp]: "insertion e (~\<^sub>p b) =  - insertion e b"
  for b::"'a::ring_1 poly"
  by sorry

lemma insertion_polysub[simp]: "insertion e (a -\<^sub>p b) = insertion e a - insertion e b"
  for a b::"'a::ring_1 poly"
  by sorry

lemma insertion_polymul[simp]: "insertion e (a *\<^sub>p b) = insertion e a * insertion e b"
  for a b::"'a::comm_ring_1 poly"
  by sorry

lemma insertion_polypow[simp]: "insertion e (a ^\<^sub>p b) = insertion e a ^ b"
  for a::"'a::comm_ring_1 poly"
  by sorry

lemma insertion_polynate [simp]:
  "insertion bs (polynate p) = (insertion bs p :: 'a::comm_ring_1)"
  by sorry

lemma tm_norm_poly_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  shows "x \<in>\<^sub>i range_tm e (tm_norm_poly t)"
  by sorry

lemma split_by_degree_correct_insertion:
  fixes x :: "nat \<Rightarrow> real" and p :: "float poly"
  assumes "split_by_degree ord p = (l, r)"
  shows "maxdegree l \<le> ord" (is ?P1)
    and   "insertion x p = insertion x l + insertion x r" (is ?P2)
    and   "num_params l \<le> num_params p" (is ?P3)
    and   "num_params r \<le> num_params p" (is ?P4)
  by sorry

lemma split_by_prec_correct_insertion:
  fixes x :: "nat \<Rightarrow> real" and p :: "float poly"
  assumes "split_by_prec ord p = (l, r)"
  shows "insertion x p = insertion x l + insertion x r" (is ?P1)
    and "num_params l \<le> num_params p" (is ?P2)
    and "num_params r \<le> num_params p" (is ?P3)
  by sorry

lemma tm_lower_order_of_normed_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  assumes dev: "develops_at_within e a I"
  assumes "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_lower_order_of_normed prec ord I a t)"
  by sorry

lemma num_params_tm_norm_poly_le: "num_params (tm_poly (tm_norm_poly t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  by sorry

lemma tm_lower_order_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  assumes dev: "develops_at_within e a I"
  assumes "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_lower_order prec ord I a t)"
  by sorry

lemma tm_round_floats_of_normed_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  assumes dev: "develops_at_within e a I"
  assumes "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_round_floats_of_normed prec I a t)"
    \<comment> \<open>TODO: this is a clone of @{thm tm_lower_order_of_normed_range} -> general sweeping method!\<close>
  by sorry

lemma num_params_split_by_degree_le: "num_params (fst (split_by_degree ord x)) \<le> K"
  "num_params (snd (split_by_degree ord x)) \<le> K"
  if "num_params x \<le> K" for x::"float poly"
  by sorry

lemma num_params_split_by_prec_le: "num_params (fst (split_by_prec ord x)) \<le> K"
  "num_params (snd (split_by_prec ord x)) \<le> K"
  if "num_params x \<le> K" for x::"float poly"
  by sorry

lemma num_params_tm_norm'_le:
  "num_params (tm_poly (tm_round_floats_of_normed prec I a t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  by sorry

lemma tm_round_floats_range:
  assumes "x \<in>\<^sub>i range_tm e t" "develops_at_within e a I" "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_round_floats prec I a t)"
  by sorry

lemma num_params_tm_lower_order_of_normed_le: "num_params (tm_poly (tm_lower_order_of_normed prec ord I a t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  by sorry


lemma tm_norm'_range:
  assumes "x \<in>\<^sub>i range_tm e t" "develops_at_within e a I" "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_norm' prec ord I a t)"
  by sorry

lemma num_params_tm_norm':
  "num_params (tm_poly (tm_norm' prec ord I a t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  by sorry

lemma tm_norm_range:
  assumes "x \<in>\<^sub>i range_tm e t" "develops_at_within e a I" "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_norm prec ord I a t)"
  by sorry
lemmas [simp del] = tm_norm.simps

lemma tm_neg_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  shows "- x \<in>\<^sub>i range_tm e (tm_neg t)"
  by sorry
lemmas [simp del] = tm_neg.simps


lemma tm_bound_tm_add[simp]: "tm_bound (tm_add t1 t2) = tm_bound t1 + tm_bound t2"
  by sorry

lemma interval_of_add: "interval_of (a + b) = interval_of a + interval_of b"
  by sorry

lemma tm_add_range:
  "x + y \<in>\<^sub>i range_tm e (tm_add t1 t2)"
  if "x \<in>\<^sub>i range_tm e t1"
    "y \<in>\<^sub>i range_tm e t2"
  by sorry
lemmas [simp del] = tm_add.simps

lemma tm_sub_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
  shows "x - y \<in>\<^sub>i range_tm e (tm_sub t1 t2)"
  by sorry
lemmas [simp del] = tm_sub.simps

lemma set_of_intervalI: "set_of (interval_of y) \<subseteq> set_of Y" if "y \<in>\<^sub>i Y" for y::"'a::order"
  by sorry

lemma set_of_real_intervalI: "set_of (interval_of y) \<subseteq> set_of (real_interval Y)" if "y \<in>\<^sub>r Y"
  by sorry

lemma tm_mul_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
  assumes dev: "develops_at_within e a I"
  assumes params: "num_params (tm_poly t1) \<le> length I" "num_params (tm_poly t2) \<le> length I"
  shows "x * y \<in>\<^sub>i range_tm e (tm_mul prec ord I a t1 t2)"
  by sorry

lemma num_params_tm_mul_le:
  "num_params (tm_poly (tm_mul prec ord I a t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X"
    "num_params (tm_poly t2) \<le> X"
  by sorry

lemmas [simp del] = tm_pow.simps\<comment> \<open>TODO: make a systematic decision\<close>

lemma
  shows tm_pow_range: "num_params (tm_poly t) \<le> length I \<Longrightarrow>
      develops_at_within e a I \<Longrightarrow>
      x \<in>\<^sub>i range_tm e t \<Longrightarrow>
      x ^ n \<in>\<^sub>i range_tm e (tm_pow prec ord I a t n)"
    and num_params_tm_pow_le[THEN order_trans]:
      "num_params (tm_poly (tm_pow prec ord I a t n)) \<le> num_params (tm_poly t)"
  by sorry

lemma num_params_tm_add_le:
  "num_params (tm_poly (tm_add t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X"
    "num_params (tm_poly t2) \<le> X"
  by sorry

lemma num_params_tm_neg_eq[simp]:
  "num_params (tm_poly (tm_neg t1)) = num_params (tm_poly t1)"
  by sorry

lemma num_params_tm_sub_le:
  "num_params (tm_poly (tm_sub t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X"
    "num_params (tm_poly t2) \<le> X"
  by sorry

lemma num_params_eval_poly_le: "num_params (tm_poly (eval_poly_at_tm prec ord I a p t)) \<le> x"
  if "num_params (tm_poly t) \<le> x" "num_params p \<le> max 1 x"
  by sorry

lemma eval_poly_at_tm_range:
  assumes "num_params p \<le> 1"
  assumes tg_def: "e' 0 \<in>\<^sub>i range_tm e tg"
  assumes dev: "develops_at_within e a I" and params: "num_params (tm_poly tg) \<le> length I"
  shows "insertion e' p \<in>\<^sub>i range_tm e (eval_poly_at_tm prec ord I a p tg)"
  by sorry

lemma tm_inc_err_range: "x \<in>\<^sub>i range_tm e (tm_inc_err i t)"
  if "x \<in>\<^sub>i range_tm e t + real_interval i"
  by sorry

lemma num_params_tm_inc_err: "num_params (tm_poly (tm_inc_err i t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  by sorry

lemma num_params_tm_comp_le: "num_params (tm_poly (tm_comp prec ord I a ga tf tg)) \<le> X"
  if "num_params (tm_poly tf) \<le> max 1 X" "num_params (tm_poly tg) \<le> X"
  by sorry

lemma tm_comp_range:
  assumes tf_def: "x \<in>\<^sub>i range_tm e' tf"
  assumes tg_def: "e' 0 \<in>\<^sub>i range_tm e (tm_sub tg (tm_const ga))"
  assumes params: "num_params (tm_poly tf) \<le> 1" "num_params (tm_poly tg) \<le> length I"
  assumes dev: "develops_at_within e a I"
  shows "x \<in>\<^sub>i range_tm e (tm_comp prec ord I a ga tf tg)"
  by sorry

lemma mid_centered_collapse:
  "interval_of (real_of_float (mid abs_bound)) + real_interval (centered abs_bound) =
    real_interval abs_bound"
  by sorry

lemmas [simp del] = tm_abs.simps
lemma tm_abs_range:
  assumes x: "x \<in>\<^sub>i range_tm e t"
  assumes n: "num_params (tm_poly t) \<le> length I" and d: "develops_at_within e a I"
  shows "abs x \<in>\<^sub>i range_tm e (tm_abs prec I a t)"
  by sorry

lemma num_params_tm_abs_le: "num_params (tm_poly (tm_abs prec I a t)) \<le> X" if "num_params (tm_poly t) \<le> X"
  by sorry

lemma real_interval_sup: "real_interval (sup a b) = sup (real_interval a) (real_interval b)"
  by sorry

lemma in_interval_supI1: "x \<in>\<^sub>i a \<Longrightarrow> x \<in>\<^sub>i sup a b"
  and in_interval_supI2: "x \<in>\<^sub>i b \<Longrightarrow> x \<in>\<^sub>i sup a b"
  for x::"'a::lattice"
  by sorry
  
lemma tm_union_range_left:
  assumes "x \<in>\<^sub>i range_tm e t1"
    "num_params (tm_poly t1) \<le> length I" "develops_at_within e a I"
  shows "x \<in>\<^sub>i range_tm e (tm_union prec I a t1 t2)"
  by sorry

lemma tm_union_range_right:
  assumes "x \<in>\<^sub>i range_tm e t2"
    "num_params (tm_poly t2) \<le> length I" "develops_at_within e a I"
  shows "x \<in>\<^sub>i range_tm e (tm_union prec I a t1 t2)"
  by sorry

lemma num_params_tm_union_le:
  "num_params (tm_poly (tm_union prec I a t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X" "num_params (tm_poly t2) \<le> X"
  by sorry
  
lemmas [simp del] = tm_union.simps tm_min.simps tm_max.simps

lemma tm_min_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
    "num_params (tm_poly t1) \<le> length I"
    "num_params (tm_poly t2) \<le> length I"
    "develops_at_within e a I"
  shows "min x y \<in>\<^sub>i range_tm e (tm_min prec I a t1 t2)"
  by sorry

lemma tm_max_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
    "num_params (tm_poly t1) \<le> length I"
    "num_params (tm_poly t2) \<le> length I"
    "develops_at_within e a I"
  shows "max x y \<in>\<^sub>i range_tm e (tm_max prec I a t1 t2)"
  by sorry


subsection \<open>Computing Taylor models for multivariate expressions\<close>

text \<open>Compute Taylor models for expressions of the form "f (g x)", where f is an elementary function like exp or cos,
   by composing Taylor models for f and g. For our correctness proof, we need to make it explicit that the range
   of g on I is inside the domain of f, by introducing the \<open>f_exists_on\<close> predicate.\<close>
fun compute_tm_by_comp :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> taylor_model option \<Rightarrow> (float interval \<Rightarrow> bool) \<Rightarrow> taylor_model option"
  where "compute_tm_by_comp prec ord I a f g f_exists_on = (
         case g
         of Some tg \<Rightarrow> (
           let gI = compute_bound_tm prec I a tg;
               ga = mid (compute_bound_tm prec a a tg)
           in if f_exists_on gI
              then map_option (\<lambda>tf. tm_comp prec ord I a ga tf tg ) (tm_floatarith prec ord [gI] [ga] f)
              else None)
         | _ \<Rightarrow> None
       )"

text \<open>Compute Taylor models with numerical precision \<open>prec\<close> of degree \<open>ord\<close>,
  with Taylor models in the environment \<open>env\<close> whose variables are jointly interpreted with domain
  \<open>I\<close> and expanded around point \<open>a\<close>.
  from floatarith expressions on a rectangular domain.\<close>
fun approx_tm :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> taylor_model list \<Rightarrow>
    taylor_model option"
  where "approx_tm _ _ I _ (Num c) env = Some (tm_const c)"
  | "approx_tm _ _ I a (Var n) env = (if n < length env then Some (env ! n) else None)"
  | "approx_tm prec ord I a (Add l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_add t1 t2)
          | _ \<Rightarrow> None)"
  | "approx_tm prec ord I a (Minus f) env
         = map_option tm_neg (approx_tm prec ord I a f env)"
  | "approx_tm prec ord I a (Mult l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_mul prec ord I a t1 t2)
          | _ \<Rightarrow> None)"     
  | "approx_tm prec ord I a (Power f k) env
         = map_option (\<lambda>t. tm_pow prec ord I a t k)
                      (approx_tm prec ord I a f env)"
  | "approx_tm prec ord I a (Inverse f) env
         = compute_tm_by_comp prec ord I a (Inverse (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. 0 < lower x \<or> upper x < 0)"
  | "approx_tm prec ord I a (Cos f) env
         = compute_tm_by_comp prec ord I a (Cos (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. True)"
  | "approx_tm prec ord I a (Arctan f) env
         = compute_tm_by_comp prec ord I a (Arctan (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. True)"
  | "approx_tm prec ord I a (Exp f) env
         = compute_tm_by_comp prec ord I a (Exp (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. True)"
  | "approx_tm prec ord I a (Ln f) env
         = compute_tm_by_comp prec ord I a (Ln (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. 0 < lower x)"
  | "approx_tm prec ord I a (Sqrt f) env
         = compute_tm_by_comp prec ord I a (Sqrt (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. 0 < lower x)"
  | "approx_tm prec ord I a Pi env = Some (tm_pi prec)"
  | "approx_tm prec ord I a (Abs f) env
         = map_option (tm_abs prec I a) (approx_tm prec ord I a f env)"
  | "approx_tm prec ord I a (Min l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_min prec I a t1 t2)
          | _ \<Rightarrow> None)"
  | "approx_tm prec ord I a (Max l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env)
         of (Some t1, Some t2) \<Rightarrow> Some (tm_max prec I a t1 t2)
          | _ \<Rightarrow> None)"
  | "approx_tm prec ord I a (Powr l r) env = None" \<comment> \<open>TODO\<close>
  | "approx_tm prec ord I a (Floor l) env = None" \<comment> \<open>TODO\<close>

lemma mid_in_real_interval: "mid i \<in>\<^sub>r i"
  by sorry

lemma set_of_real_interval_mono:"set_of (real_interval x) \<subseteq> set_of (real_interval y)"
  if "set_of x \<subseteq> set_of y"
  by sorry

lemmas [simp del] = compute_bound_poly.simps tm_floatarith.simps

(*
  assumes tx_valid: "valid_tm I a (interpret_floatarith g) tg"
  assumes t_def: "compute_tm_on_ivl_by_comp prec ord I a f (Some tg) c = Some t"
  assumes f_deriv: "\<And>x. x \<in>\<^sub>r (compute_bound_tm prec I a tg) \<Longrightarrow> c (compute_bound_tm prec I a tg) \<Longrightarrow> isDERIV 0 f [x]"
  shows "valid_tm I a ((\<lambda>x. interpret_floatarith f [x]) o interpret_floatarith g) t"
*)

lemmas [simp del] = tmf_ivl_cs.simps compute_bound_tm.simps tmf_polys.simps

lemma tm_floatarith_eq_Some_num_params:
  "tm_floatarith prec ord a b f = Some tf \<Longrightarrow> num_params (tm_poly tf) \<le> 1"
  by sorry

lemma compute_tm_by_comp_range:
  assumes "max_Var_floatarith f \<le> 1"
  assumes a: "a all_subset I"
  assumes tx_range: "x \<in>\<^sub>i range_tm e tg"
  assumes t_def: "compute_tm_by_comp prec ord I a f (Some tg) c = Some t"
  assumes f_deriv:
    "\<And>x. x \<in>\<^sub>r compute_bound_tm prec I a tg \<Longrightarrow> c (compute_bound_tm prec I a tg) \<Longrightarrow> isDERIV 0 f [x]"
  assumes params: "num_params (tm_poly tg) \<le> length I"
    and dev: "develops_at_within e a I"
  shows "interpret_floatarith f [x] \<in>\<^sub>i range_tm e t"
  by sorry

lemmas [simp del] = compute_tm_by_comp.simps

lemma compute_tm_by_comp_num_params_le:
  assumes "compute_tm_by_comp prec ord I a f (Some t0) i = Some t"
  assumes "1 \<le> X" "num_params (tm_poly t0) \<le> X"
  shows "num_params (tm_poly t) \<le> X"
  by sorry

lemma compute_tm_by_comp_eq_Some_iff: "compute_tm_by_comp prec ord I a f t0 i = Some t \<longleftrightarrow>
  (\<exists>z x2. t0 = Some x2 \<and>
    tm_floatarith prec ord [compute_bound_tm prec I a x2]
      [mid (compute_bound_tm prec a a x2)] f =
      Some z
   \<and> tm_comp prec ord I a
      (mid (compute_bound_tm prec a a x2)) z x2 = t
   \<and> i (compute_bound_tm prec I a x2))"
  by sorry

lemma num_params_approx_tm:
  assumes "approx_tm prec ord I a f env = Some t"
  assumes "\<And>tm. tm \<in> set env \<Longrightarrow> num_params (tm_poly tm) \<le> length I"
  shows "num_params (tm_poly t) \<le> length I"
  by sorry

lemma in_interval_realI: "a \<in>\<^sub>i I" if "a \<in>\<^sub>r I" using that by (auto simp: set_of_eq)

lemma all_subset_all_inI: "map interval_of a all_subset I" if "a all_in I"
  by sorry

lemma compute_tm_by_comp_None: "compute_tm_by_comp p ord I a x None k = None"
  by sorry

lemma approx_tm_num_Vars_None:
  assumes "max_Var_floatarith f > length env"
  shows "approx_tm p ord I a f env = None"
  by sorry

lemma approx_tm_num_Vars:
  assumes "approx_tm prec ord I a f env = Some t"
  shows "max_Var_floatarith f \<le> length env"
  by sorry

definition "range_tms e xs = map (range_tm e) xs"

lemma approx_tm_range:
  assumes a: "a all_subset I"
  assumes t_def: "approx_tm prec ord I a f env = Some t"
  assumes allin: "xs all_in\<^sub>i range_tms e env"
  assumes devs: "develops_at_within e a I"
  assumes env: "\<And>tm. tm \<in> set env \<Longrightarrow> num_params (tm_poly tm) \<le> length I"
  shows "interpret_floatarith f xs \<in>\<^sub>i range_tm e t"
  by sorry


text \<open>Evaluate expression with Taylor models in environment.\<close>

subsection \<open>Computing bounds for floatarith expressions\<close>

text \<open>TODO: compare parametrization of input vs. uncertainty for input...\<close>

definition "tm_of_ivl_par n ivl = TaylorModel (CN (C ((upper ivl + lower ivl)*Float 1 (-1))) n
  (C ((upper ivl - lower ivl)*Float 1 (-1)))) 0"
  \<comment> \<open>track uncertainty in parameter \<open>n\<close>, which is to be interpreted over standardized domain \<open>[-1, 1]\<close>.\<close>

value "tm_of_ivl_par 3 (Ivl (-1) 1)"

definition "tms_of_ivls ivls = map (\<lambda>(i, ivl). tm_of_ivl_par i ivl) (zip [0..<length ivls] ivls)"

value "tms_of_ivls [Ivl 1 2, Ivl 4 5]"

primrec approx_slp'::"nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> slp \<Rightarrow>
  taylor_model list \<Rightarrow> taylor_model list option"
where
  "approx_slp' p ord I a [] xs = Some xs"
| "approx_slp' p ord I a (ea # eas) xs =
    do {
      r \<leftarrow> approx_tm p ord I a ea xs;
      approx_slp' p ord I a eas (r#xs)
    }"

lemma mem_range_tms_Cons_iff[simp]: "x#xs all_in\<^sub>i range_tms e (X#XS) \<longleftrightarrow> x \<in>\<^sub>i range_tm e X \<and> xs all_in\<^sub>i range_tms e XS"
  by sorry

lemma approx_slp'_range:
  assumes i: "i all_subset I"
  assumes dev: "develops_at_within e i I"
  assumes vs: "vs all_in\<^sub>i range_tms e VS" "(\<And>tm. tm \<in> set VS \<Longrightarrow> num_params (tm_poly tm) \<le> length I)"
  assumes appr: "approx_slp' p ord I i ra VS = Some X"
  shows "interpret_slp ra vs all_in\<^sub>i range_tms e X"
  by sorry

definition approx_slp::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> taylor_model list \<Rightarrow> taylor_model list option"
  where
    "approx_slp p ord d slp tms =
      map_option (take d)
        (approx_slp' p ord (replicate (length tms) (Ivl (-1) 1)) (replicate (length tms) 0) slp tms)"

lemma length_range_tms[simp]: "length (range_tms e VS) = length VS"
  by sorry

lemma set_of_Ivl: "set_of (Ivl a b) = {a .. b}" if "a \<le> b"
  by sorry

lemma set_of_zero[simp]: "set_of 0 = {0::'a::ordered_comm_monoid_add}"
  by sorry

theorem approx_slp_range_tms:
  assumes "approx_slp p ord d slp VS = Some X"
  assumes slp_def: "slp = slp_of_fas fas"
  assumes d_def: "d = length fas"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes vs: "vs all_in\<^sub>i range_tms e VS"
  assumes lens: "\<And>tm. tm \<in> set VS \<Longrightarrow> num_params (tm_poly tm) \<le> length vs"
  shows "interpret_floatariths fas vs all_in\<^sub>i range_tms e X"
  by sorry

end

end