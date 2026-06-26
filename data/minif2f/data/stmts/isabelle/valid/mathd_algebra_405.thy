(*
  Authors: Albert Qiaochu Jiang
*)

theory mathd_algebra_405 imports
  Complex_Main
begin

theorem mathd_algebra_405:
  fixes x :: nat
  assumes h0 : "0 < x"
    and h1 : "x ^ 2 + 4 * x + 4 < 20"
  shows "x = 1 \<or> x = 2"
  by sorry

end