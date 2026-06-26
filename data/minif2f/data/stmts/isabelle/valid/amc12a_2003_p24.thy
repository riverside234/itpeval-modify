(*
  Authors: Wenda Li
*)

theory amc12a_2003_p24 imports
  Complex_Main
begin

theorem amc12a_2003_p24:
  fixes a b::real
  assumes "b\<le>a"
    and "1<b"
  shows "ln (a/b) / ln a + ln (b/a) / ln b \<le>0" (is "?L \<le> _")
  by sorry

end