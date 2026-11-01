theory DSP_Driver imports DSP_Native "Complex_Main" "HOL-Number_Theory.Number_Theory" "HOL-Library.Discrete_Functions" "HOL-Decision_Procs.Approximation_Bounds" "HOL-Library.Code_Target_Numeral" "Pratt_Certificate.Pratt_Certificate"
begin
ML \<open>
val _ = File.write (Path.explode "ready-8e8c341b785e4839b631e6cc350556d6") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
