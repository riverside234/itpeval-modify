theory DSP_Driver imports DSP_Native "HOL-Analysis.Lebesgue_Measure" "HOL-Analysis.Tagged_Division" "HOL-Real_Asymp.Real_Asymp"
begin
ML \<open>
val _ = File.write (Path.explode "ready-98f3ae1af7af4e21bdcd562f386d135e") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
