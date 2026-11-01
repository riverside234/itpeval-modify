theory DSP_Driver imports DSP_Native "HOL-Analysis.Lebesgue_Measure" "HOL-Analysis.Tagged_Division" "HOL-Real_Asymp.Real_Asymp"
begin
ML \<open>
val _ = File.write (Path.explode "ready-0ffbaaf8e4bc436099afeb39e2ea8056") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
