theory DSP_Driver imports DSP_Native "HOL-Analysis.Lebesgue_Measure" "HOL-Analysis.Tagged_Division" "HOL-Real_Asymp.Real_Asymp"
begin
ML \<open>
val _ = File.write (Path.explode "ready-c92a54696c984394884db061d11e2582") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
