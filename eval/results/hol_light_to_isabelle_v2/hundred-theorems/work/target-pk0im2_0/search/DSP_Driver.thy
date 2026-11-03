theory DSP_Driver imports DSP_Native "HOL-Analysis.Lebesgue_Measure" "HOL-Analysis.Tagged_Division" "HOL-Real_Asymp.Real_Asymp"
begin
ML \<open>
val _ = File.write (Path.explode "ready-efd0f5a0df0e402fa1fd0f77a36eec67") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
