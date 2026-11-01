theory DSP_Driver imports DSP_Native "Lebesgue_Measure" "Tagged_Division" "HOL-Real_Asymp.Real_Asymp"
begin
ML \<open>
val _ = File.write (Path.explode "ready-b0bba28ce72642c5bc8d18a771a806eb") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
