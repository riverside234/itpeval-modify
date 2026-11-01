theory DSP_Driver imports DSP_Native "HOL-Analysis.Multivariate_Analysis"
begin
ML \<open>
val _ = File.write (Path.explode "ready-cce263f8e2204d0eb5413ee8833c2e1f") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
