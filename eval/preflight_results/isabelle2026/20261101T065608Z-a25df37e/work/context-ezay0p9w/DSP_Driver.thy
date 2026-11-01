theory DSP_Driver imports DSP_Native "Square_Matrix" "HOL-Computational_Algebra.Polynomial"
begin
ML \<open>
val _ = File.write (Path.explode "ready-cac47d224bd04037a58800a088d56253") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
