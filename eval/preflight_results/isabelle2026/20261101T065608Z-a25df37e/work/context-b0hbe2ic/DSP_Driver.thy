theory DSP_Driver imports DSP_Native "Angles"
begin
ML \<open>
val _ = File.write (Path.explode "ready-7d7cf359b7394c7d9a6fdca7cc1b5119") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
