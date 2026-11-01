theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-2b88a248111343dcb40eb18c37861d83") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
