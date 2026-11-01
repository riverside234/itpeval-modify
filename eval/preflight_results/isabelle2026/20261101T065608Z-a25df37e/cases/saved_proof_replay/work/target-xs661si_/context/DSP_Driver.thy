theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-73626d2f239e4ac490f11c437e6fa41b") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
