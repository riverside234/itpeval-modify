theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-c38468439937466687683de5b0d63ae6") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
