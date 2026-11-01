theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-d605797f237749bd935a3c3418af78b7") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
