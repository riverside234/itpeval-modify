theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-14b90be9ee8948a4b19e1be2fc18f681") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
