theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-8c4b34abc51842eb81db5d0d99d7b7b3") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
