theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-f8da3e8648f340b19460d99b1cfb810f") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
