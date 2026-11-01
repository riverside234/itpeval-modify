theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-1bf6d73f8af4490d948a1375c2959faa") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
