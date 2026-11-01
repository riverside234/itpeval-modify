theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-a7e19dd571cc4b44b0e83430770a2ff0") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
