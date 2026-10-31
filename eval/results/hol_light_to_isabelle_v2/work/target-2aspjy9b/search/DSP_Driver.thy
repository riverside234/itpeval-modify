theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-ce60ecee9c93491598b2805d22448cf0") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
