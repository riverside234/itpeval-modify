theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-4ae351fd0fd24fe1a3c109b2d9627193") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
