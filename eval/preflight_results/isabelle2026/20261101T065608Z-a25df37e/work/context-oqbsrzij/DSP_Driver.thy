theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-d578e85d3c7b47099be52c725e74a6b9") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
