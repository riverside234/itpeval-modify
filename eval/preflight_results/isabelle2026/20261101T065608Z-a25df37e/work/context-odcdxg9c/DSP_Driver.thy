theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-b8534b41d7704a6f847026bd2256111f") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
