theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-de889ec3dc7847b4a1cbf4c9a280effe") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
