theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-7aaa8925d59043c08cc9a152bc96e287") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
