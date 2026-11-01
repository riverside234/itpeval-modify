theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-354ee8b9f5a14967b722487ef4cb157b") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
