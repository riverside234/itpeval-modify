theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-1bbe7f3df5ff4298b215e3eab35e9b66") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
