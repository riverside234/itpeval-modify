theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-ac83afe6c42e4bafaf88ed225fc20309") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
