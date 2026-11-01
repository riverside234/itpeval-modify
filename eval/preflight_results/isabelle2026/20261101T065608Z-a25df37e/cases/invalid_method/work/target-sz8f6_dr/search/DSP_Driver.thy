theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-ecb77658c414490da7a8b593f5514c7b") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
