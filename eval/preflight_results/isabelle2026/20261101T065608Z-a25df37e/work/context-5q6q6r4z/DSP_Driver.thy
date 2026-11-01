theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-1cd31f8dddfc442ea49746feae560f66") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
