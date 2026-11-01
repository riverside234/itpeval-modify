theory DSP_Driver imports DSP_Native "Complex_Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-8a56c687c9bd4345b8d75b89d096560d") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
