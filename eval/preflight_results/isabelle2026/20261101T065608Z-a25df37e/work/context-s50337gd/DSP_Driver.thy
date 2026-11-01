theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-68d2be4a154a4e7cb4726754b105a71e") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
