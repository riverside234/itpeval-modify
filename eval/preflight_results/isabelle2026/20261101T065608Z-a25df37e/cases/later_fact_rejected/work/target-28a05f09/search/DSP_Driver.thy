theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-1d5aefc015a843018b2cfc88013c2d50") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
