theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-9c10720c09724040b37c1394e5a2b1ba") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
