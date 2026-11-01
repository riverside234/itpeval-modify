theory DSP_Driver imports DSP_Native "Angles"
begin
ML \<open>
val _ = File.write (Path.explode "ready-2f6e86f9b6324528ae1d0ccf5b271173") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
