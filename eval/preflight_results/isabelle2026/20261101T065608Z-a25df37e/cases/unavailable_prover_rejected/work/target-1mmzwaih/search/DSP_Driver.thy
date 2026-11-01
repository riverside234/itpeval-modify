theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-bf4e048cbf2942b3a7fff90adf033cf1") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
