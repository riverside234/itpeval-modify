theory DSP_Driver imports DSP_Native "Complex_Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-0a49d92abdab46c6b199f902f622cbfd") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
