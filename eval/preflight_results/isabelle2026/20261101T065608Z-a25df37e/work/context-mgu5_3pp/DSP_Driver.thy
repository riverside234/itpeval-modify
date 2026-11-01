theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-44fca1b4a1aa47f8b8f1897b7bb198c4") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
