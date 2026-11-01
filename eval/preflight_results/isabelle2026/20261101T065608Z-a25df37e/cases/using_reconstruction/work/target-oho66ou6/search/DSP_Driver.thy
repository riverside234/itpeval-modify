theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-f4c10e2610ec40a180f43adbedf7ac03") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
