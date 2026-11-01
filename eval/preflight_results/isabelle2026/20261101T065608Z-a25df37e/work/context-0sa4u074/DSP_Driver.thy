theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-1d3bc3f4182f418f9491f2f48a40ee0d") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
