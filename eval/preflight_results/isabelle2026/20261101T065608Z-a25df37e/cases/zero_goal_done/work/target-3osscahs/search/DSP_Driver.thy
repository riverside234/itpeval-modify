theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-f08f31631dbe439ba1b2bd439687ebc0") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
