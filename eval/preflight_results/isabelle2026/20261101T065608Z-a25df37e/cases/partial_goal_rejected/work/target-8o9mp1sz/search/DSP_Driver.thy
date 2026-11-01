theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-00ca00acaf37477596bc475fa57bbf39") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
