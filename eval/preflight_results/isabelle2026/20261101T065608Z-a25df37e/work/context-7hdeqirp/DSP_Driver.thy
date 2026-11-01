theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-3f00441d08374e688fc721be9986156c") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
