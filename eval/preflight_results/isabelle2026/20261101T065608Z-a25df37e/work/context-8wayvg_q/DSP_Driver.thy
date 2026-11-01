theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-58248b54a2d44ce98ae7a8ccc97fa367") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
