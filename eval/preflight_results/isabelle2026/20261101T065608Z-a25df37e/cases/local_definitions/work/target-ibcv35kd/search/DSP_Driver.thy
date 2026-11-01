theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-c285bb6bcf924272be79e0ddd837d77f") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
