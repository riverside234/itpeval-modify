theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-2ee08bdc5c7747fc950a19aa41bea73a") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
