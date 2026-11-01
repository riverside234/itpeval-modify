theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-b6c86f82996e4975bcd9c1d9a3788d97") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
