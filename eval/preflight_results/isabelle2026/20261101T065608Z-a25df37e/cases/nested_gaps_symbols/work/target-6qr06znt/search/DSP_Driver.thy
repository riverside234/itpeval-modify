theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-53544399c8034c48a4604eb77fab8b0f") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
