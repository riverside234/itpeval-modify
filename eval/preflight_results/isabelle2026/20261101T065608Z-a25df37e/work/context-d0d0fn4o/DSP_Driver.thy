theory DSP_Driver imports DSP_Native "Complex_Main" "HOL-Library.FuncSet"
begin
ML \<open>
val _ = File.write (Path.explode "ready-365d9a2525d6400092011ddae396360c") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
