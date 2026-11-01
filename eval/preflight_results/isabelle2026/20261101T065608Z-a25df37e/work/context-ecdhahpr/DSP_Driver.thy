theory DSP_Driver imports DSP_Native "Complex_Main" "HOL-Library.FuncSet"
begin
ML \<open>
val _ = File.write (Path.explode "ready-988885518aca4fd2ac727c71d0e58108") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
