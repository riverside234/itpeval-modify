theory DSP_Driver imports DSP_Native "Complex_Main" "HOL-Library.FuncSet"
begin
ML \<open>
val _ = File.write (Path.explode "ready-9df5b00adafa464f8b9dfc120b7dfd53") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
