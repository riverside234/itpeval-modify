theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-da801c2eaf1342cd857ab2a817e2c5fe") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
