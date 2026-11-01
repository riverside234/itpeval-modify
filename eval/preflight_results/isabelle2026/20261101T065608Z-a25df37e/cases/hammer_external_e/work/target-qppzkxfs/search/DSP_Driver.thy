theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-09cccfa669874af78d96430daa3d6236") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
