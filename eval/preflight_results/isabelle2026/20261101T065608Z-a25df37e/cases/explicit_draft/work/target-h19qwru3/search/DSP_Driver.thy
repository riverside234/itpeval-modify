theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-77d992ae31524145a7304a2d3e190ba9") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
