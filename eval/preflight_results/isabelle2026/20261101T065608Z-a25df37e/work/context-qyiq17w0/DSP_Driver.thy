theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-0eea274ed30b49e6a763903f8d9dcffa") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
