theory DSP_Driver imports DSP_Native "Euclidean_Algorithm"
begin
ML \<open>
val _ = File.write (Path.explode "ready-eb23f6457a7b481eb114b0c331b32728") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
