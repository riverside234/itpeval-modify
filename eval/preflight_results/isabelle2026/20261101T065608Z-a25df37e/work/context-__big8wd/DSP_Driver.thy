theory DSP_Driver imports DSP_Native "Complex_Main" "HOL-Library.More_List" "HOL-Library.Infinite_Set" "Primes"
begin
ML \<open>
val _ = File.write (Path.explode "ready-bcb4d101b99c490c8e8026fee6d9c987") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
