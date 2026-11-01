theory DSP_Driver imports DSP_Native "Complex_Main" "HOL-Combinatorics.Permutations"
begin
ML \<open>
val _ = File.write (Path.explode "ready-d7a6a09c942e4d3f81a120bc7dc95cf1") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
