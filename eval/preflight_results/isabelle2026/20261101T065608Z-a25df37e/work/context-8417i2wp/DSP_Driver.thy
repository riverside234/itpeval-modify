theory DSP_Driver imports DSP_Native "Lattices" "Boolean_Algebras"
begin
ML \<open>
val _ = File.write (Path.explode "ready-df6f80334f8c464b8636b277b8269cdb") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
