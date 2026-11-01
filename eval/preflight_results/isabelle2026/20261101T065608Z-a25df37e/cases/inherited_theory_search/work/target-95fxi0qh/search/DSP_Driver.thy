theory DSP_Driver imports DSP_Native "Main"
begin
ML \<open>
val _ = File.write (Path.explode "ready-f290ef9bb51543bebd9e6d67a91f711a") "ready";
val _ = DSP_Native.run \<^theory> "request.xml" "result.xml";
\<close>
end
