theory DSP_Native
  imports Main
begin

(* Trusted infrastructure only: no dataset theories or target facts are imported. *)
ML_file "dsp_sledgehammer.ML"
ML_file "dsp_native.ML"

end
