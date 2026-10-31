theory DSP_Reconstruction_Test
  imports DSP_Native
begin

(* Typed adapter fixtures test command transport, not theorem truth.
   The native control tests separately require actual search, gap closure and replay. *)
ML \<open>
local
  open Sledgehammer_Proof_Methods;

  fun expect label wanted actual =
    if actual = wanted then () else error ("Reconstruction regression: " ^ label);

  fun result methods command : Sledgehammer_Prover.prover_result =
    {outcome = NONE, used_facts = [], used_from = [],
     preferred_methss = (Simp_Method, methods), run_time = Time.zeroTime,
     message = fn _ => try_command_line "Native method" (Played Time.zeroTime) command};

  fun run () =
    let
      val played = (Simp_Method, (Played Time.zeroTime, []));
      val external = result [[Simp_Method]] "by simp";
      val tactic = result [] "by simp";
      val plain = one_line_proof_text (([], (Simp_Method, Played Time.zeroTime)), "", 1, 1);
      val _ = expect "fixture reproduces absent sendback in batch mode" []
        (DSP_Sledgehammer.sendbacks (YXML.parse_body plain));
      val _ = expect "played command survives batch mode" (["by simp"], "preplayed")
        (DSP_Sledgehammer.reconstructions 1 (Sledgehammer.SH_Some (external, [played])));
      val _ = expect "already executed tactic has no separate preplay" (["by simp"], "native_tactic")
        (DSP_Sledgehammer.reconstructions 1 (Sledgehammer.SH_Some (tactic, [])));
      val _ = expect "native using command retains its local facts"
        (["using local_fact by metis"], "native_tactic")
        (DSP_Sledgehammer.reconstructions 1
          (Sledgehammer.SH_Some (result [] "using local_fact by metis", [])));
      val _ = expect "external result cannot bypass missing preplay" ([], "preplayed")
        (DSP_Sledgehammer.reconstructions 1 (Sledgehammer.SH_Some (external, [])));
      val _ = expect "failed preplay cannot use the native tactic fallback" ([], "preplayed")
        (DSP_Sledgehammer.reconstructions 1
          (Sledgehammer.SH_Some (tactic, [(Simp_Method, (Play_Failed, []))])));
      val _ = expect "timed-out preplay cannot use the native tactic fallback" ([], "preplayed")
        (DSP_Sledgehammer.reconstructions 1
          (Sledgehammer.SH_Some (tactic, [(Simp_Method, (Play_Timed_Out Time.zeroTime, []))])));
      val _ = expect "native failure yields no reconstruction" ([], "none")
        (DSP_Sledgehammer.reconstructions 1 Sledgehammer.SH_None);
      val _ = expect "serialization restores the caller's print mode" false
        (Print_Mode.PIDE_enabled ());
    in () end;
in
  val _ = Print_Mode.setmp [] run ();
end;
\<close>

end
