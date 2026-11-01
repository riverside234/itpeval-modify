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
      val _ = expect "multi-subgoal preplay retains the apply command"
        (["apply simp"], "preplayed")
        (DSP_Sledgehammer.reconstructions 2 (Sledgehammer.SH_Some (external, [played])));
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
      val keywords = Thy_Header.get_keywords \<^theory>;
      val quoted = "have h: \"True\" (* keep comment *)\n  by simp";
      val quote_tokens = Token.explode keywords Position.start quoted;
      val _ = expect "old source_of representation loses string delimiters" true
        (String.isSubstring Symbol.DEL (implode (map Token.source_of quote_tokens)));
      val _ = expect "quoted terms and comments survive executable serialization" quoted
        (DSP_Native.source_text quote_tokens);
      val cartouched = "have h: " ^ cartouche "True" ^ "\n  by simp";
      val _ = expect "cartouche delimiters survive executable serialization" cartouched
        (DSP_Native.source_text (Token.explode keywords Position.start cartouched));
      (* Tiny timeouts must fail before evaluating their body, not become
         Isabelle's deliberately unbounded Timeout.apply special case. *)
      val entered = Unsynchronized.ref false;
      val tiny = Exn.capture (fn () => DSP_Native.checked_timeout 0.000001
        (fn () => entered := true) ()) ();
      val _ = expect "submillisecond budget fails closed" true
        (case tiny of Exn.Exn (DSP_Native.Failure ("timeout", _)) => true | _ => false);
      val _ = expect "timed-out body was not entered" false (!entered);
      val slow = Exn.capture (fn () => DSP_Native.checked_timeout 0.01
        (fn () => OS.Process.sleep (Time.fromSeconds 2)) ()) ();
      val _ = expect "ordinary ML timeout is enforced" true
        (case slow of Exn.Exn (Timeout.TIMEOUT _) => true | _ => false);
      fun rejected source =
        (case Exn.capture DSP_Native.check_proof_tokens
            (Token.explode keywords Position.start source) of
          Exn.Exn (DSP_Native.Failure ("rejected_proof", _)) => true
        | _ => false);
      val _ = List.app (fn source => expect "decoded unsafe method/setting" true (rejected source))
        ["by (\"tactic\" " ^ cartouche "all_tac" ^ ")",
         "by (Pure.raw_tactic " ^ cartouche "all_tac" ^ ")",
         "by (\"ta\\099tic\" " ^ cartouche "all_tac" ^ ")",
         "supply [[quick_and_dirty = true]]", "supply [[smt_oracle = true]]"];
      val _ = expect "ordinary quoted methods remain legal" false (rejected "by \"simp\"");
      val _ = expect "mathematical strings are not scanned as ML" false
        (rejected "have \"tactic = tactic\" by simp");
      val _ = expect "qualified names inside formulas are opaque" false
        (rejected "have \"Local.tactic = Local.tactic\" by simp");
      val imported = Exn.capture (DSP_Native.check_imported_target \<^theory>) "Set";
      val _ = expect "inherited theory cannot become a fresh target" true
        (case imported of Exn.Exn (DSP_Native.Failure ("context_error", _)) => true | _ => false);
      val _ = expect "serialization restores the caller's print mode" false
        (Print_Mode.PIDE_enabled ());
    in () end;
in
  val _ = Print_Mode.setmp [] run ();
end;
\<close>

end
