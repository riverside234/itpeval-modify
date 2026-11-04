theory DSP_Reconstruction_Test
  imports DSP_Native
begin

(* Typed adapter fixtures test command transport, not theorem truth.
   The native control tests separately require actual search, gap closure and target completion. *)
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
      val fresh = DSP_Native.begin_context_theory \<^theory>
        "theory DSP_Context_Resource_Test imports Main begin";
      val _ = expect "context master directory is the current job, not its parent heap"
        (Path.implode (Resources.master_directory \<^theory>))
        (Path.implode (Resources.master_directory fresh));
      val keywords = Thy_Header.get_keywords \<^theory>;
      fun transitions source = Outer_Syntax.parse_text \<^theory>
        (fn () => {skip_theory = false, theory = \<^theory>}) Position.start source;
      fun open_test_goal source = fold Toplevel.command_exception (transitions source)
        (Toplevel.make_state (SOME (Context.Theory \<^theory>)));
      val _ = List.app (fn message => expect "ordinary method failure is recoverable" true
        (DSP_Native.recoverable_terminal_error message))
        ["Failed to apply initial proof method (line 12): goal (1 subgoal)",
         "Failed to apply terminal proof method (line 12): goal (1 subgoal)",
         "Failed to finish proof: goal (1 subgoal)"];
      val _ = List.app (fn message => expect "syntax/name/structure errors are not repaired" false
        (DSP_Native.recoverable_terminal_error message))
        ["Undefined fact: target", "Undefined method: unknown", "Outer syntax error",
         "Failed to refine any pending goal", "Timeout after 10.0s",
         "Undefined fact: Failed to finish proof"];
      val plain_goal = open_test_goal "lemma dsp_plain_goal: True";
      val _ = expect "unrelated goals get no sum/norm hints" []
        (DSP_Sledgehammer.fact_hints (Toplevel.proof_of plain_goal));
      val pair_goal = open_test_goal
        "lemma dsp_pair_goal: \"(\\<Sum>(x,y)\\<in>A. (x::nat) + y) = (\\<Sum>z\\<in>A. fst z + snd z)\"";
      val _ = expect "pair binder is detected in the typed goal" true
        (DSP_Native.has_pair_binder pair_goal);
      val hints = DSP_Sledgehammer.fact_hints (Toplevel.proof_of pair_goal);
      val _ = expect "pair rewrite is an available hint" true (member (op =) hints "case_prod_beta'");
      val _ = expect "sum monotonicity is an available hint" true (member (op =) hints "sum_mono");
      val _ = expect "hints stay bounded" true (length hints <= 7);
      val using_steps = transitions "using local_fact (* comment *)\n by metis\n";
      val _ = expect "using/by has an ignored separator" true
        (exists Toplevel.is_ignored using_steps);
      val _ = List.app DSP_Native.check_reconstruction_transition using_steps;
      val _ = List.app DSP_Native.check_reconstruction_transition
        (transitions "unfolding local_def\n apply simp\n done\n");
      val _ = List.app (fn tr => expect "unsafe transition remains rejected" true
          (case Exn.capture DSP_Native.check_reconstruction_transition tr of
            Exn.Exn (DSP_Native.Failure ("missing_reconstruction", _)) => true | _ => false))
        [Toplevel.malformed Position.none "fixture malformed span",
         Toplevel.make {name = "sorry", kind = "", is_begin = false, pos = Position.none}];

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
        (fn () => Time.sleep (Time.fromSeconds 2)) ()) ();
      val _ = expect "ordinary ML timeout is enforced" true
        (case slow of Exn.Exn (Timeout.TIMEOUT _) => true | _ => false);
      val local_timeout = Exn.capture (fn () => DSP_Native.candidate_timeout (K 10.0) 0.01
        (fn () => Time.sleep (Time.fromSeconds 2)) ()) ();
      val _ = expect "optional method timeout is a candidate failure" true
        (case local_timeout of Exn.Exn (DSP_Native.Candidate_Timeout _) => true | _ => false);
      val terminal_timeout = Exn.capture (fn () => DSP_Native.terminal_timeout (K 10.0) 0.01
        (fn () => Time.sleep (Time.fromSeconds 2)) ()) ();
      val _ = expect "terminal by timeout is separately classified" true
        (case terminal_timeout of Exn.Exn (DSP_Native.Terminal_Timeout _) => true | _ => false);
      val _ = expect "unavailable norm heuristic is skipped in HOL-only context" false
        (DSP_Native.heuristic_available pair_goal "by (simp only: case_prod_beta' norm_sum)");
      val _ = expect "ordinary heuristic remains available" true
        (DSP_Native.heuristic_available pair_goal "by simp");
      val budget_left = Unsynchronized.ref 10.0;
      val exhausted = Exn.capture (fn () => DSP_Native.candidate_timeout (fn () => !budget_left) 0.1
        (fn () => (budget_left := 0.0; raise Timeout.TIMEOUT Time.zeroTime)) ()) ();
      val _ = expect "target deadline cannot become a candidate retry" true
        (case exhausted of Exn.Exn (DSP_Native.Failure ("timeout", _)) => true | _ => false);
      val _ = entered := false;
      val tiny_candidate = Exn.capture (fn () => DSP_Native.candidate_timeout (K 0.000001) 1.0
        (fn () => entered := true) ()) ();
      val _ = expect "candidate respects submillisecond whole budget" true
        (case tiny_candidate of Exn.Exn (DSP_Native.Failure ("timeout", _)) => true | _ => false);
      val _ = expect "exhausted candidate body was not entered" false (!entered);
      val interrupted = Exn.capture (fn () => DSP_Native.candidate_timeout (K 10.0) 1.0
        (fn () => raise Exn.Interrupt_Break) ()) ();
      val _ = expect "external interrupt is never a retryable timeout" true
        (case interrupted of Exn.Exn exn => Exn.is_interrupt_proper exn | _ => false);
      val _ = budget_left := 10.0;
      val terminal_exhausted = Exn.capture (fn () => DSP_Native.terminal_timeout (fn () => !budget_left) 0.1
        (fn () => (budget_left := 0.0; raise Timeout.TIMEOUT Time.zeroTime)) ()) ();
      val _ = expect "whole-target timeout cannot become terminal repair" true
        (case terminal_exhausted of Exn.Exn (DSP_Native.Failure ("timeout", _)) => true | _ => false);
      val terminal_interrupted = Exn.capture (fn () => DSP_Native.terminal_timeout (K 10.0) 1.0
        (fn () => raise Exn.Interrupt_Break) ()) ();
      val _ = expect "terminal repair never catches external interrupts" true
        (case terminal_interrupted of Exn.Exn exn => Exn.is_interrupt_proper exn | _ => false);
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
