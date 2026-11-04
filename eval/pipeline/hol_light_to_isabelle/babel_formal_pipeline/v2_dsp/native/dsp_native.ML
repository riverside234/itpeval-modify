(* Trusted full-session state/search orchestration for individual targets.
   Ordered heuristics follow albertqjiang/draft_sketch_prove commit 647aa65.
   See ../UPSTREAM_LICENSE.txt for attribution. *)
structure DSP_Native =
struct

exception Failure of string * string;
exception Candidate_Timeout of Time.time;
exception Terminal_Timeout of Time.time;
val allowed = space_explode " "
  "proof qed by apply apply_end done prefer defer back supply using unfolding have show thus hence assume presume fix obtain guess let note from with then next case moreover ultimately also finally interpret include including write consider define subgoal { } . ..";

(* Token.source_of is compact internal text with DEL padding for removed
   delimiters. Token.unparse restores executable strings/cartouches and comments. *)
fun source_text span = implode (map Token.unparse span);
fun goal_of state = #goal (Proof.goal (Toplevel.proof_of state));
fun subgoal_count state = Thm.nprems_of (goal_of state);
fun has_pair_binder state =
  member (op =) (Term.add_const_names (Thm.prop_of (goal_of state)) [])
    \<^const_name>\<open>case_prod\<close>;
fun closes_obligation saved next =
  not (Toplevel.is_proof next) orelse Toplevel.proof_level next < Toplevel.proof_level saved;

fun fail category message = raise Failure (category, message);
(* Isabelle ignores sub-millisecond timeouts: never turn an almost exhausted
   whole-target budget into an unbounded operation. *)
fun checked_timeout seconds f arg =
  let val timeout = Time.fromReal seconds
  in if seconds <= 0.0 orelse Timeout.ignored timeout then
       fail "timeout" "native budget below Isabelle's one-millisecond timeout resolution"
     else Timeout.apply timeout f arg
  end;

(* Optional methods run transactionally from the saved proof state. A local
   timeout rejects only that candidate; structural source commands still use
   checked_timeout and abort. Only Timeout.TIMEOUT is converted: external
   interrupts and an exhausted whole-target budget must never become retries. *)
fun candidate_timeout remaining seconds f arg =
  let val budget = Real.min (seconds, remaining ())
  in checked_timeout budget f arg
    handle Timeout.TIMEOUT elapsed =>
      if remaining () < 0.001 then fail "timeout" "whole-target deadline exceeded"
      else raise Candidate_Timeout elapsed
  end;

(* A terminal by method is also transactional. Keep its timeout distinct from
   optional candidates and catch it only at the proof_step repair boundary. *)
fun terminal_timeout remaining seconds f arg =
  candidate_timeout remaining seconds f arg
    handle Candidate_Timeout elapsed => raise Terminal_Timeout elapsed;

(* Avoid known optional candidates whose methods/facts are absent from imports.
   Source commands are never filtered; missing source names remain errors. *)
fun heuristic_available state command =
  let
    val ctxt = Toplevel.context_of state;
    val (methods, facts) =
      (case command of
        "by sos" => (["sos"], [])
      | "by (simp only: case_prod_beta' norm_sum)" => ([], ["case_prod_beta'", "norm_sum"])
      | "by (simp only: norm_scaleR; metis abs_of_nonneg mult_right_mono mult.commute)" =>
          ([], ["norm_scaleR", "abs_of_nonneg", "mult_right_mono", "mult.commute"])
      | _ => ([], []));
  in forall (fn name => can (Method.check_name ctxt) (name, Position.none)) methods andalso
     forall (can (Proof_Context.get_thms ctxt)) facts end;

(* Inspect decoded Isabelle names, not their surface spelling. Quoting or
   qualifying a method must not bypass the no-ML/no-admission policy. *)
fun check_proof_tokens span =
  let
    val forbidden = space_explode " "
      "tactic raw_tactic Skip_Proof skip_proof cheat quick_and_dirty smt_oracle";
    fun check token =
      if member (op =) [Token.Ident, Token.Long_Ident, Token.String] (Token.kind_of token)
         andalso Long_Name.is_identifier (Token.content_of token)
         andalso member (op =) forbidden (Long_Name.base_name (Token.content_of token))
      then fail "rejected_proof" ("forbidden proof method or setting: " ^ Token.content_of token)
      else ();
  in List.app check span end;

(* Reject a copy of a theory already loaded through a parent/import, before
   duplicate declarations or inherited target facts can affect the prefix. *)
fun check_imported_target driver_theory name =
  if exists (fn thy => Context.theory_base_name thy = name) (Theory.ancestors_of driver_theory)
  then fail "context_error"
    ("selected target theory is already inherited from the parent/imports: " ^ name)
  else ();

(* Whitespace/comments between reconstructed commands produce <ignored>
   transitions, not an empty command name. Never broaden the command allowlist
   to malformed or arbitrary outer syntax. *)
fun check_reconstruction_transition tr =
  if Toplevel.is_ignored tr orelse
     member (op =) ["using", "unfolding", "by", "apply", "prefer", "done"] (Toplevel.name_of tr)
  then ()
  else fail "missing_reconstruction"
    ("unsafe reconstructed command: " ^ quote (Toplevel.name_of tr));

fun elem name attrs body = XML.Elem ((name, attrs), body);
fun clean value = XML.content_of (YXML.parse_body value);
fun text name value = elem name [] [XML.Text (clean value)];
(* Retry only ordinary terminal-method failure. Parse/name/type errors, rejected
   commands, interrupts and Isar structural errors remain fatal. Local terminal
   timeouts take the separate typed Terminal_Timeout path, never text matching. *)
fun recoverable_terminal_error message =
  exists (fn prefix => String.isPrefix prefix (clean message))
    ["Failed to apply initial proof method", "Failed to apply terminal proof method",
     "Failed to finish proof"];
fun attr attrs name =
  (case AList.lookup (op =) attrs name of SOME s => s | NONE => fail "protocol_error" ("missing " ^ name));
fun child nodes name =
  (case filter (fn XML.Elem ((n, _), _) => n = name | _ => false) nodes of
    [XML.Elem (_, body)] => body
  | _ => fail "protocol_error" ("missing or repeated field " ^ name));
fun value nodes name = XML.content_of (child nodes name);
fun values nodes name = map (fn XML.Elem (("item", _), body) => XML.content_of body
  | _ => fail "protocol_error" "bad item") (child nodes name);
fun number nodes name =
  (case Real.fromString (value nodes name) of SOME n => n | NONE => fail "protocol_error" ("bad " ^ name));
fun integer nodes name =
  (case Int.fromString (value nodes name) of SOME n => n | NONE => fail "protocol_error" ("bad " ^ name));

(* A fresh theory must use its job's source directory. Theory.begin_theory
   alone inherits the first parent's master directory (the infrastructure heap),
   which makes relative ML_file loads fail even when their files are staged. *)
fun begin_context_theory driver_theory prefix =
  let
    val header = Thy_Header.read Position.none prefix;
    val (name, pos) = #name header;
    val directory = Resources.master_directory driver_theory;
    val source: Resources.thy =
      {name = {node = Path.implode (directory + Path.basic (name ^ ".thy")),
               master_dir = directory, theory = name},
       pos = pos, imports = [], options = [], keywords = #keywords header,
       condition_bad = (false, ""), errors = [], initiators = []};
  in Resources.begin_theory source (Theory.parents_of driver_theory) end;

fun run driver_theory request_file result_file =
  let
    val (attrs, nodes) =
      (case XML.parse (File.read (Path.explode request_file)) of
        XML.Elem (("dsp_request", attrs), nodes) => (attrs, nodes)
      | _ => fail "protocol_error" "bad request root");
    val _ = if attr attrs "schema" = "dsp_native_request_v1" then ()
            else fail "protocol_error" "unsupported request version";
    val id = attr attrs "request_id";
    val digest = attr attrs "input_sha256";
    val action = attr attrs "action";
    val _ = if member (op =) ["context", "search"] action then () else fail "protocol_error" "bad action";
    val attempts = Unsynchronized.ref ([]: XML.tree list);
    val settings = Unsynchronized.ref ([]: (string * string) list);
    val serial = Unsynchronized.ref 0;
    val state_serial = Unsynchronized.ref 0;
    val target_closed = Unsynchronized.ref false;
    val reconstructed = Unsynchronized.ref "";
    val stage = Unsynchronized.ref "context_error";
    val timer = Timer.startRealTimer ();
    val whole_budget = number nodes "remaining_s";
    val step_budget = number nodes "step_timeout_s";
    val context_budget = number nodes "context_step_timeout_s";
    (* Leave room for bounded normalization, search, preplay and reconstruction
       instead of spending the remaining target budget on optional heuristics. *)
    val hammer_reserve = number nodes "hammer_timeout_s" +
      number nodes "preplay_timeout_s" + 2.0 * step_budget;
    val last_error = Unsynchronized.ref "";
    fun remaining () = whole_budget - Time.toReal (Timer.checkRealTimer timer);
    fun bounded seconds f arg =
      let val budget = Real.min (seconds, remaining ())
      in if budget <= 0.0 then fail "timeout" "whole-target deadline exceeded"
         else checked_timeout budget f arg end;
    fun init () =
      {skip_theory = false,
       theory = begin_context_theory driver_theory (value nodes "prefix")};
    fun spans state source =
      let
        val thy = if Toplevel.is_toplevel state then driver_theory else Toplevel.theory_of state;
        val keywords = Thy_Header.get_keywords thy;
      in Token.explode keywords Position.start source
         |> Outer_Syntax.parse_spans (Keyword.command_kind keywords)
         |> map Command_Span.content end;
    fun transition state span =
      let val thy = if Toplevel.is_toplevel state then driver_theory else Toplevel.theory_of state
      in Outer_Syntax.parse_span thy init span end;
    fun record_attempt mode command line source_state started success error_message extra_attrs =
      let
        val _ = serial := !serial + 1;
        val row = elem "attempt"
          ([("mode", mode), ("success", Bool.toString success), ("index", string_of_int (!serial)),
            ("line", string_of_int line), ("source_state", string_of_int source_state),
            ("duration_seconds", Time.toString (Timer.checkRealTimer started))] @ extra_attrs)
          [text "command" command, text "error" error_message];
      in attempts := row :: !attempts end;
    fun attempt mode command line execute =
      let
        val started = Timer.startRealTimer ();
        val source_state = !state_serial;
        val result = Exn.capture execute ();
        val success = (case result of Exn.Res _ => true | _ => false);
        val error_message = (case result of
            Exn.Exn (Candidate_Timeout elapsed) => Timeout.message elapsed
          | Exn.Exn (Terminal_Timeout elapsed) => Timeout.message elapsed
          | Exn.Exn exn => Runtime.exn_message exn | _ => "");
        val timeout_attrs = (case result of
            Exn.Exn (Candidate_Timeout _) => [("timeout_scope", "candidate")]
          | Exn.Exn (Terminal_Timeout _) => [("timeout_scope", "terminal_method")]
          | _ => []);
        val _ = last_error := error_message;
        val _ = record_attempt mode command line source_state started success error_message timeout_attrs;
      in
        (case result of
          Exn.Res state => SOME state
        | Exn.Exn (Candidate_Timeout _) => NONE
        | Exn.Exn (exn as Terminal_Timeout _) => Exn.reraise exn
        | Exn.Exn (Failure ("timeout", message)) => fail "timeout" message
        | Exn.Exn (Timeout.TIMEOUT _) => fail "timeout" "native operation timed out; isolated job aborted"
        | Exn.Exn DSP_Sledgehammer.Hammer_Timeout => fail "timeout" "native Sledgehammer timed out"
        | Exn.Exn (DSP_Sledgehammer.No_Reconstruction message) => fail "missing_reconstruction" message
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else NONE)
      end;
    fun execute mode state span =
      let
        val tr = transition state span;
        val command = source_text span;
        val line = the_default 1 (Position.line_of (Toplevel.pos_of tr));
        val run_command =
          if mode = "search" andalso Toplevel.name_of tr = "by" andalso Toplevel.is_proof state
          then terminal_timeout remaining step_budget
          else bounded (if mode = "context" then context_budget else step_budget);
      in
        (case attempt mode command line
          (fn () => run_command (Toplevel.command_exception tr) state) of
          SOME next => (state_serial := !state_serial + 1; next)
        | NONE => fail (!stage) ("failed command: " ^ command ^ "\n" ^ !last_error))
      end;
    fun execute_text mode state source = fold (fn span => fn st => execute mode st span) (spans state source) state;
    fun ensure_real state =
      if Toplevel.is_skipped state orelse Toplevel.is_skipped_proof state
      then fail "rejected_proof" "skipped target/intermediate proof" else state;
    fun candidate mode allow_partial saved proof =
      let
        val level = Toplevel.proof_level saved;
        fun apply_candidate () =
          let
            fun step span st =
              let
                val _ = check_proof_tokens span;
                val tr = transition st span;
                val _ = check_reconstruction_transition tr;
              in ensure_real (Toplevel.command_exception tr st) end;
            val next = candidate_timeout remaining step_budget
              (fn () => fold step (spans saved proof) saved) ();
            (* Only the fixed normalization below may retain a changed goal with
               the same subgoal count. Heuristics must still close it; ordinary
               reconstructions must still strictly reduce the pending obligations. *)
            val normalized = mode = "normalization" andalso Toplevel.is_proof next andalso
              Toplevel.proof_level next = level andalso subgoal_count next <= subgoal_count saved andalso
              not (Thm.eq_thm_prop (goal_of saved, goal_of next));
            val progress = closes_obligation saved next orelse normalized orelse
              (allow_partial andalso Toplevel.is_proof next andalso
               Toplevel.proof_level next = level andalso subgoal_count next < subgoal_count saved);
            val _ = if progress then ()
                    else fail "incomplete_obligation" "candidate made no permitted progress on the pending obligation";
          in next end;
      in attempt mode proof 0 apply_candidate end;
    fun choose _ _ _ [] = NONE
      | choose mode allow_partial state (proof :: rest) =
          if mode = "heuristic" andalso remaining () <= hammer_reserve + step_budget
          then NONE
          else if mode = "heuristic" andalso not (heuristic_available state proof)
          then choose mode allow_partial state rest
          else (case candidate mode allow_partial state proof of SOME next => SOME (proof, next)
            | NONE => choose mode allow_partial state rest);
    fun normalize_for_hammer state =
      if has_pair_binder state then
        (* Use the kernel-checked apply command, and retain it in the final proof.
           This changes only pair syntax; scalar norms are intentionally untouched.
           apply also consumes chained facts normally, without losing their premises. *)
        choose "normalization" false state ["apply (simp only: case_prod_beta')"]
      else NONE;
    fun gap try_heuristics initial =
      let
        val _ = Proof.assert_backward (Toplevel.proof_of initial);
        fun solve state chunks =
          if closes_obligation initial state then (cat_lines (rev chunks), state)
          else
            let
              (* Do not report a previous gap's hammer success for this state. *)
              val _ = settings := [];
              fun continue (proof, next) =
                (state_serial := !state_serial + 1; solve next (proof :: chunks));
            in
              if subgoal_count state = 0 then
                (* An apply command may solve every subgoal without ending the proof. *)
                (case choose "reconstruction" false state ["done"] of
                  SOME selected => continue selected
                | NONE => fail "incomplete_obligation" "could not finish the solved obligation")
              else
                (case choose "heuristic" false state (if try_heuristics then values nodes "heuristics" else []) of
                  SOME selected => continue selected
                | NONE =>
                  (case normalize_for_hammer state of
                    SOME normalized => continue normalized
                  | NONE =>
                    let
                      val budget = number nodes "hammer_timeout_s";
                      val config = {provers = values nodes "provers", hammer_timeout = budget,
                                    preplay_timeout = number nodes "preplay_timeout_s"};
                      val returned = Unsynchronized.ref (NONE: (string list * (string * string) list) option);
                      val found = attempt "hammer" "native Sledgehammer" 0 (fn () =>
                        (returned := SOME (bounded (budget + #preplay_timeout config)
                            (DSP_Sledgehammer.search (fn params => settings := params) config) state); state));
                      val (candidates, params) =
                        (case (found, !returned) of
                          (SOME _, SOME result) => result
                        | _ => fail "hammer_failure" "native Sledgehammer returned no executable reconstruction");
                      val _ = settings := params;
                    in
                      (* Isabelle emits apply, not by, when more than one subgoal
                         remains. Accept only strict progress, then solve the rest;
                         the placeholder succeeds only when its entire obligation closes. *)
                      (case choose "reconstruction" true state candidates of
                        SOME selected => continue selected
                      | NONE => fail "missing_reconstruction" "all native reconstructions failed to make progress")
                    end))
            end;
      in solve initial [] end;
    fun check_proof_span span =
      let
        val _ = check_proof_tokens span;
        val proper = filter Token.is_proper span;
        val name = (case proper of [] => "" | t :: _ => Token.content_of t);
      in
        if name = "sledgehammer" then
          if length proper = 1 then true else fail "sketch_parse_error" "sledgehammer must be standalone"
        else if name = "" orelse member (op =) allowed name then false
        else fail "rejected_proof" ("forbidden proof command: " ^ name)
      end;
    fun proof_step span (state, chunks) =
      if check_proof_span span then
        let val (proof, next) = gap true state
        in (ensure_real next, chunks @ [proof ^ "\n"]) end
      else
        let
          val tr = transition state span;
          val command = source_text span;
          val attempted = Exn.capture (fn () => ensure_real (execute "search" state span)) ();
          fun repair reason try_heuristics =
            let
              val started = Timer.startRealTimer ();
              val source_state = !state_serial;
              (* Immutable saved state: discard all progress from the failed by.
                 gap must close this exact obligation before the next source span. *)
              val outcome = Exn.capture (gap try_heuristics) state;
              val success = (case outcome of Exn.Res _ => true | _ => false);
              val message = (case outcome of Exn.Exn exn => Runtime.exn_message exn | _ => "");
              val _ = record_attempt "terminal_repair" command
                (the_default 1 (Position.line_of (Toplevel.pos_of tr)))
                source_state started success message [("repair_reason", reason)];
              val (proof, next) = Exn.release outcome;
            in (ensure_real next, chunks @ [proof ^ "\n"]) end;
        in
          (case attempted of
            Exn.Res next => (next, chunks @ [command])
          | Exn.Exn (exn as Failure ("sketch_step_failure", _)) =>
              if Toplevel.name_of tr = "by" andalso Toplevel.is_proof state andalso
                 recoverable_terminal_error (!last_error)
              then repair "method_failure" true else Exn.reraise exn
          | Exn.Exn (Terminal_Timeout _) =>
              (* Do not retry the expensive source method or another heuristic
                 portfolio: give native Hammer the remaining bounded opportunity. *)
              repair "method_timeout" false
          | Exn.Exn exn => Exn.reraise exn)
        end;
    fun work () =
      let
        val prefix = value nodes "prefix";
        val original_name = #1 (#name (Thy_Header.read Position.none prefix));
        val _ = check_imported_target driver_theory original_name;
        val prefix_spans = spans (Toplevel.make_state NONE) prefix;
        fun prepare span state =
          let
            val tr = transition state span;
            val next = execute "context" state span;
          in if Toplevel.name_of tr = "theory" then
               execute_text "context" next "declare [[quick_and_dirty = true]]"
             else next end;
        val context = fold prepare prefix_spans (Toplevel.make_state NONE);
        val _ = if Toplevel.is_proof context then fail "context_error" "prefix leaves an open proof" else ();
        (* Detect the target and unambiguous later names already present in context.
           The request excludes later basenames also used by earlier scoped helpers;
           no later source is executed, and the ancestor guard above still applies. *)
        val ctxt = Toplevel.context_of context;
        val _ = List.app (fn name =>
          let val qualified = distinct (op =) [original_name ^ "." ^ name,
                                              Proof_Context.full_name ctxt (Binding.name name)]
          in if exists (can (Proof_Context.get_thms ctxt)) qualified then
               fail "context_error" ("target or later fact leaked into the input context: " ^ name)
             else () end) (values nodes "forbidden_names");
        val clean = execute_text "context" context "declare [[quick_and_dirty = false, smt_oracle = false]]";
        val opened = execute_text "target" clean (value nodes "statement" ^ "\n" ^ value nodes "proof_prefix");
        val _ = if Toplevel.is_proof opened andalso not (Toplevel.is_skipped opened) then ()
                else fail "context_error" "oracle did not open a real target proof";
      in
        if action = "context" then ()
        else
          let
            val _ = stage := "sketch_step_failure";
            val source = value nodes "sketch";
            val (finished, chunks) = fold proof_step (spans opened source) (opened, []);
            val _ = if Toplevel.is_proof finished orelse Toplevel.is_skipped finished then
                      fail "incomplete_proof" "selected target did not finish its own proof" else ();
            val _ = reconstructed := implode chunks;
            val closed = fold (fn _ => fn st => execute_text "close_scope" st "end")
              (1 upto integer nodes "depth") finished;
            val _ = if Toplevel.is_end_theory closed then ()
                    else fail "incomplete_proof" "original scopes did not close";
          in target_closed := true end
      end;
    val outcome = Exn.capture work ();
    val (success, category, message) =
      (case outcome of
        Exn.Res _ => (true, "", "")
      | Exn.Exn (Failure (category, message)) => (false, category, message)
      | Exn.Exn (Timeout.TIMEOUT _) => (false, "timeout", "native deadline exceeded")
      | Exn.Exn DSP_Sledgehammer.Hammer_Timeout => (false, "timeout", "native Sledgehammer timeout")
      | Exn.Exn exn => (false, !stage, Runtime.exn_message exn));
    val result = elem "dsp_result"
      [("schema", "dsp_native_result_v1"), ("request_id", id), ("input_sha256", digest),
       ("action", action), ("success", Bool.toString success),
       ("target_closed", Bool.toString (!target_closed))]
      [text "proof" (!reconstructed), text "category" category, text "error" message,
       elem "attempts" [] (rev (!attempts)),
       elem "settings" [] (map (fn (name, value) => elem "param" [("name", name)] [XML.Text value]) (!settings))];
    val _ = File.write (Path.explode result_file) (XML.string_of result);
  in () end;

end;
