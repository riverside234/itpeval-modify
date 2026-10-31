(* Trusted full-session state/search orchestration for individual targets.
   Ordered heuristics follow albertqjiang/draft_sketch_prove commit 647aa65.
   See ../UPSTREAM_LICENSE.txt for attribution. *)
structure DSP_Native =
struct

exception Failure of string * string;
val allowed = space_explode " "
  "proof qed by apply apply_end done prefer defer back supply using unfolding have show thus hence assume presume fix obtain guess let note from with then next case moreover ultimately also finally interpret include including write";

fun fail category message = raise Failure (category, message);
fun elem name attrs body = XML.Elem ((name, attrs), body);
fun clean value = XML.content_of (YXML.parse_body value);
fun text name value = elem name [] [XML.Text (clean value)];
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
    fun bounded seconds f arg =
      let val budget = Real.min (seconds, whole_budget - Time.toReal (Timer.checkRealTimer timer))
      in if budget <= 0.0 then fail "timeout" "whole-target deadline exceeded"
         else Timeout.apply (Time.fromReal budget) f arg end;
    fun init () =
      let
        val header = Thy_Header.read Position.none (value nodes "prefix");
        (* Use completed imported parents, never the currently executing driver theory. *)
        val theory = Theory.begin_theory (#name header) (Theory.parents_of driver_theory)
          |> Thy_Header.add_keywords (#keywords header);
      in {skip_theory = false, theory = theory} end;
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
    fun attempt mode command line execute =
      let
        val started = Timer.startRealTimer ();
        val result = Exn.capture execute ();
        val _ = serial := !serial + 1;
        val success = (case result of Exn.Res _ => true | _ => false);
        val error_message = (case result of Exn.Exn exn => Runtime.exn_message exn | _ => "");
        val row = elem "attempt"
          [("mode", mode), ("success", Bool.toString success), ("index", string_of_int (!serial)),
           ("line", string_of_int line), ("source_state", string_of_int (!state_serial)),
           ("duration_seconds", Time.toString (Timer.checkRealTimer started))]
          [text "command" command, text "error" error_message];
        val _ = attempts := row :: !attempts;
      in
        (case result of
          Exn.Res state => SOME state
        | Exn.Exn (Timeout.TIMEOUT _) => fail "timeout" "native operation timed out; isolated job aborted"
        | Exn.Exn DSP_Sledgehammer.Hammer_Timeout => fail "timeout" "native Sledgehammer timed out"
        | Exn.Exn DSP_Sledgehammer.No_Reconstruction => fail "missing_reconstruction" "no preplayed native reconstruction"
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else NONE)
      end;
    fun execute mode state span =
      let
        val tr = transition state span;
        val command = implode (map Token.source_of span);
        val line = the_default 1 (Position.line_of (Toplevel.pos_of tr));
      in
        (case attempt mode command line
          (fn () => bounded step_budget (Toplevel.command_exception tr) state) of
          SOME next => (state_serial := !state_serial + 1; next)
        | NONE => fail (!stage) ("failed command: " ^ command))
      end;
    fun execute_text mode state source = fold (fn span => fn st => execute mode st span) (spans state source) state;
    fun ensure_real state =
      if Toplevel.is_skipped state orelse Toplevel.is_skipped_proof state
      then fail "rejected_proof" "skipped target/intermediate proof" else state;
    fun candidate mode saved proof =
      let
        val level = Toplevel.proof_level saved;
        fun apply_candidate () =
          let
            fun step span st =
              let
                val tr = transition st span;
                val name = Toplevel.name_of tr;
                val _ = if name = "" orelse member (op =) ["using", "unfolding", "by", "apply", "done"] name then ()
                        else fail "missing_reconstruction" "unsafe reconstructed command";
              in ensure_real (Toplevel.command_exception tr st) end;
            val next = bounded step_budget
              (fn () => fold step (spans saved proof) saved) ();
            val _ = if not (Toplevel.is_proof next) orelse Toplevel.proof_level next < level then ()
                    else fail "incomplete_obligation" "candidate did not close the pending obligation";
          in next end;
      in attempt mode proof 0 apply_candidate end;
    fun choose _ _ [] = NONE
      | choose mode state (proof :: rest) =
          (case candidate mode state proof of SOME next => SOME (proof, next)
          | NONE => choose mode state rest);
    fun gap state =
      (case choose "heuristic" state (values nodes "heuristics") of
        SOME selected => selected
      | NONE =>
          let
            val budget = number nodes "hammer_timeout_s";
            val config = {provers = values nodes "provers", hammer_timeout = budget,
                          preplay_timeout = number nodes "preplay_timeout_s"};
            val returned = Unsynchronized.ref (NONE: (string list * (string * string) list) option);
            val found = attempt "hammer" "native Sledgehammer" 0 (fn () =>
              (returned := SOME (bounded (budget + #preplay_timeout config)
                  (DSP_Sledgehammer.search config) state); state));
            val (candidates, params) =
              (case (found, !returned) of
                (SOME _, SOME result) => result
              | _ => fail "hammer_failure" "native Sledgehammer returned no executable reconstruction");
            val _ = settings := params;
          in
            (case choose "reconstruction" state candidates of
              SOME selected => selected
            | NONE => fail "missing_reconstruction" "all native reconstructions failed to close the obligation")
          end);
    fun check_proof_span span =
      let
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
        let val (proof, next) = gap state
            val _ = state_serial := !state_serial + 1
        in (ensure_real next, chunks @ [proof ^ "\n"]) end
      else
        (ensure_real (execute "search" state span), chunks @ [implode (map Token.source_of span)]);
    fun work () =
      let
        val prefix = value nodes "prefix";
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
        (* Detect target/later facts already present in inherited sessions or prefix. *)
        val ctxt = Toplevel.context_of context;
        val original_name = #1 (#name (Thy_Header.read Position.none prefix));
        val _ = List.app (fn name =>
          let val qualified = distinct (op =) [original_name ^ "." ^ name,
                                              Proof_Context.full_name ctxt (Binding.name name)]
          in if exists (can (Proof_Context.get_thms ctxt)) qualified then
               fail "context_error" ("target or later fact leaked into the input context: " ^ name)
             else () end) (values nodes "forbidden_names");
        val clean = execute_text "context" context "declare [[quick_and_dirty = false]]";
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
