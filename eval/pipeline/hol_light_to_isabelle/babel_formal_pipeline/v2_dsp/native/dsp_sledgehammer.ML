(* Isabelle2026 adapter. API/source hashes are checked by runtime.py.
   Use native proof results and sendback XML, never English output or PISA delimiters. *)
structure DSP_Sledgehammer =
struct

exception No_Reconstruction of string;
exception Hammer_Timeout;

fun sendbacks trees =
  maps (fn XML.Elem ((name, _), body) =>
          if name = Markup.sendbackN then [XML.content_of body] else sendbacks body
        | XML.Text _ => []) trees;

(* Active.sendback_markup_command omits its wrapper outside PIDE print mode.
   Enable it only while serializing the native command, then restore the caller's mode. *)
fun proof_commands render =
  Print_Mode.setmp [Print_Mode.PIDE] render () |> YXML.parse_body |> sendbacks;

fun preplayed_commands count (meth, (played as Sledgehammer_Proof_Methods.Played _, facts)) =
      proof_commands (fn () =>
        Sledgehammer_Proof_Methods.one_line_proof_text ((facts, (meth, played)), "", 1, count))
  | preplayed_commands _ _ = [];

fun reconstructions count (Sledgehammer.SH_Some (result, preplayed)) =
      (* Native tactic provers have already executed their proof method and deliberately
         return preferred_methss = (method, []) with no separate preplay results.
         Preserve their own structured command, including any selected local facts.
         DSP_Native still executes it from the saved state and requires target closure. *)
      if null preplayed andalso null (snd (#preferred_methss result)) andalso
         is_none (#outcome result)
      then (proof_commands (fn () => (#message result) NONE), "native_tactic")
      else (maps (preplayed_commands count) preplayed, "preplayed")
  | reconstructions _ _ = ([], "none");

(* Small, goal-driven hints from already available library facts. Keep normal
   fact selection (only=false); do not import theories or manufacture premises.
   Missing names are omitted, and no dataset/target names occur in this policy. *)
fun fact_hints proof =
  let
    val ctxt = Proof.context_of proof;
    val names = Term.add_const_names (Thm.prop_of (#goal (Proof.goal proof))) []
      |> map Long_Name.base_name;
    fun has name = member (op =) names name;
    val wanted =
      (if has "sum" then ["sum_mono", "sum_distrib_left", "sum_distrib_right"] else []) @
      (if has "sum" andalso has "norm" then ["norm_sum", "sum_norm_le"] else []) @
      (if has "case_prod" then ["case_prod_beta'"] else []) @
      (if has "scaleR" andalso has "norm" then ["norm_scaleR"] else []);
  in filter (can (Proof_Context.get_thms ctxt)) wanted end;

fun search report {provers, hammer_timeout, preplay_timeout} state =
  let
    val proof = Toplevel.proof_of state;
    val hints = fact_hints proof;
    val fact_override: Sledgehammer_Fact.fact_override =
      {add = map (fn name => (Facts.named name, [])) hints, del = [], only = false};
    val raw = [("timeout", Real.toString hammer_timeout),
               ("preplay_timeout", Real.toString preplay_timeout),
               (* Imported theory defaults must not switch a proof gap to falsification/abduction. *)
               ("falsify", "false"), ("abduce", "0"),
               ("try0", "false"), ("learn", "false"), ("fact_filter", "mepo"),
               ("isar_proofs", "false"), ("max_proofs", "4")]
      @ (if null provers then [] else [("provers", space_implode " " provers)]);
    val params = Sledgehammer_Commands.default_params (Proof.theory_of proof) raw;
    val goal_text = Syntax.string_of_term (Proof.context_of proof) (Thm.prop_of (#goal (Proof.goal proof)))
      |> YXML.parse_body |> XML.content_of;
    val initial =
      [("resolved_provers", space_implode " " (#provers params)),
       ("added_fact_hints", space_implode " " hints),
       ("fact_hint_policy", "available_sum_norm_facts_v1"),
       ("goal_before_search", goal_text),
       ("native_parameters", Sledgehammer_Prover.string_of_params params),
       ("caller_pide_enabled", Bool.toString (Print_Mode.PIDE_enabled ()))];
    val _ = report initial;
    val messages = Synchronized.var "DSP_Sledgehammer.messages" ([]: string list);
    fun clean message = XML.content_of (YXML.parse_body message);
    fun capture message = Synchronized.change messages (fn previous =>
      if length previous < 32 then clean message :: previous else previous);
    val returned = Exn.capture (fn () => Sledgehammer.run_sledgehammer params
      Sledgehammer_Prover.Normal (SOME capture) 1 fact_override proof) ();
    val captured = [("native_messages", cat_lines (rev (Synchronized.value messages)))];
    val _ = report (initial @ captured);
    val (_, (outcome, message)) = Exn.release returned;
    val count = Thm.nprems_of (#goal (Proof.goal proof));
    val preplayed =
      (case outcome of
        Sledgehammer.SH_Some (_, results) => results
      | _ => []);
    val played_count = length (filter (fn (_, (Sledgehammer_Proof_Methods.Played _, _)) => true
      | _ => false) preplayed);
    val native_outcome = Sledgehammer.short_string_of_sledgehammer_outcome outcome;
    val before_reconstruction = initial @ captured @
      [("native_outcome", native_outcome), ("native_message", clean message),
       ("preplay_count", string_of_int (length preplayed)),
       ("preplayed_count", string_of_int played_count),
       ("preplay_results", cat_lines (map (fn (meth, (played, _)) =>
         Sledgehammer_Proof_Methods.string_of_proof_method [] meth ^ ": " ^
         Sledgehammer_Proof_Methods.string_of_play_outcome played) preplayed))];
    val _ = report before_reconstruction;
    val (raw_candidates, source) = reconstructions count outcome;
    val candidates = distinct (op =) raw_candidates;
    val diagnostics = before_reconstruction @
      [("reconstruction_source", source), ("candidate_count", string_of_int (length candidates))];
    val _ = report diagnostics;
    val _ = (case outcome of Sledgehammer.SH_TimeOut => raise Hammer_Timeout | _ => ());
    val _ = if null candidates then raise No_Reconstruction
      ("native Sledgehammer returned no usable reconstruction; outcome=" ^ native_outcome ^
       ", preplays=" ^ string_of_int (length preplayed) ^
       ", played=" ^ string_of_int played_count ^ ", source=" ^ source) else ();
  in
    (candidates, diagnostics)
  end;

end;
