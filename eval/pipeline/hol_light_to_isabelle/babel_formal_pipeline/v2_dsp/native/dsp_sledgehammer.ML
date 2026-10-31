(* Isabelle2026 adapter. API/source hashes are checked by runtime.py.
   Use native preplay results and sendback XML, never English output or PISA delimiters. *)
structure DSP_Sledgehammer =
struct

exception No_Reconstruction;
exception Hammer_Timeout;

fun sendbacks trees =
  maps (fn XML.Elem ((name, _), body) =>
          if name = Markup.sendbackN then [XML.content_of body] else sendbacks body
        | XML.Text _ => []) trees;

fun search {provers, hammer_timeout, preplay_timeout} state =
  let
    val proof = Toplevel.proof_of state;
    val raw = [("timeout", Real.toString hammer_timeout),
               ("preplay_timeout", Real.toString preplay_timeout),
               ("try0", "false"), ("learn", "false"), ("fact_filter", "mepo"),
               ("isar_proofs", "false"), ("max_proofs", "4")]
      @ (if null provers then [] else [("provers", space_implode " " provers)]);
    val params = Sledgehammer_Commands.default_params (Proof.theory_of proof) raw;
    val (_, (outcome, _)) = Sledgehammer.run_sledgehammer params
      Sledgehammer_Prover.Normal (SOME (K ())) 1 Sledgehammer_Fact.no_fact_override proof;
    val count = Thm.nprems_of (#goal (Proof.goal proof));
    fun reconstruct (meth, (played as Sledgehammer_Proof_Methods.Played _, facts)) =
          Sledgehammer_Proof_Methods.one_line_proof_text ((facts, (meth, played)), "", 1, count)
          |> YXML.parse_body |> sendbacks
      | reconstruct _ = [];
    val candidates =
      (case outcome of
        Sledgehammer.SH_Some (_, preplayed) => maps reconstruct preplayed
      | Sledgehammer.SH_TimeOut => raise Hammer_Timeout
      | _ => []);
    val _ = if null candidates then raise No_Reconstruction else ();
  in
    (distinct (op =) candidates,
     [("resolved_provers", space_implode " " (#provers params)),
      ("native_parameters", Sledgehammer_Prover.string_of_params params),
      ("native_outcome", Sledgehammer.short_string_of_sledgehammer_outcome outcome)])
  end;

end;
