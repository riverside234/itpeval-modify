"""Shared, deterministic native acceptance cases. No model-generated proofs or API calls."""
from __future__ import annotations

from dataclasses import asdict, dataclass, replace
from pathlib import Path
import shutil
import time
import uuid

from ..common import fingerprint
from ..sanitize_isabelle import sanitize_target
from .checker import Checker
from .export_dsp import export_record
from .native_search import NativeSearch, build_diagnostics, build_error
from .preflight import control_record
from .runtime import DspConfig, NATIVE_DIR

FIXTURE = NATIVE_DIR / "checks" / "DSP_Reconstruction_Test.thy"


@dataclass
class ProofCase:
    name: str
    record: dict
    provers: tuple[str, ...] | None = None
    force_hammer: bool = False
    expected_failure: str | None = None
    hammer_kind: str | None = None
    min_reconstructions: int = 0
    require_apply: bool = False
    candidate: str | None = None


def proof_cases() -> list[ProofCase]:
    """All controls have explicit expected outcomes, including negative controls."""
    cases = []
    def add(name, proof, *, extra_context="", conclusion="True", mode="draft", **options):
        row = control_record(proof, sketch_source=mode, conclusion=conclusion, extra_context=extra_context)
        cases.append(ProofCase(name, row, **options))
        return row

    add("explicit_draft", "by simp")
    add("explicit_direct", "by simp", mode="hol-light-proof")
    hammer = 'proof -\n show "True"\n sledgehammer\nqed'
    add("hammer_configured", hammer, force_hammer=True, hammer_kind="any")
    add("hammer_native_tactic", hammer, provers=("simp",), force_hammer=True,
        hammer_kind="native_tactic", extra_context="sledgehammer_params [falsify = true, abduce = 1]\n")
    add("hammer_external_e", hammer, provers=("e",), force_hammer=True, hammer_kind="preplayed")
    using = 'proof -\n have h: "True" by simp\n show "True"\n sledgehammer\nqed'
    for name, candidate in (("using_reconstruction", "using h by metis"),
                            ("using_reconstruction_comments", "using h (* separator *)\n by metis\n")):
        add(name, using, candidate=candidate)
    add("nested_gaps_symbols", r"""proof -
 have first: True
 sledgehammer
 have both: \<open>True \<and> True\<close>
 proof
  show True using first
  sledgehammer
  show True using first
  sledgehammer
 qed
 show True using both
 sledgehammer
qed""")
    add("multiple_subgoals", r'''proof -
 have both: "True \<and> True"
 apply (rule conjI)
 sledgehammer
 from both show "True" by simp
qed''', provers=("simp",), force_hammer=True, min_reconstructions=2, require_apply=True)
    add("partial_goal_rejected", r'''proof -
 have impossible: "True \<and> False"
 apply (rule conjI)
 sledgehammer
 then show "True" by simp
qed''', provers=("simp",), force_hammer=True, expected_failure="missing_reconstruction",
        min_reconstructions=1, require_apply=True)
    add("zero_goal_done", 'proof -\n show "True"\n apply simp\n sledgehammer\nqed', min_reconstructions=1)
    add("local_blocks", 'proof -\n { have "True" .. }\n then show "True" .\nqed')
    add("local_definitions", 'proof -\n define t where "t = True"\n'
        ' have ht: t unfolding t_def by simp\n consider t using ht by blast\n then show True by cases simp\nqed')
    add("subgoal_block", 'proof -\n show "True"\n subgoal by simp\n done\nqed')
    add("invalid_method", "by (v2_missing_negative_control_method)", expected_failure="sketch_step_failure")
    add("admission_rejected", "proof -\n sorry\nqed", expected_failure="rejected_proof")
    add("quoted_ml_rejected", r'by ("tactic" \<open>all_tac\<close>)', expected_failure="rejected_proof")
    for name in ("quick_and_dirty", "smt_oracle"):
        add(name + "_override_rejected", 'proof -\n supply [[' + name + ' = true]]\n show True by simp\nqed',
            expected_failure="rejected_proof")
    add("self_reference_rejected", "by (rule v2_control)", expected_failure="sketch_step_failure")
    later = add("later_fact_rejected", "by (rule v2_later_secret)", conclusion="False",
                expected_failure="sketch_step_failure")
    later["isabelle_theory_template"] = later["isabelle_theory_template"].rsplit("end", 1)[0] + 'lemma v2_later_secret: "False" sorry\nend\n'
    add("unavailable_prover_rejected", hammer, provers=("dsp_nonexistent_prover",), force_hammer=True,
        expected_failure="hammer_failure")
    row = add("inherited_theory_search", "by simp", expected_failure="context_error")
    template = row["isabelle_theory_template"].replace("theory V2Control", "theory Set")
    target = sanitize_target(template, "v2_control")
    row.update(isabelle_theory_template=template, isabelle_context_before_target=target.context_before_target,
               isabelle_target_proof_span=list(target.proof_span))
    return cases


def dataset_cases(records: list[dict]) -> list[ProofCase]:
    result = []
    for raw in records:
        if (raw["source"], raw["topic"], raw["target_key"]) == (
                "babel-formal", "circle_average", "circleAverage_center_independent"):
            row = export_record({**raw, "draft": "Unfold the definitions and use integral_shift."})
            row["isabelle_sketch"] = "proof -\n show ?thesis unfolding circleAverage_def circleMap_def\n sledgehammer\nqed"
            result.append(ProofCase("circle_average_configured", row))
            result.append(ProofCase("circle_average_native_metis", row, provers=("metis",),
                                    force_hammer=True, hammer_kind="native_tactic"))
        elif (raw["source"], raw["topic"], raw["target_key"]) == (
                "hundred-theorems", "030_the_ballot_problem", "all_countings"):
            row = export_record({**raw, "draft": "Use all_countings_set and n_subsets."}, expected_source="hundred-theorems")
            row["isabelle_sketch"] = "by (simp add: all_countings_set n_subsets)"
            result.append(ProofCase("ballot_explicit", row))
    return result


class PreparedNative(NativeSearch):
    """Reuse this invocation's checked parent; each job still runs isabelle build."""
    def __init__(self, config, parent, *, candidate=None):
        super().__init__(config)
        self.parent = parent
        self.candidate = candidate

    def infrastructure(self, *, deadline):
        return self.parent

    def request(self, record, sketch, **options):
        if self.candidate is not None and options["action"] == "search":
            options["heuristics"] = (self.candidate,)
        return super().request(record, sketch, **options)


def case_problems(case: ProofCase, result: dict) -> list[str]:
    errors = []
    if case.expected_failure:
        if result.get("verified") or result.get("failure_category") != case.expected_failure:
            errors.append("expected rejection category " + case.expected_failure)
        if result.get("prove_success"):
            errors.append("a rejected search/context was marked successful")
    elif not all(result.get(name) for name in ("verified", "prove_success")):
        errors.append("expected executed proof and complete target closure")
    if "replay_verified" in result or "native_replay" in result:
        errors.append("obsolete separate replay artifact in native completion result")
    if not case.expected_failure and not result.get("native_search", {}).get("target_closed"):
        errors.append("native worker did not close the selected target")
    steps = result.get("step_results", [])
    recon = [s for s in steps if s.get("mode") == "reconstruction" and s.get("success")]
    if len(recon) < case.min_reconstructions:
        errors.append("missing successful partial/complete reconstructions")
    if case.require_apply and not any(s.get("command", "").lstrip().startswith("apply") for s in recon):
        errors.append("multi-subgoal reconstruction did not execute apply")
    if case.candidate and not any(s.get("success") and s.get("command") == case.candidate for s in steps):
        errors.append("injected reconstruction was not executed")
    settings = result.get("prover_settings", {})
    if case.hammer_kind:
        if not any(s.get("mode") == "hammer" and s.get("success") for s in steps) or not recon:
            errors.append("native Sledgehammer and executable reconstruction were not exercised")
        if case.hammer_kind != "any" and settings.get("reconstruction_source") != case.hammer_kind:
            errors.append("unexpected reconstruction source")
        if case.hammer_kind == "preplayed" and int(settings.get("preplayed_count", 0)) < 1:
            errors.append("external ATP did not return a Played reconstruction")
    if case.name == "hammer_native_tactic":
        parameters = " ".join(settings.get("native_parameters", "").split())
        if "falsify = SOME false" not in parameters or "abduce = SOME 0" not in parameters:
            errors.append("inherited falsification/abduction settings were not disabled")
        if settings.get("preplay_count") != "0":
            errors.append("integrated tactic control unexpectedly used external preplay")
    if case.name == "unavailable_prover_rejected" and settings.get("resolved_provers") != "dsp_nonexistent_prover":
        errors.append("unavailable prover control did not reach prover selection")
    if case.name.startswith("inherited_theory_") and "already inherited" not in result.get("verify_error", ""):
        errors.append("inherited theory control failed for an unrelated reason")
    return errors


def run_proof_case(case: ProofCase, *, config: DspConfig, backend: dict, parent, directory: Path) -> dict:
    actual = replace(config, provers=case.provers) if case.provers is not None else config
    # The same installed distribution/heap was checked once. Only the prover
    # selection changes; reflect it in metadata rather than hashing the install again.
    identity = {k: v for k, v in backend.items() if k != "backend_fingerprint"}
    identity["config"] = asdict(actual)
    identity["backend_fingerprint"] = fingerprint(identity)
    checker = Checker(actual, results_dir=str(directory), native_factory=lambda cfg:
        PreparedNative(cfg, parent, candidate=case.candidate))
    result = checker.check(case.record, force_hammer=case.force_hammer,
                           backend_metadata=identity)
    problems = case_problems(case, result)
    return {"ok": not problems, "expectation_errors": problems,
            "expected_failure": case.expected_failure, "result": result}


def run_fixture(config: DspConfig, parent, directory: Path) -> dict:
    directory.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(FIXTURE, directory / FIXTURE.name)
    session = "DSP_Acceptance_" + uuid.uuid4().hex
    (directory / "ROOT").write_text(f"session {session} = {parent[1]} +\n"
        "  options [document = false]\n  theories DSP_Reconstruction_Test\n", encoding="utf-8")
    native = NativeSearch(config)
    code = native.run_build(directory, session, parent_dir=parent[0],
                            timeout_s=config.startup_timeout_s,
                            deadline=time.monotonic() + config.target_timeout_s)
    details = build_diagnostics(directory, code)
    return {"ok": code == 0, **details, "error": "" if code == 0 else
            build_error("native acceptance fixture failed", details)}
