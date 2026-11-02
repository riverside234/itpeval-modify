"""Fixed capability cases for original DSP/PISA; no models and no replay."""
from dataclasses import dataclass
from .checker import Checker
from .export_dsp import export_record
from .preflight import control_record


@dataclass
class ProofCase:
    name: str
    record: dict
    force_hammer: bool = False
    expected_failure: str | None = None


def proof_cases():
    cases = []
    def add(name, proof, **options):
        mode = options.pop("mode", "draft")
        cases.append(ProofCase(name, control_record(proof, sketch_source=mode), **options))
    add("explicit_draft", "by simp")
    add("explicit_direct", "by simp", mode="hol-light-proof")
    add("heuristic_gap", 'proof -\n show "True"\n sledgehammer\nqed')
    add("normalhammer", 'proof -\n show "True"\n sledgehammer\nqed', force_hammer=True)
    add("using_facts", 'proof -\n have h: "True" by simp\n show "True" using h by metis\nqed')
    add("using_comments", 'proof -\n have h: "True" by simp\n show "True" using h (* separator *)\n by metis\nqed')
    add("multiple_gaps", 'proof -\n have h: "True"\n sledgehammer\n show "True" using h\n sledgehammer\nqed')
    add("local_definitions", 'proof -\n define t where "t = True"\n have ht: t unfolding t_def by simp\n show True using ht by simp\nqed')
    add("nested_isar", r'''proof -
 have both: "True \<and> True"
 proof
  show True by simp
  show True by simp
 qed
 show True using both by simp
qed''')
    add("invalid_method", "by dsp_nonexistent_method", expected_failure="proof_failure")
    add("self_reference", "by (rule v2_control)", expected_failure="proof_failure")
    add("admission", "proof -\n sorry\nqed", expected_failure="rejected_proof")
    add("unsafe_ml", r'by ("tactic" \<open>all_tac\<close>)', expected_failure="rejected_proof")
    add("admission_setting", 'proof -\n supply [[quick_and_dirty = true]]\n show True by simp\nqed', expected_failure="rejected_proof")
    later = control_record("by (rule v2_later_secret)", conclusion="False")
    later["isabelle_theory_template"] = later["isabelle_theory_template"].rsplit("end", 1)[0] + 'lemma v2_later_secret: "False" sorry\nend\n'
    cases.append(ProofCase("later_fact", later, expected_failure="proof_failure"))
    partial = control_record('proof -\n have impossible: "True \\<and> False"\n apply (rule conjI)\n sledgehammer\n then show True by simp\nqed')
    cases.append(ProofCase("partial_goal", partial, expected_failure="proof_failure"))
    return cases


def dataset_cases(records):
    cases = []
    for raw in records:
        if (raw["source"], raw["topic"], raw["target_key"]) == ("babel-formal", "circle_average", "circleAverage_center_independent"):
            record = export_record({**raw, "draft": "Unfold the definitions and apply integral_shift."})
            record["isabelle_sketch"] = "proof -\n show ?thesis unfolding circleAverage_def circleMap_def\n sledgehammer\nqed"
            cases += [ProofCase("circle_average_default", record), ProofCase("circle_average_normalhammer", record, force_hammer=True)]
        elif (raw["source"], raw["topic"], raw["target_key"]) == ("hundred-theorems", "030_the_ballot_problem", "all_countings"):
            record = export_record({**raw, "draft": "Use all_countings_set and n_subsets."}, expected_source="hundred-theorems")
            record["isabelle_sketch"] = "by (simp add: all_countings_set n_subsets)"
            cases.append(ProofCase("ballot_explicit", record))
    return cases


def case_problems(case, result):
    errors = []
    if case.expected_failure:
        if result.get("verified") or result.get("prove_success") or result.get("failure_category") != case.expected_failure:
            errors.append("expected rejection: " + case.expected_failure)
    elif not result.get("verified") or not result.get("prove_success"):
        errors.append("expected successful original DSP/PISA completion")
    if case.force_hammer and not any(s.get("mode") == "hammer" and s.get("success") and "<hammer>" in s.get("observation", "")
                                     for s in result.get("step_results", [])):
        errors.append("normalhammer did not return an executed reconstruction")
    if any(name in result for name in ("native_search", "native_replay", "replay_verified")):
        errors.append("retired native/replay fields in a PISA result")
    return errors


def run_proof_case(case, *, config, backend, directory):
    result = Checker(config, results_dir=str(directory)).check(case.record, backend_metadata=backend, force_hammer=case.force_hammer)
    problems = case_problems(case, result)
    return {"ok": not problems, "expected_failure": case.expected_failure, "expectation_errors": problems, "result": result}
