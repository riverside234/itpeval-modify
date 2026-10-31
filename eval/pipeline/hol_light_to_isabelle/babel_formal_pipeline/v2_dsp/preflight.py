"""Native capability gate and extracted-record context checks, without model calls."""
from __future__ import annotations

import argparse
import json

from ..common import LAB_REPO_ROOT, RESULTS_DIR, key, latest_records, repo_path, require_source, validate_layout
from ..extract_hol_light import DEFAULT_OUTPUT as DEFAULT_INPUT
from ..sanitize_isabelle import sanitize_target
from .checker import Checker
from .export_dsp import export_record
from .input_contract import MODES
from .runtime import DspConfig


def control_record(proof: str, *, source: str = "babel-formal", sketch_source="draft",
                   conclusion="True", extra_context="") -> dict:
    template = ('theory V2Control imports Main begin\n' + extra_context +
                'lemma v2_control: "' + conclusion + '"\n  sorry\nend\n')
    target = sanitize_target(template, "v2_control")
    record = {
        "source": source, "theorem_id": 0, "topic": "preflight", "target_key": "v2_control",
        "isabelle_target_name": "v2_control", "isabelle_statement": target.statement,
        "isabelle_proof_prefix": target.proof_prefix, "isabelle_theory_template": template,
        "isabelle_context_before_target": target.context_before_target,
        "isabelle_target_proof_span": list(target.proof_span),
        "sample_idx": 0, "isabelle_sketch": proof,
    }
    if sketch_source == "draft":
        record["draft"] = "Establish the supplied conclusion."
    else:
        record.update(hol_light_target_name="v2_control", hol_light_statement="T",
                      hol_light_proof="ACCEPT_TAC TRUTH", hol_light_reference_context="let v2_control = `T`;;")
    return export_record(record, expected_source=source, sketch_source=sketch_source)


def preflight(record: dict, *, config: DspConfig, controls: bool = True,
              backend_metadata: dict | None = None, results_dir: str = RESULTS_DIR,
              sketch_source: str = "draft") -> dict:
    result = {"pipeline": "v2-dsp", "sketch_source": sketch_source, "target": key(record), "ok": False}
    try:
        backend = backend_metadata or config.metadata()
        checker = Checker(config, results_dir=results_dir)
        result.update(checker.check_context(record, backend_metadata=backend))
        if controls:
            def control(proof, **options):
                return control_record(proof, source=record["source"], sketch_source=sketch_source, **options)
            good = checker.check(control("by simp"), backend_metadata=backend)
            hammer = checker.check(control("proof -\n show True\n sledgehammer\nqed"),
                                    force_hammer=True, backend_metadata=backend)
            bad = checker.check(control("by (v2_missing_negative_control_method)"), backend_metadata=backend)
            admitted = checker.check(control("proof -\n sorry\nqed"), backend_metadata=backend)
            self_reference = checker.check(control("by (rule v2_control)"), backend_metadata=backend)
            later_reference = control("by (rule v2_later_secret)", conclusion="False")
            later_reference["isabelle_theory_template"] = later_reference["isabelle_theory_template"].rsplit("end", 1)[0] + 'lemma v2_later_secret: "False" sorry\nend\n'
            later = checker.check(later_reference, backend_metadata=backend)
            result.update({
                "valid_control_verified": bool(good["verified"]),
                "hammer_control_verified": bool(hammer["verified"]) and any(
                    row["mode"] == "hammer" and row["success"] for row in hammer["step_results"]),
                "invalid_control_rejected": not bad["verified"] and bad["failure_category"] == "sketch_step_failure",
                "admitted_control_rejected": not admitted["verified"] and admitted["failure_category"] == "rejected_proof",
                "self_reference_rejected": not self_reference["verified"] and self_reference["failure_category"] == "sketch_step_failure",
                "later_reference_rejected": not later["verified"] and later["failure_category"] == "sketch_step_failure",
                "controls": {"valid": good, "hammer": hammer, "invalid": bad, "admitted": admitted,
                             "self_reference": self_reference, "later_reference": later},
            })
            result["ok"] = all(result[name] for name in (
                "valid_control_verified", "hammer_control_verified", "invalid_control_rejected",
                "admitted_control_rejected", "self_reference_rejected", "later_reference_rejected"))
        else:
            result["ok"] = True
    except Exception as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    directory = repo_path(results_dir) / "preflight"
    directory.mkdir(parents=True, exist_ok=True)
    from ..common import fingerprint
    path = directory / (fingerprint({"key": key(record), "mode": sketch_source})[:20] + ".json")
    path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    result["report_path"] = str(path)
    return result


def main(*, default_input: str = DEFAULT_INPUT, results_dir: str = RESULTS_DIR,
         expected_source: str = "babel-formal") -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--config", required=True)
    parser.add_argument("--input", default=default_input)
    parser.add_argument("--sketch-source", choices=MODES, default="draft")
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--all-targets", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    records = latest_records(args.input, topic=args.topic, target_key=args.target_key,
                             limit=args.limit or (None if args.all_targets else 1))
    require_source(records, expected_source)
    if not records:
        parser.error("no matching targets")
    config = DspConfig.load(args.config)
    try:
        backend = config.metadata()
    except Exception as exc:
        print(json.dumps({"ok": False, "error": str(exc)}, indent=2))
        raise SystemExit(1)
    results = [preflight(record, config=config, controls=index == 0, backend_metadata=backend,
                         results_dir=results_dir, sketch_source=args.sketch_source)
               for index, record in enumerate(records)]
    print(json.dumps(results, indent=2))
    if not all(row["ok"] for row in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
