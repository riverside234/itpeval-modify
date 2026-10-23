"""Check the DSP runtime, target context, and valid/invalid proof controls."""

from __future__ import annotations

import argparse
import json

from eval.pipeline.hol_light_to_isabelle.common import (
    LAB_REPO_ROOT, key, latest_records, validate_layout,
)
from eval.pipeline.hol_light_to_isabelle.extract_hol_light import DEFAULT_OUTPUT as DEFAULT_INPUT
from eval.pipeline.hol_light_to_isabelle.sanitize_isabelle import sanitize_target
from eval.pipeline.hol_light_to_isabelle.v2_dsp.checker import Checker
from eval.pipeline.hol_light_to_isabelle.v2_dsp.export_dsp import export_record
from eval.pipeline.hol_light_to_isabelle.v2_dsp.runtime import DspConfig


def control_record(proof: str) -> dict:
    template = 'theory V2Control imports Main begin\nlemma v2_control: "True"\n  sorry\nend\n'
    target = sanitize_target(template, "v2_control")
    return export_record({
        "source": "babel-formal", "theorem_id": 0, "topic": "preflight",
        "target_key": "v2_control", "isabelle_target_name": "v2_control",
        "isabelle_statement": target.statement, "isabelle_proof_prefix": target.proof_prefix,
        "isabelle_theory_template": template,
        "isabelle_context_before_target": target.context_before_target,
        "isabelle_target_proof_span": list(target.proof_span),
        "draft": "True holds.", "sample_idx": 0, "isabelle_sketch": proof,
    })


def preflight(record: dict, *, config: DspConfig, controls: bool = True,
              backend_metadata: dict | None = None) -> dict:
    result = {"pipeline": "v2-dsp", "target": key(record), "ok": False}
    try:
        backend = backend_metadata or config.metadata()
        result.update(Checker(config).check_context(record, backend_metadata=backend))
        if controls:
            good = Checker(config).check(control_record("by simp"), backend_metadata=backend)
            hammer = Checker(config).check(
                control_record("proof -\n  show True\n    sledgehammer\nqed"),
                backend_metadata=backend)
            bad = Checker(config).check(
                control_record("by (v2_missing_negative_control_method)"),
                backend_metadata=backend)
            admitted = Checker(config).check(
                control_record("proof -\n  sorry\nqed"), backend_metadata=backend)
            result.update({
                "valid_control_verified": bool(good["verified"]),
                "hammer_control_verified": bool(hammer["verified"]),
                "invalid_control_rejected": (
                    not bad["verified"] and bad["failure_category"] == "sketch_step_failure"),
                "admitted_control_rejected": (
                    not admitted["verified"] and admitted["failure_category"] == "rejected_proof"),
                "controls": {"valid": good, "hammer": hammer,
                             "invalid": bad, "admitted": admitted},
            })
            result["ok"] = all(result[name] for name in (
                "valid_control_verified", "hammer_control_verified",
                "invalid_control_rejected", "admitted_control_rejected"))
        else:
            result["ok"] = True
    except Exception as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root", help=f"Lab repo: {LAB_REPO_ROOT}")
    parser.add_argument("--config", required=True)
    parser.add_argument("--input", default=DEFAULT_INPUT)
    parser.add_argument("--topic")
    parser.add_argument("--target-key")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--all-targets", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    records = latest_records(args.input, topic=args.topic, target_key=args.target_key,
                             limit=args.limit or (None if args.all_targets else 1))
    if not records:
        parser.error("no matching targets")
    config = DspConfig.load(args.config)
    results = [preflight(record, config=config, controls=index == 0)
               for index, record in enumerate(records)]
    print(json.dumps(results, indent=2))
    if not all(row["ok"] for row in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
