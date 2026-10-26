"""Explicit cross-language mappings for names that differ between provers."""

from __future__ import annotations

import argparse
from dataclasses import asdict
import json
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.manifest import Target, candidate_targets
from .common import SOURCE, repo_path, validate_layout

MANIFEST = Path(__file__).parent / "manifests" / "hundred_targets.json"


def load_targets(path: str | Path = MANIFEST) -> list[Target]:
    data = json.loads(repo_path(path).read_text(encoding="utf-8"))
    if data.get("source") != SOURCE or data.get("direction") != "hol-light-to-isabelle":
        raise ValueError("invalid Hundred Theorems target manifest")
    targets = [Target(**item) for item in data["targets"]]
    keys = [(target.topic,target.target_key) for target in targets]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate Hundred Theorems manifest target")
    for target in targets:
        if not all(isinstance(value,str) and value.strip() for value in
                   (target.topic,target.target_key,target.hol_light_target_name,target.isabelle_target_name)):
            raise ValueError("empty manifest target field")
        if target.status == "verified" and not target.semantic_alignment_verified:
            raise ValueError("verified mapping requires semantic_alignment_verified=true")
    return targets


def targets_for_topic(topic: str, pairs: list[tuple[str,str,str]], *,
                      verified_only: bool = False, manifest_path: str | Path = MANIFEST) -> list[Target]:
    manual = [target for target in load_targets(manifest_path) if target.topic == topic]
    if verified_only:
        return [target for target in manual if target.status == "verified" and target.semantic_alignment_verified]
    result = {target.target_key:target for target in candidate_targets(topic,pairs)}
    result.update({target.target_key:target for target in manual})
    return sorted(result.values(), key=lambda target:target.target_key)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--manifest",default=str(MANIFEST))
    parser.add_argument("--verified-only",action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    targets = load_targets(args.manifest)
    if args.verified_only:
        targets = [target for target in targets if target.status == "verified" and target.semantic_alignment_verified]
    print(json.dumps([asdict(target) for target in targets],indent=2))


if __name__ == "__main__":
    main()
