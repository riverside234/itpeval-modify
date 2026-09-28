from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path

from eval.pipeline.hol_light_to_isabelle.common import validate_layout


MANIFEST = Path(__file__).parent / "manifests" / "babel_targets.json"


@dataclass(frozen=True)
class Target:
    topic: str
    target_key: str
    hol_light_target_name: str
    isabelle_target_name: str
    status: str
    semantic_alignment_verified: bool
    notes: str = ""


def load_targets() -> list[Target]:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("source") != "babel-formal" or data.get("direction") != "hol-light-to-isabelle":
        raise ValueError("invalid V2 target manifest")
    targets = [Target(**item) for item in data["targets"]]
    keys = [(t.topic, t.target_key) for t in targets]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate V2 target manifest key")
    return targets


def candidate_targets(topic: str, pairs: list[tuple[str, str, str]]) -> list[Target]:
    return [Target(topic=topic, target_key=target, hol_light_target_name=source,
                   isabelle_target_name=target, status=status,
                   semantic_alignment_verified=False)
            for source, target, status in pairs]


def targets_for_topic(topic: str, pairs: list[tuple[str, str, str]], *,
                      verified_only: bool = False) -> list[Target]:
    manual = [t for t in load_targets() if t.topic == topic]
    if verified_only:
        return [t for t in manual if t.status == "verified" and t.semantic_alignment_verified]
    result = {t.target_key: t for t in candidate_targets(topic, pairs)}
    result.update({t.target_key: t for t in manual})
    return sorted(result.values(), key=lambda t: t.target_key)


def main() -> None:
    parser = argparse.ArgumentParser(description="Inspect V2 target manifest.")
    parser.add_argument("--expected-root")
    parser.add_argument("--verified-only", action="store_true")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    targets = load_targets()
    if args.verified_only:
        targets = [t for t in targets if t.status == "verified" and t.semantic_alignment_verified]
    from dataclasses import asdict
    print(json.dumps([asdict(t) for t in targets], indent=2))


if __name__ == "__main__":
    main()
