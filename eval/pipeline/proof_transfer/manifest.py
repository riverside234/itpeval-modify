from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from eval.pipeline.proof_transfer.aligned_data import LAB_REPO_ROOT, validate_repo_layout


MANIFEST_DIR = Path(__file__).resolve().parent / "manifests"
BABEL_TARGETS_JSON = MANIFEST_DIR / "babel_targets.json"


@dataclass(frozen=True)
class BabelTarget:
    topic: str
    target_key: str
    isabelle_target_name: str
    lean4_target_name: str
    status: str
    semantic_alignment_verified: bool
    notes: str = ""

    @classmethod
    def from_dict(cls, raw: dict[str, Any]) -> "BabelTarget":
        required = {
            "topic",
            "target_key",
            "isabelle_target_name",
            "lean4_target_name",
            "status",
            "semantic_alignment_verified",
        }
        missing = sorted(required - set(raw))
        if missing:
            raise ValueError(f"manifest target is missing required fields: {missing}")
        return cls(
            topic=raw["topic"],
            target_key=raw["target_key"],
            isabelle_target_name=raw["isabelle_target_name"],
            lean4_target_name=raw["lean4_target_name"],
            status=raw["status"],
            semantic_alignment_verified=bool(raw["semantic_alignment_verified"]),
            notes=raw.get("notes", ""),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "topic": self.topic,
            "target_key": self.target_key,
            "isabelle_target_name": self.isabelle_target_name,
            "lean4_target_name": self.lean4_target_name,
            "status": self.status,
            "semantic_alignment_verified": self.semantic_alignment_verified,
            "notes": self.notes,
        }


def load_babel_manifest(path: Path | str = BABEL_TARGETS_JSON) -> dict[str, Any]:
    manifest_path = Path(path)
    raw = json.loads(manifest_path.read_text(encoding="utf-8"))
    if raw.get("source") != "babel-formal":
        raise ValueError(f"expected Babel Formal manifest, got source={raw.get('source')!r}")
    if not isinstance(raw.get("targets"), list):
        raise ValueError("manifest must contain a list field named 'targets'")
    return raw


def iter_babel_targets(
    *,
    path: Path | str = BABEL_TARGETS_JSON,
    statuses: Iterable[str] | None = None,
) -> Iterable[BabelTarget]:
    allowed_statuses = set(statuses) if statuses else None
    manifest = load_babel_manifest(path)
    for raw_target in manifest["targets"]:
        target = BabelTarget.from_dict(raw_target)
        if allowed_statuses is not None and target.status not in allowed_statuses:
            continue
        yield target


def get_babel_target(
    *,
    topic: str,
    target_key: str,
    path: Path | str = BABEL_TARGETS_JSON,
) -> BabelTarget:
    for target in iter_babel_targets(path=path):
        if target.topic == topic and target.target_key == target_key:
            return target
    raise KeyError(f"missing Babel target mapping for topic={topic!r}, target_key={target_key!r}")


def exact_name_candidate_targets(topic: str, names: Iterable[str]) -> list[dict[str, Any]]:
    return [
        {
            "topic": topic,
            "target_key": name,
            "isabelle_target_name": name,
            "lean4_target_name": name,
            "status": "candidate",
            "semantic_alignment_verified": False,
            "notes": "Auto-seeded exact-name candidate; requires review before use.",
        }
        for name in sorted(set(names))
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description="Inspect the Babel Formal proof-transfer manifest.")
    parser.add_argument("--expected-root", help=f"Expected repo root, e.g. {LAB_REPO_ROOT}.")
    parser.add_argument("--check-layout", action="store_true", help="Validate repo/input paths and exit.")
    parser.add_argument("--verified-only", action="store_true")
    args = parser.parse_args()

    if args.expected_root or args.check_layout:
        layout = validate_repo_layout(args.expected_root)
        if args.check_layout:
            print(json.dumps(layout, indent=2, ensure_ascii=False))
            return

    statuses = ["verified"] if args.verified_only else None
    targets = [target.to_dict() for target in iter_babel_targets(statuses=statuses)]
    print(json.dumps(targets, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
