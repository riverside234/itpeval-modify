"""Conservative alignment with explicit unmatched/ambiguous coverage."""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
from .aligned_data import load_topic, topics
from .common import DATASET_ROOT, SOURCE, repo_path, validate_layout
from ..hundred_theorems_pipeline.inventory import match_pairs


def candidates(group):
    matches = defaultdict(list)
    for source in group["sources"]:
        for hol, isa, status in match_pairs(source.proofs, source.statements, group["targets"]):
            matches[isa].append({"hol_light_name": hol, "isabelle_name": isa,
                                 "source_file": Path(source.path).name, "status": status})
    accepted, ambiguous = [], []
    for name, rows in sorted(matches.items()):
        (accepted if len(rows) == 1 else ambiguous).extend(rows)
    return accepted, ambiguous


def inventory_topic(group):
    pairs, ambiguous = candidates(group)
    names = {row["isabelle_name"] for row in pairs}
    return {"source": SOURCE, "topic": group["topic"], "candidate_count": len(pairs),
            "candidate_pairs": pairs, "ambiguous_pairs": ambiguous,
            "isabelle_declarations": len(group["targets"]),
            "unmatched_isabelle": [item.name for item in group["targets"] if item.name not in names],
            "semantic_alignment_verified": False,
            "source_files": [{"file": Path(s.path).name, "proof_chars": len(s.proof_text),
                              "statement_chars": len(s.statement_text),
                              "extracted_proofs": len(s.proofs)} for s in group["sources"]]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--dataset-root", default=DATASET_ROOT)
    parser.add_argument("--topic")
    parser.add_argument("--output")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    rows = [inventory_topic(load_topic(name, args.dataset_root)) for name in topics(args.topic)]
    result = {"source": SOURCE, "candidate_count": sum(r["candidate_count"] for r in rows), "topics": rows}
    if args.output:
        path = repo_path(args.output)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    for row in rows:
        print(f"{row['topic']}: {row['candidate_count']} candidates; "
              f"{len(row['unmatched_isabelle'])} unmatched Isabelle declarations; "
              f"{len(row['ambiguous_pairs'])} ambiguous matches")
    print("Total candidates:", result["candidate_count"])


if __name__ == "__main__":
    main()
