from __future__ import annotations

import json

from eval.pipeline.config import STMTS_JSON, PROOFS_JSON


def load_pairs(
    mode: str = "proofs",
    *,
    sources: list[str] | None = None,
    tiers: list[str] | None = None,
    theorem_ids: list[int] | None = None,
    subset: set[tuple[str, int]] | None = None,
) -> list[dict]:
    """Load translation pairs from flat eval JSON.

    mode: 'stmts' or 'proofs'
    Returns list of dicts with keys: theorem_id, title, source, tier,
    src_prover, tgt_prover, src_content.
    """
    json_path = STMTS_JSON if mode == "stmts" else PROOFS_JSON
    records = json.loads(json_path.read_text())

    if sources:
        records = [r for r in records if r["source"] in sources]
    if tiers:
        records = [r for r in records if r["tier"] in tiers]
    if theorem_ids:
        records = [r for r in records if r["theorem_id"] in theorem_ids]
    if subset:
        records = [r for r in records if (r["source"], int(r["theorem_id"])) in subset]

    # Pair records only within the same theorem/source group
    by_theorem: dict[tuple, list[dict]] = {}
    for r in records:
        if not r.get("content"):
            continue
        by_theorem.setdefault((r["source"], r["theorem_id"]), []).append(r)

    pairs = []
    for recs in by_theorem.values():
        prover_map = {r["prover"]: r for r in recs}
        # For each theorem with n provers, emit all n * (n - 1) directed pairs
        for src_prover, src_rec in prover_map.items():
            for tgt_prover in prover_map:
                if src_prover != tgt_prover:
                    pairs.append({
                        "theorem_id":  src_rec["theorem_id"],
                        "title":       src_rec["title"],
                        "source":      src_rec["source"],
                        "tier":        src_rec["tier"],
                        "src_prover":  src_prover,
                        "tgt_prover":  tgt_prover,
                        "src_content": src_rec["content"],
                    })
    return pairs
