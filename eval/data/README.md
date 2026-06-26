# ITPEval Benchmark Data

Two JSON files covering all benchmarks and ITPs evaluated in the paper:

```
eval/data/
├── stmts.json    # sorry-stripped theorem statements  (1,560 records)
└── proofs.json   # full proofs                        (296 records)
```

Only theorems formalized in **all four ITPs** (the 4-way intersection) are included.

## Record schema

Every record is a flat dict:

| Field | Type | Always present | Description |
|-------|------|----------------|-------------|
| `theorem_id` | int | ✓ | Globally unique theorem ID (1–390); groups all prover variants of the same theorem |
| `title` | str | ✓ | Theorem name / file stem |
| `source` | str | ✓ | Benchmark: `babel-formal` · `hundred-theorems` · `minif2f` |
| `tier` | str | ✓ | `"a"` (controlled) or `"b"` (ecosystem) |
| `prover` | str | ✓ | `hol-light` · `isabelle` · `lean4` · `rocq` |
| `content` | str | ✓ | Full file text (sorry-stripped in stmts.json, full proof in proofs.json) |
| `split` | str | minif2f only | `"test"` or `"valid"` |

## Benchmark summary

| Source | Tier | Theorems | `theorem_id` range | stmts | proofs |
|--------|------|----------|-------------------|-------|--------|
| `babel-formal` | A | 16 | 1–16 | ✓ | ✓ |
| `hundred-theorems` | B | 58 | 17–74 | ✓ | ✓ |
| `minif2f` | B | 316 | 75–390 | ✓ | — |
| **Total** | | **390** | 1–390 | **1,560 records** | **296 records** |

All four ITPs (HOL Light, Isabelle, Lean 4, Rocq) are represented for every theorem.

## Usage

```python
import json

stmts  = json.load(open("eval/data/stmts.json"))
proofs = json.load(open("eval/data/proofs.json"))

# All Lean 4 statements
lean4_stmts = [r for r in stmts if r["prover"] == "lean4"]

# All prover variants of a single theorem
theorem_1 = [r for r in stmts if r["theorem_id"] == 1]

# 4-way intersection is guaranteed: every theorem_id has exactly 4 records
assert all(
    sum(1 for r in stmts if r["theorem_id"] == tid) == 4
    for tid in range(1, 391)
)

# Join stmts and proofs by (theorem_id, prover)
proof_lookup = {(r["theorem_id"], r["prover"]): r for r in proofs}
for s in stmts:
    p = proof_lookup.get((s["theorem_id"], s["prover"]))
    if p:
        pass  # s["content"] is sorry-stripped; p["content"] is the full proof
```

## Regenerating

From the repo root:

```bash
python data/build_eval_jsons.py
```
