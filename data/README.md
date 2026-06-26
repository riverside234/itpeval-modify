# Data

This document describes the benchmark dataset structure across two axes:

- **Tier** — A (controlled/axiomatized) vs. B (ecosystem-backed)
- **Task** — theorem-only (`stmts`: statement + sorry placeholder) vs. theorem-and-proof (`proofs`: full proof file)

## Benchmarks

| Benchmark | Tier | Theorems | ITPs | Notes |
|---|---|---|---|---|
| **babel-formal** | A | 16 | isabelle, lean4, rocq, hol-light | Axiomatized, self-contained (no library imports) |
| **hundred-theorems** | B | 58 (4-way) | isabelle, lean4, rocq, hol-light | Freek's 100 theorems list, scraped from upstream libraries |
| **minif2f** | B | 316 (4-way) | isabelle, lean4, rocq, hol-light | Competition math (IMO, Putnam, AIME); already sorry-stripped at source |

**Not in current eval:**
- `putnambench` — only 3 ITP variants (no HOL-Light); excluded for uniform 4-ITP coverage
- `ntp4vc` — verification conditions from Why3; very large, file-path-based rather than inlined

## Raw File Structure (`data/`)

Each benchmark lives under `data/<source>/data/`:

```
data/
  babel-formal/data/
    index.json                  # metadata: topics, items per topic
    proofs/                     # full proofs (one file per topic per ITP)
      isabelle/                 # 16 .thy files
      lean4/                    # 16 .lean files
      rocq/                     # 16 .v files
      hol-light/                # 16 .ml files
    stmts/                      # sorry-stripped versions
      isabelle/
      lean4/
      rocq/
      hol-light/

  hundred-theorems/data/
    index.json
    proofs/                     # full proofs scraped from upstream
      hol-light/                # 86 theorems
      isabelle/                 # 88 theorems
      lean4/                    # 77 theorems
      rocq/                     # 79 theorems
    stmts/                      # sorry-stripped versions
      hol-light/
      isabelle/
      lean4/
      rocq/

  minif2f/data/
    index.json
    proofs/                     # already sorry-stripped at source
      hol-light/
        test/  valid/
      isabelle/
        test/  valid/
      lean4/
        test/  valid/
      rocq/
        test/  valid/
```

**Convention:** `proofs/` contains the original scraped or authored files. `stmts/` mirrors `proofs/` with all proof bodies replaced by the appropriate placeholder (`sorry`, `Admitted`, etc.).

## Eval JSON Files (`eval/data/`)

The eval pipeline consumes two flat JSON files built from the above raw data:

| File | Content |
|---|---|
| `eval/data/stmts.json` | Sorry-stripped theorem statements |
| `eval/data/proofs.json` | Full proof files |

Both files have the same schema — one JSON array with one record per (theorem, ITP) pair:

```json
[
  {
    "theorem_id": 1,
    "title":      "circle_average",
    "source":     "babel-formal",
    "tier":       "a",
    "prover":     "lean4",
    "content":    "<full file text>"
  },
  ...
]
```

`theorem_id` is globally unique (1–390). Only theorems in the 4-way intersection (all 4 ITPs) are included: babel-formal 1–16, hundred-theorems 17–74, minif2f 75–390.

To regenerate the eval JSONs from raw data:

```bash
python3 data/build_eval_jsons.py
```

To regenerate sorry-stripped statements from full proofs:

```bash
python3 data/sorry_strip.py
```
