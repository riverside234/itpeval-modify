# Provers

Each prover lives in `itpeval/provers/<name>/` and should provide:
- `install.sh` (best-effort local install under `ITPEVAL_PREFIX`)
- `check.sh` (smoke test that runs the prover on a minimal artifact)
- `hello/` (the minimal artifact)

Current adapters:
- `hol-light`
- `isabelle`
- `lean4`
- `rocq`
