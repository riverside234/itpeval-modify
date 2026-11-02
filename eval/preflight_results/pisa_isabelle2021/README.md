# DSP/PISA Isabelle2021 lab reports

Complete the [lab setup](../../pipeline/hol_light_to_isabelle/babel_formal_pipeline/v2_dsp_pisa/README.md),
then run from the repository root in the main Python 3.10 environment:

```bash
PIPE=eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp_pisa
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_2021.local.json
python -m "${PIPE}.lab_preflight" \
  --expected-root "$PWD" --config "$CFG" --dataset both --all-targets
```

No LLM calls. Omit `--all-targets` for representative contexts, or add `--plan-only`
to inspect coverage without running Isabelle. Each unique run directory contains
five compact files: `report.json`, `summary.md`, `checks.jsonl`, `metadata.json`,
and `logs.jsonl`. Each exported file is capped at 32 MiB. Complete inputs and
RPC/JVM/worker logs stay in ignored `itpeval/.runs/preflight/`; no ZIP is created.
Stage the compact run directory using your normal Git workflow. See
[storage and rejected-push recovery](../README.md) for older runs.

Success means original DSP/PISA completion. There is no separate replay stage.
The default native Isabelle2026 backend and reports stay in their separate folders.
