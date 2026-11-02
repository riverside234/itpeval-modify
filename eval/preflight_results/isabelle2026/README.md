# Isabelle2026 lab preflight reports

Native Isabelle2026 is the default again. See the [setup and full-cohort guide](../../pipeline/hol_light_to_isabelle/babel_formal_pipeline/v2_dsp/README.md).
Separate replay verification has been removed; old report directories are historical evidence.

Run in the main Python 3.10 environment on the Linux lab host:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.lab_preflight \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --dataset both --all-targets --expected-contexts 262
```

Before the first lab preflight, run:

```bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.prepare_afp \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
```

This installs the full pinned AFP release for Isabelle2026 and updates
`session_roots`. There are 31 AFP-dependent candidates, checked normally after
setup. The 24 core Set candidates instead receive **unavailable context**, remain
in the cohort and are listed in `unavailable_contexts.json` and a separate summary
table. They are neither failures nor passes. The native isolation guard remains.
`contexts_ok`/exit 0 concern available checks; `full_context_coverage` remains false
when contexts are unavailable. An entirely unavailable selection cannot pass.

The run performs 292 checks (262 contexts, 23 backend controls, three fixed real
proofs, and four setup/fixture/selection checks), without model calls or separate
replay. `--plan-only` prints scope without running Isabelle. Default representative
selection remains available by omitting `--all-targets --expected-contexts 262`.

Each timestamped run saves at most six compact, Git-trackable files:
`report.json`, `summary.md`, `checks.jsonl`, `metadata.json`, `logs.jsonl`, and
`unavailable_contexts.json`. Each exported file is capped at 32 MiB. Full native
inputs/results and runtime logs stay in ignored `itpeval/.runs/preflight/`;
no `diagnostics.zip` is created. Ordinary failures and caught interruptions
preserve completed checks and mark unexecuted checks.

See [report storage and rejected-push recovery](../README.md) to compact an old
run without losing its original diagnostics, then repair an unpushed commit.
