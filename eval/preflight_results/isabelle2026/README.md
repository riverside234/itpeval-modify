> Historical reports: the active DSP baseline is original DSP/PISA with Isabelle2021.
> See [current lab preflight](../pisa_isabelle2021/README.md). Existing reports are retained unchanged.

# Isabelle2026 lab preflight reports

This folder is intentionally **not ignored by Git**. The consolidated lab
preflight creates one timestamped subdirectory per invocation, containing
`report.json`, `summary.md`, individual check details, native input/output files,
build logs, and `diagnostics.zip`. Heap images and toolchain binaries stay in the
ignored runtime directories.

From the lab repository root, with the main Python 3.10 environment active:

```bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.lab_preflight \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
```

The default checks both datasets, 26 backend controls, the native ML fixture,
three fixed real-theorem proofs, and 32 representative target contexts. Add
`--all-targets` for all 262 target contexts. No LLM calls are made.
See [the runner documentation](../../pipeline/hol_light_to_isabelle/babel_formal_pipeline/v2_dsp/README.md#consolidated-lab-acceptance-recommended)
for scope flags, interpretation, and exit codes. A failed or interrupted run is
also useful: push its complete directory so its original inputs and logs can be
reviewed together.

```bash
git add eval/preflight_results/isabelle2026/
git commit -m "Record Isabelle2026 lab preflight"
git push
```

No `git add -f` is necessary. Reports with `status: running` are incomplete; a
finished run uses `complete` or `interrupted`, while `ok` records acceptance.
These are diagnostic controls, not proof-translation benchmark results.
