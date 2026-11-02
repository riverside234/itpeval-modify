# Original DSP + PISA + Isabelle2021

Both datasets now use the checker copied directly from the local
`mathLLM/draft_sketch_prove/autoformalization/checker.py`. It tries DSP's original
eleven heuristic methods, then PISA's `normalhammer`, and accepts the original
PISA completion result. **There is no separate replay stage.** The Isabelle2024
baseline remains in `v2_itpeval/`.

[Copied checker](upstream/checker.py) · [Provenance and patch](upstream/ORIGIN.md) ·
[Review of the pulled reports](PROVER_REVIEW.md)

## Lab setup

Use Linux, the main **Python 3.10** environment, **Isabelle2021**, **Java 11**,
Git, and `sbt` on `PATH`. PISA's project selects sbt 1.4.3 and Scala 2.13.
The API and separate Python 3.12 vLLM inference options remain available.

Download the Linux bundle from the official
[Isabelle2021 installation page](https://www.isabelle.in.tum.de/website-Isabelle2021/installation.html)
and extract it under `itpeval/_toolchains/Isabelle2021/`. Keep the archive under
the repository too. The installed version must print exactly `Isabelle2021`;
`Isabelle2021-1` and later releases are different runtimes. For example, after
downloading the archive:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
mkdir -p itpeval/_toolchains
tar -xzf itpeval/_toolchains/Isabelle2021_linux.tar.gz -C itpeval/_toolchains
```

Activate the main environment, then prepare PISA:

```bash
python -m pip install -r requirements.txt
PIPE=eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_2021.local.json
cp -n eval/configs/hol_light_to_isabelle/v2_dsp_2021.example.json "$CFG"

java -version  # Must be Java 11; set java_bin in CFG if needed.
python -m "${PIPE}.prepare_pisa" \
  --expected-root "$PWD" --config "$CFG" --build
```

This clones PISA into `external/Portal-to-ISAbelle/` if absent and pins
`690eed41fa03fe04ec015bb375c668cd6fd94261`. An existing checkout at another
revision or with changes to pinned sources produces an explicit error; changes
are not overwritten. Setup fixes the upstream local JAR URL in `build.sbt`,
regenerates Python gRPC bindings from the unchanged protocol, and builds
`PISA-assembly-0.1.jar`. The build log is
`external/Portal-to-ISAbelle/pisa-build.log`.

Initialize the repository-local Isabelle environment and build the HOL heap.
Original PISA uses `build = false`; this prepares its base runtime, not a
replay of a generated proof:

```bash
eval "$(python -m "${PIPE}.prepare_pisa" --config "$CFG" --print-env)"
"$PWD/itpeval/_toolchains/Isabelle2021/bin/isabelle" build -b HOL
```

If the config uses another installation path, use that `bin/isabelle` instead.
Settings, heaps, temporary files and build caches are under
`itpeval/.runs/isabelle2021-pisa/`. OS `HOME` and `CODEX_HOME` are preserved.
Each job starts its own server on the configured port, default 9000. Do not start
another PISA server manually; an occupied port fails rather than attaching to it.
Run one pipeline at a time on that port.

## Consolidated lab preflight

Run this once after setup. It makes no LLM calls and extracts its inputs in
memory, so saved Drafts or Sketches are not required:

```bash
python -m "${PIPE}.lab_preflight" \
  --expected-root "$PWD" --config "$CFG" \
  --dataset both --all-targets
```

With the current data it checks **all 262 target contexts** (163 Babel, 99 Hundred
Theorems), setup, 16 proof controls, and three real-theorem proof checks. Controls
cover explicit methods, the original heuristic order, forced `normalhammer`,
`using` facts, comments, multiple gaps, nested proofs, local definitions, invalid
methods, self/later references, admissions, unsafe commands, and incomplete goals.
Forced hammer is diagnostic only; normal runs use the original search order.

For a smaller first pass omit `--all-targets`: 32 representative/sentinel contexts
across 29 topics, **54 total checks**. That does not establish readiness for every
target. Add `--plan-only` to inspect coverage without executing or writing outputs.
Filters include `--dataset hundred-theorems`, `--topic ...`, and `--target-key ...`.
Repeat `--input <records.jsonl>` to use saved record files instead of extraction.

Each run creates a unique folder:

```text
eval/preflight_results/pisa_isabelle2021/<UTC-time>-<run-id>/
├── report.json, summary.md, events.jsonl
├── config.json, backend.json       # when setup reaches these stages
├── details/                       # exact result of each check
├── transport/, cases/, work/       # input, RPC, JVM and worker logs
└── diagnostics.zip                # portable copy of the run
```

The **entire directory is not Git-ignored**, including logs, JSON and ZIP files.
Push the complete run folder after it finishes. Reports are checkpointed after
each check. A caught Ctrl-C also saves a partial report and bundle. Exit codes:
0 all passed, 1 failed/blocked checks, 130 interruption. A setup failure blocks
its dependent checks once; independent proof/context failures are all collected.

`backend_ok` covers setup and fixed controls; `contexts_ok` covers input selection,
real dataset proof checks, and selected contexts. Neither measures model accuracy.
The previous 2026 report had seven dataset import/dependency failures. An older
prover does not automatically supply those libraries; see the linked review.
Install compatible library/AFP dependencies before counting those contexts as
ready. Failures remain explicit and stay in the requested denominator.

The focused `preflight` command still accepts `--input`, `--topic`, and
`--target-key`, using the same config. Its report is saved under
`eval/preflight_results/pisa_isabelle2021/single-target/`. Use `lab_preflight`
above for comprehensive acceptance with a complete diagnostics bundle.

## Experiment commands

Saved mathematical Draft to Sketch to Prove:

```bash
DATA=eval/results/hol_light_to_isabelle_v2
python -m "${PIPE}.run_babel" \
  --expected-root "$PWD" --config "$CFG" \
  --sketch-source draft --drafts "$DATA/babel_formal_v2_drafts.jsonl" \
  --topic circle_average --target-key circleAverage_center_independent --samples 1
```

Direct completed HOL Light proof to Sketch to Prove:

```bash
python -m "${PIPE}.run_babel" \
  --expected-root "$PWD" --config "$CFG" \
  --sketch-source hol-light-proof --records "$DATA/babel_formal_v2_exact_name_records.jsonl" \
  --topic circle_average --target-key circleAverage_center_independent --samples 1
```

For Hundred Theorems use
`eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.run_hundred`,
its records/Draft file and the corresponding topic/target filters. Both frontends
share the checker. Omit filters for a batch. `--dry-run` previews prompts;
`--skip-sketch` consumes saved Sketches. `--sketch-llm-config` selects API or vLLM.
Defaults remain `gpt-6.1-terra`, medium reasoning for Draft and high for Sketch.
The runner checks the runtime and target contexts before model calls.

## Results and migration

New schema: `hol_light_to_isabelle_dsp_pisa_v1`. Default result directories:

```text
eval/results/hol_light_to_isabelle_v2/
├── v2-dsp-pisa-isabelle2021/{draft,direct}/<inference-profile>/
└── hundred-theorems/v2-dsp-pisa-isabelle2021/{draft,direct}/<inference-profile>/
```

Runs save `inputs.jsonl`, `sketches.jsonl`, `prove.jsonl`, `verified.jsonl`, and
summaries. **`prove.jsonl` and `verified.jsonl` contain the same one-pass result**;
the final filename is retained for existing consumers. `verified == prove_success`
means the upstream checker completed with `done` and reward 1.0.
`verification_method` is `dsp_pisa_completion`. There is no `replay_verified`,
replay subprocess, or separately assembled/rebuilt proof. The original Sketch
and `dsp_result.step_results` retain proof commands and reconstruction outputs;
`step_results` also records attempted methods and observations.

Each PISA job receives the original header, preceding definitions/masked helper
statements, and exact selected declaration. Earlier helpers are admitted background;
admission is disabled before the selected proof. Generated admissions/unsafe commands
and later declarations are rejected. The copied miniF2F proof wrapper is unused;
the job directory is named `miniF2F` only because original PISA uses that convention
to select its HOL runtime.

Reuse extracted records and saved mathematical Drafts. Regenerate DSP exports and
Sketches with the Isabelle2021 prompts/config. Old native and earlier PISA artifacts
are rejected rather than resumed. Historical 2026 reports/config stay available;
use the new 2021 config. `--replay-only` and `--skip-prove` were removed. Resume
checks include runtime/source/build identity, inputs, model, prompt, and budgets.
Keep the same cohort, budgets, and sample counts when comparing experiment modes.
Failed Drafts, contexts, Sketches and missing samples stay in the denominator.

## Tests

```bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
```

Offline tests check copied-method identity, setup, handoffs, failure accounting,
timeouts, process ownership, and reports. Native Isabelle2021/PISA execution still
requires the lab run. The optional integration test uses the same acceptance cases
and is enabled by `ITPEVAL_PISA_ISABELLE2021_CONFIG="$CFG"`; normally the single
consolidated lab preflight is sufficient without repeating that test.
