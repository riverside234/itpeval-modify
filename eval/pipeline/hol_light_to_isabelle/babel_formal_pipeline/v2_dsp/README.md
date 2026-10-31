# DSP-style native Isabelle2026

This baseline uses the original DSP heuristic ordering with repository-owned
Isabelle/ML search and fresh proof replay. It is distinct from a reproduction
of the original PISA-based DSP stack. Both Babel Formal and Hundred Theorems
support two Sketch inputs on this same backend:

| Input mode | Input file | Model input |
| --- | --- | --- |
| `draft` (default) | `--drafts` saved successful/failed Draft records | Saved mathematical Draft, oracle declaration and original preceding Isabelle context |
| `hol-light-proof` | `--records` extracted records | Selected completed HOL Light statement/proof, required proof-masked source reference, oracle and preceding Isabelle context |

Direct mode never generates a Draft and excludes Draft text/generation metadata
from its normalized artifacts. GPT API and Qwen/vLLM remain selectable with
`--sketch-llm-config`. Only visible final response content is stored.
The separate `v2_itpeval` pipeline continues to use its Isabelle2024 configuration.

## Install and configure on the lab computer

Use the existing Python >=3.10 ITPEval conda environment. Install the official
**Isabelle2026 Linux distribution** separately under
`/data/not_backed_up/yxu209/ITPEval/itpeval/_toolchains/Isabelle2026`.
Use the platform distribution with its bundled provers and heaps, rather than
the source-only archive. Obtain and verify its published checksum from the
[official distribution directory](https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/).
This change does not install Isabelle on the local Windows computer.

~~~bash
cd /data/not_backed_up/yxu209/ITPEval
python -m pip install -e .
cp eval/configs/hol_light_to_isabelle/v2_dsp.example.json \
   eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
~~~

Edit the local JSON to set the actual `isabelle_home`. All paths must be under
the ITPEval root. PISA, a JAR, gRPC, Scala-Isabelle and the original DSP checkout
are not required. Old PISA configurations/results are rejected with migration
messages; use new output directories.

The default base session is `HOL`. For other standard/AFP imports, configure
`session_dependencies` and any `session_roots` containing compatible 2026
`ROOT`/`ROOTS` files. For example, a theory importing
`HOL-Analysis.Analysis` needs the compatible `HOL-Analysis` session available.
Preflight every target prefix; the adapter does not rewrite imports, oracle
statements or assumptions to make an unavailable context compile.

Python pins the checked ML interfaces against hashes extracted from the
[Isabelle2026 release source archive](https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2026.tar.gz).
The native infrastructure is then compiled on the installed distribution.
Installations, version-specific Isabelle user settings, heaps and temporary
files stay under the repository. The OS `HOME` and Isabelle2024 installation
are preserved. Native execution is intended for the Linux lab host.

## Native gate before model calls

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --input eval/results/hol_light_to_isabelle_v2/single_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent
~~~

This accepts raw extracted records without requiring a Draft. It checks the
original prefix and executes positive, forced-native-Sledgehammer, invalid
method, admission, self-reference and later-fact controls. The hammer control
bypasses all heuristics and must obtain, apply and independently replay a
concrete reconstruction. Controls must pass before the runner invokes a model.
The first run builds the infrastructure heap and can require a larger
`startup_timeout_s` than later runs. Failed gates/context checks are recorded;
failed targets remain in the selected cohort.

For all-target context acceptance, remove the topic/target filters and add
`--all-targets`. For Hundred Theorems use
`eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.preflight`
and its extracted records. Native preflight is required on the lab installation;
local offline tests do not establish native proof-search compatibility.

## Run the matched experiments

Saved-Draft mode:

~~~bash
DSP_RUN_DIR=eval/results/hol_light_to_isabelle_v2/v2-dsp-isabelle2026/draft/api-smoke
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.run_babel \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --sketch-source draft \
  --drafts eval/results/hol_light_to_isabelle_v2/single_drafts.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --samples 1 \
  --dsp-output "$DSP_RUN_DIR/inputs.jsonl" \
  --sketch-output "$DSP_RUN_DIR/sketches.jsonl" \
  --prove-output "$DSP_RUN_DIR/prove.jsonl" \
  --output "$DSP_RUN_DIR/verified.jsonl"
~~~

Direct completed HOL Light proof to Sketch:

~~~bash
DSP_RUN_DIR=eval/results/hol_light_to_isabelle_v2/v2-dsp-isabelle2026/direct/api-smoke
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.run_babel \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --sketch-source hol-light-proof \
  --records eval/results/hol_light_to_isabelle_v2/single_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --samples 1 \
  --dsp-output "$DSP_RUN_DIR/inputs.jsonl" \
  --sketch-output "$DSP_RUN_DIR/sketches.jsonl" \
  --prove-output "$DSP_RUN_DIR/prove.jsonl" \
  --output "$DSP_RUN_DIR/verified.jsonl"
~~~

`--drafts` and `--records` are mutually exclusive and must match the selected mode.
Add `--dry-run` to preview the complete prompt without model calls, output writes
or native execution. `--skip-sketch` searches saved Sketches; `--skip-prove`
replays saved completed proofs without searching or invoking a model.
Omit topic/target filters for all targets, including failed Drafts in Draft mode.
Compare both modes on the same original target cohort, with equal sample counts,
search budgets and native configuration. Summary files report Draft and Sketch
usage separately.

For Hundred Theorems, use
`eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.run_hundred`,
its records/Drafts, and a directory under
`eval/results/hol_light_to_isabelle_v2/hundred-theorems/v2-dsp-isabelle2026/`.
Both datasets retain their standalone `export_dsp`, `generate_sketch` and `prove`
commands. Export/generation accept `--sketch-source` with `--records` or `--drafts`;
`--input` remains a compatibility spelling. Verification accepts
`--sketch-source` and saved `--input`, with `--replay-only` for completed proofs.

For Qwen, add
`--sketch-llm-config eval/configs/inference/qwen_vllm.example.json` and choose a
separate Qwen run directory. Server setup remains in [vllm/README.md](../../../../../vllm/README.md).
Measure the complete direct prompt, including the masked reference, before a batch:

~~~bash
python vllm/check_server.py \
  --llm-config eval/configs/inference/qwen_vllm.example.json \
  --stage dsp-sketch --sketch-source hol-light-proof \
  --records eval/results/hol_light_to_isabelle_v2/single_records.jsonl
~~~

The vLLM client also checks the complete prompt for every inference request and
rejects overflow without truncation. API profiles use provider context-limit
errors when a local tokenizer is unavailable.

## Artifacts, proof policy and resume

Defaults are separated by dataset, `v2-dsp-isabelle2026`, `draft`/`direct` and
model-profile fingerprint. Each run stores `inputs.jsonl`, `sketches.jsonl`,
`prove.jsonl`, `verified.jsonl`, summaries, `preflight/` reports and `work/` jobs.
Infrastructure/runtime files live in `itpeval/.runs/isabelle2026-native/`.

Schema `hol_light_to_isabelle_dsp_v2` records the mode, `draft_used`, expected
version, visible model output/usage, input/prompt/model fingerprints, actual
backend identity, per-attempt results, original Sketch and reconstructed proof.
Search requests/results use versioned XML with matching request IDs and input
hashes. A zero exit code or console suggestion cannot substitute for a valid
matching search result. Native commands, section-relative source lines/state
IDs, input files and process logs are preserved on failure.

Only the original imports and preceding target context enter search. The full
masked target theory is not imported. Earlier masked helpers are admitted
background; the target and generated intermediate claims must be proved.
Each gap tries the ordered DSP heuristics from the same saved state, then
native Sledgehammer. Only preplayed, executable reconstructions that actually
close the pending obligation are accepted, including `using ... by ...`.
The reconstructed target must close its original scopes, and a fresh
`isabelle build` of the resulting theory must succeed without search helpers.

`prove_success` records search completion; `verified` and `replay_verified`
require fresh replay. Interruptions/timeouts abort the isolated job.
Startup, method, hammer, preplay and replay budgets are capped by the whole-target
deadline. Cleanup targets owned process groups/descendants only.

Resume fingerprints include consumed text (the direct source proof/reference
or saved Draft), target context, model/profile, native adapter, release/session
sources/heaps, provers and budgets. Changing any relevant input invalidates
reuse. Mixing modes or old PISA results in a reused file is rejected, including
when `--no-resume` is supplied. Missing/stale Sketches and context failures
remain explicit failed samples in the denominator. Success is relative to the
supplied admitted background, not an admission-free proof of the whole file.

## Validation

Offline checks, with no native installation or LLM calls:

~~~bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
~~~

After lab installation, run the native controls above and opt into the real
integration tests (no model calls):

~~~bash
export ITPEVAL_NATIVE_ISABELLE2026_CONFIG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
python -m unittest discover -s tests/hol_light_to_isabelle/v2_dsp -p 'test_native_integration.py'
~~~

Native integration and representative context acceptance for both datasets
are pending until executed on the lab computer. Run all-target context
preflight before the matched experiment; source compatibility and proof quality
are not established by offline mocks.
