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

## Prompt contracts and revisions

Both datasets use the same instructions with dataset-specific prompt versions:

| Stage | Input and expected output | Current version suffix |
| --- | --- | --- |
| Draft | Completed selected HOL Light proof, masked source reference and oracle context -> mathematical claims with justifications in target vocabulary | `hol_light_to_isabelle_p3` |
| Draft to Sketch | Saved mathematical Draft and oracle context -> Isabelle Isar proof body | `isabelle2026_draft_p4` |
| Direct to Sketch | Completed selected HOL Light proof, masked source reference and oracle context -> Isabelle Isar proof body | `isabelle2026_direct_p3` |

The Draft uses numbered steps with `Claim:` and `Justification:`. Each step
identifies its premises and earlier-step dependencies. It distinguishes constants
from defining equations, available facts from claims being proved, and local
assumptions from the outer theorem context. Substitutions and side conditions
remain explicit; it gives mathematical reasoning rather than proof commands.
Both Sketch prompts preserve that argument and use the same rules for available
facts, proof prefixes, local claims, and standalone `sledgehammer` gaps. Earlier
masked helper statements are available background; the selected target and later
declarations cannot justify the target. There is no brevity or step-count target.
The shared Draft builder also supplies newly generated Drafts to `v2_itpeval`.

Rerun `generate_draft` on the extracted records to use the revised Draft prompt,
then run saved-Draft mode with that output. The DSP runner consumes saved Drafts
and does not regenerate them. Direct mode uses the revised prompt on its next
Sketch generation. Prompt versions and hashes prevent generation from reusing
old prompt outputs; `--skip-sketch` deliberately uses the saved Sketch instead.
Use separate output paths to compare prompt revisions, and add `--dry-run` to
the generation command to inspect the prompt before inference.

A structured Isabelle proof starts with `proof -` (or an appropriate proof
method) and ends with `qed`. A terminal `by` takes method expressions; it does
not open an indented block. Both Sketch prompts now demonstrate this distinction.
Generation rejects the observed `by`/`have` mixture and unparenthesized sequences
of bare names before invoking native search. These are lexical checks, not a
complete Isabelle parser. Imported methods and mathematical correctness still
require native checking and fresh replay.

`sketch_response_content` stores only the model's visible final response,
including when the Sketch fails validation; reasoning and prompts are excluded.
The API usage metadata also survives validation failure. The
`sketch_validator_version` participates in generation resume identity.
A failed validation remains a failed sample; the pipeline does not silently
repair it or request additional samples.


The default API model is now `gpt-6.1-terra` for Draft, Draft-to-Sketch and
Direct-to-Sketch. Draft keeps medium reasoning effort; Sketch keeps high.
Explicit model/profile selections still override the default. The Qwen/vLLM
profile remains selectable. The exact identifier and both reasoning settings
are supported by the [official model documentation](https://developers.openai.com/api/docs/models/gpt-6.1-terra).

To adopt both revisions, rerun `generate_draft` from the extracted records,
then pass that new Draft file to the DSP runner. The runner does not refresh
saved Draft text automatically. The revised prompt version and model metadata
invalidate generation reuse; use fresh output paths to preserve old experiments.
A copied local API profile that pins the previous model must be updated or
explicitly overridden with `--model` (generators) or `--sketch-model` (runner).

## Install and configure on the lab computer

Use the existing Python >=3.10 ITPEval conda environment. Install the official
**Isabelle2026 Linux distribution** separately under
`/data/not_backed_up/yxu209/itpeval-modify/itpeval/_toolchains/Isabelle2026`.
Use the platform distribution with its bundled provers and heaps, rather than
the source-only archive. Obtain and verify its published checksum from the
[official distribution directory](https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/).
This change does not install Isabelle on the local Windows computer.

~~~bash
cd /data/not_backed_up/yxu209/itpeval-modify
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
  --expected-root /data/not_backed_up/yxu209/itpeval-modify \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --input eval/results/hol_light_to_isabelle_v2/single_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent
~~~

This accepts raw extracted records without requiring a Draft. It checks the
original prefix and executes positive, forced-native-Sledgehammer, invalid
method, admission, self-reference and later-fact controls. The hammer control
bypasses all heuristics and must obtain, apply and independently replay a
concrete reconstruction. Controls must pass before the runner invokes a model.
Preflight checks the backend, target context and fixed capability controls. It
does not validate a future model-generated Sketch. A successful preflight and a
later syntax/proof failure are therefore compatible. The pulled single-theorem
failure and regeneration commands are documented in [PROVER_REVIEW.md](PROVER_REVIEW.md#pulled-single-theorem-run-c8fb3cb).
The first run builds the infrastructure heap and can require a larger
`startup_timeout_s` than later runs. Failed gates/context checks are recorded;
failed targets remain in the selected cohort.

Sledgehammer diagnostics are retained on failure in
`controls.hammer.prover_settings` in the preflight JSON report: resolved provers,
native outcome/messages, preplay results/counts, reconstruction source and
candidate count. A successful `isabelle build` alone does not imply successful
search; consult the structured report/result XML.

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
  --expected-root /data/not_backed_up/yxu209/itpeval-modify \
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
  --expected-root /data/not_backed_up/yxu209/itpeval-modify \
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
native Sledgehammer. ATP reconstructions require a native `Played` result.
Isabelle2026's integrated tactic provers return an already executed command
with no separate preplay list; their structured sendback is also supported.
Serialization enables PIDE markup locally so batch mode cannot discard the
sendback wrapper. Every candidate executes from the saved proof state. When
Isabelle returns `apply` for one of several subgoals, reconstruction requires a
strict reduction in remaining goals and continues until the entire obligation
closes. Zero remaining goals are finished with `done` when needed. Partial
progress never counts as a completed gap or target. Executable proof text uses
`Token.unparse` to preserve quoted terms, cartouches and comments.
The reconstructed target must close its original scopes, and a fresh
`isabelle build` of the resulting theory must succeed without search helpers.

`prove_success` records search completion; `verified` and `replay_verified`
require fresh replay. Interruptions/timeouts abort the isolated job.
Startup, method, hammer, preplay and replay budgets are capped by the whole-target
deadline. `startup_timeout_s` applies separately to infrastructure compilation
and to worker startup/import loading, ending when that request's readiness
marker appears. Cleanup tracks children from every Linux thread and checks
process start times before signaling owned descendants.

The [2026-10-31 prover review](PROVER_REVIEW.md) records the source comparison,
fixed bugs, and native regression cases. The checker version is
`dsp_isabelle2026_native_p3`; adapter and checker changes invalidate old
verification caches. Preflight now includes a quoted goal to exercise proof
serialization and fresh replay.

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
