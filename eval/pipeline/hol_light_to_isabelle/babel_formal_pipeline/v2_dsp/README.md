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
| Draft to Sketch | Saved mathematical Draft and oracle context -> Isabelle Isar proof body | `isabelle2026_draft_p5` |
| Direct to Sketch | Completed selected HOL Light proof, masked source reference and oracle context -> Isabelle Isar proof body | `isabelle2026_direct_p4` |

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
Complete proofs with zero gaps are valid. Draft step headings do not require
one `have` per step: adjacent rewrites/helper applications can share a method
when it preserves the argument and all necessary dependencies. The p3 Draft
from the successful `547adaf` run can be reused with this Sketch revision;
regenerating that Draft is unnecessary.

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
Preflight every target prefix. The adapter can qualify explicitly configured
bare imports to their owning session; it preserves the imported theory's
basename and never replaces it with a different or broader theory. Oracle
statements, assumptions and stored dataset contexts remain unchanged.

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
The subsequent [547adaf review](PROVER_REVIEW.md#successful-single-theorem-runs-547adaf)
confirms both proof modes passed native checking and replay; neither needed
heuristic gap filling or Sledgehammer on that target.
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

## Hundred Theorems: imports after relocating a library theory

Some Hundred Theorems files are copies of standard-library theories whose
imports were local to their original session. A temporary job cannot find
`Lebesgue_Measure` or `Tagged_Division` by those bare names. The example config
and the tracked `v2_dsp_2026.local.json` now include:

~~~json
"theory_imports": {
  "Lebesgue_Measure": "HOL-Analysis.Lebesgue_Measure",
  "Tagged_Division": "HOL-Analysis.Tagged_Division"
}
~~~

Add this field to any separately maintained config used as `$CFG`. The mapping
only adds a session qualifier to the same theory name. Other unresolved bare
imports need their own verified mappings; the adapter does not guess owners.
Global imports such as `Main`, and already qualified imports, are unchanged.

For `015_the_fundamental_theorem_of_integral_calculus/rsum_bound`, both the native
driver and replay theory import `HOL-Analysis.Lebesgue_Measure`,
`HOL-Analysis.Tagged_Division`, and `HOL-Real_Asymp.Real_Asymp`. Their generated
`ROOT` files automatically include `sessions "HOL-Analysis" "HOL-Real_Asymp"`
from those qualified names, in addition to configured session dependencies.
The parent stays `HOL`; importing the complete original target theory or using
its whole library session as the parent could expose the existing target proof.

Only generated runtime headers are qualified. Parsed JSONL records, template
hashes, proof spans, oracle declarations and all preceding mathematical content
are preserved. Each job stores `import_resolution.json`; successful native
results also record that mapping. This behavior follows Isabelle's
[session-import rules](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Doc/System/Sessions.thy).

Missing imports now report `failure_category: "import_error"`, the absolute
`workdir` and `build_log_path`, the actual `build_returncode`, and a bounded
`build_log_excerpt`. Context failures with a structured native result keep its
step diagnostics too. The batch runner preserves the failure category and
makes no model call for that blocked target. Replay failures retain their build
errors rather than only saying to inspect a log.

After updating the code and `$CFG`, rerun the original preflight command. See
[the 52fa4ea review](PROVER_REVIEW.md#hundred-theorems-rsum_bound-preflight-52fa4ea)
for the exact command and the native regression check. This failure happens
before Sketch generation or Sledgehammer, so no prompt change addresses it.

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

`prove_success` records proof completion; `verified` and `replay_verified`
require fresh replay. Replay-only verification first runs the native context gate
without search, so a changed parent/import graph cannot bypass target/later-fact
checks. A target theory already inherited from the parent/imports is rejected
before executing its copied prefix. The fresh replay still imports no search
helper theory. New checks clear old native results and log paths.

Proof bodies cannot use ML tactics via quoted, escaped, or qualified names, or
change `quick_and_dirty` / `smt_oracle`. Both native search and replay explicitly
disable those two settings at the target boundary. Earlier masked helpers
remain admitted background.

Interruptions/timeouts abort the isolated job.
Startup, method, hammer, preplay and replay budgets are capped by the whole-target
deadline. `startup_timeout_s` applies separately to infrastructure compilation
and to worker startup/import loading, ending when that request's readiness
marker appears. ML method, hammer, and preplay limits must be at least 0.001
seconds: Isabelle ignores smaller timeouts. An exhausted sub-millisecond
remaining budget aborts before executing another operation. Builds pin
`timeout_scale=1.0`. Timeout/launch failures retain the actual build directory,
session, exit status when available, and log excerpt, even without result XML.
Cleanup tracks children from every Linux thread and checks
process start times before signaling owned descendants.

The [2026-10-31 prover review](PROVER_REVIEW.md) records the source comparison,
fixed bugs, and native regression cases. The checker version is
`dsp_isabelle2026_native_p5`; adapter and checker changes invalidate old
verification caches. Preflight now includes a quoted goal to exercise proof
serialization and fresh replay.

Resume fingerprints include consumed text (the direct source proof/reference
or saved Draft), target context, model/profile, native adapter, release/session
sources/heaps, provers and budgets. Changing any relevant input invalidates
reuse. Mixing modes or old PISA results in a reused file is rejected, including
when `--no-resume` is supplied. Missing/stale Sketches and context failures
remain explicit failed samples in the denominator. Success is relative to the
supplied admitted background, not an admission-free proof of the whole file.

### Histories and summaries

Draft and Sketch JSONL files are append-only histories. The loader selects the
latest record per target/sample within that target's latest input, Draft
provenance, Sketch model, prompt and validator settings. It does not combine
sample 0 from a new model with sample 1 from an older model. With a requested
cohort/K, absent current samples become `missing_sketch` failures. Same-setting
failures remain failures rather than falling back to older successes.

Sketch reuse also checks Draft model, prompt, generation identity/time and
response metadata. Two Draft generations with identical mathematical text
retain their own attribution. A new Draft generation can therefore invalidate
Sketch reuse even when the visible text is unchanged.

Prove/verified files are current result snapshots. Re-evaluating a target replaces
all its saved sample indices, including obsolete indices when K decreases.
Unselected targets are preserved with resume enabled; historical Draft/Sketch
logs are preserved separately. Use separate run directories for comparisons.

Each summary describes the current invocation's selection (`summary_scope`),
while `stored_samples` counts all rows in its paired JSONL, including retained
unselected targets. `llm_profiles` exposes the recorded Draft/Sketch model and
reasoning settings. `search_activity` counts search execution, heuristic attempts,
Sledgehammer calls and reconstruction attempts from native steps; empty
`prover_settings` is expected for a complete proof that never invokes Sledgehammer.
These counts describe the selected proof results, not the preflight controls or
all historical inference attempts. `llm_usage` likewise counts the selected
Draft once per target and selected Sketch once per sample, not total historical
API spend.

The `547adaf` artifacts record `gpt-6.1-terra` and **medium** reasoning for both
Sketch modes. To request high explicitly, pass `--sketch-reasoning-effort high`
to the runner (`--reasoning-effort high` to standalone `generate_sketch`). The
code default remains high; profile/CLI overrides are honored. `--skip-sketch`
uses the saved model/prompt settings, regardless of newly specified inference
options; inspect `llm_profiles` in the summary for what was actually evaluated.

## Validation

Offline checks, with no native installation or LLM calls:

~~~bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
~~~

After lab installation, run the native controls above and opt into the real
integration tests (no model calls). These include a forced external **E** ATP
case, in addition to integrated tactic provers: the ordinary `True` preflight
can succeed using an integrated tactic and alone does not establish that an
external prover works. The suite also exercises actual ML timeout behavior,
quoted/escaped method filtering, inherited target theory rejection, and replay
context checks:


~~~bash
export ITPEVAL_NATIVE_ISABELLE2026_CONFIG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
python -m unittest discover -s tests/hol_light_to_isabelle/v2_dsp -p 'test_native_integration.py'
~~~

Native integration and representative context acceptance for both datasets
are pending until executed on the lab computer. Run all-target context
preflight before the matched experiment; source compatibility and proof quality
are not established by offline mocks.

The [comprehensive audit](PROVER_REVIEW.md#comprehensive-isabelle2026-audit-after-0be9014)
records the new regressions, source references and the static import/context
survey of all 163 Babel and 99 Hundred targets. That static survey does not
replace native acceptance of each target; Hundred topics include unresolved
bare imports and AFP dependencies absent from a stock Isabelle installation.
