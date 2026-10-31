# Babel Formal: HOL Light to Isabelle V2

Draft and Sketch support the existing GPT API and an optional local Qwen
server. Standalone generators accept `--llm-config`; saved-Draft runners
accept `--sketch-llm-config`. See [vLLM setup and commands](../../../../vllm/README.md).


The two baselines consume the same saved mathematical Drafts, oracle Isabelle
statements, and proof-masked target contexts. Each record represents one
theorem. Draft generation is in this dataset package.

| Pipeline | Package | Proof verification |
|---|---|---|
| v2-itpeval | v2_itpeval | Complete proof checked through ITPEval with Isabelle2024 |
| v2-dsp | v2_dsp | Isar Sketch, native Isabelle2026 search, then a fresh replay build |

This dataset's code now lives in `babel_formal_pipeline/`. Existing JSONL
files and default output paths remain usable. Both `v2_itpeval.run` and
`v2_dsp.run` are aliases for the respective `run_babel` runners.

The existing ITPEval implementation was moved and polished. The old
generate_sketch, verify_isabelle, sketch_prompt, and run_babel module paths
remain compatible. The legacy run_babel command can still generate Drafts.
The two new runners require saved Drafts and never generate them implicitly.

## Shared Input

Run lab commands from the ITPEval root:

~~~bash
cd /data/not_backed_up/yxu209/ITPEval
~~~

Reuse existing V2 records/Drafts. To create them:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --all-topics --all-targets \
  --output eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl

python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.generate_draft \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --input eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl \
  --output eval/results/hol_light_to_isabelle_v2/babel_formal_v2_drafts.jsonl
~~~

The cohort currently contains 163 candidates across 16 topics. Name matching
does not establish semantic equivalence; the original alignment flags remain
in every record.

Sketch generation uses the existing configured API client, default model
gpt-5.6-terra, and high reasoning effort. Draft generation retains medium
reasoning effort. Only visible content is stored; final records omit prompt
text and thinking. Prompt previews print prompts only in dry-run mode.

## v2-itpeval

Use an installed Isabelle2024 under the normal ITPEval prefix. Set
ITPEVAL_PREFIX if the lab installation uses another prefix; the same resolved
prefix is used for version checks and compilation. Other Isabelle versions
are rejected.

Preflight one target:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.verify_isabelle \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --preflight \
  --input eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent
~~~

Run one theorem from the saved Draft file:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.run_babel \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --drafts eval/results/hol_light_to_isabelle_v2/babel_formal_v2_drafts.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --samples 1 \
  --sketch-output eval/results/hol_light_to_isabelle_v2/v2-itpeval/babel_formal_v2_single_sketches.jsonl \
  --output eval/results/hol_light_to_isabelle_v2/v2-itpeval/babel_formal_v2_single_verified.jsonl
~~~

Add --dry-run to preview the Sketch prompt without Isabelle or an API call.
The normal runner preflights each selected topic's masked theory before
making Sketch calls. It records topic context failures as failed samples;
--fail-fast stops at the first failure. A missing or wrong Isabelle
installation must be fixed before generating a batch.

Use --skip-sketch to verify an existing --sketch-output without an API call.
The generated candidate replaces only the selected target placeholder in the
full masked template.

## v2-dsp

The DSP-style baseline now uses **Isabelle2026 native search and fresh replay**.
It supports saved mathematical Drafts and direct completed HOL Light proof
inputs. Isabelle installation and native acceptance will run on the lab
computer. The separate ITPEval baseline continues to use Isabelle2024.

See [native DSP setup, both modes and lab commands](v2_dsp/README.md).
The example configuration is `eval/configs/hol_light_to_isabelle/v2_dsp.example.json`.
Old PISA configurations/results require new native configuration and outputs.
No PISA, JAR, gRPC or original DSP checkout is needed by the active backend.

The normal runner preflights the runtime and target contexts before model
calls. A dry run previews the full selected prompt without native execution
or inference. Standalone stages and legacy entry points remain available.

## Results and interpretation

Native DSP outputs use schema `hol_light_to_isabelle_dsp_v2` under
`eval/results/hol_light_to_isabelle_v2/v2-dsp-isabelle2026/`, separated by
`draft`/`direct` and inference profile. Direct mode has no Draft fields or
Draft-generation metadata. Draft mode retains the exact Draft as
`informal_proof`. Both preserve the oracle and original preceding context.

Keep the same original target cohort, sample counts and search budgets for
the Draft/direct comparison on Isabelle2026. Failed Drafts, invalid contexts
and missing Sketches remain in the denominator. The Isabelle2024 ITPEval
baseline uses a different verifier/Sketch contract and is reported separately.

Earlier masked helpers remain admitted background. Each selected target and
new intermediate claim must be proved. Native search must yield executable
reconstructions and close the target and its scopes; `verified` additionally
requires a fresh proof build without search helpers. Resume checks include
the mode, consumed text, target context, inference profile, native
release/adapter/session identity, provers and budgets.

## Verification

Run the regression suite without an API key or native prover installation:

~~~bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
~~~

The suite checks extraction across the 163 Babel and 99 Hundred Theorems
targets, legacy imports, masked
context identity and scopes, stale caches, failed Drafts, DSP reconstruction,
replay failures, timeouts, and process ownership. DSP search tests use an
explicit fake adapters; they do not establish native Isabelle2026
compatibility. Run native preflight and the opt-in integration tests on the
lab computer before the experiment.
