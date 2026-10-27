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
| v2-dsp | v2_dsp | Isar sketch, DSP heuristics/hammer, then replay through PISA |

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

This uses the original Isabelle DSP implementation as its source reference,
not the separate DSP+ Lean workflow. DSP/PISA dependencies are optional;
v2-itpeval does not import them.

Install the optional Python dependencies in the lab environment:

~~~bash
python -m pip install -e '.[isabelle-dsp]'
~~~

Configure:

~~~text
eval/configs/hol_light_to_isabelle/v2_dsp.example.json
eval/configs/hol_light_to_isabelle/v2_dsp.local.json
~~~

The local configuration is Git-ignored. Set the actual PISA protobuf directory,
built PISA JAR, Isabelle home, Java executable, and port.
Relative dependency paths resolve under the ITPEval root. Example paths are
placeholders; the provided example is not a tested installation.

The original DSP checkout is optional and is not needed to execute proofs.
By default, check_dsp_repo is false: dsp_repo_root can be omitted, no DSP
checkout or commit is checked, and metadata records dsp_repo_checked=false
and dsp_commit=null. PISA and Isabelle runtime checks remain mandatory.

To check the original DSP source explicitly, set check_dsp_repo=true and
provide dsp_repo_root. Its commit must match expected_dsp_commit, whose
default is the DSP reference pin below.

The reference pins are:

- DSP: 647aa65ca7b89f4e0f7a65dc15b4e64a81af5e80
- PISA: 56def2c39f85d211e1f40cc5765581a567879106

The example proposes Isabelle2021, reflecting upstream DSP's setup. Actual
compatibility with the configured PISA JAR and Babel contexts must pass the
native preflight. A different tested stack can be selected explicitly by
updating the version and source pins. The adapter records actual versions,
checked source commits, client hashes, and JAR hash. A changed stack invalidates
verification resume.

The original DSP clone on the local Windows workspace is the sibling
mathLLM/draft_sketch_prove. Lab dependency paths are configured separately.
To retain all lab files under ITPEval, use its ignored external/ directory
for the source checkouts and the configured toolchain directory for Isabelle.

The adapter uses upstream protobuf RPCs with deadlines. It starts its own
PISA JVM and refuses an occupied port. Each attempt has an isolated directory
under eval/results/hol_light_to_isabelle_v2/v2-dsp/work/. The miniF2F path
component in these directories selects HOL in upstream PisaOS; it does not
replace the Babel theorem context with miniF2F imports.

Preflight before generating sketches:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp.local.json \
  --input eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent
~~~

Preflight checks target context, valid-proof replay, a hammer gap, an invalid
method, and admission rejection. To check every target prefix, omit the
topic/target filters and add --all-targets. Negative controls must fail for
the expected proof error; missing infrastructure cannot pass the controls.

Run the same selected theorem/Draft through DSP:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.run_babel \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp.local.json \
  --drafts eval/results/hol_light_to_isabelle_v2/babel_formal_v2_drafts.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --samples 1 \
  --dsp-output eval/results/hol_light_to_isabelle_v2/v2-dsp/babel_formal_v2_single_dsp_input.jsonl \
  --sketch-output eval/results/hol_light_to_isabelle_v2/v2-dsp/babel_formal_v2_single_sketches.jsonl \
  --prove-output eval/results/hol_light_to_isabelle_v2/v2-dsp/babel_formal_v2_single_prove.jsonl \
  --output eval/results/hol_light_to_isabelle_v2/v2-dsp/babel_formal_v2_single_verified.jsonl
~~~

Add --dry-run to inspect the exported Sketch prompt without installed DSP,
PISA, Isabelle, or an API call. The normal runner checks the runtime and
selected target prefixes before paid Sketch generation. Failed contexts
remain visible in the result cohort.

Use --skip-sketch to run Prove from the saved Sketch file. Use --skip-prove
to replay completed proofs from --prove-output, without another model call or
proof search. Individual stages are also executable modules:

~~~text
eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.export_dsp
eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.generate_sketch
eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.prove
~~~

The prove module accepts --replay-only with a completed-proof --input.

## Results and Interpretation

For the full cohort, omit --topic/--target-key and use output paths without
single in their names. Use equal --samples K and the identical shared Draft
JSONL in both pipelines. --limit N selects targets, retaining all requested
samples for each. Keep smoke and batch output paths distinct.

Exports map draft to informal_proof and isabelle_statement to formal_statement.
They retain the original masked context, proof prefix, template, spans,
alignment flags, and hashes. These are adapter records; upstream DSP does
not natively consume the existing DSP+ JSONL schema.

DSP sketches contain explicit sledgehammer steps. The checker tries the
original heuristic portfolio, then normalhammer, always from the same state
before that obligation. Successful gaps must yield concrete methods.
isabelle_sketch retains the original outline; isabelle_proof stores its
filled form. Search success alone is not verified success: the proof is
replayed from a new default-state branch with the same original prefix.
The target must open and close its own proof, and all original scopes must
close. The replayed theory and server logs are retained in the work directory.

Upstream PISA also has internal limits: ordinary transitions use 10 seconds,
and normalhammer search uses 40 seconds, followed by a checked transition.
Configured RPC and whole-target deadlines cap the adapter's wait; increasing
them does not increase those upstream internal limits. A timeout aborts the
target and closes its owned process group.

Earlier masked helper lemmas remain admitted background facts in both
baselines. Each result lists their names/count. The target and all generated
intermediate claims must be proved. Success therefore establishes the
individual theorem relative to that supplied background.

Summary JSON files report the selected target denominator, generated/failed
samples, missing samples, and failure categories. pass_at_k denotes empirical
success among the supplied K Sketch samples. Failed Drafts and stale/missing
Sketches cannot disappear from the denominator. Resume checks include Draft,
context, statement, prompt/model settings, pipeline, backend, and budgets.
Filtered verification runs preserve saved results for unselected targets.
Their summary file describes the current requested cohort.

The two pipelines have different Sketch contracts and may use different
Isabelle versions. Report these differences and search budgets when comparing
their results.

## Verification

Run the regression suite without an API key or native prover installation:

~~~bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
~~~

The suite checks extraction across the 163 Babel and 99 Hundred Theorems
targets, legacy imports, masked
context identity and scopes, stale caches, failed Drafts, DSP reconstruction,
replay failures, timeouts, and process ownership. DSP search tests use an
explicit fake transport; they do not establish native Isabelle/PISA
compatibility. Run both native preflight commands on the lab machine before
the real experiment.
