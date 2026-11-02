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
| v2-dsp | v2_dsp | Isar Sketch checked by original DSP/PISA with Isabelle2021 |

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
cd /data/not_backed_up/yxu209/itpeval-modify
~~~

Reuse existing V2 records/Drafts. To create them:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.extract_hol_light \
  --expected-root /data/not_backed_up/yxu209/itpeval-modify \
  --all-topics --all-targets \
  --output eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl

python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.generate_draft \
  --expected-root /data/not_backed_up/yxu209/itpeval-modify \
  --input eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl \
  --output eval/results/hol_light_to_isabelle_v2/babel_formal_v2_drafts.jsonl
~~~

The cohort currently contains 163 candidates across 16 topics. Name matching
does not establish semantic equivalence; the original alignment flags remain
in every record.

Sketch generation uses the existing configured API client, default model
gpt-6.1-terra, and high reasoning effort. Draft generation retains medium
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
  --expected-root /data/not_backed_up/yxu209/itpeval-modify \
  --preflight \
  --input eval/results/hol_light_to_isabelle_v2/babel_formal_v2_exact_name_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent
~~~

Run one theorem from the saved Draft file:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_itpeval.run_babel \
  --expected-root /data/not_backed_up/yxu209/itpeval-modify \
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

The baseline uses **original DSP + PISA + Isabelle2021**, with the checker copied
from the local original DSP repository. Saved mathematical Drafts and direct HOL
Light proofs are supported. There is no separate replay stage.

See [DSP/PISA setup, both modes and consolidated lab preflight](v2_dsp/README.md).
Use `eval/configs/hol_light_to_isabelle/v2_dsp_2021.example.json` as the config
starting point. The normal runner checks capabilities and target contexts before
model calls; `--dry-run` previews the selected prompt without native execution or
inference. `--skip-sketch` consumes saved Sketches.

## Results and interpretation

DSP outputs use schema `hol_light_to_isabelle_dsp_pisa_v1` under
`eval/results/hol_light_to_isabelle_v2/v2-dsp-pisa-isabelle2021/`, separated by
`draft`/`direct` and inference profile. Direct mode has no Draft fields. Draft
mode retains the exact Draft as `informal_proof`. Both preserve the oracle and
original preceding context. Old native artifacts are rejected; reuse records and
Drafts, then regenerate DSP exports and Sketches with the new prompt/config.

Keep the same cohort, sample counts and budgets when comparing Draft/direct modes.
Failed Drafts, contexts and Sketches remain in the denominator. Earlier masked
helpers remain admitted background. Each selected target and generated intermediate
claim must be proved. `verified` and `prove_success` both mean the original
PISA completion result; `prove.jsonl` and `verified.jsonl` are two saved copies of
that single result, without an additional proof replay.

The Isabelle2024 ITPEval baseline retains its own verifier and output directories.
Runtime/source/build identity, consumed context, prompt and model settings are part
of DSP resume checks. Historical 2026 reports remain available.

## Verification

```bash
python -m unittest discover -s tests/hol_light_to_isabelle -p 'test_*.py'
```

The offline suite covers all 163 Babel and 99 Hundred Theorems extracted targets,
masked contexts, stale artifacts, failed Drafts, copied DSP behavior, process
ownership and reports. Transport tests use explicit fakes. Run the consolidated
PISA preflight on Linux to check actual Isabelle2021, ATP and dataset compatibility.
