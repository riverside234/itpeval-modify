# Hundred Theorems: HOL Light to Isabelle V2

Draft and Sketch support the existing GPT API and an optional local Qwen
server. Standalone generators accept `--llm-config`; saved-Draft runners
accept `--sketch-llm-config`. See [vLLM setup and commands](../../../../vllm/README.md).


This is the same experiment as [Babel Formal](../babel_formal_pipeline/README.md):
a selected HOL Light proof and masked source reference produce a mathematical
Draft; the unchanged oracle Isabelle declaration and masked target context
then feed either the ITPEval baseline or the DSP baseline.

## Inputs and alignment

Use the aligned `eval/data/proofs.json` and `eval/data/stmts.json` records
whose source is `hundred-theorems`. Only HOL Light completed proofs are read.
Completed Isabelle proofs are excluded from the loader.

The current aligned inputs contain **58 file groups**. The default inventory
finds **99 unique case-insensitive name matches in 13 file groups**. These
include helper lemmas from the library files; they are not 99 independently
reviewed statements of the famous 100 theorems. A matching filename/title
alone does not establish theorem correspondence. Some aligned target files
contain no named theorem declaration.

Automatic matches have `semantic_alignment_verified=false`. Review those
statements for a final semantic cohort. Use `manifests/hundred_targets.json`
or `--manifest <repo-relative-path>` to add renamed mappings. For example:

```json
{
  "source": "hundred-theorems",
  "direction": "hol-light-to-isabelle",
  "targets": [
    {
      "topic": "<exact topic from inventory>",
      "target_key": "<stable experiment key>",
      "hol_light_target_name": "<actual source declaration>",
      "isabelle_target_name": "<actual target declaration>",
      "status": "verified",
      "semantic_alignment_verified": true,
      "notes": "<statement equivalence review>"
    }
  ]
}
```

Replace the placeholders after reviewing the two statements. The checked-in
manual manifest starts empty. `--verified-only` therefore needs reviewed
entries before it can produce records. Duplicate or ambiguous source/target
names are excluded from automatic pairing. The coverage report identifies
unmatched declarations and masked source statements without an extracted
source proof. The first parser version supports exported `let NAME = prove
(...)` declarations; local bindings and tuple-producing proof wrappers are
not automatically treated as individual exported targets.

## Masking

The supplied statement files retain some proof code. The loader repairs
remaining HOL Light `prove` phrases and Isabelle `by`, structured, `apply`,
and implicit dot proofs before they enter a reference context. For residual
OCaml tuple/local proof producers, a literal combined proposition is retained
when available. Dynamic proof-producing functions without a literal statement
are omitted. Quoted formulas, nested comments, and document cartouches are
handled lexically.

Isabelle `by sorry` becomes a canonical `sorry` placeholder. The repair
preserves theorem names, attributes, private modifiers, definitions, and
theory scopes. Raw file hashes and the masking version are retained in
metadata alongside hashes of the normalized inputs. Source proof spans
refer to the original completed HOL Light file; the target proof span
refers to the normalized masked Isabelle template.

The record schema is the same as Babel's. `source` is `hundred-theorems`;
the Draft/export/prover stages retain that provenance. Earlier target helper
lemmas remain admitted background facts in both baselines. The selected target
and newly generated intermediate claims must be proved.

## Prepare records

Run from the lab repository root:

```bash
cd /data/not_backed_up/yxu209/ITPEval

python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.inventory \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --all-topics --names \
  --output eval/results/hol_light_to_isabelle_v2/hundred-theorems/inventory.json

python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --all-topics --all-targets
```

Defaults:

```text
eval/results/hol_light_to_isabelle_v2/hundred-theorems/
├── inventory.json                         # explicitly requested above
├── hundred_theorems_v2_records.jsonl       # 99 records for current inputs
├── hundred_theorems_v2_records.jsonl.coverage.json
├── hundred_theorems_v2_drafts.jsonl
├── v2-itpeval/
└── v2-dsp-isabelle2026/                 # draft/<profile>/ and direct/<profile>/
```

The coverage report includes every selected file group and any skipped
target/error. `--fail-fast` stops extraction on the first parser/context error.
`--topic` expects the complete title printed by inventory. `--id` is the
aligned JSON `theorem_id` (17–74 here), not the leading 001–100 filename number.

To prepare just one target instead:

```bash
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.extract_hol_light \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --topic 030_the_ballot_problem --target-key all_countings \
  --output eval/results/hol_light_to_isabelle_v2/hundred-theorems/single_records.jsonl
```

## Generate a shared Draft

Generate one target from the full prepared record file:

```bash
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.generate_draft \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --topic 030_the_ballot_problem --target-key all_countings \
  --output eval/results/hol_light_to_isabelle_v2/hundred-theorems/single_drafts.jsonl
```

The default model is `gpt-5.6-terra` with medium reasoning effort, using the
existing API configuration. Only visible content is used as the Draft.
Prompt text and hidden reasoning are absent from saved records. The prompt
follows the same translation instructions as Babel, without a brevity limit.

Add `--dry-run` to inspect the prompt without an API call or output file.
For a complete batch, omit the topic/target filters and the single output
override; this creates the default `hundred_theorems_v2_drafts.jsonl`.

## ITPEval baseline

Check the selected masked theory with Isabelle2024 before generating sketches:

```bash
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_itpeval.verify_isabelle \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --preflight \
  --input eval/results/hol_light_to_isabelle_v2/hundred-theorems/hundred_theorems_v2_records.jsonl \
  --topic 030_the_ballot_problem --target-key all_countings
```

Run one saved Draft:

```bash
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_itpeval.run \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --drafts eval/results/hol_light_to_isabelle_v2/hundred-theorems/single_drafts.jsonl \
  --topic 030_the_ballot_problem --target-key all_countings \
  --samples 1 \
  --sketch-output eval/results/hol_light_to_isabelle_v2/hundred-theorems/v2-itpeval/single_sketches.jsonl \
  --output eval/results/hol_light_to_isabelle_v2/hundred-theorems/v2-itpeval/single_verified.jsonl
```

The runner preflights the masked template before paid Sketch calls. The
generated complete proof replaces only the selected oracle placeholder.
`--skip-sketch` verifies saved sketches. `--dry-run` previews the Sketch prompt
without an installed prover or API call.

## DSP baseline

The shared DSP-style backend now uses **Isabelle2026 native search and fresh
replay**, with saved-Draft and direct HOL Light proof inputs. Install Isabelle
on the lab computer as described in [the native DSP guide](../babel_formal_pipeline/v2_dsp/README.md).
The separate `v2_itpeval` baseline retains Isabelle2024.

Preflight accepts raw records without requiring a Draft:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.preflight \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --input eval/results/hol_light_to_isabelle_v2/hundred-theorems/hundred_theorems_v2_records.jsonl \
  --topic 030_the_ballot_problem --target-key all_countings
~~~

Direct-mode smoke run:

~~~bash
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.run_hundred \
  --expected-root /data/not_backed_up/yxu209/ITPEval \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --sketch-source hol-light-proof \
  --records eval/results/hol_light_to_isabelle_v2/hundred-theorems/hundred_theorems_v2_records.jsonl \
  --topic 030_the_ballot_problem --target-key all_countings \
  --samples 1
~~~

For saved-Draft mode, use `--sketch-source draft` and replace `--records` with
`--drafts <saved_drafts.jsonl>`. `--dry-run` previews prompts without native
execution or inference; `--sketch-llm-config` selects API or Qwen/vLLM.
Defaults are under `hundred-theorems/v2-dsp-isabelle2026/`, separated by mode
and inference profile. Export/Sketch/prove/final flags match Babel's runner.
`--skip-sketch` searches saved Sketches; `--skip-prove` replays saved proofs.

## Batch runs and interpretation

For all targets, use the complete records/Draft JSONL for the selected mode,
omit topic/target filters and omit single-file output overrides.
Both baselines preserve all requested samples and failed targets in the
denominator. Use the same saved Drafts and `--samples K` for a comparison.
Output paths, work artifacts, and resume state are separate from Babel's.

Native context acceptance is separate from parsing acceptance. These
Hundred Theorems files originate from several Isabelle libraries and AFP
developments; their imports and tool versions must be available in the
configured runtime. A native preflight failure stays an explicit context
failure. The adapter does not replace imports, add missing mathematical
assumptions, or silently substitute a theorem from another library.
Configure compatible Isabelle2026 session roots/dependencies for additional
imports before treating a target context as accepted.

The local regression suite validates all 58 aligned groups, the 99 emitted
contexts, compatibility paths, visible-only Draft generation, both handoffs,
and fake-adapter DSP replay. Native Isabelle2026 and live API experiments
still require the lab environment.
