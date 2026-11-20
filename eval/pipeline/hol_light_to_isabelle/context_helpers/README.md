# HOL Light to Isabelle context and helper proof experiments

Babel Formal, Hundred Theorems, and most-match share a direct Sketch workflow
for testing bounded HOL Light dependency retrieval and complete source helper
proofs. Each arm uses one sample per target and the dataset's Isabelle oracle,
prefix and imports.

| Arm | Prompt reference selection |
|---|---|
| baseline | The references in the original extracted record. |
| context | Follow explicit references and simple aliases to earlier theorems. Select masked statements, definitions and candidate Isabelle signatures. Cross-file loads are optional. |
| context-native | Resolve the Isabelle shortlist in the verifier's actual context before the oracle. Supply resolved names and typed propositions. |
| expand | Use the Mode A references and add complete HOL Light proofs for selected dependencies. |
| expand-native | Use the native Mode A references and add complete HOL Light proofs where a unique live name candidate has yet to be supplied. |

The defaults follow two theorem edges and five unique helpers per target.
For Babel Formal and Hundred Theorems, the `baseline` arm uses the full
references. Context arms default to 16,000 HOL Light and 8,000 Isabelle
characters. Change `source_context_chars` and `isabelle_context_chars` in
`--helper-config` for those datasets. Most-match takes its caps from the
extracted record.

The whole-prompt guard `max_prompt_chars` defaults to 100,000 and applies
to every arm. Some full-reference Hundred Theorems prompts exceed it. An
inspection reports `prompt_context_overflow` and the measured size. For a
paired run on such a target, set a higher limit in the helper config if the
chosen model has sufficient context. Use that config for both arms. The
vLLM client also checks input tokens and reserves room for model output.

Scope and the masked source target take priority. Reports distinguish
a missing or ambiguous statement, traversal or size limits, and a candidate
that does not resolve in the native context. Retrieved Isabelle references
exclude the target and later declarations. The native lookup returns signatures only, including all
propositions of a fact bundle when it fits the lookup limit.

The source index supports literal top-level prove declarations and simple
aliases. Reports record opaque bindings, possible local shadowing and unresolved
loads. Dependencies used implicitly inside tactics are outside the static scan.
Babel Formal and Hundred Theorems load HOL Light source by aligned ID from
`eval/data` and check its hashes against the extraction record. Most-match
uses its proof and statement files. Isabelle snapshot traversal follows
explicit imports available in the shared masked AFP and HOL snapshots.
Native availability is scoped to the pre-oracle context. A resolved signature
can still require a bridge, an instantiation or additional premises. A name
match is a candidate correspondence.

## Offline inspection

Run from the ITPEval checkout with the Python 3.10 main environment active. The
example uses one target. Use the same original records file and selection across
the arms. Existing records from each extractor work with this command.

| `--dataset` | Extractor package | Topic | Target key |
|---|---|---|---|
| `babel-formal` | `babel_formal_pipeline` | `circle_average` | `circleAverage_center_eq` |
| `hundred-theorems` | `hundred_theorems_pipeline` | `015_the_fundamental_theorem_of_integral_calculus` | `rsum_bound` |
| `most-match` | `most_match_pipeline` | `Canonical_Models` | `compact_canon_qfree` |

~~~bash
cd /data/not_backed_up/yxu209/itpeval-modify
PIPE=eval.pipeline.hol_light_to_isabelle
DATASET=babel-formal
EXTRACTOR=babel_formal_pipeline
RUN="eval/results/hol_light_to_isabelle_v2/$DATASET/context_helpers/pilot"
TOPIC=circle_average
TARGET=circleAverage_center_eq
HELPER=eval/configs/hol_light_to_isabelle/context_helpers.example.json
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.example.json
LLM=eval/configs/inference/api.example.json

python -m "$PIPE.$EXTRACTOR.extract_hol_light" \
  --expected-root "$PWD" --topic "$TOPIC" --target-key "$TARGET" \
  --output "$RUN/records.jsonl"

python -m "$PIPE.context_helpers.workflow" \
  --expected-root "$PWD" --dataset "$DATASET" --records "$RUN/records.jsonl" \
  --helper-config "$HELPER" --output-dir "$RUN" --inspect-only
~~~

Read the dependency graph, candidate statuses and reference selections in
`context/inspection.jsonl` under the run directory. For a most-match run, use
`v2_dsp_most_match_2026.example.json` and the most-match row in the table.
The report includes unresolved identifiers that may be tactics or theorem
names.

## Optional cross-file retrieval

Set `"cross_file": true` in the helper config, or add `--cross-file` to a
context command. It defaults to false. `--no-cross-file` overrides a true
config value. The enabled runs append `-cross-file` to their arm directories. Use the same
run directory and limits to compare the two settings. The baseline arm uses
the saved references.

~~~bash
python -m "$PIPE.context_helpers.workflow" \
  --expected-root "$PWD" --dataset "$DATASET" --records "$RUN/records.jsonl" \
  --helper-config "$HELPER" --output-dir "$RUN" --cross-file --inspect-only
~~~

The resolver follows top-level literal `needs`, `loadt`, and `loads` in order.
It visits nested loads and resolves each proof's names at the point where that
proof was declared. Duplicate `needs` uses the load basename and file identity.
`loadt` and `loads` may rebind names. The report records the load chain, origin,
cycles, missing entries, hash mismatches, and budget limits. The manifest
supplies the local resolution for each literal path. The scan does not run
OCaml or search its runtime load path. See the
[HOL Light loader](https://github.com/jrh13/hol-light/blob/master/hol_loader.ml).

The [default manifest](../../../configs/hol_light_to_isabelle/context_hol_light_loads.json)
pins 23 files available in the dataset. An unmapped literal is reported even
when a different file has the same basename. To add sources, copy the manifest
and set `source_load_manifest` to your copy. It has `version: 1`, a
repository-local `root`, and `files` keyed by exact load paths. Each entry
gives a `proof` path under that root and a `proof_sha256`. Optional
`statement` and `statement_sha256` fields give a paired masked snapshot.
Hashes use UTF-8 text with normalized line endings. For a proof-only entry,
the model receives only the proposition extracted from a supported literal
`prove` declaration. Definition excerpts require a matching masked snapshot.

The load walk is bounded by `max_load_depth`, `max_load_files`, and
`max_load_directives`. It is available for each dataset and depends on which
literal loads the source exposes. In most-match, `Polytope/Krein_Milman` follows
`Multivariate/paths.ml` into `Multivariate/convex.ml` and select
`CONVEX_HULL_EMPTY`.

Use records extracted with [`--isabelle-reference-proofs`](../README.md#include-isabelle-helper-proofs-in-the-model-context)
to include matching Isabelle helper proofs in any context arm. The proof
examples share the Isabelle reference cap with signatures and scope. The workflow
places these runs under an `isabelle-reference-proofs` subdirectory of the
run directory. This also works with `--cross-file` and `--native-facts`.

## Lab inspection and paired runs

First check the native fact lookup with the same lab config. The control checks
fact bundles, types, visibility after leaving a scope, and target/later-fact
exclusion.

~~~bash
ITPEVAL_NATIVE_ISABELLE2026_CONFIG="$CFG" python -m unittest \
  discover -s tests/hol_light_to_isabelle/context_helpers -k NativeInspectionTests

python -m "$PIPE.context_helpers.workflow" \
  --expected-root "$PWD" --dataset "$DATASET" --records "$RUN/records.jsonl" \
  --helper-config "$HELPER" --config "$CFG" --output-dir "$RUN" \
  --inspect-only --native-facts
~~~

The lab inspection opens the original target in the normal scratch context. It
performs fact lookup without model calls or proof search. The report is in
context-native/inspection.jsonl. It includes the snapshot-to-native selection
change and reports when a candidate is unavailable, dynamic or too large.
Native runs with the HOL parent record Hundred Theorems targets in Core Set
as `unavailable_context`.

Run the paired sketches with one shared configuration:

~~~bash
COMMON=(--expected-root "$PWD" --dataset "$DATASET" --records "$RUN/records.jsonl"
  --helper-config "$HELPER" --config "$CFG" --llm-config "$LLM"
  --output-dir "$RUN" --samples 1 --workers 1)

python -m "$PIPE.context_helpers.workflow" "${COMMON[@]}" --helper-mode baseline
python -m "$PIPE.context_helpers.workflow" "${COMMON[@]}" --helper-mode context
python -m "$PIPE.context_helpers.workflow" "${COMMON[@]}" --helper-mode context --native-facts
~~~

Use a different API or vLLM profile by changing LLM for every arm. For a batch,
the existing worker and memory admission settings apply. The arm directories
hold their own inputs, sketches, verification results and resume state.
Inspection runs use a separate report file from the Sketch/Prove run.
Keep concurrent invocations in different run directories.

After the baseline and an enhanced arm finish, comparison.json pairs results
with the same original input and model/verifier settings. It reports matched
successes and failures, prompt size and token usage, stage, timings, and native
search counts. Selected fact mentions are lexical observations from the
completed proof. An arm's selection.jsonl records its context decisions,
including blocked targets, and verified.summary.json records sample outcomes.
Complete run artifacts live under the ignored results directory.

## Mode B source proof expansion

Use `--helper-mode expand` with the same original extraction records and
helper config. The HOL Light reference stays proof-masked. The separate
`source_helper_bundle` contains whole source proofs in child-before-parent
order with their statements, spans, dependency references and candidate
Isabelle facts. The model uses these proofs to establish required instances
as local `have` facts. The existing native Prove stage checks those local
proofs while closing the original target.

The default expansion budgets are configurable in `--helper-config`.

| Setting | Characters |
|---|---:|
| `max_helper_proof_chars` per proof | 12,000 |
| `max_total_helper_proof_chars` for all proof text | 32,000 |
| `max_helper_support_chars` including statements, labels and instructions | 40,000 |
| `max_prompt_chars` for the complete prompt | 100,000 |

A package that exceeds a limit stays out of the prompt in its entirety.
`source_helper_expansion` in the report records the budget, provenance and
omitted dependencies. Snapshot-only evidence keeps a helper eligible.
With `--native-facts`, a unique selected and live-resolved exact-name match
defers expansion for that helper. Its mathematical alignment is unreviewed.

Inspect the bundle selection offline. The report is at
`$RUN/expand/inspection.jsonl`. To inspect an example with two levels, use
`Conformal_Mappings/Bloch` in most-match.

~~~bash
python -m "$PIPE.context_helpers.workflow" \
  --expected-root "$PWD" --dataset "$DATASET" --records "$RUN/records.jsonl" \
  --helper-config "$HELPER" --output-dir "$RUN" --helper-mode expand --inspect-only
~~~

The lab control checks a two-level chain of local facts with native
Sledgehammer reconstruction. Run it before the paired model calls.

~~~bash
ITPEVAL_NATIVE_ISABELLE2026_CONFIG="$CFG" python -m unittest \
  discover -s tests/hol_light_to_isabelle/context_helpers -k NativeExpansionTests

python -m "$PIPE.context_helpers.workflow" "${COMMON[@]}" --helper-mode context
python -m "$PIPE.context_helpers.workflow" "${COMMON[@]}" --helper-mode expand
~~~

Apply `--native-facts` or `--cross-file` to both commands when testing those
settings. The comparison pairs matching Mode A and Mode B selections and
shows the added proof characters, total support characters, token usage and
native outcomes. If a Mode A result predates expansion, rerun its command
to refresh the comparison metadata. Compatible Sketch and Prove artifacts
can resume. Full bundles are available in the expand arm's `inputs.jsonl`.
`--isabelle-reference-proofs` on the extraction command can be used in both
arms to include eligible Isabelle proof examples.
