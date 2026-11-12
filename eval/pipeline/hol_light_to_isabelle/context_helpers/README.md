# Most-match context experiment

This experiment compares the saved most-match ranking with bounded HOL Light
dependency retrieval for direct Sketch. All arms use one sample per target, the
same Sketch instructions, and the original Isabelle oracle, prefix and imports.
The checker runs its usual native Prove stage.

| Arm | Prompt reference selection |
|---|---|
| baseline | The references in the original extracted record. |
| context | Follow explicit references and simple aliases to earlier theorems. Select masked statements, definitions and candidate Isabelle signatures. Cross-file loads are optional. |
| context-native | Use the same candidate ranking. Resolve the Isabelle shortlist in the verifier's actual context before the oracle, and use the resolved names and typed propositions. |

The defaults follow two theorem edges and five unique helpers per target.
Reference caps come from the input record, normally 16,000 HOL Light characters
and 8,000 Isabelle characters. An independent whole-prompt character cap applies
to both arms. The existing vLLM client also checks model tokens and output
reserve. Scope and the masked source target take priority. Reports distinguish
a missing or ambiguous statement, traversal or size limits, and a candidate
that does not resolve in the native context. Later declarations and the target
are excluded. The native lookup returns signatures only, including all
propositions of a fact bundle when it fits the lookup limit.

The source index supports literal top-level prove declarations and simple
aliases. Reports record opaque bindings, possible local shadowing and unresolved
loads. Dependencies used implicitly inside tactics are outside the static scan.
Isabelle snapshot traversal is limited to
explicit imports found under the dataset's masked AFP and HOL snapshots.
Native availability is scoped to the pre-oracle context. A resolved signature
can still require a bridge, an instantiation or additional premises. A name
match is a candidate correspondence.

## Offline inspection

Run from the ITPEval checkout with the Python 3.10 main environment active. The
example uses one target. Use the same original records file and selection across
the arms.

~~~bash
cd /data/not_backed_up/yxu209/itpeval-modify
PIPE=eval.pipeline.hol_light_to_isabelle
RUN=eval/results/hol_light_to_isabelle_v2/most-match/context_helpers/pilot
TOPIC=Canonical_Models
TARGET=compact_canon_qfree
HELPER=eval/configs/hol_light_to_isabelle/context_helpers.example.json
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_most_match_2026.example.json
LLM=eval/configs/inference/api.example.json

python -m "$PIPE.most_match_pipeline.extract_hol_light" \
  --expected-root "$PWD" --topic "$TOPIC" --target-key "$TARGET" \
  --output "$RUN/records.jsonl"

python -m "$PIPE.context_helpers.workflow" \
  --expected-root "$PWD" --records "$RUN/records.jsonl" \
  --helper-config "$HELPER" --output-dir "$RUN" --inspect-only
~~~

Read the dependency graph, candidate statuses and old/new reference selections
in the run's context/inspection.jsonl. For a second-hop example, set the topic to
Conformal_Mappings and the target to Bloch before extracting. The report also
records unresolved identifiers, which can be tactics or theorem names.

## Optional cross-file retrieval

Set `"cross_file": true` in the helper config, or add `--cross-file` to a
context command. It defaults to false. `--no-cross-file` overrides a true
config value. The enabled runs use the `context-cross-file` and
`context-native-cross-file` arm directories, so both settings can use the same
run directory. Run both context settings with identical limits to compare their
selections. The baseline arm continues to use the saved references.

~~~bash
python -m "$PIPE.context_helpers.workflow" \
  --expected-root "$PWD" --records "$RUN/records.jsonl" \
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
`max_load_directives`. The theorem walk and prompt keep their existing helper
and character limits. Try `Polytope/Krein_Milman` to see the resolver follow
`Multivariate/paths.ml` into `Multivariate/convex.ml` and select
`CONVEX_HULL_EMPTY`.

## Lab inspection and paired runs

First check the native fact lookup with the same lab config. The control checks
fact bundles, types, visibility after leaving a scope, and target/later-fact
exclusion.

~~~bash
ITPEVAL_NATIVE_ISABELLE2026_CONFIG="$CFG" python -m unittest \
  discover -s tests/hol_light_to_isabelle/context_helpers -k NativeInspectionTests

python -m "$PIPE.context_helpers.workflow" \
  --expected-root "$PWD" --records "$RUN/records.jsonl" \
  --helper-config "$HELPER" --config "$CFG" --output-dir "$RUN" \
  --inspect-only --native-facts
~~~

The lab inspection opens the original target in the normal scratch context. It
performs fact lookup without model calls or proof search. The report is in
context-native/inspection.jsonl. It includes the snapshot-to-native selection
change and reports when a candidate is unavailable, dynamic or too large.

Run the paired sketches with one shared configuration:

~~~bash
COMMON=(--expected-root "$PWD" --records "$RUN/records.jsonl"
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
