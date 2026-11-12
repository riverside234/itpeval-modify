# Most-match context experiment

This experiment compares the saved most-match ranking with bounded HOL Light
dependency retrieval for direct Sketch. All arms use one sample per target, the
same Sketch instructions, and the original Isabelle oracle, prefix and imports.
The checker runs its usual native Prove stage.

| Arm | Prompt reference selection |
|---|---|
| baseline | The references in the original extracted record. |
| context | Follow explicit references and simple aliases to earlier theorems in the same HOL Light file. Select masked statements, definitions and candidate Isabelle signatures from masked snapshots. |
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
aliases. Literal loads, opaque bindings and possible local shadowing are
reported. The pilot does not resolve cross-file HOL Light loads or recover
implicit theorem uses inside tactics. Isabelle snapshot traversal is limited to
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
