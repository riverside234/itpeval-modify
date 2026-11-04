# HOL Light to Isabelle: most-match

This pipeline reads `hol_dataset/aligned-isabelle-hl-main/most-match` and uses the native Isabelle2026 DSP checker. It has separate records, Drafts, Sketches, verification outputs and compact preflight reports. Existing Babel Formal and Hundred Theorems commands remain available. API and vLLM inference profiles both work; only visible model content is retained.

## Dataset review and alignment

The supplied snapshot has 16 Isabelle statement files and 31 HOL Light files in each variant. Thirteen underscore-prefixed HOL files mirror named library files. Several named topics also share the same library. The loader uses explicit topic/file groups, supports the two-file Continuous_Extension and Improper_Integral topics, and caches repeated libraries without creating duplicate targets.

There are **353 unique exact/case-insensitive name candidates across 15 topics**. A candidate requires a unique completed HOL `prove` declaration, an identical masked HOL statement, and a unique Isabelle name. Candidate matching does **not** establish semantic equivalence; records retain `semantic_alignment_verified=false`. Coverage reports list unmatched and ambiguous declarations. `Poly_Roots` has zero automatic matches: source names start with `COMPLEX_`, and some target results generalize complex numbers to type classes. These need reviewed mappings and are not silently treated as aligned. Unsupported source proof generators are not fabricated into proofs.

Completed Isabelle proof files are never read by extraction or prompt construction. The oracle and verifier template come from `stmts/isabelle`, with residual proofs masked by the existing masker.

## Context policy

The model receives the complete selected HOL statement/proof, the exact Isabelle oracle, and selected references:

- HOL Light reference: **16,000 characters** by default. Select earlier helper statements and definitions, ranked by names used in the proof, identifier overlap and one dependency expansion. Keep the masked target statement for input validation; it is explicitly not a premise. Omit tactic programs and later source facts.
- Isabelle reference: **8,000 characters** by default. Select relevant earlier declarations and preserve active theory/locale/context headers, parameters and assumptions. Never include target or later proof declarations.
- Select whole snippets. If required scope/target material exceeds the budget, extraction reports an error instead of truncating it. Optional oversized snippets are omitted.

The caps include reference labels/separators. They are character counts, not estimated token counts, and exclude the selected proof, oracle, instructions and generated Draft. The largest selected source proof in this snapshot is about 30,000 characters. `isabelle_prompt_context` is the bounded model view; `isabelle_context_before_target` and `isabelle_theory_template` retain the full masked verifier context. Earlier masked helpers remain admitted background facts, consistent with the existing experiment.

Each record saves selected spans, hashes, budgets, omitted counts and original file hashes in `metadata.prompt_context`. Retrieval is deterministic. Changing budgets/selections changes prompt/input fingerprints, so stale results are not reused.

## Lab commands

Run from the repository root with the Python 3.10 main environment active. Dataset files and Isabelle/AFP installations must be inside this checkout.

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
PIPE=eval.pipeline.hol_light_to_isabelle.most_match_pipeline
DATA=eval/results/hol_light_to_isabelle_v2/most-match
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_most_match_2026.example.json

python -m "$PIPE.inventory" --expected-root "$PWD" \
  --output "$DATA/inventory.json"

python -m "$PIPE.extract_hol_light" --expected-root "$PWD" \
  --all-topics --all-targets \
  --source-context-chars 16000 --isabelle-context-chars 8000 \
  --output "$DATA/records.jsonl"
```

The dedicated config qualifies imports in `HOL-Analysis`, `HOL-Complex_Analysis`, `HOL-Algebra` and AFP `FOL_Compactness`. It expects Isabelle at `itpeval/_toolchains/Isabelle2026` and AFP sources at `external/afp-2026/thys`. Copy it to a `.local.json` and edit the paths if needed. Keep `base_session=HOL`; a parent containing the completed target theory is rejected. The existing AFP download command can install the sources and update this config:

```bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.prepare_afp \
  --expected-root "$PWD" --config "$CFG"
```

### Retry only the failures from f56944e

The completed report `20261103T030137Z-650c526a` has **241 passed contexts and 112 failed contexts**. All proof controls and the real Cross3 proof passed. The failures are 99 startup timeouts, six SIGKILL exits (137), and seven exits inside imported library proofs. A SIGKILL can indicate memory pressure or external termination; the report does not contain kernel evidence proving an OOM kill.

Use this command for the next lab run:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m eval.pipeline.hol_light_to_isabelle.v2_dsp.lab_preflight \
  --expected-root "$PWD" --dataset most-match \
  --failed-from eval/preflight_results/isabelle2026-most-match/20261103T030137Z-650c526a \
  --workers 8 --threads-per-worker 1 --memory-per-worker-gb 12 \
  --dependency-jobs 2 --dependency-threads 8 \
  --expected-contexts 112
```

This uses the dedicated example config; append `--config path/to/your.local.json` if your lab paths differ. It selects exactly the 112 failed contexts across eight topics. It **does not rerun** the 241 passed contexts, the successful native fixture, the 11 successful proof controls or the successful Cross3 proof. Installation/source validation and dependency/native/import-heap setup still run because the selected contexts require them. There are 112 context tests plus five prerequisite/selection checks. Append `--plan-only` to inspect the selection without executing Isabelle.

`--failed-from` is deliberately different from `--resume-from`: it selects historical failures even when the checker has changed, never copies previous passes, and labels the new report `failed_only`. A successful retry establishes only this subset. Missing failed targets or unknown failed checks are errors, not silently dropped tests. Do not combine it with `--all-targets` or `--resume-from`.

### Preflight without model calls

Use `--dataset most-match` on the shared command to test only this dataset. It routes to the dedicated config, selection policy and report folder; `both` continues to mean only Babel Formal plus Hundred Theorems.

```bash
python -m eval.pipeline.hol_light_to_isabelle.v2_dsp.lab_preflight \
  --expected-root "$PWD" --dataset most-match --workers 8
```

Add `--all-targets` for all 353 most-match candidates. The dedicated command below also accepts `--dataset most-match` explicitly.

Preview selection and scheduling:

```bash
python -m "$PIPE.v2_dsp.lab_preflight" --expected-root "$PWD" \
  --config "$CFG" --workers 8 --plan-only
```

Run the **65 representative contexts** (fresh extraction by default):

```bash
python -m "$PIPE.v2_dsp.lab_preflight" --expected-root "$PWD" \
  --config "$CFG" --workers 8 --threads-per-worker 1 \
  --memory-per-worker-gb 12 --expected-contexts 65
```

Selection covers first/middle/last declarations, longest selected proofs, deepest scopes and every source library in each matched topic. Eleven positive/negative native controls, the ML reconstruction fixture, a real Cross3 proof, setup and dependency checks give **83 checks** in this snapshot. A representative pass establishes readiness only for those contexts. To check every candidate:

```bash
python -m "$PIPE.v2_dsp.lab_preflight" --expected-root "$PWD" \
  --config "$CFG" --workers 8 --all-targets --expected-contexts 353
```

Optional `--input "$DATA/records.jsonl"` uses saved records and their saved caps. Reports are written to `eval/preflight_results/isabelle2026-most-match/<run>/`, using at most six compact files allowed by `.gitignore`. Full build artifacts stay under ignored `itpeval/.runs/preflight/`. No diagnostics ZIP or separate replay build is created.

### Resume an interrupted preflight

`--resume-from` accepts a previous report directory or `report.json`. It creates a new report and carries forward only successful context checks with matching target/template hashes and checked backend/config identity. Failed, blocked, missing or changed contexts are retried. Setup, dependency freshness checks and proof controls run again; carried context passes are explicitly marked `resumed_from` and remain in the full denominator. Repository commits containing only report/orchestration changes do not invalidate an otherwise identical backend; checker/source/config changes do.

The new `p9` checker adds import heaps, so old `p8` passes cannot be resumed as new passes. Use the failure-only command above to investigate just the failures from the completed old run. Future interrupted runs made with this checker can use `--resume-from` when input and backend identities still match.

### Import heaps and measured performance

Dependency sessions have separate `--dependency-jobs` (default up to 4) and `--dependency-threads` (default up to 8) limits. They do not inherit the 1-thread-per-theorem policy. Dependency builds use `parallel_proofs=1`; theorem/checker builds retain `parallel_proofs=0`. CPU and memory caps apply (dependency admission reserves at least 1 GiB per thread and at least `--memory-per-worker-gb` per session; these are estimates, not hard limits).

The `77cbbe9` log shows why this matters: HOL-Analysis took 34m44s and its dependent HOL-Complex_Analysis took another 3m21s, under the old `-j 60 -o threads=1 -o parallel_proofs=0` policy. The total 39m dependency build used only 1.35 CPU-seconds per wall-second. More session jobs could not accelerate that dependency chain. Build options are described in the [official Isabelle options](https://github.com/isabelle-prover/mirror-isabelle/blob/master/etc/options).

The newer `f56944e` report confirms warm owning-session reuse: dependency setup took about **35 seconds**, with **22 seconds** in the Isabelle build log. However, its context phase took **6,329.8 seconds (105.5 minutes)** for 322 newly scheduled contexts, of which 210 passed and 112 failed; another 31 passes were resumed. The reported 3.052 completed contexts/minute includes failures. Successful new contexts averaged about 1.99/minute. Its overlap factor of 52.039 is not CPU utilization or measured speedup.

The cause visible in worker logs is repeated source compilation: ROOT `sessions HOL-Analysis` makes theory sources available but does not load that session's heap as the worker parent. The old HOL-based workers each recompiled imported theories such as `Elementary_Metric_Spaces`, even though the owning session had been built. With 60 concurrent workers, the report shows long startup waits, timed library tactics and killed processes; resource contention is a likely contributor.

Most-match now builds a reusable `DSP_Imports_*` parent for **each exact original import set** before theorem workers start. The 112 failures require eight such heaps. Each contains the native adapter and only the original imported theory closure. It contains no selected theorem, masked dataset prefix or later dataset declarations. Different import sets are not combined, and the original target-theory ancestor guard remains active. A theorem worker keeps the original driver imports and inherits the matching prepared heap. This applies to preflight, the runner's context gate and Sketch compilation, including single-worker Prove runs.

Import builds use the separate dependency job/thread budget and dependency timeout. Their ROOT options pin `threads` and `parallel_proofs`, so the theorem workers' one-thread options cannot change those cached build options. Ordinary `isabelle build -b` rechecks source/heap freshness on every batch; there is no clean flag or blind success marker. The first run must compile these new heaps once and may take time; later runs can reuse them. Actual wall-time improvement requires the lab measurement.

Start this retry with eight theorem workers and two import-build jobs of eight threads each. Most-match now defaults to a **12 GiB admission allowance per worker**; this is not an enforced memory limit. Up to 60 workers remain available explicitly, subject to CPU/memory caps. Per-context compact reports preserve startup time, time after readiness and sampled owned-process RSS, including failed workers. Shared RSS pages may be counted more than once, and short memory peaks can be missed. Both completed and successful throughput are reported. Full local metrics remain under ignored runtime directories; the Git report still has at most six files.

The relevant distinction between session imports and parent heaps follows the [official session dependency implementation](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Build/sessions.scala).

### Direct to Sketch and Prove (default)

Native `run`, `export_dsp`, `generate_sketch`, `prove` and the single-record
`preflight` commands now default to **HOL Light proof → Isabelle Sketch**.
Supply `--records` to the runner; it does not generate or consume a Draft.
`--sketch-source hol-light-proof` remains an accepted explicit spelling. The
same default applies to the Babel and Hundred native command-line adapters.
Saved artifact mode tags and existing Python API defaults remain unchanged.

```bash
python -m "$PIPE.v2_dsp.run" --expected-root "$PWD" \
  --config "$CFG" --records "$DATA/records.jsonl" \
  --workers 8 --samples 1 \
  --dsp-output "$DATA/direct/inputs.jsonl" \
  --sketch-output "$DATA/direct/sketches.jsonl" \
  --prove-output "$DATA/direct/prove.jsonl" --output "$DATA/direct/verified.jsonl"
```

To check existing direct Sketches without model calls:

```bash
python -m "$PIPE.v2_dsp.prove" --expected-root "$PWD" --config "$CFG" \
  --input "$DATA/direct/sketches.jsonl" --workers 8 \
  --prove-output "$DATA/direct/prove.jsonl" --output "$DATA/direct/verified.jsonl"
```

Saved-Draft mode remains available. `--drafts` selects it automatically when
`--sketch-source` is omitted. For generic `--input` paths, select
`--sketch-source draft` explicitly; an input/mode mismatch is an error.

```bash
python -m "$PIPE.generate_draft" --expected-root "$PWD" \
  --input "$DATA/records.jsonl" --output "$DATA/drafts.jsonl"

python -m "$PIPE.v2_dsp.run" --expected-root "$PWD" \
  --config "$CFG" --sketch-source draft --drafts "$DATA/drafts.jsonl" \
  --samples 1 --workers 8 \
  --dsp-output "$DATA/draft/inputs.jsonl" \
  --sketch-output "$DATA/draft/sketches.jsonl" \
  --prove-output "$DATA/draft/prove.jsonl" --output "$DATA/draft/verified.jsonl"
```

Both modes support `--topic`, `--target-key`, `--limit`, `--samples`, and
`--no-resume`. `--dry-run` previews the prompt without Isabelle or model calls.
Use `--llm-config` for standalone generation and `--sketch-llm-config` for the
runner to choose an API/vLLM profile. `--workers` controls native builds, not
LLM request concurrency. Context failures are recorded before inference.

### Review of commit ea7bb55: compact_canon_qfree

The `Canonical_Models/compact_canon_qfree` sample (HOL name `COMPACT_CANON_QFREE`)
reached its proof and completed **two Sledgehammer searches/reconstructions**.
Checker p13 also repaired one failed `by blast` at line 39. The final failure
was another explicit `by blast`, at line 56, which hit the 10-second method
budget after 10.464 seconds. This was a local method timeout; the logged whole
verification took 89.053 seconds against a configured 1,800-second target budget.
The result does not indicate a broken installation or unavailable ATPs.

The sketch uses equivalent set comprehensions with different binder/conjunct
orders. At line 39 it asks `blast` to transfer a semantic predicate between
these representations; the trace shows it failing and native search recovering
with `Collect_cong`. Later it gives `blast` a general monotonicity rule and large
set expressions instead of first matching the representations and instantiating
the rule. The later compactness step was never executed, so its success remains
unknown.

Checker **p14** handles a local timeout of a terminal `by` transactionally:
restore the saved state, skip the heuristic portfolio, and run bounded native
Sledgehammer/reconstruction. The replacement must close the original local
obligation before execution continues. Partial effects on the proof state from
the failed method are discarded; the original sketch remains in the result.
Whole-target deadlines, external interrupts and timeouts in structural commands
such as `apply` still abort. Missing source facts/methods and malformed Isar
remain errors. There is no separate replay build.

`search_summary` and batch `search_activity` now report
`terminal_method_timeouts` separately from optional candidate timeouts.
The original source attempt has `timeout_scope=terminal_method`; its repair has
`repair_reason=method_timeout`. A failed repair reports the underlying search
failure and original source line. Known optional heuristics that require absent
`sos`, `norm_sum` or `norm_scaleR` support are skipped; source commands are never
silently skipped.

The direct prompt advances to `most_match_direct_sketch_v5` (shared Babel/Hundred
p8). It calls for explicit helper instantiation, consistent local abbreviations,
separate set equality/inclusion bridges, and correct `obtains` witness handling.
The input context caps and oracle are unchanged. Draft prompts are unchanged.

Regenerate and check **only this failed theorem** after syncing:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
PIPE=eval.pipeline.hol_light_to_isabelle.most_match_pipeline
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_most_match_2026.example.json
RUN=eval/results/hol_light_to_isabelle_v2/most-match/v2-dsp-isabelle2026/canonical-models-compact-canon-qfree/direct-p14

python -m "$PIPE.extract_hol_light" --expected-root "$PWD" \
  --topic Canonical_Models --target-key compact_canon_qfree \
  --output "$RUN/records.jsonl"

python -m "$PIPE.v2_dsp.run" --expected-root "$PWD" \
  --config "$CFG" --records "$RUN/records.jsonl" --samples 1 --workers 1 \
  --dsp-output "$RUN/inputs.jsonl" --sketch-output "$RUN/sketches.jsonl" \
  --prove-output "$RUN/prove.jsonl" --output "$RUN/verified.jsonl"
```

Use your most-match `.local.json` for `CFG` if it contains different lab paths.
Direct-to-Sketch remains the default. This makes one new Sketch call and checks
only that theorem, including its prerequisite context/import setup. Old results
are retained. Updated adapter hashes require the cached native/import heaps to
be refreshed once. Add `--dry-run` to the runner to inspect its prompt first.

To isolate the backend change without a model call, check the saved failing
sketch with a separate output path:

```bash
OLD=eval/results/hol_light_to_isabelle_v2/most-match/v2-dsp-isabelle2026/canonical-models-compact-canon-qfree/direct/verified.jsonl
python -m "$PIPE.v2_dsp.prove" --expected-root "$PWD" --config "$CFG" \
  --input "$OLD" --workers 1 \
  --prove-output "$RUN/saved-prove.jsonl" --output "$RUN/saved-verified.jsonl"
```

This is a normal Prove run on the saved sketch, not an additional verification
stage. It tests recovery independently of the prompt change; it may still fail
at a later obligation. Native compilation and theorem completion must be checked
on the lab; offline tests do not establish them.

### Review of commit 852f31b: finite_subset_instance

The committed direct result for `Canonical_Models/finite_subset_instance`
failed at sketch line 12:

```isabelle
by (intro impI, rule exI[where x="{}"], simp)
```

The logged goal was already existential. `intro impI` requires an applicable
object implication and failed before the witness method. The import/context
setup succeeded; **zero heuristics and zero Sledgehammer calls** ran. This is
an explicit-method failure, not evidence of an ATP timeout or missing AFP.
The later insertion case also uses a bare `proof` followed by a repeated premise
introduction; its case structure needs revision rather than just removing impI.

Checker **p13** can recover ordinary failed terminal `by` methods from the
unchanged saved state using the existing bounded heuristic/Hammer search.
Failed partial progress is discarded. The replacement must close the same
local obligation before the next source command, and only the executed
replacement enters `isabelle_proof`. Original sketches remain in
`isabelle_sketch`, with the failed command and recovery recorded in the trace.
`search_summary` and final summaries expose `terminal_repair_attempts` and
`terminal_repair_successes`. A repair failure retains the underlying search
error plus `repair_of_command` / `repair_of_line`.

Only Isabelle's ordinary method-application/completion errors are eligible.
Unknown facts/methods, syntax/type errors, invalid proof structure, forbidden
commands, source-command timeouts, and interrupts still fail. Target closure
and all existing context/admission guards still apply. This is a general shared
native-backend change, not a target-name special case. There is no separate replay.

The direct prompt advances to `most_match_direct_sketch_v4`. It distinguishes
meta/object implication, explains induction case premises and hypotheses,
requires explicit existential witnesses, and distinguishes `proof -` from a
bare `proof`. Uncertain method chains should become well-scoped search gaps
with their supporting facts. The Draft and Draft-to-Sketch prompts are unchanged.
Prompt/checker fingerprints invalidate old cached generation/verification.

After syncing, regenerate and check **only this failed theorem**:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
PIPE=eval.pipeline.hol_light_to_isabelle.most_match_pipeline
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_most_match_2026.example.json
RUN=eval/results/hol_light_to_isabelle_v2/most-match/v2-dsp-isabelle2026/canonical-models-finite-subset-instance/direct-p13

python -m "$PIPE.extract_hol_light" --expected-root "$PWD" \
  --topic Canonical_Models --target-key finite_subset_instance \
  --output "$RUN/records.jsonl"

python -m "$PIPE.v2_dsp.run" --expected-root "$PWD" \
  --config "$CFG" --records "$RUN/records.jsonl" --samples 1 --workers 1 \
  --dsp-output "$RUN/inputs.jsonl" --sketch-output "$RUN/sketches.jsonl" \
  --prove-output "$RUN/prove.jsonl" --output "$RUN/verified.jsonl"
```

Set `CFG` to your existing most-match `.local.json` if its installation paths
or settings differ. This makes one new Sketch call plus the required context
and proof checks. It does not rerun the broad preflight cohort. The changed
native adapter requires its cached infrastructure/import heaps to be rebuilt
once. Add `--dry-run` to the second command to preview the new direct prompt.
Native proof success must be established on the lab; offline tests cannot prove
that the new model sample, or the old structurally flawed sample, will close.

## Parallel execution

`--workers` accepts 1–60; default 1 preserves existing serial behavior. With parallel jobs, the default is one Isabelle thread per worker. Effective workers are capped by CPU affinity and available memory divided by `--memory-per-worker-gb` (most-match default 12 GiB; Babel/Hundred default 4 GiB). Thus 60 most-match workers ordinarily require at least 60 available CPUs and roughly 720 GiB available RAM at the default allowance. This is a scheduling allowance, not an enforced process memory limit; long theory imports can require more. Increase the allowance or reduce workers if the lab shows memory pressure. The effective plan is printed and recorded.

Dependency sessions and the native adapter are prepared once, followed by the exact-import heaps described above. Each most-match target uses only its matching original imports; complete owning sessions never become the target parent. Each job has a unique session and directory, with `-j 1` and its own deadline/process group. Only the coordinator writes shared reports/results. Verification checkpoints preserve completed samples, and resume checks their fingerprints. Ctrl-C cancels queued jobs and terminates only owned Isabelle/ATP descendants.

The shared Babel/Hundred native runner, Prove command and lab preflight also accept these parallel flags. Do not launch multiple batches against the same output files. No separate replay verification has been reintroduced.

Build options and owning sessions were checked against the official [Isabelle build implementation](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Build/build.scala), [HOL session definitions](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/ROOT), and the Isabelle2026 source archive. Actual Isabelle2026 acceptance runs require the Linux lab installation.
