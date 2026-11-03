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

### Preflight without model calls

Use `--dataset most-match` on the shared command to test only this dataset. It routes to the dedicated config, selection policy and report folder; `both` continues to mean only Babel Formal plus Hundred Theorems.

```bash
python -m eval.pipeline.hol_light_to_isabelle.v2_dsp.lab_preflight \
  --expected-root "$PWD" --dataset most-match --workers 60
```

Add `--all-targets` for all 353 most-match candidates. The dedicated command below also accepts `--dataset most-match` explicitly.

Preview selection and scheduling:

```bash
python -m "$PIPE.v2_dsp.lab_preflight" --expected-root "$PWD" \
  --config "$CFG" --workers 60 --plan-only
```

Run the **65 representative contexts** (fresh extraction by default):

```bash
python -m "$PIPE.v2_dsp.lab_preflight" --expected-root "$PWD" \
  --config "$CFG" --workers 60 --threads-per-worker 1 \
  --memory-per-worker-gb 4 --expected-contexts 65
```

Selection covers first/middle/last declarations, longest selected proofs, deepest scopes and every source library in each matched topic. Eleven positive/negative native controls, the ML reconstruction fixture, a real Cross3 proof, setup and dependency checks give **82 checks** in this snapshot. A representative pass establishes readiness only for those contexts. To check every candidate:

```bash
python -m "$PIPE.v2_dsp.lab_preflight" --expected-root "$PWD" \
  --config "$CFG" --workers 60 --all-targets --expected-contexts 353
```

Optional `--input "$DATA/records.jsonl"` uses saved records and their saved caps. Reports are written to `eval/preflight_results/isabelle2026-most-match/<run>/`, using at most six compact files allowed by `.gitignore`. Full build artifacts stay under ignored `itpeval/.runs/preflight/`. No diagnostics ZIP or separate replay build is created.

### Resume an interrupted preflight

`--resume-from` accepts a previous report directory or `report.json`. It creates a new report and carries forward only successful context checks with matching target/template hashes and checked backend/config identity. Failed, blocked, missing or changed contexts are retried. Setup, dependency freshness checks and proof controls run again; carried context passes are explicitly marked `resumed_from` and remain in the full denominator. Repository commits containing only report/orchestration changes do not invalidate an otherwise identical backend; checker/source/config changes do.

For the interrupted 353-context run committed as `77cbbe9`:

```bash
python -m eval.pipeline.hol_light_to_isabelle.v2_dsp.lab_preflight \
  --expected-root "$PWD" --dataset most-match --all-targets --workers 60 \
  --dependency-jobs 4 --dependency-threads 8 \
  --resume-from eval/preflight_results/isabelle2026-most-match/20261103T012707Z-994fa284
```

With the same inputs/backend this reuses 31 context passes and schedules the other 322. Look for `RESUME` near the start. This old interrupted report truncated its per-context payloads; retain its lab-local `local_artifacts` directory (`backend.json` and `checks.full.jsonl`). Missing legacy evidence produces a clear error rather than trusting theorem names. New reports store small resume fingerprints directly, so future resumes do not require these local full payloads. `--plan-only --resume-from ...` previews prior pass counts without running Isabelle; final eligibility is checked at runtime.

### Dependency build performance

Dependency sessions have separate `--dependency-jobs` (default up to 4) and `--dependency-threads` (default up to 8) limits. They do not inherit the 1-thread-per-theorem policy. Dependency builds use `parallel_proofs=1`; theorem/checker builds retain `parallel_proofs=0`. CPU and memory caps apply (dependency admission reserves at least 1 GiB per thread and at least `--memory-per-worker-gb` per session; these are estimates, not hard limits).

The `77cbbe9` log shows why this matters: HOL-Analysis took 34m44s and its dependent HOL-Complex_Analysis took another 3m21s, under the old `-j 60 -o threads=1 -o parallel_proofs=0` policy. The total 39m dependency build used only 1.35 CPU-seconds per wall-second. More session jobs could not accelerate that dependency chain. Build options are described in the [official Isabelle options](https://github.com/isabelle-prover/mirror-isabelle/blob/master/etc/options).

`isabelle build -b` still checks and reuses current heaps; no clean/rebuild flag or blind success marker is used. A warm rerun should avoid unchanged sessions; actual speedup and cache reuse must be confirmed on the lab. The dependency command and timings are recorded. Context reports also record wall time, completed worker time and throughput, with a progress heartbeat while parallel jobs are pending. Their overlap metric is not a measured speedup or CPU-utilization percentage.

### Draft, Sketch and Prove

Generate Drafts (append `--limit 1` for a smoke test, or `--dry-run` to inspect the first prompt):

```bash
python -m "$PIPE.generate_draft" --expected-root "$PWD" \
  --input "$DATA/records.jsonl" --output "$DATA/drafts.jsonl"
```

Generate Sketches from those Drafts, then compile independent samples concurrently:

```bash
python -m "$PIPE.v2_dsp.run" --expected-root "$PWD" \
  --config "$CFG" --drafts "$DATA/drafts.jsonl" --samples 1 \
  --workers 60 --threads-per-worker 1 \
  --dsp-output "$DATA/draft/inputs.jsonl" \
  --sketch-output "$DATA/draft/sketches.jsonl" \
  --prove-output "$DATA/draft/prove.jsonl" --output "$DATA/draft/verified.jsonl"
```

Direct source proof to Sketch, using separate outputs:

```bash
python -m "$PIPE.v2_dsp.run" --expected-root "$PWD" \
  --config "$CFG" --sketch-source hol-light-proof --records "$DATA/records.jsonl" \
  --workers 60 --samples 1 \
  --dsp-output "$DATA/direct/inputs.jsonl" \
  --sketch-output "$DATA/direct/sketches.jsonl" \
  --prove-output "$DATA/direct/prove.jsonl" --output "$DATA/direct/verified.jsonl"
```

To compile existing Sketches without generating new ones:

```bash
python -m "$PIPE.v2_dsp.prove" --expected-root "$PWD" --config "$CFG" \
  --input "$DATA/draft/sketches.jsonl" --workers 60 \
  --prove-output "$DATA/draft/prove.jsonl" --output "$DATA/draft/verified.jsonl"
```

Both modes also support `--topic Cross3 --target-key cross_refl`, `--limit`, `--samples`, and `--no-resume`. Use `--llm-config` for Draft and `--sketch-llm-config` for the runner to select an existing API or vLLM profile. `--workers` controls native builds, not LLM request concurrency. The runner validates contexts before inference; context failures are recorded and do not spend model calls.

## Parallel execution

`--workers` accepts 1–60; default 1 preserves existing serial behavior. With parallel jobs, the default is one Isabelle thread per worker. Effective workers are capped by CPU affinity and available memory divided by `--memory-per-worker-gb` (default 4 GiB). Thus 60 workers ordinarily require at least 60 available CPUs and roughly 240 GiB available RAM. This is a scheduling allowance, not an enforced process memory limit; long theory imports can require more. Increase the allowance or reduce workers if the lab shows memory pressure. The effective plan is printed and recorded.

Dependency sessions are built once with bounded `isabelle build -j`, then the native parent is prepared before target jobs start. Dependency sessions do not become the proof state's parent: each target still imports only its original dependencies. Each job has a unique session and directory, with `-j 1` and its own deadline/process group. Only the coordinator writes shared reports/results. Verification checkpoints preserve completed samples, and resume checks their fingerprints. Ctrl-C cancels queued jobs and terminates only owned Isabelle/ATP descendants.

The shared Babel/Hundred native runner, Prove command and lab preflight also accept these parallel flags. Do not launch multiple batches against the same output files. No separate replay verification has been reintroduced.

Build options and owning sessions were checked against the official [Isabelle build implementation](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Build/build.scala), [HOL session definitions](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/ROOT), and the Isabelle2026 source archive. Actual Isabelle2026 acceptance runs require the Linux lab installation.
