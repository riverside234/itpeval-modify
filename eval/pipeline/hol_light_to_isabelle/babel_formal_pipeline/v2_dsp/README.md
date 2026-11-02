# Isabelle2026 native DSP backend (default)

`v2_dsp/` is the default for both Babel Formal and Hundred Theorems. The original
DSP/PISA/Isabelle2021 implementation is preserved separately in
[`v2_dsp_pisa/`](../v2_dsp_pisa/README.md), including its copied upstream checker
and recent runtime fixes. `v2_itpeval/` still uses Isabelle2024.

Both native input modes remain available: saved mathematical Draft to Sketch,
and HOL Light proof directly to Sketch. API and Qwen/vLLM inference are unchanged.

## Verification

There is **no separate replay verification** in either DSP backend. Native
Isabelle2026 executes the selected Sketch, tries DSP-style heuristics at gaps,
then calls Sledgehammer and executes its reconstructed commands. Success requires
complete target closure, an admissible completed proof, the matching request
identity, and a successful native process exit. Sledgehammer's internal preplay
is still part of proof search; it is not a second whole-proof verification stage.

`verified` and `prove_success` describe this one native job;
`verification_method` is `isabelle2026_native_completion`. There are no new
`native_replay` or `replay_verified` fields. `prove.jsonl` and `verified.jsonl`
store the same completed result. `--skip-prove` and `--replay-only` are removed.
Use `--skip-sketch` to check a saved Sketch without model calls.

Earlier masked helpers are admitted background. The selected theorem and its
new intermediate claims must be proved with `quick_and_dirty` and `smt_oracle`
disabled. Context guards reject direct self-import, inherited target theories,
and previously available target/later facts. Removing replay does not remove
these checks or the checked reconstruction of each Sledgehammer result.

## Lab setup

Use the main Python 3.10 environment on Linux. Install the released Isabelle2026
at `itpeval/_toolchains/Isabelle2026/` under the repository. This backend does not
require PISA, sbt or a separate Java server. Its source checks remain pinned to
Isabelle2026, and its settings, heaps and temporary files stay under
`itpeval/.runs/isabelle2026-native/`.

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m pip install -r requirements.txt
```

`eval/configs/hol_light_to_isabelle/v2_dsp.example.json` and
`v2_dsp_2026.example.json` select native Isabelle2026. The existing
`v2_dsp_2026.local.json` is also supported. Old configurations automatically gain
the verified missing import qualifications. A legacy `replay_timeout_s` field is
ignored for compatibility; it does not enable replay.

Keep `base_session` as `HOL`. Do not use `HOL-Analysis` or a complete AFP target
session as the parent to work around missing imports: that may import the proof
being evaluated. The configuration qualifies only original theory basenames:

| Original import | Owning session and theory |
| --- | --- |
| Lebesgue_Measure | HOL-Analysis.Lebesgue_Measure |
| Tagged_Division | HOL-Analysis.Tagged_Division |
| Euclidean_Algorithm | HOL-Computational_Algebra.Euclidean_Algorithm |
| Primes | HOL-Computational_Algebra.Primes |
| Lattices | HOL.Lattices |
| Boolean_Algebras | HOL.Boolean_Algebras |
| Angles | Triangle.Angles |
| Square_Matrix | Cayley_Hamilton.Square_Matrix |

Hundred Theorems also requires the AFP sessions `Triangle`, `Cayley_Hamilton`,
and `Pratt_Certificate` (31 extracted contexts in total). Install the **full AFP
source archive for Isabelle2026** using the supplied Python 3.10 script:

```bash
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.prepare_afp \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
```

The installer downloads the [official dated release](https://isa-afp.org/release/afp-2026-10-26.tar.gz),
pinned to SHA-256 `7f48e3fc3dc823a30149a90fa4a614ed53be175273971f4923debb9457fa60e4`.
It verifies the archive checksum and `AFP_VERSION=2026`, extracts all sources to
`external/afp-2026/`, then adds `external/afp-2026/thys` to `session_roots` in the
requested config. Other settings and roots are preserved. The tracked local
config already contains that portable path; run the installer on the lab before
preflight. It does not install Isabelle or build AFP sessions.

The cache is `itpeval/.downloads/afp-2026-10-26.tar.gz`; `--archive` can supply an
already downloaded copy with the same checksum. Reruns reuse a validated install
without duplicating roots. Existing unmanaged directories are never replaced;
choose another `--destination` if necessary. Sources, archive and installation
manifest remain repository-local and Git-ignored. No global Isabelle settings
are changed. The dated release avoids silently switching to a future AFP version.

The **24 core Set contexts** receive status `unavailable_context` (displayed as
**unavailable context**) because HOL already inherits their original theory.
Preflight lists them separately and does not launch a native job for them.
They remain in the 262-candidate denominator and are never counted as passes.
The 31 AFP-dependent contexts receive normal native checks after installation;
missing AFP is still a dependency error, not a core Set unavailability marker.

## One consolidated preflight: all 262 contexts

After activating the main environment and preparing Isabelle/AFP:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
PIPE=eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json

python -m "${PIPE}.lab_preflight" \
  --expected-root "$PWD" \
  --config "$CFG" \
  --dataset both \
  --all-targets \
  --expected-contexts 262
```

Use the actual repository-local AFP root. Omit `--afp-root` if it is already in
`session_roots`. Without AFP, you can still run the command without that option;
its 31 dependent contexts will report missing dependencies. A supplied nonexistent
root is a setup error and blocks native execution.

The full run has **292 checks**: selection, metadata, infrastructure, the repaired
ML fixture, 23 proof/search controls, three fixed real-theorem proofs, and all
**163 Babel + 99 Hundred contexts**. No LLM calls are made. These checks establish
context and backend readiness, not successful proofs of every dataset theorem.

`--expected-contexts 262` detects accidentally restricted or changed input scope.
Add `--plan-only` to inspect the full selection without Isabelle or output writes.
Omitting `--all-targets` selects 32 representative contexts across 29 topics.

Each invocation writes a new directory under
`eval/preflight_results/isabelle2026/<UTC-timestamp>-<run-id>/`, including:

- `report.json` and `summary.md` with all check outcomes;
- `checks.jsonl` with one bounded payload per check;
- `metadata.json`, `logs.jsonl` and `unavailable_contexts.json`.

There are at most six tracked files, each capped at 32 MiB. Full inputs, results,
and runtime logs stay in ignored `itpeval/.runs/preflight/`; no ZIP is generated.
See [report storage and rejected-push recovery](../../../../preflight_results/README.md)
for bounds and the command to compact existing runs safely.
Independent failures do not stop the
remaining checks; an infrastructure failure blocks dependent checks explicitly.
Exit status is 0 when backend controls and available dataset checks pass, 1 for
failures or an entirely unavailable selection, or 130 for interruption.
`contexts_ok` covers available dataset checks. `full_context_coverage` stays false
when any context is unavailable/blocked or unreported; a green readiness result
never means all 262 contexts passed. `context_counts` reports selected, reported,
passed, failed, blocked and unavailable counts separately. The full run retains
292 report entries, with 24 marked unavailable and 238 normal context checks.

```bash
git add eval/preflight_results/isabelle2026/<run-id>
# Commit and push using your normal workflow.
```

## Context repairs after the November 2 preflight

The report committed in `fabeacf1` had 41 context failures in three topics; all
backend controls passed. See [the diagnosis and fixes](PROVER_REVIEW.md).
The native checker now stages the pinned AFP `bertrand.ML` companion in each job,
uses that job's master directory, and allows legitimate earlier scoped helpers
whose basenames recur later. The selected target and inherited-theory guards remain.

`context_step_timeout_s` defaults to 120 seconds for trusted context initialization,
including the Bertrand ML calculation. Generated proof steps retain the separate
10-second `step_timeout_s`. Both are bounded by `target_timeout_s`.

Hundred extraction now uses `hundred_theorems_repair_p2`, preserving `setup_lifting`
after masked typedef proofs. Run the full preflight command above **without
`--input`** to use freshly extracted contexts. For experiments reading old Polynomial
JSONL, re-extract those records and regenerate their dependent Draft/Sketch files;
old contexts receive an explicit re-extraction error. Other unchanged contexts
can retain their saved artifacts. No old preflight outcome has been relabeled.

## Running experiments

Use each dataset's `v2_dsp.run` / `run_babel` / `run_hundred` entry point and the
2026 config. `--sketch-source draft --drafts <drafts.jsonl>` consumes saved Drafts;
`--sketch-source hol-light-proof --records <records.jsonl>` uses the direct mode.
Normal runs check native capabilities and each context before making model calls.
`--dry-run` previews the chosen prompt without inference or native execution.

Native output paths remain `v2-dsp-isabelle2026/{draft,direct}/<profile>/` under
the dataset's result root. PISA uses `v2-dsp-pisa-isabelle2021/` and a distinct
artifact schema. Saved 2026 Sketches can be rechecked without regenerating Drafts.
Checker `dsp_isabelle2026_native_p7` invalidates old verification caches; historical
reports and model outputs are not rewritten.

See [review and fixes](PROVER_REVIEW.md). Offline tests use explicit fake
transports; the updated ML fixture and real dataset dependencies still require
execution on the Linux lab installation.
