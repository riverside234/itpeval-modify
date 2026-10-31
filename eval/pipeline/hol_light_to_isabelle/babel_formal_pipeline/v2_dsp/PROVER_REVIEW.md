# Native DSP prover review

Date: 2026-10-31
Scope: shared Isabelle2026 prover used by both datasets and both Sketch input modes.

## Source comparison

Reviewed the requested upstream Sledgehammer directory at commit
[`bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370`](https://github.com/isabelle-prover/mirror-isabelle/tree/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Tools/Sledgehammer).
Also checked the locally cached official Isabelle2026 release sources against
all nine hashes in `native/release_sources.json`. Runtime compatibility remains
pinned to Isabelle2026; upstream master is a comparison source, not a replacement
for the installed release. The release and reviewed master versions of
`sledgehammer_proof_methods.ML` have the same Git blob hash.

Relevant official code:

- [`sledgehammer_proof_methods.ML`, lines 230-264](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Tools/Sledgehammer/sledgehammer_proof_methods.ML#L230): one-line reconstruction emits `apply` when multiple subgoals remain.
- [`sledgehammer.ML`, lines 223-278](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Tools/Sledgehammer/sledgehammer.ML#L223): `SH_Some` carries preplay results, which may be empty or unsuccessful; it alone does not establish an executable proof.
- [`sledgehammer_prover_tactic.ML`, lines 185-199](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML#L185): native tactics provide an executed command with an empty preferred preplay-method list. The existing native-tactic fallback remains necessary.
- [`token.ML`, lines 320-328 and 387-395](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/token.ML#L387) and [`symbol_pos.ML`, lines 239-270](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/General/symbol_pos.ML#L239): compact token sources contain deleted-character padding; executable syntax is produced by `Token.unparse`.
- [`Pure.thy`, proof command declarations](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Pure.thy#L54): braces, `.`, `..`, `consider`, `define`, and `subgoal` are standard proof commands.
- [Linux procfs documentation, section 3.7](https://docs.kernel.org/filesystems/proc.html#proc-pid-task-tid-children-information-about-task-children): child lists belong to individual threads and list only immediate children.

## Fixes

| Finding | Effect before the fix | Change |
| --- | --- | --- |
| High: internal token text used as executable source | Quoted terms, cartouches and comments could lose delimiters in reconstructed proofs. The old `show True` preflight did not exercise this. | Serialize spans with `Token.unparse`; use a quoted goal in preflight and add native round-trip/replay regressions. |
| High: each native reconstruction had to close an entire obligation | Valid `apply` results solving one of several subgoals were rejected. | Require strict subgoal reduction, continue reconstruction, and finish only after the original obligation closes. A failed remaining goal still fails the sample. |
| Medium: incomplete Isar command allowlist | Valid local blocks, short proofs, local definitions, case considerations and `subgoal` blocks were rejected. | Admit the specific standard proof commands; retain rejection of admissions and arbitrary ML/setup. |
| Medium: expired ML deadline swallowed as an ordinary candidate failure | Whole-target expiry could be mislabeled and additional candidates attempted. | Propagate the native deadline failure immediately. |
| Medium: missing worker startup deadline | Startup/import loading could consume the full target budget despite a smaller startup setting. | A unique readiness marker ends the worker startup phase; Python enforces startup and whole-target deadlines separately. |
| Medium: process deadline measured too early | Delaying `run()` after constructing its process wrapper extended the absolute deadline. | Compute the remaining budget at process launch against the original deadline. |
| Medium: incomplete descendant tracking | Children created by non-main threads, or children changing process groups, could be missed during cleanup. | Traverse every thread's child list recursively and identify live processes by start time before signaling their current group or PID. |
| Robustness: inherited Sledgehammer search modes | Imported theory settings could switch a proof search to falsification or abduction. | Explicitly request `falsify = false` and `abduce = 0`. |

The existing checked-reconstruction and fresh-replay requirements remain the
acceptance gate. This review introduced checker version `dsp_isabelle2026_native_p2` and
native adapter fingerprints change, so old verification results are not reused.
The previous prompt revisions are preserved.

## Validation and lab acceptance

Local result: **126 offline tests passed; 10 native integration tests skipped**
(136 collected). Python 3.10 syntax checks also passed.

Offline regressions cover worker startup, absolute deadlines, children created
by another thread, changed process groups, PID reuse, request-specific readiness
markers, and propagation of startup budgets. Existing protocol, replay,
input-isolation and resume tests also run without native Isabelle or LLM calls.

The opt-in Isabelle2026 tests add executable cases for quoted terms/cartouches,
multiple pending subgoals, a solvable first subgoal followed by an unsatisfiable
one, local Isar blocks/short proofs, local definitions, `consider`, `subgoal`,
zero-goal completion, and inherited search-mode overrides. These tests and the
changed ML must still be compiled and executed on the lab installation; local
Python checks do not establish native correctness. Procfs sampling can also miss
very short-lived processes; the changes improve owned-descendant tracking rather
than providing a kernel-level process containment boundary.

Run after updating the lab checkout and activating the main environment:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify

python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.preflight \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --input eval/results/hol_light_to_isabelle_v2/single_records.jsonl \
  --topic circle_average --target-key circleAverage_center_independent

export ITPEVAL_NATIVE_ISABELLE2026_CONFIG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
python -m unittest discover \
  -s tests/hol_light_to_isabelle/v2_dsp -p 'test_native_integration.py'
```

The native dataset-context test also checks a Hundred Theorems import; configure
its required session dependencies as described in the README. No model calls
are made by preflight or native integration tests.

## Pulled single-theorem run (c8fb3cb)

The newly pulled lab run passed preflight, including native Sledgehammer
reconstruction and fresh replay. Its real Draft-to-Sketch run failed before any
heuristic or Sledgehammer call. No timeout or prover configuration failure is
shown for that sample.

Evidence:

- `eval/results/hol_light_to_isabelle_v2/preflight/0108afca2e6bf8b4453a.json`:
  `ok = true`, `baseline_ok = true`, and `controls.hammer.verified = true`.
- `eval/results/hol_light_to_isabelle_v2/work/target-lvk5pwyk/search/result.xml`:
  the context and target declaration succeeded; attempt 57 is the first Sketch
  command, `by`, and fails with `keyword "(" expected, but end-of-input`.
  `settings` is empty because no search gap was reached.
- The saved Draft-mode Sketch starts with `by`, then contains `have`/`show`
  commands and a closing `qed`. This structure requires `proof -`, not `by`.
- The direct-mode Sketch is `by` followed by `unfold circleAverage circleMap`
  and `rule integral_shift` on indented lines. The pulled files contain no
  native Prove result for this direct sample, but its body is already invalid:
  Isabelle does not use indentation to sequence tactics, method arguments need
  parentheses, and definitions are rewritten using their theorem facts.

The visible-content normalizers only strip thinking/fences and whitespace;
they do not replace `proof` with `by`. The old artifacts retained the normalized
Sketch and API statistics, but not an independent copy of the visible response.
The specific pipeline bug was accepting these shapes as valid generated Sketches.
Passing preflight demonstrates environment/capability readiness, not that an
arbitrary subsequent model response has valid syntax or proves its target.

This diagnosis agrees with official
[`Pure.thy`'s terminal `by` parser](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Pure.thy#L985)
and the
[`Method.parse` grammar](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/method.ML#L691).
`by` accepts one required and one optional method expression; a bare name is one
expression, while arguments and combinators require parentheses. `unfold`
**is** a valid Isabelle method when used correctly; the fix does not ban it.

Changes following this run:

1. Revised both datasets' shared Sketch instructions, with a valid generic Isar
   example, explicit `proof - ... qed` structure, and correct method/definition
   syntax. Draft-to-Sketch is now `*_draft_p4`, direct-to-Sketch `*_direct_p3`.
   The mathematical Draft prompt is unchanged.
2. Added narrow lexical validation for the observed malformed bodies. They are
   rejected before native startup, with actionable errors, rather than silently
   changed into different proofs. This is not a complete Isabelle parser.
3. Preserve `sketch_response_content` (visible final output only) and API usage
   when validation fails. Previously the exception handler replaced completed
   API response metadata with an empty object, undercounting failed samples.
4. Include the final native command's detailed error/line in `verify_error`.
   Do not attach an earlier failed heuristic if later commands succeeded.
5. Bump the checker to `dsp_isabelle2026_native_p3` and include the lexical
   validator version in generation fingerprints. A normal generation run will
   not reuse the old prompt/validator output. `--skip-sketch` still deliberately
   reads the saved Sketch and cannot repair it.

Follow-up validation: **134 offline tests passed; 11 native integration tests
skipped** (145 collected). Python 3.10 syntax checks passed for all 125 pipeline
and test modules. The two exact saved failures are regression fixtures; valid
parenthesized methods, two-method proofs, structured proofs, comments and
cartouches remain accepted by the lexical validator. Native execution of the
corrected diagnostic proofs is still pending on the lab machine.

A minimal manual diagnostic for the saved Draft-mode proof changes only the
first `by` to `proof -`. The direct proof's mathematical steps can be expressed as:

```isabelle
proof -
  show ?thesis
    unfolding circleAverage_def circleMap_def
    by (rule integral_shift)
qed
```

These manual diagnostics are test fixtures, not model outputs or experimental
successes. They have not been executed locally because Isabelle2026 is installed
on the lab computer. Run the focused native test without making any LLM calls:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
export ITPEVAL_NATIVE_ISABELLE2026_CONFIG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
python -m unittest discover \
  -s tests/hol_light_to_isabelle/v2_dsp \
  -p 'test_native_integration.py' -k corrected_real_run_sketches
```

For an experimental rerun, retain the saved mathematical Draft and generate a
new Sketch with the revised prompt. Use a new output directory so the failed
sample remains available for comparison. Do not add `--skip-sketch` or
`--skip-prove` to this command:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
DSP_RUN_DIR=eval/results/hol_light_to_isabelle_v2/v2-dsp-isabelle2026/single/draft-syntax-p4
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.run_babel \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --sketch-source draft \
  --drafts eval/results/hol_light_to_isabelle_v2/v2-dsp-isabelle2026/single/draft/drafts.jsonl \
  --topic circle_average --target-key circleAverage_center_independent \
  --samples 1 \
  --dsp-output "$DSP_RUN_DIR/inputs.jsonl" \
  --sketch-output "$DSP_RUN_DIR/sketches.jsonl" \
  --prove-output "$DSP_RUN_DIR/prove.jsonl" \
  --output "$DSP_RUN_DIR/verified.jsonl"
```

For direct mode, use another new directory such as `single/direct-syntax-p3`,
replace `--sketch-source draft` with `--sketch-source hol-light-proof`, and replace
`--drafts ...` with
`--records eval/results/hol_light_to_isabelle_v2/single_records.jsonl`.
The rerun makes one new Sketch-model call per selected sample. Prompt changes
reduce the observed syntax confusion but do not guarantee model correctness.

## Successful single-theorem runs (547adaf)

Reviewed commit `547adaf6733252a5f9dbc699525a3230e0377b43` and the current
Python code. Both latest samples prove `circleAverage_center_independent`:

| Mode | Saved Sketch | Search | Fresh replay | Gap-filling / hammer calls |
| --- | --- | --- | --- | --- |
| Saved Draft | `proof -`, definition equality, `integral_shift`, transitivity, `qed` | Target closed | Passed | 0 / 0 |
| Direct HOL Light | `by (simp only: circleAverage_def circleMap_def integral_shift)` | Target closed | Passed | 0 / 0 |

Evidence lives under `eval/results/hol_light_to_isabelle_v2/`:

- `v2-dsp-isabelle2026/single/draft/{drafts,sketches,prove,verified}.jsonl`
- `v2-dsp-isabelle2026/single/direct/{sketches,prove,verified}.jsonl`
- `work/target-2aspjy9b/{search/result.xml,replay/circle_average.thy,replay/build.log}`
- `work/target-i5uxxth6/{search/result.xml,replay/circle_average.thy,replay/build.log}`

The XML request identifiers/input hashes match their saved requests, returned
proofs match the result rows, and both replay logs report successful builds.
The replay theories disable `quick_and_dirty` before the target, contain its
actual proof and exclude later declarations. The 11 earlier masked helpers
remain admitted background under the existing experiment policy. The generated
proofs explicitly use definitions and the locale's `integral_shift` assumption.
No new native prover failure or incorrect success flag was found in these runs.

The new p3 Draft correctly explains definition expansion, the instantiated
locale assumption and transitivity. The old malformed gpt-5.6 sketches remain
in the append-only histories; each latest gpt-6.1 sample is the one evaluated.
Both latest Sketch metadata records say **medium** reasoning. This is the
recorded setting, even though the code defaults to high when no override is
supplied. These are one-theorem smoke tests; they do not establish dataset-wide
success or exercise real-target Sledgehammer reconstruction.

### Bugs found while reviewing repeated-run handling

These did not invalidate the two successful K=1 results, but would affect
subsequent experiments reusing paths. Offline regressions reproduced them before
applying the fixes:

1. `load_inputs(samples=True)` previously selected the last row independently
   for each sample index. After changing model/prompt/input and generating only
   index 0, it could also select index 1 from an older configuration. Selection
   now keeps only samples compatible with the target's latest generation
   settings. Requested but absent samples remain explicit failures.
2. `save_results` preserved indices outside the current selection even for the
   same target. Reducing K could leave an old successful index in `verified.jsonl`
   while its summary described only the current failed sample. Saving now
   replaces all indices for selected targets and retains only unselected targets.
3. Sketch resume used Draft text without its generation provenance. A new Draft
   model producing identical text could reuse a Sketch carrying the old Draft
   metadata. Generation identity and expected-input alignment now include Draft
   provenance. Current input validation and fresh replay remain required.

Summaries now expose actual model profiles, native search/gap-filling counts,
and the distinction between the evaluated selection and all stored rows.
Token totals describe selected artifacts, not every call in the historical logs.
The native engine and proof-admission policy were not changed by this review.

### Prompt revision and validation

Keep the p3 Draft prompt: the observed mathematical reasoning is correct.
Draft-to-Sketch p5 and direct-to-Sketch p4 explicitly allow a complete proof with
zero search placeholders. The Draft handoff also permits combining neighboring
rewrites/helper applications without mechanically generating one `have` per
Draft step. Necessary dependencies and source strategy remain required; there
is no length restriction. Both datasets use these shared instructions.

Reuse the successful p3 Draft, run Sketch normally with fresh output paths to
compare this revision, and omit `--skip-sketch` if testing the new prompt.
No historical experiment artifacts were edited. No live API calls or native
Isabelle execution were made on Windows for this review.

Validation after this revision: **141 offline tests passed; 11 native integration
tests skipped** (152 total). Seven new result-history regressions cover both
input modes, model/prompt/provenance changes, failed/missing samples, K reduction
and summary accounting. Python 3.10 syntax checks passed for all 100 v2 pipeline
modules. Re-reading the pulled artifacts with the new loader still selects one
verified sample in each mode and reports zero real-target Sledgehammer calls.
