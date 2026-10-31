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
