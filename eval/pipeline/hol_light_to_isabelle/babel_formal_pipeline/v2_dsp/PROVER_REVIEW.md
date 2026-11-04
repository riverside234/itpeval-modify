# Review of commit 4d53634: compactness search and bounded references

The `compact_canon_qfree` p14 result advanced past the two previously failing set
steps. It stopped at `compact_prop_instance` (sketch line 78), with three optional
candidate timeouts and a real Sledgehammer timeout (42.431 seconds). The result
contains one successful earlier Hammer reconstruction and one successful terminal
repair; no terminal timeouts. There is no evidence here of a broken ATP install.

The masked imported signature in
`hol_dataset/aligned-isabelle-hl-main/afp/stmts/isabelle/Ground_FOL_Compactness.thy`
shows that `compact_prop` requires a whole-set quantifier-free premise as well
as finite-subset satisfiability. This signature and `qfree_formsubst` were absent
from the old prompt. The sketch's local `qf_inst` is inside the finite-subset
proof and is insufficient as a scoped whole-set fact at the later application.
The oracle supports proving that condition; this is not a claim that the sketch's
mathematical implication is false. The target's completed Isabelle proof was not
read or added to the prompt.

Implemented fixes:

- Most-match retrieval v2 walks only explicit transitive imports with matching
  headers in the masked AFP statement snapshot. It excludes the target theory,
  unrelated files, scoped and unnamed helper declarations, and records origins,
  hashes and unresolved imports. Named source dependencies are prioritized.
  The total Isabelle reference cap stays at 8,000 characters; checker input and
  imports are unchanged. Older v1 artifacts remain usable for saved-sketch tests.
- Direct prompts advance to most-match v6 and Babel/Hundred p9. They require
  all target-helper premises and concrete applications at the correct scope.
  Draft instructions are unchanged; fresh records gain the improved reference.
- Native p15 limits the optional heuristic portfolio to two step budgets per
  gap, including its subsequent normalization/reconstruction rounds. It then
  yields to bounded Hammer. Existing per-candidate and whole-target deadlines,
  rollback, admission checks and target closure remain mandatory.
- Goal diagnostics and goal-based hints use the pending first subgoal, following
  Isabelle's [`Logic.get_goal` use in Sledgehammer](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Tools/Sledgehammer/sledgehammer.ML).
  Failure reports prefer that actual search state over a failed heuristic's
  discarded simplified goal, while retaining the latter separately.

Regression coverage includes transitive-only masked import retrieval, target and
sibling exclusion, locale/unnamed theorem exclusion, provenance for overlapping
spans, leading document headings, all-dataset context caps, the committed p14
failure, and exact search-state diagnostics. Native controls additionally cover
portfolio timeouts followed by real Hammer and the first-subgoal diagnostic.

Validation: **194 offline tests passed; 33 native tests skipped pending the lab**.
All 353 most-match candidates extract successfully within the context caps.
Python 3.10 syntax and patch whitespace checks passed. Native Isabelle2026 is
not installed on this workstation. No API calls or lab proof runs were made.
Use the [focused retry](../../most_match_pipeline/README.md#review-of-commit-4d53634-compactness-premise-and-imported-references)
with re-extraction; old records do not gain new imported signatures automatically.

---

# Review of commit ea7bb55: COMPACT_CANON_QFREE

The committed most-match `Canonical_Models/compact_canon_qfree` direct sample
failed at sketch line 56, `using ps_mono cover psT by blast`, with a local
10.464-second method timeout. Imports/context execution succeeded, two native
Sledgehammer searches reconstructed proofs, and p13 repaired the earlier
failed `by blast` at line 39. The target did not close. Its later compactness
argument was not reached.

The earlier failure compares two extensionally equal comprehensions under
`satisfies`, with different guard orders. Its native reconstruction used
`Collect_cong`. The later timeout combines a general monotonicity rule with
large, differently written set arguments. Explicit instantiation and a separate
set-representation bridge are preferable to unbounded logical search here.
This diagnosis uses the saved source proof, oracle, masked reference, sketch
and execution trace; no completed target Isabelle proof is supplied.

Implemented in shared native checker **p14**:

- A typed local terminal-method timeout restores the saved state and goes
  directly to bounded native Hammer/reconstruction. It must close the same
  obligation; no failed partial proof state or unproved fact is committed.
- The timeout classification preserves the whole-target deadline and external
  interrupts. Nonterminal source commands keep their fatal timeout policy.
  Ordinary parse/name/type failures remain errors. Timeout text alone is never
  used to authorize a repair.
- Attempt records distinguish `timeout_scope=terminal_method` and repair
  `repair_reason=method_timeout`; per-sample/batch summaries count terminal
  method timeouts separately. Failed repair diagnostics retain the native
  failure, source command and source line.
- Optional `sos`/norm candidates are skipped if their required methods or facts
  are absent from the current context. Source commands are not filtered.
- Only direct prompts advance: shared Babel/Hundred p8 and most-match v5.
  They require matching helper premises, consistent comprehensions, explicit
  equality/inclusion bridges and witnesses for `obtains`. Draft prompts, model
  settings, bounded context policy and default direct mode stay unchanged.

The timeout path follows the pinned Isabelle2026
[`Timeout.apply`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Concurrent/timeout.ML),
which cancels its timer and distinguishes its own timeout from other interrupts.
Optional method lookup uses the official
[`Method.check_name`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/method.ML).
No new imports, target-specific facts, admissions or replay stage are added.

Regression coverage includes the committed failure, current direct prompt with
unchanged bounded input/oracle, and timeout/repair summary diagnostics. Opt-in
native tests cover timeout after partial method progress, forced Hammer,
following-command preservation, structural timeout rejection, set equality under
an opaque predicate and explicit higher-order rule instantiation. ML fixtures
also check whole-budget exhaustion and interrupt propagation.

Validation: **192 offline tests passed; 32 native tests skipped pending the lab**.
The shared native suite, most-match extraction/parallel/cache tests, CLI adapters
and Hundred fake-transport check passed. Native Isabelle is not installed on
this workstation; real proof success is pending lab verification. The [one-theorem retry](../../most_match_pipeline/README.md#review-of-commit-ea7bb55-compact_canon_qfree)
regenerates just the failed target. A separate saved-sketch command can test the
backend change without calling a model. Existing committed logs are unchanged.

---

# Review of commit 852f31b: most-match induction method failure

The saved `Canonical_Models/finite_subset_instance` direct sample reached its
Isar induction base case and failed at `by (intro impI, rule exI[where x="{}"], simp)`.
Its reported goal was existential; no heuristic or Sledgehammer attempt ran.
The setup and imports had succeeded. The later insertion block also appears to
reintroduce a case premise after a default `proof` rule, so a new generated
Sketch is needed to test the prompt improvement.

Checker **p13** adds narrowly classified terminal-method recovery. It discards
failed `by` progress, runs bounded search from the saved state, and requires
local closure before continuing. The original command, inner search result and
repair outcome are recorded separately. Missing names, parser/type failures,
invalid structure, source timeouts, interrupts and forbidden commands are not
eligible. It does not rewrite declarations or insert premises. No replay is added.

The classification follows Isabelle2026
[`Proof_Display.method_error`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/proof_display.ML)
and [`Proof.finished_goal` / terminal proof execution](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/proof.ML).
The failing `intro` requires changed proof state, as defined in
[`method.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/method.ML).

Direct prompts now cover meta/object implication, induction premises, explicit
witnesses, and deliberate proof-block opening. Only direct prompt versions
advance (Babel/Hundred p7; most-match v4). Draft prompts remain unchanged.
Native CLI commands default to direct mode, with `--drafts` retaining the saved
Draft path. Artifact tags and legacy Python API defaults are preserved.

Regression coverage includes the committed failure, all three dataset CLI
adapters, retained Draft commands, mode conflicts, and repair diagnostics.
Native lab tests additionally check existential recovery, rollback before forced
Sledgehammer, preserved local facts/following commands, false/missing-fact
rejection, and an independent finite-set induction example. Local tests cannot
establish native compilation or complete theorem success.

Validation: **189 offline tests passed; 29 native tests skipped pending the lab**.
The shared native suite, most-match extraction/parallel/cache tests, CLI adapters
and Hundred fake-transport check passed. Python 3.10 syntax and patch checks
passed. No model calls or native Isabelle builds were run locally.

Use the [one-theorem retry](../../most_match_pipeline/README.md#review-of-commit-852f31b-finite_subset_instance)
to regenerate this sample; broad previously passed contexts are not requested.
Historical logs and generated sketches have not been edited.

---

# Review of run 20261104T002751Z-cfc4b7f0: test syntax and sum search

Reviewed 2026-11-03 (America/Chicago). Source commit `7e7203655662a45e4d5d31d0951e7508f02c34e1`.
The committed compact report is under
`eval/preflight_results/isabelle2026-rsum-bound/20261104T002751Z-cfc4b7f0/`.
The lab-only directory under `itpeval/.runs/preflight/` holds its full artifacts.

All five setup checks passed. Four proof checks failed:

| Check | Evidence and diagnosis |
| --- | --- |
| `candidate_timeout_then_hammer` | Rejected before native execution: its test sketch was a bare `sledgehammer`, while the public input contract requires a complete `by` or `proof ... qed` body. This was a regression-fixture bug, not a prover timeout. |
| Both stored `rsum_bound` sketches | The scaling step passed. At the triangle step the new candidate timeout was recovered and Sledgehammer actually ran. The norm-sum heuristic failed because `rule norm_sum` tried to resolve the chained `finite p` fact into a rule with no premises. The log also reported the unsupported `nlinarith` method. |
| `rsum_bound_triangle_forced_hammer` | One actual Hammer attempt, zero heuristics, `native_outcome=timeout`, no proof/preplay candidate. This demonstrates a search failure on the raw pair-indexed goal, not another early-abort bug. |

The saved and direct searches reached Hammer after their timed-out `metis`
candidate (12.409 s / 11.115 s); their final Hammer calls took 45.012 s / 47.021 s.
The isolated Hammer call took 44.044 s. Timeouts remain failures.

Checker **p12** changes the shared native pipeline for every dataset:

- The general timeout fixture now supplies a complete Isar proof body. Offline
  tests validate positive retry inputs and require this fixture to reach the
  native transport, catching the earlier mock-test blind spot. The real lab
  check still requires a local candidate timeout, rollback, actual Hammer,
  reconstruction and target closure.
- The norm-sum heuristic uses `simp only: case_prod_beta' norm_sum`, preserving
  scalar norms while matching the structural bound and avoiding `rule`'s
  resolution of irrelevant chained facts. Unsupported nonlinear tactic names
  are removed; existing Isabelle order-rule and `metis` candidates remain.
- Before Hammer, pair binders can be normalized by the bounded, kernel-checked
  command `apply (simp only: case_prod_beta')`. A changed goal is retained only
  at the same proof level with no additional subgoals. The executed command is
  included in the resulting proof. Ordinary heuristic/reconstruction closure
  rules remain strict, and target completion is still required.
- Hammer receives at most seven relevant, already available library hints for
  sums, norms, scalar norms and pair binders. Selection inspects goal constants,
  not theorem/topic names; absent facts are omitted. Native fact selection stays
  enabled (`only=false`). No target proof, new import or mathematical assumption
  is supplied. The chosen hints are recorded in `prover_settings.added_fact_hints`.
- `search_summary` includes normalization attempts/successes. Hammer records the
  actual `goal_before_search`, with Isabelle markup removed. Failed Hammer or
  reconstruction reports retain this goal even when no heuristic produced an
  error message; later unrelated source-command failures cannot inherit it.
- Both Draft-to-Sketch and direct Sketch prompts now require available Isabelle
  methods, explicit pair/summand matching, the norm-of-sum bound before scalar
  expansion, relevant `using` facts, and a complete one-gap Isar body. Versions
  advance for Babel, Hundred Theorems and most-match. The informal Draft prompt
  and the two saved regression sketches remain unchanged.

The rule/chained-fact behavior was checked in official
[`method.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/method.ML).
Normalization uses the documented proof-state transition in
[`proof.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/proof.ML).
The fact override uses
[`sledgehammer_fact.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Tools/Sledgehammer/sledgehammer_fact.ML)
and existing facts from
[`Real_Vector_Spaces.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Real_Vector_Spaces.thy).

Validation: **118 offline tests passed; 24 native tests require the lab**.
These include all three dataset adapters, prompt contracts, historical-failure
checks, positive test-body validation, transport reachability and goal diagnostics.
Native tests now include irrelevant chained facts for the sum rule and a forced
Hammer test for general pair-indexed sums. Python 3.10 syntax, plan-only selection
and patch checks pass. Native compilation and complete theorem success are not
established by offline tests.

## Retry only these four failed checks

After syncing the changes to the lab:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.retry_rsum_bound \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
```

The selection remains: general timeout-to-Hammer regression, both unchanged saved
sketches, and the isolated triangle obligation with heuristics disabled. Required
setup still runs; previously passed broad controls/standalone contexts do not.
No model calls or separate replay. The new native adapter requires an initial
heap rebuild. Push the same six compact report files under
`eval/preflight_results/isabelle2026-rsum-bound/<timestamp>/`.

`--plan-only` previews the selection. This retry tests the prover on saved input;
prompt changes affect newly generated sketches and do not rewrite those inputs.
All four proof checks must pass; a successful isolated probe cannot substitute
for a failed full sketch.

---

# Review of run 20261103T232010Z-e2f73e8b: optional method timeout

Date: 2026-11-03. Report:
`eval/preflight_results/isabelle2026-rsum-bound/20261103T232010Z-e2f73e8b/`.
Historical reports and both saved sketches remain unchanged.

Both searches passed the former scaled-norm bound and reached the next gap,
`triangle` (`using fin`, saved-sketch line 30 / direct-sketch line 26). The
optional scalar-norm `metis` candidate then timed out after **11.855 s / 10.711 s**.
The ML runner treated this candidate timeout as fatal and aborted before the
remaining candidates or Sledgehammer could run on that gap. This is a runner
bug; the report does not demonstrate a Sledgehammer failure on the triangle
inequality. The saved run's `native_outcome=some` described an earlier gap.

The original-import heap succeeded. Startup was **17.925 s / 15.938 s**, compared
with **272.823 s / 306.492 s** in the earlier two jobs. The new heap's one-time
build took 194.037 s. These measurements support reusing the cache, but do not
constitute a general end-to-end speedup benchmark.

Changes in checker **p11**, shared by Babel Formal, Hundred Theorems and most-match:

- Every optional heuristic or reconstruction candidate runs from a saved state.
  A local `Timeout.TIMEOUT` rejects that candidate and tries the next one from
  the same state; partial progress and its proof text are discarded. Exhausted
  target budgets, required context/sketch command timeouts, and external
  interrupts still abort. The timeout policy has no target-name, topic, or
  mathematical-goal special case.
- Optional heuristics stop when the remaining target budget needs to be reserved
  for Sledgehammer search, preplay and one reconstruction. If heuristics do not
  close a gap, Sledgehammer gets that remaining opportunity. Successful easy
  proofs do not need an additional search. Existing budgets are not increased.
- General pair-indexed sum rules handle norm bounds, sum monotonicity and constant
  factoring before expensive search; the scalar-norm `metis` fallback moves last.
  These use standard library facts, with no completed target proof or
  `rsum_bound`-specific fact in the shared prover.
- Hammer settings reset at each pending state, so a previous gap's success is not
  shown as the current failure's result. Compact reports retain `search_summary`
  (heuristic/hammer/reconstruction attempts and successes, candidate timeouts)
  and final-state diagnostics before truncating long traces.
- The existing prompts already request explicit sum/sign reasoning and are
  unchanged in this fix. Stored-sketch retries do not invoke the model.

The timeout/transaction behavior and library facts were checked against the
pinned official Isabelle2026 sources:
[`timeout.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Concurrent/timeout.ML),
[`toplevel.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/toplevel.ML),
[`Real_Vector_Spaces.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Real_Vector_Spaces.thy),
[`Product_Type.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Product_Type.thy), and
[`Groups_Big.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Groups_Big.thy).

## Focused lab retry, including general Sledgehammer coverage

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.retry_rsum_bound \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
```

Append `--plan-only` to preview. Four proof checks are selected:

1. `candidate_timeout_then_hammer`: a general conjunction goal, unrelated to
   norms or integrals. A trusted test method deliberately delays after a partial
   `apply` step. Acceptance requires a recorded candidate timeout, native
   Sledgehammer on the original saved state, executable reconstruction and
   target closure. It selects Sledgehammer's native `simp` prover for a
   deterministic fallback check; this is not a direct `by simp` shortcut.
2. `rsum_bound_saved_search`: the first unchanged recorded sketch.
3. `rsum_bound_direct_search`: the second unchanged recorded sketch.
4. `rsum_bound_triangle_forced_hammer`: the failed triangle obligation isolated
   in the same earlier masked context, using configured provers and **no
   heuristic candidates**. Acceptance requires actual successful Hammer and
   reconstruction attempts. This is an explicitly labelled regression probe,
   not an additional dataset theorem or a proof of `rsum_bound`.

The command runs required setup but skips previously passed standalone contexts,
previous broad capability controls and the full native fixture. No LLM calls or
separate replay builds are made. The new adapter invalidates old heaps, so one
initial rebuild is expected. All four proof checks must pass for overall OK;
the command exits nonzero on failure. Successful isolated probes never replace
an unsuccessful complete sketch.

At most six compact files remain pushable under
`eval/preflight_results/isabelle2026-rsum-bound/<timestamp>/`. Full artifacts
stay ignored under `itpeval/.runs/`. Check `search_summary.hammer_attempts`,
`hammer_successes` and `candidate_timeouts` on each report row to inspect coverage.

Validation: **110 offline tests passed; 23 native tests were skipped** because
Isabelle is installed on the lab computer. The checks cover all three adapters,
saved-input preservation, forced-Hammer acceptance, timeout diagnostics and
compact report accounting. The plan-only command selects exactly four checks;
Python 3.10 syntax and patch whitespace checks pass.
Native regression tests additionally cover retrying a later heuristic, discarded
partial progress, required-command failure, whole-target limits, interrupts,
Sledgehammer reservation, and generic sum rules with a negative case. Native
compilation and complete theorem success still require the lab installation;
local mocked tests do not establish either.

---

# Review of commit 6300569: rsum_bound proof search

Date: 2026-11-03. Source commit `6300569dde128f9e9ec54e7af1c4e12a66c4efc5`.
The two historical work directories and their sketches are preserved unchanged.

Both `target-pk0im2_0/search` and `target-3zezl1b1/search` completed all **657
context commands**, opened the oracle, and then failed at the same scaled-norm
bound. These are real search failures, not an import, parser or process crash.
One earlier gap was successfully reconstructed with `metis` in the first run.
Both Isabelle processes exited 0, but their structured results had
`success=false`, `target_closed=false`, and `category=timeout`; process success
must not count as a proof success.

The unresolved mathematics is: from `norm (f x) <= e` and `0 <= content k`,
normalize `norm (content k *R f x)` and multiply the bound by `content k`.
The original DSP portfolio simplifies to a product inequality but has no
nonlinear arithmetic fallback or explicit multiplication-monotonicity strategy.
`linarith` alone does not infer an inequality between products of variable terms.
Sledgehammer returned no proof within its 40-second search budget (the recorded
calls took 45.216 and 48.467 seconds including search/reconstruction overhead).
This does not establish a Sledgehammer implementation bug or justify marking a
timeout as success.

Changes:

- Checker **p10** retains the original heuristic ordering and appends bounded
  scalar-norm normalization plus `metis` with standard order rules, multiplication
  monotonicity, and nonlinear arithmetic candidates. They execute through the
  existing kernel-checked candidate path and must close the pending obligation.
  No target-specific theorem or completed Isabelle proof is supplied.
- Both Draft-to-Sketch and direct Sketch prompts now separate scalar normalization,
  sign conditions, multiplication monotonicity, and the stages of a finite-sum
  bound. `linarith` is not suggested for nonlinear products. Prompt versions are
  updated for Babel, Hundred Theorems and the most-match adapters.
- Failure results expose `failed_obligation`, including the preceding source
  command/line and a goal diagnostic from the same failed state. Compact reports
  retain this field even if the large context/attempt payload is truncated.
- Hundred Theorems now uses the exact-original-import heap cache already used for
  most-match, including single-worker batch runs. Imports are not broadened and
  the inherited-target guard remains. The two recorded startups took **272.823 s**
  and **306.492 s**; the change moves reusable import work outside per-target jobs.
  Its actual speedup still needs a lab measurement. The default batch admission
  allowance is now 12 GiB per worker; it is not a hard memory limit.
- There is still no separate replay build. A focused retry runs only the two
  previously failed proof searches, using the recorded sketches byte-for-byte
  after normalization and checking the old request hashes and current context.
  It neither calls an LLM nor reruns passed context/capability controls.

The order and norm facts were checked in the official Isabelle2026 sources:
[`Real_Vector_Spaces.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Real_Vector_Spaces.thy)
and [`Rings.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Rings.thy).
Native compilation and complete proof success remain lab acceptance checks;
offline tests cannot establish them.

Validation: the full suite collected 347 tests (326 passed, 19 native tests
skipped, and two fake-transport fixtures needed updates for shared preparation).
After correcting those fixtures and avoiding heap builds for already blocked
sketches, **all 57 affected tests passed** in the focused rerun. The recorded
requests match the current extracted target/context; retry selection contains
exactly two failed searches and zero standalone context/control tests. Python
3.10 syntax and patch whitespace checks passed. No native Isabelle or LLM call
was made locally.

## Rerun only the failed searches

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline.v2_dsp.retry_rsum_bound \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
```

Append `--plan-only` to preview selection without starting Isabelle. Setup checks
and one shared original-import heap are prerequisites. Both selected searches
still execute their masked context as part of proving the target. There are **two
proof tests**, zero standalone context tests, zero backend proof controls, and no
native acceptance fixture. This is a prover regression; its direct-input envelope
provides current source/context validation and is not a new generation experiment.

Push the six compact files under
`eval/preflight_results/isabelle2026-rsum-bound/<timestamp>/`. Full work artifacts
stay ignored under `itpeval/.runs/`; there is no diagnostics ZIP. A failure at any
later sketch step remains a failure with its current goal and source command
reported. New prompt wording affects newly generated sketches, not these stored
regression inputs.

---

# Review of committed run fabeacf1: context repairs

Date: 2026-11-02. Source: commit `fabeacf1a89563bee5c9d9cc2d1a810fc31f1e54`,
run `20261102T054119Z-67780b09`. Historical reports remain unchanged.

There were **227 passes, 41 failures, and 24 unavailable contexts** among 292
checks. All 30 setup/backend/dataset-proof checks passed. All 163 Babel contexts
passed; Hundred contributed 34 passes, 41 failures, and the 24 core Set contexts.
No failure in this run was an LLM Draft/Sketch or Sledgehammer control failure.

| Failed contexts | Root cause | Repair |
| --- | --- | --- |
| 5 Cauchy-Schwarz targets | `dot_square_norm` appears both as an earlier class-local helper and a later global declaration. Checking later basenames in the current namespace falsely rejected the earlier helper. | Exclude ambiguous later basenames already declared in the prefix. Always retain the selected target check, checks for unambiguous later names, exclusion of later source, and the original-theory ancestor guard. |
| 15 factor/remainder targets | The masking command boundary list lacked `setup_lifting`, so masking the preceding typedef proof also deleted `setup_lifting type_definition_poly`. `lift_definition zero_poly` then had no quotient registration. | Preserve lifting setup/update/forget commands and bump the masking version to `hundred_theorems_repair_p2`. Original mathematical statements stay unchanged. |
| 21 Bertrand targets | Relative `ML_file` used the infrastructure theory's master directory, and the companion `bertrand.ML` had never been staged. | Copy only the SHA-256-pinned companion from configured AFP sources into the job. Initialize the copied context with the official `Resources.begin_theory` API and the driver job's directory. Do not import the completed Bertrand target theory. |

Additional fixes:

- Trusted context commands use `context_step_timeout_s=120`; generated proof
  commands still use `step_timeout_s=10`. The original Bertrand source says its
  calculation can take a minute. Both budgets remain bounded by the target deadline.
- Top-level errors now include the underlying Isabelle exception, rather than
  only `failed command`, so the compact summary retains the useful diagnosis.
- Missing or modified companion sources fail explicitly before native execution.
  The pinned `bertrand.ML` SHA-256 is
  `423110be6c919dec5add93272fe461371562ea66fec40bd3832bcbb3a6627bf0`.
- Checker **p8** and updated adapter hashes invalidate prior prover caches.
  The new resource API is pinned against `src/Pure/Build/resources.ML` from the
  official Isabelle2026 source archive, in addition to the existing nine pins.

API/source verification: the official
[Isabelle2026 source archive](https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2026.tar.gz),
[`Resources.begin_theory`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Build/resources.ML),
and the installed pinned AFP-2026 `Bertrands_Postulate/bertrand.ML`.

## Rerun on the lab

The full preflight below extracts current contexts itself; it does not reuse the
old broken masked records or call an LLM. AFP already installed by `prepare_afp`
can be reused. Keep the 24 core Set targets unavailable and in the 262 denominator.

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.lab_preflight \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json \
  --dataset both --all-targets --expected-contexts 262
```

For experiments that read saved JSONL, re-extract the affected Polynomial records
and regenerate their dependent Draft/Sketch artifacts. The native checker rejects
old contexts missing lifting registration with a re-extraction instruction. Do
not splice the new template into a saved artifact with stale hashes/proof spans.
Unchanged contexts can retain their existing saved artifacts.

Validation: **302 tests collected, 285 passed, 17 native integration tests skipped**.
All 262 contexts passed offline preparation with the actual pinned AFP helper:
241 required no auxiliary file, and 21 staged `bertrand.ML`. Candidate selection
still reports 262 with no extraction issues and 24 unavailable core Set contexts.
Python 3.10 syntax and patch whitespace checks passed.

Offline regression coverage checks the exact 5/15/21 failure groups, all 262
candidates, preservation of lifting commands, missing/modified auxiliary sources,
source staging and request identity, and separate context/proof timeout settings.
The lab fixture now checks the context's master directory, and opt-in integration
tests check all three affected theories. Actual Isabelle compilation and the full
lab rerun are still required; offline checks are not proof of native success.

---

# AFP setup and unavailable-context reporting update

Date: 2026-11-01. This update supersedes the core Set failure accounting below.

The consolidated preflight now records the **24 inherited core Set targets** as
`status=unavailable_context`, displayed as **unavailable context**. They stay in
the original 262-candidate scope and in all 292 report entries. A separate
`unavailable_contexts.json` and Markdown table list their identities and reasons.
They are not passed proofs or ordinary failures; no native job is launched for
these known unavailable contexts. The underlying prover's isolation guard remains.

`contexts_ok` and readiness exit status evaluate available contexts, while
`full_context_coverage` and `context_counts` expose missing coverage. An entirely
unavailable selection cannot pass. Ordinary missing dependencies, proof failures,
setup failures and interruptions retain their existing failure/blocking behavior.
The **31 AFP-dependent contexts are separate from the 24 Set targets** and receive
normal native checks after setup.

`prepare_afp.py` installs the entire official `afp-2026-10-26.tar.gz` release with
pinned SHA-256 and `AFP_VERSION=2026` checks. It extracts through a private staging
directory, rejects links and escaping archive paths, preserves existing user
checkouts, records installation provenance, and updates only `session_roots` in
the selected native config after successful installation. It preserves other
roots/settings and reuses its installation on subsequent runs. The local config
now contains `external/afp-2026/thys`. The full installer was exercised locally:
16,148 source files extracted; actual Isabelle compilation still requires the lab.
See [setup and complete preflight commands](README.md).

---

# Isabelle2026 restored as default; no separate replay

Date: 2026-11-01.

The active `v2_dsp/` backend is again native Isabelle2026, restored from `e06e512`
with the prior p6 safety fixes intact. Original DSP/PISA/Isabelle2021 and its
recent diagnostics fixes are preserved separately in `v2_dsp_pisa/`. Both datasets
expose both implementations. Runtime configs, prompts, artifact schemas, output
paths, and tests are separate. `v2_itpeval/` is unchanged.

## Report diagnosis and current fixes

The report `eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/report.json`
had **57 passing / 8 failing checks**. All 26 then-current proof/search/replay
controls and three fixed real-theorem checks passed. The failures were the ML
fixture and seven Hundred Theorems dependency contexts, not a universal search
failure.

| Reported issue or additional finding | Current change |
| --- | --- |
| Fixture uses `OS.Process.sleep`, unavailable in Isabelle/ML | Use `Time.sleep`, the Isabelle API, in the interrupted-operation regression. |
| Bare `Euclidean_Algorithm` and `Primes` | Resolve to same-named `HOL-Computational_Algebra` theories. |
| Bare `Angles` and `Square_Matrix` | Resolve to `Triangle.Angles` and `Cayley_Hamilton.Square_Matrix`; require matching AFP sources. |
| Bare `Lattices` and `Boolean_Algebras` | Qualify with `HOL`; retain the ancestor guard for the copied core `Set` theory. |
| Missing `Pratt_Certificate` session | Report the required AFP session and root setup before building when no session roots are configured. |
| `Bad imports session` was missed by error classification | Classify the actual plural error as `import_error` and preserve the build diagnostics. |
| Nonzero build after writing a result XML could hide its log | Keep process status and bounded build-log excerpt; it cannot count as success. |
| Legacy local configs lacked new import mappings | Merge verified defaults into explicit mappings while retaining basename validation. |
| Version banners can include a release date | Accept only exact `Isabelle2026` or its colon-delimited date banner; reject RC/other releases. |

Import fixes modify generated import tokens and session declarations only.
Original dataset records, proofs and statements are unchanged. Session roots are
still required for AFP. The all-context dependency plan identifies **31 AFP-dependent
contexts** and **24 core Set contexts already inherited by HOL**. Those 24 stay in
the cohort as isolation failures, not successful translations or silently skipped
records. The next lab run may reveal additional release-compatibility issues.

API cross-checks: official
[`Time.sleep`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/General/time.ML),
[HOL session ownership](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/ROOT),
[Triangle session](https://github.com/isabelle-prover/mirror-afp-devel/blob/master/thys/Triangle/ROOT),
and [Cayley_Hamilton session](https://github.com/isabelle-prover/mirror-afp-devel/blob/master/thys/Cayley_Hamilton/ROOT).
These source checks establish the API/import owners, not installed AFP release
compatibility; use the AFP release matching the pinned Isabelle2026 distribution.

## Verification and lab acceptance

Separate replay has been removed from the native checker, runner, acceptance
catalog and integration tests. `verified` requires successful execution and
closure of the selected target in the original native job. Kernel-checked gap
reconstruction, no-admission filtering, inherited-target guards, request identity,
process exit checks and deadlines remain. Sledgehammer's own preplay remains.

The result records `verification_method=isabelle2026_native_completion`, omits
old replay-success fields, and clears stale diagnostics before each check.
Checker **p7** invalidates previous verification caches. Saved 2026 Sketches can
be rechecked with `--skip-sketch` without another model call. The new default
example config is 2026; PISA uses its separate package and 2021 config.

The consolidated preflight covers **all 262 candidate contexts** with
`--dataset both --all-targets --expected-contexts 262`. It has 23 backend controls,
three fixed dataset proofs and four selection/setup/fixture checks: **292 total**.
`--afp-root` supplies an existing repository-local AFP `thys` directory.
`dependencies.json` records exact import/session requirements and known inherited
contexts. Reports remain Git-trackable in `eval/preflight_results/isabelle2026/`.
The [current guide](README.md) gives the complete command and setup instructions.

Validation: **277 tests collected, 261 passed, 16 native integration tests skipped**.
Python 3.10 syntax checks passed for 187 pipeline/test files. All 12 native/PISA,
Babel/Hundred runner/prove/preflight CLI entry points load; no replay flags remain.
The exact all-targets command's plan selected 262 contexts across 29 topics,
23 controls and three dataset proofs, with no selection issues.

Local regression tests cover both backends, the full extracted cohort, original
record preservation, corrected imports, dependency diagnostics, protocol failures,
no-replay behavior, and unchanged context/timeout isolation. Actual ML compilation
and native execution remain pending on the Linux lab host. No LLM calls or
historical report edits were made.

---

# Historical reviews

The sections below preserve the review history. Their replay requirements,
checker versions, default backends and old commands are superseded above.

# DSP/PISA rollback review

Date: 2026-11-01. The active backend is original DSP + PISA + Isabelle2021.
The native Isabelle2026 review below is historical; its ML paths, fixtures and
replay requirements no longer describe active code.

## Pulled preflight results

Reviewed `eval/preflight_results/isabelle2026/20261101T065608Z-a25df37e/report.json`:
65 checks, **57 passed, 8 failed**. All 26 proof/search controls and all three
real-theorem proof checks passed. The infrastructure fixture failed because
`OS.Process.sleep` was not declared in the Isabelle/ML environment. This does
not indicate that all native proof search was broken.

The other seven failures were dataset import/dependency issues:

| Hundred Theorems topic | Missing dependency reported |
| --- | --- |
| 011, infinitude of primes | Bare `Euclidean_Algorithm` |
| 027, triangle angles | Bare `Angles` |
| 049, Cayley-Hamilton | Bare `Square_Matrix` |
| 052, subsets / core Set | Bare `Lattices` and `Boolean_Algebras` |
| 065, isosceles triangle | Bare `Angles` |
| 089, factor/remainder | Bare `Primes` |
| 098, Bertrand | AFP session `Pratt_Certificate` |

The Fundamental Theorem of Integral Calculus context, including `rsum_bound`,
passed. Fixing imports alone cannot make a core `Set` target valid when the target
theory is already inherited; the context-leakage guard remains. Changing prover
versions does not automatically resolve missing dependencies. Matching library
versions still need installation and compatibility checks on the lab host.

## Requested rollback

The checker is copied directly from local `mathLLM/draft_sketch_prove`; see
[provenance and complete patch](upstream/ORIGIN.md). The original heuristic and
normalhammer algorithm is preserved. PISA is pinned to an Isabelle2021 revision.
The custom native ML backend, fixture and separate replay stage were removed.
Both datasets share the checker with separate data/results directories. API and
vLLM inference remain available.

The new consolidated preflight stores reports and all RPC/JVM/worker logs under
`eval/preflight_results/pisa_isabelle2021/`, outside Git ignore rules. It separates
setup/backend controls from real dataset-context checks, requires specific expected
negative outcomes, collects independent failures, and checkpoints each result.
`--all-targets` covers all 262 extracted candidate contexts.

Offline tests cover the copied algorithm, setup, handoffs, failure/resume accounting,
context selection, timeouts, owned-process cleanup and report behavior. Native
execution and ATP availability still require the Linux lab preflight. Original
source reduces custom implementation; it cannot guarantee compatibility with every
dataset theory or eliminate upstream bugs.

---

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

## Hundred Theorems rsum_bound preflight (52fa4ea)

Reviewed `52fa4eaf14b3bd5b7553a811928ce953d1087bc0`. The failure occurs before
`DSP_Driver` executes its ML worker, before the target proof is checked, and
before any Sledgehammer or LLM call. It does not indicate a bad generated proof.

The report is
`eval/results/hol_light_to_isabelle_v2/hundred-theorems/preflight/f9f02a6539f90379b88b.json`.
Its original message only said the worker produced no structured result. The
actual cause is in `work/context-_rdyic9a/build.log`:

- Isabelle searched the temporary directory for `Lebesgue_Measure.thy` and
  `Tagged_Division.thy`, because the driver copied the original bare import names.
- The generated `ROOT` had no `sessions` clause, so
  `HOL-Real_Asymp.Real_Asymp` was unavailable too.

The extracted theory is `Henstock_Kurzweil_Integration`; its original header is
preserved in the record and matches the
[official library source](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Analysis/Henstock_Kurzweil_Integration.thy).
It normally belongs to `HOL-Analysis`, as specified by the
[HOL session ROOT](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/ROOT).
The [system manual](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Doc/System/Sessions.thy)
distinguishes a parent session from imported session namespaces: cross-session
theory imports need qualified names and matching `sessions` declarations.

### Fix

1. Add a validated `theory_imports` config field. The example and pulled local
   config map `Lebesgue_Measure` and `Tagged_Division` to their same-named theories
   in `HOL-Analysis`. Mappings cannot replace a theory with a different basename.
2. Qualify only the import tokens in generated driver/request/replay headers;
   preserve the extracted record, mathematical context, theorem statement and
   proof spans. Record original/resolved imports in `import_resolution.json`.
3. Derive the direct owning session dependencies from qualified imports and merge
   them with configured `session_dependencies`. Search and replay both get
   `HOL-Analysis` and `HOL-Real_Asymp` in `ROOT` for this target.
4. Preserve the build-log path, bounded log excerpt, process return code, work
   directory and failure category in preflight/proof diagnostics. Propagate
   `import_error` through the batch runner without calling the model. Missing or
   malformed structured results still cannot count as successful verification.
5. Keep `base_session: "HOL"`. Using `HOL-Analysis` as the parent or importing the
   complete `Henstock_Kurzweil_Integration` would risk bringing in the existing
   target theorem. The adapter rejects direct self-imports in search and replay.

The checker version is now `dsp_isabelle2026_native_p4`; configuration and adapter
hashes invalidate older verification caches. Prompts are unchanged because the
failure occurs before inference. Historical result logs were not edited.

### Lab rerun

If `$CFG` points to another private config, add the `theory_imports` mapping shown
in the README. Otherwise the tracked config is already updated. With the user's
existing Python environment activated:

~~~bash
cd /data/not_backed_up/yxu209/itpeval-modify
PIPE=eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline
CFG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
DATA=eval/results/hol_light_to_isabelle_v2/hundred-theorems

python -m "${PIPE}.v2_dsp.preflight" \
  --expected-root "$PWD" \
  --config "$CFG" \
  --input "$DATA/single_records.jsonl" \
  --topic 015_the_fundamental_theorem_of_integral_calculus \
  --target-key rsum_bound
~~~

The existing parsed record can be reused. No new Draft or Sketch is needed for
preflight. An opt-in native test checks this exact context without an LLM:

~~~bash
export ITPEVAL_NATIVE_ISABELLE2026_CONFIG="$CFG"
python -m unittest discover \
  -s tests/hol_light_to_isabelle/v2_dsp \
  -p 'test_native_integration.py' -k hundred_rsum_bound
~~~

Local regression checks exercise the real extracted record with mocked native
execution, verify consistent qualified headers and session dependencies, preserve
original hashes/statements, reject theory substitution/self-import, and retain
failure details through preflight and the batch runner. These checks validate the
adapter, not Isabelle's compilation of the 153-helper prefix. That final native
check requires the lab installation.

Validation for this revision: **150 offline tests passed; 12 native integration
tests skipped** (162 total). Python 3.10 syntax checks passed for all 100 v2
pipeline modules, and `git diff --check` passed. No live model calls or native
Isabelle execution were performed locally. The original `52fa4ea` build log is
now classified as `import_error` with its actual missing-theory diagnostics.


## Comprehensive Isabelle2026 audit (after 0be9014)

Scope: configuration and environment isolation, session/import resolution,
request/result identity, native command execution and obligation closure,
Sledgehammer reconstruction, process deadlines/cleanup, proof replay, and
verification-cache/result reporting. Both datasets use this shared engine.
No API inference, toolchain installation, or historical-result changes were made.

### Findings and fixes

| Finding | Consequence | Fix |
| --- | --- | --- |
| High: Isabelle ignores timeouts below 1 ms | A configured microsecond limit, or an almost exhausted ML budget, could execute without the intended ML timeout. The Python whole-job watchdog still bounded the worker. | Reject configured step/hammer/preplay limits below 0.001 s; abort an ML operation when its remaining budget is below that resolution; pin `timeout_scale=1.0` in builds. |
| High: proof filtering only considered bare words | `by ("tactic" ...)`, qualified `Pure.raw_tactic`, and quoted decimal-escaped names bypassed the Python no-ML policy. | Inspect decoded identifier basenames in Python and native tokens. Apply the same policy to Sketches, reconstructed proofs and saved proof replay. Ordinary quoted methods and mathematical formulas remain supported. |
| High: proof code could change admission/oracle settings | `supply [[quick_and_dirty = true]]` / `smt_oracle = true` passed the filter. Imported defaults could also enable SMT oracle mode. | Reject those settings in generated proof bodies and explicitly reset both to false immediately before the target in search and replay. Prefix admissions remain explicit. |
| High: replay-only skipped the native context-leakage gate | Replaying a saved proof against a changed parent/import graph did not run the same target/later-fact checks as search. | Run a context-only native request before replay; keep it in `native_context`; no proof search occurs. Both paths reject the selected theory if it is already an ancestor, before copied declarations execute. Direct self-import checks also recognize `.thy` suffixes. |
| Medium: rechecks inherited old success diagnostics | A failed new replay could still contain `native_replay.success = true`, old prover settings, paths, or an old verification fingerprint from its input row. | Clear previous verification artifacts before checking. Current diagnostics and the input proof are added only by the current check. Backend setup failures use the same cleanup. |
| Medium: watchdog/startup failures omitted structured build diagnostics | A killed worker often has no XML result, leaving the important build excerpt outside the reported error. | Wrap build timeout/launch errors with category, build directory/session, log path, bounded excerpt, and available process return code. |
| Test gap: a successful default hammer control does not prove ATP availability | Isabelle2026's integrated tactics can solve the small control without using an external ATP. | Add an opt-in native case that selects only bundled E, requires a `Played` preplay and reconstruction, and verifies fresh replay. Keep integrated-tactic coverage. |

The offline regressions reproduced the timeout/filter/stale-result failures
before the fixes. Search success still requires complete target closure and
independent replay; partial subgoal progress alone never counts as success.
Heuristic ordering and configured search budgets/provers are unchanged.
Per-operation timeouts still abort the isolated worker; the audit does not
introduce retries after an interrupted native state.

Checker version: `dsp_isabelle2026_native_p5`.
Sketch validator: `isabelle_sketch_structure_v2`.
Changed adapter/checker fingerprints prevent reuse of old verification results.
Saved valid Sketches can be rechecked with `--skip-sketch`; this does not require
regenerating Drafts or making an API call. Generated bodies are revalidated.

### Source checks

All nine locally cached release source files still match
`native/release_sources.json`. The runtime keeps those Isabelle2026 release
checks. Additional API/semantic cross-checks used the official repository at
`bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370`, not an assumption that current master
is identical to the release:

- [`timeout.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Concurrent/timeout.ML): `Timeout.ignored`, the 1 ms threshold and `timeout_scale`.
- [`method.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/method.ML): method names use `Parse.name`; `tactic` and `raw_tactic` evaluate ML.
- [`SMT.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/SMT.thy) and [`smt_solver.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/HOL/Tools/SMT/smt_solver.ML): `smt_oracle` controls whether solver output needs proof reconstruction. Standard SMT.thy turns it off; an input context could turn it on again.
- [`context.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/context.ML) and [`theory.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/theory.ML): ancestor identity and base theory names.
- Cached release `sledgehammer.ML`, `sledgehammer_proof_methods.ML`, `toplevel.ML`, `outer_syntax.ML`, and `token.ML`: preplay filtering, structured reconstruction, proof-state transitions and executable token serialization. Existing release-compatible handling remains in place.

### Dataset/setup coverage

The offline survey extracted every current aligned target, validated its stored
statement, proof span and preceding context, and resolved configured imports:
**163 Babel targets + 99 Hundred targets; no static validation errors.**
This is not an Isabelle build result. Babel uses `Main`; Hundred has the
following additional setup concerns:

| Hundred topic | Targets | Import/context concern to check natively |
| --- | ---: | --- |
| `011_the_infinitude_of_primes` | 4 | Bare `Euclidean_Algorithm`. |
| `015_the_fundamental_theorem_of_integral_calculus` | 7 | Existing `Lebesgue_Measure` / `Tagged_Division` qualification fix plus `HOL-Real_Asymp`. |
| `027_sum_of_the_angles_of_a_triangle`, `065_isosceles_triangle_theorem` | 2 | Bare `Angles`; compatible dependency theory/session required. |
| `049_the_cayley-hamilton_theorem` | 1 | Bare `Square_Matrix`; compatible dependency theory/session required. |
| `052_the_number_of_subsets_of_a_set` | 24 | Copy of core theory `Set`, with bare `Lattices` / `Boolean_Algebras`. A loaded original `Set` is rejected as inherited target context. Do not bypass the guard by renaming the copied theory or broadening its parent. |
| `089_the_factor_and_remainder_theorems` | 15 | Bare `Primes`, plus qualified library imports. |
| `098_bertrand_s_postulate` | 28 | Explicit AFP `Pratt_Certificate.Pratt_Certificate`; configure a compatible AFP session root. |

The remaining 18 Hundred targets use `Complex_Main` and/or qualified HOL library
imports. Qualified names alone do not establish release compatibility. Unknown
bare import owners are not guessed. Missing AFP dependencies are not installed
automatically. No mathematical statement, imported theorem, or dataset prefix
was replaced to make a target pass. Targets whose original proof is already in
the parent need an explicitly redesigned experimental context or exclusion;
they cannot be counted as isolated proof-translation successes under that parent.

### Validation and lab commands

Final offline run: **173 tests collected; 158 passed and 15 native tests skipped**.
The eight focused audit regressions also passed after the final formula-name
handling refinement. Python 3.10 syntax checks passed for 111 pipeline/test files;
`git diff --check` passed with the repository's existing CRLF handling.

The new offline tests cover the reproduced failures, quoted/escaped/qualified
names, accepted ordinary proof text, direct self-import variants, failure log
propagation, replay-only context rejection, and stale-diagnostic removal.
The native fixture additionally exercises a real interrupted ML operation,
sub-millisecond rejection without executing the body, decoded token checks,
and ancestor-theory rejection. New integration cases cover E reconstruction,
SMT setting reset, and inherited target rejection in search and replay.

Native compilation/execution remains pending on the lab host. The local Windows
machine has no Isabelle2026 installation; offline tests cannot establish that
the modified ML compiles or that an ATP works on that machine.

After syncing the changes and activating the main Python 3.10 environment:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
export ITPEVAL_NATIVE_ISABELLE2026_CONFIG=eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json

# Native controls, E, timeout/filter fixtures, representative contexts and replay.
python -m unittest discover \
  -s tests/hol_light_to_isabelle/v2_dsp -p 'test_native_integration.py'

# Then repeat the original Hundred single-target preflight.
PIPE=eval.pipeline.hol_light_to_isabelle.hundred_theorems_pipeline
DATA=eval/results/hol_light_to_isabelle_v2/hundred-theorems
python -m "${PIPE}.v2_dsp.preflight" \
  --expected-root "$PWD" \
  --config "$ITPEVAL_NATIVE_ISABELLE2026_CONFIG" \
  --input "$DATA/single_records.jsonl" \
  --topic 015_the_fundamental_theorem_of_integral_calculus \
  --target-key rsum_bound
```

For a batch, supply the full extracted record file and `--all-targets`, removing
the single-topic/target filters. Keep failed contexts in the reported cohort.
The first infrastructure build and large library imports may need the existing
600 s startup allowance; changing it is an explicit configuration choice.


## Lab result 708e204 and consolidated preflight

Reviewed the artifact merged by `708e204356f9fff41ac46b6f1de41dd92fdbe4a8`:
`eval/results/hol_light_to_isabelle_v2/work/target-paafzeb6/search/result.xml`.
It arrived in `35520b1`, whose parent is `0be9014`; this result predates the p5
comprehensive audit. Only the XML was included, without its request, build log,
or aggregate test report. It cannot establish the outcome of the whole native
suite or whether the subsequent audit changes passed on the lab host.

The target context and goal loaded. Sledgehammer returned an executable candidate
`using integral_shift by metis` with `native_outcome=some`,
`reconstruction_source=native_tactic`, and `candidate_count=1`. Search then rejected
that candidate as `unsafe reconstructed command` and ended with
`missing_reconstruction`. Zero separate preplay results are valid for this
integrated tactic path; that is not the failure. The optional failed `sos`
heuristic is also not the cause of the final rejection.

The adapter's allowlist assumed ignored command spans had an empty name.
Isabelle parses whitespace/comments between `using` and `by` into an ignored
transition named `<ignored>`. The released `Outer_Syntax.parse_span` and
[`Toplevel.is_ignored`](https://github.com/isabelle-prover/mirror-isabelle/blob/bc2b0ebd7ff3e6779a3fc9c0d88b90333ed83370/src/Pure/Isar/toplevel.ML#L490)
confirm this behavior. The matching Isabelle2026 source hashes are already pinned
in `native/release_sources.json`.

Checker **p6** accepts `Toplevel.is_ignored tr` while retaining the narrow actual
command allowlist and rejection of malformed/unsafe commands. Unexpected command
errors now include the parsed command name. The packaged native fixture parses
actual `using`/`unfolding`/`apply`/`done` spans, including comments and separators;
it also confirms malformed and `sorry` transitions remain rejected. Two controls
execute the injected multi-command candidate from a real pending goal and require
fresh replay, rather than testing serialization alone. The real circle-average
case additionally forces the integrated `metis` path.

`v2_dsp.lab_preflight` consolidates setup, the native fixture, 26 backend controls,
three fixed real-theorem proofs, and 32 contexts across both datasets into one
recorded invocation (65 checks including selection/setup). It builds the shared
native parent once and uses fresh search/replay jobs for each case. Independent
failures continue; a shared setup failure explicitly blocks dependent checks.
It records exact scope and expected negative outcomes, separates backend health
from dataset compatibility, and supports all 262 contexts via `--all-targets`.
No LLM calls or new model-generated experiment samples are involved.

Reports now have a dedicated, explicitly unignored destination:
`eval/preflight_results/isabelle2026/<UTC-timestamp>-<run-id>/`. The consolidated
runner saves a JSON report, Markdown summary, per-check results, effective config,
backend/source identity, native requests/results, replay theories, build/process
logs, and a ZIP. Completed work is checkpointed; an interrupted run marks the
unexecuted checks as blocked and finalizes diagnostics when possible. Reports
must be staged normally, without forcing ignored runtime files into Git.

Run on the lab host with the main Python 3.10 environment active:

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.lab_preflight \
  --expected-root "$PWD" \
  --config eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json
```

Add `--all-targets` for every extracted target. Default record discovery was checked
locally: 262 available targets, 29 topics, 32 selected contexts, no extraction
selection errors. The focused offline tests cover report/bundle preservation,
setup blocking, continuation after failures, expected rejection categories,
selection scope, and exact candidate execution/replay requirements. Actual native
compilation, Sledgehammer execution and proof replay remain pending on the Linux
lab computer; the local Windows checks do not establish native acceptance.

Validation after this change: **194 tests collected; 178 passed and 16 native
integration tests skipped**. All 20 consolidated-preflight offline regressions
passed. Python 3.10 syntax checks passed for 131 pipeline/test files. Git ignore
checks confirmed report JSON, logs and ZIPs are trackable while experiment/runtime
outputs stay ignored. The reviewed parser/transition files matched the pinned
Isabelle2026 hashes; `git diff --check` passed with existing CRLF handling.
