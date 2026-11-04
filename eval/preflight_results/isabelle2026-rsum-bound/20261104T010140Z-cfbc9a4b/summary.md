# Isabelle2026 lab preflight

Status: **complete**; overall OK: **True**.
Backend OK: **True**; available dataset checks OK: **True**.

Scope: `failed_only`; 1 contexts.

| Check | Domain | Status | Failure | Details |
| --- | --- | --- | --- | --- |
| input_selection | selection | pass |  | [Line 1](checks.jsonl) |
| metadata | setup | pass |  | [Line 2](checks.jsonl) |
| dependencies | setup | pass |  | [Line 3](checks.jsonl) |
| infrastructure | setup | pass |  | [Line 4](checks.jsonl) |
| import_heaps | setup | pass |  | [Line 5](checks.jsonl) |
| candidate_timeout_then_hammer | backend | pass |  | [Line 6](checks.jsonl) |
| rsum_bound_saved_search | dataset_proof | pass |  | [Line 7](checks.jsonl) |
| rsum_bound_direct_search | dataset_proof | pass |  | [Line 8](checks.jsonl) |
| rsum_bound_triangle_forced_hammer | dataset_proof | pass |  | [Line 9](checks.jsonl) |

## Unavailable context

0 selected contexts are unavailable; they remain in the candidate count.

| Target | Reason | Details |
| --- | --- | --- |

Overall OK evaluates the backend and available contexts; it does not claim unavailable contexts passed.
An entirely unavailable selection cannot pass.

Separate context tests were not requested. Each selected proof search still loads and checks its original context before proving the target.

Failure-only regression run: previously passed contexts and successful proof controls were not rerun.
Setup checks are prerequisites. Overall OK applies only to this selected subset; it is not a new full-dataset pass.

## Context scheduling

New checks completed: 0/0; batch wall time: 0.001 s; completed checks/minute: 0.0.
Overlap excludes unfinished jobs; it is not CPU utilization or serial speedup.

Expected negative controls pass only for their specific expected rejection.
Dataset failures do not turn into backend successes or disappear from the denominator.
Representative contexts do not establish readiness for every target; use --all-targets for that scope.

Push the compact report files in this directory. Full runtime artifacts are retained locally at: /data/not_backed_up/yxu209/itpeval-modify/itpeval/.runs/preflight/isabelle2026-rsum-bound/20261104T010140Z-cfbc9a4b
