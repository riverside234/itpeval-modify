# Sharing preflight reports without large Git files

New Isabelle2026 and PISA preflights export at most six files per run:

- `report.json`: status, all check outcomes, candidate counts and local artifact path.
- `summary.md`: readable outcome table.
- `checks.jsonl`: one bounded payload per check, in report order (`details_line`).
- `metadata.json`: configuration, backend/source identity, dependencies and log-export counts.
- `logs.jsonl`: bounded head/tail excerpts from build, process and server logs.
- `unavailable_contexts.json`: separate unavailable contexts (native backend).

Every exported file has a 32 MiB cap. Individual check payloads are compacted to
48 KiB; log excerpts retain at most 16 KiB of original log bytes per file, with
up to 1,024 logs. Truncation and omitted-log counts are explicit. Full payloads,
requests and logs remain in ignored `itpeval/.runs/preflight/<backend>/<run-id>/`.
There is no generated ZIP and no per-check file tree in the report directory.
Proof checking, all 262 candidates and unavailable-context accounting are unchanged.

Only the compact filenames and these README files are eligible for new Git
tracking under `eval/preflight_results/`. Existing tracked historical files are
not automatically removed by `.gitignore`.

## Compact the rejected lab run

Run after transferring the updated code to the lab checkout. Stop the run first;
this command only accepts completed/interrupted reports. It does not run Isabelle
or an LLM, or change Git branches, commits, the index, or remotes.

```bash
cd /data/not_backed_up/yxu209/itpeval-modify
RUN=eval/preflight_results/isabelle2026/20261102T054119Z-67780b09
python -m eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.compact_preflight \
  --expected-root "$PWD" --run "$RUN"
```

The complete original directory, including `diagnostics.zip`, is moved to
ignored `itpeval/.runs/preflight_archives/` only after the compact output is ready.
No original diagnostics are deleted. Check outcomes, counts and scope are
preserved. The command prints the exact backup location. Repeat `--run` to
compact other completed runs; repeating a successful conversion is a no-op.
A failed conversion leaves the original directory in place.

## Repair the rejected Git commit

GitHub rejects files larger than 100 MiB. A later deletion commit cannot remove
the large blob from the earlier unpushed commit. The rejected history must be
rewritten; Git LFS is unnecessary for these disposable diagnostic artifacts.
See [GitHub's large-file removal instructions](https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-large-files-on-github#removing-files-from-a-repositorys-history).

First inspect the unpushed history and create a local recovery branch:

```bash
git status --short
git log --oneline origin/main..HEAD
git log --oneline origin/main..HEAD -- "$RUN"
git branch "backup/preflight-before-cleanup-$(date +%Y%m%d-%H%M%S)"
```

If the offending run appears **only in the latest unpushed commit**, compact it
as above, then replace the tracked run contents and amend that commit:

```bash
git rm -r --cached --ignore-unmatch -- "$RUN"
git add -- .gitignore "$RUN"
git diff --cached --stat
git commit --amend --no-edit
git push origin main
```

`git rm --cached` changes Git's index, not local files. `git add` re-adds only
compact reports. Review the staged diff before amending, including any other
changes already staged. Keep the recovery branch local; do not push it or use
`git push --all`, as it still references the original large ZIP.

If the large run occurs in **multiple unpushed commits**, amending just the last
commit is insufficient. After the backup, compaction and staged-diff review,
you can consolidate the unpublished commits while retaining their combined file
changes. This intentionally replaces their individual commit history. Ensure
`origin/main` is an ancestor first; otherwise integrate the remote changes before
using this sequence:

```bash
git merge-base --is-ancestor origin/main HEAD
# Continue only if that command succeeded and these commits are unpublished.
git reset --soft origin/main
git rm -r --cached --ignore-unmatch -- "$RUN"
git add -- .gitignore "$RUN"
git diff --cached --stat
git commit -m "Update pipeline and compact preflight reports"
git push origin main
```

Neither route needs force-push for rejected unpublished commits based on the
current remote branch. If the remote has advanced, resolve that divergence rather
than force-pushing. Code fixes also need to be committed and transferred through
your normal workflow; the commands above focus on the rejected run.
