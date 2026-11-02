# Copied DSP checker and pinned PISA

`checker.py` was copied directly from local
`mathLLM/draft_sketch_prove/autoformalization/checker.py` at commit
`647aa65ca7b89f4e0f7a65dc15b4e64a81af5e80`. The local source matches that commit;
the original checkout remains untouched. See the
[original checker](https://github.com/albertqjiang/draft_sketch_prove/blob/647aa65ca7b89f4e0f7a65dc15b4e64a81af5e80/autoformalization/checker.py),
[retained license](../UPSTREAM_LICENSE.txt), and `origin.json` (normalized-LF hashes).

[checker.patch](checker.patch) is the complete integration diff against the local
original. `_run_step`, `_run_sledgehammer`, `_parse_output`, and `get_parsed` are
unchanged; tests compare their AST hashes. Heuristic order, state naming, the
parsing protocol (including `$`), and normalhammer fallback are original code.

Integration changes in the copied file:

- Lazy import of the original PISA client; omit unused imports/Slurm launcher.
- Accept the full dataset context instead of fixed miniF2F imports. The old static
  wrapper helpers remain unused.
- Report failed initialization with its RPC error; keep actual step exceptions.
- Initialize reward for an empty parse to fail closed and expose the final state
  for the context-only goal check.
- Remove upstream's two machine-wide process-kill commands. The adapter cleans
  up only its owned JVM and descendants.

`pisa_worker.py` adds RPC deadlines/logging, checks inherited theory names, and
retains state until cleanup. Forced hammer exists only for capability controls.
There is no separate replay or new ML search algorithm.

## PISA sources

The runtime pins
[PISA 690eed41fa03fe04ec015bb375c668cd6fd94261](https://github.com/albertqjiang/Portal-to-ISAbelle/tree/690eed41fa03fe04ec015bb375c668cd6fd94261).
Its README targets Isabelle2021/Java 11 and it includes `PisaFlexibleClient.py`,
the bundled Scala-Isabelle JAR, and `normalhammer`. Later revisions change client
and Sledgehammer interfaces for newer Isabelle versions.

Setup keeps the dependency checkout inside ITPEval. `pisa_sources.json` records
hashes of the pinned Scala sources, Python client, protocol, project settings and
bundled JAR. Scala/ML search code is unmodified. The only build change fixes the
literal `file:{$PWD}` URL to reference the same bundled JAR. Python gRPC bindings
are regenerated from unchanged `server.proto` into `generated/python/` to match
the installed protobuf/gRPC versions. Original client code and wire protocol
remain unchanged; the full checkout retains its upstream notices.

`pisa-build.json` records source, server JAR, build-setting and binding hashes.
Preflight checks those, Isabelle2021 and Java 11. Original DSP's model-generation
scripts are not needed here: the existing API/vLLM Draft and Sketch stages supply
our theorem-specific inputs.
