# ITPEval

`ITPEval` is a lightweight environment harness for Interactive Theorem Provers (ITPs).

Goals:
- Install a set of common ITP toolchains locally (no global system pollution).
- Provide one command to (best-effort) install and one command to smoke-test everything.
- Keep native prover setup isolated under `itpeval/provers/<name>/`.

## Quickstart (macOS)

`bootstrap-system.sh` targets Amazon Linux 2023 and will not work on macOS. Use the macOS bootstrap instead:

```bash
cd itpeval
./bin/bootstrap-macos.sh   # installs Homebrew deps (opam, gcc, java, …)
./bin/itpeval install
./bin/itpeval check
```

### macOS prover compatibility

| Prover | macOS (Apple Silicon / Intel) | Notes |
|--------|-------------------------------|-------|
| Lean 4 | Works | `elan` supports arm64/x86_64 |
| Rocq (Coq) | Works | Requires `opam` (installed by bootstrap) |
| HOL Light | Works | Builds via OCaml (installed by bootstrap) |
| Isabelle | Works | `install.sh` selects the macOS tarball automatically |

```bash
./bin/itpeval install lean4 rocq hol-light isabelle
./bin/itpeval check  lean4 rocq hol-light isabelle
```

#### Isabelle tarball override

`install.sh` auto-selects `Isabelle<version>_macos.tar.gz` on macOS (Isabelle ships a universal build). If the filename ever differs, override it:

```bash
ITPEVAL_ISABELLE_TARBALL=Isabelle2024_macos_arm64.tar.gz ./bin/itpeval install isabelle
```

## Quickstart (Amazon Linux 2023)

From the repo root:

```bash
cd itpeval
./bin/bootstrap-system.sh
./bin/itpeval install
./bin/itpeval check
```

To install/check only a subset:

```bash
./bin/itpeval install lean4 rocq isabelle
./bin/itpeval check lean4 rocq isabelle
./bin/itpeval run lean4 rocq
./bin/itpeval report
```

To evaluate a one-off snippet/file against a single prover:

```bash
./bin/itpeval eval --prover rocq --ensure-installed --code $'Theorem t : 2 + 3 = 5.\\nProof. reflexivity. Qed.'
./bin/itpeval eval --prover isabelle --mode snippet --ensure-installed --code 'lemma t: \"(2::nat) + 3 = 5\" by simp'
```

Install location defaults to `itpeval/_toolchains`. You can override:

```bash
ITPEVAL_PREFIX="$PWD/_toolchains" ./bin/itpeval install
```

Shared downloads default to `itpeval/.downloads`. You can override:

```bash
ITPEVAL_DOWNLOAD_CACHE="$PWD/.downloads" ./bin/install-all.sh
```

## What “check” means

Each prover folder contains:
- `install.sh`: installs the prover into `ITPEVAL_PREFIX`.
- `check.sh`: runs a small “hello” proof/script and ensures the prover can verify it.
- `hello/`: minimal files used by `check.sh`.

Every `install`, `check`, and `run` invocation creates a timestamped run folder under `itpeval/.runs/<timestamp>/` with:
- `results.jsonl` for machine-readable per-stage results
- `summary.json` for aggregated counts and per-prover status
- `logs/` for full per-prover stdout/stderr
- for `check`/`run`, a staged copy of `itpeval/tasks/<task>/` under `tasks/<task>/itpeval/` so the shared benchmark layout stays self-contained

## Supported provers

- Lean 4: `itpeval/provers/lean4/`
- Rocq (Coq): `itpeval/provers/rocq/`
- Isabelle: `itpeval/provers/isabelle/`
- HOL Light: `itpeval/provers/hol-light/`

## One-file “run any ITP” runner

If you want a single entrypoint where you choose a prover and pass some code, use `./bin/itpeval eval ...` (or the underlying `itpeval/itp.py`).

Run inline code (writes a minimal `ITPEVAL_TASK_DIR` layout and calls the selected prover adapter):

```bash
python3 itpeval/itp.py --prover lean4 --code 'theorem t : (2+3:Nat)=5 := rfl'
python3 itpeval/itp.py --prover rocq --code $'Theorem t : 2 + 3 = 5.\\nProof. reflexivity. Qed.'
python3 itpeval/itp.py --prover isabelle --mode snippet --code 'lemma t: \"(2::nat) + 3 = 5\" by simp'
```

## Shared cache

`itpeval/manifest.json` acts as a simple lockfile for shared downloads we already know about. The cache helper in `itpeval/bin/common.sh` stores files under `itpeval/.downloads` by default and reuses them across runs.

After sourcing the helper file, you can prefetch or reuse a download manually:

```bash
source itpeval/bin/common.sh
download_cached "https://example.com/some-archive.tar.gz" \
  "<sha256-hash>"
```

You can also pass a destination path as the third argument if you want the cached file copied somewhere specific.

If the file is already cached, the helper validates the hash and reuses it. If you set `ITPEVAL_DOWNLOAD_CACHE`, the same cache can live outside the repo for offline or shared-machine workflows.

## Per-prover notes

### Lean 4

- Installer: `itpeval/provers/lean4/install.sh`
- Toolchain override: `LEAN_TOOLCHAIN=leanprover/lean4:stable`
- Installs wrappers into: `ITPEVAL_PREFIX/bin/lean` and `ITPEVAL_PREFIX/bin/lake`

### Rocq (Coq)

- Installer: `itpeval/provers/rocq/install.sh`
- Uses a local opam root: `ITPEVAL_PREFIX/rocq/opamroot`
- You can override the opam root (useful if an old root is in a bad state): `ITPEVAL_ROCQ_OPAMROOT=/some/path`
- If `opam` is missing, downloads a local opam binary into `ITPEVAL_PREFIX/rocq/bin/opam`
- Opam repository URL override: `ITPEVAL_OPAM_REPO_URL=git+https://github.com/ocaml/opam-repository.git`
- Version overrides:
  - `ROCQ_VERSION=9.0.0`
  - `OCAML_VERSION=4.14.2`
  - `ROCQ_SWITCH_NAME=rocq`
  - `ITPEVAL_OPAM_VERSION=2.5.0`

### Isabelle

- Installer: `itpeval/provers/isabelle/install.sh`
- Downloads the Isabelle distribution tarball into `ITPEVAL_PREFIX/isabelle/dist`
- Tarball is selected automatically based on platform/arch (`_linux`, `_macos`, `_macos_arm64`)
- Version override: `ITPEVAL_ISABELLE_VERSION=Isabelle2024`
- Base URL override: `ITPEVAL_ISABELLE_BASE_URL=...`
- Tarball filename override: `ITPEVAL_ISABELLE_TARBALL=Isabelle2024_macos_arm64.tar.gz`
- Installs wrapper into: `ITPEVAL_PREFIX/bin/isabelle`

### HOL Light

- Installer: `itpeval/provers/hol-light/install.sh`
- Clones from the upstream GitHub repo by default and builds in-place.
- Useful env vars: `HOL_LIGHT_HOME`, `ITPEVAL_HOL_LIGHT_HOME`, `ITPEVAL_HOL_LIGHT_SRC`
