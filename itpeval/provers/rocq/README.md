# Rocq support

This folder contains the Rocq/Coq adapter for `ITPEval`.

Files:
- `install.sh` installs Rocq into `ITPEVAL_PREFIX/rocq` using a local opam root and switch.
- `check.sh` compiles `hello/hello.v` with `rocq` or `coqc`.
- `hello/hello.v` is the minimal smoke-test lemma.

The install path is intentionally local and isolated:
- opam root: `ITPEVAL_PREFIX/rocq/opamroot`
- switch name: `rocq` by default

You can override versions with:
- `ROCQ_VERSION=9.0.0`
- `OCAML_VERSION=4.14.2`
- `ROCQ_SWITCH_NAME=rocq`
