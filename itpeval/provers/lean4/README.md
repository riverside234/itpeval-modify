# Lean 4 Adapter

This directory contains the Lean 4-specific ITPEval adapter.

Files:
- `install.sh`: installs Lean 4 locally under `ITPEVAL_PREFIX/lean4`
- `check.sh`: typechecks the minimal hello file
- `hello/Hello.lean`: the smoke-test source

The adapter uses `elan` and keeps all Lean files local to the ITPEval prefix.

