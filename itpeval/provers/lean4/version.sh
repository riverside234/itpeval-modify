#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
LEAN_BIN="${PREFIX}/lean4/bin/lean"

if [[ -x "${LEAN_BIN}" ]]; then
  exec "${LEAN_BIN}" --version
fi

if command -v lean >/dev/null 2>&1; then
  exec lean --version
fi

echo "[ITPEval][lean4] missing Lean binary" >&2
exit 1
