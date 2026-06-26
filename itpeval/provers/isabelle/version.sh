#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"

ISABELLE="${PREFIX}/isabelle/bin/isabelle"

if [[ -x "${ISABELLE}" ]]; then
  exec "${ISABELLE}" version
fi

if command -v isabelle >/dev/null 2>&1; then
  exec isabelle version
fi

echo "[ITPEval][isabelle] missing Isabelle executable" >&2
exit 1
