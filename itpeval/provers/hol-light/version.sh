#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"
VERSION_BIN="${PREFIX}/hol-light/bin/hollight-version"

if [[ -x "${VERSION_BIN}" ]]; then
  exec "${VERSION_BIN}"
fi

echo "[ITPEval][hol-light] hollight-version not found; run install.sh first" >&2
exit 1
