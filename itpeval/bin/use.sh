#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
source "${SCRIPT_DIR}/common.sh"

PREFIX="$(itpeval_prefix)"

cat <<EOF
# Source this file to add ITPEval tools to your PATH:
#   source itpeval/bin/use.sh
export ITPEVAL_PREFIX="${PREFIX}"
export PATH="$(itpeval_root)/bin:${PREFIX}/bin:\$PATH"
EOF
