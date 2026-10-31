#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
if [[ -z "${CONDA_PREFIX:-}" ]]; then
  echo "Activate the Python 3.12 server environment first: conda activate vllm" >&2
  exit 1
fi
SERVER_PYTHON="$CONDA_PREFIX/bin/python"
if [[ ! -x "$SERVER_PYTHON" ]]; then
  echo "Missing Python interpreter in the active conda environment: $SERVER_PYTHON" >&2
  exit 1
fi
source "$SCRIPT_DIR/env_vars.sh"
exec "$SERVER_PYTHON" "$SCRIPT_DIR/serve.py" "$@"
