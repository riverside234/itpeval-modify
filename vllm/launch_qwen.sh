#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$SCRIPT_DIR/env_vars.sh"
SERVER_PYTHON="$ITPEVAL_ROOT/vllm/env/bin/python"
if [[ ! -x "$SERVER_PYTHON" ]]; then
  echo "Missing isolated server environment: $ITPEVAL_ROOT/vllm/env" >&2
  echo "Follow vllm/README.md to create it." >&2
  exit 1
fi
exec "$SERVER_PYTHON" "$SCRIPT_DIR/serve.py" "$@"
