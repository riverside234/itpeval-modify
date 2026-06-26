#!/usr/bin/env bash
# Compatibility wrapper — prefer: ./bin/itpeval check
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec "${SCRIPT_DIR}/itpeval" check "$@"
