#!/usr/bin/env bash
# Bootstrap system dependencies for ITPEval on macOS (Homebrew).
# Equivalent of bootstrap-system.sh for Amazon Linux 2023.
# Run once before ./bin/itpeval install.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
source "${SCRIPT_DIR}/common.sh"

log "Detected OS: $(sw_vers -productName) $(sw_vers -productVersion) ($(uname -m))"

if ! command -v brew >/dev/null 2>&1; then
  log "Homebrew not found. Install it from https://brew.sh and re-run this script."
  exit 1
fi

log "Updating Homebrew"
brew update

log "Installing common system dependencies"
brew install \
  bash \
  coreutils \
  curl \
  git \
  gawk \
  gnu-sed \
  gzip \
  make \
  m4 \
  patch \
  rsync \
  xz \
  findutils \
  pkg-config \
  gcc \
  opam \
  ocaml \
  python3

log "Installing Java (needed for Isabelle)"
# Note: PVS on macOS runs via Docker (install.sh builds a linux/amd64 image automatically).
# Docker Desktop must be running when you install or check PVS.

if ! command -v java >/dev/null 2>&1; then
  brew install --cask temurin
else
  log "java already available: $(java -version 2>&1 | head -1)"
fi

log "Done. You can now run: cd itpeval && ./bin/itpeval install"
