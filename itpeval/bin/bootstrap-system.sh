#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
source "${SCRIPT_DIR}/common.sh"

log "Detected OS: $(. /etc/os-release && echo "${PRETTY_NAME}")"


if ! command -v sudo >/dev/null; then
  fail "sudo not found; install system deps manually"
fi

log "Installing common system dependencies (best-effort)"
run sudo dnf -y update
run sudo dnf -y install \
  bash \
  bzip2 \
  ca-certificates \
  curl \
  binutils \
  gcc \
  gcc-c++ \
  git \
  gzip \
  make \
  m4 \
  patch \
  perl \
  pkgconf-pkg-config \
  rsync \
  tar \
  unzip \
  xz \
  which \
  findutils \
  coreutils \
  gawk \
  sed \
  diffutils \
  ocaml \
  ocaml-findlib \
  ocaml-zarith \
  java-17-amazon-corretto-headless \
  fontconfig \
  dejavu-sans-fonts

log "Done"
