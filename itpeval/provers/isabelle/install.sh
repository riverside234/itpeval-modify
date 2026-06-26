#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITPEVAL_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# shellcheck source=../../bin/common.sh
source "${ITPEVAL_ROOT}/bin/common.sh"

PREFIX="$(itpeval_prefix)"

ISABELLE_VERSION="${ITPEVAL_ISABELLE_VERSION:-Isabelle2024}"
BASE_URL="${ITPEVAL_ISABELLE_BASE_URL:-https://isabelle.in.tum.de/website-${ISABELLE_VERSION}/dist}"

platform="$(uname -s)"
arch="$(uname -m)"
if [[ -n "${ITPEVAL_ISABELLE_TARBALL:-}" ]]; then
  TARBALL="${ITPEVAL_ISABELLE_TARBALL}"
elif [[ "${platform}" == "Darwin" ]]; then
  # Isabelle ships a universal macOS build (no separate arm64 tarball)
  TARBALL="${ISABELLE_VERSION}_macos.tar.gz"
else
  TARBALL="${ISABELLE_VERSION}_linux.tar.gz"
fi

INSTALL_ROOT="${PREFIX}/isabelle"
ARCHIVE_DIR="${INSTALL_ROOT}/archive"
DIST_DIR="${INSTALL_ROOT}/dist"
BIN_DIR="${INSTALL_ROOT}/bin"
WRAPPER="${BIN_DIR}/isabelle"
PREFIX_BIN="${PREFIX}/bin"

mkdir -p "${ARCHIVE_DIR}" "${DIST_DIR}" "${BIN_DIR}"
mkdir -p "${PREFIX_BIN}"

if [[ ! -d "${DIST_DIR}/${ISABELLE_VERSION}" ]]; then
  tarball_path="${ARCHIVE_DIR}/${TARBALL}"
  isabelle_sha="${ITPEVAL_ISABELLE_SHA256:-}"
  download_cached "${BASE_URL}/${TARBALL}" "${isabelle_sha}" "${tarball_path}"
  run tar -xzf "${tarball_path}" -C "${DIST_DIR}"
fi

ISABELLE_HOME="$(find "${DIST_DIR}" -maxdepth 1 -type d -name 'Isabelle*' | sort | tail -n 1)"
if [[ -z "${ISABELLE_HOME}" || ! -x "${ISABELLE_HOME}/bin/isabelle" ]]; then
  fail "failed to locate Isabelle distribution under ${DIST_DIR}"
fi

cat > "${WRAPPER}" <<EOF
#!/usr/bin/env bash
set -euo pipefail
exec "${ISABELLE_HOME}/bin/isabelle" "\$@"
EOF
chmod +x "${WRAPPER}"
ln -sf "${WRAPPER}" "${PREFIX_BIN}/isabelle"

log "Isabelle installed at ${INSTALL_ROOT}"
log "Wrapper: ${WRAPPER}"
