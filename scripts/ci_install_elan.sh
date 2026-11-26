#!/usr/bin/env bash
# Install elan (the Lean toolchain manager) in CI from a pinned release, verify the
# installer binary against a pinned SHA-256, then install the toolchain named in
# `lean-toolchain`. Used by .github/workflows/ci.yml; nothing here needs a token.
#
#   scripts/ci_install_elan.sh
#
# To move to another elan release: download the release tarball named below, extract
# `elan-init`, and replace ELAN_VERSION and ELAN_INIT_SHA256 with the new version and
# `sha256sum elan-init`. A mismatch stops the job; it never falls back to an unverified
# download.
# ELAN_TARBALL, if set, names an already downloaded tarball (used by local tests only).
set -euo pipefail

ELAN_VERSION=v4.4.0
ELAN_URL="https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz"
ELAN_INIT_SHA256=54238e7fc23ede3da0d3705830b1c81c86d1e6e3e4886395e2f9f16375ad0d9b

main() {
  cd "$(dirname "$0")/.."
  local tmp tarball
  tmp=$(mktemp -d)
  tarball="${ELAN_TARBALL:-}"
  if [ -z "$tarball" ]; then
    tarball="$tmp/elan.tar.gz"
    curl --proto '=https' --tlsv1.2 -sSfL --retry 3 -o "$tarball" "$ELAN_URL"
  fi
  mkdir "$tmp/x"
  tar -xzf "$tarball" -C "$tmp/x" elan-init
  if ! echo "$ELAN_INIT_SHA256  $tmp/x/elan-init" | sha256sum --check --status; then
    echo "elan-init from $ELAN_URL does not match the pinned SHA-256 $ELAN_INIT_SHA256." >&2
    echo "Got: $(sha256sum "$tmp/x/elan-init" | cut -d' ' -f1). Update the pin deliberately." >&2
    exit 1
  fi
  chmod +x "$tmp/x/elan-init"
  "$tmp/x/elan-init" -y --no-modify-path --default-toolchain none
  rm -rf "$tmp"
  export PATH="$HOME/.elan/bin:$PATH"
  if [ -n "${GITHUB_PATH:-}" ]; then
    echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
  fi
  elan toolchain install "$(tr -d '[:space:]' < lean-toolchain)"
  elan --version
}

main "$@"
