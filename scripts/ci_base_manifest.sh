#!/usr/bin/env bash
# Build BASE and save its compiled manifest as .lake/gate/<BASE>.json, which
# scripts/gate.sh needs for the proof-only/interface classification.
#
#   scripts/ci_base_manifest.sh BASE
#
# Checks BASE out in this working tree, runs `lake build` and ExtractManifest (BASE's
# own copy, as the local gate does when it gates BASE), and checks the original HEAD out
# again. Lake rebuilds by content hashes, so the following `lake build` of HEAD rebuilds
# only the modules the change touches: this costs one incremental build instead of the
# second full build a separate worktree would need.
# Never fails the job: if BASE does not build, or the pins differ between BASE and HEAD,
# no manifest is written and gate.sh reports the change as unclassified (interface).
set -euo pipefail

main() {
  cd "$(dirname "$0")/.."
  local base head out
  base=$(git rev-parse --verify "$1^{commit}")
  head=$(git rev-parse --verify HEAD)
  out=".lake/gate/$base.json"
  mkdir -p .lake/gate
  if [ -f "$out" ]; then
    echo "Base manifest $out already present."
    return 0
  fi
  if ! git diff --quiet "$base" HEAD -- lean-toolchain lake-manifest.json lakefile.toml; then
    echo "NOTICE: the pins differ between base and head; base manifest not built."
    return 0
  fi
  if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    echo "NOTICE: working tree not clean; base manifest not built."
    return 0
  fi
  git -c advice.detachedHead=false checkout --quiet --detach "$base"
  # Restore HEAD however this function exits.
  trap 'git -c advice.detachedHead=false checkout --quiet --detach '"$head" EXIT
  if lake build && lake env lean --run scripts/ExtractManifest.lean > "$out.tmp"; then
    mv "$out.tmp" "$out"
    echo "Saved base manifest $out."
  else
    rm -f "$out.tmp"
    echo "NOTICE: base $base did not build or extract; classification will be skipped."
  fi
}

# The whole function is parsed before the checkout replaces this file on disk.
main "$@"; exit
