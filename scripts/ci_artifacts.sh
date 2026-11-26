#!/usr/bin/env bash
# Collect the CI artifacts into .lake/ci-artifacts/ after scripts/gate.sh has written
# .lake/manifest-raw.json:
#   manifest-raw.json   the compiled manifest (always);
#   manifest.json, definitions.json   the assertion manifest and definitions index, if
#                       scripts/build_manifest.py exists;
#   FRONTIER.md         the frontier, if scripts/frontier.py exists as well.
# Scripts that are not on the branch yet are skipped; a script that exists and fails
# fails the step.
set -euo pipefail

main() {
  cd "$(dirname "$0")/.."
  local out=.lake/ci-artifacts
  rm -rf "$out"
  mkdir -p "$out"
  cp .lake/manifest-raw.json "$out/manifest-raw.json"
  if [ -f scripts/build_manifest.py ]; then
    python3 scripts/build_manifest.py .lake/manifest-raw.json --output "$out/manifest.json" \
      --definitions-output "$out/definitions.json"
    if [ -f scripts/frontier.py ]; then
      python3 scripts/frontier.py "$out/manifest.json" --output "$out/FRONTIER.md"
    fi
  else
    echo "scripts/build_manifest.py not present: manifest.json, definitions.json and FRONTIER.md skipped."
  fi
  ls -l "$out"
}

main "$@"
