#!/usr/bin/env bash
# Run every Python test script under scripts/ (scripts/test_*.py) and the shell tests
# of the CI helpers (scripts/ci_test_*.sh). Exit non-zero if any fails.
# scripts/test_manifest.py is skipped: it needs `lake` and the built packages, so the
# gate job of .github/workflows/ci.yml runs it after the gate. Nothing here needs Lean.
set -uo pipefail

main() {
  cd "$(dirname "$0")/.."
  local t failed=0 ran=0
  for t in scripts/test_*.py scripts/ci_test_*.sh; do
    [ -f "$t" ] || continue
    [ "$t" == scripts/test_manifest.py ] && { echo "== $t skipped (needs lake; run by the gate job)"; continue; }
    echo "== $t"
    ran=$((ran + 1))
    case "$t" in
      *.py) python3 "$t" || failed=1 ;;
      *.sh) bash "$t" || failed=1 ;;
    esac
  done
  echo "Ran $ran test script(s)."
  [ "$ran" -gt 0 ] || { echo "No test scripts found." >&2; return 1; }
  return "$failed"
}

main "$@"
