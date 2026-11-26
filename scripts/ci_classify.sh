#!/usr/bin/env bash
# Print `proof-only` or `interface` for the change from BASE to HEAD.
#
#   scripts/ci_classify.sh BASE GATE_LOG      (BASE may be empty: no base, interface)
#
# proof-only needs both:
#  1. scripts/gate.sh, run with BASE, printed the classifier's PROOF-ONLY verdict
#     (scripts/check_proof_pr.py: Lean sources and compiled interfaces); and
#  2. every changed path is a Lean file under PercLib/ (or the root PercLib.lean) other
#     than Basic.lean and Defs.lean. check_proof_pr.py looks at Lean files only, so a
#     change to scripts/, .github/, the pins, docs/ or tasks/ is caught here (D-37 e).
# Anything else, including a missing base or a failed gate, is `interface`.
set -euo pipefail

main() {
  cd "$(dirname "$0")/.."
  local base="${1:-}" log="${2:-}" path
  if [ -z "$base" ] || [ -z "$log" ] || [ ! -f "$log" ]; then
    echo interface
    return 0
  fi
  if ! grep -q '^PROOF-ONLY change against ' "$log"; then
    echo interface
    return 0
  fi
  while IFS= read -r path; do
    case "$path" in
      PercLib.lean) ;;
      */Basic.lean | */Defs.lean) echo interface; return 0 ;;
      PercLib/*.lean) ;;
      *) echo interface; return 0 ;;
    esac
  done < <(git diff --name-only --no-renames "$base" HEAD)
  echo proof-only
}

main "$@"
