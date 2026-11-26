#!/usr/bin/env bash
# Print the base commit a CI run compares against, or nothing if there is none.
#
#   EVENT=pull_request TARGET_SHA=<base branch tip> scripts/ci_base.sh
#   EVENT=push BEFORE_SHA=<previous tip of the ref>  scripts/ci_base.sh
#
# Pull request: the merge base of HEAD (the pull request head) with the target branch
# tip, so that only the pull request's own changes are classified.
# Push: the previous tip of the pushed ref; for a new ref or a rewritten history (the
# previous tip is all zeros or is not in the clone), the first parent of HEAD.
# Values arrive through the environment, never interpolated into a command line.
set -euo pipefail

main() {
  cd "$(dirname "$0")/.."
  local candidate=""
  case "${EVENT:-}" in
    pull_request)
      [[ "${TARGET_SHA:-}" =~ ^[0-9a-f]{40}$ ]] || { echo "bad TARGET_SHA" >&2; exit 2; }
      git cat-file -e "${TARGET_SHA}^{commit}" 2>/dev/null \
        || git fetch --quiet --no-tags origin "$TARGET_SHA"
      candidate=$(git merge-base "$TARGET_SHA" HEAD)
      ;;
    push)
      if [[ "${BEFORE_SHA:-}" =~ ^[0-9a-f]{40}$ ]] && [[ ! "$BEFORE_SHA" =~ ^0+$ ]] \
          && git cat-file -e "${BEFORE_SHA}^{commit}" 2>/dev/null \
          && git merge-base --is-ancestor "$BEFORE_SHA" HEAD; then
        candidate="$BEFORE_SHA"
      else
        candidate=$(git rev-parse --verify --quiet 'HEAD^1^{commit}' || true)
      fi
      ;;
    *)
      echo "EVENT must be pull_request or push" >&2
      exit 2
      ;;
  esac
  [ -n "$candidate" ] && git rev-parse "$candidate"
  return 0
}

main "$@"
