#!/usr/bin/env bash
# The local gate of D-34, run by LEAD on the merged tree before the integration branch
# moves. Usage, from any directory:
#
#   scripts/gate.sh [BASE]        BASE: the integration tip the change is merged onto
#
# Steps: forbidden-construct scan, before any of the library is elaborated; full build
# with warnings as errors; axiom audit of every constant under PercLib; import closure;
# forbidden-construct scan again; unit tests of the proof-only classifier;
# manifest extraction (saved as .lake/gate/<HEAD>.json for later comparisons); the D-35
# checks (tagged statements, headers of new files); and, if
# BASE is given and its saved extraction exists, the proof-only/interface
# classification. Exit 0 only if every check passes. An interface classification is
# reported (exit 0 with a notice) because it needs an auditor, not a failure.
# The kernel replay (scripts/kernel_replay.sh) is separate: it runs before milestone
# pushes and must not run alongside a build (it needs about 4 GB per batch).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
head=$(git rev-parse HEAD)
dirty=$(git status --porcelain --untracked-files=no -- PercLib PercLib.lean | head -1)
echo "== gate on $head${dirty:+ (with uncommitted changes)}"
python3 scripts/check_forbidden.py PercLib
lake build --wfail
lake env lean --run scripts/AxiomAudit.lean
python3 scripts/check_import_closure.py PercLib
python3 scripts/check_forbidden.py PercLib
python3 scripts/test_proof_pr.py
mkdir -p .lake/gate
lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json
python3 scripts/check_d35.py .lake/manifest-raw.json
[ -z "$dirty" ] && cp .lake/manifest-raw.json ".lake/gate/$head.json"
if [ $# -ge 1 ]; then
  base=$(git rev-parse "$1")
  if [ -f ".lake/gate/$base.json" ]; then
    set +e
    python3 scripts/check_proof_pr.py --base "$base" --base-raw ".lake/gate/$base.json"
    rc=$?
    set -e
    [ $rc -eq 0 ] || [ $rc -eq 3 ] || exit $rc
    [ $rc -eq 3 ] && echo "NOTICE: interface change; an auditor must approve before merge."
  else
    echo "NOTICE: no saved extraction for base $base; classification skipped (treat as interface)."
  fi
fi
echo "== gate passed on $head${dirty:+ (with uncommitted changes)}"
