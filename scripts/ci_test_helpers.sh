#!/usr/bin/env bash
# Tests of the CI helpers ci_base.sh, ci_classify.sh and ci_base_manifest.sh on a
# throwaway git repository, with a stub `lake` (no Lean needed), and a test that
# ci_script_tests.sh passes on a PATH without `lake` (as in the `scripts` CI job). Run by
# scripts/ci_script_tests.sh; CI_TEST_HELPERS_NESTED marks the nested run of that last
# test, which skips it so that it does not recurse.
set -euo pipefail

src="$(cd "$(dirname "$0")" && pwd)"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fails=0

check() { # NAME EXPECTED ACTUAL
  if [ "$2" == "$3" ]; then echo "ok   $1"; else echo "FAIL $1: expected '$2', got '$3'"; fails=1; fi
}

# --- ci_script_tests.sh without lake (before the stub lake below joins PATH)
if [ -z "${CI_TEST_HELPERS_NESTED:-}" ]; then
  nolake=""
  IFS=: read -ra dirs <<< "$PATH"
  for d in "${dirs[@]}"; do
    [ -n "$d" ] && [ ! -e "$d/lake" ] && nolake="${nolake:+$nolake:}$d"
  done
  check "script tests: PATH has no lake" "" "$(PATH="$nolake" command -v lake || true)"
  set +e
  PATH="$nolake" CI_TEST_HELPERS_NESTED=1 bash "$src/ci_script_tests.sh" > "$tmp/script-tests.log" 2>&1
  rc=$?
  set -e
  check "script tests pass without lake" 0 "$rc"
  [ "$rc" -eq 0 ] || tail -20 "$tmp/script-tests.log"
  check "script tests skip test_manifest.py" 1 \
    "$(grep -c '^== scripts/test_manifest.py skipped' "$tmp/script-tests.log" || true)"
fi

repo="$tmp/repo"
mkdir -p "$repo/scripts" "$repo/PercLib/Area"
cd "$repo"
git init -q -b main
g() { git -c user.name=ci -c user.email=ci@example.invalid "$@"; }
cp "$src"/ci_base.sh "$src"/ci_classify.sh "$src"/ci_base_manifest.sh scripts/
echo '.lake/' > .gitignore
echo 'leanprover/lean4:v4.35.0' > lean-toolchain
echo '{}' > lake-manifest.json
echo 'name = "x"' > lakefile.toml
echo 'theorem a : True := trivial' > PercLib/Area/A.lean
echo 'def d := 1' > PercLib/Area/Defs.lean
echo 'import PercLib.Area.A' > PercLib.lean
echo 'v1' > scripts/ExtractManifest.lean
g add -A && g commit -qm base
base=$(git rev-parse HEAD)

proof_log="$tmp/proof.log"; echo 'PROOF-ONLY change against abc: 1 Lean file(s)' > "$proof_log"
iface_log="$tmp/iface.log"; printf 'INTERFACE change against abc: x\nNOTICE: interface change\n' > "$iface_log"

# --- ci_classify.sh
echo 'theorem b : True := trivial' >> PercLib/Area/A.lean
g commit -qam proof
check "classify proof-only" proof-only "$(scripts/ci_classify.sh "$base" "$proof_log")"
check "classify classifier says interface" interface "$(scripts/ci_classify.sh "$base" "$iface_log")"
check "classify no base" interface "$(scripts/ci_classify.sh "" "$proof_log")"
check "classify no log" interface "$(scripts/ci_classify.sh "$base" "$tmp/missing.log")"
echo 'import PercLib.Area.B' >> PercLib.lean; echo 'theorem c : True := trivial' > PercLib/Area/B.lean
g add -A && g commit -qm root
check "classify new file and root import" proof-only "$(scripts/ci_classify.sh "$base" "$proof_log")"
for f in PercLib/Area/Defs.lean scripts/gate.sh .github/workflows/ci.yml lake-manifest.json \
         tasks/open/x.md docs/STATUS.md PercLib/Area/Basic.lean README.md; do
  g checkout -q -b "t-$RANDOM" HEAD
  mkdir -p "$(dirname "$f")"; echo '-- change' >> "$f"
  g add -A && g commit -qm "touch $f"
  check "classify touching $f" interface "$(scripts/ci_classify.sh "$base" "$proof_log")"
  g checkout -q main
done
g checkout -q -b "t-del" HEAD; g rm -q PercLib/Area/Defs.lean; g commit -qm del
check "classify deleting Defs.lean" interface "$(scripts/ci_classify.sh "$base" "$proof_log")"
g checkout -q main

# --- ci_base.sh
head=$(git rev-parse HEAD)
parent=$(git rev-parse HEAD^)
check "base pull_request: merge base" "$base" "$(EVENT=pull_request TARGET_SHA="$base" scripts/ci_base.sh)"
g checkout -q -b side "$base"; echo x > side.txt; g add -A; g commit -qm side; side=$(git rev-parse HEAD)
g checkout -q main
check "base pull_request: diverged target" "$base" "$(EVENT=pull_request TARGET_SHA="$side" scripts/ci_base.sh)"
check "base push: before" "$base" "$(EVENT=push BEFORE_SHA="$base" scripts/ci_base.sh)"
check "base push: zeros (new ref)" "$parent" "$(EVENT=push BEFORE_SHA=0000000000000000000000000000000000000000 scripts/ci_base.sh)"
check "base push: not an ancestor (force push)" "$parent" "$(EVENT=push BEFORE_SHA="$side" scripts/ci_base.sh)"
check "base push: unknown commit" "$parent" "$(EVENT=push BEFORE_SHA=1111111111111111111111111111111111111111 scripts/ci_base.sh)"
check "base push: junk" "$parent" "$(EVENT=push BEFORE_SHA='$(touch pwned)' scripts/ci_base.sh)"
check "base push: junk did not run" "no" "$([ -e pwned ] && echo yes || echo no)"
g checkout -q --orphan root-only; g commit -qm orphan --allow-empty
check "base push: root commit, no parent" "" "$(EVENT=push BEFORE_SHA=0000000000000000000000000000000000000000 scripts/ci_base.sh)"
g checkout -q -f main
set +e
EVENT=pull_request TARGET_SHA='main; true' scripts/ci_base.sh >/dev/null 2>&1; rc=$?
set -e
check "base pull_request: rejects non-sha" 2 "$rc"

# --- ci_base_manifest.sh, with a stub lake that records what it built
mkdir -p "$tmp/bin"
cat > "$tmp/bin/lake" <<'EOF'
#!/usr/bin/env bash
echo "$(git rev-parse HEAD) $*" >> "$LAKE_LOG"
if [ "$1" == env ]; then
  [ -n "${LAKE_FAIL_EXTRACT:-}" ] && exit 1
  echo "{\"extracted_by\": \"$(cat scripts/ExtractManifest.lean)\"}"
fi
exit 0
EOF
chmod +x "$tmp/bin/lake"
export PATH="$tmp/bin:$PATH" LAKE_LOG="$tmp/lake.log"
echo 'v2' > scripts/ExtractManifest.lean; g commit -qam 'extractor v2'; head=$(git rev-parse HEAD)
: > "$LAKE_LOG"
scripts/ci_base_manifest.sh "$base" > /dev/null
check "base manifest written" '{"extracted_by": "v1"}' "$(cat ".lake/gate/$base.json")"
check "base manifest built at base" "$base build" "$(head -1 "$LAKE_LOG")"
check "base manifest restores HEAD" "$head" "$(git rev-parse HEAD)"
check "base manifest leaves tree clean" "" "$(git status --porcelain)"
: > "$LAKE_LOG"
scripts/ci_base_manifest.sh "$base" > /dev/null
check "base manifest reused" "" "$(cat "$LAKE_LOG")"
rm -rf .lake/gate
LAKE_FAIL_EXTRACT=1 scripts/ci_base_manifest.sh "$base" > /dev/null
check "base manifest: failed extraction writes nothing" "no" \
  "$([ -e ".lake/gate/$base.json" ] || [ -e ".lake/gate/$base.json.tmp" ] && echo yes || echo no)"
check "base manifest: failed extraction restores HEAD" "$head" "$(git rev-parse HEAD)"
echo '{"changed": 1}' > lake-manifest.json; g commit -qam 'bump pins'
: > "$LAKE_LOG"
scripts/ci_base_manifest.sh "$base" > /dev/null
check "base manifest: pins differ, not built" "" "$(cat "$LAKE_LOG")"

if [ "$fails" -ne 0 ]; then echo "CI helper tests FAILED"; exit 1; fi
echo "CI helper tests passed."
