#!/usr/bin/env bash
# Kernel replay of every library module (D-29), run by LEAD after `lake build`.
#
#   scripts/kernel_replay.sh [BATCH]      (default BATCH: 12 modules per process)
#
# Replays each module of PercLib through the independent checker shipped with the
# pinned toolchain (`leanchecker`). `leanchecker PercLib` replays all 250 modules in one
# process and needs more than 15 GB, so modules are replayed in sequential batches.
# Exits non-zero on the first module the checker rejects.
set -euo pipefail
cd "$(dirname "$0")/.."
batch="${1:-12}"
mapfile -t modules < <(find PercLib -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | sort)
total=${#modules[@]}
for ((i = 0; i < total; i += batch)); do
  chunk=("${modules[@]:i:batch}")
  # A module name is matched as a prefix, so a parent module also replays its children;
  # the overlap is small. The root PercLib.lean only imports and is not replayed alone.
  lake env leanchecker "${chunk[@]}"
  echo "replayed $((i + ${#chunk[@]}))/$total"
done
echo "Kernel replay passed: $total modules."
