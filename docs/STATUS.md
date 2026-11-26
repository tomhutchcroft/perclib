# Status

Handoff for the maintainer (LEAD role of D-34). Updated 26 November 2026, ~21:10 UTC, end of **paced cycle 7** (ruling 25).
Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default; cycle 1 details are at its end).
A maintainer with no memory resumes from this file and `/home/user/reports/ACTIVE.md` (ruling 25: 40 calls per round;
order: collaborators' pull requests and fork branches, then `main`, then the task board, then our own work).

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2`. **Last gated commit `71836f3`** (cycle 7, two batches, both `== gate passed`):
  `integrate.sh a35e438` + Yujin #13..#19 in stack order + `work/yujin-stack-c2-fix`: attempt 1 failed (longLine lint in
  `Envelope/Defs.lean` from audit edit 3), the fix branch was dropped (right culprit) and the stack passed on `0120f9a` (pushed);
  then `integrate.sh 0120f9a work/yujin-stack-c2-fix` (`f1f7c78` = the 9 exact edits of audit c2, verbatim; `4317c96` = rewrap of
  that docstring line, no text change) passed on `71836f3`. Logs `/home/user/reports/integrate-cycle7.log`, `integrate-cycle7b.log`.
  On top: FRONTIER regenerated at `71836f3` + this STATUS commit (docs). `a35e438` = merge of `origin/main` (#28 = `7d084c2`) back.
- **`main` = `7d084c2`** (#28, merged by ARCHITECT on green `gate`). **PR #29 OPEN** (head `a58c5e8` = gated `71836f3` + FRONTIER + STATUS). Next cycle FIRST: merge #29 with
  `{"merge_method":"merge","sha":"a58c5e8..."}` if CI `gate` is green on `a58c5e8` (ruling 29), then merge `origin/main` back, then push
  the local commit holding this line (kept unpushed so #29's CI is not restarted). Before: `5eea93e` (#27), `026af1c` (#26).
- Cycle 3: 7WHX task held out (possible overlap with Yujin's BFS exploration, now merged in #15/#16): re-check before re-adding.
- **Kernel replay:** the run on `28c8877` is dead at 180/538 (`/home/user/wt/kreplay-28c8877`). Last passed: `a747905`.
  Restart niced when a cycle has room (`nice -n 15 scripts/kernel_replay.sh 2` in a fresh worktree of the tip); remove the old one.
- **Actions (cycle 7):** CI on `main` `7d084c2` success; CI on `12b0b51` success; CI on #2 `bfb66cf` success; Automerge skipped (normal).
- integrate.sh refuses a branch cut from an unpushed commit: push a gated tip before integrating a fix branch cut from it.

Commands (`/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
export INTEGRATE_TRAILER="Co-Authored-By: ...
Claude-Session: ..."; export MSG_1="Merge work/<a> (...)" MSG_2=...
setsid nohup scripts/integrate.sh <tip> <sha-or-branch> ... > /home/user/reports/integrate-<id>.log 2>&1 < /dev/null &
timeout 590 bash -c 'until ! pgrep -f "scripts/integ[r]ate.sh" >/dev/null; do sleep 60; done'; tail -4 /home/user/reports/integrate-<id>.log
git fetch https://github.com/yujinhkim/perclib work/<b>:refs/remotes/yujin/work/<b>; git fetch origin pull/<n>/head:refs/remotes/pr/<n>
python3 scripts/apply_exact_edits.py EDITS.json --repo <worktree>
python3 scripts/build_manifest.py .lake/gate/<sha>.json --output .lake/manifest.json
python3 scripts/frontier.py .lake/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
python3 scripts/check_tasks.py      # "possibly done" warnings: check proof_status in the manifest, then git mv to tasks/done/
```

PR to `main`: POST `/pulls` (head `claude/zen-lovelace-rvlcw2`), then PUT `/pulls/<n>/merge` `{"merge_method":"merge","sha":<gated>}`.

## Collaborators (ruling 25.1)

| PR | Author / branch @ tip | State | Next |
|---|---|---|---|
| #10, #11, #12 | yujinhkim / TejasO2 | merged (#10 by Tom; #11, #12 via #24/#25) | none |
| #13-#19 | yujinhkim stack `aa1cf85`..`302759e` | **gated on the integration branch (cycle 7)**, audit c2 (`060`): #13 A APPROVE WITH CHANGES, #15 APPROVE, #17 APPROVE WITH CHANGES; exact edits applied (`f1f7c78`); close as merged when the PR to main merges | comment on #13-#19 when on `main`; follow-ups for him: A.4 `configWeight` bridge, C.1 `incidentEdges` refactor |
| #20 | yujinhkim `8acc3a8` | audit c3 A **REJECT (fixable)**: `RowSum` duplicates `rowSum`; **commented cycle 7** | wait for new tip |
| #21 | yujinhkim `cd5ff5c` (P) | waits on #20; commented | gate after #20 |
| #22 | yujinhkim `cc6eb18` | audit c3 B APPROVE WITH CHANGES (2 exact edits in the report; rename `N` is his); commented | merge after #20 + #21 |
| #23 | yujinhkim `bf03542` (35 defs, 70 files) | commented (asked to split); audit part 1 briefed (`060d`) | parts 2-4 (see Queue) |
| #2 | tomhutchcroft `bfb66cf` (moved 19:41; vs main 56 files +9.6k, Percolation + wiki, new defs; CI green) | **commented cycle 7** | D-35 audit after the Yujin stack, unless Tom merges |

Cycle 7 (check 20:40): no new PRs (open: #2, #13-#23); fork tips unchanged; no PR from `TejasO2`. Fork tips seen (ruling 24):
the eleven stack tips above, `80ee07a`, `e6cf6fe` (merged). No fork of `TejasO2` is watched (he opens pull requests directly).

## Progress (D-35 measure)

Manifest regenerated at `71836f3`: **423 proved of 1,403** (unchanged; the Yujin stack carries no tags).
Cycle 7 report: pull requests handled 12 (#13-#19 merged into the integration branch after audit + gate, PR #29 to main; #20, #21, #22, #23, #2
commented); merged to `main`: PR to main opened (head = STATUS commit over gated `71836f3`), merge next cycle on green `gate`;
`main` = `7d084c2` (#28, cycle 6 work) merged back; assertions proved: 0 new; agents started by me: 0; brief queued: `060d-audit-c4-yujin-23a`.
Cycle 6 report: pull requests handled 1 (#2 commented); merged to `main`: nothing yet (PR #28 open, waiting on CI `gate`; local gate `2ac793f` passed);
assertions proved and merged: 6 tags (TVM9, 0RX3, MTYL, 8WO7, OVG9, MIFH; audit r20-b); agents started by me: 0; briefs queued:
`060b-audit-c3-yujin-defs` (#20 + #22), `060c-audit-r21-a` (8 tags: W8PB, J1LW, IZAO, 87W3, RL1L, HATE, L0TE, RDF0).
Cycle 5 report: pull requests handled 0 (none new or updated); merged to `main`: `5eea93e` (PR #27, task board, gate `8f875be`);
assertions proved: 4 new tags on two prover branches, unmerged, need audit (HATE/L0TE/RDF0 on `work/p-c-HATE` @ `3be8e67`; FZQQ on
`work/p-d-FZQQ` @ `d9629d3`); agents started by me: 0; no new brief (`050a`, `060` still unclaimed).
Cycles 2-4: see STATUS_LOG.md / git history of this file.
Lane B finished since cycle 1: `audit-c2-yujin-defs`, `audit-c3-yujin-defs` (cycle 7 intake), `audit-c1-planar` (report `/home/user/reports/audit-c1-planar.md`).

## Finished, not merged

- `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (0MK8): approved, fails the gate on `local macro`
  (`PercLib/Combinatorics/NonbacktrackingRecurrence.lean` lines 98, 379). Needs fix branch (inline the notations, statements unchanged).
- Briefed in `060c-audit-r21-a` (cycle 6; requests moved to `audit-requests/done/`): W8PB `f030931`, J1LW `772a62c`,
  IZAO/87W3 `a2b00b4`, RL1L `00c7eee`, HATE/L0TE/RDF0 `3be8e67`.
- Not yet briefed (requests in `audit-requests/`): N9P5/Q4NA `work/p-b-N9P5` (new, cycle 7); FZQQ `work/p-d-FZQQ` @ `d9629d3`; 27T8 `work/p-a-27T8` @ `e55ffd2`
  (`Models/Tags/HierarchicalMaximumScale.lean`); XXQK `work/p-b-XXQK` @ `1a17e3a` (`Probability/Tags/GaltonWatsonThinning.lean`).
- `work/p-b-Z4JP` @ `6d15a35` (Z4JP, WSKG): audit r20-b A APPROVE WITH CHANGES, change 1 blocking and needs judgement (move
  `permuteHilbertBasis` + API to new `PercLib/Analysis/PermuteHilbertBasis/Defs.lean`); fix brief not yet written. TVM9/MTYL merged cycle 6.

## In flight / claims

- Lane B: `060`, `060b` done (reports `audit-c2-yujin-defs.md`, `audit-c3-yujin-defs.md`). Queued unclaimed: `060c-audit-r21-a`
  (8 of our tags), `060d-audit-c4-yujin-23a` (#23 part 1: `Bond/RestorationWindow` + `Bond/IndependentLayer/UnionChange`, 8 defs).
- Task board (cycle 5, `8f875be`): of the 7 non-lrp claimed tasks, 6 are `proved` in the manifest (R3I9, D106, UNJ6, HQ6X, GGH2, YPNG)
  and moved to `done/`; `countable-closed-product` (QH7Q, unformalised, no branch activity) released to `open/`. `claimed/` now holds
  only the three held lrp ports. `check_tasks.py` clean, 16 open. `work/p-a-YXL0` = `62815b5` (prover slot a, no commits yet).
- Launcher `tag-*` claims: self-directed provers (PROVER-CHARTER).

## Queue (`/home/user/reports/queue/`)

Next lane-B briefs, one per cycle (ruling 26 order): (1) #23 part 2 `Analysis/CapFlux` + `LongRange/Corner` + `CornerMoment` (8),
part 3 `CornerDerivative` (9), part 4 `CornerCoupling` + `DegreeCorner` (10, split if needed), all over `cc6eb18`;
(2) batched audit FZQQ + 27T8 + XXQK, then N9P5/Q4NA (`work/p-b-N9P5`, new request); (3) Z4JP move fix (r20-b A.1, A.2);
(4) 0MK8 macro fix; (5) PR #2 definition audit; (6) ruling 27 wiki briefs; (7) restock, planar map, `tasks/areas/long-range.md`
listing of the merged #13-#19, `docs/reviews/pr-{13,15,17,20,22}.md` from audits c2/c3, check_d35 label regex, integrate.sh culprit parsing.
Prover drain only (ruling 21): `420`-`423` in queue. Held: `HOLD-060/205/210/220/230/371` (ruling 18b).

## Held items

- Port packages (ruling 18b). MDB8 follow-up (move `ConvexOrder`/`UnifIntegrableAlong` to Defs). XMYD follow-up
  (`HierarchicalLayers.pairLevel` via `level`).

## For ARCHITECT

- Ruling 22.1 PR open+merge worked this cycle (#24, #25); the cycle-1 refusal item is closed.
- `/home/user/reports/hard/` is empty.
- Cycle 6: lane B finished `050a` (r20-b); check_d35 label regex gives false positives on maths in headers (TVM9).
- Cycle 5: still nothing claimed by lane B; six audit requests (9 tags) plus `050a` and the Yujin stack wait on audits, so nothing can reach `main`.
- Cycle 4: lane B claimed no brief in cycles 3 and 4 although `others` = 1 (`050a`, `060` unclaimed). Check the lane-B launcher;
  the Yujin audit (`060`) is what unblocks #13-#19, and collaborators wait on it.
- The Yujin stack is ~45k lines with ~78 definitions; at one lane-B worker per cycle its audits take many cycles. Consider raising
  `others` for a few cycles, or asking him for smaller branches (asked on #23).
- The task board is down to 8 open tasks after moving 7 proved ones to done; a restock needs the single wiki/tooling slot.
- integrate.sh culprit detection misses gate `FAIL <file>: forbidden tokens` and lake's "logged failures" list; trial merges
  still run on the main checkout.

## For Tom

- Merged by us under ruling 22, cycle 5: #27 (`5eea93e`: task board only, gate `8f875be`).
- Merged by us under ruling 22, cycle 3: #26 (`026af1c`: task-board restock, gate `97fee82`; 7WHX task held, see Tip).
- Merged by us under ruling 22: #24 (`c1f1a95`: Tejas's #11, #12 after a D-35 audit + gate; KGNK) and #25 (`be36e68`: audit
  docstring edits, task board, FRONTIER). Compare link: https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 —
  last gate `97fee82` (local, not CI); last gate + kernel replay: `a747905`.
- Pull requests #13-#23 were opened by us from Yujin's fork (ruling 24) so that each has a thread; their audit has started.
- Stray remote branch `work/fix-ci-cancelled-push-run-fix` (merged); delete when convenient. Issue #1 can be closed.

## Lessons

- After a stop of several days, read `git log origin/main` first: Tom may have merged work while STATUS was stale.
- integrate.sh may drop innocent branches: when the gate log names a forbidden-token or module failure in one branch,
  re-merge the others in a new batch.
- An approved audit does not mean the gate passes (forbidden tokens such as `macro`): audit briefs now ask auditors to flag them.
- The gate extract `.lake/gate/<sha>.json` feeds `build_manifest.py` directly: FRONTIER regeneration costs no extra build.
- Check `git status -sb` before committing STATUS, and `git ls-remote` after pushing. Push only the integration branch.
- Older lessons: STATUS at `2e65744` and STATUS_LOG.md "Lessons".
