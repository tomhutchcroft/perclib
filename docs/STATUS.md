# Status

Handoff for the maintainer (LEAD role of D-34). Updated 26 November 2026, ~00:15 UTC 27 Nov, end of **paced cycle 8** (ruling 25).
Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default; cycle 1 details are at its end).
A maintainer with no memory resumes from this file and `/home/user/reports/ACTIVE.md` (ruling 25: 40 calls per round;
order: collaborators' pull requests and fork branches, then `main`, then the task board, then our own work).

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2`. **Last gated commit `2d366a2`** (cycle 8, one batch, attempt 1 `== gate passed`, nothing skipped):
  `integrate.sh e05542e` + the five audit-r21-a branches (all APPROVE): `work/p-b-W8PB` `f030931`, `work/p-c-J1LW` `772a62c`,
  `work/p-d-IZAO` `a2b00b4`, `work/p-b-RL1L` `00c7eee`, `work/p-c-HATE` `3be8e67` (+ import-closure commit). Log
  `/home/user/reports/integrate-cycle8.log`. On top: FRONTIER at `2d366a2`, task `galton-watson-dwass` -> done (RL1L proved), this STATUS.
  `e05542e` = merge of `origin/main` (#29 = `68f9945`, merged by ARCHITECT) back.
- **`main` = `68f9945`** (#29). **PR #31 OPEN** (head `58fb1fe` = gated `2d366a2` + FRONTIER/tasks/STATUS; `.github/automerge-authors` already on `main`). Next cycle FIRST: merge it with
  `{"merge_method":"merge","sha":"58fb1fea0701f8e4acb18ec4bb3c10b1df7fb503"}` if CI `gate` is green on it (ruling 29), then merge `origin/main`
  back, then push the local commit holding this line (kept unpushed so #31's CI is not restarted).
  Before: `7d084c2` (#28), `5eea93e` (#27).
- Cycle 3: 7WHX task held out (possible overlap with Yujin's BFS exploration, now merged in #15/#16): re-check before re-adding.
- **Kernel replay:** the run on `28c8877` is dead at 180/538 (`/home/user/wt/kreplay-28c8877`). Last passed: `a747905`.
  Restart niced when a cycle has room (`nice -n 15 scripts/kernel_replay.sh 2` in a fresh worktree of the tip); remove the old one.
- **Actions (cycle 8):** CI on #30 `61e8d84`: gate, scripts, wiki, kernel-replay all success. (Cycle 7: `main` `7d084c2` success.)
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
| #13-#19 | yujinhkim stack `aa1cf85`..`302759e` | **merged** (on `main` via #29, closed as merged) | follow-ups for him: A.4 `configWeight` bridge, C.1 `incidentEdges` refactor (not yet commented) |
| #20 | yujinhkim `8acc3a8` | audit c3 A **REJECT (fixable)**: `RowSum` duplicates `rowSum`; **commented cycle 7** | wait for new tip |
| #21 | yujinhkim `cd5ff5c` (P) | waits on #20; commented | gate after #20 |
| #22 | yujinhkim `cc6eb18` | audit c3 B APPROVE WITH CHANGES (2 exact edits in the report; rename `N` is his); commented | merge after #20 + #21 |
| #23 | yujinhkim `bf03542` (35 defs, 70 files) | audit part 1 (`audit-c4-yujin-23a.md`): 4 APPROVE, 4 WITH CHANGES (exact edits, ours to apply in a `-fix` commit at merge); **commented cycle 8**; part 2 briefed (`060f`) | parts 3-4 (see Queue) |
| #30 | TejasO2 `61e8d84` (planar separated arms, 6 defs, 1 new file; CI green) | **new cycle 8; commented** (audit queued) | D-35 audit `060e`, then gate + merge |
| #2 | tomhutchcroft `bfb66cf` (moved 19:41; vs main 56 files +9.6k, Percolation + wiki, new defs; CI green) | **commented cycle 7** | D-35 audit after the Yujin stack, unless Tom merges |

Cycle 8 (check 23:50): new PR #30 (TejasO2); open: #2, #20-#23, #30; fork tips unchanged (the stack tips above, `80ee07a`, `e6cf6fe` merged). No fork of `TejasO2` is watched (he opens pull requests directly).

## Progress (D-35 measure)

Manifest regenerated at `2d366a2`: **431 proved** (FRONTIER: 260 ready, 705 blocked, 7 without prerequisites).
Cycle 8 report: pull requests handled 2 (#30 first response, #23 part-1 verdict commented); merged to `main`: PR #31 for gated `2d366a2`
(8 tags: W8PB, J1LW, IZAO, 87W3, RL1L, HATE, L0TE, RDF0; audit r21-a) opened, merge next cycle on green `gate`; assertions proved: 8 merged
(+8, 423 -> 431); agents started by me: 0; briefs queued: `060e-audit-c5-planar-30`, `060f-audit-c6-yujin-23b`.
Cycle 7 report: pull requests handled 12 (#13-#19 merged into the integration branch after audit + gate, PR #29 to main; #20, #21, #22, #23, #2
commented); merged to `main`: PR to main opened (head = STATUS commit over gated `71836f3`), merge next cycle on green `gate`;
`main` = `7d084c2` (#28, cycle 6 work) merged back; assertions proved: 0 new; agents started by me: 0; brief queued: `060d-audit-c4-yujin-23a`.
Cycle 6 report: pull requests handled 1 (#2 commented); merged to `main`: nothing yet (PR #28 open, waiting on CI `gate`; local gate `2ac793f` passed);
assertions proved and merged: 6 tags (TVM9, 0RX3, MTYL, 8WO7, OVG9, MIFH; audit r20-b); agents started by me: 0; briefs queued:
`060b-audit-c3-yujin-defs` (#20 + #22), `060c-audit-r21-a` (8 tags: W8PB, J1LW, IZAO, 87W3, RL1L, HATE, L0TE, RDF0).
Cycles 2-5: see STATUS_LOG.md / git history of this file.
Lane B finished since cycle 1: `audit-c2-yujin-defs`, `audit-c3-yujin-defs` (cycle 7 intake), `audit-c1-planar` (report `/home/user/reports/audit-c1-planar.md`).

## Finished, not merged

- `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (0MK8): approved, fails the gate on `local macro`
  (`PercLib/Combinatorics/NonbacktrackingRecurrence.lean` lines 98, 379). Needs fix branch (inline the notations, statements unchanged).
- Not yet briefed (requests in `audit-requests/`): 25Z0 `p-a-25Z0`, 4OFD `p-d-4OFD` (new, cycle 8); N9P5/Q4NA `work/p-b-N9P5` (new, cycle 7); FZQQ `work/p-d-FZQQ` @ `d9629d3`; 27T8 `work/p-a-27T8` @ `e55ffd2`
  (`Models/Tags/HierarchicalMaximumScale.lean`); XXQK `work/p-b-XXQK` @ `1a17e3a` (`Probability/Tags/GaltonWatsonThinning.lean`).
- `work/p-b-Z4JP` @ `6d15a35` (Z4JP, WSKG): audit r20-b A APPROVE WITH CHANGES, change 1 blocking and needs judgement (move
  `permuteHilbertBasis` + API to new `PercLib/Analysis/PermuteHilbertBasis/Defs.lean`); fix brief not yet written. TVM9/MTYL merged cycle 6.

## In flight / claims

- Lane B: `060c` (r21-a, all APPROVE, merged cycle 8) and `060d` (#23 part 1) done. Queued unclaimed: `060e-audit-c5-planar-30`
  (#30), `060f-audit-c6-yujin-23b` (#23 part 2: `Analysis/CapFlux`, `LongRange/Corner`, `LongRange/CornerMoment`, 8 defs).
- Task board cycle 8: `galton-watson-dwass` -> done (RL1L proved); `check_tasks.py` clean, 15 open.
- Task board (cycle 5, `8f875be`): of the 7 non-lrp claimed tasks, 6 are `proved` in the manifest (R3I9, D106, UNJ6, HQ6X, GGH2, YPNG)
  and moved to `done/`; `countable-closed-product` (QH7Q, unformalised, no branch activity) released to `open/`. `claimed/` now holds
  only the three held lrp ports. `check_tasks.py` clean, 16 open. `work/p-a-YXL0` = `62815b5` (prover slot a, no commits yet).
- Launcher `tag-*` claims: self-directed provers (PROVER-CHARTER).

## Queue (`/home/user/reports/queue/`)

Next lane-B briefs (ruling 26 order): (1) #23 part 3 `CornerDerivative` (9), part 4 `CornerCoupling` + `DegreeCorner` (10, split if needed), all over `cc6eb18`;
(2) batched audit FZQQ + 27T8 + XXQK + N9P5/Q4NA + 25Z0 + 4OFD (up to 8 tags); (3) Z4JP move fix (r20-b A.1, A.2);
(4) 0MK8 macro fix; (5) PR #2 definition audit; (6) ruling 27 wiki briefs; (7) restock, planar map, `tasks/areas/long-range.md`
listing of the merged #13-#19, `docs/reviews/pr-{13,15,17,20,22}.md` from audits c2/c3, check_d35 label regex, integrate.sh culprit parsing.
Prover drain only (ruling 21): `420`-`423` in queue. Held: `HOLD-060/205/210/220/230/371` (ruling 18b).

## Held items

- Port packages (ruling 18b). MDB8 follow-up (move `ConvexOrder`/`UnifIntegrableAlong` to Defs). XMYD follow-up
  (`HierarchicalLayers.pairLevel` via `level`).

## For ARCHITECT

- Cycle 8: an immediate merge attempt on #31 (right after opening, CI pending) was refused by the session's permission layer
  (auto-mode classifier), not by GitHub; not retried (ruling 25.2). Ruling 29 merges it next cycle anyway; if that is refused too, it needs you.

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
