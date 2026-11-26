# Status

Handoff for the maintainer (LEAD role of D-34). Updated 26 November 2026, ~17:35 UTC, end of **paced cycle 6** (ruling 25).
Older history: [STATUS_LOG.md](STATUS_LOG.md) (do not read by default; cycle 1 details are at its end).
A maintainer with no memory resumes from this file and `/home/user/reports/ACTIVE.md` (ruling 25: 40 calls per round;
order: collaborators' pull requests and fork branches, then `main`, then the task board, then our own work).

## Tip and gate

- Branch `claude/zen-lovelace-rvlcw2`. **Last gated commit `2ac793f`** (cycle 6, two batches, both `== gate passed`):
  `integrate.sh f23c8a4 work/p-c-TVM9 work/p-d-MTYL-fix` dropped TVM9 (check_d35 FAIL (iv): header text `Λ_{L-1}` read as label
  `L-1`, a scanner false positive) and passed on `41d633b` (MTYL-fix = `44b697a` + `c24cdd6`, the audit r20-b C.1 exact edits);
  then `integrate.sh 41d633b work/p-c-TVM9-fix` (`fbd75fa` + `e986fd6`, spacing `Λ_{L - 1}` in the header) passed on `2ac793f`.
  Logs `/home/user/reports/integrate-cycle6.log`, `integrate-cycle6b.log`. Includes `f23c8a4` (`.github/automerge-authors`, ruling 28).
  On top: FRONTIER regenerated at `2ac793f` + this STATUS commit (docs).
- **`main` = `5eea93e` still. PR #28 OPEN** (head `91e3002` = gated `2ac793f` + docs); merge refused: required CI check `gate` in progress (>10 min). Next round: merge #28 with sha `91e3002` FIRST, then push the local STATUS commit on top. Before: `5eea93e` (#27, cycle 5, head `8f875be`); `026af1c` (#26); #25 `be36e68`, #24 `c1f1a95`.
  Integration PR open+merge through the API works.
- Cycle 3 batch: task-board restock `714fb71` (lane B, 8 tasks) + our `227d7c6` holding `exploration-terminates-at-cluster` (7WHX)
  out: possible overlap with the BFS exploration in Yujin's #15/#16 (`Bond/Exploration/BFS/Cluster.lean`); file kept in
  `714fb71`. Re-add only if the overlap check clears it. `check_tasks.py` clean.
- Cycle 2 batches:
  - `scripts/integrate.sh ded7bc4 pr/11 pr/12` -> **`d311edc`**, gate passed (log `/home/user/reports/integrate-cycle2.log`). PR #24.
  - `65f027f`: the five exact docstring edits of `audit-c1-planar` applied verbatim (`scripts/apply_exact_edits.py`); changed
    modules built `--wfail`. `80a735b`: 7 proved tasks moved to `tasks/done/`, FRONTIER regenerated. Gate on `80a735b` passed
    (base extract missing, so "treat as interface" NOTICE; content is verbatim audit edits + docs, no re-audit, ruling 10). PR #25.
- **Kernel replay:** the run on `28c8877` is dead at 180/538 (`/home/user/wt/kreplay-28c8877`). Last passed: `a747905`.
  Restart niced when a cycle has room (`nice -n 15 scripts/kernel_replay.sh 2` in a fresh worktree of the tip); remove the old one.
- **Actions (cycle 5):** CI on the integration branch at `b585a3a` success. Automerge on `main` skipped (normal). No failing workflow.

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
| #10 | yujinhkim `work/yujin-cutoff-moment-prereqs` @ `80ee07a` | **merged** (Tom, `97b39e5`) | none |
| #11 | TejasO2 `work/TejasO2-planar-defs` @ `e3f955b` | **merged** via #24; audit A APPROVE WITH CHANGES; fix `65f027f` in #25; commented | none |
| #12 | TejasO2 `work/TejasO2-planar-arm-defs` @ `26bc850` | **merged** via #24; audit B APPROVE WITH CHANGES; fix in #25; commented (offered definitional `ArmsDisjoint` fix as his PR) | none |
| #13-#23 | yujinhkim stack (ruling 24), opened by us in cycle 1, commented | not reviewed; tips unchanged this cycle | audit `060-audit-c2-yujin-defs` queued (#13, #15, #17) |
| #2 | tomhutchcroft `work/lace-foundations` @ `ed1497c` (moved from `630d985`, 26 Nov 16:33; 8 commits, 17 files, +2.6k, new definitions) | commented cycle 6 (seen; needs D-35 definition audit; queued after the Yujin stack unless Tom merges it himself) | Codex's area; audit brief after `060`/`060b` |

Cycle 6 (check 17:10): no new comments since 14:00; only #2 moved; all 11 stack tips and `80ee07a` unchanged; no new PRs
(open: #2, #13-#23); no open PR from `TejasO2`. Yujin stack (base `45309ab`, bottom to top; D = definitions, needs audit; P = proof-only,
merges on the gate after its base): #13 `exploration-envelope` `aa1cf85` D -> #14 `exploration-proofs` `9e7382d` P -> #15
`bfs-definitions` `45926a3` D -> #16 `bfs-core-proofs` `20fb6e9` P -> #17 `bfs-revelation-definitions` `2bde2d8` D -> #18
`bfs-revelation-proofs` `e9d938c` P -> #19 `bfs-limit-proofs` `302759e` P -> #20 `generation-definitions` `8acc3a8` D (9) -> #21
`generation-proofs` `cd5ff5c` P -> #22 `bfs-moment-definitions` `cc6eb18` D (1; one line mentions sorry/axiom/admit) -> #23
`bfs-high-temperature-proofs` `bf03542` D (~37k lines, 35 defs, long-range `Defs.lean` files; 7 lines mention sorry/axiom/admit;
asked him to confirm). **When `060` approves: integrate #13..#19 in stack order in one batch** (#14, #16, #18, #19 are proof-only),
apply exact edits in a `-fix` commit, comment on each PR. Then audit #20 + #22.

**Fork tips seen (ruling 24):** `lrp-I41-mt-updated` `e6cf6fe` (merged, #9); `work/yujin-cutoff-moment-prereqs` `80ee07a` (merged,
#10); the eleven stack tips above (unchanged at 14:00, cycle 5). No fork of `TejasO2` is watched (he opens pull requests directly).

## Progress (D-35 measure)

Manifest regenerated at `2ac793f`: **423 proved of 1,403** (was 417 at `d311edc`).
Cycle 6 report: pull requests handled 1 (#2 commented); merged to `main`: nothing yet (PR #28 open, waiting on CI `gate`; local gate `2ac793f` passed);
assertions proved and merged: 6 tags (TVM9, 0RX3, MTYL, 8WO7, OVG9, MIFH; audit r20-b); agents started by me: 0; briefs queued:
`060b-audit-c3-yujin-defs` (#20 + #22), `060c-audit-r21-a` (8 tags: W8PB, J1LW, IZAO, 87W3, RL1L, HATE, L0TE, RDF0).
Cycle 5 report: pull requests handled 0 (none new or updated); merged to `main`: `5eea93e` (PR #27, task board, gate `8f875be`);
assertions proved: 4 new tags on two prover branches, unmerged, need audit (HATE/L0TE/RDF0 on `work/p-c-HATE` @ `3be8e67`; FZQQ on
`work/p-d-FZQQ` @ `d9629d3`); agents started by me: 0; no new brief (`050a`, `060` still unclaimed).
Cycle 4 report: pull requests handled 0 (none new or updated; #13-#23 still await `060`); merged to `main`: nothing (no audited
work ready; no gate run); assertions proved: 1 new on a prover branch, unmerged (RL1L, `work/p-b-RL1L` @ `00c7eee`, needs audit);
agents started by me: 0; no new brief (lane B already has two unclaimed briefs, `050a` and `060`).
Cycles 2-3: see STATUS_LOG.md / git history of this file.
Lane B finished since cycle 1: `audit-c1-planar` (report `/home/user/reports/audit-c1-planar.md`).

## Finished, not merged

- `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (0MK8): approved, fails the gate on `local macro`
  (`PercLib/Combinatorics/NonbacktrackingRecurrence.lean` lines 98, 379). Needs fix branch (inline the notations, statements unchanged).
- Briefed in `060c-audit-r21-a` (cycle 6; requests moved to `audit-requests/done/`): W8PB `f030931`, J1LW `772a62c`,
  IZAO/87W3 `a2b00b4`, RL1L `00c7eee`, HATE/L0TE/RDF0 `3be8e67`.
- Not yet briefed (requests in `audit-requests/`): FZQQ `work/p-d-FZQQ` @ `d9629d3`; 27T8 `work/p-a-27T8` @ `e55ffd2`
  (`Models/Tags/HierarchicalMaximumScale.lean`); XXQK `work/p-b-XXQK` @ `1a17e3a` (`Probability/Tags/GaltonWatsonThinning.lean`).
- `work/p-b-Z4JP` @ `6d15a35` (Z4JP, WSKG): audit r20-b A APPROVE WITH CHANGES, change 1 blocking and needs judgement (move
  `permuteHilbertBasis` + API to new `PercLib/Analysis/PermuteHilbertBasis/Defs.lean`); fix brief not yet written. TVM9/MTYL merged cycle 6.

## In flight / claims

- Lane B: `050a` done (report `audit-r20-b.md`, 14:38). Queued unclaimed: `060-audit-c2-yujin-defs` (#13/#15/#17),
  `060b-audit-c3-yujin-defs` (#20 + #22), `060c-audit-r21-a` (8 of our tags).
- Task board (cycle 5, `8f875be`): of the 7 non-lrp claimed tasks, 6 are `proved` in the manifest (R3I9, D106, UNJ6, HQ6X, GGH2, YPNG)
  and moved to `done/`; `countable-closed-product` (QH7Q, unformalised, no branch activity) released to `open/`. `claimed/` now holds
  only the three held lrp ports. `check_tasks.py` clean, 16 open. `work/p-a-YXL0` = `62815b5` (prover slot a, no commits yet).
- Launcher `tag-*` claims: self-directed provers (PROVER-CHARTER).

## Queue (`/home/user/reports/queue/`)

Next lane-B briefs, one per cycle, after `060`, `060b`, `060c`: (1) #23 audit in parts of at most 8 definitions' worth (ruling 26);
(2) batched audit FZQQ + 27T8 + XXQK; (3) Z4JP move fix (r20-b A.1, A.2); (4) 0MK8 macro fix; (5) PR #2 definition audit;
(6) ruling 27 wiki briefs (STYLE approval, banner, errata disclaimer, licences, "Original results"); (7) restock, planar map,
check_d35 label regex (`[A-Z]{1,3}-\d+` matches math such as `L-1`), integrate.sh culprit parsing.
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
