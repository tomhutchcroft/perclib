# Status log (history; nobody reads this by default, ruling 20e)

Round 7 handoff (the last long-form STATUS.md, verbatim, moved here in round 9):

## Status

Handoff file for the coordinator (the LEAD role of D-34). Last updated 21 November 2026, about 18:20 UTC, at the end of
coordinator round 7 of a new series (twenty-fifth coordinator overall; the previous handoff, round 6, is at `1af691c`;
older rounds are in `git log -p docs/STATUS.md`, the long per-round gate records up to round 3 in `git show
47b6ffa:docs/STATUS.md`). A coordinator with no memory resumes from this file, [COORDINATOR.md](COORDINATOR.md),
[COORDINATION.md](COORDINATION.md), [DECISIONS.md](DECISIONS.md) (D-34 to D-37) and `/home/user/reports/RULINGS.md`
(rulings 1-19; obey them). **Ruling 19 (new, ~18:19):** Tom approved the model article; roll the ruling-8 shape out in the critic's order, and hyperlink inline citations to a per-page References section (recorded in D-36; generator brief `008-wiki-citation-links` queued; then the model article `hierarchical-two-point` and the restructured articles are converted, and a catalogue-gap scout runs). **Ruling 18 (18:02; first acted on in round 7):** Tom's collaborator, author of the
outside LRP I formalisation that D-33 ports from, wants to merge with perclib. (a) scout `tasks/areas/long-range.md` +
`docs/reports/long-range-concordance.md`: `001-scout-long-range-map`, claimed; (b) **no new port packages until Tom
reports the agreement**: the unclaimed port briefs 205, 210, 220, 230 and the port salvage 371 were renamed `HOLD-…` with
a note (their public twins stay in `tasks/claimed/`); fill lanes with frontier, near-miss, hierarchical work; (c) port
credits: `002-docs-port-credits` (claimed) writes `docs/PORTED_FILES.md` and lists header gaps for a follow-up; (d) no
interface change to `Models/LongRange/**/Defs.lean`, `Analysis/ModelNorm`, `Probability/Dispersion/Defs.lean` until the
joint review (migration (e) is already announced as merged in `docs/INTERFACE_CHANGES.md`). Rulings 14 (Codex owns the
lace-expansion Lean area; each round `git ls-remote`, fetch outside heads, `git fetch origin main`) and 17 (check Actions
runs each round) stand. Container-local reports and briefs are copied for durability to `lrp/docs/reports/` at each
round's lrp commit (ruling 9i). No GitHub write tool exists (ruling 13a): Tom opens the pull requests.

### Integration tip and gate

- Branch `claude/zen-lovelace-rvlcw2` in both repositories. **Last gated commit `2023c28`** (pushed; extract
  `.lake/gate/2023c28….json` saved). On top of it, pushed: `4c846e9` (board mirror: three twins to `tasks/claimed/`;
  `docs/FRONTIER.md` at `2023c28`) and this STATUS commit. **Next gate: `scripts/gate.sh 2023c28`.**
- **Round 7 (18:09-18:20): one gated batch, passed, pushed.** Started 18:09 (predecessor's STATUS commit 18:08:37, tree
  clean and pushed; only a worker build and the replay running, each in its own worktree). Merged, in order:
  `work/fix-nm-tree-depth` (`8fb0e70`, GGH2 + UHVH, audit r2 APPROVE), `work/wiki-revise-regular-variation-r2`
  (`6ca5601`, critic r3 PASS), `work/fix-tooling-task-board-check` (`cd514dd`, `scripts/check_tasks.py`, re-audit
  APPROVE), `work/fix-ci-concurrency` (`169291b`, ruling 17; its audit arrived during the first gate run: (A) and (B)
  APPROVE, (C) one required fail-closed fix C1, so it merged under ruling 13c and the fix was queued; the gate was
  restarted once to include it, still one batch). Merged files byte-identical to the audited heads. Gate
  `scripts/gate.sh a747905` (log `/home/user/reports/gate-round7.log`): build `--wfail` OK (3,964 jobs), axiom audit
  6,789 constants only `propext`/`Classical.choice`/`Quot.sound`, import closure 371 modules, forbidden scan 371 files,
  script tests OK, "D-35 checks passed", "INTERFACE change against a7479055312b: …Models/Tags/TreeDepth.lean" (expected:
  audited GGH2/UHVH), "== gate passed on 2023c28…". Wiki `npm test` 107/107 on the merged tree;
  `python3 -I scripts/check_tasks.py` clean (now on the tip).
- **Kernel replay (ruling 13b).** Still running at `a747905` in `/home/user/wt/replay-a747905` (batch size 2, niced,
  `setsid`); log `/home/user/reports/replay-a747905.log`, 192/369 at 18:17. Next coordinator: `tail` the log; "Kernel
  replay passed" = pass at `a747905` (record it, `rm` the `.lake/packages` symlink, `git worktree remove`, update
  `READY-FOR-MAIN` and the "For Tom" line); a checker error names the module ("For ARCHITECT"); if `pgrep -f
  kernel_replay.sh` is empty with neither line: `dmesg | grep -i oom`, restart the same way. Last replay that passed:
  baseline `4c72765`. Round 7 is the second batch since the replay started; the next scheduled replay (every tenth batch)
  is due after round 15 unless this one fails.
- **GitHub (rulings 14c/d, 17).** `git ls-remote` at 18:10: `main` `ae4eb08` (unchanged, already in the tip);
  `refs/pull/2/head` = `work/lace-foundations` `630d985` (unchanged, reviewed: `docs/reviews/pr-2.md`);
  `work/hierarchical-two-point-paper` `be2b9df` (unchanged, reviewed). No new outside heads. Open issues/PRs (public
  API): #2 (PR, unchanged since 16:53), #1 (issue, README, fixed on `main`). **Actions at 18:10:** Pages on `main`
  `ae4eb08` **success** (first deploy; the site is https://tomhutchcroft.github.io/perclib/); Automerge on `main`
  skipped (no pull request); CI push on `main` `ae4eb08` still in progress (started 17:58); CI push runs on the
  integration branch for `6867e43`, `f7bb516`, `f268213`, `1af691c` in progress, the pull-request duplicates cancelled.
  The concurrency fix is merged as of `2023c28`, so pushes from now on cancel older integration runs. Next coordinator:
  record the CI conclusion on `main` `ae4eb08` and on the integration tip.

Commands (from `/home/user/perclib`, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
scripts/gate.sh <previous-gated-commit>  # build --wfail, AxiomAudit, closure, forbidden, tests, extract
                                         # (.lake/manifest-raw.json; saved .lake/gate/<sha>.json),
                                         # check_d35, proof-only/interface classification
scripts/kernel_replay.sh 2               # leanchecker in batches of 2 (6 was OOM-killed); in its own worktree
python3 scripts/build_manifest.py .lake/manifest-raw.json --output /home/user/reports/manifest.json
python3 scripts/frontier.py /home/user/reports/manifest.json --proof-uses wiki/records --commit <sha> --output docs/FRONTIER.md
python3 -I scripts/check_tasks.py        # task-board checker (on the tip since round 7)
cd wiki && ln -s /home/user/lrp/wiki/node_modules node_modules && npm test; rm node_modules; rm -rf dist
```

Use the perclib `scripts/build_manifest.py` (as above). Run the gate in the background (`setsid nohup scripts/gate.sh …
> log 2>&1 < /dev/null &`) and wait with `until ! pgrep -f scripts/gate.sh; do sleep 10; done` (foreground `sleep` is
blocked). The base passed to `gate.sh` must have a saved extract in `.lake/gate/` (STATUS-, FRONTIER- or merge-of-main
commits have none: pass their gated parent). After `frontier.py` delete `scripts/__pycache__/frontier.*.pyc`. Older
worktrees still track `scripts/__pycache__/*.pyc`: before `git worktree remove` there, `git checkout --
scripts/__pycache__`.

### Progress (D-35 measure)

Round 7 (new series): **2 new assertions proved and merged (GGH2, UHVH); 2 tagged statements audited and merged (the
same); 6 more tagged statements audited APPROVE and waiting for the next batch (D106, HQ6X, NBY2, YPNG; 1EWX, HRS7).**
Manifest at `2023c28` (perclib script): **301 proved, 1 statement-only, 1,101 unformalised, of 1,403**.
`docs/FRONTIER.md` regenerated at `2023c28`.

Round 6: 1 proved (9YE6), 5 audited. Round 5: 5 proved and merged (J98J, W498, XLWI, YVJT, EZJ7), 4 audited. Round 4:
10 proved, 11 audited. Round 3: 7 proved, 7 audited. Round 2: 1 (KJWA). Round 1: 0 proved, 2 re-audited. Earlier
series: `git show 180d45f:docs/STATUS.md`.

### Merged in round 7 (new series)

- **Lean:** `fix-nm-tree-depth` (contains `nm-tree-depth`: GGH2, UHVH).
- **Wiki:** `wiki-revise-regular-variation-r2` (`regular-variation`; critic r3 PASS with seven optional items "For Tom").
- **Tooling/CI:** `fix-tooling-task-board-check` (contains `tooling-task-board-check`: `scripts/check_tasks.py` and
  tests), `fix-ci-concurrency` (`ci.yml` concurrency groups, `docs/CI_KNOWN_LIMITATIONS.md`).
- **Docs/board:** `4c846e9` (twins `window-correlation-chains`, `event-entropy-comparison`, `truncated-maximal-bound` in
  `tasks/claimed/`; FRONTIER). `/home/user/reports/READY-FOR-MAIN` rewritten (round-6 version kept as
  `READY-FOR-MAIN.round6`).
- Worktrees removed: fix-nm-tree-depth, nm-tree-depth, wiki-revise-regular-variation-r2, fix-tooling-task-board-check,
  tooling-task-board-check, fix-ci-concurrency.

### Task board (`tasks/`, ruling 9b)

**5 open, 21 claimed, 11 done on the tip**; `work/tasks-restock` (`8148d6f`, 15 new open tasks, the
`lace-expansion.md` name fixes, four shared-file notes) finished at 18:15; its audit `006-audit-tasks-restock` is queued.
On approval merge it (then 20 open). Its tags do not overlap the round-7 briefs (checked: none of UXBN, OB0A, 58HC,
HXNR, 4GBV; owned files disjoint). After it merges, the board needs the long-range area row in `tasks/README.md`
(once `scout-long-range-map` reports) and a note that the held port twins in `claimed/` wait on ruling 18b.

### Finished, not merged (each waits for the item named)

**Ready for the next batch (all approved; merge in this order, then `scripts/gate.sh 2023c28`, push):**
1. `work/nm-graph-certificates` (`208bfd4`; D106, HQ6X, NBY2, YPNG): `audit-nm-graph-certificates` **APPROVE** (4/4,
   binder tables; one non-blocking rule-6 nit).
2. `work/nm-small-intensity` (`6dab52e`; 1EWX, HRS7): `audit-nm-small-intensity` **APPROVE** (2/2). The author asks
   (for LEAD) to move `locallyLipschitzOn_chi` to `Bond/SusceptibilityDerivative.lean` and `connected_fromEdgeSet_pos`
   to `Models/HeavySecondMoment.lean` later: a small proof-only package when those files are free.

**Waiting for audits / fixes:**
- `work/wiki-revise-proof-sections-a-r3` (`3acea3f`): audit r3 APPROVE; waits for `007-critic-reread-proof-sections-a-r3`
  (third and last critic read; still unclaimed at 18:18). Merge when it passes, or with its residual list "For Tom".
- `work/nm-closed-products` (`161cb56`, UNJ6, R3I9 + closed-product iff): audit `005-audit-nm-closed-products` claimed.
- `work/fix-ci-c1` (`8a75eaa`, C1-C3 of `audit-fix-ci-concurrency`): scoped re-audit `000-audit-fix-ci-c1` claimed.
  Merge on approval (top priority, ruling 17).
- `work/docs-automerge-state` (`26416a0`): fix `006-fix-docs-automerge-state` queued (unclaimed), re-audit
  `HOLD-audit-fix-docs-automerge-state`. Merge the fix branch (it contains the original) on approval.
- `work/wiki-revise-proof-sections-c` (`fd33e50`, `critical-exponents`, `adaptive-three-point`): tag/proof audit
  `004-audit-wiki-revise-proof-sections-c` and critic re-read `005-critic-reread-proof-sections-c` (round 2) queued.
- `work/tasks-restock` (`8148d6f`): audit `006-audit-tasks-restock` queued.
- `scout-defs-2` interface packages: not yet briefed (first `chiCriticalIntensity`, 5LNL respelled; announce in
  `docs/INTERFACE_CHANGES.md` first, ruling 14e). Folds are migrations, one window at a time. None may touch the files
  frozen by ruling 18d.
- Lemma I.5.5 / 2KB9 / B5SL tag package: brief it (Lean `Tags/` only) once `wiki-revise-proof-sections-a-r3` merges.
- D-33 package 18 (`lrp-I31-I32`) and the held ports: wait for ruling 18b to lift.

### In flight (claims without a done marker at 18:18)

`audit-fix-ci-c1` (000), `audit-nm-closed-products` (005), `scout-long-range-map` (001), `docs-port-credits` (002); check
`claims/` against `done/` for later ones. Also running: the kernel replay at `a747905`. Worktrees kept:
nm-closed-products, nm-graph-certificates, nm-small-intensity, docs-automerge-state, fix-ci-c1,
wiki-revise-proof-sections-a-r3, wiki-revise-proof-sections-c, tasks-restock, replay-a747905, and the claimed packages'
worktrees.

### Migration windows

No window is open; all three D-35 migrations are done. The next interface changes come from `scout-defs-2` (each
announced in `docs/INTERFACE_CHANGES.md` first); a fold that renames shared names opens a new window under the usual
rule. Ruling 18d freezes the long-range definition files until the joint review.

### Queue (`/home/user/reports/queue/`)

A brief is startable when it has no `HOLD-` prefix and no `claims/<id>`; claimed briefs stay in the directory.
**Startable at 18:20 (17; 11 Lean proving briefs):** `004-audit-wiki-revise-proof-sections-c`,
`005-critic-reread-proof-sections-c`, `006-audit-tasks-restock`, `006-fix-docs-automerge-state`,
`007-critic-reread-proof-sections-a-r3`, `008-wiki-citation-links` (ruling 19 generator, tooling; owns `wiki/src/{render,build,citations}.mjs`, tests, `wiki/STYLE.md`), `160-connection-kernel-tags`, `161-monotone-coupling-tag`,
`170-hier-pointwise-ingredients`, `171-dedup-exponential-moments`, `200-nm-bond-core`, `240-nm-probability` (items 1-2),
`250-nm-window-correlation` (UXBN, OB0A; new), `251-nm-entropy-event` (58HC; new), `252-nm-truncated-maximal` (HXNR,
stretch 4GBV; new), `370-salvage-directional-decay`, `389-frontier-riccati-linear-error`. Lean owned files mutually
disjoint and disjoint from claimed work: new files each, plus `Bond/ConnectionKernel` 160, `Probability/Coupling/Monotone`
161, `Bond/IntensityScaling` 200, `Probability/{FKG,TotalVariation}` 240, `Bond/Tightness/Hyperscaling` 250,
`Probability/BernoulliDivergence` 251, `Probability/TruncatedMaximal` 252 (checked against the finished-unmerged branches
too: nm-graph-certificates, nm-closed-products and nm-small-intensity touch none of them).
**Held:** `HOLD-audit-nm-bond-core` (after 200), `HOLD-audit-nm-probability` (after 240),
`HOLD-audit-fix-docs-automerge-state` (after 006), `HOLD-audit-nm-window-correlation` (after 250),
`HOLD-audit-nm-entropy-event` (after 251), `HOLD-audit-nm-truncated-maximal` (after 252); **ruling 18b:**
`HOLD-205-lrp-volume-law`, `HOLD-210-lrp-I41-mt`, `HOLD-220-lrp-spatial-russo-a`, `HOLD-230-lrp-levy-measures`,
`HOLD-371-salvage-kernel-geometry` (release by renaming back once RULINGS.md lifts 18b). Audit releases: fill in the
head sha in the first parenthesis and drop `HOLD-`, giving a number.

Next packages to brief: the tooling audit of `wiki-citation-links` when it reports, then converting `hierarchical-two-point` to citation markup (after it merges) and a catalogue-gap scout (owns `wiki/src/content/catalog.json`; can run beside the generator); audits of each tagged prover package as it reports (160, 161, 370, 389 need fresh audit briefs;
200, 240, 250-252 have HOLD audits; 170, 171 are proof-only: merge on the gate); a header-fix package from
`docs-port-credits`' list (comment-only edits of files no live brief owns); the 7YNX tag package after 170 (hier-map H10
step 2); near-misses B2ZL (`Models/LongRange/PowerLaw.lean`: not a Defs file, but wait for 18b's agreement since it is
in the long-range area) and 32GP; the small move package from nm-small-intensity's report; the XB1U planar-topology proof
package (critic M-X3) and the article splits (X-S1/A-S1, deferred); restructuring the index and hubs (ruling 8).

### For ARCHITECT

- **Round 7 additions.** (1) **Ruling 18b applied to briefs released but unclaimed before it:** 205, 210, 220, 230
  (D-33 ports) and 371 (salvage of an unverified port from the same source) were held, since "queue no new port
  packages" was read as "start none not already claimed". 370 (salvage, own source) stays open. Overrule if you meant
  only briefs written after the ruling. (2) **CI fix merged on (A)/(B) approval with a fail-closed functional fix
  outstanding** (ruling 13c/15c reading): the C1 race can only turn an integration pull request's `kernel-replay` check
  red spuriously, never green; fix `8a75eaa` is under re-audit. (3) **One batch, restarted once:** the CI audit arrived
  while the batch's gate was running; I stopped that gate before its axiom audit, added the branch and re-ran it (one
  gate result for one batch). Two more approvals (six tagged statements) arrived after the gate and wait for round 8,
  as in rounds 4-6; the request for a second batch per round stands. (4) B2ZL (near miss in
  `Models/LongRange/PowerLaw.lean`) is not briefed until the long-range arrangement is known, to avoid editing the area
  the collaborator may take over; say if you want it queued now.

- **Round 6 additions.** (1) **One batch per round, third time.** The gate ran 17:59-18:08; within it eight done markers
  arrived (three approvals: GGH2/UHVH, a wiki revision, a critic PASS; two tagged prover packages; the ruling-17 CI fix;
  two audits with changes). All wait for round 7. Please allow a second gated batch per round; the lanes clearly outrun
  one. (2) **Kernel replay batch size reduced from 6 to 2** (your option (a) of round 4) after a third OOM kill at
  228/363; CI on `main` also runs the replay (option (c)); the next coordinator records whichever passes first. (3)
  **Coordinator decisions on the `proof-sections-c` critique:** the article moves the critic advised (WD31 and the
  critical $\mathbb Z^2$ material to its own article; XCYH/JM5A/R9NU to `planar-factorization`) are deferred to a later
  structural package; the reviser does the six must-change items of each article in place. Overrule if you want the
  moves first. (4) **`countable-closed-product` moved to `claimed/`** although 240 now excludes QH7Q: it duplicates the
  lemma 157 has just made public; it returns as a restatement task after 157 merges.

- **Round 5 additions.** (1) **One batch per round, again.** During this round's gate (17:36-17:52) the (e) migration
  finished and was approved, and four more approvals arrived (9YE6, two wiki revisions, a tooling audit with changes).
  All wait for round 6, and window (e) stays open one round longer than ruling 11g intends. I kept to one batch as the
  launcher says; please allow a second gated batch per round when an approved migration arrives during the first.
  (2) **W498 merge repair (coordinator's call):** the gate's D-35 check (i) failed because `hier-cor12`'s brief told
  the author not to tag the theorem proving the tagged Prop W498. I added the one line `@[tag "W498"]` (the J98J
  pattern; no statement changed) and queued a mechanical confirmation audit; W498 now counts as proved. Overrule if you
  want such repairs audited before the merge. (3) **Proving reopened under 11g** at the end of round 5 for every held
  brief disjoint from (e)'s six files, with (e) approved but unmerged; the five briefs that touch (e)'s files or names
  stay held until it merges.

- **Round 4 additions.** (1) **One batch per round versus ruling 15 ("stop waiting for one thing behind another").**
  This round's batch (11 branches, 13 min) closed at 17:19; within the next eight minutes eleven done markers arrived,
  among them the auto-merge audit (approve with one change) and its fix, four approvals of tagged packages and a wiki
  re-audit approval. Under the launcher's one-batch rule they wait for round 5, which is the queueing ruling 15 asks us
  to stop. I kept to one batch; please let the coordinator run a second gated batch when ruling-15 items or approvals
  arrive during the first gate. (2) **The kernel replay keeps dying.** Two runs were OOM-killed (`cfef666` at 66/338,
  `622c846` at 234/342; one `leanchecker` reached 10.7 GB RSS beside a gate and worker builds). No replay has passed since
  the baseline `4c72765`, so ruling 10(1)'s "after each batch that passed the gate and the kernel replay" cannot be met;
  Tom merged `b1db272` regardless. Options: (a) reduce the batch size of `kernel_replay.sh` from 6 to 2 and accept longer
  runs; (b) hold worker Lean builds for the replay's duration once per series; (c) rely on CI's `kernel-replay` job once
  `ci.yml` is on `main` (16 GB runner, nothing else running) and record its result. I recommend (c), with (a) locally as
  a fallback. (3) **Migration (d) kept no deprecated aliases** for its 11 renames (ruling 9h asks for them "where
  possible"); pull request #2 uses none of the old names. Overrule if you want aliases added in a follow-up.
- Still open from round 3: (3) **shared lace prerequisites** (nearest-neighbour bond model on `ℤ^d` with `p_c`, Fourier
  transform, signed convolution: I recommend (a) we propose the bond model and `p_c` as interface packages, (b) leave
  Fourier/convolution to Codex) and (4) **reserved scope** (all 111 transitive dependants of the lace articles, or only
  the 21 direct ones). Nothing is queued in either until you answer. The board tasks `connection-kernel-tags` (70KD,
  UZ7J) and `monotone-coupling-tag` (2ML7) are shared prerequisites outside the lace articles (ruling 14a gives them
  priority). Also from round 3: the critic's M-T2 (2ZI0 in `triangle-condition` and I23O in `triangle-susceptibility`
  are one lattice theorem with two full proofs; any Lean work should target one chain; `triangle-condition` is a lace
  article, so that is Codex's call).

- **Window (d) on the strict reading (round 1 of this series).** The launcher asked that, once its preconditions hold,
  only the migration brief be startable until claimed Lean work merges. Done so: (d) released, six unclaimed Lean
  briefs held (hier-cor12 among them), audits/wiki/tooling left open (ruling 11f). Lanes therefore take audits until
  (d) merges; reopening is a rename (steps in the window section). Overrule if you prefer the round-5 reading
  (disjoint proving open beside the migration), which the previous series used.
- **One batch per round** (launcher) **is now the bottleneck.** In round 2, ten mergeable or approved packages arrived
  within 20 minutes of the round's single batch (six approved tagged statements, a proof-only port, two wiki branches,
  the (d) report); all wait for round 3. The lessons of the previous series (several small gated batches per round,
  2.5-4 min each) suggest allowing up to three batches per round when no gate is already running. Overrule or confirm.
- **Workers run the full `scripts/gate.sh` in their own worktrees** (the (d) brief asked for it): with the coordinator's
  gate, the kernel replay and audit builds beside it, the coordinator's gate was OOM-killed (15 GB) and the replay died.
  Proposal: briefs ask workers for `lake build --wfail` of changed modules and importers only; the gate is the
  coordinator's (one machine-wide). Coordinator's call from round 3 unless you object.
- **Window (c) closed early for proving (round 5, coordinator's call under 11g).** The fold still runs (phase 1
  of 3 after 22 minutes); fourteen prover briefs on new or disjoint files were released beside it rather than
  let the window run past one round. Overrule if you want the queue kept empty until the fold merges.
- **Unrecorded predecessor.** A coordinator merged eight branches (05:33-05:56) without gating its last
  two merges or writing STATUS (it seems to have been cut off). Recovered and gated in round 1. The
  launcher should not start a coordinator while a predecessor may still be running, and a coordinator
  should commit STATUS after each gated batch, not only at the end.
- **mig-linters left three linters off** (`lakefile.toml`): `style.header` (six files carry third-party
  notices; rewriting them into mathlib's `Copyright (c) … All rights reserved.` form means asserting a
  holder: a licence-notice question, see "For Tom"), `unusedFintypeInType` and `unusedDecidableInType`
  (removing 44 unused instance binders changes statements, ≥5 tagged: an interface package after the
  window, coordinator's call unless you object).
- **Window reading changed in round 2 (coordinator's call under 11g; overrule if you disagree).**
  Migration (c) is waiting on its interface audit, and (d), (e) follow one at a time; no Lean proof has
  merged since round 4 of the earlier series. Ten prover briefs whose owned files are disjoint from every
  file of (c), the D4b fold, (d) and (e) were released. The migrations still run one at a time, but no
  longer behind an empty queue: each is checked for file-disjointness against the claimed prover work
  before release. (Still: no GitHub write tool in rounds 2 and 3; the first item above stands.)
  Round 4 opened window (c) properly once `mig-def-bond` merged: unclaimed prover briefs held, the fold the
  only new Lean brief; three prover packages claimed seconds earlier on disjoint new files ran beside it and
  merged. Overrule if you want strict emptiness even in that case.

### For ARCHITECT (round 7 additions)

- **Proving kept open beside the migrations (coordinator's call under 11g; overrule if you want strict quiet
  windows).** In round 7 the fold merged and the iscut part of (c) ran beside eight prover packages, all on files
  disjoint from it; seven tagged statements were proved and merged and eight more await audit. The same reading is
  proposed for (d) and (e), each still run alone among migrations.

### For Tom

- **Next pull request to `main` (ruling 13a):** open and merge (merge commit)
  https://github.com/tomhutchcroft/perclib/compare/main...claude/zen-lovelace-rvlcw2 when you wish; last gated commit
  `2023c28` (gate passed 18:12; GGH2/UHVH, the regular-variation revision, the task-board checker and the CI
  concurrency fix, on top of round 6's `a747905`); no local kernel replay has passed since `4c72765` (one is running at
  `a747905`). Summary in `/home/user/reports/READY-FOR-MAIN`. The first Pages deployment from `main` succeeded
  (https://tomhutchcroft.github.io/perclib/). Repository settings still yours: Settings → Branches, protect `main`,
  require `CI / gate`, no force pushes; and switch the auto-merge workflow on as the top of
  `.github/workflows/automerge.yml` says (repository variable `AUTOMERGE_ENABLED=true`).
- **Long-range collaboration (ruling 18):** new port work from the outside LRP I formalisation is paused until you tell
  us what was agreed; five briefs are held. The area map (`tasks/areas/long-range.md`), a neutral definition
  concordance (`docs/reports/long-range-concordance.md`) and a list of ported files with their credits
  (`docs/PORTED_FILES.md`) are being written for the joint review.
- **`regular-variation` (ruling 7, third critic read passed with advice):** seven optional wording items are listed in
  `/home/user/reports/critic/regular-variation-r3.md` §3 (copy in `lrp/docs/reports/critic/`): shorten the notation
  sentence on $L$ (l. 29), place the integer-valued verification after the tagged block, a summary line for the
  non-example, link the progeny tail to PVM9, one name each for the measures theorem and 3C2F, drop "The statement is
  given for $0<\alpha<1$.", and say once that $|K|$ is the $T$ of `ghost-fields`. The article merges as is; tell us which
  you want.
- **Pages wording for your approval (ruling 12):** the banner ("This wiki is unfinished and under active construction.
  Articles may be incomplete, and statements and proofs may contain errors. Only assertions marked 'proved' have been
  checked in Lean; see About.") and the About page text, exactly as in `wiki/src/render.mjs` and `wiki/src/build.mjs`
  at `eea6ceb` (list in `/home/user/reports/audit-pages-deploy.md` §"For Tom", item 2). The site ships with them
  meanwhile; the `noindex` meta stays until you lift it.
- **Wiki-original results, all nine now audited:** Q7QG, V7MP and 9FO5 (`hierarchical-runaway`) are judged CORRECT by a
  fresh correctness audit (`audit-wiki-original-runaway-c`), like J0DE, MFGT, OQV3, Q4PO, F7Q2, NC7F before them. They
  stay marked "original to this wiki; proof not independently checked" until you say how the marking should change; the
  NC7F precision fix (refining grids) is written and under audit.
- **Your branch `work/hierarchical-two-point-paper`** (`be2b9df`): reviewed (ruling 14c); the review is on the
  integration branch at `docs/reviews/branch-hierarchical-two-point-paper.md`. Verdict MERGEABLE AFTER CHANGES: the six
  translation-invariant first-exit theorems duplicate `PercLib/Models/HierarchicalTranslation.lean` (already merged, with
  Theorem 1.1 built on it) and should be dropped; `HierarchicalTriangle.lean` (the triangle recursion, new to the
  library) needs 15 whitespace fixes to build under `--wfail`. We do not merge or change your branch.
- **Licence notices (from `mig-linters`).** Six files keep their third-party headers and the header
  linter stays off: `Probability/ProdBernoulli.lean`, `Probability/Harris.lean`,
  `Probability/Cylinder.lean` (adapted from PercolationContinuity, Anthropic PBC), `Models/Site/Basic.lean`,
  `Percolation/Bond/Basic.lean` (Percolation, Apache 2.0 via `third_party/percolation/`),
  `Probability/Russo.lean` ("adapted from NearCritical/Russo.lean by Tom Hutchcroft and collaborators").
  Either prepend a mathlib-form block naming the upstream holder and keep the old notice below it, or
  keep the linter off for these headers. Your choice.
- **Issue #1** (README) is fixed on `main` since your merge of pull request #3: it can be closed.

- **Wiki-original results (critic of `hierarchical-runaway`, M8).** J0DE, MFGT, OQV3, Q4PO, F7Q2,
  NC7F (and Q7QG, V7MP, 9FO5) go beyond Hutchcroft 2022 Remark 6.14 (Gaussian limits with explicit
  covariance, a functional limit, a nested-block limit) and are marked in the body as "not attributed
  to the source". How should results original to the wiki be marked in History, and must each have a
  fresh correctness audit before it stays public? (The critic read their proofs and found no error; two
  steps are compressed, P10 and P11.)
- **T9KC scope** (long-range uniqueness of the infinite cluster): settled by `audit-wiki-proofs-misc`:
  the statement as worded (allowing p(z) = 1 and Σ p(z) = ∞) is true, by an elementary coset argument
  when some p(u) = 1 and by Grimmett–Keane–Marstrand (1984) connectivity when Σ p = ∞; the article's
  scope paragraph was rewritten accordingly and is merged (`4b5b504`, re-audit APPROVE). Nothing for
  you unless the GKM hypothesis check fails.
- **The model article is ready for you to look at (ruling 8):** `/articles/hierarchical-two-point/` (merged on
  the integration branch at `c8e3d2c` after a correctness audit, a second critic read and two re-audits; it
  includes the new J98J statement). The reviser's open questions are in §5 of its report (copy in
  `lrp/docs/reports/`, `wiki-model-hier-two-point.md`); the restructuring of the other articles follows this
  pattern unless you object.
- **Milestone:** Theorem 1.1 of *Critical percolation on the hierarchical lattice* (arXiv:2103.17013v1), the averaged
  critical two-point bounds with constants uniform in the kernel, is now proved in Lean on the integration branch
  (`PercLib/Models/HierarchicalTwoPointAveraged.lean`, merged `78ee775`), using the corrected Prop. 2.12(ii) constant
  listed below. Corollary 1.2 (pointwise bounds for radial kernels) is the next package. The kernel replay of `cfef666`
  (which contains it) was started this round; see "Integration tip and gate".
- **Questions from the wiki revisions (D-19: you judge style).** (1) `regular-variation`: the slowly varying function
  is written `L` (as in Feller, Vol. II, cited first) or `ℓ` (STYLE notation table; Bingham–Goldie–Teugels)? It stays
  `L` with one defining sentence until you decide; `ℓ` would touch the tagged statements 3491 and SLGY (letter
  only, with an audit). The assertion titles of SLGY and LTJ1 are being renamed to the literature's terms (metadata
  only); overrule if you prefer the old titles. (2) `branching-random-walk`: the reviser keeps the parameter
  conversion of BSI3 after the idea, with the references (critic: before the statement as setting). (3)
  `size-biased-laws`: the near-critical input of the IIC construction is stated as uniform-in-p
  quasi-multiplicativity plus uniform convergence (Basu–Sapozhnikov), not as `L(p)`-based arm bounds and
  θ(p) ≍ π(L(p)) (critic); the polynomial rate in r/s of the old FM8D idea was dropped (the published scheme gives
  geometric damping in the number of annuli only); the decoupling uses the innermost circuit with the outside
  independent. Both versions are in `/home/user/reports/authors/wiki-revise-proof-sections-a.md` (copy in
  `lrp/docs/reports/authors/`), "Disagreements with the critic".
- **Wiki-original results (ruling 11h), audited:** fresh correctness audits judge J0DE, MFGT, OQV3, Q4PO, F7Q2 and
  NC7F (`hierarchical-runaway` material beyond Hutchcroft 2022 Remark 6.14) correct, with no step failing
  (`/home/user/reports/audit-wiki-original-runaway-a.md`, `-b.md`; copies in `lrp/docs/reports/`). They are being
  marked "original to this wiki; proof not independently checked" as ruling 11h says; tell us whether, now that
  they have been checked, the marking should change. One precision point: NC7F's interpolated-paths clause holds
  for deterministic grids N_n → ∞ at every node, not for a fixed grid; a wording fix of the tagged block (with a
  fresh audit) is planned.

- Publishing the wiki: done as ruling 6 directs. The attribution pass (`pub-attrib`, 56
  articles credited "T. Hutchcroft, book in preparation", one catalogue entry, no locators)
  was approved by a fresh auditor on all four points of 6b with nothing withheld, and is
  merged and pushed on `claude/zen-lovelace-rvlcw2` of `perclib` (merge `6146737`). It
  reaches `main` only with the first pull request (see "For ARCHITECT").
- The wiki critic's mathematical reports (critic/general.md §5) were settled from the published
  sources by `scout-wiki-math`: the erratum "susceptibility-lower-coefficient" now attaches to
  FF30 and 7YNX only, and `tree-graph`'s proof of L82Q now follows the Lean route (both merged,
  `202e752`); FCU7 (`sharpness`) gets the precise statement of Duminil-Copin–Tassion
  arXiv:1502.03051 Thm 1.1 (`014-wiki-fcu7`, then a fresh audit). Nothing needed your ruling.
- Repository settings for ruling 10(2), once the CI workflow is on `main`: (1) Settings →
  Branches → add a protection rule for `main`: require a pull request, require the status
  check `CI / gate`, no force pushes; (2) Settings → General → allow auto-merge;
  (3) add collaborators to `.github/automerge-authors` and `CODEOWNERS` as you wish.
- Lemma I.4.13, second half, of *Critical long-range percolation I* implicitly assumes
  local integrability of `h` on `(1, ∞)` (compiled counterexample
  `not_integrableOn_rpow_mul_indicator_sub_inv`).
- The provisional errata in the wiki await confirmation (D-30). There are **180**, not 194 as said
  before. `scout-errata-triage` checked 104 against the published arXiv versions: **92 are forced
  corrections (class A), safe to confirm in bulk** (list in `/home/user/reports/scout-errata-triage.md`
  §2, copy in `lrp/docs/reports/`); 4 are A* (printed step wrong, repair a choice:
  `hnhyper:upper-extrapolation-error-scale`, `hhier21:scaled-truncation`,
  `triangle:boundary-positive-part`, `richards:conditioning-induction`); 6 are B (source readable as
  right: `hhiervol:coalescent-holding-rate`, `hhiervol:periodic-quotient-subgroup`,
  `lrp1:levy-first-moment-weight`, `rohde:reverse-derivative-comparison`, `sw:radial-clock-derivative`,
  `sw:finite-starting-image`); none found mistaken. Worth your glance first:
  `hhiervol:first-moment-terminal-amplitude` (p=1 coefficient in Thms 1.4/1.6 off by L^α),
  `hhiervol:critical-integral-and-amplitude`, `chensakai:compound-zeta-normalization` (forced; the
  choice of fix is yours), `gladkov:capacity-law` (Thm 8.2 false as stated). **Round 6:**
  `scout-errata-triage-b` classed the remaining 43 (`/home/user/reports/scout-errata-triage-b.md` §2,
  copy in `lrp/docs/reports/`): **42 more class A** (safe to confirm in bulk; list in §2), 1 A*
  (`lrp3:restricted-cluster-heredity`: Lemma III.4.2 false for arbitrary classes; the repair restricts
  to downward-closed classes; please confirm the classes used later in LRP III satisfy it), none
  mistaken. Totals over 180: A 134, A* 5, B 6, C 0, D 33 (Heydenreich–van der Hofstad: no public
  copy reachable), 2 handled elsewhere. Within A worth a glance: `triangle:triangle-numerator` (the
  main differential inequality (1.23) is false near β = 0; the corrected form is weaker),
  `hl2:reverse-bk-cancellation` (the step is false; no repair known), `kls:red-first-round-parameter`,
  `lrp3:deficit-ode-merger-forcing`.
- Universal tightness, issue-52 reading (`k ≥ 1` where the source prints `k ≥ 0`, false
  at `k = 0`); the hierarchical programme uses only `k ≥ 1`.
- arXiv:2103.17013v1 Prop. 2.12(ii) prints constant 1 where the flux argument gives
  `(L^α-1)/(β_c C (1-L^{-d}))` (provisional erratum; the Lean target keeps the factor).
- J98J (Theorem 1.1, averaged estimate for symmetric kernels) is audited and fixed; V4QQ/YWTU now
  cite it, so they hold for symmetric `J` (audit-j98j C1/C2). It reaches the tip with the
  restructured model article.
- Critic reports on `hierarchical-two-point` that change tagged statements (R2, R4, R6 in
  `/home/user/reports/critic/hierarchical-two-point.md` §4): V4QQ and YWTU are prose, not precise
  statements; the coordinator will queue a wiki package to state them precisely (hypotheses as
  in J98J; constants depending only on d, L, α, c, C) with a fresh audit. Say if you prefer to
  word them yourself.
- **Please approve `wiki/STYLE.md`** (merged on the integration branch as a draft, ruling 7 (i);
  wiki work follows it meanwhile). Open choices for you: the notation table (`P_q` for
  edge-dependent laws, `η` for the extinction probability) and whether "we" stays allowed
  inside proofs. Coming next: the restructured model article `hierarchical-two-point`.
- CI settings (from `audit-workflows`, note N6): with "require Code Owner review, no required
  approvals", anyone with write access could merge interface pull requests touching paths
  outside CODEOWNERS (definitions in area files, `PercLib/**/Tags/`, `docs/`, `tasks/`). Either
  add `/PercLib/**/Tags/` (and area `Defs`) to CODEOWNERS or accept this knowingly. Also check
  once that each action SHA pinned in the workflows is the tag it names (N4).

### Lessons

- **Round 7 (new series, 18:09-18:20):** started a minute after the predecessor's STATUS commit. **A ruling had
  arrived during the predecessor's round (18, at 18:02) and was not yet acted on:** compare the highest ruling number
  with the one STATUS names before anything else. Releasing held briefs and a new ruling can conflict (here 18b held
  four just-released ports): check the queue against each new ruling. Stopping a running gate (kill its process group
  before the extract step) to add a just-approved non-Lean branch cost about two minutes, since the rebuild was cached.
  Eleven done markers in ten minutes again; audit/critic/fix briefs for them took one minute each from templates
  (`mkbriefs.py`-style generator in the scratchpad: setup, D-35 block and audit block are fixed text).

- **Round 6 (new series, 17:57-18:10):** started a minute after the predecessor's STATUS commit (tree clean, nothing
  building; the replay had silently died of OOM 15 minutes earlier: check `dmesg` and the log's mtime, not only STATUS).
  **A ruling arrived mid-round again (17, during the gate):** re-read RULINGS.md after the gate. Lanes claimed every
  brief within minutes and eight done markers arrived during one 9-minute gate. Write follow-up briefs (audits, fixes,
  releases) while the gate runs; the HOLD → release substitution with `sed` takes seconds. Foreground `sleep` is blocked:
  wait with `until ! pgrep …; do sleep 10; done`. `git worktree remove` worked on merged worktrees after deleting the
  `.lake/packages` and `wiki/node_modules` symlinks.

- **Round 5 (new series, 17:30-18:00):** started 50 s after the predecessor's STATUS commit (tree clean; only the
  replay and a worker build, each in its own worktree). A top-priority audit claimed seconds before the round finished
  within 5 minutes: waiting for it before gating put Pages in the batch. **Run `check_d35` expectations through the
  brief:** a brief that says "no tag on the proof of a tagged Prop" makes the gate fail (D-35 check (i)); proof
  packages for a tagged Prop must carry the tag (write that in future briefs). A worker branched from the
  coordinator's unpushed batch commit and something pushed the integration branch: check `git status -sb` before
  pushing. Twelve done markers arrived within 25 minutes; the one-batch rule left five approvals for round 6.

- **Round 4 (new series, 17:05-17:28):** lanes were extremely fast: eleven briefs written during the gate were claimed
  within minutes and most finished before the gate ended (an interface audit in 3 minutes, a critique in 4). The
  bottleneck was the single gate (13 min beside the replay and worker builds) and the one-batch rule, not briefs.
  Prepare non-Lean commits (board mirror, `INTERFACE_CHANGES`) in a separate worktree branched from the gated commit
  while the gate runs, then fast-forward after it passes; never edit the main checkout during a gate. A ruling arrived
  mid-round again (15, during orientation): re-read RULINGS.md after the first commands. `find … -delete` on
  `__pycache__` in older worktrees deletes tracked files: use `git checkout -- scripts/__pycache__` instead. The kernel
  replay died from OOM near the end of a gate: start it right after the gate, not before.

- **Round 3 (new series, 16:56-17:15):** started one minute after the predecessor's push (tree clean; the only build
  running was an audit's, in its own worktree). Eleven approved/mergeable branches gated in one 9-minute batch beside the
  kernel replay without OOM (no worker gate running). Five more approvals arrived during the gate: with one batch per
  round they wait. Write release notes and new prover briefs while the gate runs; a scripted pre-release check (tags
  untagged, new files absent, no branch/claim of the id, owned files vs. migration files) took one command. `git worktree
  remove` refuses a worktree whose `scripts/__pycache__` the gate touched: `git checkout scripts/__pycache__/` and delete
  untracked `.pyc` there first. An outside pull request appeared minutes before the round (`git ls-remote` showed
  `refs/pull/2/head`): check at the start and queue its review early; it was claimed within a minute.

- **Round 2 (new series, 16:35-16:58):** started the minute the predecessor pushed (tree clean, nothing running in the
  main checkout; the kernel replay in its own worktree does not count). Two packages waiting: one gated batch. **Check
  memory before gating:** `pgrep -af 'scripts/gate.sh'` and read each process's cwd (`readlink /proc/<pid>/cwd`): a
  worker running its own gate plus the replay plus audit builds made the coordinator's gate OOM in the extract step; the
  log simply stops after the script tests (`dmesg | grep -i oom` confirms). Wait for the other gate, re-run alone. Start
  the replay with `setsid nohup … < /dev/null &` so it survives the coordinator's shell. **RULINGS.md can change
  mid-round** (ruling 14 arrived at 16:40): re-read it before writing STATUS. A fixer may merge the coordinator's
  local, not yet pushed batch commit into its branch (here `622c846`): harmless when the gate passes, but push promptly.
  Claims were instant: four new briefs were claimed within five minutes.

- **Round 1 (new series, 16:22-16:40):** started 2h20 after the predecessor's last STATUS with the tree clean and all
  four lanes claiming Lean briefs at the same second (16:22): an idle gap, not a running predecessor. Three done markers
  were waiting (one approved migration, two interface packages): one 4-minute gated batch. The kernel replay niced
  beside four worker builds runs at about 2 modules a minute (338 modules: hours); start it at the very beginning of a
  round, right after a gated commit, and leave the log where the next coordinator can read it. Interface reports
  arrive faster than audits are claimed when lanes are all on Lean: keep the audit template (148/149/152) handy.

- **Round 7, second half (13:36-14:00):** throughput was very high: 20 done markers in 25 minutes, including an
  interface audit of a 30-file migration in 15 minutes and four prover packages within ten minutes of release. The
  bottleneck was writing briefs, not gates: keep audit-brief and fix-brief templates (the frontier audit 134 served
  for seven more by substitution) and release held re-audits the moment a fixer's marker appears. A batch with the
  fold needed a 9-minute gate; small batches took 2.5 minutes. Prover briefs released from HOLD need a release note
  (current tip, which migrations run beside them, renamed names) and a scripted check that their tags are untagged
  and their new files absent.

- **Round 7:** started 13:15 with the tree clean; nothing waiting, and the wait produced two markers within 90 s,
  then nine more during the first gate. Four small gated batches (2.5 min each) kept every approved branch moving.
  Each wiki branch that adds a lead rewrites the frozen-digest test in `wiki/tests/lead.test.mjs`: expect that
  conflict on every such merge and keep the most general form (now on the tip). Running `pytest` in `scripts/`
  leaves untracked `__pycache__/*.pyc`: delete them before committing. An interface package's audit brief takes
  ten minutes to write from the brief and the diff: write it as soon as the done marker appears.

- **Round 6:** started at 13:03 with the tree clean and the predecessor's STATUS pushed; three done markers waiting
  (an audit with changes, a fix, a revision), none mergeable: two held audits released and a fix brief written within
  five minutes. A proof-only new-file merge gated in 2.5 min beside three worker Lean builds without OOM. When all
  four lanes are on Lean, released audits sit unclaimed: expect merges of wiki/tooling work only once a lane frees.

- **Round 5:** short (10 min); four done markers in the first six minutes, none mergeable (audit with changes,
  fix awaiting re-audit, premises audit, follow-up needing its own audit). Reopening proving was a rename once the
  held briefs had been brought up to date (G3/G5 edits, note) and checked by script: grep each brief for the
  fold's owned basenames and for target files that already exist, and `git grep 'tag "XXXX"'` for its tags.

- **Round 4:** started at 12:24 with the tree clean; done markers kept arriving (twelve in 30 minutes), so the
  round ran six small gated batches (2.5-4 min each, the `Bond/Basic.lean` gate included) instead of one; each
  was pushed at once. When holding briefs to open a window, expect races: three prover briefs were claimed in
  the seconds before the rename; check `claims/` after renaming and record them as in flight. Release a held
  re-audit only with the fixer's exact `<merge>`/`<fix>` commits from its report. An interface audit with a
  change "for the next package" (mig-def-bond change (1)) lets the branch merge as is; carry the change into
  the next brief explicitly.

- **Round 3:** started 25 s after the predecessor's push; nothing waiting; the 8-minute wait produced one critique
  within 90 s. A critique covering several articles gets one reviser brief owning all of them (ruling 7: one
  reviser at a time), with the held audit written at the same time. Briefs released in round 2 sat unclaimed for
  several minutes: there is no need to add more beyond about 20 startable.

- **Round 2:** a predecessor's STATUS commit (12:09) and this round's start (12:09) coincided; the tree
  was clean and pushed, so no wait was needed. Five done markers arrived in ten minutes, all needing an
  audit or a fix: no merge was possible, so the round's work was briefs. Release a fixer's re-audit with
  the exact commits (`git diff <merge> <fix>`) instead of branch-diff "minus the tip" wording. Workers
  take the alphabetically first brief: renumbering the whole startable set is how to set the lane mix.

- **Round 1 (this series):** the predecessor stopped mid-round after merging eight branches; nothing
  in STATUS said so. Compare `git log` with STATUS first, gate any ungated merges before adding more,
  and commit a short STATUS update after each gated batch so a cut-off coordinator loses little.
- **Read a fixer's report before releasing its re-audit.** A done marker also means "blocked": the
  model-article fixer stopped on a conflict, the audit was released on the marker alone and spent a
  worker on an unchanged branch. Check `git log` of the branch for the expected commit.
- Fix briefs that merge the tip into an older branch must say how to resolve the expected trivial
  conflicts (`wiki/tags.json` allocation entries, `migration-baseline.json` entries: keep both).
- Throughput: 20 done markers in 45 minutes; 8 startable briefs were all claimed within minutes. Write
  the next briefs (and HOLD follow-ups) while gates run.
- A full gate after a 323-file Lean merge took about 20 min; a gate running beside a worker's Lean
  build triggered an OOM kill (gate survived). Prefer gating when no worker builds Lean.
- No GitHub write tool may be available: check with ToolSearch and `gh auth status` early, and read
  pull requests and issues anonymously (`curl https://api.github.com/repos/<owner>/<repo>/pulls`).
- `mig-linters` added a copyright block before each provenance header: header checks must read all
  leading comment blocks (`071`/`081`).


- **Round 9:** two audit markers arrived within two minutes of the start (one at 05:22, one at 05:24);
  both approved with changes. When a correctness audit and a critic re-read target the same article,
  hold one combined revision brief until both are done instead of two fixes on one file. Workers now
  write build logs into the coordinator's scratchpad path; read them there to judge a long Lean claim.

- **Round 8:** predecessor's handoff and this round's start overlapped by a minute (STATUS time 05:14,
  clock 05:13 at start); tree was clean, so no wait needed. One done marker arrived within 90 s of
  waiting; an errata-only merge plus gate took about 4 min. Errata entries are not tagged statements:
  merged on the gate (as `wiki-math-fixes` was).

- **Round 7:** nothing new was done at the start; within one minute of waiting two markers arrived
  (`fix-workflows-r2`, `audit-wiki-fcu7`), both leading to audit briefs, no merge. Claims are fast
  again (two audits claimed within a minute of the round's start).

- **Round 6:** six done markers were waiting at the start (four wiki branches with mathematical or
  tagged content needing audits, one records-only branch, one critique), and a seventh arrived during
  the gate. Only records-only work merged on the gate; everything else became audit briefs. A
  wiki-only gate on a 0-Lean merge took about 5 min. Claims slowed: nine startable briefs from round 5
  and this round sat unclaimed for 15+ minutes, so do not over-produce briefs beyond about 10.
- Merged worktrees with a `wiki/node_modules` symlink refuse `git worktree remove`: delete the
  symlink first (never `--force`).

- **Round 5:** a comments-only migration over 266 files still rebuilds them: the gate took about
  12 min (beyond the Bash tool's 10-min foreground limit; run it in the background and poll for
  `pgrep -f scripts/gate.sh`). Check comment-only migrations by comparing the saved extracts in
  `.lake/gate/`: only the `line` field may differ. The classifier's token scan flags the word
  "tag(s)" in comments: a known false positive. Workers claimed six briefs within ten minutes.

- **Workers run as in-process agents:** there are no separate worker processes to look for; judge a
  claim live by recent file changes in its worktree (`find <wt> -newer docs/STATUS.md`).
- **Round 4 (short):** one finished package at the start (`wiki-lead-parser`), one more during the
  round (`wiki-I421`, interface: audit queued). The wiki gate on a 0-Lean merge took about 4 min.

- **Worktrees:** `git worktree add /home/user/wt/<id> -b work/<id> claude/zen-lovelace-rvlcw2`,
  `ln -s /home/user/perclib/.lake/packages <wt>/.lake/packages`, and
  `cp -a /home/user/perclib/.lake/build <wt>/.lake/build` so the worker does not rebuild
  PercLib; never download or rebuild mathlib per worktree.
- **Memory:** 15 GB, no swap. `lake env leanchecker PercLib` in one process is killed; use
  `kernel_replay.sh` batches, never during builds. A warm gate takes 4-6 min.
- **Merges:** conflicts are only `PercLib.lean` import lines; keep both sides in sorted
  position, `git add`, commit with `-m`, then `check_import_closure.py`. During an
  unresolved conflict the closure check reports spurious missing modules; rerun after
  the commit.
- **Workers are fast:** done markers arrive while the gate runs (four during this round's
  first gate). Integrate them in follow-up gated batches in the same round when they
  unblock something (here: the drain before the migration window); otherwise record them
  as finished-unmerged.
- **Check `git log` against STATUS** at the start: a predecessor may have merged after
  writing its handoff.
- **Briefs are claimed within a minute** of being written; write a brief only when it is
  ready to start, and put HOLD briefs in place before releasing anything they depend on.
- **Workers** sometimes use their harness's commit trailer instead of the preamble's;
  accepted, not rewritten.
- **Headers:** ported files tend to say "pull request 488" and package ids in headers; the
  D-35 check rejects them in new files; briefs say "repository, branch, commit".
- **Tags inside `to_additive`:** write `@[tag "XXXX", to_additive …]`.
- **One coordinator per checkout**, never two `gate.sh` runs at once.
- **Wiki merges** need no Lean rebuild beyond the gate; verify the merged `wiki/` tree is
  byte-identical to the audited commit (`git diff --quiet <audited> HEAD -- wiki`) instead of
  re-running `npm` (no network for `npm ci` is guaranteed).
- **Docs that describe CI** (contrib-docs, task-board) wait for the workflows; check each
  non-Lean branch for references to files or processes not yet on the tip.
- **`frontier.py` leaves an untracked `scripts/__pycache__/frontier.*.pyc`**: delete it before
  committing.
- **Kernel replay** was not run this pass: `mig-rowsum` may be building in its worktree
  (memory). Run `scripts/kernel_replay.sh 6` when no worker builds, before the first pull
  request to `main`.
- **Removing worktrees:** only if `done/<id>` exists and the branch is an ancestor of the
  tip (a fresh branch is trivially an ancestor before its first commit).
- **Pre-gate an interface branch while its audit runs:** `git worktree add --detach
  /home/user/wt/gate-<id> <tip>`, merge the branch there, symlink `.lake/packages`, copy the
  branch's built `.lake/build` and `.lake/gate/<base>.json`, run `scripts/gate.sh <base>` there
  (2.5 min warm), then remove the worktree. The main checkout stays clean.
- **During a window the queue empties fast:** workers claimed 10 non-Lean briefs within 15
  minutes. Keep HOLD Lean briefs ready (written this round from the scouts) so closing the
  window is a rename, and keep enough read-only/tooling briefs to stay at 8 startable.
- **An audit that approves with required changes** gets a fix brief to a new worker with the
  audit attached and a HOLD re-audit brief written at the same time.
- **Low numeric prefixes (000-014)** put critical-path briefs first; workers take the
  alphabetically first startable brief.
- **Wiki merges:** run `npm test` (or `npm run build`) on the merged tree with
  `node_modules` symlinked from `/home/user/lrp/wiki/node_modules`, then remove the symlink and
  `dist/`; no network needed. Several wiki branches touching `migration-baseline.json` or
  `tags.json` will conflict trivially: merge one at a time.
- **This round's throughput:** about 25 done markers in 50 minutes. Integrate in several gated
  batches within the round (each wiki-only gate is ~2.5 min warm) rather than leaving finished
  work for the next coordinator.

- Round 14 (new series, 21 Nov ~23:15): batch gated at `29c7c4b` (11 tagged statements), 343 proved; full STATUS at `13418dc`.
- Round 15 (21 Nov ~23:15): batch gated at `c26219e` (10 tagged statements: 32GP, R2Y7, J2TE, L9YJ, XA7C, CYYG, 94E7, CUE4, N0HM, TIKW), 353 proved.

## Paced cycle 1 (26 Nov 2026, ~02:50 UTC), moved from STATUS in cycle 2

- Batches `c6efdce` -> `2f5be3e` (KGNK, `frontier-lazy-return-kernel` @ `d3988df`) and `2f5be3e` -> `4a6dc1b` (PR #10 update
  `80ee07a`, proof-only); both gated. `frontier-nonbacktracking-recurrence` @ `1a3f0ed` (0MK8) failed the gate on `local macro`.
- PRs #13-#23 opened from Yujin's fork (ruling 24), all commented; Tejas #11/#12 first response; audit `050-audit-c1-planar` queued.
- The integration PR to `main` was refused by the permission layer that cycle; Tom then merged #10 directly (`97b39e5`).
