# Task board

This directory is the list of work that is ready to start. Each task is one Markdown file,
written so that a contributor with only a clone of this repository (person or AI assistant)
can do it, open a pull request and get it checked, with nobody else online. Read
[`AGENTS.md`](../AGENTS.md) and [`CONTRIBUTING.md`](../CONTRIBUTING.md) first: they give the
build commands, the rules for Lean code and what CI checks.

| Directory | Meaning |
|---|---|
| `tasks/open/<task-id>.md` | ready to start; nobody has claimed it unless an open pull request's title begins with its id |
| `tasks/claimed/<task-id>.md` | being done by the project's own agents; do not start it |
| `tasks/done/<task-id>.md` | finished and merged |

## Areas taken

Some parts of the library have an owner who is building them. Do not start work inside an
area taken by someone else; read its map for what exists and what it needs from shared
prerequisites.

| Area | Owner | Map |
|---|---|---|
| Lace expansion | Codex (Tom's) | [`areas/lace-expansion.md`](areas/lace-expansion.md) |
| Planar percolation | Tejas Oke (`TejasO2`; pull requests #11, #12) | map to come (`areas/planar.md`) |

## What a task file contains

Every task follows the same brief format (decision D-35 in `docs/DECISIONS.md`):

- a front-matter block with `id`, `title`, `difficulty` (`easy`, `medium`, `hard`),
  `kind` (`proof-only` or `interface`, see below) and `labels`;
- **Goal**: what the task proves and why it is wanted;
- **Target**: the exact statement, mathematically and, where it helps, as a Lean signature
  sketch. A sketch fixes the mathematics, not the spelling: binder names, implicit
  arguments and the namespace may change; hypotheses and conclusion may not be weakened;
- **Owned files**: the only files the pull request may create or change (plus one import line
  per new module in `PercLib.lean`, and moving the task file to `tasks/done/`);
- **Allowed inputs**: the library files, papers and wiki assertions the work may rely on.
  Anything else on `main` may be imported too, but never copied or re-proved;
- **Stop condition**: when the task is finished, and when to stop and report instead;
- **Hand-off**: what the pull request description must contain.

**Kinds.** A `proof-only` task adds theorems and lemmas only (no `def`, `structure`,
`instance`, notation or `@[tag]`) in the owned `.lean` files; such a pull request can merge
on green CI. An `interface` task adds or changes something others depend on (here, almost
always a statement carrying a wiki tag `@[tag "XXXX"]`); a maintainer reviews the statement
against its source before merge, so state it faithfully and keep it separate from unrelated
proofs.

**Labels.** `labels: [good-first-task]` marks tasks that are short and self-contained, a good
way to learn the library's conventions. Other tasks have `labels: []`.

## How to take a task

1. Check the open pull requests: a task is taken if an open pull request's title begins with
   its id. A **draft** pull request with no push for **seven days** is free to take over;
   open your own and link the old one.
2. Claim it by opening a **draft pull request** against `main` whose title begins with the
   task id, for example `cluster-count-any-law: expected component count under any law`.
   An empty first commit is fine.
3. Branch from `main`. If `main` does not yet contain a file the task names as an input, base
   the branch on the integration branch `claude/zen-lovelace-rvlcw2`, which reaches `main`
   regularly, and say so in the pull request.
4. Do the work in the owned files only. Build only the modules you change:
   `lake build --wfail PercLib.Area.File`.
5. In the pull request that completes the task, move its file from `tasks/open/` to
   `tasks/done/` with `git mv`. Change nothing else under `tasks/`.
6. If the target turns out false, vacuous or to need a hypothesis its source does not state,
   **do not change the statement**. Stop, open a "Mathematical gap" issue with the
   counterexample or the missing hypothesis, link it from the pull request, and finish
   whatever parts of the task remain true.

## Rules every task inherits

These summarise `AGENTS.md` and `docs/COORDINATION.md`; those files win if they differ.

- No `sorry`, `admit`, `axiom`, `native_decide`, `set_option maxHeartbeats` or
  `set_option linter.*`.
- Search before writing: for any lemma that does not mention percolation, search mathlib (by
  name and by type: `exact?`, `rg` in `.lake/packages/mathlib`) and `PercLib`, and list what
  you searched in the pull request. Never keep a private copy of a lemma that exists.
- State a lemma at the generality its proof supports when that costs nothing; the
  wiki-facing form is a corollary.
- Names follow mathlib: the name describes the conclusion, hypotheses go in `_of_`, the most
  specific namespace. A tag or task id never appears in a declaration name.
- Definitions only in `Basic.lean` or `Defs.lean`, never in a task that does not say so.
- A tagged statement lives in a `Tags/` file and only restates library lemmas: each conjunct
  of a tagged conjunction is also a named lemma in the area file, and downstream code uses the
  area lemma. Follow the pattern of `PercLib/Analysis/Tags/IntegratedSusceptibility.lean`:
  `public import PercLib.Meta.Tag`, `@[tag "XXXX"]` before the theorem, a docstring that
  paraphrases the assertion in your own words. Before tagging, check that the tag is unused
  (`git grep -n 'tag "XXXX"'`). Hypotheses the assertion states but the proof does not use
  are kept, with the binder prefixed by `_`.
- New files open, after the imports, with a module docstring `/-! # Title … ## Main
  results -/`. File headers carry provenance (source, revision, licence) and the
  mathematical reference only, never task, issue or pull-request numbers.
- A row sum over `Sym2` is written with `rowSum` from `PercLib/Percolation/Bond/Basic.lean`.

## Sources referred to by tasks

- **Papers** by arXiv number, for example arXiv:2508.18807v1 (T. Hutchcroft, *Critical
  long-range percolation I*) and arXiv:2103.17013v1 (T. Hutchcroft, critical two-point
  function of long-range percolation on the hierarchical lattice). Statement numbers such as
  "Lemma I.5.5" refer to arXiv:2508.18807v1; numbers such as "Proposition 2.7" in the
  `hier-…` tasks refer to arXiv:2103.17013v1.
- **Wiki assertions** by tag, for example `ZAIH`: an assertion of the PercLib wiki, anchored
  as `tag-ZAIH` in an article under `wiki/articles/`. The task gives the mathematical content;
  the article gives context and the intended proof.
- **Port sources.** Tasks named `lrp-…` port Lean code from the public repository
  `yujinhkim/lrp`, branch `critical-lrp-1`, commit
  `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc` (directory `PercLib/CriticalLRP/`), a
  formalisation of arXiv:2508.18807v1 released under Apache-2.0. Read those files as text;
  do not add that repository as a dependency.

### Rules for port tasks (decision D-33)

- PercLib's notions win. Where PercLib already has a notion, use it; never add an alias, a
  second copy or a bridge to the source's own definitions. Delete any source lemma that
  duplicates one in PercLib or mathlib and use the existing one.
- The source's `RegularlyVaryingAtTop f ρ` becomes `RegularlyVarying ρ f` of
  `PercLib/Analysis/RegularVariation/Defs.lean`, which also asks measurability on a tail and
  eventual positivity: carry those hypotheses. The source's bundled hypothesis structures
  (`RVPosData`, `HasPotterBounds`, `HasLocalUniformRatio`) are written out as explicit
  hypotheses. The source's own size-biased laws become the `withDensity` form of
  `PercLib/Probability/SizeBias.lean`. Source definitions are written out inline in
  statements; no new `def` unless the task says so.
- Every new file carries the provenance header used by the existing ports (see
  `PercLib/Analysis/Tauberian/Endpoints.lean`): adapted from `yujinhkim/lrp`, branch
  `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, the source file paths,
  licence Apache-2.0, the upstream `yujinhkim/Critical-Long-range-percolation` at
  `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`, the paper reference, and a short list of what
  was modified.
- Keep statements faithful to the source theorems, modulo the notion changes above, and list
  every statement change (before/after) in the pull request.
- A premise the source needs but the paper does not state stays an explicit hypothesis, and
  the pull request says so. Nothing is described as a proved theorem of the paper while such a
  premise remains. Never introduce `…Input` structures.
- If a source statement is false or vacuous after translation, stop on that statement, report
  the counterexample in a "Mathematical gap" issue, and port the rest.
- Port tasks are `proof-only`: no `@[tag]`, even where a statement matches a wiki assertion.
  Say in the pull request which statement matches which candidate tag; tagging is a later,
  reviewed step.

## Other work

`docs/FRONTIER.md` is generated from the library's manifest: it lists wiki assertions that are
not yet proved and whose prerequisites are all proved. Use it to find work that no task
covers; for anything large, open an issue describing the statements first, so that it does
not collide with work in progress. Tasks whose prerequisites are not yet merged are added to
`tasks/open/` when they become startable.
