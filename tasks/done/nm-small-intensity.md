---
id: nm-small-intensity
title: Small-intensity bounds for normalized models (1EWX) and a root-only moment counterexample (HRS7)
difficulty: medium
kind: interface
labels: []
---

# Small-intensity bounds for normalized models and a root-only moment counterexample

Being done by the project's own agents; do not start it.

## Goal
Prove and tag two wiki assertions whose Lean is nearly complete: **1EWX** (article
`boundary-susceptibility`, anchor `tag-1EWX`) and **HRS7** (article `multipoint-trees`,
anchor `tag-HRS7`). Read each article's front-matter `context` block: the tagged statement
must be faithful to it as well as to the displayed assertion.

## Target
1. **1EWX.** For a countable transitive independent-bond intensity model with symmetric
   nonnegative weights of row sum one and `0 < β < 1`:
   `1 + β - β²/2 ≤ χ(β) ≤ 1/(1-β)` and `1 ≤ Δ(β) ≤ 1 + 3(β/(1-β))² + (β/(1-β))³`;
   `χ` is locally Lipschitz on `(0,1)` with `χ' ≤ (1-β)⁻²` almost everywhere (from the
   finite-susceptibility regularity assertion MXGM); and the "stronger source formula" the
   article refers to fails almost everywhere for all sufficiently small `β` (state it exactly
   as the article's earlier display does, and quote that anchor in the pull request).
   The bounds exist as lemmas in `PercLib/Models/NormalizedSmallIntensity.lean`.
2. **HRS7.** There exist a countable vertex type `V`, a profile `q`, and a root `o` such that
   the host graph `SimpleGraph.fromEdgeSet {e | 0 < q e}` is connected, `E|K_o| = 2`,
   `E|K_o|² = ∞`, and the remaining conjuncts exactly as the wiki block states them (root
   cluster finite almost surely, every positive exponential moment infinite, susceptibilities
   of other vertices not uniformly bounded).

Every conjunct of a tagged conjunction is also a named lemma in the area file; the `Tags/`
file holds only the tagged restatements.

## Owned files
- `PercLib/Models/NormalizedSmallIntensity.lean` (append only).
- New `PercLib/Models/Tags/SmallIntensity.lean` (tagged statements only).
- Its import line in `PercLib.lean`.

Read, do not edit, `PercLib/Models/HeavySecondMoment.lean`; if HRS7 needs a lemma there,
put the new lemma in `NormalizedSmallIntensity.lean`.

## Allowed inputs
`main` (or the integration branch), mathlib, the wiki articles named above. No new `def`:
a missing notion (for example a mass-transport principle, needed by the neighbouring
assertion MTYL, which is not part of this task) is reported as a definition proposal.

## Stop condition
Both tags proved and the changed modules built with `lake build --wfail`; or a target found
false, vacuous or under-hypothesised (stop on that item, open a "Mathematical gap" issue,
finish the other).

## Hand-off
Pull request description: each tagged statement with its tag, the area lemmas, searches made
in mathlib and PercLib, build result. A maintainer reviews the tagged statements against the
wiki before merge.
