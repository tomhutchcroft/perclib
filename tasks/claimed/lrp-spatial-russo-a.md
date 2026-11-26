---
id: lrp-spatial-russo-a
title: Infinite-volume Russo formula for truncated spatial moments (port, part A)
difficulty: hard
kind: proof-only
labels: []
---

# Infinite-volume Russo formula for truncated spatial moments (port, part A)

Being done by the project's own agents; do not start it.

## Goal
Port the part of the infinite-volume spatial Russo formula of arXiv:2508.18807v1 that needs no
uniformity premise: truncated spatial moments, their finite-window flux bounds and their
approximation from finite windows. This is a rewrite against PercLib's own infinite-volume
Russo development, not a line-by-line port. Follow "Rules for port tasks" in `tasks/README.md`.

## Target
Source file (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`):
`PercLib/CriticalLRP/RussoInf/SpatialExchange.lean`.

Port the theorems that do **not** take the hypothesis `hunif`:
- the truncated spatial moment (source `sMomentTrunc`, written out inline) and its API:
  nonnegativity, the absolute bound, measurability, dependence on finitely many coordinates,
  monotonicity, the finite-sum form, convergence under cut configurations
  (`eventually_sMomentTrunc_cutConfig`, `tendsto_sMomentTrunc_cutConfig`,
  `tendsto_integral_sMomentTrunc`);
- the countable-exception and almost-everywhere derivative lemmas
  (`countable_range_edgeLen`, `ae_hasDerivAt_of_off_edgeLen`, …);
- the extended-valued forms and `lintegral_spatialMomentENN_eq_iSup`,
  `tendsto_sMomentTrunc_of_finite`;
- the flux bounds `tsum_abs_pivotalFlux_sMomentTrunc_le`, the quadratic weight (source
  `quadWeight`, written out) and `tsum_abs_pivotalFlux_quadWeight_le`.

Do **not** port the four main theorems that assume `hunif` (a uniformity premise the paper does
not state). The source builds on `RussoInf.Exchange`/`FluxMain`, which PercLib replaced by
`PercLib/Models/LongRange/InfiniteVolumeRusso.lean`: use that file and
`PercLib/Percolation/Bond/SpatialMoments/{Defs,Derivative}.lean` (`spatialMoment`) instead.

Candidate wiki tags 57RX, 1K61, 6DOC: do not tag; say in the pull request how close each
ported statement comes (57RX and 1K61 need the infinite-volume almost-everywhere derivative on
`ℤ^d`, local Lipschitz continuity and, for 57RX, an upper bound of the form `2Mχ S + Dχ²`).

## Owned files
- New `PercLib/Percolation/Bond/SpatialMoments/InfiniteRusso.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Models/LongRange/InfiniteVolumeRusso.lean`,
  `PercLib/Percolation/Bond/SpatialMoments/{Defs,Derivative}.lean`,
  `PercLib/Probability/Russo*.lean`, `PercLib/Probability/Pivotal/*`.
- The source file above (read as text); arXiv:2508.18807v1, §I.4-I.5.

## Stop condition
The non-`hunif` content is ported and the module builds with `--wfail`; or a statement is false
or vacuous after translation (report it, port the rest).

## Hand-off
Pull request description: public theorems with signatures and source names; statement
changes; the candidate-tag comparison; searches; build result.
