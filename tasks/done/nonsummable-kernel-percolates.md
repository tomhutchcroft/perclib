---
id: nonsummable-kernel-percolates
title: Non-summable displacement kernels give infinite degree and percolation at every positive intensity
difficulty: medium
kind: interface
labels: []
---

# Non-summable displacement kernels give infinite degree and percolation at every positive intensity

## Goal
Prove wiki assertion **K38T** (article `displacement-kernels`) in full and tag it. The library
proves that both critical intensities vanish for a non-summable translation-invariant kernel
(`rootCriticalIntensity_eq_zero_of_translationInvariant`,
`globalCriticalIntensity_eq_zero_of_translationInvariant`, `PercLib/Models/NonSummable.lean`);
the assertion also gives the almost-sure behaviour at each fixed intensity.

## Target
Let `G` be a countable additive group (not necessarily commutative), `k : G → ℝ≥0` and
`J s(x, y) = k(y − x)` (so `k` is even), with `Σ_{z ≠ 0} k(z) = ∞`. Let `q` be a profile with
`q e = 1 − exp(−β J e)` for every non-diagonal `e` (diagonal arbitrary).
1. If `β > 0`, then almost surely every vertex has infinitely many open neighbours and an infinite
   cluster.
2. `rootCriticalIntensity J v = 0` for every `v`, and `globalCriticalIntensity J = 0` (exist).
3. If `β = 0`, then almost surely every cluster is a singleton.

Sketch of the new area lemma for 1:
```lean
theorem ae_forall_infinite_of_translationInvariant [Countable G] (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y, J s(x, y) = k (y - x))
    (hk : (∑' z, if z = 0 then 0 else (k z : ℝ≥0∞)) = ∞) {β : ℝ≥0} (hβ : 0 < β)
    (q : Sym2 G → unitInterval) (hq : ∀ e, ¬ e.IsDiag → q e = intensityProfile J β e) :
    ∀ᵐ ω ∂law q, ∀ v, {w | (openGraph ω).Adj v w}.Infinite ∧ (cluster ω v).Infinite
```
Inputs: the row identity (`rowSum_eq_of_translationInvariant` in
`PercLib/Models/TranslationInvariant.lean`), `rowSum_intensityProfile_eq_top` and
`ae_infinite_neighbors_of_rowSum_eq_top` (`PercLib/Percolation/Bond/InfiniteDegree.lean`), and
diagonal erasure for the arbitrary diagonal. Tagged statement: the conjunction of 1-3.

## Owned files
- `PercLib/Models/NonSummable.lean` (append only).
- New `PercLib/Models/Tags/NonSummable.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Models/{NonSummable,TranslationInvariant}.lean`,
`PercLib/Percolation/Bond/{InfiniteDegree,Basic}.lean`, `Diagonal/Probability.lean`, mathlib;
wiki assertions K38T, XJ74, R01V.

## Stop condition
K38T tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
