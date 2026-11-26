---
id: cluster-second-moment-any-law
title: Second moment of a cluster as a supremum over cofinal windows, under any law
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Second moment of a cluster as a supremum over cofinal windows, under any law

## Goal
Prove wiki assertion **NEM5** (article `finite-volume`) in full and tag it. The library proves
it only under the Bernoulli product law (`lintegral_cluster_sq_eq_iSup`,
`PercLib/Percolation/Bond/ClusterMoments.lean`), but the proof uses no independence.

## Target
Let `V` be countable and `(F_i)_{i ∈ I}` finite vertex sets such that every finite `S ⊆ V` is
contained in some `F_i`. Then for every root `u` and every probability measure `μ` on
configurations,
`E_μ |K(u)|² = sup_i E_μ |K(u) ∩ F_i|²`
(extended nonnegative values; no ordering of `I` and no finite-moment assumption).

Sketch of the area lemma (general measure, if the proof allows it):
```lean
theorem lintegral_cluster_sq_eq_iSup_of_measure [Countable V] (μ : Measure (Config V))
    {ι : Type*} (v : V) (F : ι → Finset V) (hF : ∀ s : Finset V, ∃ i, s ⊆ F i) :
    (∫⁻ ω, ((cluster ω v).encard : ℝ≥0∞) ^ 2 ∂μ) =
      ⨆ i, ∫⁻ ω, ((cluster ω v ∩ (F i : Set V)).encard : ℝ≥0∞) ^ 2 ∂μ
```
Tagged statement: the same for every probability measure `μ`. Re-prove
`lintegral_cluster_sq_eq_iSup` as a corollary without changing its statement.

## Owned files
- `PercLib/Percolation/Bond/ClusterMoments.lean` (append; re-prove the existing lemma as a
  corollary).
- New `PercLib/Percolation/Bond/Tags/ClusterSecondMoment.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

If the task `cluster-mixed-moments-any-law` is open at the same time, coordinate through the
pull requests: both append to `ClusterMoments.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/ClusterMoments.lean` and its imports, mathlib; wiki assertion NEM5.

## Stop condition
NEM5 tagged and proved, modules built with `--wfail`; or the statement is found false as
written (report it).

## Hand-off
Pull request description: the tagged statement, the area lemma(s), searches, build result.
