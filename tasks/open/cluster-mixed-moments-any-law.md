---
id: cluster-mixed-moments-any-law
title: Mixed cluster moments as sums of joint connection probabilities, under any law
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Mixed cluster moments as sums of joint connection probabilities, under any law

## Goal
Prove wiki assertion **6HJ9** (article `finite-volume`) in full and tag it. The pointwise
identities are in the library; the expectation identities are proved only under the Bernoulli
product law, although they hold under every probability measure.

## Target
For finite vertex sets `F, D` and roots `u, v`, with `X_F(u) = |K(u) ∩ F|`:
1. (pointwise, exists) `X_F(u) = Σ_{a∈F} 1{u↔a}` and
   `X_F(u) X_D(v) = Σ_{a∈F} Σ_{b∈D} 1{u↔a, v↔b}` (`encard_cluster_inter_mul_eq_sum`,
   `encard_cluster_mul_eq_tsum` and neighbours in `PercLib/Percolation/Bond/ClusterMoments.lean`;
   check which of the two pointwise identities is stated, and add the missing one).
2. (new) If `V` is countable, under any probability measure `μ` on configurations,
   `E_μ[X_F(u) X_D(v)] = Σ_{a∈F} Σ_{b∈D} μ(u↔a, v↔b)` and
   `E_μ[|K(u)| |K(v)|] = Σ_{a∈V} Σ_{b∈V} μ(u↔a, v↔b) ∈ [0, ∞]`.

Sketch (area lemmas; general measure if free):
```lean
theorem lintegral_cluster_inter_mul_of_measure [Countable V] (μ : Measure (Config V))
    (u v : V) (F D : Finset V) :
    (∫⁻ ω, ((cluster ω u ∩ (F : Set V)).encard : ℝ≥0∞) *
      ((cluster ω v ∩ (D : Set V)).encard : ℝ≥0∞) ∂μ) =
    ∑ x ∈ F, ∑ y ∈ D, μ (conn u x ∩ conn v y)
theorem lintegral_cluster_mul_of_measure [Countable V] (μ : Measure (Config V)) (u v : V) :
    (∫⁻ ω, ((cluster ω u).encard : ℝ≥0∞) * ((cluster ω v).encard : ℝ≥0∞) ∂μ) =
      ∑' x, ∑' y, μ (conn u x ∩ conn v y)
```
Tagged statement: the conjunction of the pointwise identities and of the two expectation
identities for every probability measure. Re-prove `lintegral_cluster_inter_mul` and
`lintegral_cluster_mul` as corollaries without changing their statements.

## Owned files
- `PercLib/Percolation/Bond/ClusterMoments.lean` (append; re-prove the two existing lemmas as
  corollaries).
- New `PercLib/Percolation/Bond/Tags/ClusterMixedMoments.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

If `cluster-second-moment-any-law` is open at the same time, coordinate: both append to
`ClusterMoments.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/ClusterMoments.lean` and its imports, mathlib; wiki assertion 6HJ9.

## Stop condition
6HJ9 tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemma(s), searches, build result.
