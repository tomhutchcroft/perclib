---
id: cluster-boundary-product
title: Law of a prescribed finite cluster as internal connectivity times a boundary product
difficulty: medium
kind: interface
labels: []
---

# Law of a prescribed finite cluster as internal connectivity times a boundary product

## Goal
Prove wiki assertion **R3I9** (article `boundary-laws`) in full and tag it. The library has the
event identity and the factorisation `P(K(x) = C) = P(I_C) P(D_C)` (`law_cluster_eq_finset`,
`PercLib/Percolation/Bond/ClusterLaw.lean`); the product formula for the closed-boundary
event is missing.

## Target
Let `C` be a finite vertex set with `x ∈ C`, `I_C` the event that every vertex of `C` is joined to
`x` by an open path inside `C`, and `D_C` the event that every pair `{u, v}` with `u ∈ C`,
`v ∉ C` is closed.
1. For every configuration on an arbitrary vertex set, `{K(x) = C} = I_C ∩ D_C`.
2. On countable `V`, the three events are measurable and
   `P_q(K(x) = C) = P_q(I_C) P_q(D_C) = P_q(I_C) ∏_{u∈C, v∉C} (1 − q_{uv})`,
   the product being the limit along any increasing finite exhaustion of the boundary pairs
   (it may be zero).

The new content is `P_q(D_C) = ∏_{u ∈ C, v ∉ C} (1 − q_{uv})`. The map `(u, v) ↦ s(u, v)` on
`C × Cᶜ` is injective, so this is a countable closed product; prove it by continuity from above
over finite subfamilies and finite independence. (If the task `countable-closed-product` has
merged, use its area lemma instead.) State the product with `∏'` in `ℝ≥0∞` or as an infimum over
an exhaustion, matching item 3 of `countable-closed-product` if it exists. Tagged statement: the
conjunction of 1 and 2.

## Owned files
- `PercLib/Percolation/Bond/ClusterLaw.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/ClusterBoundaryProduct.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/ClusterLaw.lean` and its imports,
`PercLib/Probability/{ProdBernoulli,ProdBernoulliIndependence}.lean`,
`PercLib/Probability/Exploration/Transcript.lean`, mathlib; wiki assertions R3I9, QH7Q.

## Stop condition
R3I9 tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
