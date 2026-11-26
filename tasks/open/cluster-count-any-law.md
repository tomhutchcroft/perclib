---
id: cluster-count-any-law
title: Expected number of clusters under any law on a finite graph
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Expected number of clusters under any law on a finite graph

## Goal
Prove wiki assertion **ZAIH** (article `cluster-partitions`) in full and tag it. The library
proves the expectation identity only under the Bernoulli product law `law q`; the assertion
holds under every probability measure on configurations, since it is linearity of a finite sum.

## Target
For finite `V`, write `κ(ω)` for the number of connected components of the open graph.
1. (deterministic, exists) `κ(ω) = Σ_{x ∈ V} 1/|K_ω(x)|` for every configuration
   (`card_connectedComponent_eq_sum_inv`, `PercLib/Percolation/Bond/ClusterCount.lean`).
2. (new) Under **any** probability measure `μ` on `Config V`,
   `E_μ κ = Σ_{x ∈ V} E_μ[1/|K(x)|]`.

Sketch of the area lemma (state it for any finite measure, or any measure for which the proof
works, if that is free):
```lean
theorem integral_card_connectedComponent_eq_sum [Fintype V] (μ : Measure (Config V))
    [IsFiniteMeasure μ] :
    ∫ ω, (Nat.card (openGraph ω).ConnectedComponent : ℝ) ∂μ =
      ∑ v, ∫ ω, 1 / ((cluster ω v).ncard : ℝ) ∂μ
```
Tagged statement (in the Tags file): the conjunction of 1 and of 2 for every probability
measure `μ` (`[IsProbabilityMeasure μ]`), proved by a term from the area lemmas.
`integral_card_connectedComponent` (the `law q` case) should become a one-line corollary of
the new lemma; do not change its statement.

Hints: `integral_finset_sum`; every function on the finite configuration space is measurable
and bounded (check what `Config V`'s measurable space gives for finite `V`, and search for an
existing `Integrable.of_finite`-type lemma).

## Owned files
- `PercLib/Percolation/Bond/ClusterCount.lean` (append; do not change existing statements
  except re-proving `integral_card_connectedComponent` as a corollary).
- New `PercLib/Percolation/Bond/Tags/ClusterCountAnyLaw.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

The open task `component-count-edge-insert` also appends to `ClusterCount.lean`: do not take both
at once, and if both are in progress, coordinate through the two pull requests.

## Allowed inputs
`PercLib/Percolation/Bond/ClusterCount.lean`, `PercLib/Percolation/Bond/Basic.lean`, mathlib;
wiki assertion ZAIH.

## Stop condition
ZAIH tagged and proved, modules built with `--wfail`; or the statement is found false as
written (report it).

## Hand-off
Pull request description: the tagged statement in full, the area lemma(s) added, what was
searched, build result.
