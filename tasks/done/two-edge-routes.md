---
id: two-edge-routes
title: Exact connection probability through a family of two-edge routes
difficulty: medium
kind: interface
labels: []
---

# Exact connection probability through a family of two-edge routes

## Goal
Prove wiki assertion **YPNG** (article `connection-paths`) in full and tag it. The library has the
homogeneous case (`tau_completeBipartite_bool`, `PercLib/Percolation/Bond/PathLowerBounds.lean`:
all route probabilities equal to `t`, zero diagonal); the assertion allows different
probabilities on every bond and an arbitrary diagonal.

## Target
On the vertex set `{x, y, z_1, …, z_k}` (all distinct; in Lean for instance `Bool ⊕ Fin k` with
`x = inl false`, `y = inl true`, `z_i = inr i`), suppose the only pairs of distinct vertices with
positive opening probability are `{x, z_i}` and `{z_i, y}`, with probabilities `a_i` and `b_i`.
Diagonal probabilities are arbitrary. Then
`τ(x, y) = 1 − ∏_{i=1}^k (1 − a_i b_i)`,
and in particular `τ(x,y) = 1 − (1 − t²)^k` when all probabilities equal `t`. Sketch:
```lean
theorem tau_twoEdgeRoutes (k : ℕ) (a b : Fin k → unitInterval)
    (q : Sym2 (Bool ⊕ Fin k) → unitInterval)
    (hxz : ∀ i, q s(Sum.inl false, Sum.inr i) = a i)
    (hzy : ∀ i, q s(Sum.inr i, Sum.inl true) = b i)
    (hzero : ∀ e, ¬ e.IsDiag → (∀ i, e ≠ s(Sum.inl false, Sum.inr i)) →
      (∀ i, e ≠ s(Sum.inr i, Sum.inl true)) → q e = 0) :
    tau q (Sum.inl false) (Sum.inl true) =
      1 - ∏ i, (1 - (unitInterval.toNNReal (a i) : ℝ≥0∞) * unitInterval.toNNReal (b i))
```
Proof (article): almost surely only host bonds are open; the routes use disjoint bonds, so the
right side is the probability that some route is open; if no route is open, the set
`{x} ∪ {z_i : {x,z_i} open}` is closed under open adjacency and avoids `y`. Use diagonal erasure
(`law_event_eq_of_offDiagonal`) for the arbitrary diagonal. Re-prove `tau_completeBipartite_bool`
as a corollary if it is short, without changing its statement. Tagged statement: the general
formula (with the homogeneous case as a second conjunct if you wish).

## Owned files
- `PercLib/Percolation/Bond/PathLowerBounds.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/TwoEdgeRoutes.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/{PathLowerBounds,Basic}.lean`, `Diagonal/Probability.lean`,
`PercLib/Probability/{ProdBernoulli,ProdBernoulliIndependence}.lean`, mathlib; wiki assertion
YPNG.

## Stop condition
YPNG tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
