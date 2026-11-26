---
id: schur-product-kernels
title: Schur product of positive kernels on a countable set, and its operator norm
difficulty: hard
kind: interface
labels: []
---

# Schur product of positive kernels on a countable set, and its operator norm

## Goal
Prove wiki assertion **TAB8** (article `connection-kernels`) and tag it: the entrywise (Schur)
product of two positive semidefinite kernels on a countable set is positive semidefinite, and
for bounded kernels `‖S ∘ T‖ ≤ ‖S‖ ‖T‖`. The connection-kernel positivity results build on these
two facts. `70KD` and `UZ7J` are covered by the claimed task `connection-kernel-tags` and are
not part of this task.

## Target
Kernels are functions `S T : V → V → ℝ` on a countable type `V`; `S ∘ T` is `(x,y) ↦ S x y * T x y`.
1. If every finite principal submatrix of `S` and of `T` is positive semidefinite, so is every
   finite principal submatrix of `S ∘ T`. No boundedness is assumed. (This is the convention of
   `posSemidef_connProb`, `PercLib/Percolation/Bond/ConnectionKernel.lean`.)
2. If `S` and `T` are bounded operators on `ℓ²(V)` with norms at most `a` and `b`, then `S ∘ T`
   defines a bounded operator of norm at most `a b`.

For 1, mathlib already has the finite Schur product theorem `Matrix.PosSemidef.hadamard`
(`Mathlib/Analysis/Matrix/Order.lean`); the countable statement reduces to it. For 2, state
boundedness through finitely supported vectors, so that no operator on `ℓ²` has to be
constructed in the statement:
```lean
-- "the bilinear form of S on finitely supported vectors is bounded by a"
∀ (s : Finset V) (u w : V → ℝ),
  |∑ x ∈ s, ∑ y ∈ s, u x * S x y * w y| ≤
    a * Real.sqrt (∑ x ∈ s, u x ^ 2) * Real.sqrt (∑ y ∈ s, w y ^ 2)
```
and conclude the same for `S ∘ T` with `a * b`. If you prefer `lp (fun _ : V => ℝ) 2 →L[ℝ] …`,
say why in the pull request and check that the two forms agree. The finite-dimensional core is
`‖A ∘ B‖ ≤ ‖A‖ ‖B‖` for the `ℓ²` operator norm of real matrices; the article proves it by
compressing `A ⊗ B` (mathlib's `Matrix.kronecker`) with the isometry `δ_x ↦ δ_x ⊗ δ_x`. Search
mathlib (`Matrix.l2OpNorm…`, `Matrix.kronecker`, `Mathlib/Analysis/CStarAlgebra/Matrix.lean`)
for the operator norm and any existing Hadamard norm bound before writing one.

Tagged statement: the conjunction of 1 and 2.

## Owned files
- New `PercLib/Analysis/SchurProduct.lean` (area lemmas).
- New `PercLib/Analysis/Tags/SchurProduct.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Analysis/HadamardPowers.lean`, `PercLib/Percolation/Bond/ConnectionKernel.lean` (for the
positivity convention), mathlib; wiki assertion TAB8 (its proof uses no other assertion).

## Stop condition
TAB8 tagged and proved, modules built with `--wfail`. If only part 1 is done, open the pull
request as a draft with part 1 and say what blocks part 2; never tag part 1 alone as TAB8.

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
