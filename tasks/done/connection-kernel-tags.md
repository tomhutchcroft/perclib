---
id: connection-kernel-tags
title: Positive semidefiniteness and cubic bounds of the connection kernel (70KD, UZ7J)
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Positive semidefiniteness and cubic bounds of the connection kernel

Being done by the project's own agents; do not start it.

## Goal
Tag wiki assertions **70KD** and **UZ7J** (article `connection-kernels`). The mathematics is
already proved, untagged, in `PercLib/Percolation/Bond/ConnectionKernel.lean`; these are shared
prerequisites of the lace-expansion area (see `tasks/areas/lace-expansion.md`), so they are
wanted soon.

## Target
Write `T(x,y) = P(x ↔ y)` (in the library `tau q x y`, or `connProb μ x y` for a general measure;
use the generality the existing lemmas have and the article's front-matter `context` allows).
1. **70KD.** For every finitely supported real family `(a_x)`,
   `∑_{x,y} a_x a_y T(x,y) = E[∑_C (∑_{x∈C} a_x)²] ≥ 0`, the sum over open clusters `C`; hence
   every finite principal submatrix of `T` is positive semidefinite. Existing lemmas:
   `sum_mul_connProb_eq_integral`, `sum_mul_connProb_nonneg`, `posSemidef_connProb`.
2. **UZ7J.** If the diagonal triangles `Δ_x`, `Δ_y` are finite then
   `T³(x,y) ≤ √(Δ_x Δ_y) < ∞`, and `∑_u T(x,u)² ≤ Δ_x` for every `x`, plus any further clause
   of the wiki block. Existing lemmas: `triangle_sq_le`, `triangle_le_rpow`, `triangle_le_sqrt`,
   `tsum_connProb_sq_le_triangle`.
Read both blocks in full: if a clause has no existing lemma, prove it in the area file.

## Owned files
- `PercLib/Percolation/Bond/ConnectionKernel.lean` (append only, only if a clause is missing).
- New `PercLib/Percolation/Bond/Tags/ConnectionKernel.lean` (tagged restatements only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`main`, mathlib, the article `wiki/articles/connection-kernels.md`.

## Stop condition
Both tags stated faithfully and proved, modules built with `lake build --wfail`; or a clause is
false or under-hypothesised as written (open a "Mathematical gap" issue).

## Hand-off
Pull request description: each tagged statement with its tag, the area lemmas used, build
result. A maintainer reviews the statements against the wiki.
