---
id: erdos-renyi-mean-susceptibility
title: Subcritical bound for the mean susceptibility of G(n,p)
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Subcritical bound for the mean susceptibility of G(n,p)

## Goal
Prove wiki assertion **MIQ7** (article `finite-random-graphs`) and tag it. The library already
bounds the susceptibility of every root of the complete graph; the assertion is the bound for
the root-averaged susceptibility `χ̄ = (1/n) Σ_v E|K_v|`, which `PXP9` uses.

## Target
On `Fin n`, let the profile `q` equal `p` on every pair of distinct vertices (the diagonal is
irrelevant). If `(n − 1) p < 1`, then
`χ̄ = (1/n) Σ_{v} χ(v) ≤ 1 / (1 − (n − 1) p)`.

The per-root bound exists: `chi_completeGraph_le` in `PercLib/Models/FiniteGraph.lean` (its
hypotheses fix the spelling of `(n − 1) p` in `ℝ≥0∞`). Sketch of the area lemma:
```lean
theorem sum_chi_div_le_of_completeGraph (n : ℕ) (q : Sym2 (Fin n) → unitInterval)
    (p : unitInterval) (hq : ∀ v w, v ≠ w → q s(v, w) = p)
    (hp : ((n - 1 : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) < 1) :
    (∑ x, chi q x) / n ≤ (1 - ((n - 1 : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞))⁻¹
```
Decide what the statement says at `n = 0` (the average of an empty family) and keep the
hypotheses honest: if `n ≥ 1` is needed, add it and say so. Tagged statement: the averaged bound,
by a term from the area lemma.

## Owned files
- New `PercLib/Models/ErdosRenyi.lean` (area lemma; later Erdős–Rényi results may append here).
- New `PercLib/Models/Tags/ErdosRenyi.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Models/FiniteGraph.lean`, `PercLib/Percolation/Bond/RowSum.lean`,
`PercLib/Percolation/Bond/Basic.lean`, mathlib; wiki assertions MIQ7 and 53Z9 (the row-sum
bound, tagged in `PercLib/Percolation/Bond/Tags/SubcriticalBound.lean`).

## Stop condition
MIQ7 tagged and proved, modules built with `--wfail`; or the statement is found false as
written (report it).

## Hand-off
Pull request description: the tagged statement in full, the area lemma, what was searched,
build result.
