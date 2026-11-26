---
id: disjoint-union-both-sides
title: Percolation on a disjoint union with null cross pairs, for both sides
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Percolation on a disjoint union with null cross pairs, for both sides

## Goal
Prove wiki assertion **WD2J** (article `product-symmetries`) in full and tag it. The library has
the two-point and susceptibility identities only for the left inclusion `Sum.inl`; the assertion
states them for both sides.

## Target
Let `V₁, V₂` be countable, `q` a profile on `Sym2 (V₁ ⊕ V₂)` with `q s(inl a, inr b) = 0` for all
`a, b`, and `q_j` its restriction to side `j` (`fun e => q (Sym2.map Sum.inl e)` and the same with
`Sum.inr`). Then:
1. almost surely every full cluster lies in one side, with
   `K_{ι_j(x)}(ω) = ι_j(K_x(ω_j))` for `j = 1, 2`;
2. for each side, `τ_q(ι_j x, ι_j y) = τ_{q_j}(x, y)`, `θ_q(ι_j x) = θ_{q_j}(x)`,
   `χ_q(ι_j x) = χ_{q_j}(x)`;
3. `τ_q(ι₁ x, ι₂ y) = 0`;
4. `Θ = 1 − (1 − Θ₁)(1 − Θ₂)` for the probabilities that some infinite cluster exists.

Existing (`PercLib/Percolation/Bond/DisjointUnion.lean`): `ae_no_cross`, `cluster_inl_eq`,
`cluster_inr_eq`, `tau_inl_inl`, `tau_inl_inr`, `law_cluster_inl_infinite`,
`law_cluster_inr_infinite`, `chi_inl`, `law_exists_cluster_infinite_sum`. Missing: `tau_inr_inr`
and `chi_inr` (prove them by transport along `Sum.swap`, or by copying the `inl` proofs if that
is shorter, but do not duplicate a general lemma), and the almost-sure form of 1 if only the
deterministic form is stated. Tagged statement: the conjunction of 1-4 for both sides.

## Owned files
- `PercLib/Percolation/Bond/DisjointUnion.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/DisjointUnion.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/DisjointUnion.lean` and its imports, mathlib; wiki assertion WD2J.

## Stop condition
WD2J tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
