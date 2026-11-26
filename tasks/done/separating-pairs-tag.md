---
id: separating-pairs-tag
title: Closed pair boundaries and separating pair sets (definition tag)
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Closed pair boundaries and separating pair sets (definition tag)

## Goal
Tag the definition assertion **GA03** (article `closed-separators`). The library already proves
the characterisations of non-connection by closed boundaries and closed separating pair sets
(`PercLib/Percolation/Bond/ClosedCertificates.lean`); GA03 fixes the two notions they use and
records their elementary properties.

## Target
For `C ⊆ V` its pair boundary is `δC = {s(a,b) | a ∈ C, b ∉ C}`, closed in `ω` when
`Disjoint δC ω`. A set `P` of pairs separates `x` from `y` when every walk from `x` to `y` in the
complete graph `⊤ : SimpleGraph V` uses a pair of `P`; this is the spelling in
`not_mem_conn_iff_exists_closed_separating_pairs`. Write both notions inline (no new `def`).
1. No pair of `δC` is a loop: `∀ e ∈ δC, ¬ e.IsDiag`.
2. No pair used by a walk of `⊤` is a loop.
3. No set of pairs separates a vertex from itself (the length-zero walk).

Sketch:
```lean
theorem pairBoundary_not_isDiag_and_not_separates_self (C : Set V) :
    (∀ e ∈ {e : Sym2 V | ∃ a ∈ C, ∃ b ∉ C, e = s(a, b)}, ¬ e.IsDiag) ∧
    (∀ {x y : V} (w : (⊤ : SimpleGraph V).Walk x y), ∀ e ∈ w.edges, ¬ e.IsDiag) ∧
    (∀ (P : Set (Sym2 V)) (x : V),
      ¬ ∀ w : (⊤ : SimpleGraph V).Walk x x, ∃ e ∈ w.edges, e ∈ P)
```
For 2, mathlib has `SimpleGraph.Walk.edges_subset_edgeSet` and
`SimpleGraph.not_isDiag_of_mem_edgeSet`.

## Owned files
- New `PercLib/Percolation/Bond/SeparatingPairs.lean` (area lemmas).
- New `PercLib/Percolation/Bond/Tags/SeparatingPairs.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/ClosedCertificates.lean`, `PercLib/Percolation/Bond/Basic.lean`,
mathlib; wiki assertion GA03.

## Stop condition
GA03 tagged, modules built with `--wfail`.

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
