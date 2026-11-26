---
id: open-degree-counts
title: Open degree and incident-coordinate counts (definition tag)
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Open degree and incident-coordinate counts (definition tag)

## Goal
Tag the definition assertion **PMHN** (article `open-degree-laws`): the open degree `D_v`, the
count `N_F(v)` of open pair coordinates from `v` into a finite set `F`, and the elementary facts
the article records about them. The other assertions of the article (`SZLN`, `TOTD`, `TEYJ`, …)
are already tagged in `PercLib/Percolation/Bond/Tags/CoreOpenDegree.lean`; PMHN is the one
left.

## Target
For a configuration `ω` on `V` and a vertex `v`:
1. `D_v` is `{w | (openGraph ω).Adj v w}.encard` (the spelling the library already uses).
2. For `w ≠ v`, the adjacency event is the one-coordinate cylinder `{ω | s(v,w) ∈ ω}`, it is
   measurable and has probability `q(v,w)` under `law q` (`setOf_adj_eq`, `measurableSet_adj`,
   `law_adj` in `PercLib/Percolation/Bond/Degree.lean`).
3. Self-adjacency is impossible, whatever the diagonal coordinate: `¬ (openGraph ω).Adj v v`.
4. For a finite set `F`, with `N_F(v) = #{w ∈ F | s(v,w) ∈ ω}` (this counts the diagonal pair
   when `v ∈ F`), the degree inside `F`, `#{w ∈ F | Adj v w}`, equals `N_{F \ {v}}(v)`.
5. `w ↦ s(v,w)` is injective, so distinct `w` give distinct pair coordinates.

Write `N_F(v)` inline as `(F.filter fun w => s(v, w) ∈ ω).card` (no new `def`). Sketch:
```lean
theorem card_filter_adj_eq_card_filter_erase (ω : Config V) (v : V) (F : Finset V) :
    (F.filter fun w => (openGraph ω).Adj v w).card =
      ((F.erase v).filter fun w => s(v, w) ∈ ω).card
```
Tagged statement: the conjunction of 2–5 (1 fixes notation and goes in the docstring), by a
term from the area lemmas.

## Owned files
- New `PercLib/Percolation/Bond/IncidentCounts.lean` (area lemmas for 4 and anything missing).
- New `PercLib/Percolation/Bond/Tags/OpenDegreeCounts.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/Degree.lean`, `PercLib/Percolation/Bond/Basic.lean`, mathlib
(`Sym2`, `SimpleGraph.fromEdgeSet`); wiki assertion PMHN.

## Stop condition
PMHN tagged, modules built with `--wfail`.

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
