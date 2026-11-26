---
id: increasing-events-tag
title: Increasing events and observables; connection events are increasing
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Increasing events and observables; connection events are increasing

## Goal
Tag the definition assertion **H4OA** (article `harris-inequality`). The library uses mathlib's
`IsUpperSet` and `Monotone` for the inclusion order on configurations; this task records that
convention against the wiki and states the facts the assertion makes.

## Target
Configurations `Config V = Set (Sym2 V)` are ordered by inclusion (mathlib's order on `Set`).
1. An event `A` is increasing iff `IsUpperSet A`; an observable `f : Config V → ℝ` is
   increasing iff `Monotone f`. (These are notation; put them in the docstring, and state as a
   conjunct only something with content, for example that the indicator of an increasing event
   is a monotone observable.)
2. Every connection event `conn x y` is increasing (`isUpperSet_conn`,
   `PercLib/Probability/OpenEventHarris.lean`; `conn_mono`, `PercLib/Percolation/Bond/Basic.lean`).

Measurability is not part of the assertion (H4OA only remarks that it must be proved
separately); the docstring may mention it with a pointer to `measurableSet_conn`
(`PercLib/Percolation/Bond/Basic.lean`).

Sketch:
```lean
theorem isUpperSet_conn_and_monotone_indicator (x y : V) :
    IsUpperSet (conn x y : Set (Config V)) ∧
    Monotone ((conn x y : Set (Config V)).indicator (1 : Config V → ℝ))
```
Search mathlib for the
indicator lemma (`Set.indicator_le_indicator_of_subset`, `IsUpperSet`) before writing one.

## Owned files
- New `PercLib/Percolation/Bond/Tags/IncreasingEvents.lean` (the tagged statement only; if a
  missing area lemma is needed, put it at the top of this file's companion new area file
  `PercLib/Percolation/Bond/IncreasingEvents.lean`).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/OpenEventHarris.lean`, `PercLib/Percolation/Bond/Basic.lean`, mathlib;
wiki assertion H4OA.

## Stop condition
H4OA tagged, built with `--wfail`.

## Hand-off
Pull request description: the tagged statement in full, the lemmas it restates, build result.
