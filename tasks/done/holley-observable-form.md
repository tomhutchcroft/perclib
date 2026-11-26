---
id: holley-observable-form
title: Holley's inequality for increasing observables
difficulty: medium
kind: interface
labels: []
---

# Holley's inequality for increasing observables

Being done by the project's own agents; do not start it.

## Goal
Prove wiki assertion **KB49** (article `harris-inequality`) in full and tag it. The library has
Holley's comparison for increasing **events** (`measure_le_of_holley`,
`PercLib/Probability/FKG.lean`); the assertion compares the expectations of every increasing
real function.

## Target
Let `E` be finite and `μ, ν` probability measures on `Set E` (configurations) such that
`μ{S} ν{T} ≤ μ{S ∩ T} ν{S ∪ T}` for all `S, T ⊆ E`. Then
`E_μ[f] ≤ E_ν[f]` for every increasing (monotone for `⊆`) function `f : Set E → ℝ`,
and in particular `μ(A) ≤ ν(A)` for every increasing event `A`. Neither measure needs full
support.

Sketch of the area lemma:
```lean
theorem integral_le_integral_of_holley [Finite E] (μ ν : Measure (Set E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ ω η : Set E, μ {ω} * ν {η} ≤ μ {ω ∩ η} * ν {ω ∪ η})
    {f : Set E → ℝ} (hf : Monotone f) : ∫ ω, f ω ∂μ ≤ ∫ ω, f ω ∂ν
```
Tagged statement: the conjunction of the observable form and the event form (the latter is
`measure_le_of_holley`).

Two routes: the layer-cake formula from the event form (for `f ≥ 0`, then add a constant), or
mathlib's four-functions theorem with `a = u f`, `b = v`, `c = u`, `d = v f` as in the article.
Search mathlib first (`four_functions_theorem`, `Finset.four_functions_theorem`, Holley,
`holley`): if mathlib already has the observable form, the task is a translation.

## Owned files
- `PercLib/Probability/FKG.lean` (append only).
- New `PercLib/Probability/Tags/HolleyObservable.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/FKG.lean`, `PercLib/Probability/LayerCake.lean`, mathlib; wiki assertion
KB49.

## Stop condition
KB49 tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemma(s), what was searched (in
particular in mathlib), build result.
