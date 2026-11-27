---
id: galton-watson-dwass
title: Dwass's formula for the Galton-Watson total progeny from one ancestor
difficulty: hard
kind: interface
labels: []
---

# Dwass's formula for the Galton-Watson total progeny from one ancestor

## Goal
Prove and tag wiki assertion **RL1L** (article `branching-processes`): for the Galton–Watson
process with one ancestor and offspring law `p`, and every `n ≥ 1`,
`P(T = n) = (1/n) P(ξ₁ + ⋯ + ξ_n = n − 1)`, on either side of criticality. Here `T` is the
library's `totalProgeny` of the generation-size process `generationSize`
(`PercLib/Probability/GaltonWatson/Defs.lean`), not a queue walk: the task includes the
identification of the generation-by-generation process with the breadth-first queue encoding.

## Target
Let `p : PMF ℕ`, `n ≥ 1`. Then
`galtonWatsonMeasure p {ω | totalProgeny ω = n} = (1/n) · P(ξ₁ + ⋯ + ξ_n = n − 1)`,
where `ξ_i` are i.i.d. with law `p` (for instance the coordinates of
`Measure.infinitePi fun _ : ℕ => p.toMeasure`, or the `n`-fold convolution of `p.toMeasure`).

Sketch (spelling free):
```lean
theorem galtonWatsonMeasure_totalProgeny_eq (p : PMF ℕ) {n : ℕ} (hn : 1 ≤ n) :
    galtonWatsonMeasure p {ω | totalProgeny ω = n} =
      (n : ℝ≥0∞)⁻¹ * (Measure.infinitePi fun _ : ℕ => p.toMeasure)
        {ξ | ∑ i ∈ Finset.range n, ξ i = n - 1}
```
Route: (a) on `{totalProgeny ω = n}`, list the offspring counts of the `n` individuals in
breadth-first order; this map is measurable and its law is that of the first `n` coordinates of
an i.i.d. sequence restricted to the event that the queue walk `1 + Σ_{i ≤ k}(ξ_i − 1)` first
hits `0` at `k = n`; (b) the cycle lemma (the article's proof) gives the factor `1/n`.

Step (b) is exactly the `m = 1` case of task `dwass-total-progeny` (wiki assertion UPOZ, owned
files `PercLib/Probability/TotalProgeny.lean` and `PercLib/Probability/Tags/TotalProgeny.lean`).
Do not prove a second cycle lemma: if that task has merged, import its result; if it is open or
claimed, do step (a) first and coordinate with its author in the pull request. The new work of
this task is step (a).

## Owned files
- New `PercLib/Probability/GaltonWatson/BreadthFirst.lean` (the breadth-first encoding and
  step (a)).
- New `PercLib/Probability/Tags/GaltonWatsonDwass.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/GaltonWatson/Defs.lean`, the result of task `dwass-total-progeny` once
merged, mathlib (`Measure.infinitePi`, `ProbabilityTheory.iIndepFun`); wiki assertions RL1L and
UPOZ.

## Stop condition
RL1L tagged, built with `--wfail`; or step (a) is done and step (b) waits for
`dwass-total-progeny` (submit step (a) untagged and say so).

## Hand-off
Pull request description: the tagged statement in full, the lemmas it restates (including the
UPOZ result used), build result.
