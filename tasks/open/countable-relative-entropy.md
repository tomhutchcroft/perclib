---
id: countable-relative-entropy
title: Relative entropy of laws on a countable set as a sum
difficulty: medium
kind: interface
labels: []
---

# Relative entropy of laws on a countable set as a sum

## Goal
Tag the definition assertion **UVKE** (article `entropy-comparison`): for probability laws
`μ, ν` on a countable set `S`, `D(μ‖ν) = Σ_s μ(s) log(μ(s)/ν(s))`, with the conventions that a
term with `μ(s) = 0` is zero and a term with `μ(s) > 0 = ν(s)` is `+∞`, the sum being
well-defined in `[0, ∞]`. Mathlib already has the Kullback–Leibler divergence
`InformationTheory.klDiv`; the task identifies it with the countable sum, so the article's
`D(μ‖ν)` is `klDiv` and no new definition is introduced.

## Target
Let `S` be countable with `MeasurableSingletonClass`, and `μ ν : PMF S`. Write
`f s = (μ s).toReal * Real.log ((μ s).toReal / (ν s).toReal)`.
1. If some `s` has `μ s ≠ 0` and `ν s = 0`, then `klDiv μ.toMeasure ν.toMeasure = ⊤`.
2. Otherwise, the negative part of `f` is summable (`t log t ≥ -1/e`), and
   `klDiv μ.toMeasure ν.toMeasure = ENNReal.ofReal (∑' s, f s)` if `f` is summable, and `= ⊤` if
   it is not.
3. In the summable case `0 ≤ ∑' s, f s` (log-sum / Gibbs inequality; mathlib's `klDiv` is
   nonnegative by construction, so this may follow from 2 together with the real formula for
   `klDiv` under absolute continuity).

Sketch (spelling free):
```lean
theorem klDiv_toMeasure_eq [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ ν : PMF S) :
    InformationTheory.klDiv μ.toMeasure ν.toMeasure =
      if (∃ s, μ s ≠ 0 ∧ ν s = 0) ∨
          ¬ Summable (fun s => (μ s).toReal * Real.log ((μ s).toReal / (ν s).toReal)) then ⊤
      else ENNReal.ofReal (∑' s, (μ s).toReal * Real.log ((μ s).toReal / (ν s).toReal))
```
plus the summability of the negative part and the nonnegativity of the sum as separate named
lemmas. Area lemmas in the area file; the tagged conjunction (or single statement) in `Tags/`.
Compare `PercLib/Probability/BernoulliDivergence.lean`, which computes `klDiv` for two-point laws,
and reuse its approach.

## Owned files
- New `PercLib/Probability/CountableDivergence.lean` (area lemmas).
- New `PercLib/Probability/Tags/CountableDivergence.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
Mathlib (`InformationTheory.klDiv` and its API, `PMF`, `Real.mul_log`-type lemmas such as
the lower bound of `x log x`), `PercLib/Probability/BernoulliDivergence.lean`; wiki assertion
UVKE.

## Stop condition
UVKE tagged, built with `--wfail`; or a convention of the article is found not to match
`klDiv` (report the discrepancy instead of adjusting the statement).

## Hand-off
Pull request description: the tagged statement in full, the lemmas it restates, what was
searched in mathlib, build result.
