/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the event-level entropy comparison. The statement is assembled from
lemmas proved in `PercLib.Probability.BernoulliDivergence`, which uses mathlib's
`InformationTheory.klDiv` and its data processing inequality; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.BernoulliDivergence

/-!
# Event-level entropy comparison: statement form

For probability laws `μ, ν` on a countable type and an event `A`, with `a = μ A`, `b = ν A`:
`d(a‖b) ≤ D(μ‖ν)`, `|a − b|² ≤ 2 max{a,b} d(a‖b)`, and hence
`|μ A − ν A|² ≤ 2 max{μ A, ν A} D(μ‖ν)` when `D(μ‖ν) < ∞`. Here `D` is mathlib's `klDiv` and
`d(a‖b)` is the `klDiv` of the Bernoulli laws `Ber(1, 0, a)` and `Ber(1, 0, b)`, valued in
`ℝ≥0∞`: it equals the explicit formula for `0 < b < 1` and is `∞` for `b ∈ {0,1}`, `a ≠ b`.

## Main results

* `event_entropy_comparison`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace PercLib.Probability

/-- Event-level entropy comparison: data processing for the indicator of `A`, the quadratic
bound for the Bernoulli divergence (in `ℝ≥0∞`, where `0 · ∞ = 0` covers `a = b = 0`), and the
resulting bound for `|μ A − ν A|²` when the divergence is finite. -/
@[tag "58HC"]
theorem event_entropy_comparison {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set Ω) :
    klDiv Ber((1 : ℝ), 0, ⟨μ.real A, by simp⟩) Ber((1 : ℝ), 0, ⟨ν.real A, by simp⟩) ≤
        klDiv μ ν ∧
      ENNReal.ofReal ((μ.real A - ν.real A) ^ 2) ≤
        2 * ENNReal.ofReal (max (μ.real A) (ν.real A)) *
          klDiv Ber((1 : ℝ), 0, ⟨μ.real A, by simp⟩) Ber((1 : ℝ), 0, ⟨ν.real A, by simp⟩) ∧
      (klDiv μ ν ≠ ∞ →
        (μ.real A - ν.real A) ^ 2 ≤ 2 * max (μ.real A) (ν.real A) * (klDiv μ ν).toReal) :=
  ⟨klDiv_bernoulliMeasure_le_klDiv μ ν A.to_countable.measurableSet,
    ofReal_sq_sub_le_two_mul_max_mul_klDiv_bernoulliMeasure (one_ne_zero (α := ℝ))
      ⟨μ.real A, by simp⟩ ⟨ν.real A, by simp⟩,
    sq_measureReal_sub_le_two_mul_max_mul_toReal_klDiv μ ν A.to_countable.measurableSet⟩

end PercLib.Probability
