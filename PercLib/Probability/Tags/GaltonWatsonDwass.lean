/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for Dwass's formula, proved in
`PercLib.Probability.GaltonWatson.Dwass`. Mathematical reference: M. Dwass, *The total
progeny in a branching process and a related random walk*, J. Appl. Probab. 6 (1969)
682–686. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.GaltonWatson.Dwass

/-!
# Galton–Watson process: Dwass's formula

## Main results

* `PercLib.Probability.totalProgeny_law_eq_inv_mul_sum_law`: for every `n ≥ 1`, the total
  progeny `T` of a Galton–Watson process satisfies `P(T = n) = n⁻¹ P(ξ₁ + ⋯ + ξₙ = n - 1)`,
  where the `ξᵢ` are independent offspring variables.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PercLib.Probability

/-- **Dwass's formula.** Let `T` be the total progeny of the Galton–Watson process with
offspring law `p`, and let `ξ₀, ξ₁, …` be independent random variables with law `p`. For
every `n ≥ 1`, `P(T = n)` equals `1/n` times the probability that `n` of the offspring
variables sum to `n - 1`. No assumption on the mean is made, so the identity holds on either
side of criticality. -/
@[tag "RL1L"]
theorem totalProgeny_law_eq_inv_mul_sum_law (p : PMF ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p.toMeasure) {n : ℕ} (hn : 1 ≤ n) :
    galtonWatsonMeasure p {ω | totalProgeny ω = n} =
      (n : ℝ≥0∞)⁻¹ * P {ω | ∑ i ∈ Finset.range n, ξ i ω = n - 1} :=
  galtonWatsonMeasure_totalProgeny_eq p P ξ hξ hind hlaw hn

end PercLib.Probability
