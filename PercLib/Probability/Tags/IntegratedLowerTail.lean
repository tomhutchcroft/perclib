/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the integrated square-root lower bound from cubic moments. The
statement is assembled from lemmas proved in the imported module; no new definition is
introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.IntegratedLowerTail

/-!
# Integrated lower tails from cubic moments: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Probability.IntegratedLowerTail`.

## Main results

* `integrated_sqrt_lower_bound_of_cubic_moments`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

/-- Let `X t ≥ 0`, for `t` in an interval `I` with least element `t₀`, have means
`m t ∈ (0, ∞)` that are continuous and unbounded above on `I`, with `E (X t)² ≤ C (m t)³`
for a fixed `C > 0`. If `Xs` stochastically dominates every `X t`, then
`E[Xs ∧ N] ≥ √N / (2 √(2C))` for every real `N ≥ 2 C (m t₀)²`; and for every `ℕ∞`-valued `T`
stochastically dominating every `X t`, `∑_{n=1}^N P(T ≥ n) ≥ √N / (2 √(2C))` for every
integer `N` in the same range. -/
@[tag "F75G"]
theorem integrated_sqrt_lower_bound_of_cubic_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {I : Set ℝ} {t₀ : ℝ} (hI : IsLeast I t₀)
    (hIc : I.OrdConnected) (X : ℝ → Ω → ℝ) (hXm : ∀ t ∈ I, Measurable (X t))
    (_hX0 : ∀ t ∈ I, ∀ ω, 0 ≤ X t ω) (m : ℝ → ℝ≥0∞)
    (hm : ∀ t ∈ I, m t = ∫⁻ ω, ENNReal.ofReal (X t ω) ∂P)
    (hpos : ∀ t ∈ I, 0 < m t) (hfin : ∀ t ∈ I, m t < ∞) (C : ℝ) (hC : 0 < C)
    (hsq : ∀ t ∈ I, ∫⁻ ω, ENNReal.ofReal (X t ω) ^ 2 ∂P ≤ ENNReal.ofReal C * m t ^ 3)
    (hcont : ContinuousOn (fun t => (m t).toReal) I)
    (hunb : ¬BddAbove ((fun t => (m t).toReal) '' I))
    (Xs : Ω → ℝ≥0∞) (hXs : Measurable Xs)
    (hdom : ∀ t ∈ I, ∀ x : ℝ≥0∞, P {ω | x < ENNReal.ofReal (X t ω)} ≤ P {ω | x < Xs ω}) :
    (∀ N : ℝ, 2 * C * (m t₀).toReal ^ 2 ≤ N →
      ENNReal.ofReal (Real.sqrt N / (2 * Real.sqrt (2 * C))) ≤
        ∫⁻ ω, min (Xs ω) (ENNReal.ofReal N) ∂P) ∧
    (∀ T : Ω → ℕ∞, Measurable T →
      (∀ t ∈ I, ∀ x : ℝ≥0∞,
        P {ω | x < ENNReal.ofReal (X t ω)} ≤ P {ω | x < (T ω : ℝ≥0∞)}) →
      ∀ N : ℕ, 2 * C * (m t₀).toReal ^ 2 ≤ N →
        ENNReal.ofReal (Real.sqrt N / (2 * Real.sqrt (2 * C))) ≤
          ∑ n ∈ Finset.Icc 1 N, P {ω | (n : ℕ∞) ≤ T ω}) :=
  ⟨fun _ hN => le_lintegral_min_of_lintegral_sq_le P hI hIc hXm hm hpos hfin hC hsq hcont hunb
      hXs hdom hN,
    fun _ hT hdomT _ hN => le_sum_meas_le_of_lintegral_sq_le P hI hIc hXm hm hpos hfin hC hsq
      hcont hunb hT hdomT hN⟩

end PercLib.Probability
