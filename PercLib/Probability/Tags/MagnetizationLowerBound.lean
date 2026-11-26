/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the magnetization lower bound obtained by integrating a
differential inequality from the positive-field limit. The statement is proved in the
imported module; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.MagnetizationLowerBound

/-!
# Magnetization lower bound: statement form

The theorem restates `sqrt_sub_le_magnetization_of_le_deriv` from
`PercLib.Probability.MagnetizationLowerBound`.

## Main results

* `magnetization_lower_bound_of_differential_inequality`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- Let `T ∈ {1, 2, …, ∞}` be a cluster volume with `P(T < ∞) > 0` and magnetization
`m(γ) = P(T = ∞) + ∑_{k ≥ 1} (1 - (1 - γ)^k) P(T = k)` for `0 < γ < 1`. If, for some `A ≥ 0`,
`m ≤ γ m' + m² + A m² m'` on `(0, 1)`, then with `K = A + 1` and `u = 1 / E[T; T < ∞]`
(`1 / ∞ = 0`), `m(γ) ≥ √(γ / K + (u / (2K))²) - u / (2K)` for every `0 < γ < 1`. -/
@[tag "ZDVK"]
theorem magnetization_lower_bound_of_differential_inequality [IsProbabilityMeasure μ]
    (hT : Measurable T) (hT1 : ∀ ω, 1 ≤ T ω) (hfin : 0 < μ {ω | T ω ≠ ⊤}) {m : ℝ → ℝ}
    (hm : ∀ γ ∈ Ioo (0 : ℝ) 1,
      m γ = μ.real {ω | T ω = ⊤} + ∑' k : ℕ, (1 - (1 - γ) ^ k) * μ.real {ω | T ω = k})
    {A : ℝ} (hA : 0 ≤ A)
    (hineq : ∀ γ ∈ Ioo (0 : ℝ) 1,
      m γ ≤ γ * deriv m γ + m γ ^ 2 + A * m γ ^ 2 * deriv m γ)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    √(γ / (A + 1) + ((∫⁻ ω in {ω | T ω ≠ ⊤}, (T ω : ℝ≥0∞) ∂μ)⁻¹.toReal / (2 * (A + 1))) ^ 2) -
        (∫⁻ ω in {ω | T ω ≠ ⊤}, (T ω : ℝ≥0∞) ∂μ)⁻¹.toReal / (2 * (A + 1)) ≤ m γ :=
  sqrt_sub_le_magnetization_of_le_deriv hT hT1 hfin hm hA hineq hγ

end PercLib.Probability
