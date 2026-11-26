/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the ghost-field transform `M(h) = E[1 - e^{-hT}]` of an
`ℕ∞`-valued random variable. Every statement is assembled from lemmas proved in the
imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.GhostTransform

/-!
# Ghost-field transform: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `ghost_series_and_bounds`
* `ghost_small_field_limits`
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PercLib.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- The ghost transform as a geometric series of tail probabilities, with the two-sided
truncation bounds at every level `N`. -/
@[tag "0NVH"]
theorem ghost_series_and_bounds (hT : Measurable T) {h : ℝ} (hh : 0 < h) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ =
      ENNReal.ofReal (1 - Real.exp (-h)) * ∑' n : ℕ,
        ENNReal.ofReal (Real.exp (-h)) ^ n * μ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} ∧
    ∀ N : ℕ, 1 ≤ N →
      ENNReal.ofReal (1 - Real.exp (-(h * N))) * μ {ω | (N : ℕ∞) ≤ T ω} ≤
        ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ ∧
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ ≤
        ENNReal.ofReal h * ∫⁻ ω, ((min (T ω) N : ℕ∞) : ℝ≥0∞) ∂μ +
          μ {ω | (N : ℕ∞) ≤ T ω} :=
  ⟨lintegral_ghost_eq_tsum hT hh, fun N _ =>
    ⟨mul_measure_le_lintegral_ghost hT hh N, lintegral_ghost_le hT hh N⟩⟩

/-- As `h ↓ 0`, the ghost transform tends to `P(T = ∞)` and `M(h)/h` tends to `E T`. -/
@[tag "8B62"]
theorem ghost_small_field_limits [IsProbabilityMeasure μ] (hT : Measurable T) :
    Tendsto (fun h : ℝ => ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ)
      (𝓝[>] 0) (𝓝 (μ {ω | T ω = ⊤})) ∧
    Tendsto (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal))))
      ∂μ) / ENNReal.ofReal h) (𝓝[>] 0) (𝓝 (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ)) :=
  ⟨tendsto_lintegral_ghost hT, tendsto_lintegral_ghost_div hT⟩

end PercLib.Probability
