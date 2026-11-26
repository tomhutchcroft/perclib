/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the cutoff-localization assertion 04ZI, proved from
`ReciprocalCutoff.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.ReciprocalCutoff

/-!
# Reciprocal cutoff bound: correspondence

Wiki correspondence for the reciprocal cutoff bounds of
`PercLib/Analysis/ReciprocalCutoff.lean`.

## Main results

* `reciprocal_cutoff_bounds`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PercLib.Analysis

/-- **04ZI.** Let `α, A, C > 0`. There are `c₁, c₂ > 0`, depending only on `α, A, C`, such that
for every `f`, positive, nondecreasing and locally absolutely continuous on `[1, ∞)` with limit
`X ∈ ℝ≥0∞`, satisfying `f r ≤ C r^α` and `f' ≤ A r^{-α-1} f²` a.e. on `[1, ∞)`, and every
`r ≥ 1`: `(1/X + (A/α) r^{-α})⁻¹ ≤ f r ≤ min (C r^α) X` (with `1/∞ = 0`) and
`c₁ min (r^α) X ≤ f r ≤ c₂ min (r^α) X`. -/
@[tag "04ZI"]
theorem reciprocal_cutoff_bounds {α A C : ℝ} (hα : 0 < α) (hA : 0 < A) (hC : 0 < C) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ (f : ℝ → ℝ) (X : ℝ≥0∞), (∀ r, 1 ≤ r → 0 < f r) →
      MonotoneOn f (Ici 1) → (∀ p q, 1 ≤ p → p ≤ q → AbsolutelyContinuousOnInterval f p q) →
      Tendsto (fun r => ENNReal.ofReal (f r)) atTop (𝓝 X) →
      (∀ r, 1 ≤ r → f r ≤ C * r ^ α) →
      (∀ᵐ s, 1 ≤ s → deriv f s ≤ A * s ^ (-α - 1) * f s ^ 2) →
      (∀ r, 1 ≤ r → ((X⁻¹).toReal + A / α * r ^ (-α))⁻¹ ≤ f r) ∧
      (∀ r, 1 ≤ r → ENNReal.ofReal (f r) ≤ min (ENNReal.ofReal (C * r ^ α)) X) ∧
      (∀ r, 1 ≤ r → ENNReal.ofReal (f r) ∈
        Icc (ENNReal.ofReal c₁ * min (ENNReal.ofReal (r ^ α)) X)
          (ENNReal.ofReal c₂ * min (ENNReal.ofReal (r ^ α)) X)) :=
  ⟨(1 + A / α)⁻¹, inv_pos.2 (by have := div_pos hA hα; positivity), max C 1,
    hC.trans_le (le_max_left _ _), fun _ _ hpos hmono hac hlim hCf hder =>
    ⟨fun _ hr => inv_le_of_deriv_le_rpow_mul_sq hα hA hpos hmono hac hlim hder hr,
      fun _ hr => ofReal_le_min_of_monotoneOn_of_tendsto hmono hlim hCf hr,
      fun _ hr => ofReal_mem_Icc_mul_min_of_deriv_le_rpow_mul_sq hα hA hpos hmono hac hlim hder
        hCf hr⟩⟩

end PercLib.Analysis
