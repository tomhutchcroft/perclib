/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the mesoscopic-tail-transfer assertion 19IN, proved from
`RiccatiLinearError.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.RiccatiLinearError

/-!
# Riccati propagation with a linear error: correspondence

Wiki correspondence for subthreshold Riccati propagation under a linear error term.

## Main results

* `riccati_linear_error_bounds`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Real

namespace PercLib.Analysis

/-- **19IN.** Let `α, A > 0`, `0 ≤ e < α`, `r₀ > 0`, and let `f > 0` be absolutely continuous
on every compact interval of `[r₀, ∞)` with `f' ≤ A t^{-α-1} f² + e t⁻¹ f` a.e. on `[r₀, ∞)`.
If `r ≥ r₀` and `f r ≤ (α - e) r^α / A`, then for every `R ≥ r` the bracket
`B(R) = 1/f r - A/((α - e) r^α) + A/((α - e) r^α) (r/R)^{α-e}` is positive and
`f R ≤ (R/r)^e B(R)⁻¹`. If `0 < θ < 1` and `f r ≤ (1 - θ)(α - e) r^α / A`, then
`f R ≤ θ⁻¹ (R/r)^e f r` for every `R ≥ r`. -/
@[tag "19IN"]
theorem riccati_linear_error_bounds {α A e r₀ : ℝ} {f : ℝ → ℝ} (_hα : 0 < α) (hA : 0 < A)
    (_he : 0 ≤ e) (heα : e < α) (hr₀ : 0 < r₀) (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hac : ∀ p q, r₀ ≤ p → p ≤ q → AbsolutelyContinuousOnInterval f p q)
    (hder : ∀ᵐ t, r₀ ≤ t → deriv f t ≤ A * t ^ (-α - 1) * f t ^ 2 + e * t⁻¹ * f t) :
    (∀ r, r₀ ≤ r → f r ≤ (α - e) * r ^ α / A → ∀ R, r ≤ R →
      0 < 1 / f r - A / ((α - e) * r ^ α) + A / ((α - e) * r ^ α) * (r / R) ^ (α - e) ∧
      f R ≤ (R / r) ^ e *
        (1 / f r - A / ((α - e) * r ^ α) + A / ((α - e) * r ^ α) * (r / R) ^ (α - e))⁻¹) ∧
    (∀ θ, 0 < θ → θ < 1 → ∀ r, r₀ ≤ r → f r ≤ (1 - θ) * (α - e) * r ^ α / A →
      ∀ R, r ≤ R → f R ≤ θ⁻¹ * (R / r) ^ e * f r) := by
  have local_hyps : ∀ r R, r₀ ≤ r → r ≤ R →
      (∀ t ∈ Icc r R, 0 < f t) ∧
      ∀ᵐ t, t ∈ Icc r R → deriv f t ≤ A * t ^ (-α - 1) * f t ^ 2 + e * t⁻¹ * f t :=
    fun r R hr _ => ⟨fun t ht => hpos t (hr.trans ht.1), by
      filter_upwards [hder] with t h ht using h (hr.trans ht.1)⟩
  refine ⟨fun r hr hfr R hrR => ?_, fun θ hθ0 _ r hr hfr R hrR => ?_⟩
  · obtain ⟨hp, hd⟩ := local_hyps r R hr hrR
    have hr0 : 0 < r := hr₀.trans_le hr
    exact ⟨one_div_sub_add_mul_rpow_pos heα hA hr0 (hr0.trans_le hrR) (hp r ⟨le_rfl, hrR⟩) hfr,
      le_rpow_mul_inv_of_deriv_le_mul_sq_add heα hA hr0 hrR (hac r R hr hrR) hp hd hfr⟩
  · obtain ⟨hp, hd⟩ := local_hyps r R hr hrR
    exact le_inv_mul_rpow_mul_of_deriv_le_mul_sq_add heα hA (hr₀.trans_le hr) hrR
      (hac r R hr hrR) hp hd hθ0 hfr

end PercLib.Analysis
