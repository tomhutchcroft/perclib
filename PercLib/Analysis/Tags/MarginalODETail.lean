/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the perturbed-Riccati remainder assertion K58A, proved from
`RiccatiComparison.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.RiccatiComparison

/-!
# The exact tail remainder for a perturbed Riccati equation

Restates results of `PercLib.Analysis.RiccatiComparison` as one tagged conjunction.

## Main results

* `PercLib.Analysis.riccati_tail_remainder`: for `f' = A (1 - h) r^{-α-1} f²` on `[r₀, ∞)`, the
  finite reciprocal identity, the closed tail formula with positive denominator when `f → ∞`,
  and `f ~ (α/A) r^α` when moreover `h → 0`.
-/

@[expose] public section
noncomputable section

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-- **K58A.** Let `A, α, r₀ > 0`, let `f > 0` be differentiable on `[r₀, ∞)` (one-sided at `r₀`)
with derivative `f'`, and let `h` be measurable and bounded on `[r₀, ∞)` with
`f' = A (1 - h) r^{-α-1} f²` there. Then for `r₀ ≤ r ≤ R`,
`1/f r = 1/f R + (A/α)(r^{-α} - R^{-α}) - A ∫_r^R h s s^{-α-1} ds`. If moreover `f → ∞`, then
for every `r ≥ r₀` the quantity `1 - α r^α ∫_r^∞ h s s^{-α-1} ds` is strictly positive and
`f r = (α/A) r^α / (1 - α r^α ∫_r^∞ h s s^{-α-1} ds)`; and if in addition `h → 0`, then
`f ~ (α/A) r^α`. -/
@[tag "K58A"]
theorem riccati_tail_remainder {f f' h : ℝ → ℝ} {A α r₀ : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hr₀ : 0 < r₀) (hderiv : ∀ x, r₀ ≤ x → HasDerivWithinAt f (f' x) (Ici r₀) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hode : ∀ x, r₀ ≤ x → f' x = A * (1 - h x) * x ^ (-α - 1) * f x ^ 2)
    (hmeas : Measurable ((Ici r₀).domRestrict h)) (hbdd : ∃ C, ∀ x, r₀ ≤ x → |h x| ≤ C) :
    (∀ r R, r₀ ≤ r → r ≤ R →
      (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1)) ∧
    (Tendsto f atTop atTop →
      (∀ r, r₀ ≤ r → 0 < 1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1) ∧
        f r = α / A * r ^ α / (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))) ∧
      (Tendsto h atTop (𝓝 0) → f ~[atTop] fun r => α / A * r ^ α)) := by
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨fun r R hr hrR => inv_eq_of_hasDerivWithinAt hA hα hr₀ hderiv hpos hode hmeas hC hr hrR,
    fun hinf => ⟨one_sub_mul_integral_Ioi_pos_and_eq_div_of_hasDerivWithinAt hA hα hr₀ hderiv hpos
      hinf hode hmeas hC, fun hh => isEquivalent_rpow_of_hasDerivWithinAt_riccati hA hα hr₀ hderiv
      hpos hinf hode hmeas hC hh⟩⟩

end PercLib.Analysis
