/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the integrated-susceptibility assertions 6PGV, TC6Q and W9IY,
proved from `LogarithmicCorrections.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.LogarithmicCorrections

/-!
# Integrated susceptibility: correspondence

Wiki correspondence for the logarithmic correction bounds of
`PercLib/Analysis/LogarithmicCorrections.lean`.

## Main results

* `integrated_susceptibility_bounds`
* `integrated_susceptibility_bound_of_mul_sub`
* `susceptibility_upper_bounds_of_log_diagram`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-- **6PGV.** Let `0 ≤ β₀ < β_c`, `χ > 0` nondecreasing and locally absolutely continuous on
`(β₀, β_c)`, `D ≥ 1` measurable and `χ' ≥ (χ - D)₊²/(3β²D²)` a.e. on `(β₀, β_c)`. Then
`χ(β) ≤ (1 + 2(β_c - β)/(3ββ_c)) (∫_β^{β_c} ds/(3s²D(s)²))⁻¹` for every `β ∈ (β₀, β_c)`, and if
`D(β_c - u) ≤ C (log(1/u))^a` for small `u > 0` (`C > 0`, `a ≥ 0`), then
`χ(β_c - ε) = O(ε⁻¹ (log(1/ε))^{2a})` as `ε ↓ 0`. -/
@[tag "6PGV"]
theorem integrated_susceptibility_bounds {β₀ βc : ℝ} {χ D : ℝ → ℝ} (hβ₀ : 0 ≤ β₀)
    (hlt : β₀ < βc) (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      max (χ β - D β) 0 ^ 2 / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β) :
    (∀ β ∈ Ioo β₀ βc,
      χ β ≤ (1 + 2 * (βc - β) / (3 * β * βc)) * (∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2))⁻¹) ∧
    (∀ {C a : ℝ}, 0 < C → 0 ≤ a → (∀ᶠ u in 𝓝[>] 0, D (βc - u) ≤ C * Real.log (1 / u) ^ a) →
      (fun ε => χ (βc - ε)) =O[𝓝[>] 0] fun ε => ε⁻¹ * Real.log (1 / ε) ^ (2 * a)) :=
  ⟨fun _ hβ => le_of_deriv_ge_sq_div hβ₀ hpos hmono hac hD hD1 hder hβ,
    fun hC ha h => isBigO_of_deriv_ge_sq_div hβ₀ hlt hpos hmono hac hD hD1 hder hC ha h⟩

/-- **TC6Q.** Let `0 ≤ β₀ < β_c`, `χ > 0` nondecreasing and locally absolutely continuous on
`(β₀, β_c)`, `D ≥ 1` measurable and `χ' ≥ χ(χ - D)/(3β²D²)` a.e. on `(β₀, β_c)`. Then for every
`β ∈ (β₀, β_c)`, `χ(β) ≤ (1 + (β_c - β)/(3ββ_c)) (∫_β^{β_c} ds/(3s²D(s)²))⁻¹`, and the integral
is finite (the integrand is integrable) and strictly positive. -/
@[tag "TC6Q"]
theorem integrated_susceptibility_bound_of_mul_sub {β₀ βc : ℝ} {χ D : ℝ → ℝ} (hβ₀ : 0 ≤ β₀)
    (_hlt : β₀ < βc) (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      χ β * (χ β - D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β) :
    ∀ β ∈ Ioo β₀ βc,
      χ β ≤ (1 + (βc - β) / (3 * β * βc)) * (∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2))⁻¹ ∧
      IntervalIntegrable (fun s => 1 / (3 * s ^ 2 * D s ^ 2)) volume β βc ∧
      0 < ∫ s in β..βc, 1 / (3 * s ^ 2 * D s ^ 2) :=
  fun _ hβ => ⟨le_of_deriv_ge_mul_sub_div hβ₀ hpos hmono hac hD hD1 hder hβ,
    intervalIntegrable_and_integral_pos_inv_three_sq_mul_sq hβ₀ hD hD1 hβ⟩

/-- **W9IY.** Under the hypotheses of TC6Q, let `C > 0`, `a ≥ 0` and
`0 < ε₀ < min(e⁻¹, β_c - β₀)` with `D(β_c - u) ≤ C (log(1/u))^a` for `0 < u < ε₀`. Then there are
`C' > 0` and `ε₁ > 0` with `χ(β_c - ε) ≤ C' ε⁻¹ (log(1/ε))^{2a}` for `0 < ε < ε₁`. In particular,
if `D(β_c - u) ≤ C` for `0 < u < ε₀`, then `χ(β_c - ε) ≤ C' ε⁻¹` for `0 < ε < ε₁`. -/
@[tag "W9IY"]
theorem susceptibility_upper_bounds_of_log_diagram {β₀ βc : ℝ} {χ D : ℝ → ℝ} (hβ₀ : 0 ≤ β₀)
    (hlt : β₀ < βc) (hpos : ∀ β ∈ Ioo β₀ βc, 0 < χ β) (hmono : MonotoneOn χ (Ioo β₀ βc))
    (hac : ∀ p q, β₀ < p → p ≤ q → q < βc → AbsolutelyContinuousOnInterval χ p q)
    (hD : Measurable D) (hD1 : ∀ β ∈ Ioo β₀ βc, 1 ≤ D β)
    (hder : ∀ᵐ β, β ∈ Ioo β₀ βc →
      χ β * (χ β - D β) / (3 * β ^ 2 * D β ^ 2) ≤ deriv χ β)
    {C ε₀ : ℝ} (hC : 0 < C) (hε₀ : 0 < ε₀) (_hε₀' : ε₀ < min (Real.exp (-1)) (βc - β₀)) :
    (∀ {a : ℝ}, 0 ≤ a → (∀ u, 0 < u → u < ε₀ → D (βc - u) ≤ C * Real.log (1 / u) ^ a) →
      ∃ C' > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
        χ (βc - ε) ≤ C' * (ε⁻¹ * Real.log (1 / ε) ^ (2 * a))) ∧
    ((∀ u, 0 < u → u < ε₀ → D (βc - u) ≤ C) →
      ∃ C' > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → χ (βc - ε) ≤ C' * ε⁻¹) :=
  ⟨fun ha h => exists_le_inv_mul_log_rpow_of_deriv_ge_mul_sub_div hβ₀ hlt hpos hmono hac
      hD hD1 hder hC ha hε₀ h,
    fun h => exists_le_inv_of_deriv_ge_mul_sub_div hβ₀ hlt hpos hmono hac hD hD1 hder hC hε₀ h⟩

end PercLib.Analysis
