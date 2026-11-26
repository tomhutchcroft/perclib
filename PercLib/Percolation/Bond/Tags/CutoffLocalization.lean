/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.SpatialMoments.LocalizationMetric

/-!
# Correspondence wrapper: a spatial moment localizes the first volume moment

All mathematical inputs are proved in
`PercLib.Percolation.Bond.SpatialMoments.LocalizationMetric`.

## Main results

* `PercLib.Probability.chi_localization_of_correlationLength_le`: the three clauses of the
  localization of the first volume moment by a correlation-length bound, for a family of
  random sets `K r` (`r ≥ 1`) with measurable membership events and finite positive mean size,
  with no coupling between scales.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Probability

/-- On a countable pseudometric vertex type with root `o`, let `K_r` (`r ≥ 1`) be random sets,
on a measurable space `Ω` with laws `μ r` (no coupling between scales is used), with measurable
membership events and finite positive mean size `χ_r = E_r|K_r|`. If for one `p > 0` the
correlation length `ξ_p(r) = (E_r[∑_{x ∈ K_r} d(o, x)^p] / χ_r)^{1/p}` satisfies
`ξ_p(r) ≤ C_p r` for every `r ≥ 1`, then, with `Z_{r,C} = |K_r \ B_{C r}|`:
for every `C > 0` and `r ≥ 1`, `E_r Z_{r,C} / χ_r ≤ (C_p / C)^p`; for every `ε > 0` one
`C > 0` gives `χ_r ≤ (1 + ε) E_r|K_r ∩ B_{C r}|` for all `r ≥ 1`; and for every `C > 0` and
`r ≥ 1`, `P_r(Z_{r,C} > 0) ≤ χ_r (C_p / C)^p`. Neither `o ∈ K_r` nor `μ r` being a
probability measure is needed. -/
@[tag "32GP"]
theorem chi_localization_of_correlationLength_le {Ω V : Type*} [MeasurableSpace Ω]
    [Countable V] [PseudoMetricSpace V] (o : V) (μ : ℝ → Measure Ω) (K : ℝ → Ω → Set V)
    (hK : ∀ r : ℝ, 1 ≤ r → ∀ x, MeasurableSet {ω | x ∈ K r ω})
    (hχ : ∀ r : ℝ, 1 ≤ r →
      0 < ∫⁻ ω, ((K r ω).encard : ℝ≥0∞) ∂μ r ∧ ∫⁻ ω, ((K r ω).encard : ℝ≥0∞) ∂μ r < ⊤)
    {p : ℝ} (hp : 0 < p) (Cp : ℝ≥0)
    (hξ : ∀ r : ℝ, 1 ≤ r →
      ((∫⁻ ω, ∑' x, (K r ω).indicator (fun x => ENNReal.ofReal (dist o x ^ p)) x ∂μ r) /
        ∫⁻ ω, ((K r ω).encard : ℝ≥0∞) ∂μ r) ^ p⁻¹ ≤ ENNReal.ofReal (Cp * r)) :
    (∀ C : ℝ, 0 < C → ∀ r : ℝ, 1 ≤ r →
      (∫⁻ ω, ((K r ω \ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂μ r) /
          ∫⁻ ω, ((K r ω).encard : ℝ≥0∞) ∂μ r ≤ ENNReal.ofReal ((Cp / C) ^ p)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ∫⁻ ω, ((K r ω).encard : ℝ≥0∞) ∂μ r ≤ ENNReal.ofReal (1 + ε) *
        ∫⁻ ω, ((K r ω ∩ Metric.closedBall o (C * r)).encard : ℝ≥0∞) ∂μ r) ∧
    (∀ C : ℝ, 0 < C → ∀ r : ℝ, 1 ≤ r →
      μ r {ω | 0 < (K r ω \ Metric.closedBall o (C * r)).encard} ≤
        (∫⁻ ω, ((K r ω).encard : ℝ≥0∞) ∂μ r) * ENNReal.ofReal ((Cp / C) ^ p)) := by
  refine ⟨fun C hC r hr => ?_, fun ε hε => ?_, fun C hC r hr => ?_⟩
  · exact lintegral_encard_diff_closedBall_div_lintegral_encard_le (μ r) (K r) o hp
      (by linarith) hC (hχ r hr).1 (hχ r hr).2 (hξ r hr)
  · obtain ⟨C, hC, h⟩ := exists_lintegral_encard_le_mul_lintegral_encard_inter_closedBall
      (Ω := Ω) (V := V) (Cp := Cp) hp hε
    exact ⟨C, hC, fun r hr =>
      h (μ r) (K r) (hK r hr) o r (by linarith) (hχ r hr).2 (hξ r hr)⟩
  · exact measure_encard_diff_closedBall_pos_le (hK r hr) o hp (by linarith) hC
      (hχ r hr).2 (hξ r hr)

end PercLib.Probability
