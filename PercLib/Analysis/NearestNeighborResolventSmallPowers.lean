/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original refinements from exact resolvent identities; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.NearestNeighborWeightedResolventPowers
public import PercLib.Analysis.NearestNeighborResolventCritical
public import PercLib.Analysis.LatticeFourier.Bounds

/-!
# Refined second and third resolvent integrals

## Main results

Exact rational identities express the unweighted second and third powers through
the first three squared-symbol integrals. The odd symbol term integrates to zero.
This retains the factor `r²` and gives corrections `379/(252d)` and `253/(84d)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real

namespace PercLib.Analysis

variable {d : ℕ}

/-- The massive nearest-neighbour resolvent is continuous everywhere. -/
theorem continuous_nearestNeighborResolvent (hd : 0 < d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) : Continuous (nearestNeighborResolvent (d := d) r) := by
  unfold nearestNeighborResolvent
  apply Continuous.inv₀
  · unfold nearestNeighborSymbol
    fun_prop
  · intro l
    exact (nearestNeighborResolvent_den_pos hd hr l).ne'

/-- Every nonnegative integer power of a massive resolvent is integrable on
the physical Fourier box, including power zero. -/
theorem integrableOn_nearestNeighborResolvent_pow (hd : 0 < d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    IntegrableOn (fun l : Fin d → ℝ => nearestNeighborResolvent r l ^ n) (ball 0 π) :=
  (((continuous_nearestNeighborResolvent hd hr).pow n).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Fin d → ℝ) π)).mono_set ball_subset_closedBall

private theorem weighted_integrable (hd : 0 < d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    IntegrableOn (fun l : Fin d → ℝ =>
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ n) (ball 0 π) := by
  have hD : Continuous (nearestNeighborSymbol (d := d)) := by
    unfold nearestNeighborSymbol
    fun_prop
  have hc := (hD.pow 2).mul ((continuous_nearestNeighborResolvent hd hr).pow n)
  exact (hc.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Fin d → ℝ) π)).mono_set ball_subset_closedBall

private theorem normalized_integral_one :
    ((2 * π) ^ d)⁻¹ * (∫ _l in ball (0 : Fin d → ℝ) π, (1 : ℝ)) = 1 := by
  rw [volume_restrict_pi_ball_eq_pi_Ioo]
  have hvol : (∫ _l : Fin d → ℝ, (1 : ℝ)
      ∂Measure.pi (fun _ => volume.restrict (Set.Ioo (-π) π))) = (2 * π) ^ d := by
    simpa using integral_pi_sum_cos_pow_zero d
  rw [hvol, inv_mul_cancel₀ (by positivity)]

private theorem integral_symbol_zero :
    (∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l) = 0 := by
  simpa only [Nat.mul_zero, Nat.zero_add, pow_one, nearestNeighborSymbol] using
    integral_nearestNeighborSymbol_pow_odd d 0

/-- The second-power integral has an exact two-term weighted remainder. -/
theorem integral_nearestNeighborResolvent_sq_eq_weighted (hd : 0 < d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborResolvent r l ^ 2) =
      1 + r ^ 2 *
        (2 * (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) +
        ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 2) := by
  have hp (l : Fin d → ℝ) : nearestNeighborResolvent r l ^ 2 =
      (1 + 2 * r * nearestNeighborSymbol l) + r ^ 2 *
        (2 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) +
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 2) := by
    unfold nearestNeighborResolvent
    field_simp [(nearestNeighborResolvent_den_pos hd hr l).ne']
    ring
  have h1 : IntegrableOn (fun l : Fin d → ℝ =>
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) (ball 0 π) := by
    simpa only [pow_one] using weighted_integrable hd hr 1
  have h2 := weighted_integrable hd hr 2
  have hD : IntegrableOn (nearestNeighborSymbol (d := d)) (ball 0 π) := by
    have hc : Continuous (nearestNeighborSymbol (d := d)) := by
      unfold nearestNeighborSymbol
      fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Fin d → ℝ) π)).mono_set
      ball_subset_closedBall
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => (1 : ℝ)) (ball 0 π) := by
    simpa only [pow_zero] using integrableOn_nearestNeighborResolvent_pow hd hr 0
  have hleft : IntegrableOn (fun l : Fin d → ℝ => 1 + 2 * r * nearestNeighborSymbol l)
      (ball 0 π) := hconst.add (hD.const_mul _)
  have hright : IntegrableOn (fun l : Fin d → ℝ =>
      2 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) +
        nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 2) (ball 0 π) :=
    (h1.const_mul 2).add h2
  have heq := congrArg (fun f : (Fin d → ℝ) → ℝ =>
    ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π, f l) (funext hp)
  rw [heq]
  rw [integral_add hleft (hright.const_mul _), integral_const_mul,
    integral_add hconst (hD.const_mul _), integral_const_mul,
    integral_add (h1.const_mul 2) h2, integral_const_mul, integral_symbol_zero, mul_zero, add_zero]
  have hn := normalized_integral_one (d := d)
  nlinarith [hn]

/-- The third-power integral has an exact three-term weighted remainder. -/
theorem integral_nearestNeighborResolvent_cube_eq_weighted (hd : 0 < d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborResolvent r l ^ 3) =
      1 + r ^ 2 *
        (3 * (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) +
        2 * (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 2) +
        ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) := by
  have hp (l : Fin d → ℝ) : nearestNeighborResolvent r l ^ 3 =
      (1 + 3 * r * nearestNeighborSymbol l) + r ^ 2 *
        ((3 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) +
          2 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 2)) +
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) := by
    unfold nearestNeighborResolvent
    field_simp [(nearestNeighborResolvent_den_pos hd hr l).ne']
    ring
  have h1 : IntegrableOn (fun l : Fin d → ℝ =>
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) (ball 0 π) := by
    simpa only [pow_one] using weighted_integrable hd hr 1
  have h2 := weighted_integrable hd hr 2
  have h3 := weighted_integrable hd hr 3
  have hD : IntegrableOn (nearestNeighborSymbol (d := d)) (ball 0 π) := by
    have hc : Continuous (nearestNeighborSymbol (d := d)) := by
      unfold nearestNeighborSymbol
      fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Fin d → ℝ) π)).mono_set
      ball_subset_closedBall
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => (1 : ℝ)) (ball 0 π) := by
    simpa only [pow_zero] using integrableOn_nearestNeighborResolvent_pow hd hr 0
  have hleft : IntegrableOn (fun l : Fin d → ℝ => 1 + 3 * r * nearestNeighborSymbol l)
      (ball 0 π) := hconst.add (hD.const_mul _)
  have h12 : IntegrableOn (fun l : Fin d → ℝ =>
      3 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) +
        2 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 2)) (ball 0 π) :=
    (h1.const_mul 3).add (h2.const_mul 2)
  have hright : IntegrableOn (fun l : Fin d → ℝ =>
      (3 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l) +
        2 * (nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 2)) +
        nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) (ball 0 π) := h12.add h3
  have heq := congrArg (fun f : (Fin d → ℝ) → ℝ =>
    ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π, f l) (funext hp)
  rw [heq]
  rw [integral_add hleft (hright.const_mul _), integral_const_mul,
    integral_add hconst (hD.const_mul _), integral_const_mul,
    integral_add h12 h3, integral_add (h1.const_mul 3) (h2.const_mul 2),
    integral_const_mul, integral_const_mul, integral_symbol_zero, mul_zero, add_zero]
  have hn := normalized_integral_one (d := d)
  nlinarith [hn]

/-- The refined unweighted second-power bound retains the massive parameter. -/
theorem integral_nearestNeighborResolvent_sq_le_refined (hd : 1000 ≤ d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborResolvent r l ^ 2) ≤
      1 + r ^ 2 * (379 / (252 * (d : ℝ))) := by
  have h1 := integral_nearestNeighborSymbol_sq_mul_inv_le hd hr.1 hr.2
  have h2 := integral_nearestNeighborSymbol_sq_mul_inv_sq_le hd hr.1 hr.2
  rw [integral_nearestNeighborResolvent_sq_eq_weighted (by omega) hr]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  calc
    _ ≤ 2 * (631 / (1260 * (d : ℝ))) + 211 / (420 * (d : ℝ)) := by
      simp only [nearestNeighborSymbol, nearestNeighborResolvent, inv_pow,
        div_eq_mul_inv] at h1 h2 ⊢
      linarith
    _ = _ := by ring

/-- The refined unweighted cubic bound retains the massive parameter. -/
theorem integral_nearestNeighborResolvent_cube_le_refined (hd : 1000 ≤ d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborResolvent r l ^ 3) ≤
      1 + r ^ 2 * (253 / (84 * (d : ℝ))) := by
  have h1 := integral_nearestNeighborSymbol_sq_mul_inv_le hd hr.1 hr.2
  have h2 := integral_nearestNeighborSymbol_sq_mul_inv_sq_le hd hr.1 hr.2
  have h3 := integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd hr.1 hr.2
  rw [integral_nearestNeighborResolvent_cube_eq_weighted (by omega) hr]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  calc
    _ ≤ 3 * (631 / (1260 * (d : ℝ))) + 2 * (211 / (420 * (d : ℝ))) +
        53 / (105 * (d : ℝ)) := by
      simp only [nearestNeighborSymbol, nearestNeighborResolvent, inv_pow,
        div_eq_mul_inv] at h1 h2 h3 ⊢
      linarith
    _ = _ := by ring

end PercLib.Analysis
