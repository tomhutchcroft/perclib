/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: Fatou's lemma and the uniform squared-symbol cubic
nearest-neighbour resolvent estimate.
-/
module

public import PercLib.Analysis.NearestNeighborWeightedResolvent

/-!
# The critical weighted cubic nearest-neighbour resolvent

The critical weighted integrand is dominated by one plus the critical inverse-sixth
integrand, whose integrability has already been proved. Fatou's lemma then transfers
the sharper weighted subcritical bound. At symbol value one, the totalized critical
integrand is zero, and only its inequality with the lower limit is used.

## Main results

* `integrableOn_nearestNeighborSymbol_sq_mul_critical_inv_cube`: integrability.
* `integral_nearestNeighborSymbol_sq_mul_critical_inv_cube_le`: the normalized
  critical weighted cubic integral is at most `53/(105d)` for `d ≥ 1000`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Filter
open scoped Topology

namespace PercLib.Analysis

/-- The critical squared-symbol cubic integrand is integrable, by domination
with one plus the already integrable critical inverse-sixth resolvent. -/
theorem integrableOn_nearestNeighborSymbol_sq_mul_critical_inv_cube {d : ℕ}
    (hd : 1000 ≤ d) :
    IntegrableOn (fun k : Fin d → ℝ => ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
      (1 - (d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 3) (ball 0 π) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ => volume.restrict (Ioo (-π) π)
  let A : (Fin d → ℝ) → ℝ := fun k => (d : ℝ)⁻¹ * ∑ j, cos (k j)
  have hA (k : Fin d → ℝ) : |A k| ≤ 1 :=
    abs_nearestNeighborSymbol_le_one (show 0 < d by omega) k
  have hden (k : Fin d → ℝ) : 0 ≤ 1 - A k :=
    sub_nonneg.mpr ((le_abs_self _).trans (hA k))
  have hnonneg (k : Fin d → ℝ) : 0 ≤ A k ^ 2 / (1 - A k) ^ 3 :=
    div_nonneg (sq_nonneg _) (pow_nonneg (hden k) _)
  have hdom (k : Fin d → ℝ) : A k ^ 2 / (1 - A k) ^ 3 ≤ 1 + 1 / (1 - A k) ^ 6 := by
    have hden0 := hden k
    have ht : 0 ≤ 1 / (1 - A k) ^ 3 := by positivity
    have hsquare : (1 / (1 - A k) ^ 3) ^ 2 = 1 / (1 - A k) ^ 6 := by
      rw [div_pow, one_pow, ← pow_mul]
    calc
      _ = A k ^ 2 * (1 / (1 - A k) ^ 3) := by ring
      _ ≤ 1 / (1 - A k) ^ 3 := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right ((sq_le_one_iff_abs_le_one _).2 (hA k)) ht
      _ ≤ _ := by nlinarith [sq_nonneg (1 / (1 - A k) ^ 3 - 1 / 2)]
  have hsix : Integrable (fun k => 1 / (1 - A k) ^ 6) μ := by
    have h := integrableOn_nearestNeighborSymbol_critical_inv_six hd
    simpa only [IntegrableOn, volume_restrict_pi_ball_eq_pi_Ioo, μ, A] using h
  have hmeas : Measurable (fun k => A k ^ 2 / (1 - A k) ^ 3) := by
    dsimp [A]
    fun_prop
  have hint : Integrable (fun k => A k ^ 2 / (1 - A k) ^ 3) μ :=
    ((integrable_const 1).add hsix).mono_nonneg
      hmeas.aestronglyMeasurable (Eventually.of_forall hnonneg) (Eventually.of_forall hdom)
  simpa only [IntegrableOn, volume_restrict_pi_ball_eq_pi_Ioo, μ, A] using hint

/-- The actual normalized critical weighted cubic resolvent is at most
`53/(105d)` in every dimension at least 1000. -/
theorem integral_nearestNeighborSymbol_sq_mul_critical_inv_cube_le {d : ℕ}
    (hd : 1000 ≤ d) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
        (1 - (d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 3) ≤ 53 / (105 * (d : ℝ)) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ => volume.restrict (Ioo (-π) π)
  let A : (Fin d → ℝ) → ℝ := fun k => (d : ℝ)⁻¹ * ∑ j, cos (k j)
  let f : (Fin d → ℝ) → ℝ := fun k => A k ^ 2 / (1 - A k) ^ 3
  let F : ℕ → (Fin d → ℝ) → ℝ := fun n k =>
    A k ^ 2 / (1 - (1 - 1 / ((n : ℝ) + 1)) * A k) ^ 3
  let C : ℝ := (2 * π) ^ d
  let B : ℝ := 53 / (105 * (d : ℝ))
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA (k : Fin d → ℝ) : |A k| ≤ 1 :=
    abs_nearestNeighborSymbol_le_one (show 0 < d by omega) k
  have hr0 (n : ℕ) : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    have h : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hr1 (n : ℕ) : 1 - 1 / ((n : ℝ) + 1) < 1 := by
    have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hr : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hAsqmeas : Measurable (fun k => A k ^ 2) := by dsimp [A]; fun_prop
  have hFint (n : ℕ) : Integrable (F n) μ := by
    have h := (integrable_nearestNeighborSymbol_inv_pow (show 0 < d by omega) μ
      (hr0 n) (hr1 n) 2).bdd_mul
      (f := fun k => A k ^ 2) (c := 1) hAsqmeas.aestronglyMeasurable
      (Eventually.of_forall fun k => by
        change ‖A k ^ 2‖ ≤ 1
        rw [norm_pow, Real.norm_eq_abs]
        exact pow_le_one₀ (abs_nonneg _) (hA k))
    simpa only [F, A, mul_one_div] using h
  have hFnonneg (n : ℕ) (k : Fin d → ℝ) : 0 ≤ F n k := by
    have hmul := mul_le_of_le_one_right (hr0 n) ((le_abs_self _).trans (hA k))
    have hden : 0 < 1 - (1 - 1 / ((n : ℝ) + 1)) * A k := by linarith [hr1 n]
    dsimp [F]
    positivity
  have hfnonneg (k : Fin d → ℝ) : 0 ≤ f k := by
    have hden : 0 ≤ 1 - A k := sub_nonneg.mpr ((le_abs_self _).trans (hA k))
    dsimp [f]
    positivity
  have hfint : Integrable f μ := by
    have h := integrableOn_nearestNeighborSymbol_sq_mul_critical_inv_cube hd
    simpa only [IntegrableOn, volume_restrict_pi_ball_eq_pi_Ioo, μ, f, A] using h
  have hFbound (n : ℕ) : (∫ k, F n k ∂μ) ≤ C * B := by
    have h := integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd (hr0 n) (hr1 n)
    rw [volume_restrict_pi_ball_eq_pi_Ioo] at h
    change C⁻¹ * (∫ k, F n k ∂μ) ≤ B at h
    have h' := mul_le_mul_of_nonneg_left h hC.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using h'
  have hFofReal (n : ℕ) :
      (∫⁻ k, ENNReal.ofReal (F n k) ∂μ) ≤ ENNReal.ofReal (C * B) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint n)
      (Eventually.of_forall (hFnonneg n))]
    exact ENNReal.ofReal_le_ofReal (hFbound n)
  have hpoint (k : Fin d → ℝ) :
      ENNReal.ofReal (f k) ≤ liminf (fun n => ENNReal.ofReal (F n k)) atTop := by
    by_cases hk : A k = 1
    · simp only [f, hk, sub_self, zero_pow (by omega : (3 : ℕ) ≠ 0), div_zero,
        ENNReal.ofReal_zero]
      exact bot_le
    · have hden : Tendsto (fun n : ℕ => 1 - (1 - 1 / ((n : ℝ) + 1)) * A k)
          atTop (𝓝 (1 - A k)) := by
        simpa only [one_mul] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hr.mul_const (A k))
      have hlim : Tendsto (fun n => F n k) atTop (𝓝 (f k)) :=
        tendsto_const_nhds.div (hden.pow 3)
          (pow_ne_zero 3 (sub_ne_zero.mpr (fun h => hk h.symm)))
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim).liminf_eq.ge
  have hfatou : (∫⁻ k, ENNReal.ofReal (f k) ∂μ) ≤ ENNReal.ofReal (C * B) := by
    calc
      _ ≤ ∫⁻ k, liminf (fun n => ENNReal.ofReal (F n k)) atTop ∂μ :=
        lintegral_mono hpoint
      _ ≤ liminf (fun n => ∫⁻ k, ENNReal.ofReal (F n k) ∂μ) atTop :=
        lintegral_liminf_le' fun n => (hFint n).aemeasurable.ennreal_ofReal
      _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hFofReal).frequently
  rw [← ofReal_integral_eq_lintegral_ofReal hfint
    (Eventually.of_forall hfnonneg)] at hfatou
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le hB)).mp hfatou
  have hnormalized : C⁻¹ * (∫ k, f k ∂μ) ≤ B := by
    have h := mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hC.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using h
  simpa only [volume_restrict_pi_ball_eq_pi_Ioo, μ, f, A, C, B] using hnormalized

end PercLib.Analysis
