/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: Fatou's lemma applied to the subcritical nearest-neighbour
walk resolvent, using the proved uniform inverse-sixth estimate.
-/
module

public import PercLib.Analysis.NearestNeighborResolventUniform

/-!
# The critical inverse-sixth nearest-neighbour walk estimate

The uniform subcritical bound passes to the critical parameter by Fatou's lemma,
and proves integrability at the same time. At a frequency where the symbol equals
one, Lean's totalized reciprocal makes the critical integrand zero. This is harmless
for the upper bound: the proof uses a pointwise inequality with the lower limit there,
and does not assert pointwise convergence at a singular frequency.

## Main results

* `integrableOn_nearestNeighborSymbol_critical_inv_six`: critical integrability.
* `integral_nearestNeighborSymbol_critical_inv_six_le`: the normalized critical
  inverse-sixth integral is at most `1 + 53/(5d)` for `d ≥ 1000`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Filter
open scoped Topology

namespace PercLib.Analysis

/-- Every subcritical inverse power of the nearest-neighbour symbol is integrable
against an arbitrary finite measure, by its positive denominator bound. -/
theorem integrable_nearestNeighborSymbol_inv_pow {d : ℕ} (hd : 0 < d)
    (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℕ) :
    Integrable (fun k => 1 / (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1)) μ := by
  have hmeas : Measurable (fun k : Fin d → ℝ =>
      1 / (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1)) := by fun_prop
  apply Integrable.of_bound hmeas.aestronglyMeasurable (1 / (1 - r) ^ (s + 1))
  apply Eventually.of_forall
  intro k
  have hsymbol : (d : ℝ)⁻¹ * ∑ j, cos (k j) ≤ 1 :=
    (le_abs_self _).trans (abs_nearestNeighborSymbol_le_one hd k)
  have hmul := mul_le_of_le_one_right hr0 hsymbol
  have hbase : 0 < 1 - r := sub_pos.mpr hr1
  have hden : 0 < 1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j)) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (pow_pos hbase _)
    (pow_le_pow_left₀ hbase.le (by linarith) _)

/-- Fatou's lemma gives both critical integrability and the explicit normalized
bound, without requiring pointwise convergence at singular frequencies. -/
theorem integrableOn_and_integral_nearestNeighborSymbol_critical_inv_six_le
    {d : ℕ} (hd : 1000 ≤ d) :
    IntegrableOn (fun k : Fin d → ℝ =>
      1 / (1 - (d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 6) (ball 0 π) ∧
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      1 / (1 - (d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 6) ≤ 1 + 53 / (5 * (d : ℝ)) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ => volume.restrict (Ioo (-π) π)
  let A : (Fin d → ℝ) → ℝ := fun k => (d : ℝ)⁻¹ * ∑ j, cos (k j)
  let f : (Fin d → ℝ) → ℝ := fun k => 1 / (1 - A k) ^ 6
  let F : ℕ → (Fin d → ℝ) → ℝ := fun n k =>
    1 / (1 - (1 - 1 / ((n : ℝ) + 1)) * A k) ^ 6
  let C : ℝ := (2 * π) ^ d
  let B : ℝ := 1 + 53 / (5 * (d : ℝ))
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
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
  have hFint (n : ℕ) : Integrable (F n) μ :=
    integrable_nearestNeighborSymbol_inv_pow (show 0 < d by omega) μ (hr0 n) (hr1 n) 5
  have hFnonneg (n : ℕ) (k : Fin d → ℝ) : 0 ≤ F n k := by dsimp [F]; positivity
  have hfnonneg (k : Fin d → ℝ) : 0 ≤ f k := by dsimp [f]; positivity
  have hFbound (n : ℕ) : (∫ k, F n k ∂μ) ≤ C * B := by
    have h := integral_nearestNeighborSymbol_inv_six_le_one_add_refined hd (hr0 n) (hr1 n)
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
    · simp only [f, hk, sub_self, zero_pow (by omega : (6 : ℕ) ≠ 0), div_zero,
        ENNReal.ofReal_zero]
      exact bot_le
    · have hden : Tendsto (fun n : ℕ => 1 - (1 - 1 / ((n : ℝ) + 1)) * A k)
          atTop (𝓝 (1 - A k)) := by
        simpa only [one_mul] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hr.mul_const (A k))
      have hlim : Tendsto (fun n => F n k) atTop (𝓝 (f k)) :=
        tendsto_const_nhds.div (hden.pow 6) (pow_ne_zero 6 (sub_ne_zero.mpr (fun h => hk h.symm)))
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim).liminf_eq.ge
  have hfatou : (∫⁻ k, ENNReal.ofReal (f k) ∂μ) ≤ ENNReal.ofReal (C * B) := by
    calc
      _ ≤ ∫⁻ k, liminf (fun n => ENNReal.ofReal (F n k)) atTop ∂μ :=
        lintegral_mono hpoint
      _ ≤ liminf (fun n => ∫⁻ k, ENNReal.ofReal (F n k) ∂μ) atTop :=
        lintegral_liminf_le' fun n => (hFint n).aemeasurable.ennreal_ofReal
      _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hFofReal).frequently
  have hfmeas : Measurable f := by dsimp [f, A]; fun_prop
  have hfint : Integrable f μ := ⟨hfmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hfnonneg)).2
      (hfatou.trans_lt ENNReal.ofReal_lt_top)⟩
  have hreal : (∫ k, f k ∂μ) ≤ C * B := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint
      (Eventually.of_forall hfnonneg)] at hfatou
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le hB)).mp hfatou
  have hnormalized : C⁻¹ * (∫ k, f k ∂μ) ≤ B := by
    have h := mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hC.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using h
  simpa only [IntegrableOn, volume_restrict_pi_ball_eq_pi_Ioo, μ, f, A, C, B] using
    And.intro hfint hnormalized

/-- The actual critical inverse-sixth nearest-neighbour symbol is integrable
on the Fourier torus in every dimension at least 1000. -/
theorem integrableOn_nearestNeighborSymbol_critical_inv_six {d : ℕ} (hd : 1000 ≤ d) :
    IntegrableOn (fun k : Fin d → ℝ =>
      1 / (1 - (d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 6) (ball 0 π) :=
  (integrableOn_and_integral_nearestNeighborSymbol_critical_inv_six_le hd).1

/-- The normalized critical inverse-sixth nearest-neighbour integral is at most
`1 + 53/(5d)` for every dimension at least 1000. -/
theorem integral_nearestNeighborSymbol_critical_inv_six_le {d : ℕ} (hd : 1000 ≤ d) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      1 / (1 - (d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 6) ≤ 1 + 53 / (5 * (d : ℝ)) :=
  (integrableOn_and_integral_nearestNeighborSymbol_critical_inv_six_le hd).2

end PercLib.Analysis
