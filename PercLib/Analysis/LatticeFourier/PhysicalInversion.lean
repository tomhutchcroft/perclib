/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import PercLib.Analysis.LatticeFourier.Characters
public import PercLib.Analysis.LatticeFourier.Inversion
public import PercLib.Analysis.LatticeFourier.TorusIntegration

/-!
# Physical-frequency bounds for summable lattice kernels

## Main results

A summable even real kernel is bounded by the normalized integral of the absolute
value of its actual cosine transform on the physical Fourier box. This combines
coefficient recovery on the normalized torus with the exact change of variables.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real

namespace PercLib.Analysis

/-- Absolute summability makes the actual cosine transform continuous. -/
theorem continuous_latticeCosineTransform {ι : Type*} [Fintype ι]
    {f : (ι → ℤ) → ℝ} (hf : Summable f) : Continuous (latticeCosineTransform f) := by
  apply continuous_tsum (u := fun x => |f x|)
  · intro x
    fun_prop
  · exact hf.abs
  · intro x k
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

/-- The actual cosine transform is integrable on every finite Fourier ball. -/
theorem integrableOn_latticeCosineTransform_ball {d : ℕ}
    {f : (Fin d → ℤ) → ℝ} (hf : Summable f) (r : ℝ) :
    IntegrableOn (latticeCosineTransform f) (ball (0 : Fin d → ℝ) r) := by
  exact ((continuous_latticeCosineTransform hf).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Fin d → ℝ) r)).mono_set ball_subset_closedBall

/-- Physical-frequency Fourier inversion bounds every coefficient of an even
summable real lattice kernel, with the exact normalized box measure. -/
theorem abs_le_normalized_integral_abs_cosineTransform {d : ℕ}
    {f : (Fin d → ℤ) → ℝ} (hf : Summable f) (heven : Function.Even f)
    (x : Fin d → ℤ) :
    |f x| ≤ ((2 * π) ^ d)⁻¹ *
      ∫ k in ball (0 : Fin d → ℝ) π, |latticeCosineTransform f k| := by
  have hnorm : Summable (fun n => ‖(f n : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf.abs
  have h := norm_le_integral_norm_tsum_mFourier (fun n => (f n : ℂ)) hnorm x
  rw [integral_unitTorus_eq_normalized_box] at h
  simp_rw [tsum_mul_mFourier_div_two_pi_eq_cosineTransform hf heven,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end PercLib.Analysis
