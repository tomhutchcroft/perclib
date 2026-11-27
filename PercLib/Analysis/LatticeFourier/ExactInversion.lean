/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.PhysicalInversion
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exact real Fourier inversion on the physical box

## Main results

A summable even real lattice kernel equals the normalized integral of its actual
cosine transform against the corresponding cosine character. The normalization
is inherited from coefficient recovery on the normalized torus.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real UnitAddTorus

namespace PercLib.Analysis

/-- Exact physical-frequency inversion for summable even real lattice kernels. -/
theorem eq_normalized_integral_cos_mul_cosineTransform {d : ℕ}
    {f : (Fin d → ℤ) → ℝ} (hf : Summable f) (heven : Function.Even f)
    (x : Fin d → ℤ) :
    f x = ((2 * π) ^ d)⁻¹ * ∫ k in ball (0 : Fin d → ℝ) π,
      cos (∑ i, k i * (x i : ℝ)) * latticeCosineTransform f k := by
  have hnorm : Summable (fun n => ‖(f n : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf.abs
  have h := mFourierCoeff_tsum_mul (fun n => (f n : ℂ)) hnorm x
  change (∫ t : UnitAddTorus (Fin d), mFourier (-x) t *
    (∑' n, (f n : ℂ) * mFourier n t)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = (f x : ℂ) at h
  rw [integral_unitTorus_eq_normalized_box] at h
  simp_rw [tsum_mul_mFourier_div_two_pi_eq_cosineTransform hf heven,
    mFourier_div_two_pi_eq_latticeCharacter] at h
  have hcont : Continuous (fun k : Fin d → ℝ =>
      (latticeCharacter k (-x) : ℂ) * (latticeCosineTransform f k : ℂ)) := by
    have hc := continuous_latticeCosineTransform hf
    simp_rw [latticeCharacter_coe_apply]
    fun_prop
  have hint : IntegrableOn (fun k : Fin d → ℝ =>
      (latticeCharacter k (-x) : ℂ) * (latticeCosineTransform f k : ℂ))
      (closedBall (0 : Fin d → ℝ) π) :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Fin d → ℝ) π)
  have hint' := hint.mono_set ball_subset_closedBall
  have hre := congrArg Complex.re h
  have hreal : (∫ k in ball (0 : Fin d → ℝ) π,
      (latticeCharacter k (-x) : ℂ) * (latticeCosineTransform f k : ℂ)).re =
      ∫ k in ball (0 : Fin d → ℝ) π,
        ((latticeCharacter k (-x) : ℂ) * (latticeCosineTransform f k : ℂ)).re :=
    (Complex.reCLM.integral_comp_comm hint').symm
  rw [Complex.smul_re, hreal] at hre
  have hpoint (k : Fin d → ℝ) :
      ((latticeCharacter k (-x) : ℂ) * (latticeCosineTransform f k : ℂ)).re =
        cos (∑ i, k i * (x i : ℝ)) * latticeCosineTransform f k := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, latticeCharacter_re, Pi.neg_apply, Int.cast_neg, mul_neg,
      Finset.sum_neg_distrib, cos_neg]
  simpa only [hpoint, Complex.ofReal_re, smul_eq_mul] using hre.symm

end PercLib.Analysis
