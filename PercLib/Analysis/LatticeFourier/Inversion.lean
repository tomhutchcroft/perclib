/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Recovering summable lattice kernels from their torus series

## Main results

Mathlib's Fourier coefficients recover the coefficients of an absolutely
summable lattice series. The measure is the product of the normalized circle
Haar measures. No alternative Fourier coefficient definition is introduced.
-/

@[expose] public section
noncomputable section

open MeasureTheory UnitAddTorus

namespace PercLib.Analysis

/-- Every multivariate Fourier monomial has pointwise norm one. -/
theorem norm_mFourier_apply {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (t : UnitAddTorus ι) : ‖mFourier n t‖ = 1 := by
  simp [mFourier, fourier_apply, norm_prod]

/-- Coordinate orthogonality recovers a single multivariate monomial. -/
theorem mFourierCoeff_mFourier {ι : Type*} [Fintype ι] (n x : ι → ℤ) :
    mFourierCoeff (mFourier n) x = if n = x then 1 else 0 := by
  classical
  change (∫ t : UnitAddTorus ι, mFourier (-x) t * mFourier n t
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (fun i (t : UnitAddCircle) => fourier (-(x i)) t * fourier (n i) t)]
  have hcoord (i : ι) :
      (∫ t : UnitAddCircle, fourier (-(x i)) t * fourier (n i) t
        ∂AddCircle.haarAddCircle) = if n i = x i then (1 : ℂ) else 0 := by
    change fourierCoeff (fourier (n i)) (x i) = _
    rw [fourierCoeff_fourier]
    simp [Pi.single_apply, eq_comm]
  simp_rw [hcoord]
  by_cases h : n = x
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Fourier coefficients recover an absolutely summable lattice kernel from
its actual torus character series. -/
theorem mFourierCoeff_tsum_mul {ι : Type*} [Fintype ι]
    (f : (ι → ℤ) → ℂ) (hf : Summable (fun n => ‖f n‖)) (x : ι → ℤ) :
    mFourierCoeff (fun t => ∑' n, f n * mFourier n t) x = f x := by
  classical
  let μ : Measure (UnitAddTorus ι) := Measure.pi (fun _ => AddCircle.haarAddCircle)
  have hn (n : ι → ℤ) (t : UnitAddTorus ι) :
      ‖mFourier (-x) t * (f n * mFourier n t)‖ = ‖f n‖ := by
    simp only [norm_mul, norm_mFourier_apply, mul_one, one_mul]
  have hint (n : ι → ℤ) :
      Integrable (fun t => mFourier (-x) t * (f n * mFourier n t)) μ := by
    apply Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) ‖f n‖
    exact Filter.Eventually.of_forall (fun t => (hn n t).le)
  have hnorm : Summable (fun n : ι → ℤ =>
      ∫ t, ‖mFourier (-x) t * (f n * mFourier n t)‖ ∂μ) := by
    simp_rw [hn]
    simpa only [integral_const, probReal_univ, one_smul] using hf
  change (∫ t, mFourier (-x) t * (∑' n, f n * mFourier n t) ∂μ) = _
  simp_rw [← tsum_mul_left]
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  have hterm (n : ι → ℤ) :
      (∫ t, mFourier (-x) t * (f n * mFourier n t) ∂μ) =
        f n * (if n = x then 1 else 0) := by
    have heq (t : UnitAddTorus ι) :
        mFourier (-x) t * (f n * mFourier n t) =
          f n * (mFourier (-x) t * mFourier n t) := by ring
    simp_rw [heq]
    rw [integral_const_mul]
    change f n * mFourierCoeff (mFourier n) x = _
    rw [mFourierCoeff_mFourier]
  simp_rw [hterm]
  simp

/-- A recovered coefficient is bounded by the integral of the transform's norm. -/
theorem norm_le_integral_norm_tsum_mFourier {ι : Type*} [Fintype ι]
    (f : (ι → ℤ) → ℂ) (hf : Summable (fun n => ‖f n‖)) (x : ι → ℤ) :
    ‖f x‖ ≤ ∫ t : UnitAddTorus ι, ‖∑' n, f n * mFourier n t‖
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle) := by
  rw [← mFourierCoeff_tsum_mul f hf x]
  change ‖∫ t : UnitAddTorus ι, mFourier (-x) t * (∑' n, f n * mFourier n t)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ ≤ _
  simpa only [norm_mul, norm_mFourier_apply, one_mul] using
    norm_integral_le_integral_norm (μ := Measure.pi (fun _ => AddCircle.haarAddCircle))
      (fun t : UnitAddTorus ι => mFourier (-x) t * (∑' n, f n * mFourier n t))

end PercLib.Analysis
