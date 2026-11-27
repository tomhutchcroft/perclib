/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Fourier-series proof of the theta-diagram inequality.
No upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.JoiningSeries
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The theta contraction of an absolutely summable torus series

## Main results

The exact double integral of three character series is obtained by orthogonality.
For a continuous nonnegative torus function, the theta product of its squares
is bounded by the square of its cubic integral, with constant one.
-/

@[expose] public section
noncomputable section

open MeasureTheory UnitAddTorus

namespace PercLib.Analysis

variable {ι : Type*} [Fintype ι]

/-- Absolute summability makes the actual torus series continuous. -/
theorem continuous_tsum_mul_mFourier (f : (ι → ℤ) → ℂ)
    (hf : Summable fun x => ‖f x‖) :
    Continuous (fun t : UnitAddTorus ι => ∑' x, f x * mFourier x t) := by
  apply continuous_tsum (u := fun x => ‖f x‖)
  · intro x
    fun_prop
  · exact hf
  · intro x t
    simp only [norm_mul, norm_mFourier_apply, mul_one, le_rfl]

/-- Two-frequency orthogonality gives the exact theta contraction. The input
may be complex and need not be even; reflection is retained in the result. -/
theorem integral_two_mFourier_series_triangle_eq
    (f : (ι → ℤ) → ℂ) (hf : Summable fun x => ‖f x‖) :
    let S := fun t : UnitAddTorus ι => ∑' x, f x * mFourier x t
    (∫ s : UnitAddTorus ι, ∫ t : UnitAddTorus ι, S s * S t * S (s + t)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      ∑' x, f x * f (-x) * f (-x) := by
  classical
  let S := fun t : UnitAddTorus ι => ∑' x, f x * mFourier x t
  let W : (ι → ℤ) × ((ι → ℤ) × (ι → ℤ)) → ℂ := fun p => f p.1 * (f p.2.1 * f p.2.2)
  have hW : Summable fun p => ‖W p‖ := hf.mul_norm (hf.mul_norm hf)
  have hs (t : UnitAddTorus ι) : Summable fun x => ‖f x * mFourier x t‖ := by
    simpa only [norm_mul, norm_mFourier_apply, mul_one] using hf
  have hexpand (s t : UnitAddTorus ι) : S s * S t * S (s + t) =
      ∑' p : (ι → ℤ) × ((ι → ℤ) × (ι → ℤ)),
        W p * mFourier (p.1 + p.2.1) s * mFourier (p.1 + p.2.2) t := by
    rw [mul_comm (_ * _) (S (s + t))]
    dsimp only [S]
    rw [tsum_mul_tsum_of_summable_norm (hs s) (hs t),
      tsum_mul_tsum_of_summable_norm (hs (s + t)) ((hs s).mul_norm (hs t))]
    apply tsum_congr
    intro p
    simp only [W, mFourier_apply_add, mFourier_add]
    ring
  have hint := integral_tsum_three_mFourier W (fun p => p.1 + p.2.1)
    (fun p => p.1 + p.2.2) (fun _ => 0) hW
  simp only [mFourier_zero, ContinuousMap.one_apply, mul_one, integral_const,
    probReal_univ, one_smul, ↓reduceIte] at hint
  change (∫ s : UnitAddTorus ι, ∫ t : UnitAddTorus ι, S s * S t * S (s + t)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _
  simp_rw [hexpand]
  rw [hint]
  have hmask : Summable fun p : (ι → ℤ) × ((ι → ℤ) × (ι → ℤ)) =>
      if p.1 + p.2.1 = 0 then (if p.1 + p.2.2 = 0 then W p else 0) else 0 := by
    apply hW.of_norm_bounded
    intro p
    split_ifs <;> simp only [norm_zero, norm_nonneg, le_rfl]
  rw [hmask.tsum_prod' (fun x => hmask.prod_factor x)]
  apply tsum_congr
  intro x
  have hpair : Summable fun p : (ι → ℤ) × (ι → ℤ) =>
      if x + p.1 = 0 then (if x + p.2 = 0 then W (x, p) else 0) else 0 :=
    hmask.prod_factor x
  rw [hpair.tsum_prod' (fun y => hpair.prod_factor y)]
  have heq (y : ι → ℤ) : x + y = 0 ↔ y = -x := by
    constructor
    · intro h
      exact (eq_neg_iff_add_eq_zero).2 (by simpa only [add_comm] using h)
    · rintro rfl
      exact add_neg_cancel x
  rw [tsum_eq_single (-x) (fun y hy => by simp [heq, hy])]
  simp [heq, W, mul_assoc]

private theorem theta_pointwise {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * (a ^ 2 * b ^ 2 * c ^ 2) ≤ a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3 := by
  have h (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
      3 * x * y * z ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
      (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z))) (sq_nonneg (z - x)))]
  convert h (a * b) (b * c) (c * a) (mul_nonneg ha hb) (mul_nonneg hb hc)
    (mul_nonneg hc ha) using 1 <;> ring

/-- The theta integral of a continuous nonnegative torus function costs exactly
the square of its cubic integral. No Fourier representation is assumed here. -/
theorem integral_torus_theta_le_cube_sq
    (F : UnitAddTorus ι → ℝ) (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t) :
    (∫ s : UnitAddTorus ι, ∫ t : UnitAddTorus ι,
      F s ^ 2 * F t ^ 2 * F (s + t) ^ 2
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
      (∫ t : UnitAddTorus ι, F t ^ 3 ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ^ 2 := by
  let μ : Measure (UnitAddTorus ι) := Measure.pi (fun _ => AddCircle.haarAddCircle)
  have hint {f : UnitAddTorus ι × UnitAddTorus ι → ℝ} (hf : Continuous f) :
      Integrable f (μ.prod μ) := hf.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hθ : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι =>
      F p.1 ^ 2 * F p.2 ^ 2 * F (p.1 + p.2) ^ 2) (μ.prod μ) := hint (by fun_prop)
  have hA : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι =>
      F p.1 ^ 3 * F p.2 ^ 3) (μ.prod μ) := hint (by fun_prop)
  have hB : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι =>
      F p.2 ^ 3 * F (p.1 + p.2) ^ 3) (μ.prod μ) := hint (by fun_prop)
  have hC : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι =>
      F (p.1 + p.2) ^ 3 * F p.1 ^ 3) (μ.prod μ) := hint (by fun_prop)
  have hAB : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι =>
      F p.1 ^ 3 * F p.2 ^ 3 + F p.2 ^ 3 * F (p.1 + p.2) ^ 3) (μ.prod μ) := hA.add hB
  have hsum : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι =>
      (F p.1 ^ 3 * F p.2 ^ 3 + F p.2 ^ 3 * F (p.1 + p.2) ^ 3) +
        F (p.1 + p.2) ^ 3 * F p.1 ^ 3) (μ.prod μ) := hAB.add hC
  have h := integral_mono (hθ.const_mul 3) hsum (fun p =>
    theta_pointwise (hF0 p.1) (hF0 p.2) (hF0 (p.1 + p.2)))
  rw [integral_const_mul, integral_add hAB hC, integral_add hA hB] at h
  have hAi : (∫ p : UnitAddTorus ι × UnitAddTorus ι,
      F p.1 ^ 3 * F p.2 ^ 3 ∂μ.prod μ) = (∫ t, F t ^ 3 ∂μ) ^ 2 := by
    rw [integral_prod_mul (fun t => F t ^ 3) (fun t => F t ^ 3)]
    ring
  have hBi : (∫ p : UnitAddTorus ι × UnitAddTorus ι,
      F p.2 ^ 3 * F (p.1 + p.2) ^ 3 ∂μ.prod μ) = (∫ t, F t ^ 3 ∂μ) ^ 2 := by
    rw [integral_prod_symm _ hB]
    simp_rw [integral_const_mul, integral_add_right_eq_self (fun t => F t ^ 3)]
    rw [integral_mul_const]
    ring
  have hCi : (∫ p : UnitAddTorus ι × UnitAddTorus ι,
      F (p.1 + p.2) ^ 3 * F p.1 ^ 3 ∂μ.prod μ) = (∫ t, F t ^ 3 ∂μ) ^ 2 := by
    rw [integral_prod _ hC]
    simp_rw [integral_mul_const, integral_add_left_eq_self (fun t => F t ^ 3)]
    rw [integral_const_mul]
    ring
  rw [hAi, hBi, hCi, integral_prod _ hθ] at h
  change (∫ s, ∫ t, F s ^ 2 * F t ^ 2 * F (s + t) ^ 2 ∂μ ∂μ) ≤ _
  linarith

end PercLib.Analysis
