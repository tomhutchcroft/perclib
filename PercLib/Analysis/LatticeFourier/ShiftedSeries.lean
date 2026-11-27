/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.Inversion
public import PercLib.Analysis.CharacterSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Shifted products of positive Fourier series

Nonnegative, absolutely summable Fourier coefficients make the integral of a
product of translates largest at simultaneous zero shifts. The proof expands
the series and uses orthogonality and the unit modulus of the translation phases.
It does not translate a weighted measure.

## Main results

* `norm_integral_phase_mFourier_series_le`: inserting unit phases cannot increase
  the norm of the zero Fourier coefficient of a positive series.
* `norm_integral_shifted_mFourier_series_mul_three_le`: the resulting bound for
  three translated positive Fourier series.
-/

@[expose] public section

noncomputable section

open MeasureTheory UnitAddTorus

namespace PercLib.Analysis

variable {ι : Type*} [Fintype ι]

/-- A torus monomial is multiplicative in its torus argument. -/
theorem mFourier_apply_add (n : ι → ℤ) (s t : UnitAddTorus ι) :
    mFourier n (s + t) = mFourier n s * mFourier n t := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

open scoped Classical in
/-- Normalized torus integration extracts the zero monomial. -/
theorem integral_mFourier (n : ι → ℤ) :
    (∫ t : UnitAddTorus ι, mFourier n t
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = if n = 0 then 1 else 0 := by
  classical
  have h := mFourierCoeff_mFourier n 0
  change (∫ t : UnitAddTorus ι, mFourier (-0) t • mFourier n t
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _ at h
  simpa [mFourier_zero] using h

open scoped Classical in
/-- A summable indexed character series is integrated by retaining its zero frequencies.
The frequency map need not be injective. -/
theorem integral_tsum_mul_mFourier {A : Type*} [Countable A]
    (w : A → ℂ) (v : A → ι → ℤ) (hw : Summable fun a => ‖w a‖) :
    (∫ t : UnitAddTorus ι, ∑' a, w a * mFourier (v a) t
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
        ∑' a, if v a = 0 then w a else 0 := by
  classical
  have hint (a : A) : Integrable
      (fun t : UnitAddTorus ι => w a * mFourier (v a) t)
      (Measure.pi (fun _ => AddCircle.haarAddCircle)) := by
    apply Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) ‖w a‖
    exact Filter.Eventually.of_forall fun t => by simp [norm_mFourier_apply]
  have hnorm : Summable fun a : A =>
      ∫ t : UnitAddTorus ι, ‖w a * mFourier (v a) t‖
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle) := by
    simpa only [norm_mul, norm_mFourier_apply, mul_one, integral_const,
      probReal_univ, one_smul] using hw
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  apply tsum_congr
  intro a
  rw [integral_const_mul, integral_mFourier]
  split_ifs <;> simp

/-- Inserting phases of norm one cannot increase the zero coefficient of an
absolutely summable series with nonnegative coefficients. -/
theorem norm_integral_phase_mFourier_series_le {A : Type*} [Countable A]
    (w : A → ℝ) (v : A → ι → ℤ) (z : A → ℂ)
    (hw : Summable w) (hw0 : ∀ a, 0 ≤ w a) (hz : ∀ a, ‖z a‖ = 1) :
    ‖∫ t : UnitAddTorus ι, ∑' a, (w a : ℂ) * z a * mFourier (v a) t
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ ≤
        (∫ t : UnitAddTorus ι, ∑' a, (w a : ℂ) * mFourier (v a) t
          ∂Measure.pi (fun _ => AddCircle.haarAddCircle)).re := by
  classical
  have hnorm (a : A) : ‖(w a : ℂ) * z a‖ = w a := by
    simp [hz, Complex.norm_real, Real.norm_of_nonneg (hw0 a)]
  have hphase : Summable fun a => ‖(w a : ℂ) * z a‖ := by simpa only [hnorm] using hw
  have hplain : Summable fun a => ‖(w a : ℂ)‖ := by simpa using hw.norm
  rw [integral_tsum_mul_mFourier _ _ hphase, integral_tsum_mul_mFourier _ _ hplain]
  have hzero : Summable fun a => if v a = 0 then w a else 0 :=
    Summable.of_nonneg_of_le
      (fun a => by
        split_ifs
        · exact hw0 a
        · exact le_rfl)
      (fun a => by
        split_ifs
        · exact le_rfl
        · exact hw0 a) hw
  have hsum : Summable fun a => ‖if v a = 0 then (w a : ℂ) * z a else 0‖ := by
    simpa only [apply_ite norm, hnorm, norm_zero] using hzero
  calc
    _ ≤ ∑' a, ‖if v a = 0 then (w a : ℂ) * z a else 0‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' a, if v a = 0 then w a else 0 := by simp only [apply_ite norm, hnorm, norm_zero]
    _ = _ := by
      have heq : (∑' a, if v a = 0 then (w a : ℂ) else 0) =
          ((∑' a, if v a = 0 then w a else 0 : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        apply tsum_congr
        intro a
        split_ifs <;> simp
      rw [heq, Complex.ofReal_re]

/-- Multiplying two summable monomial series adds their frequencies. -/
theorem tsum_mul_mFourier_mul_tsum_mul_mFourier {A B : Type*}
    (w : A → ℂ) (u : B → ℂ) (v : A → ι → ℤ) (s : B → ι → ℤ)
    (hw : Summable fun a => ‖w a‖) (hu : Summable fun b => ‖u b‖)
    (t : UnitAddTorus ι) :
    (∑' a, w a * mFourier (v a) t) * (∑' b, u b * mFourier (s b) t) =
      ∑' p : A × B, (w p.1 * u p.2) * mFourier (v p.1 + s p.2) t := by
  have hw' : Summable fun a => ‖w a * mFourier (v a) t‖ := by
    simpa only [norm_mul, norm_mFourier_apply, mul_one] using hw
  have hu' : Summable fun b => ‖u b * mFourier (s b) t‖ := by
    simpa only [norm_mul, norm_mFourier_apply, mul_one] using hu
  rw [tsum_mul_tsum_of_summable_norm hw' hu']
  apply tsum_congr
  intro p
  rw [mFourier_add]
  ring

/-- For positive absolutely summable Fourier series, arbitrary shifts in a triple
product cannot increase the norm of its integral beyond the unshifted zero coefficient. -/
theorem norm_integral_shifted_mFourier_series_mul_three_le
    {A B C : Type*} [Countable A] [Countable B] [Countable C]
    (w : A → ℝ) (u : B → ℝ) (v : C → ℝ)
    (a : A → ι → ℤ) (b : B → ι → ℤ) (c : C → ι → ℤ)
    (hw : Summable w) (hu : Summable u) (hv : Summable v)
    (hw0 : ∀ i, 0 ≤ w i) (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (s r : UnitAddTorus ι) :
    ‖∫ t : UnitAddTorus ι,
      (∑' i, (w i : ℂ) * mFourier (a i) t) *
        (∑' j, (u j : ℂ) * mFourier (b j) (t + s)) *
          (∑' k, (v k : ℂ) * mFourier (c k) (t + r))
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ ≤
      (∫ t : UnitAddTorus ι,
        (∑' i, (w i : ℂ) * mFourier (a i) t) *
          (∑' j, (u j : ℂ) * mFourier (b j) t) *
            (∑' k, (v k : ℂ) * mFourier (c k) t)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)).re := by
  let W : (A × B) × C → ℝ := fun p => w p.1.1 * u p.1.2 * v p.2
  let N : (A × B) × C → ι → ℤ := fun p => a p.1.1 + b p.1.2 + c p.2
  let Z : (A × B) × C → ℂ := fun p => mFourier (b p.1.2) s * mFourier (c p.2) r
  have hW : Summable W :=
    summable_mul_of_summable_norm (summable_mul_of_summable_norm hw.norm hu.norm).norm hv.norm
  have hW0 (p) : 0 ≤ W p := mul_nonneg (mul_nonneg (hw0 _) (hu0 _)) (hv0 _)
  have hZ (p) : ‖Z p‖ = 1 := by simp [Z, norm_mFourier_apply]
  have hexpand (s r t : UnitAddTorus ι) :
      (∑' i, (w i : ℂ) * mFourier (a i) t) *
        (∑' j, (u j : ℂ) * mFourier (b j) (t + s)) *
          (∑' k, (v k : ℂ) * mFourier (c k) (t + r)) =
        ∑' p : (A × B) × C, (W p : ℂ) *
          (mFourier (b p.1.2) s * mFourier (c p.2) r) * mFourier (N p) t := by
    have hwC : Summable fun i => ‖(w i : ℂ)‖ := by simpa using hw.norm
    have huC : Summable fun j => ‖(u j : ℂ) * mFourier (b j) s‖ := by
      simpa only [norm_mul, norm_mFourier_apply, mul_one, Complex.norm_real] using hu.norm
    have hvC : Summable fun k => ‖(v k : ℂ) * mFourier (c k) r‖ := by
      simpa only [norm_mul, norm_mFourier_apply, mul_one, Complex.norm_real] using hv.norm
    have hshift (z : ℝ) (n : ι → ℤ) (t s : UnitAddTorus ι) :
        (z : ℂ) * mFourier n (t + s) =
          ((z : ℂ) * mFourier n s) * mFourier n t := by rw [mFourier_apply_add]; ring
    simp_rw [hshift]
    rw [tsum_mul_mFourier_mul_tsum_mul_mFourier _ _ _ _ hwC huC]
    rw [tsum_mul_mFourier_mul_tsum_mul_mFourier _ _ _ _
      (summable_mul_of_summable_norm hwC huC).norm hvC]
    apply tsum_congr
    intro p
    simp only [W, N, Complex.ofReal_mul]
    ring
  have h := norm_integral_phase_mFourier_series_le W N Z hW hW0 hZ
  have hzero (n : ι → ℤ) : mFourier n (0 : UnitAddTorus ι) = 1 := by
    simp [mFourier]
  have hplain (t : UnitAddTorus ι) :
      (∑' i, (w i : ℂ) * mFourier (a i) t) *
        (∑' j, (u j : ℂ) * mFourier (b j) t) *
          (∑' k, (v k : ℂ) * mFourier (c k) t) =
        ∑' p : (A × B) × C, (W p : ℂ) * mFourier (N p) t := by
    simpa only [add_zero, hzero, mul_one] using hexpand 0 0 t
  simpa only [hexpand, hplain, Z] using h

end PercLib.Analysis
