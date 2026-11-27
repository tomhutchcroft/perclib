/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original integral estimate for the joining diagram; no upstream Lean code is copied.
Mathematical reference: Heydenreich and van der Hofstad (2017), Section 8.3.
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The shifted joining integral

## Main results

Hölder's inequality and translation invariance bound the nine-factor joining
integral by two unweighted cubic integrals and one squared-weight cubic integral.
The estimate holds for arbitrary shifts and nonnegative measurable kernels.
-/

@[expose] public section
noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace PercLib.Analysis

variable {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]

private theorem lintegral_three (f : G × G × G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ l, f l ∂μ.prod (μ.prod μ)) =
      ∫⁻ l₁, ∫⁻ l₂, ∫⁻ l₃, f (l₁, l₂, l₃) ∂μ ∂μ ∂μ := by
  rw [lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro l₁
  exact lintegral_prod _ (by fun_prop)

variable [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  [IsAddLeftInvariant μ] [IsNegInvariant μ]

omit [SFinite μ] in
private theorem lintegral_shifted_three_halves_mul_le
    (C : G → ℝ≥0∞) (hC : Measurable C) (a b : G) :
    (∫⁻ l, C (l + b) ^ (3 / 2 : ℝ) * C (a - l) ^ (3 / 2 : ℝ) ∂μ) ≤
      ∫⁻ l, C l ^ 3 ∂μ := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp
    (f := fun l => C (l + b) ^ (3 / 2 : ℝ))
    (g := fun l => C (a - l) ^ (3 / 2 : ℝ))
    ((hC.comp (measurable_id.add_const b)).pow_const _).aemeasurable
    ((hC.comp (measurable_const.sub measurable_id)).pow_const _).aemeasurable
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at h
  norm_num at h
  rw [lintegral_add_right_eq_self (μ := μ) (fun l => C l ^ 3) b,
    lintegral_sub_left_eq_self (μ := μ) (fun l => C l ^ 3) a] at h
  refine h.trans_eq ?_
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

omit [SFinite μ] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  [IsAddLeftInvariant μ] [IsNegInvariant μ] in
private theorem lintegral_weight_three_halves_le
    (D C : G → ℝ≥0∞) (hD : Measurable D) (hC : Measurable C) :
    (∫⁻ l, D l ^ (3 / 2 : ℝ) * C l ^ 3 ∂μ) ≤
      (∫⁻ l, D l ^ 2 * C l ^ 3 ∂μ) ^ (3 / 4 : ℝ) *
        (∫⁻ l, C l ^ 3 ∂μ) ^ (1 / 4 : ℝ) := by
  have hp : (4 / 3 : ℝ).HolderConjugate 4 := by
    norm_num [Real.holderConjugate_iff]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp
    (f := fun l => D l ^ (3 / 2 : ℝ) * C l ^ (9 / 4 : ℝ))
    (g := fun l => C l ^ (3 / 4 : ℝ))
    ((hD.pow_const _).mul (hC.pow_const _)).aemeasurable
    (hC.pow_const _).aemeasurable
  simp only [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4 / 3),
    ← ENNReal.rpow_mul] at h
  norm_num at h
  have he (l : G) :
      (D l ^ (3 / 2 : ℝ) * C l ^ (9 / 4 : ℝ)) * C l ^ (3 / 4 : ℝ) =
        D l ^ (3 / 2 : ℝ) * C l ^ 3 := by
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  simpa only [he] using h

/-- The joining integral with arbitrary shifts is bounded by two cubic
kernel masses and one cubic mass weighted by the square of the symbol.
This is an extended-real inequality; no integrability is assumed. -/
theorem lintegral_joining_product_le
    (D C : G → ℝ≥0∞) (hD : Measurable D) (hC : Measurable C) (a b : G) :
    (∫⁻ l₁, ∫⁻ l₂, ∫⁻ l₃,
      D l₁ * C l₁ ^ 2 * D l₂ * C l₂ ^ 2 * C (l₃ + a) * C (l₃ + b) *
        C (l₁ - l₂) * C (l₂ - l₃) * C (l₁ - l₃) ∂μ ∂μ ∂μ) ≤
      (∫⁻ l, C l ^ 3 ∂μ) ^ 2 * (∫⁻ l, D l ^ 2 * C l ^ 3 ∂μ) := by
  let X : G × G × G → ℝ≥0∞ := fun l =>
    D l.1 * C l.1 ^ 2 * D l.2.1 * C l.2.1 ^ 2 * C (l.2.2 + b) * C (l.1 - l.2.2)
  let Y : G × G × G → ℝ≥0∞ := fun l =>
    C (l.1 - l.2.1) * C (l.2.1 - l.2.2) * C (l.2.2 + a)
  let S₀ := ∫⁻ l, C l ^ 3 ∂μ
  let S₂ := ∫⁻ l, D l ^ 2 * C l ^ 3 ∂μ
  let S₁ := ∫⁻ l, D l ^ (3 / 2 : ℝ) * C l ^ 3 ∂μ
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hXpow : (∫⁻ l, X l ^ (3 / 2 : ℝ) ∂μ.prod (μ.prod μ)) ≤ S₀ * S₁ ^ 2 := by
    rw [lintegral_three μ _ (hX.pow_const _)]
    let A : G → ℝ≥0∞ := fun l => D l ^ (3 / 2 : ℝ) * C l ^ 3
    have hA : Measurable A := (hD.pow_const _).mul (hC.pow_const _)
    have he (l₁ l₂ l₃ : G) : X (l₁, l₂, l₃) ^ (3 / 2 : ℝ) =
        (D l₁ ^ (3 / 2 : ℝ) * C l₁ ^ 3) *
          (D l₂ ^ (3 / 2 : ℝ) * C l₂ ^ 3) *
            (C (l₃ + b) ^ (3 / 2 : ℝ) * C (l₁ - l₃) ^ (3 / 2 : ℝ)) := by
      simp only [X, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      rw [← ENNReal.rpow_natCast (C l₁) 2, ← ENNReal.rpow_natCast (C l₂) 2]
      simp only [← ENNReal.rpow_mul]
      norm_num
      ring
    simp_rw [he]
    change (∫⁻ l₁, ∫⁻ l₂, ∫⁻ l₃,
      A l₁ * A l₂ *
        (C (l₃ + b) ^ (3 / 2 : ℝ) * C (l₁ - l₃) ^ (3 / 2 : ℝ)) ∂μ ∂μ ∂μ) ≤ _
    have hinner (l₁ l₂ : G) :
        (∫⁻ l₃, A l₁ * A l₂ *
          (C (l₃ + b) ^ (3 / 2 : ℝ) * C (l₁ - l₃) ^ (3 / 2 : ℝ)) ∂μ) =
          A l₁ * A l₂ *
            ∫⁻ l₃, C (l₃ + b) ^ (3 / 2 : ℝ) * C (l₁ - l₃) ^ (3 / 2 : ℝ) ∂μ := by
      exact lintegral_const_mul _
        (((hC.comp (measurable_id.add_const b)).pow_const _).mul
          ((hC.comp (measurable_const.sub measurable_id)).pow_const _))
    simp_rw [hinner]
    calc
      _ ≤ ∫⁻ l₁, ∫⁻ l₂,
          A l₁ * A l₂ * S₀ ∂μ ∂μ :=
        lintegral_mono fun l₁ => lintegral_mono fun l₂ => mul_le_mul' le_rfl
          (lintegral_shifted_three_halves_mul_le μ C hC l₁ b)
      _ = _ := by
        have hmiddle (l₁ : G) :
            (∫⁻ l₂, A l₁ * A l₂ * S₀ ∂μ) = A l₁ * S₁ * S₀ := by
          rw [lintegral_mul_const S₀ (μ := μ) (f := fun l₂ => A l₁ * A l₂)
            (by fun_prop), lintegral_const_mul (A l₁) hA]
        simp_rw [hmiddle]
        rw [lintegral_mul_const S₀ (μ := μ) (f := fun l₁ => A l₁ * S₁)
          (by fun_prop), lintegral_mul_const S₁ hA]
        change S₁ * S₁ * S₀ = S₀ * S₁ ^ 2
        ring
  have hYpow : (∫⁻ l, Y l ^ (3 : ℝ) ∂μ.prod (μ.prod μ)) = S₀ ^ 3 := by
    rw [lintegral_three μ _ (hY.pow_const _)]
    simp only [Y, ENNReal.rpow_ofNat, mul_pow]
    rw [lintegral_lintegral_swap (by fun_prop)]
    have hinner (l₂ : G) :
        (∫⁻ l₁, ∫⁻ l₃,
          C (l₁ - l₂) ^ 3 * C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3 ∂μ ∂μ) =
          S₀ * ∫⁻ l₃, C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3 ∂μ := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      have hsingle (l₃ : G) :
          (∫⁻ l₁, C (l₁ - l₂) ^ 3 * C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3 ∂μ) =
            S₀ * (C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3) := by
        rw [lintegral_mul_const (C (l₃ + a) ^ 3) (μ := μ)
          (f := fun l₁ => C (l₁ - l₂) ^ 3 * C (l₂ - l₃) ^ 3) (by fun_prop),
          lintegral_mul_const (C (l₂ - l₃) ^ 3) (μ := μ)
            (f := fun l₁ => C (l₁ - l₂) ^ 3) (by fun_prop),
          lintegral_sub_right_eq_self (μ := μ) (fun l => C l ^ 3) l₂]
        change S₀ * _ * _ = S₀ * (_ * _)
        rw [mul_assoc]
      simp_rw [hsingle]
      exact lintegral_const_mul S₀ (μ := μ)
        (f := fun l₃ => C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3) (by fun_prop)
    have hpair :
        (∫⁻ l₂, ∫⁻ l₃, C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3 ∂μ ∂μ) = S₀ ^ 2 := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      have hsingle (l₃ : G) :
          (∫⁻ l₂, C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3 ∂μ) =
            S₀ * C (l₃ + a) ^ 3 := by
        rw [lintegral_mul_const (C (l₃ + a) ^ 3) (μ := μ)
          (f := fun l₂ => C (l₂ - l₃) ^ 3) (by fun_prop),
          lintegral_sub_right_eq_self (μ := μ) (fun l => C l ^ 3) l₃]
      simp_rw [hsingle]
      rw [lintegral_const_mul S₀ (μ := μ) (f := fun l₃ => C (l₃ + a) ^ 3) (by fun_prop),
        lintegral_add_right_eq_self (μ := μ) (fun l => C l ^ 3) a]
      change S₀ * S₀ = S₀ ^ 2
      rw [pow_two]
    simp_rw [hinner]
    rw [lintegral_const_mul S₀ (f := fun l₂ =>
      ∫⁻ l₃, C (l₂ - l₃) ^ 3 * C (l₃ + a) ^ 3 ∂μ) (by fun_prop), hpair]
    ring
  have hp : (3 / 2 : ℝ).HolderConjugate 3 := by
    norm_num [Real.holderConjugate_iff]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod (μ.prod μ)) hp
    hX.aemeasurable hY.aemeasurable
  have hprod : (∫⁻ l, (X * Y) l ∂μ.prod (μ.prod μ)) =
      ∫⁻ l₁, ∫⁻ l₂, ∫⁻ l₃,
        D l₁ * C l₁ ^ 2 * D l₂ * C l₂ ^ 2 * C (l₃ + a) * C (l₃ + b) *
          C (l₁ - l₂) * C (l₂ - l₃) * C (l₁ - l₃) ∂μ ∂μ ∂μ := by
    rw [lintegral_three μ _ (hX.mul hY)]
    apply lintegral_congr
    intro l₁
    apply lintegral_congr
    intro l₂
    apply lintegral_congr
    intro l₃
    simp only [Pi.mul_apply, X, Y]
    ring
  rw [hprod, hYpow] at hh
  have hS := lintegral_weight_three_halves_le μ D C hD hC
  change S₁ ≤ S₂ ^ (3 / 4 : ℝ) * S₀ ^ (1 / 4 : ℝ) at hS
  calc
    _ ≤ (S₀ * S₁ ^ 2) ^ (2 / 3 : ℝ) * (S₀ ^ 3) ^ (1 / 3 : ℝ) := by
      refine hh.trans ?_
      norm_num only [one_div_div] at *
      exact mul_le_mul' (ENNReal.rpow_le_rpow hXpow (by norm_num)) le_rfl
    _ ≤ (S₀ * (S₂ ^ (3 / 4 : ℝ) * S₀ ^ (1 / 4 : ℝ)) ^ 2) ^ (2 / 3 : ℝ) *
        (S₀ ^ 3) ^ (1 / 3 : ℝ) := by
      gcongr
    _ = _ := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2 / 3),
        mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
      calc
        _ = (S₀ ^ (2 / 3 : ℝ) * S₀ ^ (1 / 3 : ℝ)) * S₀ * S₂ := by ring
        _ = _ := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num
          dsimp only [S₀, S₂]
          ring

end PercLib.Analysis
