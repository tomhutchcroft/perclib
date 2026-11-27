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
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import PercLib.Analysis.LatticeFourier.ShiftedResolvent
public import PercLib.Analysis.LatticeFourier.Bounds
public import PercLib.Analysis.NearestNeighborResolventSmallPowers

/-!
# The shifted joining integral

## Main results

Hölder's inequality and translation invariance bound the nine-factor joining
integral by two unweighted cubic integrals and one squared-weight cubic integral.
The estimate holds for arbitrary shifts and nonnegative measurable kernels.
For the actual nearest-neighbour resolvent, the normalized physical-frequency
integral is at most `S₃² B₃`, with coefficient one. A domination corollary
integrates the three shifted terms in the canonical second-difference majorant.
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

namespace PercLib.Analysis

open UnitAddTorus

/-- The joining estimate for continuous nonnegative kernels on the normalized
unit torus, with ordinary real integrals. -/
theorem integral_torus_joining_product_le {ι : Type*} [Fintype ι]
    (D C : UnitAddTorus ι → ℝ) (hD : Continuous D) (hC : Continuous C)
    (hD0 : ∀ t, 0 ≤ D t) (hC0 : ∀ t, 0 ≤ C t) (a b : UnitAddTorus ι) :
    (∫ l₁ : UnitAddTorus ι, ∫ l₂ : UnitAddTorus ι, ∫ l₃ : UnitAddTorus ι,
      D l₁ * C l₁ ^ 2 * D l₂ * C l₂ ^ 2 * C (l₃ + a) * C (l₃ + b) *
        C (l₁ - l₂) * C (l₂ - l₃) * C (l₁ - l₃)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
      (∫ l : UnitAddTorus ι, C l ^ 3
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ^ 2 *
      (∫ l : UnitAddTorus ι, D l ^ 2 * C l ^ 3
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) := by
  let μ : Measure (UnitAddTorus ι) := Measure.pi (fun _ => AddCircle.haarAddCircle)
  let : OpensMeasurableSpace (UnitAddTorus ι × UnitAddTorus ι) :=
    Prod.opensMeasurableSpace
  let : OpensMeasurableSpace (UnitAddTorus ι × UnitAddTorus ι × UnitAddTorus ι) :=
    Prod.opensMeasurableSpace
  let : μ.IsNegInvariant := Measure.pi.isNegInvariant _
  let f : UnitAddTorus ι × UnitAddTorus ι × UnitAddTorus ι → ℝ := fun l =>
    D l.1 * C l.1 ^ 2 * D l.2.1 * C l.2.1 ^ 2 * C (l.2.2 + a) * C (l.2.2 + b) *
      C (l.1 - l.2.1) * C (l.2.1 - l.2.2) * C (l.1 - l.2.2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf0 (l) : 0 ≤ f l := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (hD0 _) (sq_nonneg _)) (hD0 _)) (sq_nonneg _))
        (hC0 _)) (hC0 _)) (hC0 _)) (hC0 _)) (hC0 _)
  have hfi : Integrable f (μ.prod (μ.prod μ)) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCi : Integrable (fun l => C l ^ 3) μ :=
    (hC.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDi : Integrable (fun l => D l ^ 2 * C l ^ 3) μ :=
    ((hD.pow 2).mul (hC.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCmass : 0 ≤ ∫ l, C l ^ 3 ∂μ := integral_nonneg fun l => pow_nonneg (hC0 l) _
  have hDmass : 0 ≤ ∫ l, D l ^ 2 * C l ^ 3 ∂μ :=
    integral_nonneg fun l => mul_nonneg (sq_nonneg _) (pow_nonneg (hC0 l) _)
  have h := lintegral_joining_product_le μ (fun l => ENNReal.ofReal (D l))
    (fun l => ENNReal.ofReal (C l)) hD.measurable.ennreal_ofReal
    hC.measurable.ennreal_ofReal a b
  have he (l₁ l₂ l₃ : UnitAddTorus ι) :
      ENNReal.ofReal (f (l₁, l₂, l₃)) =
        ENNReal.ofReal (D l₁) * ENNReal.ofReal (C l₁) ^ 2 *
          ENNReal.ofReal (D l₂) * ENNReal.ofReal (C l₂) ^ 2 *
          ENNReal.ofReal (C (l₃ + a)) * ENNReal.ofReal (C (l₃ + b)) *
          ENNReal.ofReal (C (l₁ - l₂)) * ENNReal.ofReal (C (l₂ - l₃)) *
          ENNReal.ofReal (C (l₁ - l₃)) := by
    simp only [f, mul_assoc, ENNReal.ofReal_mul (hD0 _), ENNReal.ofReal_mul (hC0 _),
      ENNReal.ofReal_mul (pow_nonneg (hC0 _) 2), ENNReal.ofReal_pow (hC0 _)]
  have hCpoint (l : UnitAddTorus ι) :
      ENNReal.ofReal (C l) ^ 3 = ENNReal.ofReal (C l ^ 3) :=
    (ENNReal.ofReal_pow (hC0 l) 3).symm
  have hDpoint (l : UnitAddTorus ι) :
      ENNReal.ofReal (D l) ^ 2 * ENNReal.ofReal (C l) ^ 3 =
        ENNReal.ofReal (D l ^ 2 * C l ^ 3) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (hD0 l), hCpoint]
  simp_rw [← he, hDpoint, hCpoint] at h
  rw [← lintegral_three μ (fun l => ENNReal.ofReal (f l)) hf.measurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hCi
      (Filter.Eventually.of_forall fun l => pow_nonneg (hC0 l) 3),
    ← ofReal_integral_eq_lintegral_ofReal hDi
      (Filter.Eventually.of_forall fun l => mul_nonneg (sq_nonneg _) (pow_nonneg (hC0 l) 3)),
    ← ENNReal.ofReal_pow hCmass,
    ← ENNReal.ofReal_mul (sq_nonneg _)] at h
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) hDmass)).mp h
  rw [integral_prod _ hfi] at hreal
  have hsection (l₁ : UnitAddTorus ι) :
      Integrable (fun l : UnitAddTorus ι × UnitAddTorus ι => f (l₁, l)) (μ.prod μ) :=
    (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [integral_prod _ (hsection _)] at hreal
  exact hreal

open Metric Real in
/-- The actual nearest-neighbour joining integral in physical frequencies has
the sharp Hölder constant one, uniformly in its two arbitrary shifts. -/
theorem integral_nearestNeighbor_joining_product_le {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (a b : Fin d → ℝ) :
    (((2 * π) ^ d)⁻¹) ^ 3 *
      (∫ l₁ in ball (0 : Fin d → ℝ) π, ∫ l₂ in ball (0 : Fin d → ℝ) π,
        ∫ l₃ in ball (0 : Fin d → ℝ) π,
          |nearestNeighborSymbol l₁| * nearestNeighborResolvent r l₁ ^ 2 *
            |nearestNeighborSymbol l₂| * nearestNeighborResolvent r l₂ ^ 2 *
            nearestNeighborResolvent r (l₃ + a) * nearestNeighborResolvent r (l₃ + b) *
            nearestNeighborResolvent r (l₁ - l₂) * nearestNeighborResolvent r (l₂ - l₃) *
            nearestNeighborResolvent r (l₁ - l₃)) ≤
      (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
        nearestNeighborResolvent r l ^ 3) ^ 2 *
      (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
        nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) := by
  classical
  let q : (Fin d → ℝ) → UnitAddTorus (Fin d) :=
    fun k i => ((k i / (2 * π) : ℝ) : UnitAddCircle)
  let D : UnitAddTorus (Fin d) → ℝ := fun t =>
    (∑ a : Fin d × Bool, (((2 * d : ℝ)⁻¹ : ℝ) : ℂ) *
      mFourier (Function.update (0 : Fin d → ℤ) a.1 (if a.2 then 1 else -1)) t).re
  let C : UnitAddTorus (Fin d) → ℝ := fun t => (1 - r * D t)⁻¹
  have hD (k : Fin d → ℝ) : D (q k) = nearestNeighborSymbol k := by
    simpa only [D, q, Complex.ofReal_re] using
      congrArg Complex.re (nearestNeighbor_direction_symbol hd k)
  have hC (k : Fin d → ℝ) : C (q k) = nearestNeighborResolvent r k := by
    change (1 - r * D (q k))⁻¹ = _
    rw [hD]
    rfl
  have hq : Function.Surjective q := by
    intro t
    choose x hx using fun i => QuotientAddGroup.mk_surjective (t i)
    refine ⟨fun i => 2 * π * x i, ?_⟩
    funext i
    dsimp only [q]
    rw [mul_div_cancel_left₀ _ (show 2 * π ≠ 0 by positivity)]
    exact hx i
  have hDcont : Continuous D := by dsimp [D]; fun_prop
  have hden (t : UnitAddTorus (Fin d)) : 0 < 1 - r * D t := by
    obtain ⟨k, rfl⟩ := hq t
    rw [hD]
    exact nearestNeighborResolvent_den_pos hd hr k
  have hCcont : Continuous C :=
    (continuous_const.sub (continuous_const.mul hDcont)).inv₀ fun t => (hden t).ne'
  have hC0 (t : UnitAddTorus (Fin d)) : 0 ≤ C t := (inv_pos.mpr (hden t)).le
  have hqadd (k l : Fin d → ℝ) : q k + q l = q (k + l) := by
    funext i
    simp only [q, Pi.add_apply, add_div, AddCircle.coe_add]
  have hqsub (k l : Fin d → ℝ) : q k - q l = q (k - l) := by
    funext i
    simp only [q, Pi.sub_apply, sub_div, AddCircle.coe_sub]
  have h := integral_torus_joining_product_le (fun t => |D t|) C hDcont.abs hCcont
    (fun t => abs_nonneg _) hC0 (q a) (q b)
  simp_rw [integral_unitTorus_eq_normalized_box, smul_eq_mul] at h
  change (((2 * π) ^ d)⁻¹ * ∫ l₁ in ball (0 : Fin d → ℝ) π,
    ((2 * π) ^ d)⁻¹ * ∫ l₂ in ball (0 : Fin d → ℝ) π,
    ((2 * π) ^ d)⁻¹ * ∫ l₃ in ball (0 : Fin d → ℝ) π,
      |D (q l₁)| * C (q l₁) ^ 2 * |D (q l₂)| * C (q l₂) ^ 2 *
        C (q l₃ + q a) * C (q l₃ + q b) * C (q l₁ - q l₂) *
        C (q l₂ - q l₃) * C (q l₁ - q l₃)) ≤
      (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π, C (q l) ^ 3) ^ 2 *
      (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
        |D (q l)| ^ 2 * C (q l) ^ 3) at h
  simp_rw [hqadd, hqsub, hD, hC, sq_abs] at h
  simp_rw [integral_const_mul (((2 * π) ^ d)⁻¹)] at h
  convert h using 1
  ring


open Metric Real in
/-- A continuous nonnegative integrand dominated by the three actual joining
products costs their sum. Finiteness follows from the massive resolvent bound. -/
theorem integral_le_of_nearestNeighbor_joining_majorant {d : ℕ} (hd : 0 < d)
    {r A : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (hA : 0 ≤ A) (k : Fin d → ℝ)
    (f : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (hf : Continuous f) (hf0 : ∀ l, 0 ≤ f l)
    (hbound : ∀ l₁ l₂ l₃ : Fin d → ℝ,
      let C := nearestNeighborResolvent r
      let Q := fun a b : Fin d → ℝ =>
        |nearestNeighborSymbol l₁| * C l₁ ^ 2 * |nearestNeighborSymbol l₂| * C l₂ ^ 2 *
          C (l₃ + a) * C (l₃ + b) * C (l₁ - l₂) * C (l₂ - l₃) * C (l₁ - l₃)
      f (l₁, l₂, l₃) ≤ A * (Q (-k) 0 + Q 0 k + Q (-k) k)) :
    (((2 * π) ^ d)⁻¹) ^ 3 *
      (∫ l₁ in ball (0 : Fin d → ℝ) π, ∫ l₂ in ball (0 : Fin d → ℝ) π,
        ∫ l₃ in ball (0 : Fin d → ℝ) π, f (l₁, l₂, l₃)) ≤
      3 * A *
        (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborResolvent r l ^ 3) ^ 2 *
        (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) := by
  let E := Fin d → ℝ
  let ν : Measure E := volume.restrict (ball 0 π)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    ((measure_mono (ball_subset_closedBall (x := (0 : E)) (ε := π))).trans_lt
      (isCompact_closedBall (0 : E) π).measure_lt_top).ne
  let C := nearestNeighborResolvent (d := d) r
  let B := (1 - r)⁻¹
  let N := ((2 * π) ^ d)⁻¹
  let Q := fun (a b : E) (l : E × E × E) =>
    |nearestNeighborSymbol l.1| * C l.1 ^ 2 * |nearestNeighborSymbol l.2.1| * C l.2.1 ^ 2 *
      C (l.2.2 + a) * C (l.2.2 + b) * C (l.1 - l.2.1) * C (l.2.1 - l.2.2) *
      C (l.1 - l.2.2)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hB : 0 ≤ B := (inv_pos.mpr (sub_pos.mpr hr.2)).le
  have hC : Continuous C := continuous_nearestNeighborResolvent hd hr
  have hD : Continuous (nearestNeighborSymbol (d := d)) := by
    unfold nearestNeighborSymbol
    fun_prop
  have hC0 (l : E) : 0 ≤ C l := (nearestNeighborResolvent_pos hd hr l).le
  have hQ (a b : E) : Continuous (Q a b) := by dsimp only [Q]; fun_prop
  have hQ0 (a b : E) (l : E × E × E) : 0 ≤ Q a b l := by
    dsimp only [Q]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (abs_nonneg _)) (sq_nonneg _))
        (hC0 _)) (hC0 _)) (hC0 _)) (hC0 _)) (hC0 _)
  have hQB (a b : E) (l : E × E × E) : Q a b l ≤ B ^ 9 := by
    calc
      _ ≤ 1 * B ^ 2 * 1 * B ^ 2 * B * B * B * B * B := by
        dsimp only [Q]
        gcongr <;> first
          | exact nearestNeighborSymbol_abs_le_one hd _
          | exact nearestNeighborResolvent_le_inv_one_sub hd hr _
          | exact hC0 _
      _ = _ := by ring
  have hQbound (a b : E) (l : E × E × E) : ‖Q a b l‖ ≤ B ^ 9 := by
    rw [Real.norm_of_nonneg (hQ0 a b l)]
    exact hQB a b l
  have hfB (l : E × E × E) : ‖f l‖ ≤ A * (3 * B ^ 9) := by
    rw [Real.norm_of_nonneg (hf0 l)]
    calc
      _ ≤ A * (Q (-k) 0 l + Q 0 k l + Q (-k) k l) := hbound l.1 l.2.1 l.2.2
      _ ≤ A * (B ^ 9 + B ^ 9 + B ^ 9) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hQB _ _ _) (hQB _ _ _))
          (hQB _ _ _)) hA
      _ = _ := by ring
  have hQi (a b : E) : Integrable (Q a b) (ν.prod (ν.prod ν)) :=
    Integrable.of_bound (hQ a b).aestronglyMeasurable (B ^ 9)
      (Filter.Eventually.of_forall (hQbound a b))
  have hfi : Integrable f (ν.prod (ν.prod ν)) :=
    Integrable.of_bound hf.aestronglyMeasurable (A * (3 * B ^ 9))
      (Filter.Eventually.of_forall hfB)
  have hQsection (a b l₁ : E) :
      Integrable (fun l : E × E => Q a b (l₁, l)) (ν.prod ν) :=
    Integrable.of_bound ((hQ a b).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (B ^ 9) (Filter.Eventually.of_forall fun l => hQbound a b (l₁, l))
  have hfsection (l₁ : E) : Integrable (fun l : E × E => f (l₁, l)) (ν.prod ν) :=
    Integrable.of_bound (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (A * (3 * B ^ 9)) (Filter.Eventually.of_forall fun l => hfB (l₁, l))
  have hfint : (∫ l, f l ∂ν.prod (ν.prod ν)) =
      ∫ l₁, ∫ l₂, ∫ l₃, f (l₁, l₂, l₃) ∂ν ∂ν ∂ν := by
    rw [integral_prod _ hfi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun l₁ => integral_prod _ (hfsection l₁)
  have hi := integral_mono hfi (((hQi (-k) 0).add (hQi 0 k)).add (hQi (-k) k) |>.const_mul A)
    (fun l => hbound l.1 l.2.1 l.2.2)
  rw [integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add (f := fun l => Q (-k) 0 l + Q 0 k l) (g := Q (-k) k)
    ((hQi (-k) 0).add (hQi 0 k)) (hQi (-k) k),
    integral_add (hQi (-k) 0) (hQi 0 k), hfint] at hi
  have hQint (a b : E) :
      (∫ l, Q a b l ∂ν.prod (ν.prod ν)) =
        ∫ l₁, ∫ l₂, ∫ l₃, Q a b (l₁, l₂, l₃) ∂ν ∂ν ∂ν := by
    rw [integral_prod _ (hQi a b)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun l₁ => integral_prod _ (hQsection a b l₁)
  simp_rw [hQint] at hi
  let S₃ := N * ∫ l in ball (0 : E) π, C l ^ 3
  let B₃ := N * ∫ l in ball (0 : E) π, nearestNeighborSymbol l ^ 2 * C l ^ 3
  have hNN (a b : E) :
      N ^ 3 * (∫ l₁, ∫ l₂, ∫ l₃, Q a b (l₁, l₂, l₃) ∂ν ∂ν ∂ν) ≤ S₃ ^ 2 * B₃ :=
    integral_nearestNeighbor_joining_product_le hd hr a b
  calc
    _ ≤ A * (N ^ 3 * (∫ l₁, ∫ l₂, ∫ l₃, Q (-k) 0 (l₁, l₂, l₃) ∂ν ∂ν ∂ν) +
        N ^ 3 * (∫ l₁, ∫ l₂, ∫ l₃, Q 0 k (l₁, l₂, l₃) ∂ν ∂ν ∂ν) +
        N ^ 3 * (∫ l₁, ∫ l₂, ∫ l₃, Q (-k) k (l₁, l₂, l₃) ∂ν ∂ν ∂ν)) := by
      convert mul_le_mul_of_nonneg_left hi (pow_nonneg hN 3) using 1
      ring
    _ ≤ A * (S₃ ^ 2 * B₃ + S₃ ^ 2 * B₃ + S₃ ^ 2 * B₃) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hNN (-k) 0) (hNN 0 k))
        (hNN (-k) k)) hA
    _ = _ := by dsimp only [S₃, B₃, N, C, E]; ring

end PercLib.Analysis
