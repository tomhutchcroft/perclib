/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.CosineGaussian
public import PercLib.Analysis.NearestNeighborMoments
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

/-!
# Exponential majorants for the nearest-neighbour walk symbol

## Main results

Powers of the absolute ordinary nearest-neighbour symbol are bounded by a
product of one-dimensional exponential factors. The absolute cosine retains
control at the negative corner of the torus, where the ordinary symbol is
close to minus one.
-/

@[expose] public section

open Real MeasureTheory
open scoped BigOperators

namespace PercLib.Analysis

/-- The absolute symbol is bounded by the average absolute coordinate cosine. -/
theorem abs_nearestNeighborSymbol_le {d : ℕ} (k : Fin d → ℝ) :
    |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ≤ (d : ℝ)⁻¹ * ∑ i, |cos (k i)| := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- The ordinary nearest-neighbour symbol has absolute value at most one. -/
theorem abs_nearestNeighborSymbol_le_one {d : ℕ} (hd : 0 < d) (k : Fin d → ℝ) :
    |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ≤ 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ ≤ (d : ℝ)⁻¹ * ∑ i, |cos (k i)| := abs_nearestNeighborSymbol_le k
    _ ≤ (d : ℝ)⁻¹ * ∑ _i : Fin d, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => abs_cos_le_one _)
        (by positivity)
    _ = 1 := by simp [hd0]

/-- Absolute powers admit a product exponential bound, suitable for independent
coordinate integration. It applies on the whole torus, including its negative corner. -/
theorem abs_nearestNeighborSymbol_pow_le_prod_exp {d : ℕ} (hd : 0 < d)
    (n : ℕ) (k : Fin d → ℝ) :
    |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ^ n ≤
      ∏ i, exp ((n : ℝ) / d * (|cos (k i)| - 1)) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have heq : (d : ℝ)⁻¹ * (∑ i, |cos (k i)|) =
      (d : ℝ)⁻¹ * (∑ i, (|cos (k i)| - 1)) + 1 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    ring
  have hbase := (abs_nearestNeighborSymbol_le k).trans
    (heq.trans_le (add_one_le_exp _))
  calc
    _ ≤ (exp ((d : ℝ)⁻¹ * ∑ i, (|cos (k i)| - 1))) ^ n :=
      pow_le_pow_left₀ (abs_nonneg _) hbase n
    _ = exp (∑ i, (n : ℝ) / d * (|cos (k i)| - 1)) := by
      rw [← exp_nat_mul, Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := exp_sum _ _

/-- On the central half box the product majorant has an explicit Gaussian
decay rate. The full-torus estimate above handles the other periodic corners. -/
theorem abs_nearestNeighborSymbol_pow_le_gaussian {d : ℕ} (hd : 0 < d)
    (n : ℕ) (k : Fin d → ℝ) (hk : ∀ i, |k i| ≤ π / 2) :
    |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ^ n ≤
      exp (-(4 * (n : ℝ) / ((d : ℝ) * π ^ 2)) * ∑ i, (k i) ^ 2) := by
  apply (abs_nearestNeighborSymbol_pow_le_prod_exp hd n k).trans
  rw [← exp_sum]
  apply exp_le_exp.mpr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hcos0 : 0 ≤ cos (k i) := cos_nonneg_of_mem_Icc (abs_le.mp (hk i))
  have hcos := four_mul_sq_div_pi_sq_le_one_sub_cos (hk i)
  have hcos' : 4 / π ^ 2 * (k i) ^ 2 ≤ 1 - cos (k i) := by
    calc
      _ = 4 * (k i) ^ 2 / π ^ 2 := by ring
      _ ≤ _ := hcos
  rw [abs_of_nonneg hcos0]
  have h := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.mpr (by nlinarith :
      cos (k i) ≤ -(4 / π ^ 2 * (k i) ^ 2) + 1))
    (show (0 : ℝ) ≤ (n : ℝ) / d by positivity)
  convert h using 1
  ring

/-- Independent coordinate integration reduces the absolute-symbol moment to
a single one-dimensional integral. Any finite coordinate measure is allowed. -/
theorem integral_abs_nearestNeighborSymbol_pow_le {d : ℕ} (hd : 0 < d)
    (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ k : Fin d → ℝ, |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ^ n
      ∂Measure.pi (fun _ => μ)) ≤
        (∫ t : ℝ, exp ((n : ℝ) / d * (|cos t| - 1)) ∂μ) ^ d := by
  have hleft : Integrable (fun k : Fin d → ℝ =>
      |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ^ n) (Measure.pi (fun _ => μ)) := by
    apply Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
    exact Filter.Eventually.of_forall fun k => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_one₀ (abs_nonneg _) (abs_nearestNeighborSymbol_le_one hd k)
  have hright : Integrable (fun k : Fin d → ℝ =>
      ∏ i, exp ((n : ℝ) / d * (|cos (k i)| - 1))) (Measure.pi (fun _ => μ)) := by
    apply Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
    exact Filter.Eventually.of_forall fun k => by
      rw [Real.norm_of_nonneg (by positivity)]
      apply Finset.prod_le_one₀
      · intro i _
        exact (exp_pos _).le
      · intro i _
        apply exp_le_one_iff.mpr
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (sub_nonpos.mpr (abs_cos_le_one _))
  calc
    _ ≤ ∫ k : Fin d → ℝ, ∏ i, exp ((n : ℝ) / d * (|cos (k i)| - 1))
        ∂Measure.pi (fun _ => μ) := integral_mono hleft hright
      (abs_nearestNeighborSymbol_pow_le_prod_exp hd n)
    _ = _ := by
      simpa using integral_fintype_prod_eq_pow
        (ι := Fin d) (μ := μ) (fun t : ℝ => exp ((n : ℝ) / d * (|cos t| - 1)))

/-- An explicit bound for every positive absolute moment of the ordinary walk
symbol. This is the Gaussian tail estimate, with no unspecified dimension constants. -/
theorem normalized_integral_abs_nearestNeighborSymbol_pow_le {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    ((2 * π) ^ d)⁻¹ * (∫ k in Metric.ball (0 : Fin d → ℝ) π,
      |(d : ℝ)⁻¹ * ∑ i, cos (k i)| ^ n) ≤ (√(π * d / (4 * n : ℝ))) ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hperiod : 0 < 2 * π := by positivity
  have hmoment := integral_abs_nearestNeighborSymbol_pow_le hd n
    (volume.restrict (Set.Ioo (-π) π))
  have hscalar := integral_exp_abs_cos_sub_one_div_two_pi_le (div_pos hn0 hd0)
  have hnonneg : 0 ≤ (∫ t in Set.Ioo (-π) π,
      exp ((n : ℝ) / d * (|cos t| - 1))) / (2 * π) :=
    div_nonneg (integral_nonneg fun t => (exp_pos _).le) hperiod.le
  rw [volume_restrict_pi_ball_eq_pi_Ioo]
  calc
    _ ≤ ((2 * π) ^ d)⁻¹ *
        (∫ t in Set.Ioo (-π) π, exp ((n : ℝ) / d * (|cos t| - 1))) ^ d :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = ((∫ t in Set.Ioo (-π) π, exp ((n : ℝ) / d * (|cos t| - 1))) /
        (2 * π)) ^ d := by rw [div_pow]; ring
    _ ≤ (√(π / (4 * ((n : ℝ) / d)))) ^ d := pow_le_pow_left₀ hnonneg hscalar d
    _ = _ := by
      congr 2
      field_simp

end PercLib.Analysis
