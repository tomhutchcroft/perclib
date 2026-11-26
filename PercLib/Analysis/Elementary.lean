/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Shared elementary analysis lemmas, collected on 2026-11-16 from proofs already in this library, so
that each statement is proved once. No upstream proof is copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Elementary analysis helpers

* `integral_le_sub_of_ae_le_deriv`: the fundamental theorem of calculus in inequality form
  for an absolutely continuous function.
* `lipschitzOnWith_inv_Ici`: `x ↦ x⁻¹` is `1/m²`-Lipschitz on `[m, ∞)`.
* `sum_Icc_one_div_sqrt_le_two_mul`: `∑_{k=1}^n k^{-1/2} ≤ 2√n`.
* `exp_neg_mul_top`: `e^{-h·⊤} = 0` in `EReal` for `h > 0`.

None of these is in mathlib at the pinned revision. This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset intervalIntegral
open scoped ENNReal

namespace PercLib.Analysis

/-- If `f` is absolutely continuous on `[a, b]` and `g ≤ f'` a.e. there, with `g` integrable,
then `∫_a^b g ≤ f b - f a`. -/
theorem integral_le_sub_of_ae_le_deriv {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ᵐ x, x ∈ Icc a b → g x ≤ deriv f x) :
    ∫ x in a..b, g x ≤ f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  exact integral_mono_ae_restrict hab hg hf.intervalIntegrable_deriv
    ((ae_restrict_iff' measurableSet_Icc).2 h)

/-- `x ↦ x⁻¹` is Lipschitz on `[m, ∞)` for `m > 0`, with constant `1/m²`. -/
theorem lipschitzOnWith_inv_Ici {m : ℝ} (hm : 0 < m) :
    LipschitzOnWith (Real.toNNReal (1 / m ^ 2)) (fun x : ℝ => x⁻¹) (Ici m) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hm hy
  rw [Real.dist_eq, Real.dist_eq, inv_sub_inv hx0.ne' hy0.ne', abs_div,
    abs_of_pos (mul_pos hx0 hy0),
    abs_sub_comm]
  rw [div_le_iff₀ (mul_pos hx0 hy0)]
  have hxy : m ^ 2 ≤ x * y := by nlinarith [mem_Ici.1 hx, mem_Ici.1 hy]
  have h1 : 0 ≤ |x - y| := abs_nonneg _
  have : 1 / m ^ 2 * |x - y| * (x * y) ≥ |x - y| := by
    rw [mul_assoc, ge_iff_le, ← sub_nonneg]
    have : 1 / m ^ 2 * (|x - y| * (x * y)) - |x - y| = |x - y| * (x * y - m ^ 2) / m ^ 2 := by
      field_simp
    rw [this]
    exact div_nonneg (mul_nonneg h1 (by linarith)) (by positivity)
  rw [Real.coe_toNNReal _ (by positivity)]
  linarith

/-- `∑_{k=1}^n k^{-1/2} ≤ 2√n`. -/
theorem sum_Icc_one_div_sqrt_le_two_mul (n : ℕ) :
    ∑ k ∈ Icc 1 n, 1 / Real.sqrt k ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_succ]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hs : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.2 (by linarith)
    have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
    have hlt : Real.sqrt m ≤ Real.sqrt (m + 1) := Real.sqrt_le_sqrt (by linarith)
    have hsq : Real.sqrt (m + 1) ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
    have hsq' : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
    have key : 1 / Real.sqrt (m + 1) ≤ 2 * (Real.sqrt (m + 1) - Real.sqrt m) := by
      rw [div_le_iff₀ hs]
      nlinarith
    linarith

/-- At infinite volume, `e^{-h·⊤} = 0` in `EReal` for `h > 0`. -/
theorem exp_neg_mul_top {h : ℝ} (hh : 0 < h) :
    EReal.exp (-((h : EReal) * (((⊤ : ℕ∞) : ℝ≥0∞) : EReal))) = 0 := by
  simp [EReal.coe_mul_top_of_pos hh]

end PercLib.Analysis

end
