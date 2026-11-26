/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: the binomial expansion of subcritical nearest-neighbour
walk resolvents, integrated over the Fourier torus.
-/
module

public import PercLib.Analysis.NearestNeighborPairing
public import PercLib.Analysis.NearestNeighborSymbolBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Nearest-neighbour resolvents as even-moment series

Odd torus moments vanish by coordinate integration. For every subcritical parameter,
the binomial series is dominated by a summable geometric-polynomial majorant, so its
integral equals the series of the even moments. Capping the factorial pairing bound
by one gives a summable upper bound, including for the inverse sixth power.

## Main results

* `integral_nearestNeighborSymbol_pow_odd`: every odd symbol moment vanishes.
* `hasSum_integral_nearestNeighborSymbol_inv_pow`: the exact integrated binomial series.
* `integral_nearestNeighborSymbol_inv_six_le`: the capped pairing series upper bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Real Finset

namespace PercLib.Analysis

private theorem integral_pi_sum_cos_pow_odd (d m : ℕ) :
    (∫ k : Fin d → ℝ, (∑ j, cos (k j)) ^ (2 * m + 1)
      ∂Measure.pi (fun _ => volume.restrict (Ioo (-π) π))) = 0 := by
  induction d generalizing m with
  | zero => simp
  | succ d ih =>
    rw [integral_pi_sum_cos_pow_succ]
    apply sum_eq_zero
    intro r hr
    have hrm : r ≤ 2 * m + 1 := Nat.le_of_lt_succ (mem_range.mp hr)
    rcases Nat.even_or_odd' r with ⟨j, rfl | rfl⟩
    · rw [show 2 * m + 1 - 2 * j = 2 * (m - j) + 1 by omega, ih, mul_zero]
    · rw [integral_Ioo_cos_pow_odd, mul_zero, zero_mul]

/-- Every odd moment of the coordinate cosine sum on the torus vanishes. -/
theorem integral_sum_cos_pow_odd (d m : ℕ) :
    (∫ k in ball (0 : Fin d → ℝ) π, (∑ j, cos (k j)) ^ (2 * m + 1)) = 0 := by
  rw [volume_restrict_pi_ball_eq_pi_Ioo]
  exact integral_pi_sum_cos_pow_odd d m

/-- Every odd nearest-neighbour symbol moment vanishes, also in dimension zero. -/
theorem integral_nearestNeighborSymbol_pow_odd (d m : ℕ) :
    (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m + 1)) = 0 := by
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sum_cos_pow_odd, mul_zero]

/-- A bounded real function admits the integrated binomial series under any finite
measure. The geometric-polynomial majorant justifies the interchange with integration. -/
theorem hasSum_integral_binomial_of_abs_le_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ x ∂μ, |f x| ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℕ) :
    HasSum (fun n => ((n + s).choose s : ℝ) * r ^ n * (∫ x, f x ^ n ∂μ))
      (∫ x, 1 / (1 - r * f x) ^ (s + 1) ∂μ) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hbound : ∀ n, ∀ᵐ x ∂μ,
      ‖((n + s).choose s : ℝ) * (r * f x) ^ n‖ ≤
        ((n + s).choose s : ℝ) * r ^ n := by
    intro n
    filter_upwards [hb] with x hx
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hr0]
    rw [abs_of_nonneg (Nat.cast_nonneg ((n + s).choose s))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (mul_nonneg hr0 (abs_nonneg _))
      (mul_le_of_le_one_right hr0 hx) n
  have hlim : ∀ᵐ x ∂μ,
      HasSum (fun n => ((n + s).choose s : ℝ) * (r * f x) ^ n)
        (1 / (1 - r * f x) ^ (s + 1)) := by
    filter_upwards [hb] with x hx
    apply hasSum_choose_mul_geometric_of_norm_lt_one s
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hr0]
    exact (mul_le_of_le_one_right hr0 hx).trans_lt hr1
  have h : HasSum (fun n => ∫ x, ((n + s).choose s : ℝ) * (r * f x) ^ n ∂μ)
      (∫ x, 1 / (1 - r * f x) ^ (s + 1) ∂μ) :=
    hasSum_integral_of_dominated_convergence
    (μ := μ) (fun n _ => ((n + s).choose s : ℝ) * r ^ n)
    (fun n => ((hf.const_mul r).pow n).const_mul _) hbound
    (Filter.Eventually.of_forall fun _ =>
      summable_choose_mul_geometric_of_norm_lt_one s hr)
    (integrable_const _) hlim
  apply h.congr_fun
  intro n
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- The exact subcritical resolvent integral is the sum of its even Fourier moments.
The exponent is arbitrary: `s = 5` gives the inverse sixth power. -/
theorem hasSum_integral_nearestNeighborSymbol_inv_pow {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℕ) :
    HasSum (fun m => ((2 * m + s).choose s : ℝ) * r ^ (2 * m) *
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m))))
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        1 / (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1))) := by
  have hfull : HasSum (fun n => ((n + s).choose s : ℝ) * r ^ n *
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ n)))
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        1 / (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1))) := by
    rw [volume_restrict_pi_ball_eq_pi_Ioo]
    have h := hasSum_integral_binomial_of_abs_le_one
      (Measure.pi fun _ : Fin d => volume.restrict (Ioo (-π) π))
      (f := fun k => (d : ℝ)⁻¹ * ∑ j, cos (k j))
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall (abs_nearestNeighborSymbol_le_one hd)) hr0 hr1 s
    convert h.mul_left (((2 * π) ^ d)⁻¹) using 1
    ext n
    ring
  let F : ℕ → ℝ := fun n => ((n + s).choose s : ℝ) * r ^ n *
    (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ n))
  change HasSum F _ at hfull
  change HasSum (fun m => F (2 * m)) _
  have heven : Summable (fun m => F (2 * m)) := hfull.summable.comp_injective
    (show Function.Injective (fun m : ℕ => 2 * m) by intro m n h; dsimp at h; omega)
  have hodd : HasSum (fun m => F (2 * m + 1)) 0 := by
    simp only [F, integral_nearestNeighborSymbol_pow_odd, mul_zero]
    exact hasSum_zero
  have heq := (HasSum.even_add_odd (f := F) heven.hasSum hodd).unique hfull
  rw [add_zero] at heq
  exact heq ▸ heven.hasSum

/-- The normalized even nearest-neighbour moment is at most one. -/
theorem integral_nearestNeighborSymbol_pow_even_le_one {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)) ≤ 1 := by
  rw [volume_restrict_pi_ball_eq_pi_Ioo]
  have hle (k : Fin d → ℝ) :
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m) ≤ 1 := by
    calc
      _ ≤ |((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)| := le_abs_self _
      _ = |(d : ℝ)⁻¹ * ∑ j, cos (k j)| ^ (2 * m) := abs_pow _ _
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_nearestNeighborSymbol_le_one hd k)
  have hint : Integrable (fun k : Fin d → ℝ =>
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m))
      (Measure.pi fun _ => volume.restrict (Ioo (-π) π)) := by
    apply Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
    exact Filter.Eventually.of_forall fun k => by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg _) (abs_nearestNeighborSymbol_le_one hd k)
  have hvol : (∫ _k : Fin d → ℝ, (1 : ℝ)
      ∂Measure.pi (fun _ => volume.restrict (Ioo (-π) π))) = (2 * π) ^ d := by
    simpa using integral_pi_sum_cos_pow_zero d
  have h := integral_mono hint (integrable_const 1) hle
  rw [hvol] at h
  calc
    _ ≤ ((2 * π) ^ d)⁻¹ * (2 * π) ^ d := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- The capped pairing majorant for a subcritical inverse-sixth series is summable. -/
theorem summable_nearestNeighbor_pairing_inv_six (d : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m => ((2 * m + 5).choose 5 : ℝ) * r ^ (2 * m) *
      min 1 (((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * (4 * (d : ℝ)) ^ m))) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs := (summable_choose_mul_geometric_of_norm_lt_one 5 hr).comp_injective
    (show Function.Injective (fun m : ℕ => 2 * m) by intro m n h; dsimp at h; omega)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro m
    positivity
  · intro m
    exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)

/-- Replacing each even moment by the smaller of one and its factorial pairing
bound gives a convergent upper bound for the actual inverse-sixth integral. -/
theorem integral_nearestNeighborSymbol_inv_six_le {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      1 / (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ 6) ≤
      ∑' m, ((2 * m + 5).choose 5 : ℝ) * r ^ (2 * m) *
        min 1 (((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * (4 * (d : ℝ)) ^ m)) := by
  have hexp := hasSum_integral_nearestNeighborSymbol_inv_pow hd hr0 hr1 5
  rw [← hexp.tsum_eq]
  apply Summable.tsum_le_tsum _ hexp.summable
    (summable_nearestNeighbor_pairing_inv_six d hr0 hr1)
  intro m
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_min (integral_nearestNeighborSymbol_pow_even_le_one hd m)
    (integral_nearestNeighborSymbol_pow_even_le hd m)

end PercLib.Analysis
