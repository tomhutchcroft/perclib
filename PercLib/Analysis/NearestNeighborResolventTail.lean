/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.NearestNeighborResolventPrefix
public import PercLib.Analysis.PowerLawSeriesTail

/-!
# Explicit Gaussian tails for nearest-neighbour resolvent moments

## Main results

The actual even Fourier moments have a Gaussian power-law majorant. Summing
the inverse-sixth binomial weights past a cutoff gives an explicit finite
tail in every dimension greater than twelve, uniformly without a damping
parameter in the series.
-/

@[expose] public section
noncomputable section

open MeasureTheory Real Metric

namespace PercLib.Analysis

/-- Gaussian decay of the actual normalized even symbol moment. -/
theorem integral_nearestNeighborSymbol_pow_even_le_gaussian {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)) ≤
      ((π * d / 8) / (m : ℝ)) ^ ((d : ℝ) / 2) := by
  have h := normalized_integral_abs_nearestNeighborSymbol_pow_le hd
    (show 0 < 2 * m by omega)
  calc
    _ ≤ (√(π * d / (4 * (2 * m) : ℝ))) ^ d := by
      simpa only [pow_mul, sq_abs, Nat.cast_mul, Nat.cast_ofNat] using h
    _ = _ := by
      rw [sqrt_eq_rpow, ← rpow_mul_natCast (by positivity)]
      congr 1 <;> ring

/-- The undamped inverse-sixth moment tail has an explicit Gaussian bound.
This is a bound for actual torus integrals, not assumed return estimates. -/
theorem summable_and_tsum_nearestNeighbor_moment_inv_six_tail_le {d N : ℕ}
    (hd : 12 < d) (hN : 65 ≤ N) :
    let M := fun m : ℕ => ((2 * π) ^ d)⁻¹ *
      (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m))
    Summable (fun n : ℕ => ((2 * (n + N + 1) + 5).choose 5 : ℝ) * M (n + N + 1)) ∧
    (∑' n : ℕ, ((2 * (n + N + 1) + 5).choose 5 : ℝ) * M (n + N + 1)) ≤
      ((π * d / 8) ^ ((d : ℝ) / 2) *
        (N : ℝ) ^ (6 - (d : ℝ) / 2) / ((d : ℝ) / 2 - 6)) / 3 := by
  dsimp only
  have hdR : (12 : ℝ) < d := by exact_mod_cast hd
  have hp : (5 : ℝ) + 1 < (d : ℝ) / 2 := by linarith
  have hs := (summable_pow_mul_div_rpow N 5
    (show (0 : ℝ) ≤ π * d / 8 by positivity) hp).div_const 3
  have hpoint (n : ℕ) :
      ((2 * (n + N + 1) + 5).choose 5 : ℝ) *
        (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
          ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * (n + N + 1)))) ≤
      ((((n + N + 1 : ℕ) : ℝ) ^ 5) *
        ((π * d / 8) / ((n + N + 1 : ℕ) : ℝ)) ^ ((d : ℝ) / 2)) / 3 := by
    have hmoment := integral_nearestNeighborSymbol_pow_even_le_gaussian
      (show 0 < d by omega) (show 0 < n + N + 1 by omega)
    have hc := choose_two_mul_add_five_le_pow_five (show 65 ≤ n + N + 1 by omega)
    calc
      _ ≤ (((n + N + 1 : ℕ) : ℝ) ^ 5 / 3) *
          ((π * d / 8) / ((n + N + 1 : ℕ) : ℝ)) ^ ((d : ℝ) / 2) := by
        apply mul_le_mul hc hmoment
        · apply mul_nonneg (by positivity)
          apply integral_nonneg
          intro k
          dsimp only
          rw [pow_mul]
          positivity
        · positivity
      _ = _ := by ring
  have hnonneg (n : ℕ) : 0 ≤
      ((2 * (n + N + 1) + 5).choose 5 : ℝ) *
        (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
          ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * (n + N + 1)))) := by
    apply mul_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro k
    dsimp only
    rw [pow_mul]
    positivity
  have hsum := (Summable.of_nonneg_of_le hnonneg hpoint hs).tsum_le_tsum hpoint hs
  refine ⟨Summable.of_nonneg_of_le hnonneg hpoint hs, ?_⟩
  apply hsum.trans
  rw [tsum_div_const]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  convert tsum_pow_mul_div_rpow_le (show 0 < N by omega)
    (show (0 : ℝ) ≤ π * d / 8 by positivity) hp using 1
  norm_num
  ring

/-- The explicit tail estimate, separated from the summability conclusion. -/
theorem tsum_nearestNeighbor_moment_inv_six_tail_le {d N : ℕ}
    (hd : 12 < d) (hN : 65 ≤ N) :
    let M := fun m : ℕ => ((2 * π) ^ d)⁻¹ *
      (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m))
    (∑' n : ℕ, ((2 * (n + N + 1) + 5).choose 5 : ℝ) * M (n + N + 1)) ≤
      ((π * d / 8) ^ ((d : ℝ) / 2) *
        (N : ℝ) ^ (6 - (d : ℝ) / 2) / ((d : ℝ) / 2 - 6)) / 3 :=
  (summable_and_tsum_nearestNeighbor_moment_inv_six_tail_le hd hN).2

end PercLib.Analysis
