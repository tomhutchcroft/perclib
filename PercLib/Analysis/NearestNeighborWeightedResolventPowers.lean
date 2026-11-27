/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.NearestNeighborWeightedResolvent

/-!
# Lower powers of the weighted nearest-neighbour resolvent

The comparison uses the nonnegative even Fourier-moment series, rather than a
pointwise comparison of resolvents at a possibly negative Fourier symbol.
Retaining the exact second moment improves the lower-power constants.

## Main results

* `integral_nearestNeighborSymbol_sq_mul_inv_pow_le`: the common bound through power three.
* `integral_nearestNeighborSymbol_sq_mul_inv_le`: power one is at most `631/(1260d)`.
* `integral_nearestNeighborSymbol_sq_mul_inv_sq_le`: power two is at most `211/(420d)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Real

namespace PercLib.Analysis

private theorem integral_sq_mul_inv_pow_le_of_choose {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℕ) (c : ℝ)
    (hc : ∀ m : ℕ, 0 < m → ((2 * m + s).choose s : ℝ) ≤
      c * ((2 * m + 2).choose 2 : ℝ)) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
        (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1)) ≤
      1 / (2 * (d : ℝ)) + c *
        (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
          ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
            (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ 3) - 1 / (2 * (d : ℝ))) := by
  let M : ℕ → ℝ := fun m => ((2 * π) ^ d)⁻¹ *
    (∫ k in ball (0 : Fin d → ℝ) π, ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * (m + 1)))
  let F : ℕ → ℕ → ℝ := fun t m => ((2 * m + t).choose t : ℝ) * r ^ (2 * m) * M m
  have hF (t : ℕ) := hasSum_integral_nearestNeighborSymbol_sq_mul_inv_pow hd hr0 hr1 t
  have hsum (t : ℕ) : Summable (F t) := (hF t).summable
  have hzero (t : ℕ) : F t 0 = 1 / (2 * (d : ℝ)) := by
    simp only [F, M, Nat.mul_zero, zero_add, Nat.choose_self, Nat.cast_one, pow_zero,
      one_mul, Nat.reduceMul]
    exact integral_nearestNeighborSymbol_sq hd
  have hM (m : ℕ) : 0 ≤ M m := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro k
    dsimp only
    rw [pow_mul]
    positivity
  have htail : (∑' m, F s (m + 1)) ≤ c * ∑' m, F 2 (m + 1) := by
    rw [← tsum_mul_left]
    apply ((summable_nat_add_iff 1).mpr (hsum s)).tsum_le_tsum _
      (((summable_nat_add_iff 1).mpr (hsum 2)).mul_left c)
    intro m
    calc
      F s (m + 1) ≤ (c * ((2 * (m + 1) + 2).choose 2 : ℝ)) *
          r ^ (2 * (m + 1)) * M (m + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hc (m + 1) (by omega)) (pow_nonneg hr0 _))
          (hM (m + 1))
      _ = c * F 2 (m + 1) := by dsimp only [F]; ring
  have hs := (hsum s).tsum_eq_zero_add
  have htwo := (hsum 2).tsum_eq_zero_add
  rw [hzero] at hs htwo
  rw [← (hF s).tsum_eq, ← (hF 2).tsum_eq]
  change (∑' m, F s m) ≤ 1 / (2 * (d : ℝ)) + c *
    ((∑' m, F 2 m) - 1 / (2 * (d : ℝ)))
  rw [hs, htwo]
  linarith

/-- The first three positive powers have the same weighted cubic upper bound. -/
theorem integral_nearestNeighborSymbol_sq_mul_inv_pow_le {d : ℕ} (hd : 1000 ≤ d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {s : ℕ} (hs : s ≤ 2) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
        (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ (s + 1)) ≤
      53 / (105 * (d : ℝ)) := by
  have h := integral_sq_mul_inv_pow_le_of_choose (show 0 < d by omega) hr0 hr1 s 1
    (fun m _ => by
      rw [one_mul]
      exact_mod_cast (show (2 * m + s).choose s ≤ (2 * m + 2).choose 2 from by
        rw [← Nat.choose_symm (show s ≤ 2 * m + s by omega),
          ← Nat.choose_symm (show 2 ≤ 2 * m + 2 by omega)]
        simp only [Nat.add_sub_cancel]
        exact Nat.choose_le_choose _ (Nat.add_le_add_left hs _)))
  have hc := integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd hr0 hr1
  linarith

/-- Keeping the exact second moment improves the weighted inverse-one constant. -/
theorem integral_nearestNeighborSymbol_sq_mul_inv_le {d : ℕ} (hd : 1000 ≤ d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
        (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j)))) ≤ 631 / (1260 * (d : ℝ)) := by
  have h := integral_sq_mul_inv_pow_le_of_choose (show 0 < d by omega) hr0 hr1 0 (1 / 6)
    (fun m hm => by
      have hc : (6 : ℝ) ≤ ((2 * m + 2).choose 2 : ℝ) := by
        exact_mod_cast (show 6 ≤ (2 * m + 2).choose 2 from by
          simpa [Nat.choose] using Nat.choose_le_choose 2 (show 4 ≤ 2 * m + 2 by omega))
      simp only [Nat.choose_zero_right, Nat.cast_one]
      linarith)
  simp only [Nat.zero_add, pow_one] at h
  have hc := integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd hr0 hr1
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have halg : 1 / (2 * (d : ℝ)) + (1 / 6 : ℝ) *
      (53 / (105 * d) - 1 / (2 * d)) = 631 / (1260 * d) := by field_simp; ring
  rw [← halg]
  linarith

/-- Keeping the exact second moment improves the weighted inverse-square constant. -/
theorem integral_nearestNeighborSymbol_sq_mul_inv_sq_le {d : ℕ} (hd : 1000 ≤ d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ 2 /
        (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ 2) ≤
      211 / (420 * (d : ℝ)) := by
  have h := integral_sq_mul_inv_pow_le_of_choose (show 0 < d by omega) hr0 hr1 1 (1 / 2)
    (fun m hm => by
      have htwo : (2 * m + 1 : ℝ) * (2 * m + 2) =
          2 * ((2 * m + 2).choose 2 : ℝ) := by
        have hchoose := Nat.descFactorial_eq_factorial_mul_choose (2 * m + 2) 2
        change (2 * m + 1) * ((2 * m + 2) * 1) = 2 * (2 * m + 2).choose 2 at hchoose
        simp only [mul_one] at hchoose
        exact_mod_cast hchoose
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      nlinarith [sq_nonneg ((m : ℝ) - 1)])
  have hc := integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd hr0 hr1
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have halg : 1 / (2 * (d : ℝ)) + (1 / 2 : ℝ) *
      (53 / (105 * d) - 1 / (2 * d)) = 211 / (420 * d) := by field_simp; ring
  rw [← halg]
  linarith

end PercLib.Analysis
