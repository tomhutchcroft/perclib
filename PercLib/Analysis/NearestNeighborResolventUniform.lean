/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.NearestNeighborResolventTailConstants

/-!
# A uniform inverse-sixth nearest-neighbour walk estimate

## Main results

The actual undamped even-moment series is summable and at most `1 + 53 / (5 * d)`
in every dimension at least 1000. Consequently the normalized inverse-sixth
resolvent integral has the same bound uniformly over subcritical walk parameters.
-/

@[expose] public section
noncomputable section

open MeasureTheory Real Metric Finset

namespace PercLib.Analysis

private theorem higher_prefix_terms_le {d : ℕ} (hd : 1000 ≤ d) :
    189 / (2 * (d : ℝ) ^ 2) + (5 / 2 : ℝ) * (3465 / (4 * (d : ℝ) ^ 3)) ≤
      39 / (400 * (d : ℝ)) := by
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hpoly : 756 * (d : ℝ) + 17325 ≤ (39 / 50 : ℝ) * (d : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr hdR)]
  calc
    _ = (756 * (d : ℝ) + 17325) / (8 * (d : ℝ) ^ 3) := by field_simp; ring
    _ ≤ ((39 / 50 : ℝ) * (d : ℝ) ^ 2) / (8 * (d : ℝ) ^ 3) :=
      div_le_div_of_nonneg_right hpoly (by positivity)
    _ = _ := by field_simp; ring

/-- The undamped inverse-sixth moment series is genuinely summable and has
an explicit bound for every dimension at least 1000. -/
theorem summable_and_tsum_nearestNeighbor_moment_inv_six_le {d : ℕ} (hd : 1000 ≤ d) :
    let F := fun m : ℕ => ((2 * m + 5).choose 5 : ℝ) *
      (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
        ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)))
    Summable F ∧ (∑' m, F m) ≤ 1 + 53 / (5 * (d : ℝ)) := by
  let F := fun m : ℕ => ((2 * m + 5).choose 5 : ℝ) *
    (((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)))
  change Summable F ∧ (∑' m, F m) ≤ _
  have htail := summable_and_tsum_nearestNeighbor_moment_inv_six_tail_le
    (show 12 < d by omega) (show 65 ≤ d / 2 by omega)
  have hshift : Summable (fun n => F (n + (d / 2 + 1))) := by
    simpa only [F, Nat.add_assoc] using htail.1
  have hs : Summable F := (summable_nat_add_iff (d / 2 + 1)).mp hshift
  refine ⟨hs, ?_⟩
  have ht : (∑' n, F (n + (d / 2 + 1))) ≤ 1 / (400 * (d : ℝ)) := by
    simpa only [F, Nat.add_assoc] using
      htail.2.trans (nearestNeighbor_resolvent_gaussian_tail_half_le_small hd)
  rw [← hs.sum_add_tsum_nat_add (d / 2 + 1)]
  have hp := sum_nearestNeighbor_moment_inv_six_prefix_le hd
  change (∑ m ∈ range (d / 2 + 1), F m) ≤ _ at hp
  calc
    _ ≤ (1 + 21 / (2 * (d : ℝ)) + 189 / (2 * (d : ℝ) ^ 2) +
        (5 / 2 : ℝ) * (3465 / (4 * (d : ℝ) ^ 3))) + 1 / (400 * (d : ℝ)) :=
      add_le_add hp ht
    _ ≤ 1 + 21 / (2 * (d : ℝ)) + 39 / (400 * (d : ℝ)) + 1 / (400 * (d : ℝ)) := by
      linarith [higher_prefix_terms_le hd]
    _ = _ := by ring

/-- The actual inverse-sixth resolvent integral is bounded uniformly over
all subcritical walk parameters, with explicit constant and dimension threshold. -/
theorem integral_nearestNeighborSymbol_inv_six_le_one_add_refined {d : ℕ} (hd : 1000 ≤ d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      1 / (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ 6) ≤ 1 + 53 / (5 * (d : ℝ)) := by
  have hexp := hasSum_integral_nearestNeighborSymbol_inv_pow
    (show 0 < d by omega) hr0 hr1 5
  have hfull := summable_and_tsum_nearestNeighbor_moment_inv_six_le hd
  rw [← hexp.tsum_eq]
  apply le_trans _ hfull.2
  apply hexp.summable.tsum_le_tsum _ hfull.1
  intro m
  have hm : 0 ≤ ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      ((d : ℝ)⁻¹ * ∑ j, cos (k j)) ^ (2 * m)) := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro k
    dsimp only
    rw [pow_mul]
    positivity
  have hrpow : r ^ (2 * m) ≤ 1 := pow_le_one₀ hr0 hr1.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by positivity) hrpow) hm

/-- The rounded constant-eleven form of the refined uniform estimate. -/
theorem integral_nearestNeighborSymbol_inv_six_le_one_add {d : ℕ} (hd : 1000 ≤ d)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      1 / (1 - r * ((d : ℝ)⁻¹ * ∑ j, cos (k j))) ^ 6) ≤ 1 + 11 / (d : ℝ) := by
  apply (integral_nearestNeighborSymbol_inv_six_le_one_add_refined hd hr0 hr1).trans
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h : (53 / 5 : ℝ) / d ≤ 11 / d :=
    div_le_div_of_nonneg_right (by norm_num) hd0.le
  rw [div_div] at h
  linarith

end PercLib.Analysis
