/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.LatticeFourier.Defs
public import PercLib.Analysis.NearestNeighborSymbolBounds
public import PercLib.Analysis.CosineDifference

/-!
# Bounds for canonical lattice Fourier quantities

## Main results

The canonical symbol has absolute value at most one. For `0 ≤ lambda < 1`, its
resolvent lies between `1 / (1 + lambda)` and `1 / (1 - lambda)`, and hence above `1/2`.
The cosine transform respects addition and subtraction of summable kernels.
-/

@[expose] public section

namespace PercLib.Analysis

variable {d : ℕ}

/-- The canonical symbol inherits the existing sharp absolute bound. -/
theorem nearestNeighborSymbol_abs_le_one (hd : 0 < d) (k : Fin d → ℝ) :
    |nearestNeighborSymbol k| ≤ 1 := abs_nearestNeighborSymbol_le_one hd k

/-- The coordinate cosine deficit is the dimension times the normalized deficit. -/
theorem sum_one_sub_cos_eq_mul_deficit (hd : 0 < d) (k : Fin d → ℝ) :
    (∑ i, (1 - Real.cos (k i))) = (d : ℝ) * (1 - nearestNeighborSymbol k) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [nearestNeighborSymbol, Finset.sum_sub_distrib, mul_sub, hd0]

/-- The resolvent denominator is strictly positive throughout the subcritical parameter range. -/
theorem nearestNeighborResolvent_den_pos (hd : 0 < d) {lam : ℝ}
    (hlam : lam ∈ Set.Ico (0 : ℝ) 1) (k : Fin d → ℝ) :
    0 < 1 - lam * nearestNeighborSymbol k := by
  have hD := (le_abs_self (nearestNeighborSymbol k)).trans (nearestNeighborSymbol_abs_le_one hd k)
  have h := mul_le_mul_of_nonneg_left hD hlam.1
  nlinarith [hlam.2]

/-- Subcritical nearest-neighbour resolvents are positive. -/
theorem nearestNeighborResolvent_pos (hd : 0 < d) {lam : ℝ}
    (hlam : lam ∈ Set.Ico (0 : ℝ) 1) (k : Fin d → ℝ) :
    0 < nearestNeighborResolvent lam k :=
  inv_pos.mpr (nearestNeighborResolvent_den_pos hd hlam k)

/-- The lower resolvent bound retains its parameter dependence. -/
theorem inv_one_add_le_nearestNeighborResolvent (hd : 0 < d) {lam : ℝ}
    (hlam : lam ∈ Set.Ico (0 : ℝ) 1) (k : Fin d → ℝ) :
    (1 + lam)⁻¹ ≤ nearestNeighborResolvent lam k := by
  have hD := (abs_le.mp (nearestNeighborSymbol_abs_le_one hd k)).1
  have hden : 1 - lam * nearestNeighborSymbol k ≤ 1 + lam := by
    nlinarith [mul_nonneg hlam.1 (show 0 ≤ nearestNeighborSymbol k + 1 by linarith)]
  simpa only [one_div, nearestNeighborResolvent] using
    one_div_le_one_div_of_le (nearestNeighborResolvent_den_pos hd hlam k) hden

/-- Every subcritical resolvent is at least one half. -/
theorem half_le_nearestNeighborResolvent (hd : 0 < d) {lam : ℝ}
    (hlam : lam ∈ Set.Ico (0 : ℝ) 1) (k : Fin d → ℝ) :
    (1 / 2 : ℝ) ≤ nearestNeighborResolvent lam k := by
  have hpos : 0 < 1 + lam := by linarith [hlam.1]
  have h : (1 / 2 : ℝ) ≤ (1 + lam)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hpos (show 1 + lam ≤ (2 : ℝ) by linarith [hlam.2])
  exact h.trans (inv_one_add_le_nearestNeighborResolvent hd hlam k)

/-- The upper resolvent bound is the zero-frequency value. -/
theorem nearestNeighborResolvent_le_inv_one_sub (hd : 0 < d) {lam : ℝ}
    (hlam : lam ∈ Set.Ico (0 : ℝ) 1) (k : Fin d → ℝ) :
    nearestNeighborResolvent lam k ≤ (1 - lam)⁻¹ := by
  have hD := (le_abs_self (nearestNeighborSymbol k)).trans (nearestNeighborSymbol_abs_le_one hd k)
  have hden : 1 - lam ≤ 1 - lam * nearestNeighborSymbol k := by
    nlinarith [mul_le_mul_of_nonneg_left hD hlam.1]
  simpa only [one_div, nearestNeighborResolvent] using
    one_div_le_one_div_of_le (sub_pos.mpr hlam.2) hden

/-- The canonical cosine transform is additive on summable kernels. -/
theorem latticeCosineTransform_add {ι : Type*} [Fintype ι] {f g : (ι → ℤ) → ℝ}
    (hf : Summable f) (hg : Summable g) (k : ι → ℝ) :
    latticeCosineTransform (f + g) k = latticeCosineTransform f k + latticeCosineTransform g k := by
  simp only [latticeCosineTransform, Pi.add_apply, add_mul]
  exact (summable_mul_cos hf _).tsum_add (summable_mul_cos hg _)

/-- The canonical cosine transform respects subtraction of summable kernels. -/
theorem latticeCosineTransform_sub {ι : Type*} [Fintype ι] {f g : (ι → ℤ) → ℝ}
    (hf : Summable f) (hg : Summable g) (k : ι → ℝ) :
    latticeCosineTransform (f - g) k = latticeCosineTransform f k - latticeCosineTransform g k := by
  simp only [latticeCosineTransform, Pi.sub_apply, sub_mul]
  exact (summable_mul_cos hf _).tsum_sub (summable_mul_cos hg _)

end PercLib.Analysis
