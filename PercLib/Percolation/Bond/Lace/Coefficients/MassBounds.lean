/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Remainder.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A geometric coefficient-mass criterion

## Main results

The exact continuation mass `sup_u ∑ v,y J(u,v) τ(v,y)` controls the growth of
the positive coefficient masses. A value below one gives a direct convergence
criterion. This criterion is useful at small intensity; it is not the stronger
triangle-diagram criterion needed near criticality.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} [Countable V]

theorem laceCoefficient_mass_succ_le (q : Sym2 V → unitInterval)
    (n : ℕ) (x : V) (ρ : ℝ≥0∞)
    (hρ : ∀ u, (∑' v, ∑' y,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ ρ) :
    (∑' y, laceCoefficient q (n + 2) x y) ≤
      (∑' u, laceCoefficient q (n + 1) x u) * ρ := by
  let J := offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞))
  calc
    _ ≤ ∑' y, laceRemainder q (n + 1) x y :=
      ENNReal.tsum_le_tsum fun y => laceCoefficient_succ_le_remainder q (n + 1) x y
    _ ≤ ∑' y, ∑' u, ∑' v, laceCoefficient q (n + 1) x u * J u v * tau q v y :=
      ENNReal.tsum_le_tsum fun y => laceRemainder_succ_le_tsum_laceCoefficient_mul_tau q n x y
    _ = ∑' u, ∑' y, ∑' v, laceCoefficient q (n + 1) x u * J u v * tau q v y :=
      ENNReal.tsum_comm
    _ = ∑' u, laceCoefficient q (n + 1) x u * (∑' v, ∑' y, J u v * tau q v y) := by
      apply tsum_congr
      intro u
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' u, laceCoefficient q (n + 1) x u * ρ :=
      ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hρ u) _
    _ = _ := ENNReal.tsum_mul_right

/-- Every positive coefficient mass has a geometric bound, with prefactor
equal to the first positive mass and no additional combinatorial constant. -/
theorem laceCoefficient_mass_le_geometric (q : Sym2 V → unitInterval)
    (x : V) (ρ : ℝ≥0∞)
    (hρ : ∀ u, (∑' v, ∑' y,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ ρ) (n : ℕ) :
    (∑' y, laceCoefficient q (n + 1) x y) ≤
      (∑' y, laceCoefficient q 1 x y) * ρ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ (∑' y, laceCoefficient q (n + 1) x y) * ρ :=
        laceCoefficient_mass_succ_le q n x ρ hρ
      _ ≤ ((∑' y, laceCoefficient q 1 x y) * ρ ^ n) * ρ := mul_le_mul' ih le_rfl
      _ = _ := by rw [pow_succ, mul_assoc]

/-- Summation over all positive orders retains the geometric denominator. -/
theorem tsum_laceCoefficient_mass_le (q : Sym2 V → unitInterval)
    (x : V) (ρ : ℝ≥0∞)
    (hρ : ∀ u, (∑' v, ∑' y,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ ρ) :
    (∑' n : ℕ, ∑' y, laceCoefficient q (n + 1) x y) ≤
      (∑' y, laceCoefficient q 1 x y) * (1 - ρ)⁻¹ := by
  calc
    _ ≤ ∑' n : ℕ, (∑' y, laceCoefficient q 1 x y) * ρ ^ n :=
      ENNReal.tsum_le_tsum (laceCoefficient_mass_le_geometric q x ρ hρ)
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

theorem tsum_laceCoefficient_mass_ne_top (q : Sym2 V → unitInterval)
    (x : V) (ρ : ℝ≥0∞) (hρone : ρ < 1)
    (hρ : ∀ u, (∑' v, ∑' y,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ ρ)
    (hfirst : (∑' y, laceCoefficient q 1 x y) ≠ ⊤) :
    (∑' n : ℕ, ∑' y, laceCoefficient q (n + 1) x y) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hfirst (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hρone))))
    (tsum_laceCoefficient_mass_le q x ρ hρ)

end PercLib.Percolation.Bond.Lace
