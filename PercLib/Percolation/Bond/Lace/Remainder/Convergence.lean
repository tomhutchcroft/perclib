/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Remainder.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Vanishing of the canonical remainders

Summability of the positive coefficient masses and a uniform bound on `Jτ`
imply uniform vanishing of the actual nonnegative lace remainders. The bound
retains any available constant for `Jτ`, rather than replacing it by the larger
total bond intensity. Coefficient summability is an explicit analytic hypothesis;
it is not built into the coefficient definitions.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped ENNReal Topology

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} [Countable V]

/-- A bound by the coefficient mass with the exact supplied continuation
constant. In particular, one can use the supremum of `Jτ` itself. -/
theorem laceRemainder_succ_le_mass_mul (q : Sym2 V → unitInterval)
    (n : ℕ) (x y : V) (C : ℝ≥0∞)
    (hC : ∀ u, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C) :
    laceRemainder q (n + 1) x y ≤ (∑' u, laceCoefficient q (n + 1) x u) * C := by
  refine (laceRemainder_succ_le_tsum_laceCoefficient_mul_tau q n x y).trans ?_
  calc
    _ = ∑' u, laceCoefficient q (n + 1) x u *
        (∑' v, offDiagonal (fun a b : V =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v * tau q v y) := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ ∑' u, laceCoefficient q (n + 1) x u * C :=
      ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hC u) _
    _ = _ := ENNReal.tsum_mul_right

/-- Uniform convergence of all nonnegative remainder magnitudes to zero,
assuming summable positive coefficient masses and a finite continuation bound. -/
@[tag "6UGP"]
theorem tendsto_iSup_laceRemainder_zero (q : Sym2 V → unitInterval) (x : V)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ u y, (∑' v,
      offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) u v *
        tau q v y) ≤ C)
    (hsum : (∑' n : ℕ, ∑' u, laceCoefficient q (n + 1) x u) ≠ ⊤) :
    Tendsto (fun n => ⨆ y, laceRemainder q n x y) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hm := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hmul : Tendsto (fun n => (∑' u, laceCoefficient q (n + 1) x u) * C)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hm (Or.inr hCfinite)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ => bot_le) (fun n => iSup_le fun y =>
      laceRemainder_succ_le_mass_mul q n x y C (fun u => hC u y))

end PercLib.Percolation.Bond.Lace
