/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.CorrelationLength

/-! Correspondence wrappers for the connection distance and directional decay rates.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PercLib.Percolation.Bond

/-- The connection distance `D_q = -log τ_q` (with `-log 0 = ∞`) is nonnegative,
symmetric, vanishes on the diagonal and satisfies the triangle inequality. -/
@[tag "8TZJ"]
theorem neg_log_tau_distance {V : Type*} [Countable V] (q : Sym2 V → unitInterval) :
    (∀ x y : V, 0 ≤ -ENNReal.log (tau q x y)) ∧
    (∀ x y : V, -ENNReal.log (tau q x y) = -ENNReal.log (tau q y x)) ∧
    (∀ x : V, -ENNReal.log (tau q x x) = 0) ∧
    (∀ x y z : V,
      -ENNReal.log (tau q x z) ≤ -ENNReal.log (tau q x y) + -ENNReal.log (tau q y z)) :=
  ⟨fun x y => EReal.neg_nonneg.2 (ENNReal.log_le_zero_iff.2 (tau_le_one q x y)),
    neg_log_tau_comm q, neg_log_tau_self q, neg_log_tau_le_add q⟩

/-- On a countable Abelian group with translation-invariant two-point function and
`τ(0, n v) > 0` for `n ≥ 1`, the directional decay rate exists as a limit equal to the
infimum, lies in `[0, -log τ(0, v)]`, and bounds `τ(0, n v) ≤ e^{-n m(v)}`. -/
@[tag "K2LV"]
theorem directional_decay_rate {G : Type*} [AddCommGroup G] [Countable G]
    (q : Sym2 G → unitInterval) (v : G)
    (hinv : ∀ x y g : G, tau q (x + g) (y + g) = tau q x y)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < tau q 0 (n • v)) :
    Tendsto (fun n : ℕ => -Real.log (tau q 0 (n • v)).toReal / n) atTop
      (𝓝 (⨅ n : ℕ+, -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n)) ∧
    0 ≤ (⨅ n : ℕ+, -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n) ∧
    (⨅ n : ℕ+, -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n) ≤ -Real.log (tau q 0 v).toReal ∧
    ∀ n : ℕ, (tau q 0 (n • v)).toReal ≤
      Real.exp (-(n : ℝ) * ⨅ m : ℕ+, -Real.log (tau q 0 ((m : ℕ) • v)).toReal / m) := by
  have hpos' : ∀ n : ℕ, 0 < tau q 0 (n • v) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [zero_smul, tau_self]
      exact one_pos
    · exact hpos n hn
  have hbdd : BddBelow (range fun n : ℕ+ => -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n) :=
    ⟨0, by
      rintro _ ⟨n, rfl⟩
      exact div_nonneg (neg_log_tau_nonneg q _ _) (Nat.cast_nonneg _)⟩
  refine ⟨tendsto_neg_log_tau_div q v hinv hpos', ?_, ?_, tau_le_exp_neg_mul q v hpos'⟩
  · exact le_ciInf fun n => div_nonneg (neg_log_tau_nonneg q _ _) (Nat.cast_nonneg _)
  · have h := ciInf_le hbdd 1
    simpa using h

end PercLib.Percolation.Bond
