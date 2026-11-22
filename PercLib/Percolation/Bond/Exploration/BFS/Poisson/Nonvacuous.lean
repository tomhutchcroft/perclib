/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Poisson/Nonvacuous.lean`; added at source revision
`a1dd3fd7178264bb1dfc2c71abc2cdca25da9d48`, supplied under its Apache-2.0 header.
This is a proof-only module with canonical prefix `PercLib.Percolation.Bond.Exploration.BFS`.
Existing monotone-union/cardinality
APIs are used rather than duplicated. Source task labels and audit commands were omitted.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.Poisson.Assemble
public import PercLib.Probability.Exploration.Envelope

/-!
# Nonvacuity of row bounds and positive PGF budgets

The zero intensity profile satisfies explicit nonnegative row bounds,
positive exponential PGF budgets do not vanish, and the endpoint factor at unit intensity is
computed. These are mathematical nonvacuity checks for the interface, not substitutes for a
critical LRP parameter instantiation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond Finset
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- The identically-zero intensity field satisfies every nonnegative row-sum budget; in
particular `UniformRowBound` is satisfiable with `0 < M < 1`. -/
theorem uniformRowBound_zero {M : ℝ} (hM : 0 ≤ M) :
    UniformRowBound (fun _ : Sym2 V => (0 : unitInterval)) M := by
  intro x t _
  have hterm : ∀ y : V, (((fun _ : Sym2 V => (0 : unitInterval)) (s(x, y))) : ℝ) = 0 :=
    fun y => rfl
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  simpa using hM

/-- The row-sum hypothesis is satisfiable strictly inside the high-temperature range
`0 < M < 1`: the zero intensity field with budget `M = 1/2`. -/
example : UniformRowBound (fun _ : Sym2 V => (0 : unitInterval)) (1 / 2) :=
  uniformRowBound_zero (by norm_num)

/-- The budget `exp ((t-1) M)` in the one-step estimate is strictly positive, so the state
weight `(exp ((t-1) M)) ^ |T|` never vanishes. -/
theorem ofReal_exp_budget_pos (t : ℝ≥0∞) (M : ℝ) (n : ℕ) :
    0 < (ENNReal.ofReal (Real.exp ((t.toReal - 1) * M))) ^ n := by
  rw [← ofReal_exp_card_mul]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

/-- The `p = 1` endpoint: the one-coordinate factor is exactly `t`, so the finite product over
`S` of the factor at `p ≡ 1` is `t ^ |S|` and the exponential bound is attained only through
`∑_{e ∈ S} p_e = |S|`. -/
theorem prod_pgfFactor_one (t : ℝ≥0∞) (S : Finset (Sym2 V)) :
    ∏ _e ∈ S, (t * (unitInterval.toNNReal (1 : unitInterval) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (1 : unitInterval) : ℝ≥0∞))) = t ^ S.card := by
  have h1 : (unitInterval.toNNReal (1 : unitInterval) : ℝ≥0∞) = 1 := by
    rw [ExplorationPoisson.coe_toNNReal_ennreal]
    simp
  rw [Finset.prod_congr rfl (fun e _ => by rw [h1, mul_one, tsub_self, add_zero]),
    Finset.prod_const]

end PercLib.Percolation.Bond.Exploration.BFS
