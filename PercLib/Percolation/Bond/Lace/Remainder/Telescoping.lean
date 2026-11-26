/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Finite alternating telescoping

This algebraic identity converts the adjacent nonnegative remainder recurrence
to a signed finite expansion. It assumes no probabilistic expansion identity.
-/

@[expose] public section

namespace PercLib.Percolation.Bond.Lace

/-- Alternating adjacent terms cancel, retaining both boundary terms with
their exact signs. This identity is purely finite and needs no summability. -/
theorem alternating_sum_adjacent (r : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * (r i + r (i + 1))) =
      r 0 + (-1 : ℝ) ^ n * r (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

end PercLib.Percolation.Bond.Lace
