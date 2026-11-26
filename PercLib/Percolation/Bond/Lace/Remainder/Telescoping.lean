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

/-- A finite algebraic consequence of adjacent identities. In applications
the adjacent identities are proved for the canonical probabilistic remainders. -/
theorem finite_alternating_identity (a r : ℕ → ℝ) (t c : ℝ)
    (hzero : t + r 0 = c + a 0) (N : ℕ)
    (hnext : ∀ n < N, r n + r (n + 1) = a (n + 1)) :
    t = c + (∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * a n) +
      (-1 : ℝ) ^ (N + 1) * r N := by
  induction N with
  | zero =>
    simpa [sub_eq_add_neg] using eq_sub_of_add_eq hzero
  | succ N ih =>
    have hp := ih (fun n hn => hnext n (Nat.lt_trans hn (Nat.lt_succ_self N)))
    have hr : r N = a (N + 1) - r (N + 1) :=
      eq_sub_of_add_eq (hnext N (Nat.lt_succ_self N))
    rw [Finset.sum_range_succ, hp, hr]
    simp only [pow_succ]
    ring

end PercLib.Percolation.Bond.Lace
