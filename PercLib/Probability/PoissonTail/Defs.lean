/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The Poisson tail function. New for this project against pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied. Mathematical reference:
the Poisson distribution, e.g. W. Feller, *An Introduction to Probability Theory and Its
Applications*, Vol. 1, Chapter VI.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The Poisson tail function

`poissonTail j x = 1 - e^{-x} ∑_{i < j} x^i / i!` is the probability that a Poisson variable of
mean `x` is at least `j`.

## Main definitions

* `PercLib.poissonTail j x`: the Poisson tail `P(Poi(x) ≥ j)`.
-/

@[expose] public section

open Finset Real

namespace PercLib

/-- The Poisson tail `Q_j(x) = 1 - e^{-x} ∑_{i < j} x^i / i!`, the probability that a Poisson
variable of mean `x` is at least `j`. -/
noncomputable def poissonTail (j : ℕ) (x : ℝ) : ℝ :=
  1 - exp (-x) * ∑ i ∈ range j, x ^ i / i.factorial

theorem poissonTail_def (j : ℕ) (x : ℝ) :
    poissonTail j x = 1 - exp (-x) * ∑ i ∈ range j, x ^ i / i.factorial := rfl

@[simp]
theorem poissonTail_zero_left (x : ℝ) : poissonTail 0 x = 1 := by
  simp [poissonTail]

theorem poissonTail_one (x : ℝ) : poissonTail 1 x = 1 - exp (-x) := by
  simp [poissonTail]

theorem poissonTail_succ (j : ℕ) (x : ℝ) :
    poissonTail (j + 1) x = poissonTail j x - exp (-x) * x ^ j / j.factorial := by
  simp only [poissonTail, sum_range_succ, mul_add]
  ring

/-- `Q_j(0) = 0` for `j ≥ 1`. -/
theorem poissonTail_zero_right {j : ℕ} (hj : 1 ≤ j) : poissonTail j 0 = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [poissonTail, sum_range_succ']
  simp

/-- `Q_j(x) < 1` for `j ≥ 1`: the term `i = 0` alone contributes `e^{-x} > 0`. -/
theorem poissonTail_lt_one {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 0 ≤ x) : poissonTail j x < 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [poissonTail, sub_lt_self_iff, sum_range_succ']
  refine mul_pos (exp_pos _) (add_pos_of_nonneg_of_pos (sum_nonneg fun i _ ↦ ?_) (by simp))
  positivity

end PercLib
