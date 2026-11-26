/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Basic smoke test

A single elementary inequality that exercises mathlib and `nlinarith`.

## Main results

* `two_mul_le_add_sq`
-/

@[expose] public section

namespace PercLib

/-- A small initial theorem exercising mathlib and nonlinear arithmetic. -/
theorem two_mul_le_add_sq (a b : ℝ) :
    2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

end PercLib
