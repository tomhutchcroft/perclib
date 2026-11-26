/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New definitions for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Remainder.Basic

/-!
# Finite signed lace quantities

The real-valued finite expansion uses these quantities only after establishing
finiteness of the corresponding nonnegative coefficients and remainder. The
definitions themselves do not assert finiteness or an expansion identity.
-/

@[expose] public section
noncomputable section

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The alternating coefficient sum through order `N`. -/
def partialLaceSum (q : Sym2 V → unitInterval) (N : ℕ) (x y : V) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * (laceCoefficient q n x y).toReal

/-- The signed remainder of the finite order-`N` expansion. -/
def signedLaceRemainder (q : Sym2 V → unitInterval) (N : ℕ) (x y : V) : ℝ :=
  (-1 : ℝ) ^ (N + 1) * (laceRemainder q N x y).toReal

end PercLib.Percolation.Bond.Lace
