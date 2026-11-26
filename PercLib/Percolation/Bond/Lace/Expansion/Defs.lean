/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New definitions for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Expansion.Basic

/-!
# The infinite signed lace kernel

## Main results

Defines the alternating series of the canonical nonnegative lace coefficients.
-/

@[expose] public section
noncomputable section

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The signed infinite lace kernel. Results using this definition establish
absolute summability separately; the definition itself assumes no convergence. -/
def laceSum (q : Sym2 V → unitInterval) (x y : V) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * (laceCoefficient q n x y).toReal

end PercLib.Percolation.Bond.Lace
