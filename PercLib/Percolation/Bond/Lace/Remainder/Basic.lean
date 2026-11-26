/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New definitions for this project; no upstream Lean code is copied.
The remainder convention follows Heydenreich and van der Hofstad,
Progress in High-Dimensional Percolation and Random Graphs (2017), Section 6.2.
-/
module

public import PercLib.Percolation.Bond.Lace.Coefficients.Basic

/-!
# The nonnegative lace remainder

The remainder of order `n` has `n+1` directed pairs and `n+2` independent
configurations. Its last test is connection through the preceding deleted
cluster; all earlier tests are `E'`. Replacing the last through-set test by
`E'` gives the coefficient of order `n+1`.

These quantities are extended nonnegative reals. No convergence, finiteness,
or signed expansion identity is asserted by the definitions.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Independent-layer event for the nonnegative remainder of order `n`. -/
def remainderEvent {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V) :
    Set (Fin (n + 2) → Config V) :=
  {ω | ω 0 ∈ doubleConn x (b 0).1 ∧ ∀ i : Fin (n + 1),
    ω i.succ ∈ (if i.val = n then throughSet else laceEPrime)
      (cluster (ω i.castSucc \ {s((b i).1, (b i).2)})
        (Fin.cases x (fun j => (b j).2) i.castSucc))
      (b i).2 (Fin.lastCases y (fun j => (b j).1) i.succ)}

/-- The magnitude of the order-`n` signed remainder. The sign, when the finite
real expansion is established, is `(-1)^(n+1)`. -/
def laceRemainder (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) : ℝ≥0∞ :=
  ∑' b : Fin (n + 1) → V × V,
    (∏ i, offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
      (b i).1 (b i).2) *
    (Measure.pi (fun _ : Fin (n + 2) => law q)) (remainderEvent x y b)

end PercLib.Percolation.Bond.Lace
