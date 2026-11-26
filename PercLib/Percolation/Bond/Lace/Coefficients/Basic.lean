/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New definitions for this project; no upstream Lean code is copied.
The coefficient convention follows Heydenreich and van der Hofstad,
Progress in High-Dimensional Percolation and Random Graphs (2017), Section 6.2,
equations (6.2.7), (6.2.25) and (6.2.27), generalized to an inhomogeneous bond profile.
-/
module

public import PercLib.Percolation.Bond.Lace.Basic
public import PercLib.Percolation.Bond.WalkSum
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Positive lace coefficients on independent configuration layers

## Main results

For positive order `n+1`, an oriented bond sequence has `n+1` entries and the
event uses `n+2` independent configurations. The cluster at step `i` is computed
in layer `i`, with bond `i` deleted, rooted at the target of the preceding bond
(or at `x` for the first layer). The next layer is tested against `E'` with this
cluster. The last destination is `y`.

The initial event is full double connection, including its certain diagonal.
Only the order-zero coefficient subtracts the diagonal. Bond probabilities use
the existing off-diagonal kernel so the arbitrary probabilities assigned to
loops do not create terms. Coefficients are extended nonnegative reals; no
finiteness or convergence is built into the definition.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The event in the positive coefficient of order `n+1`, for a fixed sequence
of oriented pairs. The configurations are indexed from zero through `n+1`. -/
def coefficientEvent {n : ℕ} (x y : V) (b : Fin (n + 1) → V × V) :
    Set (Fin (n + 2) → Config V) :=
  {ω | ω 0 ∈ doubleConn x (b 0).1 ∧ ∀ i : Fin (n + 1),
    ω i.succ ∈ laceEPrime
      (cluster (ω i.castSucc \ {s((b i).1, (b i).2)})
        (Fin.cases x (fun j => (b j).2) i.castSucc))
      (b i).2 (Fin.lastCases y (fun j => (b j).1) i.succ)}

/-- Nonnegative lace coefficients. Order zero is `piZero`; positive orders
sum the independent-layer event probabilities with their oriented-bond weights.
The product probability measure is mathlib's `Measure.pi`. -/
@[tag "NLIV"]
def laceCoefficient (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) : ℝ≥0∞ :=
  match n with
  | 0 => piZero q x y
  | n + 1 => ∑' b : Fin (n + 1) → V × V,
      (∏ i, offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
        (b i).1 (b i).2) *
      (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b)

end PercLib.Percolation.Bond.Lace
