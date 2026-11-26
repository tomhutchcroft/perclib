/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Auxiliary finite-layer definitions on the canonical coefficient interface.
No source code is copied and no diagram estimate is assumed.
-/
module

public import PercLib.Percolation.Bond.Lace.Coefficients.Basic

/-!
# Marked prefixes for the coefficient diagram bound

The prefix with no earlier bond is the full initial double connection.
Positive-length prefixes reuse `coefficientEvent` exactly. Marking the last
deleted cluster is an auxiliary probability, not a new lace coefficient.
The specified outgoing pair is not among the earlier weighted bonds.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- A prefix using `n` earlier bonds and ending at `u`, before testing the
next deleted cluster. At positive length this is the existing coefficient event. -/
def coefficientPrefixEvent (x u : V) : (n : ℕ) →
    (Fin n → V × V) → Set (Fin (n + 1) → Config V)
  | 0, _ => {ω | ω 0 ∈ doubleConn x u}
  | _ + 1, b => coefficientEvent x u b

/-- The exact weighted probability of a prefix ending at `c.1`, with `a` in
the last root cluster after deleting the outgoing pair `{c.1,c.2}`. Only the
`n` earlier pairs are weighted; the outgoing pair is weighted by the next connector. -/
def markedCoefficient (q : Sym2 V → unitInterval) (n : ℕ) (x : V)
    (c : V × V) (a : V) : ℝ≥0∞ :=
  ∑' b : Fin n → V × V,
    (∏ i, offDiagonal (fun u v : V => (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞))
      (b i).1 (b i).2) *
    (Measure.pi (fun _ : Fin (n + 1) => law q))
      (coefficientPrefixEvent x c.1 n b ∩
        {ω | ω (Fin.last n) \ {s(c.1, c.2)} ∈
          conn (Fin.cases x (fun j => (b j).2) (Fin.last n)) a})

end PercLib.Percolation.Bond.Lace
