/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New definitions for this project; no upstream Lean code is copied.
The diagonal convention follows Heydenreich and van der Hofstad, Progress in
High-Dimensional Percolation and Random Graphs (2017), Section 6.2,
Definition 6.3 and equation (6.2.7).
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.DisjointOccurrence
public import PercLib.Meta.Tag

/-!
# Double connections and the zeroth lace coefficient

The events use the existing bond configuration and finite-certificate disjoint
occurrence. Certificates consist of edges, so the two connecting paths may share
vertices. The event includes `x = y`, witnessed by two empty certificates.

The zeroth coefficient removes this diagonal contribution. It is nonnegative;
the alternating sum of all lace coefficients will require a signed codomain.
No higher coefficient or expansion identity is postulated here.
-/

@[expose] public section
noncomputable section

open Set PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Double connection: two disjoint finite edge certificates for a connection.
This event is certain when the two endpoints coincide. -/
@[tag "ZUND"]
def doubleConn (x y : V) : Set (Config V) :=
  disjointOccurrence (conn x y) (conn x y)

/-- The zeroth lace coefficient, with the diagonal contribution removed.
Equivalently, this is the double-connection probability minus `δ(x,y)`. -/
@[tag "U8OS"]
def piZero (q : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ :=
  if x = y then 0 else law q (doubleConn x y)

end PercLib.Percolation.Bond.Lace
