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

/-- Connection through a vertex set: there is a connection, but none entirely
inside the complement of the set. On the diagonal this holds exactly when the
vertex belongs to `A`. The restricted connection uses the existing induced graph
on the same bond configuration. -/
@[tag "UINB"]
def throughSet (A : Set V) (x y : V) : Set (Config V) :=
  conn x y \ {ω | ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
    ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

/-- A pivotal pair directed from the `x` side to the `y` side. The pivotal
condition is the existing insertion/deletion convention; the two connections
in the deleted configuration fix the direction. The pair need not be open. -/
def orientedPivotal (x y u v : V) : Set (Config V) :=
  {ω | insert s(u, v) ω ∈ conn x y ∧ ω \ {s(u, v)} ∉ conn x y ∧
    ω \ {s(u, v)} ∈ conn x u ∧ ω \ {s(u, v)} ∈ conn v y}

/-- The event `E'(x,y;A)` in the lace expansion: connection through `A` with
no directed pivotal pair whose initial endpoint is already connected to `x`
through `A`. The orientation is tested with that pair deleted. -/
def laceEPrime (A : Set V) (x y : V) : Set (Config V) :=
  throughSet A x y \ ⋃ u, ⋃ v, orientedPivotal x y u v ∩ throughSet A x u

/-- The cutting event for the occupied directed pair `(u,v)`: no earlier
cutting pair on the connection from `x` to `u`, followed by this pivotal pair
for `x ↔ y`. Occupation is an explicit condition. -/
def cuttingEvent (A : Set V) (x y u v : V) : Set (Config V) :=
  (laceEPrime A x u ∩ orientedPivotal x y u v) ∩ {ω | s(u, v) ∈ ω}

end PercLib.Percolation.Bond.Lace
