/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The homogeneous bond profile on a host graph. New definition; no upstream code is copied.
Mathematical reference: G. Grimmett, *Percolation* (2nd ed., 1999), §1.1.
-/
module

public import PercLib.Percolation.Bond.Basic

/-!
# The homogeneous profile on a host graph

`homogeneousProfile G p` gives every edge of the host graph `G` probability `p` and every
other pair probability `0`. On the complete graph on `Fin n` it is the Erdős–Rényi profile.

## Main definitions

* `homogeneousProfile G p`

## Main results

* `homogeneousProfile_of_mem`, `homogeneousProfile_of_notMem`: evaluation.
* `homogeneousProfile_top_mk`: on the complete graph every off-diagonal pair has probability `p`.
* `homogeneousProfile_mono`, `homogeneousProfile_le_of_le`: monotonicity in `p` and in the host.
-/

@[expose] public section

noncomputable section

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- The homogeneous profile on the host graph `G` with edge probability `p`: host edges get
`p`, all other pairs (including the diagonal) get `0`. -/
def homogeneousProfile (G : SimpleGraph V) (p : unitInterval) : Sym2 V → unitInterval :=
  fun e => if e ∈ G.edgeSet then p else 0

open Classical in
theorem homogeneousProfile_apply (G : SimpleGraph V) (p : unitInterval) (e : Sym2 V) :
    homogeneousProfile G p e = if e ∈ G.edgeSet then p else 0 := rfl

@[simp]
theorem homogeneousProfile_of_mem {G : SimpleGraph V} (p : unitInterval) {e : Sym2 V}
    (h : e ∈ G.edgeSet) : homogeneousProfile G p e = p := by
  simp [homogeneousProfile, h]

@[simp]
theorem homogeneousProfile_of_notMem {G : SimpleGraph V} (p : unitInterval) {e : Sym2 V}
    (h : e ∉ G.edgeSet) : homogeneousProfile G p e = 0 := by
  simp [homogeneousProfile, h]

/-- On the complete graph every off-diagonal pair has probability `p`. -/
@[simp]
theorem homogeneousProfile_top_mk (p : unitInterval) {x y : V} (h : x ≠ y) :
    homogeneousProfile ⊤ p s(x, y) = p :=
  homogeneousProfile_of_mem p (by simpa using h)

@[simp]
theorem homogeneousProfile_bot (p : unitInterval) :
    homogeneousProfile (⊥ : SimpleGraph V) p = fun _ => 0 := by
  funext e
  exact homogeneousProfile_of_notMem p (by simp)

@[simp]
theorem homogeneousProfile_zero (G : SimpleGraph V) :
    homogeneousProfile G 0 = fun _ => 0 := by
  funext e
  by_cases h : e ∈ G.edgeSet <;> simp [h]

/-- The homogeneous profile is pointwise monotone in the edge probability. -/
theorem homogeneousProfile_mono (G : SimpleGraph V) : Monotone (homogeneousProfile G) := by
  intro p p' hp e
  by_cases h : e ∈ G.edgeSet <;> simp [h, hp]

/-- The homogeneous profile is pointwise monotone in the host graph. -/
theorem homogeneousProfile_le_of_le {G G' : SimpleGraph V} (hG : G ≤ G') (p : unitInterval)
    (e : Sym2 V) : homogeneousProfile G p e ≤ homogeneousProfile G' p e := by
  by_cases h : e ∈ G.edgeSet
  · rw [homogeneousProfile_of_mem p h,
      homogeneousProfile_of_mem p (SimpleGraph.edgeSet_mono hG h)]
  · rw [homogeneousProfile_of_notMem p h]
    exact unitInterval.nonneg _

end PercLib.Percolation.Bond
