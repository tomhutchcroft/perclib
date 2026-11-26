/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for closed boundaries and separating pair sets.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClosedSeparators.Defs

/-!
# Closed boundaries and separating pair sets: correspondence

Wiki correspondence for the pair boundary `δC`, its closedness in a configuration, and pair
sets separating two vertices.

## Main results

* `pairBoundary_and_separatesPairs`
-/

@[expose] public section

namespace PercLib.Percolation.Bond

/-- The pair boundary is `δC = {s(a, b) : a ∈ C, b ∉ C}`; it is closed in `ω` when
`δC ∩ ω = ∅`, that is when no pair leaving `C` is open. `P` separates `x` from `y` when every
finite walk from `x` to `y` in the complete simple graph uses a pair in `P`. Boundaries and
walks contain no loops, and the length-zero walk prevents any pair set from separating a
vertex from itself. -/
@[tag "GA03"]
theorem pairBoundary_and_separatesPairs {V : Type*} :
    (∀ (C : Set V) (e : Sym2 V), e ∈ pairBoundary C ↔ ∃ a ∈ C, ∃ b ∉ C, e = s(a, b)) ∧
    (∀ (C : Set V) (ω : Config V),
      Disjoint (pairBoundary C) ω ↔ ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω) ∧
    (∀ (P : Set (Sym2 V)) (x y : V),
      SeparatesPairs P x y ↔ ∀ w : (⊤ : SimpleGraph V).Walk x y, ∃ e ∈ w.edges, e ∈ P) ∧
    (∀ (C : Set V) (e : Sym2 V), e ∈ pairBoundary C → ¬ e.IsDiag) ∧
    (∀ (x y : V) (w : (⊤ : SimpleGraph V).Walk x y) (e : Sym2 V), e ∈ w.edges → ¬ e.IsDiag) ∧
    (∀ (P : Set (Sym2 V)) (x : V), ¬ SeparatesPairs P x x) :=
  ⟨fun _ _ => mem_pairBoundary, fun _ _ => disjoint_pairBoundary_iff,
    fun _ _ _ => separatesPairs_iff, fun _ _ => not_isDiag_of_mem_pairBoundary,
    fun _ _ w _ => not_isDiag_of_mem_edges w, not_separatesPairs_self⟩

end PercLib.Percolation.Bond
