/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.ClosedCertificates

/-!
# Pair boundaries and separating pair sets

The pair boundary `pairBoundary C` of a vertex set `C` is the set of pairs `s(a, b)` with
`a ∈ C` and `b ∉ C`; it is closed in a configuration `ω` when it is disjoint from `ω`. A set
`P` of pairs separates `x` from `y` (`SeparatesPairs P x y`) when every walk from `x` to `y`
in the complete simple graph uses a pair of `P`. Boundaries and walks contain no loops, and
no pair set separates a vertex from itself.

## Main definitions

* `pairBoundary`, `SeparatesPairs`

## Main results

* `mk_mem_pairBoundary_iff`, `pairBoundary_compl`, `not_isDiag_of_mem_pairBoundary`
* `disjoint_pairBoundary_iff`: closedness of the boundary, pair by pair.
* `not_separatesPairs_self`, `SeparatesPairs.mono`, `separatesPairs_pairBoundary`
-/

@[expose] public section

open Set

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The pair boundary `δC = {s(a, b) : a ∈ C, b ∉ C}` of a vertex set `C`. -/
def pairBoundary (C : Set V) : Set (Sym2 V) := {e | ∃ a ∈ C, ∃ b ∉ C, e = s(a, b)}

theorem mem_pairBoundary {C : Set V} {e : Sym2 V} :
    e ∈ pairBoundary C ↔ ∃ a ∈ C, ∃ b ∉ C, e = s(a, b) :=
  Iff.rfl

@[simp]
theorem mk_mem_pairBoundary_iff {C : Set V} {a b : V} :
    s(a, b) ∈ pairBoundary C ↔ (a ∈ C ∧ b ∉ C) ∨ (b ∈ C ∧ a ∉ C) := by
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact ⟨a, ha, b, hb, rfl⟩
    · exact ⟨b, hb, a, ha, Sym2.eq_swap⟩

@[simp]
theorem pairBoundary_empty : pairBoundary (∅ : Set V) = ∅ := by
  ext e; simp [mem_pairBoundary]

@[simp]
theorem pairBoundary_univ : pairBoundary (univ : Set V) = ∅ := by
  ext e; simp [mem_pairBoundary]

/-- A set and its complement have the same pair boundary. -/
@[simp]
theorem pairBoundary_compl (C : Set V) : pairBoundary Cᶜ = pairBoundary C := by
  ext e
  induction e using Sym2.ind with
  | _ a b => simp only [mk_mem_pairBoundary_iff, mem_compl_iff, not_not]; tauto

/-- The pair boundary contains no loop. -/
theorem not_isDiag_of_mem_pairBoundary {C : Set V} {e : Sym2 V} (he : e ∈ pairBoundary C) :
    ¬ e.IsDiag := by
  obtain ⟨a, ha, b, hb, rfl⟩ := he
  rw [Sym2.mk_isDiag_iff]
  rintro rfl
  exact hb ha

/-- The boundary is closed in `ω` exactly when no pair leaving `C` is open. -/
theorem disjoint_pairBoundary_iff {C : Set V} {ω : Config V} :
    Disjoint (pairBoundary C) ω ↔ ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω := by
  rw [Set.disjoint_left]
  constructor
  · intro h a ha b hb
    exact h ⟨a, ha, b, hb, rfl⟩
  · rintro h e ⟨a, ha, b, hb, rfl⟩
    exact h a ha b hb

/-- `P` separates `x` from `y`: every walk from `x` to `y` in the complete simple graph uses
a pair of `P`. -/
def SeparatesPairs (P : Set (Sym2 V)) (x y : V) : Prop :=
  ∀ w : (⊤ : SimpleGraph V).Walk x y, ∃ e ∈ w.edges, e ∈ P

theorem separatesPairs_iff {P : Set (Sym2 V)} {x y : V} :
    SeparatesPairs P x y ↔ ∀ w : (⊤ : SimpleGraph V).Walk x y, ∃ e ∈ w.edges, e ∈ P :=
  Iff.rfl

/-- The length-zero walk: no pair set separates a vertex from itself. -/
theorem not_separatesPairs_self (P : Set (Sym2 V)) (x : V) : ¬ SeparatesPairs P x x := by
  intro h
  obtain ⟨e, he, -⟩ := h SimpleGraph.Walk.nil
  simp at he

/-- Walks in the complete simple graph use no loop. -/
theorem not_isDiag_of_mem_edges {x y : V} (w : (⊤ : SimpleGraph V).Walk x y) {e : Sym2 V}
    (he : e ∈ w.edges) : ¬ e.IsDiag :=
  SimpleGraph.not_isDiag_of_mem_edgeSet _ (w.edges_subset_edgeSet he)

theorem SeparatesPairs.mono {P Q : Set (Sym2 V)} {x y : V} (h : SeparatesPairs P x y)
    (hPQ : P ⊆ Q) : SeparatesPairs Q x y := fun w =>
  let ⟨e, he, heP⟩ := h w
  ⟨e, he, hPQ heP⟩

theorem SeparatesPairs.symm {P : Set (Sym2 V)} {x y : V} (h : SeparatesPairs P x y) :
    SeparatesPairs P y x := fun w =>
  let ⟨e, he, heP⟩ := h w.reverse
  ⟨e, by simpa using he, heP⟩

/-- The pair boundary of a set containing `x` but not `y` separates `x` from `y`. -/
theorem separatesPairs_pairBoundary {C : Set V} {x y : V} (hx : x ∈ C) (hy : y ∉ C) :
    SeparatesPairs (pairBoundary C) x y := fun w =>
  let ⟨a, ha, b, hb, he⟩ := exists_mem_edges_boundary w hx hy
  ⟨s(a, b), he, a, ha, b, hb, rfl⟩

end PercLib.Percolation.Bond
