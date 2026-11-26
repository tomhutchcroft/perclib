/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the open-degree and incident-coordinate counts.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Degree.Defs

/-!
# Open degree and incident-coordinate counts: correspondence

Wiki correspondence for the definitions of the open degree `D_v` and of the count `N_F(v)` of
open pair coordinates from `v` into a finite set `F`, with the adjacency events.

## Main results

* `openDegree_incidentCount_and_adjacency`
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- The open degree is `D_v = #{w ≠ v : s(v, w) open} ∈ ℕ ∪ {∞}`. For finite `F`, `N_F(v)`
counts the open coordinates `s(v, w)` with `w ∈ F`: it counts the diagonal coordinate when
`v ∈ F`, the degree inside `F` is `N_{F ∖ {v}}(v)`, and distinct `w` give distinct
coordinates. For `w ≠ v`, adjacency is the event that `s(v, w)` is open, a measurable cylinder
of probability `q_{vw}`; self-adjacency is impossible, even when the diagonal coordinate has
probability one. -/
@[tag "PMHN"]
theorem openDegree_incidentCount_and_adjacency :
    (∀ (ω : Config V) (v : V), openDegree ω v = {w | w ≠ v ∧ s(v, w) ∈ ω}.encard) ∧
    (∀ (ω : Config V) (F : Finset V) (v : V),
      incidentCount ω F v = (F.filter fun w => s(v, w) ∈ ω).card ∧
      incidentCount ω F v =
        incidentCount ω (F.erase v) v + (if v ∈ F ∧ s(v, v) ∈ ω then 1 else 0) ∧
      incidentCount ω (F.erase v) v = (F.filter fun w => (openGraph ω).Adj v w).card ∧
      incidentCount ω F v = ((F.image fun w => s(v, w)).filter (· ∈ ω)).card) ∧
    (∀ v : V, Function.Injective fun w => s(v, w)) ∧
    (∀ (ω : Config V) (v w : V), w ≠ v → ((openGraph ω).Adj v w ↔ s(v, w) ∈ ω)) ∧
    (∀ v w : V, MeasurableSet {ω : Config V | (openGraph ω).Adj v w}) ∧
    (∀ (q : Sym2 V → unitInterval) (v w : V), w ≠ v →
      law q {ω | (openGraph ω).Adj v w} = unitInterval.toENNReal (q s(v, w))) ∧
    (∀ (ω : Config V) (v : V), ¬ (openGraph ω).Adj v v) ∧
    (∀ (q : Sym2 V → unitInterval) (v : V), law q {ω | (openGraph ω).Adj v v} = 0) :=
  ⟨openDegree_eq_encard_open, fun ω F v => ⟨incidentCount_def ω F v,
    incidentCount_eq_erase_add ω F v, incidentCount_erase_eq_card_adj ω F v,
    incidentCount_eq_card_image ω F v⟩, fun _ _ _ h => Sym2.congr_right.1 h,
    fun ω _ _ hw => openGraph_adj_iff_of_ne ω hw, measurableSet_adj,
    fun q _ _ hw => law_adj_of_ne q hw, fun ω _ => (openGraph ω).irrefl, law_adj_self⟩

end PercLib.Percolation.Bond
