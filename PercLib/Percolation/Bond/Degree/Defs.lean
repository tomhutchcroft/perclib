/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project. No upstream proof is copied.
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import PercLib.Percolation.Bond.Degree

/-!
# Open degree and incident-coordinate counts

The open degree `openDegree ω v : ℕ∞` of a vertex `v` is the number of vertices `w ≠ v` with
`s(v, w)` open, that is the number of neighbours of `v` in the open graph. For a finite set
`F`, `incidentCount ω F v : ℕ` counts the open pair coordinates `s(v, w)` with `w ∈ F`; it
counts the diagonal coordinate `s(v, v)` when `v ∈ F` and it is open, so the degree inside
`F` is `incidentCount ω (F.erase v) v`.

## Main definitions

* `openDegree`, `incidentCount`

## Main results

* `openDegree_eq_encard_open`: `D_v = #{w ≠ v : s(v, w) ∈ ω}`.
* `measurable_openDegree`: the open degree is measurable on a countable vertex type.
* `incidentCount_erase_eq_card_adj`: the degree inside `F` is `N_{F ∖ {v}}(v)`.
* `incidentCount_eq_erase_add`: `N_F(v)` is the degree inside `F` plus the diagonal term.
* `incidentCount_le_openDegree_add_one`, `incidentCount_erase_le_openDegree`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The open degree of `v`: the number of neighbours of `v` in the open graph, that is of
`w ≠ v` with `s(v, w)` open. It takes the value `⊤` for infinitely many neighbours. -/
def openDegree (ω : Config V) (v : V) : ℕ∞ := {w | (openGraph ω).Adj v w}.encard

theorem openDegree_def (ω : Config V) (v : V) :
    openDegree ω v = {w | (openGraph ω).Adj v w}.encard :=
  rfl

/-- The open degree counts the open pair coordinates `s(v, w)` with `w ≠ v`. -/
theorem openDegree_eq_encard_open (ω : Config V) (v : V) :
    openDegree ω v = {w | w ≠ v ∧ s(v, w) ∈ ω}.encard := by
  rw [openDegree_def]
  congr 1
  ext w
  simp only [mem_ofPred_eq, openGraph_adj_iff, ne_comm (a := v)]
  exact and_comm

/-- The open degree is monotone in the configuration. -/
theorem openDegree_mono {ω ω' : Config V} (h : ω ⊆ ω') (v : V) :
    openDegree ω v ≤ openDegree ω' v :=
  encard_le_encard fun _ hw => openGraph_mono h hw

@[simp]
theorem openDegree_empty (v : V) : openDegree (∅ : Config V) v = 0 := by
  simp [openDegree_eq_encard_open]

/-- **The open degree is measurable** on a countable vertex type. -/
theorem measurable_openDegree [Countable V] (v : V) :
    Measurable fun ω : Config V => openDegree ω v :=
  measurable_degree v

/-- For `w ≠ v`, adjacency in the open graph is the event that `s(v, w)` is open. -/
theorem openGraph_adj_iff_of_ne (ω : Config V) {v w : V} (hw : w ≠ v) :
    (openGraph ω).Adj v w ↔ s(v, w) ∈ ω := by
  rw [openGraph_adj_iff]
  exact ⟨And.left, fun h => ⟨h, hw.symm⟩⟩

/-- For `w ≠ v`, the adjacency event has probability `q s(v, w)`. -/
theorem law_adj_of_ne (q : Sym2 V → unitInterval) {v w : V} (hw : w ≠ v) :
    law q {ω : Config V | (openGraph ω).Adj v w} = unitInterval.toENNReal (q s(v, w)) := by
  rw [law_adj, ite_eq_right hw]
  rfl

/-- Self-adjacency has probability zero, whatever the diagonal coordinate. -/
@[simp]
theorem law_adj_self (q : Sym2 V → unitInterval) (v : V) :
    law q {ω : Config V | (openGraph ω).Adj v v} = 0 := by
  simp

open Classical in
/-- The number of open pair coordinates `s(v, w)` with `w ∈ F`. The diagonal coordinate
`s(v, v)` is counted when `v ∈ F`. -/
def incidentCount (ω : Config V) (F : Finset V) (v : V) : ℕ :=
  (F.filter fun w => s(v, w) ∈ ω).card

open Classical in
theorem incidentCount_def (ω : Config V) (F : Finset V) (v : V) :
    incidentCount ω F v = (F.filter fun w => s(v, w) ∈ ω).card :=
  rfl

/-- Unfolding `incidentCount`, for any decidability instance. -/
theorem incidentCount_eq_card_filter (ω : Config V) (F : Finset V) (v : V)
    [DecidablePred fun w => s(v, w) ∈ ω] :
    incidentCount ω F v = (F.filter fun w => s(v, w) ∈ ω).card := by
  classical
  rw [incidentCount_def]
  congr 1
  exact Finset.filter_congr_decidable _ _ _

open Classical in
/-- The incident-coordinate count is the number of open pairs in the image of `F` under
`w ↦ s(v, w)`, which is injective. -/
theorem incidentCount_eq_card_image [DecidableEq V] (ω : Config V) (F : Finset V) (v : V) :
    incidentCount ω F v = ((F.image fun w => s(v, w)).filter (· ∈ ω)).card := by
  classical
  rw [incidentCount_def, Finset.filter_image,
    Finset.card_image_of_injective _ fun _ _ h => Sym2.congr_right.1 h]

@[simp]
theorem incidentCount_empty_finset (ω : Config V) (v : V) :
    incidentCount ω ∅ v = 0 := by
  simp [incidentCount_def]

theorem incidentCount_le_card (ω : Config V) (F : Finset V) (v : V) :
    incidentCount ω F v ≤ F.card := by
  classical
  rw [incidentCount_def]
  exact Finset.card_filter_le _ _

/-- The incident-coordinate count is monotone in the configuration. -/
theorem incidentCount_mono {ω ω' : Config V} (h : ω ⊆ ω') (F : Finset V) (v : V) :
    incidentCount ω F v ≤ incidentCount ω' F v := by
  classical
  simp only [incidentCount_def]
  refine Finset.card_le_card fun w hw => ?_
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, h hw.2⟩

/-- **The degree inside `F`** is the incident-coordinate count of `F ∖ {v}`. -/
theorem incidentCount_erase_eq_card_adj [DecidableEq V] (ω : Config V) (F : Finset V) (v : V)
    [DecidablePred fun w => (openGraph ω).Adj v w] :
    incidentCount ω (F.erase v) v = (F.filter fun w => (openGraph ω).Adj v w).card := by
  classical
  rw [incidentCount_def]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_erase, openGraph_adj_iff, ne_comm (a := v)]
  tauto

open Classical in
/-- The incident-coordinate count is the degree inside `F` plus the diagonal coordinate,
counted when `v ∈ F` and `s(v, v)` is open. -/
theorem incidentCount_eq_erase_add (ω : Config V) (F : Finset V) (v : V) :
    incidentCount ω F v =
      incidentCount ω (F.erase v) v + if v ∈ F ∧ s(v, v) ∈ ω then 1 else 0 := by
  simp only [incidentCount_def, Finset.filter_erase]
  split_ifs with hv
  · have hm : v ∈ F.filter fun w => s(v, w) ∈ ω := Finset.mem_filter.2 hv
    exact (Finset.card_erase_add_one hm).symm
  · have hm : v ∉ F.filter fun w => s(v, w) ∈ ω := fun h => hv (Finset.mem_filter.1 h)
    rw [Finset.erase_eq_of_notMem hm, add_zero]

/-- The degree inside `F` is at most the open degree. -/
theorem incidentCount_erase_le_openDegree [DecidableEq V] (ω : Config V) (F : Finset V)
    (v : V) : (incidentCount ω (F.erase v) v : ℕ∞) ≤ openDegree ω v := by
  classical
  rw [incidentCount_erase_eq_card_adj, openDegree_def, ← encard_coe_eq_coe_finsetCard]
  exact encard_le_encard fun w hw => (Finset.mem_filter.1 hw).2

/-- The incident-coordinate count exceeds the open degree by at most the diagonal term. -/
theorem incidentCount_le_openDegree_add_one (ω : Config V) (F : Finset V) (v : V) :
    (incidentCount ω F v : ℕ∞) ≤ openDegree ω v + 1 := by
  classical
  calc (incidentCount ω F v : ℕ∞) ≤ (incidentCount ω (F.erase v) v + 1 : ℕ) := by
        refine Nat.cast_le.2 ?_
        rw [incidentCount_eq_erase_add ω F v]
        split_ifs <;> omega
    _ ≤ openDegree ω v + 1 := by
        push_cast
        gcongr
        exact incidentCount_erase_le_openDegree ω F v

end PercLib.Percolation.Bond
