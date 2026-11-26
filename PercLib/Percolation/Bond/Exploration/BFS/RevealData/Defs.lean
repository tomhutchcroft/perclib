/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/RevealData.lean`; added at source revision
`b4ea9ce13d15b85d2ffa5c7544656693d8e7f59a`,
supplied under its Apache-2.0 header. Canonical definitions and their stated API are moved into
this interface module; declarations are unchanged except for the coordinated namespace prefix.
The forbidden `set_option autoImplicit false` was removed, since the build enforces it.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.History
public import PercLib.Percolation.Bond.Exploration.BFS.Measurable
public import PercLib.Probability.Exploration.AdaptedReveal.Defs

/-!
# The BFS stopping-set instance

Restriction extension with all outside coordinates closed and the BFS revelation structure
on its full state. The cylindrical fibre property is proved from agreement on the revealed
history, not postulated. The state sets are not assumed finite, and the state type is not claimed
to be countable; the separate finite-state refinement supplies the product-law partition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- The canonical extension of a restriction `η` on a block `R` to a full
configuration, with every edge outside `R` closed. -/
def extendBlock (R : Set (Sym2 V)) (η : Set R) : Set (Sym2 V) :=
  {e | ∃ h : e ∈ R, (⟨e, h⟩ : R) ∈ η}

theorem measurable_extendBlock (R : Set (Sym2 V)) : Measurable (extendBlock R) := by
  rw [measurable_set_iff]
  intro e
  apply measurableSet_setOfPred.mp
  by_cases he : e ∈ R
  · have h : {η : Set R | e ∈ extendBlock R η} = {η : Set R | (⟨e, he⟩ : R) ∈ η} := by
      ext η
      simp [extendBlock, he]
    rw [h]
    exact measurableSet_mem _
  · have h : {η : Set R | e ∈ extendBlock R η} = ∅ := by
      ext η
      simp [extendBlock, he]
    rw [h]
    exact MeasurableSet.empty

/-- `extendBlock` is the image under the subtype inclusion. -/
theorem extendBlock_eq_image (R : Set (Sym2 V)) (η : Set R) :
    extendBlock R η = Subtype.val '' η :=
  Subtype.coe_image.symm

theorem blockRestrict_extendBlock (R : Set (Sym2 V)) (η : Set R) :
    blockRestrict R (extendBlock R η) = η := by
  ext ⟨e, he⟩
  simp [blockRestrict, extendBlock]

theorem extendBlock_blockRestrict (R : Set (Sym2 V)) (ω : Set (Sym2 V)) :
    extendBlock R (blockRestrict R ω) = ω ∩ R := by
  ext e
  constructor
  · rintro ⟨he, h⟩
    exact ⟨by simpa [blockRestrict] using h, he⟩
  · rintro ⟨heω, heR⟩
    exact ⟨heR, by simpa [blockRestrict] using heω⟩

/-- The outline's revealed set as a function of the state alone. -/
def revealOfState (σ : State V) : Set (Sym2 V) := {e | ∃ v ∈ σ.P, v ∈ e}

theorem revealed_eq_revealOfState (ω : Config V) (o : V) (k : ℕ) :
    revealed ω o k = revealOfState (state ω o k) := rfl

variable [Countable V]

/-- **The BFS exploration as adapted-revelation data.**  The state is the full
exploration state after `k` steps, the revealed coordinates are the edges incident
to the processed set `P k`, and the cylinder of a state `σ` is the set of
restrictions whose extension with all outside edges closed has state `σ`. -/
noncomputable def bfsRevealData (o : V) (k : ℕ) : RevealData (Sym2 V) (State V) where
  reveal := revealOfState
  state := fun ω => state ω o k
  cyl := fun σ =>
    {η : Set (revealOfState σ) | state (extendBlock (revealOfState σ) η) o k = σ}
  cyl_measurable := fun σ =>
    (measurableSet_state_eq o k σ).preimage (measurable_extendBlock _)
  fiber := fun σ => by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hω
      -- `state ω = σ`.  `ω ∩ R` agrees with `ω` on `R = revealed ω`, hence has the
      -- same state, and `extendBlock R (blockRestrict R ω) = ω ∩ R`.
      have hR : revealed ω o k = revealOfState σ := by
        rw [revealed_eq_revealOfState, hω]
      rw [extendBlock_blockRestrict]
      have h : ∀ e ∈ revealed ω o k, (e ∈ ω ↔ e ∈ ω ∩ revealOfState σ) := by
        intro e he
        exact ⟨fun h => ⟨h, hR ▸ he⟩, fun h => h.1⟩
      rw [← state_eq_of_eqOn_revealed ω (ω ∩ revealOfState σ) o k h, hω]
    · intro hη
      -- `state (ω ∩ R) = σ`, and `ω` agrees with `ω ∩ R` on `revealed (ω ∩ R) = R`.
      rw [extendBlock_blockRestrict] at hη
      have hR : revealed (ω ∩ revealOfState σ) o k = revealOfState σ := by
        rw [revealed_eq_revealOfState, hη]
      have h : ∀ e ∈ revealed (ω ∩ revealOfState σ) o k,
          (e ∈ ω ∩ revealOfState σ ↔ e ∈ ω) := by
        intro e he
        exact ⟨fun h => h.1, fun h => ⟨h, hR ▸ he⟩⟩
      exact (state_eq_of_eqOn_revealed (ω ∩ revealOfState σ) ω o k h).symm.trans hη

end PercLib.Percolation.Bond.Exploration.BFS
