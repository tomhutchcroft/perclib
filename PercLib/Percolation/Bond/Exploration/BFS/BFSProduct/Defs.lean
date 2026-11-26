/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/BFSProduct.lean`; added at source revision
`b4ea9ce13d15b85d2ffa5c7544656693d8e7f59a`,
supplied under its Apache-2.0 header. Canonical definitions and their stated API are moved into
this interface module; declarations are unchanged except for the coordinated namespace prefix.
The forbidden `set_option autoImplicit false` was removed, since the build enforces it.
The countability premise carried by source theorem statements is bound explicitly.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.RevealData.Defs
public import PercLib.Probability.Exploration.AdaptedReveal.PGF

/-!
# The countable finite-state refinement of BFS revelation

`FinState` records the processed set and frontier when both are finite, with `none` as the
fallback. The measurable and fibre properties are proved fields of `RevealData`; they make the
adapted Bernoulli product law usable on a countable state partition. The fallback reveals the
whole coordinate space, so a fresh set at `none` is necessarily empty by the disjointness premise.
No finite-frontier hypothesis is silently added.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- Compressed BFS state: `some (processed set, frontier)` when both are finite, `none` as the
fallback. It is countable when `V` is. -/
abbrev FinState (V : Type*) := Option (Finset V × Finset V)

/-- The BFS state compressed to the countable type `FinState`: `some (P k, A k)` (as finsets)
when the processed set and the frontier are both finite, and `none` otherwise. -/
noncomputable def finState (ω : Config V) (o : V) (k : ℕ) : FinState V := by
  classical
  exact if h : (P ω o k).Finite ∧ (A ω o k).Finite then
    some (h.1.toFinset, h.2.toFinset)
  else none

/-- Characterization of the finite states. -/
theorem finState_eq_some_iff [Countable V] {ω : Config V} {o : V} {k : ℕ} {Q T : Finset V} :
    finState ω o k = some (Q, T) ↔
      (Q : Set V) = P ω o k ∧ (T : Set V) = A ω o k := by
  classical
  unfold finState
  by_cases h : (P ω o k).Finite ∧ (A ω o k).Finite
  · rw [dite_eq_left h]
    constructor
    · intro heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hQ, hT⟩ := heq
      exact ⟨by rw [← Set.Finite.coe_toFinset h.1, hQ],
        by rw [← Set.Finite.coe_toFinset h.2, hT]⟩
    · rintro ⟨hQ, hT⟩
      have hQ' : h.1.toFinset = Q := by
        ext v
        rw [Set.Finite.mem_toFinset, ← Finset.mem_coe, hQ]
      have hT' : h.2.toFinset = T := by
        ext v
        rw [Set.Finite.mem_toFinset, ← Finset.mem_coe, hT]
      rw [hQ', hT']
  · rw [dite_eq_right h]
    constructor
    · intro hcon
      exact absurd hcon (by simp)
    · rintro ⟨hQ, hT⟩
      exact absurd ⟨hQ ▸ Q.finite_toSet, hT ▸ T.finite_toSet⟩ h

variable [Countable V]

theorem measurableSet_finState_eq_some (o : V) (k : ℕ) (Q T : Finset V) :
    MeasurableSet {ω : Config V | finState ω o k = some (Q, T)} := by
  have h : {ω : Config V | finState ω o k = some (Q, T)} =
      {ω : Config V | P ω o k = (Q : Set V)} ∩
        {ω : Config V | A ω o k = (T : Set V)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact ⟨fun hω => ⟨(finState_eq_some_iff.mp hω).1.symm,
        (finState_eq_some_iff.mp hω).2.symm⟩,
      fun hω => finState_eq_some_iff.mpr ⟨hω.1.symm, hω.2.symm⟩⟩
  rw [h]
  exact (measurableSet_P_eq o k (Q : Set V)).inter (measurableSet_A_eq o k (T : Set V))

theorem measurableSet_finState_eq (o : V) (k : ℕ) (σ : FinState V) :
    MeasurableSet {ω : Config V | finState ω o k = σ} := by
  cases σ with
  | none =>
      have h : {ω : Config V | finState ω o k = none} =
          (⋃ QT : Finset V × Finset V,
            {ω : Config V | finState ω o k = some QT})ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion]
        constructor
        · intro hω ⟨QT, hQT⟩
          rw [hω] at hQT
          cases hQT
        · intro hω
          cases h' : finState ω o k with
          | none => rfl
          | some QT => exact absurd ⟨QT, h'⟩ hω
      rw [h]
      exact (MeasurableSet.iUnion fun QT => by
        obtain ⟨Q, T⟩ := QT
        exact measurableSet_finState_eq_some o k Q T).compl
  | some QT =>
      obtain ⟨Q, T⟩ := QT
      exact measurableSet_finState_eq_some o k Q T

/-- The revealed edge set as a function of the countable state: for a finite
state `(Q,T)` it is the outline's `R k` (edges incident to `Q`), and for `none`
it is the whole space (the fibre of `none` is described trivially). -/
def revealFin : FinState V → Set (Sym2 V)
  | some (Q, _) => {e | ∃ v ∈ (Q : Set V), v ∈ e}
  | none => univ

/-- The BFS exploration as adapted-revelation data on the countable state
`FinState V`. -/
noncomputable def finRevealData (o : V) (k : ℕ) : RevealData (Sym2 V) (FinState V) where
  reveal := revealFin
  state := fun ω => finState ω o k
  cyl := fun σ =>
    {η : Set (revealFin σ) | finState (extendBlock (revealFin σ) η) o k = σ}
  cyl_measurable := fun σ =>
    (measurableSet_finState_eq o k σ).preimage (measurable_extendBlock _)
  fiber := fun σ => by
    ext ω
    simp only [Set.mem_ofPred_eq]
    cases σ with
    | none =>
        simp only [revealFin]
        rw [extendBlock_blockRestrict, Set.inter_univ]
    | some QT =>
        obtain ⟨Q, T⟩ := QT
        constructor
        · intro hω
          obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp hω
          have hrev : revealed ω o k = revealFin (some (Q, T)) := by
            ext e
            simp only [revealed, revealFin, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
          have hstate : P (ω ∩ revealFin (some (Q, T))) o k = P ω o k := by
            have h : ∀ e ∈ revealed ω o k, (e ∈ ω ↔ e ∈ ω ∩ revealFin (some (Q, T))) := by
              intro e he
              rw [hrev] at he
              exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
            exact (congrArg State.P
              (state_eq_of_eqOn_revealed ω (ω ∩ revealFin (some (Q, T))) o k h)).symm
          have hstateA : A (ω ∩ revealFin (some (Q, T))) o k = A ω o k := by
            have h : ∀ e ∈ revealed ω o k, (e ∈ ω ↔ e ∈ ω ∩ revealFin (some (Q, T))) := by
              intro e he
              rw [hrev] at he
              exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
            exact (congrArg State.A
              (state_eq_of_eqOn_revealed ω (ω ∩ revealFin (some (Q, T))) o k h)).symm
          rw [extendBlock_blockRestrict]
          exact finState_eq_some_iff.mpr ⟨hQ.trans hstate.symm, hT.trans hstateA.symm⟩
        · intro hη
          rw [extendBlock_blockRestrict] at hη
          obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp hη
          have hrev : revealed (ω ∩ revealFin (some (Q, T))) o k =
              revealFin (some (Q, T)) := by
            ext e
            simp only [revealed, revealFin, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
            · rintro ⟨v, hv, hve⟩
              exact ⟨v, hQ ▸ hv, hve⟩
          have h : ∀ e ∈ revealed (ω ∩ revealFin (some (Q, T))) o k,
              (e ∈ ω ∩ revealFin (some (Q, T)) ↔ e ∈ ω) := by
            intro e he
            exact ⟨fun h => h.1, fun h => ⟨h, hrev ▸ he⟩⟩
          have hstate := state_eq_of_eqOn_revealed (ω ∩ revealFin (some (Q, T))) ω o k h
          exact finState_eq_some_iff.mpr
            ⟨hQ.trans (congrArg State.P hstate), hT.trans (congrArg State.A hstate)⟩


end PercLib.Percolation.Bond.Exploration.BFS
