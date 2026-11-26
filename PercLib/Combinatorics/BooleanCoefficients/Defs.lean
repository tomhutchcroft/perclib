/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Möbius coefficients of functions on a finite Boolean lattice. New for this project against
pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied.
Mathematical reference: Möbius inversion on the Boolean lattice, e.g. R. P. Stanley,
*Enumerative Combinatorics*, Vol. 1, Section 3.7 (Example 3.8.3).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Möbius coefficients on a finite Boolean lattice

For a function `f : Finset α → R`, the Möbius coefficient of `f` at `T` is
`mobiusCoeff f T = ∑ U ⊆ T, (-1) ^ |T \ U| f U`. Every function is the sum of its Möbius
coefficients over subsets, and these are the only coefficients with this property.
`HasNonnegMobiusCoeffs E f` says that on the subsets of `E` the function `f` is a sum
`f S = ∑ T ⊆ S, a T` of nonnegative coefficients.

## Main definitions

* `PercLib.mobiusCoeff f T`: the Möbius coefficient of `f` at `T`.
* `PercLib.HasNonnegMobiusCoeffs E f`: `f` has nonnegative Möbius coefficients on the
  subsets of `E`.

## Main results

* `PercLib.sum_powerset_mobiusCoeff`: `∑ T ⊆ S, mobiusCoeff f T = f S`.
* `PercLib.mobiusCoeff_eq_of_forall_eq_sum`: coefficients representing `f` on the subsets of
  `E` are the Möbius coefficients.
* `PercLib.hasNonnegMobiusCoeffs_iff`: membership is nonnegativity of the Möbius coefficients.
* `PercLib.HasNonnegMobiusCoeffs.nonneg`, `PercLib.HasNonnegMobiusCoeffs.mono_of_subset`:
  such functions are nonnegative and increasing.
-/

@[expose] public section

namespace PercLib

open Finset

variable {α R : Type*}

/-- The Möbius coefficient `∑ U ⊆ T, (-1) ^ |T \ U| f U` of a function on finite sets. -/
def mobiusCoeff [DecidableEq α] [Ring R] (f : Finset α → R) (T : Finset α) : R :=
  ∑ U ∈ T.powerset, (-1 : R) ^ (T \ U).card * f U

/-- `f` has nonnegative Möbius coefficients on the subsets of `E`: there are coefficients
`a T ≥ 0` (`T ⊆ E`) with `f S = ∑ T ⊆ S, a T` for every `S ⊆ E`. -/
def HasNonnegMobiusCoeffs [AddCommMonoid R] [LE R] (E : Finset α) (f : Finset α → R) : Prop :=
  ∃ a : Finset α → R, (∀ T ⊆ E, 0 ≤ a T) ∧ ∀ S ⊆ E, f S = ∑ T ∈ S.powerset, a T

theorem mobiusCoeff_def [DecidableEq α] [Ring R] (f : Finset α → R) (T : Finset α) :
    mobiusCoeff f T = ∑ U ∈ T.powerset, (-1 : R) ^ (T \ U).card * f U := rfl

@[simp]
theorem mobiusCoeff_empty [DecidableEq α] [Ring R] (f : Finset α → R) :
    mobiusCoeff f ∅ = f ∅ := by
  simp [mobiusCoeff]

@[simp]
theorem mobiusCoeff_zero [DecidableEq α] [Ring R] (T : Finset α) :
    mobiusCoeff (0 : Finset α → R) T = 0 := by
  simp [mobiusCoeff]

theorem mobiusCoeff_add [DecidableEq α] [Ring R] (f g : Finset α → R) (T : Finset α) :
    mobiusCoeff (f + g) T = mobiusCoeff f T + mobiusCoeff g T := by
  simp [mobiusCoeff, mul_add, sum_add_distrib]

theorem mobiusCoeff_const_mul [DecidableEq α] [Ring R] (c : R) (f : Finset α → R) (T : Finset α) :
    mobiusCoeff (fun S ↦ c * f S) T = c * mobiusCoeff f T := by
  simp only [mobiusCoeff, mul_sum]
  exact sum_congr rfl fun U _ ↦ ((Commute.neg_one_left c).pow_left _).left_comm _

theorem mobiusCoeff_sum [DecidableEq α] [Ring R] {ι : Type*} (s : Finset ι) (F : ι → Finset α → R)
    (T : Finset α) : mobiusCoeff (fun S ↦ ∑ i ∈ s, F i S) T = ∑ i ∈ s, mobiusCoeff (F i) T := by
  simp only [mobiusCoeff, mul_sum]
  exact sum_comm

/-- The alternating sum over `W ⊆ X` of `(-1) ^ |W|` is `1` when `X = ∅` and `0` otherwise. -/
theorem sum_powerset_neg_one_pow_card_eq [DecidableEq α] [Ring R] (X : Finset α) :
    ∑ W ∈ X.powerset, (-1 : R) ^ W.card = if X = ∅ then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → R) (Finset.sum_powerset_neg_one_pow_card (x := X))
  push_cast at h
  exact h

/-- The alternating sum over the sets `T` between `U` and `S` of `(-1) ^ |T \ U|`. -/
theorem sum_powerset_filter_superset_neg_one_pow [DecidableEq α] [Ring R] {U S : Finset α}
    (hUS : U ⊆ S) :
    ∑ T ∈ S.powerset with U ⊆ T, (-1 : R) ^ (T \ U).card = if U = S then 1 else 0 := by
  rw [show (if U = S then (1 : R) else 0) = if S \ U = ∅ then 1 else 0 by
      simp only [sdiff_eq_empty_iff_subset]
      exact if_congr ⟨fun h ↦ h ▸ subset_rfl, fun h ↦ subset_antisymm hUS h⟩ rfl rfl,
    ← sum_powerset_neg_one_pow_card_eq]
  refine sum_nbij' (fun T ↦ T \ U) (fun W ↦ W ∪ U) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [mem_filter, mem_powerset] at hT
    simpa [mem_powerset] using sdiff_subset_sdiff hT.1 subset_rfl
  · intro W hW
    rw [mem_powerset] at hW
    simp only [mem_filter, mem_powerset]
    exact ⟨union_subset (hW.trans sdiff_subset) hUS, subset_union_right⟩
  · intro T hT
    simp only [mem_filter, mem_powerset] at hT
    exact sdiff_union_of_subset hT.2
  · intro W hW
    rw [mem_powerset] at hW
    rw [union_sdiff_right, sdiff_eq_self_of_disjoint]
    exact disjoint_of_subset_left hW disjoint_sdiff_self_left
  · intro T _
    rfl

/-- The alternating sum over the sets `U` between `V` and `T` of `(-1) ^ |T \ U|`. -/
theorem sum_powerset_filter_superset_neg_one_pow_sdiff [DecidableEq α] [Ring R]
    {V T : Finset α} (hVT : V ⊆ T) :
    ∑ U ∈ T.powerset with V ⊆ U, (-1 : R) ^ (T \ U).card = if V = T then 1 else 0 := by
  rw [show (if V = T then (1 : R) else 0) = if T \ V = ∅ then 1 else 0 by
      simp only [sdiff_eq_empty_iff_subset]
      exact if_congr ⟨fun h ↦ h ▸ subset_rfl, fun h ↦ subset_antisymm hVT h⟩ rfl rfl,
    ← sum_powerset_neg_one_pow_card_eq]
  refine sum_nbij' (fun U ↦ T \ U) (fun W ↦ T \ W) ?_ ?_ ?_ ?_ ?_
  · intro U hU
    simp only [mem_filter, mem_powerset] at hU
    simpa [mem_powerset] using sdiff_subset_sdiff subset_rfl hU.2
  · intro W hW
    rw [mem_powerset] at hW
    simp only [mem_filter, mem_powerset]
    refine ⟨sdiff_subset, fun x hx ↦ mem_sdiff.2 ⟨hVT hx, fun hxW ↦ ?_⟩⟩
    exact (mem_sdiff.1 (hW hxW)).2 hx
  · intro U hU
    simp only [mem_filter, mem_powerset] at hU
    exact Finset.sdiff_sdiff_eq_self hU.1
  · intro W hW
    rw [mem_powerset] at hW
    exact Finset.sdiff_sdiff_eq_self (hW.trans sdiff_subset)
  · intro U _
    rfl

/-- **Möbius inversion on the Boolean lattice.** Every function is the sum of its Möbius
coefficients over subsets. -/
theorem sum_powerset_mobiusCoeff [DecidableEq α] [Ring R] (f : Finset α → R) (S : Finset α) :
    ∑ T ∈ S.powerset, mobiusCoeff f T = f S := by
  simp only [mobiusCoeff]
  rw [sum_comm' (t' := S.powerset) (s' := fun U ↦ S.powerset.filter (U ⊆ ·))
    (fun T U ↦ by
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h ↦ ⟨h.1.1, h.1.2⟩⟩)]
  simp_rw [← sum_mul]
  rw [sum_eq_single_of_mem S (mem_powerset.2 subset_rfl)]
  · rw [sum_powerset_filter_superset_neg_one_pow subset_rfl]
    simp
  · intro U hU hne
    rw [sum_powerset_filter_superset_neg_one_pow (mem_powerset.1 hU)]
    simp [hne]

/-- **Uniqueness of the Boolean coefficients.** If `f S = ∑ T ⊆ S, a T` for every `S ⊆ E`,
then `a T` is the Möbius coefficient of `f` for every `T ⊆ E`. -/
theorem mobiusCoeff_eq_of_forall_eq_sum [DecidableEq α] [Ring R] {E : Finset α} {f a : Finset α → R}
    (h : ∀ S ⊆ E, f S = ∑ T ∈ S.powerset, a T) {T : Finset α} (hT : T ⊆ E) :
    mobiusCoeff f T = a T := by
  have hsum : mobiusCoeff f T =
      ∑ U ∈ T.powerset, ∑ V ∈ U.powerset, (-1 : R) ^ (T \ U).card * a V := by
    refine sum_congr rfl fun U hU ↦ ?_
    rw [h U ((mem_powerset.1 hU).trans hT), mul_sum]
  rw [hsum, sum_comm' (t' := T.powerset) (s' := fun V ↦ T.powerset.filter (V ⊆ ·))
    (fun U V ↦ by
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h ↦ ⟨h.1.1, h.1.2⟩⟩)]
  simp_rw [← sum_mul]
  rw [sum_eq_single_of_mem T (mem_powerset.2 subset_rfl)]
  · rw [sum_powerset_filter_superset_neg_one_pow_sdiff subset_rfl]
    simp
  · intro V hV hne
    rw [sum_powerset_filter_superset_neg_one_pow_sdiff (mem_powerset.1 hV)]
    simp [hne]

/-- Membership in the cone is nonnegativity of the Möbius coefficients on subsets of `E`. -/
theorem hasNonnegMobiusCoeffs_iff [DecidableEq α] [Ring R] [PartialOrder R] {E : Finset α}
    {f : Finset α → R} : HasNonnegMobiusCoeffs E f ↔ ∀ T ⊆ E, 0 ≤ mobiusCoeff f T := by
  constructor
  · rintro ⟨a, ha, hf⟩ T hT
    rw [mobiusCoeff_eq_of_forall_eq_sum hf hT]
    exact ha T hT
  · intro h
    exact ⟨mobiusCoeff f, h, fun S _ ↦ (sum_powerset_mobiusCoeff f S).symm⟩

theorem HasNonnegMobiusCoeffs.nonneg [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    {E : Finset α} {f : Finset α → R} (hf : HasNonnegMobiusCoeffs E f) {S : Finset α}
    (hS : S ⊆ E) : 0 ≤ f S := by
  obtain ⟨a, ha, hfa⟩ := hf
  rw [hfa S hS]
  exact sum_nonneg fun T hT ↦ ha T ((mem_powerset.1 hT).trans hS)

/-- A function with nonnegative Möbius coefficients is increasing on the subsets of `E`. -/
theorem HasNonnegMobiusCoeffs.mono_of_subset [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] {E : Finset α} {f : Finset α → R} (hf : HasNonnegMobiusCoeffs E f)
    {S S' : Finset α} (hSS' : S ⊆ S') (hS' : S' ⊆ E) : f S ≤ f S' := by
  obtain ⟨a, ha, hfa⟩ := hf
  rw [hfa S (hSS'.trans hS'), hfa S' hS']
  exact sum_le_sum_of_subset_of_nonneg (powerset_mono.2 hSS')
    fun T hT _ ↦ ha T ((mem_powerset.1 hT).trans hS')

/-- Membership passes to a smaller ground set. -/
theorem HasNonnegMobiusCoeffs.mono [AddCommMonoid R] [LE R] {E F : Finset α}
    {f : Finset α → R} (hf : HasNonnegMobiusCoeffs E f) (hFE : F ⊆ E) :
    HasNonnegMobiusCoeffs F f := by
  obtain ⟨a, ha, hfa⟩ := hf
  exact ⟨a, fun T hT ↦ ha T (hT.trans hFE), fun S hS ↦ hfa S (hS.trans hFE)⟩

@[simp]
theorem hasNonnegMobiusCoeffs_zero [AddCommMonoid R] [Preorder R] (E : Finset α) :
    HasNonnegMobiusCoeffs E (0 : Finset α → R) :=
  ⟨0, fun _ _ ↦ le_rfl, fun _ _ ↦ by simp⟩

/-- A nonnegative constant has nonnegative Möbius coefficients (only the empty set carries
weight). -/
theorem hasNonnegMobiusCoeffs_const [AddCommMonoid R] [Preorder R] (E : Finset α) {c : R}
    (hc : 0 ≤ c) : HasNonnegMobiusCoeffs E (fun _ ↦ c) := by
  classical
  refine ⟨fun T ↦ if T = ∅ then c else 0, fun T _ ↦ ?_, fun S _ ↦ ?_⟩
  · dsimp only
    split_ifs
    exacts [hc, le_rfl]
  · simp

end PercLib
