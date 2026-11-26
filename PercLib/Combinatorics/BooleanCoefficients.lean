/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Closure properties of the cone of functions with nonnegative Boolean (Möbius) coefficients.
New for this project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no
upstream code is copied. Mathematical reference: Möbius inversion on the Boolean lattice,
R. P. Stanley, *Enumerative Combinatorics*, Vol. 1, Section 3.7; the cone is used for
higher-order correlation inequalities in D. St. P. Richards, *Algebraic methods toward
higher-order probability inequalities, II*, Ann. Probab. 32 (2004).
-/
module

public import PercLib.Combinatorics.BooleanCoefficients.Defs

/-!
# The cone of functions with nonnegative Boolean coefficients

For a finite set `E`, the functions `f S = ∑ T ⊆ S, a T` with `a T ≥ 0` form a cone,
`HasNonnegMobiusCoeffs E f`. It is closed under nonnegative linear combinations and pointwise
products, and for `e ∈ E` the restrictions `S ↦ f S` and `S ↦ f (S ∪ {e})` to subsets of
`E \ {e}`, as well as their difference, stay in the cone over `E \ {e}`.

## Main results

* `PercLib.hasNonnegMobiusCoeffs_sum`: nonnegative linear combinations.
* `PercLib.HasNonnegMobiusCoeffs.mul`: pointwise products.
* `PercLib.HasNonnegMobiusCoeffs.erase`, `PercLib.HasNonnegMobiusCoeffs.comp_insert`,
  `PercLib.HasNonnegMobiusCoeffs.comp_insert_sub`: the two restrictions at a coordinate and their
  difference.
-/

@[expose] public section

namespace PercLib

open Finset

variable {α R : Type*} {E : Finset α}

/-- **Nonnegative linear combinations** of functions with nonnegative Möbius coefficients have
nonnegative Möbius coefficients. -/
theorem hasNonnegMobiusCoeffs_sum [Ring R] [PartialOrder R] [IsOrderedRing R] {ι : Type*}
    (s : Finset ι) {c : ι → R} {F : ι → Finset α → R} (hc : ∀ i ∈ s, 0 ≤ c i)
    (hF : ∀ i ∈ s, HasNonnegMobiusCoeffs E (F i)) :
    HasNonnegMobiusCoeffs E (fun S ↦ ∑ i ∈ s, c i * F i S) := by
  classical
  rw [hasNonnegMobiusCoeffs_iff]
  intro T hT
  rw [mobiusCoeff_sum]
  refine sum_nonneg fun i hi ↦ ?_
  rw [mobiusCoeff_const_mul]
  exact mul_nonneg (hc i hi) (hasNonnegMobiusCoeffs_iff.1 (hF i hi) T hT)

theorem HasNonnegMobiusCoeffs.add [AddCommMonoid R] [Preorder R] [IsOrderedAddMonoid R]
    {f g : Finset α → R} (hf : HasNonnegMobiusCoeffs E f) (hg : HasNonnegMobiusCoeffs E g) :
    HasNonnegMobiusCoeffs E (f + g) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  exact ⟨a + b, fun T hT ↦ add_nonneg (ha T hT) (hb T hT), fun S hS ↦ by
    simp [hfa S hS, hgb S hS, sum_add_distrib]⟩

/-- **Pointwise products** of functions with nonnegative Möbius coefficients have nonnegative
Möbius coefficients: the coefficient of the product at `T` is `∑_{U ∪ V = T} a U * b V`. -/
theorem HasNonnegMobiusCoeffs.mul [DecidableEq α] [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] {f g : Finset α → R} (hf : HasNonnegMobiusCoeffs E f)
    (hg : HasNonnegMobiusCoeffs E g) : HasNonnegMobiusCoeffs E (fun S ↦ f S * g S) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun T ↦ ∑ p ∈ (T.powerset ×ˢ T.powerset) with p.1 ∪ p.2 = T, a p.1 * b p.2,
    fun T hT ↦ sum_nonneg fun p hp ↦ ?_, fun S hS ↦ ?_⟩
  · simp only [mem_filter, mem_product, mem_powerset] at hp
    exact mul_nonneg (ha _ (hp.1.1.trans hT)) (hb _ (hp.1.2.trans hT))
  · dsimp only
    rw [hfa S hS, hgb S hS, sum_mul_sum, ← sum_product',
      ← sum_fiberwise_of_maps_to (s := S.powerset ×ˢ S.powerset) (t := S.powerset)
        (g := fun p ↦ p.1 ∪ p.2) (fun p hp ↦ by
          simp only [mem_product, mem_powerset] at hp ⊢
          exact union_subset hp.1 hp.2)]
    refine sum_congr rfl fun T hT ↦ sum_congr ?_ fun _ _ ↦ rfl
    rw [mem_powerset] at hT
    ext p
    simp only [mem_filter, mem_product, mem_powerset]
    constructor
    · rintro ⟨-, hp⟩
      exact ⟨⟨hp ▸ subset_union_left, hp ▸ subset_union_right⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨h1.trans hT, h2.trans hT⟩, hp⟩

/-- The restriction `S ↦ f S` to subsets of `E \ {e}` keeps nonnegative Möbius coefficients. -/
theorem HasNonnegMobiusCoeffs.erase [DecidableEq α] [AddCommMonoid R] [LE R]
    {f : Finset α → R} (hf : HasNonnegMobiusCoeffs E f) (e : α) :
    HasNonnegMobiusCoeffs (E.erase e) f :=
  hf.mono (erase_subset e E)

/-- The coefficients of `S ↦ f (S ∪ {e})` on subsets of `E \ {e}` are `a T + a (T ∪ {e})`. -/
theorem HasNonnegMobiusCoeffs.comp_insert [DecidableEq α] [AddCommMonoid R] [Preorder R]
    [IsOrderedAddMonoid R] {f : Finset α → R} (hf : HasNonnegMobiusCoeffs E f) {e : α}
    (he : e ∈ E) : HasNonnegMobiusCoeffs (E.erase e) (fun S ↦ f (insert e S)) := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun T ↦ a T + a (insert e T), fun T hT ↦ ?_, fun S hS ↦ ?_⟩
  · have hTE : T ⊆ E := hT.trans (erase_subset e E)
    exact add_nonneg (ha T hTE) (ha _ (insert_subset he hTE))
  · have heS : e ∉ S := fun h ↦ (mem_erase.1 (hS h)).1 rfl
    dsimp only
    rw [hfa _ (insert_subset he (hS.trans (erase_subset e E))), sum_powerset_insert heS,
      sum_add_distrib]

/-- The coordinate difference `S ↦ f (S ∪ {e}) - f S` on subsets of `E \ {e}` has the
nonnegative coefficients `a (T ∪ {e})`. -/
theorem HasNonnegMobiusCoeffs.comp_insert_sub [DecidableEq α] [AddCommGroup R] [LE R]
    {f : Finset α → R} (hf : HasNonnegMobiusCoeffs E f) {e : α} (he : e ∈ E) :
    HasNonnegMobiusCoeffs (E.erase e) (fun S ↦ f (insert e S) - f S) := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun T ↦ a (insert e T), fun T hT ↦ ?_, fun S hS ↦ ?_⟩
  · exact ha _ (insert_subset he (hT.trans (erase_subset e E)))
  · have heS : e ∉ S := fun h ↦ (mem_erase.1 (hS h)).1 rfl
    have hSE : S ⊆ E := hS.trans (erase_subset e E)
    dsimp only
    rw [hfa _ (insert_subset he hSE), hfa S hSE, sum_powerset_insert heS, add_sub_cancel_left]

end PercLib
