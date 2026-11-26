/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Inserting a new point into a finite partition of a finset. New for this project against
pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied.
Mathematical reference: the standard recursion for set partitions (a new point either forms a
singleton block or joins an existing block), e.g. R. P. Stanley, *Enumerative Combinatorics*,
Vol. 1, Section 1.9.
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.BigOperators

/-!
# Inserting a point into a finpartition

Let `a ∉ s`. Every partition of `insert a s` arises in exactly one way from a partition `P` of
`s`, either by adding `{a}` as a new part or by adding `a` to one part of `P`. This gives the
recursion of sums over `Finpartition (insert a s)`.

## Main definitions

* `Finpartition.extendSingleton P ha`: the partition of `insert a s` obtained from
  `P : Finpartition s` by adding the part `{a}`.
* `Finpartition.insertIntoPart P ha t ht`: the partition of `insert a s` obtained from `P` by
  replacing its part `t` by `insert a t`.
* `Finpartition.extendOption P ha`: both constructions, indexed by `Option P.parts`.
* `Finpartition.restrictErase Q ha`: the partition of `s` obtained from
  `Q : Finpartition (insert a s)` by removing `a`.

## Main results

* `Finpartition.restrictErase_extendOption`: removing `a` undoes both constructions.
* `Finpartition.extendOption_injective`, `Finpartition.exists_extendOption_eq`: each partition
  of `insert a s` arises from exactly one pair `(P, o)`.
* `Finpartition.sum_insert_eq_sum_sum_option`: the sum over partitions of `insert a s` is the
  sum over partitions `P` of `s` and over `o : Option P.parts`.
-/

@[expose] public section

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {a : α}

/-- Add the new part `{a}` to a partition of `s`, where `a ∉ s`. -/
def extendSingleton (P : Finpartition s) (ha : a ∉ s) : Finpartition (insert a s) :=
  P.extend (b := {a}) (singleton_ne_empty a) (disjoint_singleton_right.2 ha)
    (by rw [sup_eq_union, union_comm, ← insert_eq])

@[simp]
theorem parts_extendSingleton (P : Finpartition s) (ha : a ∉ s) :
    (P.extendSingleton ha).parts = insert {a} P.parts := rfl

theorem singleton_notMem_parts (P : Finpartition s) (ha : a ∉ s) : ({a} : Finset α) ∉ P.parts :=
  fun h ↦ ha (P.le h (mem_singleton_self a))

theorem notMem_of_mem_parts (P : Finpartition s) (ha : a ∉ s) {t : Finset α}
    (ht : t ∈ P.parts) : a ∉ t :=
  fun h ↦ ha (P.le ht h)

theorem card_parts_extendSingleton (P : Finpartition s) (ha : a ∉ s) :
    #(P.extendSingleton ha).parts = #P.parts + 1 := by
  rw [parts_extendSingleton, card_insert_of_notMem (P.singleton_notMem_parts ha)]

/-- Replace the part `t` of a partition of `s` by `insert a t`, where `a ∉ s`. -/
def insertIntoPart (P : Finpartition s) (ha : a ∉ s) (t : Finset α) (ht : t ∈ P.parts) :
    Finpartition (insert a s) where
  parts := insert (insert a t) (P.parts.erase t)
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint, coe_insert]
    refine (P.disjoint.subset (coe_subset.2 (erase_subset _ _))).insert fun u hu _ ↦ ?_
    obtain ⟨hut, hu⟩ := mem_erase.1 hu
    exact disjoint_insert_left.2 ⟨P.notMem_of_mem_parts ha hu, P.disjoint ht hu (Ne.symm hut)⟩
  sup_parts := by
    have h := P.sup_parts
    rw [← insert_erase ht, sup_insert] at h
    simp only [sup_insert, id, sup_eq_union] at h ⊢
    rw [insert_union, h]
  bot_notMem h := by
    rcases mem_insert.1 h with h | h
    · exact insert_ne_empty a t h.symm
    · exact P.bot_notMem (mem_of_mem_erase h)

@[simp]
theorem parts_insertIntoPart (P : Finpartition s) (ha : a ∉ s) (t : Finset α)
    (ht : t ∈ P.parts) : (P.insertIntoPart ha t ht).parts = insert (insert a t) (P.parts.erase t) :=
  rfl

theorem card_parts_insertIntoPart (P : Finpartition s) (ha : a ∉ s) (t : Finset α)
    (ht : t ∈ P.parts) : #(P.insertIntoPart ha t ht).parts = #P.parts := by
  rw [parts_insertIntoPart, card_insert_of_notMem, card_erase_add_one ht]
  intro h
  exact P.notMem_of_mem_parts ha (mem_of_mem_erase h) (mem_insert_self a t)

/-- The two ways of inserting `a ∉ s` into a partition of `s`: as a new part (`none`) or into
an existing part (`some t`). -/
def extendOption (P : Finpartition s) (ha : a ∉ s) : Option P.parts → Finpartition (insert a s)
  | none => P.extendSingleton ha
  | some t => P.insertIntoPart ha t.1 t.2

@[simp]
theorem extendOption_none (P : Finpartition s) (ha : a ∉ s) :
    P.extendOption ha none = P.extendSingleton ha := rfl

@[simp]
theorem extendOption_some (P : Finpartition s) (ha : a ∉ s) (t : P.parts) :
    P.extendOption ha (some t) = P.insertIntoPart ha t.1 t.2 := rfl

private theorem sdiff_singleton_of_notMem {d : Finset α} (h : a ∉ d) : d \ {a} = d := by
  rw [sdiff_singleton_eq_erase, erase_eq_of_notMem h]

private theorem insert_sdiff_cancel {d : Finset α} (h : a ∉ d) : insert a d \ {a} = d := by
  rw [sdiff_singleton_eq_erase, erase_insert h]

/-- Remove the point `a` from a partition of `insert a s`, where `a ∉ s`. -/
def restrictErase (Q : Finpartition (insert a s)) (ha : a ∉ s) : Finpartition s :=
  (Q.avoid {a}).copy (by rw [insert_sdiff_cancel ha])

theorem mem_parts_restrictErase (Q : Finpartition (insert a s)) (ha : a ∉ s) {c : Finset α} :
    c ∈ (Q.restrictErase ha).parts ↔ ∃ d ∈ Q.parts, ¬d ⊆ {a} ∧ d \ {a} = c := by
  simp [restrictErase, subset_singleton_iff]

theorem restrictErase_extendSingleton (P : Finpartition s) (ha : a ∉ s) :
    (P.extendSingleton ha).restrictErase ha = P := by
  ext c
  rw [mem_parts_restrictErase, parts_extendSingleton]
  constructor
  · rintro ⟨d, hd, hda, rfl⟩
    rcases mem_insert.1 hd with rfl | hd
    · exact absurd subset_rfl hda
    · rwa [sdiff_singleton_of_notMem (P.notMem_of_mem_parts ha hd)]
  · intro hc
    refine ⟨c, mem_insert_of_mem hc, fun h ↦ ?_, sdiff_singleton_of_notMem
      (P.notMem_of_mem_parts ha hc)⟩
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hc
    have := mem_singleton.1 (h hx)
    exact P.notMem_of_mem_parts ha hc (this ▸ hx)

theorem restrictErase_insertIntoPart (P : Finpartition s) (ha : a ∉ s) (t : Finset α)
    (ht : t ∈ P.parts) : (P.insertIntoPart ha t ht).restrictErase ha = P := by
  have hat := P.notMem_of_mem_parts ha ht
  have key : ∀ c ∈ P.parts, ¬c ⊆ {a} := fun c hc h ↦ by
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hc
    exact P.notMem_of_mem_parts ha hc (mem_singleton.1 (h hx) ▸ hx)
  ext c
  rw [mem_parts_restrictErase, parts_insertIntoPart]
  constructor
  · rintro ⟨d, hd, hda, rfl⟩
    rcases mem_insert.1 hd with rfl | hd
    · rwa [insert_sdiff_cancel hat]
    · rw [sdiff_singleton_of_notMem (P.notMem_of_mem_parts ha (mem_of_mem_erase hd))]
      exact mem_of_mem_erase hd
  · intro hc
    by_cases hct : c = t
    · subst hct
      refine ⟨insert a c, mem_insert_self _ _, fun h ↦ key c hc
        ((subset_insert a c).trans h), insert_sdiff_cancel hat⟩
    · exact ⟨c, mem_insert_of_mem (mem_erase.2 ⟨hct, hc⟩), key c hc,
        sdiff_singleton_of_notMem (P.notMem_of_mem_parts ha hc)⟩

@[simp]
theorem restrictErase_extendOption (P : Finpartition s) (ha : a ∉ s) (o : Option P.parts) :
    (P.extendOption ha o).restrictErase ha = P := by
  cases o with
  | none => exact P.restrictErase_extendSingleton ha
  | some t => exact P.restrictErase_insertIntoPart ha t.1 t.2

/-- The part of `P.extendOption ha o` that contains `a`. -/
theorem mem_parts_extendOption_iff_of_mem (P : Finpartition s) (ha : a ∉ s)
    (o : Option P.parts) {u : Finset α} (hu : a ∈ u) :
    u ∈ (P.extendOption ha o).parts ↔ u = o.elim {a} (fun t ↦ insert a t.1) := by
  cases o with
  | none =>
    simp only [extendOption_none, parts_extendSingleton, mem_insert, Option.elim_none]
    exact or_iff_left fun h ↦ P.notMem_of_mem_parts ha h hu
  | some t =>
    simp only [extendOption_some, parts_insertIntoPart, mem_insert, Option.elim_some]
    exact or_iff_left fun h ↦ P.notMem_of_mem_parts ha (mem_of_mem_erase h) hu

theorem extendOption_injective (P : Finpartition s) (ha : a ∉ s) :
    Function.Injective (P.extendOption ha) := by
  intro o o' h
  have key : ∀ o : Option P.parts,
      o.elim {a} (fun t ↦ insert a t.1) ∈ (P.extendOption ha o).parts := fun o ↦
    (P.mem_parts_extendOption_iff_of_mem ha o (by cases o <;> simp)).2 rfl
  have h1 := key o
  rw [h, P.mem_parts_extendOption_iff_of_mem ha o' (by cases o <;> simp)] at h1
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some t' =>
      simp only [Option.elim_none, Option.elim_some] at h1
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts t'.2
      have : x ∈ ({a} : Finset α) := h1 ▸ mem_insert_of_mem hx
      exact absurd (mem_singleton.1 this ▸ hx) (P.notMem_of_mem_parts ha t'.2)
  | some t =>
    cases o' with
    | none =>
      simp only [Option.elim_none, Option.elim_some] at h1
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts t.2
      have : x ∈ ({a} : Finset α) := h1.symm ▸ mem_insert_of_mem hx
      exact absurd (mem_singleton.1 this ▸ hx) (P.notMem_of_mem_parts ha t.2)
    | some t' =>
      simp only [Option.elim_some] at h1
      refine congrArg some (Subtype.ext ?_)
      rw [← erase_insert (P.notMem_of_mem_parts ha t.2), h1,
        erase_insert (P.notMem_of_mem_parts ha t'.2)]

/-- Every partition of `insert a s` arises from its restriction to `s` by one of the two
insertions. -/
theorem exists_extendOption_eq (Q : Finpartition (insert a s)) (ha : a ∉ s) :
    ∃ o, (Q.restrictErase ha).extendOption ha o = Q := by
  set P := Q.restrictErase ha
  obtain ⟨u, hu, hau⟩ := Q.exists_mem (mem_insert_self a s)
  have hother : ∀ d ∈ Q.parts, d ≠ u → a ∉ d := fun d hd hdu had ↦
    hdu (Q.eq_of_mem_parts hd hu had hau)
  have hP : ∀ d ∈ Q.parts, d ≠ u → d ∈ P.parts := fun d hd hdu ↦ by
    refine (Q.mem_parts_restrictErase ha).2 ⟨d, hd, fun h ↦ ?_,
      sdiff_singleton_of_notMem (hother d hd hdu)⟩
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hd
    exact hother d hd hdu (mem_singleton.1 (h hx) ▸ hx)
  have hP' : ∀ c ∈ P.parts, c ≠ u.erase a → c ∈ Q.parts ∧ c ≠ u := fun c hc hcu ↦ by
    obtain ⟨d, hd, -, rfl⟩ := (Q.mem_parts_restrictErase ha).1 hc
    by_cases hdu : d = u
    · subst hdu; exact absurd (sdiff_singleton_eq_erase a d) hcu
    · rw [sdiff_singleton_of_notMem (hother d hd hdu)]; exact ⟨hd, hdu⟩
  by_cases hsing : u = {a}
  · refine ⟨none, ?_⟩
    ext c
    rw [extendOption_none, parts_extendSingleton, mem_insert]
    constructor
    · rintro (rfl | hc)
      · exact hsing ▸ hu
      · by_cases hcu : c = u.erase a
        · exfalso
          rw [hsing, erase_singleton] at hcu
          exact P.ne_empty hc hcu
        · exact (hP' c hc hcu).1
    · intro hc
      by_cases hcu : c = u
      · exact Or.inl (hcu.trans hsing)
      · exact Or.inr (hP c hc hcu)
  · have hne : ¬u ⊆ {a} := fun h ↦ hsing (Subset.antisymm h (singleton_subset_iff.2 hau))
    have htP : u.erase a ∈ P.parts := (Q.mem_parts_restrictErase ha).2
      ⟨u, hu, hne, sdiff_singleton_eq_erase a u⟩
    refine ⟨some ⟨u.erase a, htP⟩, ?_⟩
    ext c
    rw [extendOption_some, parts_insertIntoPart, insert_erase hau, mem_insert]
    constructor
    · rintro (rfl | hc)
      · exact hu
      · exact (hP' c (mem_of_mem_erase hc) (ne_of_mem_erase hc)).1
    · intro hc
      by_cases hcu : c = u
      · exact Or.inl hcu
      · refine Or.inr (mem_erase.2 ⟨fun h ↦ hcu ?_, hP c hc hcu⟩)
        obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts htP
        exact Q.eq_of_mem_parts hc hu (h ▸ hx) (mem_of_mem_erase hx)

/-- **Sums over partitions of `insert a s`.** For `a ∉ s`, summing over the partitions of
`insert a s` is summing over the partitions `P` of `s` and over the ways `o : Option P.parts`
of inserting `a` into `P`. -/
theorem sum_insert_eq_sum_sum_option {M : Type*} [AddCommMonoid M] (ha : a ∉ s)
    (G : Finpartition (insert a s) → M) :
    ∑ Q, G Q = ∑ P : Finpartition s, ∑ o : Option P.parts, G (P.extendOption ha o) := by
  rw [← Finset.sum_fiberwise univ (fun Q ↦ Q.restrictErase ha) G]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  symm
  refine Finset.sum_bij (fun o _ ↦ P.extendOption ha o) (fun o _ ↦ ?_)
    (fun o _ o' _ h ↦ P.extendOption_injective ha h) (fun Q hQ ↦ ?_) (fun _ _ ↦ rfl)
  · simp
  · obtain rfl := (mem_filter.1 hQ).2
    obtain ⟨o, ho⟩ := Q.exists_extendOption_eq ha
    exact ⟨o, mem_univ _, ho⟩

/-- `sum_insert_eq_sum_sum_option` with the two kinds of insertion written out. -/
theorem sum_insert_eq_sum_add_sum {M : Type*} [AddCommMonoid M] (ha : a ∉ s)
    (G : Finpartition (insert a s) → M) :
    ∑ Q, G Q = ∑ P : Finpartition s, (G (P.extendSingleton ha) +
      ∑ t ∈ P.parts.attach, G (P.insertIntoPart ha t.1 t.2)) := by
  rw [sum_insert_eq_sum_sum_option ha]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  rw [Fintype.sum_option]
  rfl

end Finpartition
