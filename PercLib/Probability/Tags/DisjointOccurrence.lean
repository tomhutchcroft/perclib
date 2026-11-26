/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the disjoint-occurrence assertions. Every statement is
assembled from lemmas proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.CountableBK
public import PercLib.Probability.DisjointOccurrenceAlgebra

/-!
# Disjoint occurrence: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `countable_bk_measurable_and_bound`
* `disjointOccurrence_basic_properties`
* `disjointOccurrence_open_witness_and_upper`
* `disjointOccurrence_union_distrib`
* `disjointOccurrence_three_witness_and_assoc`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set

namespace PercLib.Probability
variable {ι : Type*}

/-- Countable BK: disjoint occurrence of increasing events is measurable and has
probability at most the product, for every Bernoulli profile. -/
@[tag "JRCI"]
theorem countable_bk_measurable_and_bound [Countable ι] (p : ι → unitInterval)
    {A B : Set (Set ι)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    MeasurableSet (disjointOccurrence A B) ∧
      prodBernoulli p (disjointOccurrence A B) ≤ prodBernoulli p A * prodBernoulli p B :=
  ⟨measurableSet_disjointOccurrence hA hB, countable_profile_bk p hA hB⟩

/-- Elementary properties of disjoint occurrence: it implies both events, is symmetric,
and is monotone in each event. -/
@[tag "X7ET"]
theorem disjointOccurrence_basic_properties :
    ∀ A B C D : Set (Set ι), disjointOccurrence A B ⊆ A ∩ B ∧
      disjointOccurrence A B = disjointOccurrence B A ∧
      (A ⊆ C → B ⊆ D → disjointOccurrence A B ⊆ disjointOccurrence C D) :=
  fun A B _ _ => ⟨disjointOccurrence_subset_inter A B, disjointOccurrence_comm A B,
    fun hAC hBD => disjointOccurrence_mono hAC hBD⟩

/-- For increasing events, disjoint occurrence is witnessed by disjoint finite open sets,
and is itself increasing. -/
@[tag "HRBD"]
theorem disjointOccurrence_open_witness_and_upper {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (∀ ω, ω ∈ disjointOccurrence A B ↔
      ∃ F H : Set ι, F.Finite ∧ H.Finite ∧ Disjoint F H ∧
        F ⊆ ω ∧ H ⊆ ω ∧ F ∈ A ∧ H ∈ B) ∧
    IsUpperSet (disjointOccurrence A B) :=
  ⟨mem_disjointOccurrence_iff_open hA hB, isUpperSet_disjointOccurrence hA hB⟩

/-- Disjoint occurrence of increasing events distributes over unions in each argument. -/
@[tag "17DW"]
theorem disjointOccurrence_union_distrib {A B C : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C) :
    disjointOccurrence (A ∪ B) C = disjointOccurrence A C ∪ disjointOccurrence B C ∧
      disjointOccurrence A (B ∪ C) = disjointOccurrence A B ∪ disjointOccurrence A C :=
  ⟨disjointOccurrence_union_left hA hB hC, disjointOccurrence_union_right hA hB hC⟩

/-- Nested disjoint occurrence of three increasing events is witnessed by three pairwise
disjoint finite open sets, and disjoint occurrence is associative. -/
@[tag "HP3X"]
theorem disjointOccurrence_three_witness_and_assoc {A B C : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C) :
    (∀ ω, ω ∈ disjointOccurrence (disjointOccurrence A B) C ↔
      ∃ F H K : Set ι, F.Finite ∧ H.Finite ∧ K.Finite ∧
        Disjoint F H ∧ Disjoint F K ∧ Disjoint H K ∧
        F ⊆ ω ∧ H ⊆ ω ∧ K ⊆ ω ∧ F ∈ A ∧ H ∈ B ∧ K ∈ C) ∧
    disjointOccurrence (disjointOccurrence A B) C =
      disjointOccurrence A (disjointOccurrence B C) :=
  ⟨mem_disjointOccurrence_three_iff hA hB hC, disjointOccurrence_assoc hA hB hC⟩

end PercLib.Probability
