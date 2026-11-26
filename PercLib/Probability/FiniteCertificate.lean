/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, from pinned mathlib's compactness of products and the finite intersection property.
Mathematical reference: the compactness step in extending the van den Berg–Kesten–Reimer
inequality to countable products (C. Borgs, J. Chayes, D. Randall, *The van den
Berg–Kesten–Reimer inequality: a review*, 1999). No source text or code is copied.
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Instances.Discrete

/-!
# Infinite certificates of open events contain finite ones

Let `X = ∀ i, E i` be a product of compact `T₁` spaces. For `ω ∈ X` and `K ⊆ ι` the cylinder
`{η | ∀ i ∈ K, η i = ω i}` fixes the coordinates in `K`. If such a cylinder lies in an open set
`U`, then already the cylinder of some finite `F ⊆ K` lies in `U`: otherwise the closed sets
`{η | ∀ i ∈ F, η i = ω i} \ U`, directed over finite `F ⊆ K`, have the finite intersection
property in the compact space `X`, and a common point lies in the `K`-cylinder but outside `U`.

Consequently, for open events of the Bernoulli configuration space `ι → Bool`, disjoint
occurrence with arbitrary disjoint certificates coincides with disjoint occurrence with finite
disjoint certificates.

## Main results

* `PercLib.Probability.exists_finset_cylinder_subset_of_isOpen`
* `PercLib.Probability.disjoint_certificates_eq_finite_of_isOpen`
-/

@[expose] public section

open Set

namespace PercLib.Probability

variable {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]

/-- **Finite subcertificates.** In a product of compact `T₁` spaces, if the cylinder
`{η | ∀ i ∈ K, η i = ω i}` is contained in an open set `U`, then so is the cylinder of some
finite `F ⊆ K`. -/
theorem exists_finset_cylinder_subset_of_isOpen [∀ i, CompactSpace (E i)] [∀ i, T1Space (E i)]
    {U : Set (∀ i, E i)} (hU : IsOpen U) (ω : ∀ i, E i) {K : Set ι}
    (hK : {η | ∀ i ∈ K, η i = ω i} ⊆ U) :
    ∃ F : Finset ι, (F : Set ι) ⊆ K ∧ {η | ∀ i ∈ F, η i = ω i} ⊆ U := by
  classical
  let t : {F : Finset ι // (F : Set ι) ⊆ K} → Set (∀ i, E i) :=
    fun F => {η | ∀ i ∈ F.1, η i = ω i}
  have ht : ∀ F, t F = (F.1 : Set ι).pi fun i => {ω i} := fun F => by
    ext η; simp [t]
  have htc : ∀ F, IsClosed (t F) := fun F => by
    rw [ht]; exact isClosed_set_pi fun i _ => isClosed_singleton
  have hdir : Directed (· ⊇ ·) t := fun F G =>
    ⟨⟨F.1 ∪ G.1, by simpa using And.intro F.2 G.2⟩,
      fun η hη i hi => hη i (Finset.mem_union_left _ hi),
      fun η hη i hi => hη i (Finset.mem_union_right _ hi)⟩
  have hinter : (⋂ F, t F) ⊆ U := fun η hη => hK fun i hi => by
    have := mem_iInter.1 hη ⟨{i}, by simpa using hi⟩
    exact this i (Finset.mem_singleton_self i)
  have : Nonempty {F : Finset ι // (F : Set ι) ⊆ K} := ⟨⟨∅, by simp⟩⟩
  obtain ⟨F, hF⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed t htc
    (disjoint_compl_left_iff_subset.2 hinter) hdir
  exact ⟨F.1, F.2, disjoint_compl_left_iff_subset.1 hF⟩

/-- **Disjoint occurrence of open events.** For open events `U, V` of `ι → Bool`, a
configuration has disjoint certificates `K, L` (cylinders `[ω]_K ⊆ U`, `[ω]_L ⊆ V`) if and only if
it has finite disjoint certificates. -/
theorem disjoint_certificates_eq_finite_of_isOpen {U V : Set (ι → Bool)} (hU : IsOpen U)
    (hV : IsOpen V) :
    {ω : ι → Bool | ∃ K L : Set ι, Disjoint K L ∧
        {η | ∀ i ∈ K, η i = ω i} ⊆ U ∧ {η | ∀ i ∈ L, η i = ω i} ⊆ V} =
      {ω : ι → Bool | ∃ K L : Set ι, K.Finite ∧ L.Finite ∧ Disjoint K L ∧
        {η | ∀ i ∈ K, η i = ω i} ⊆ U ∧ {η | ∀ i ∈ L, η i = ω i} ⊆ V} := by
  ext ω
  constructor
  · rintro ⟨K, L, hKL, hK, hL⟩
    obtain ⟨F, hFK, hF⟩ := exists_finset_cylinder_subset_of_isOpen hU ω hK
    obtain ⟨G, hGL, hG⟩ := exists_finset_cylinder_subset_of_isOpen hV ω hL
    exact ⟨F, G, F.finite_toSet, G.finite_toSet, hKL.mono hFK hGL, hF, hG⟩
  · rintro ⟨K, L, -, -, hKL, hK, hL⟩
    exact ⟨K, L, hKL, hK, hL⟩

end PercLib.Probability
