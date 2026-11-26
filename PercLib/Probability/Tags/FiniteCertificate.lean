/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the countable-Reimer assertion 1NUW, proved from
`FiniteCertificate.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.FiniteCertificate

/-!
# Finite certificates for open events: correspondence

Wiki correspondence for the reduction of arbitrary certificates of open events of the
Bernoulli configuration space `ι → Bool` (product topology) to finite ones, from
`PercLib/Probability/FiniteCertificate.lean`.

## Main results

* `exists_finset_cylinder_subset_and_disjoint_certificates_eq_finite`
-/

@[expose] public section

namespace PercLib.Probability

/-- **1NUW.** On `Ω = ι → Bool` with the product topology, write `[ω]_K` for the cylinder
`{η | ∀ i ∈ K, η i = ω i}`. If `U` is open and `[ω]_K ⊆ U`, then `[ω]_F ⊆ U` for some finite
`F ⊆ K`. Consequently, for open `U, V`, disjoint occurrence with arbitrary disjoint certificates
equals disjoint occurrence with finite disjoint certificates: `U □_∞ V = U □_f V`. -/
@[tag "1NUW"]
theorem exists_finset_cylinder_subset_and_disjoint_certificates_eq_finite {ι : Type*} :
    (∀ U : Set (ι → Bool), IsOpen U → ∀ (ω : ι → Bool) (K : Set ι),
      {η | ∀ i ∈ K, η i = ω i} ⊆ U →
        ∃ F : Finset ι, (F : Set ι) ⊆ K ∧ {η | ∀ i ∈ F, η i = ω i} ⊆ U) ∧
    ∀ U V : Set (ι → Bool), IsOpen U → IsOpen V →
      {ω : ι → Bool | ∃ K L : Set ι, Disjoint K L ∧
          {η | ∀ i ∈ K, η i = ω i} ⊆ U ∧ {η | ∀ i ∈ L, η i = ω i} ⊆ V} =
        {ω : ι → Bool | ∃ K L : Set ι, K.Finite ∧ L.Finite ∧ Disjoint K L ∧
          {η | ∀ i ∈ K, η i = ω i} ⊆ U ∧ {η | ∀ i ∈ L, η i = ω i} ⊆ V} :=
  ⟨fun _ hU ω _ hK => exists_finset_cylinder_subset_of_isOpen hU ω hK,
    fun _ _ hU hV => disjoint_certificates_eq_finite_of_isOpen hU hV⟩

end PercLib.Probability
