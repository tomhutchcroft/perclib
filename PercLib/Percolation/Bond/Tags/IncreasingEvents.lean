/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for increasing events and observables.
All mathematical inputs are proved in the imported modules or in mathlib.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.OpenEventHarris

/-!
# Increasing events and observables: correspondence

Configurations are ordered by inclusion. An increasing event is mathlib's `IsUpperSet` and an
increasing observable is mathlib's `Monotone`, for the inclusion order on `Set ι`. Connection
events are increasing.

## Main results

* `isUpperSet_monotone_iff_and_isUpperSet_conn`
-/

@[expose] public section
noncomputable section

namespace PercLib.Percolation.Bond

/-- For the inclusion order on configurations, an event `A` is increasing (`IsUpperSet A`)
exactly when `ω ∈ A` and `ω ⊆ ω'` imply `ω' ∈ A`, and a real observable `f` is increasing
(`Monotone f`) exactly when `f ω ≤ f ω'` whenever `ω ⊆ ω'`. Connection events are
increasing. -/
@[tag "H4OA"]
theorem isUpperSet_monotone_iff_and_isUpperSet_conn {ι V : Type*} :
    (∀ A : Set (Set ι), IsUpperSet A ↔ ∀ ω ω' : Set ι, ω ∈ A → ω ⊆ ω' → ω' ∈ A) ∧
    (∀ f : Set ι → ℝ, Monotone f ↔ ∀ ω ω' : Set ι, ω ⊆ ω' → f ω ≤ f ω') ∧
    (∀ x y : V, IsUpperSet (conn x y : Set (Config V))) :=
  ⟨fun _ => ⟨fun h _ _ hω hle => h hle hω, fun h _ _ hle hω => h _ _ hω hle⟩,
    fun _ => Iff.rfl, isUpperSet_conn⟩

end PercLib.Percolation.Bond
