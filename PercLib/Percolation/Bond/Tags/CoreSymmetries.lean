/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Embedding
public import PercLib.Percolation.Bond.Transport

/-! Correspondence wrappers for embedding comparison and transport of configurations along
vertex bijections.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V W : Type*}

/-- An injection of a countable vertex set that dominates the off-diagonal edge
probabilities dominates the two-point function, the percolation probability and the
susceptibility. -/
@[tag "1H8U"]
theorem embedding_comparison [Countable V] (f : V ↪ W) {q : Sym2 V → unitInterval}
    {q' : Sym2 W → unitInterval}
    (hdom : ∀ e : Sym2 V, ¬ e.IsDiag → q e ≤ q' (Sym2.map f e)) :
    (∀ x y : V, tau q x y ≤ tau q' (f x) (f y)) ∧
    (∀ x : V, law q {ω | (cluster ω x).Infinite} ≤ law q' {ω | (cluster ω (f x)).Infinite}) ∧
    (∀ x : V, chi q x ≤ chi q' (f x)) :=
  ⟨tau_le_of_embedding f hdom, law_cluster_infinite_le_of_embedding f hdom,
    chi_le_of_embedding f hdom⟩

/-- Transport along a vertex bijection `σ`: connections, clusters, cluster volumes,
infinitude and escape events are carried along by `ω ↦ σ(ω)`, and when the laws correspond
so are the two-point function, the percolation probability and the susceptibility. -/
@[tag "ZE95"]
theorem transport_along_bijection (σ : V ≃ W) :
    (∀ (ω : Config V) (x y : V), Sym2.map σ '' ω ∈ conn (σ x) (σ y) ↔ ω ∈ conn x y) ∧
    (∀ (ω : Config V) (x : V), cluster (Sym2.map σ '' ω) (σ x) = σ '' cluster ω x) ∧
    (∀ (ω : Config V) (x : V),
      (cluster (Sym2.map σ '' ω) (σ x)).encard = (cluster ω x).encard) ∧
    (∀ (ω : Config V) (x : V),
      (cluster (Sym2.map σ '' ω) (σ x)).Infinite ↔ (cluster ω x).Infinite) ∧
    (∀ (x : V) (F : Set V),
      (fun ω : Config V => Sym2.map σ '' ω) ⁻¹' (⋃ y ∈ (σ '' F)ᶜ, conn (σ x) y) =
        ⋃ y ∈ Fᶜ, conn x y) ∧
    (∀ (q : Sym2 V → unitInterval) (q' : Sym2 W → unitInterval),
      (law q).map (fun ω => Sym2.map σ '' ω) = law q' →
      (∀ x y : V, tau q' (σ x) (σ y) = tau q x y) ∧
      (∀ x : V, law q' {ω | (cluster ω (σ x)).Infinite} =
        law q {ω | (cluster ω x).Infinite}) ∧
      (∀ x : V, chi q' (σ x) = chi q x)) :=
  ⟨image_mem_conn_iff σ, cluster_image σ, encard_cluster_image σ,
    cluster_image_infinite_iff σ, preimage_escape_image σ,
    fun _ _ h => ⟨tau_eq_of_map_law σ h, law_cluster_infinite_eq_of_map_law σ h,
      chi_eq_of_map_law σ h⟩⟩

end PercLib.Percolation.Bond
