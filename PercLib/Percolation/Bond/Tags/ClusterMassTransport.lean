/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the cluster applications of mass transport on a countable group.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClusterMassTransport

/-!
# Mass transport inside clusters: correspondence

## Main results

* `lintegral_cluster_finite_average_and_measure_selection`
* `ae_notMem_cluster_infinite_and_not_exists_selection`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-- Finite-cluster averaging under an invariant graph-and-mark law: for an equivariant
measurable `f`, `E[f(ω, 1); |K_1| < ∞] = E[|K_1|⁻¹ ∑_{x ∈ K_1} f(ω, x); |K_1| < ∞]`; and an
equivariant measurable rule selecting exactly one vertex of each finite cluster and none of an
infinite cluster selects `1` with probability `E[|K_1|⁻¹; |K_1| < ∞]`. -/
@[tag "4SZ9"]
theorem lintegral_cluster_finite_average_and_measure_selection {Γ Ω : Type*} [Group Γ]
    [Countable Γ] [MeasurableSpace Ω] {μ : Measure Ω}
    (act : Γ → Ω → Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (G : Ω → Config Γ) (hG : Measurable G)
    (hGact : ∀ g ω, G (act g ω) = Sym2.map (g * ·) '' G ω) :
    (∀ f : Ω → Γ → ℝ≥0∞, (∀ x, Measurable fun ω => f ω x) →
      (∀ g ω x, f (act g ω) (g * x) = f ω x) →
      ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator (fun ω => f ω 1) ω ∂μ =
        ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator
          (fun ω => ((cluster (G ω) 1).encard : ℝ≥0∞)⁻¹ *
            ∑' x, (cluster (G ω) 1).indicator (f ω) x) ω ∂μ) ∧
    (∀ S : Ω → Set Γ, (∀ x, MeasurableSet {ω | x ∈ S ω}) →
      (∀ g ω x, g * x ∈ S (act g ω) ↔ x ∈ S ω) →
      (∀ ω x, (cluster (G ω) x).Finite → ∃! y, y ∈ cluster (G ω) x ∧ y ∈ S ω) →
      (∀ ω x, (cluster (G ω) x).Infinite → x ∉ S ω) →
      μ {ω | (1 : Γ) ∈ S ω} = ∫⁻ ω, {ω | (cluster (G ω) 1).Finite}.indicator
        (fun ω => ((cluster (G ω) 1).encard : ℝ≥0∞)⁻¹) ω ∂μ) :=
  ⟨fun f hf hfact =>
      lintegral_indicator_cluster_finite_eq_average act hact G hG hGact f hf hfact,
    fun S hS hSact hS_fin hS_inf =>
      measure_mem_selection_eq_lintegral_inv_encard act hact G hG hGact S hS hSact hS_fin
        hS_inf⟩

/-- Under an invariant graph-and-mark law (any finite invariant measure), an equivariant
measurable set meeting each infinite cluster in at most one vertex almost surely contains no
vertex of an infinite cluster; consequently, if infinite clusters occur with positive
probability, no such rule selects exactly one vertex of each infinite cluster. -/
@[tag "O0TO"]
theorem ae_notMem_cluster_infinite_and_not_exists_selection {Γ Ω : Type*} [Group Γ]
    [Countable Γ] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (act : Γ → Ω → Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (G : Ω → Config Γ) (hG : Measurable G)
    (hGact : ∀ g ω, G (act g ω) = Sym2.map (g * ·) '' G ω) :
    (∀ R : Ω → Set Γ, (∀ x, MeasurableSet {ω | x ∈ R ω}) →
      (∀ g ω x, g * x ∈ R (act g ω) ↔ x ∈ R ω) →
      (∀ ω x, (cluster (G ω) x).Infinite → (R ω ∩ cluster (G ω) x).Subsingleton) →
      ∀ᵐ ω ∂μ, ∀ x, (cluster (G ω) x).Infinite → x ∉ R ω) ∧
    (μ {ω | ∃ x, (cluster (G ω) x).Infinite} ≠ 0 →
      ¬ ∃ R : Ω → Set Γ, (∀ x, MeasurableSet {ω | x ∈ R ω}) ∧
        (∀ g ω x, g * x ∈ R (act g ω) ↔ x ∈ R ω) ∧
        ∀ ω x, (cluster (G ω) x).Infinite → ∃! y, y ∈ cluster (G ω) x ∧ y ∈ R ω) :=
  ⟨fun R hR hRact hR_inf =>
      ae_notMem_of_cluster_infinite act hact G hG hGact R hR hRact hR_inf,
    not_exists_selection_of_measure_cluster_infinite_ne_zero act hact G hG hGact⟩

end PercLib.Percolation.Bond
