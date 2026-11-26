/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for window intersection moments, rooted and global critical
intensities, the endpoint of finite susceptibility, disjoint unions and host containment.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.WindowPartition
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Percolation.Bond.SusceptibilityEndpoint
public import PercLib.Percolation.Bond.DisjointUnion
public import PercLib.Percolation.Bond.Host

/-!
# Thresholds, window moments and symmetries: correspondence

Wiki correspondence for the window intersection moments of a finite set, the rooted and
global critical intensities, the endpoint of finite susceptibility in a transitive
intensity model, percolation on a disjoint union with null cross pairs, and host
containment.

## Main results

* `sum_clusterIntersection_eq_sum_sq_and_bounds`
* `globalCriticalIntensity_eq_iInf_root`
* `globalCriticalIntensity_eq_iInf_and_root_eq_on_components`
* `chi_intensity_right_open_and_diverges_at_sSup`
* `disjoint_union_observables`
* `law_host_containment_eq_one_iff`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

open Classical in
/-- For a finite nonempty window `Λ`, `∑_{x ∈ Λ} |K(x) ∩ Λ| = ∑_{D ∈ 𝒞_Λ} |D|²` and
`M_Λ² ≤ ∑_{x ∈ Λ} |K(x) ∩ Λ| ≤ M_Λ |Λ|`, where `𝒞_Λ` is the set of traces of the full open
clusters on `Λ`. -/
@[tag "RU6O"]
theorem sum_clusterIntersection_eq_sum_sq_and_bounds {V : Type*} (Λ : Finset V)
    (_hΛ : Λ.Nonempty) (ω : Config V) :
    ∑ x ∈ Λ, clusterIntersection Λ ω x =
        ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)), D.card ^ 2 ∧
      maxClusterIntersection Λ ω ^ 2 ≤ ∑ x ∈ Λ, clusterIntersection Λ ω x ∧
      ∑ x ∈ Λ, clusterIntersection Λ ω x ≤ maxClusterIntersection Λ ω * Λ.card :=
  ⟨sum_clusterIntersection_eq_sum_sq Λ ω, sq_maxClusterIntersection_le_sum Λ ω,
    sum_clusterIntersection_le Λ ω⟩

/-- On a countable vertex set the global critical intensity is the infimum of the rooted
critical intensities. -/
@[tag "JZN0"]
theorem globalCriticalIntensity_eq_iInf_root {V : Type*} [Countable V] (J : Sym2 V → ℝ≥0) :
    globalCriticalIntensity J = ⨅ x, rootCriticalIntensity J x :=
  globalCriticalIntensity_eq_iInf_rootCriticalIntensity J

/-- On a nonempty countable vertex set the global critical intensity is the infimum of the
rooted ones; the rooted critical intensity is constant on each component of the support
graph `J > 0`; if the support graph is connected, every rooted critical intensity equals
the global one. -/
@[tag "1C8G"]
theorem globalCriticalIntensity_eq_iInf_and_root_eq_on_components {V : Type*} [Countable V]
    (_ : Nonempty V) (J : Sym2 V → ℝ≥0) :
    globalCriticalIntensity J = ⨅ x, rootCriticalIntensity J x ∧
      (∀ x y : V, (SimpleGraph.fromEdgeSet {e | 0 < J e}).Reachable x y →
        rootCriticalIntensity J x = rootCriticalIntensity J y) ∧
      ((SimpleGraph.fromEdgeSet {e | 0 < J e}).Preconnected →
        ∀ x : V, rootCriticalIntensity J x = globalCriticalIntensity J) :=
  ⟨globalCriticalIntensity_eq_iInf_rootCriticalIntensity J,
    fun _ _ h => rootCriticalIntensity_eq_of_reachable J h,
    fun hJ x => rootCriticalIntensity_eq_globalCriticalIntensity J hJ x⟩

/-- In a transitive intensity model with off-diagonal row sum `0 < L < ∞`: if `χ_β < ∞` and
`ε < 1/(L χ_β)` then `χ_{β+ε} ≤ χ_β / (1 - ε L χ_β) < ∞`; the susceptibility threshold
`b_χ = sup {β | χ_β < ∞}` is at least `1/L`; and if `b_χ` is finite then `χ_{b_χ} = ∞` and
`χ_β → ∞` as `β ↑ b_χ`. -/
@[tag "5LNL"]
theorem chi_intensity_right_open_and_diverges_at_sSup {V : Type*} [Countable V]
    {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hR0 : 0 < rowSum (fun e => (J e : ℝ≥0∞)) o)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤) :
    (∀ β ε : ℝ≥0, chi (intensityProfile J β) o < ⊤ →
      (ε : ℝ≥0∞) < (rowSum (fun e => (J e : ℝ≥0∞)) o * chi (intensityProfile J β) o)⁻¹ →
      chi (intensityProfile J (β + ε)) o ≤ chi (intensityProfile J β) o /
          (1 - (ε : ℝ≥0∞) * rowSum (fun e => (J e : ℝ≥0∞)) o *
            chi (intensityProfile J β) o) ∧
        chi (intensityProfile J (β + ε)) o < ⊤) ∧
    (rowSum (fun e => (J e : ℝ≥0∞)) o)⁻¹ ≤
      sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) ∧
    (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) < ⊤ →
      chi (intensityProfile J
        (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤})).toNNReal)
        o = ⊤) ∧
    (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) < ⊤ →
      Tendsto (fun β : ℝ≥0 => chi (intensityProfile J β) o)
        (𝓝[<] (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) ''
          {β | chi (intensityProfile J β) o < ⊤})).toNNReal) (𝓝 ⊤)) :=
  ⟨fun _ _ hχ hε => ⟨chi_intensity_add_le hJ hL hχ hε, chi_intensity_add_lt_top hJ hL hχ hε⟩,
    inv_le_chiCriticalIntensity hJ hL, chi_intensity_sSup_eq_top hJ hL,
    tendsto_chi_intensity_nhdsLT_sSup hJ hR0 hL⟩

/-- On `V₁ ⊕ V₂` with countable parts and every cross pair of probability zero: almost
surely each cluster is the image of the cluster of the restricted configuration on its side;
the two-point function, percolation probability and susceptibility on each side are those of
the restricted profile; the cross two-point function vanishes; and the probability that some
cluster is infinite is `1 - (1 - Θ₁)(1 - Θ₂)`. -/
@[tag "WD2J"]
theorem disjoint_union_observables {V₁ V₂ : Type*} [Countable V₁] [Countable V₂]
    (q : Sym2 (V₁ ⊕ V₂) → unitInterval) (hq : ∀ a b, q s(Sum.inl a, Sum.inr b) = 0) :
    (∀ᵐ ω ∂law q,
      (∀ a, cluster ω (Sum.inl a) = Sum.inl '' cluster (Sym2.map Sum.inl ⁻¹' ω) a) ∧
      (∀ b, cluster ω (Sum.inr b) = Sum.inr '' cluster (Sym2.map Sum.inr ⁻¹' ω) b)) ∧
    (∀ a b : V₁, tau q (Sum.inl a) (Sum.inl b) = tau (fun e => q (Sym2.map Sum.inl e)) a b) ∧
    (∀ a b : V₂, tau q (Sum.inr a) (Sum.inr b) = tau (fun e => q (Sym2.map Sum.inr e)) a b) ∧
    (∀ a : V₁, law q {ω | (cluster ω (Sum.inl a)).Infinite} =
      law (fun e => q (Sym2.map Sum.inl e)) {ω | (cluster ω a).Infinite}) ∧
    (∀ b : V₂, law q {ω | (cluster ω (Sum.inr b)).Infinite} =
      law (fun e => q (Sym2.map Sum.inr e)) {ω | (cluster ω b).Infinite}) ∧
    (∀ a : V₁, chi q (Sum.inl a) = chi (fun e => q (Sym2.map Sum.inl e)) a) ∧
    (∀ b : V₂, chi q (Sum.inr b) = chi (fun e => q (Sym2.map Sum.inr e)) b) ∧
    (∀ (a : V₁) (b : V₂), tau q (Sum.inl a) (Sum.inr b) = 0) ∧
    law q {ω | ∃ x, (cluster ω x).Infinite} =
      1 - (1 - law (fun e => q (Sym2.map Sum.inl e)) {ω | ∃ x, (cluster ω x).Infinite}) *
        (1 - law (fun e => q (Sym2.map Sum.inr e)) {ω | ∃ x, (cluster ω x).Infinite}) :=
  ⟨ae_cluster_inl_eq_and_cluster_inr_eq q hq, tau_inl_inl q hq, tau_inr_inr q hq,
    law_cluster_inl_infinite q hq, law_cluster_inr_infinite q hq, chi_inl q hq, chi_inr q hq,
    tau_inl_inr q hq, law_exists_cluster_infinite_sum q hq⟩

/-- On a countable vertex set and a simple host graph `G`: the configuration lies in the
host edge set with probability one exactly when every pair outside it, diagonal pairs
included, has probability zero; the open graph is a subgraph of `G` with probability one
exactly when every non-diagonal pair outside `G` has probability zero. -/
@[tag "H48I"]
theorem law_host_containment_eq_one_iff {V : Type*} [Countable V] (G : SimpleGraph V)
    (q : Sym2 V → unitInterval) :
    (law q {ω | ω ⊆ G.edgeSet} = 1 ↔ ∀ e ∉ G.edgeSet, q e = 0) ∧
    (law q {ω | openGraph ω ≤ G} = 1 ↔ ∀ x y, x ≠ y → ¬ G.Adj x y → q s(x, y) = 0) :=
  ⟨law_config_subset_host_eq_one_iff G q, law_openGraph_le_host_eq_one_iff G q⟩

end PercLib.Percolation.Bond
