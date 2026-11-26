/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for nearest-neighbour percolation on `ℤ` (forest-connections
article). All mathematical inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.Line

/-!
# Nearest-neighbour percolation on `ℤ`: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `line_nearestNeighbour`
* `line_unitKernel`
-/

@[expose] public section
noncomputable section
open MeasureTheory PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.Line

/-- On `ℤ` with nearest-neighbour parameter `p` (diagonal arbitrary):
`τ(a,b) = p^{|b-a|}` and `χ = (1+p)/(1-p)` (which is `∞` at `p = 1`); for `p < 1` all clusters
are a.s. finite and the root and global infinite-cluster probabilities are `0`; at `p = 1`
every root cluster is a.s. all of `ℤ`, `χ = ∞`, and both probabilities are `1`. -/
@[tag "BP7B"]
theorem line_nearestNeighbour (p : unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = if |b - a| = 1 then p else 0) :
    (∀ a b : ℤ, tau q a b = (unitInterval.toNNReal p : ℝ≥0∞) ^ (b - a).natAbs) ∧
    (∀ a : ℤ, chi q a = (1 + (unitInterval.toNNReal p : ℝ≥0∞)) /
      (1 - (unitInterval.toNNReal p : ℝ≥0∞))) ∧
    (p < 1 → (∀ᵐ ω ∂law q, ∀ a, (cluster ω a).Finite) ∧
      (∀ a, law q {ω | (cluster ω a).Infinite} = 0) ∧
      law q {ω | ∃ a, (cluster ω a).Infinite} = 0) ∧
    (p = 1 → (∀ a, ∀ᵐ ω ∂law q, cluster ω a = Set.univ) ∧ (∀ a, chi q a = ⊤) ∧
      (∀ a, law q {ω | (cluster ω a).Infinite} = 1) ∧
      law q {ω | ∃ a, (cluster ω a).Infinite} = 1) :=
  ⟨tau_eq_pow p q hq, chi_eq p q hq, fun hp => ⟨ae_all_clusters_finite p hp q hq,
    law_cluster_infinite_eq_zero p hp q hq, law_exists_infinite_eq_zero p hp q hq⟩,
    fun hp => by
      subst hp
      exact ⟨ae_cluster_eq_univ q hq, chi_eq_top q hq, law_cluster_infinite_eq_one q hq,
        law_exists_infinite_eq_one q hq⟩⟩

/-- For the unit nearest-neighbour kernel on `ℤ` (diagonal arbitrary), at every
finite `β`: `χ_β(a) = 2e^β - 1 < ∞`, a.s. there is no infinite cluster, and the root and
global critical intensities are `∞`. -/
@[tag "FH1B"]
theorem line_unitKernel (J : Sym2 ℤ → ℝ≥0)
    (hJ : ∀ a b, a ≠ b → J s(a, b) = if |b - a| = 1 then 1 else 0) :
    (∀ (β : ℝ≥0) (a : ℤ),
      chi (intensityProfile J β) a = ENNReal.ofReal (2 * Real.exp β - 1)) ∧
    (∀ β : ℝ≥0, law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0) ∧
    (∀ a, rootCriticalIntensity J a = ⊤) ∧ globalCriticalIntensity J = ⊤ :=
  ⟨chi_intensity_eq J hJ, law_exists_infinite_intensity_eq_zero J hJ,
    rootCriticalIntensity_eq_top J hJ, globalCriticalIntensity_eq_top J hJ⟩

end PercLib.Models.Line
