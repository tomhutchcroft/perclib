/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the one-dimensional finite-cluster assertion.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.OneDimensional

/-!
# One-dimensional finite clusters: correspondence

Wiki correspondence for finiteness of clusters of one-dimensional long-range percolation with finite
first moment.

## Main results

* `oneDimensional_clusters_finite_criticalIntensity_eq_top`
-/

@[expose] public section
noncomputable section
open MeasureTheory PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- On `ℤ`, for a symmetric translation-invariant kernel `K s(a,b) = J |b-a|` with
`∑ r J(r) < ∞`, at every finite intensity every cluster is almost surely finite, and both the
root and the global critical intensities are infinite. -/
@[tag "JK7V"]
theorem oneDimensional_clusters_finite_criticalIntensity_eq_top (J : ℕ → ℝ≥0)
    (K : Sym2 ℤ → ℝ≥0)
    (hK : ∀ a b, K s(a, b) = J (Int.natAbs (b - a)))
    (hJ : Summable fun r : ℕ => (r : ℝ) * (J r : ℝ)) :
    (∀ β : ℝ≥0, ∀ᵐ ω ∂law (intensityProfile K β), ∀ x, (cluster ω x).Finite) ∧
    (∀ x, rootCriticalIntensity K x = ⊤) ∧ globalCriticalIntensity K = ⊤ :=
  ⟨ae_cluster_finite_of_summable J K hK hJ, rootCriticalIntensity_eq_top_of_summable J K hK hJ,
    globalCriticalIntensity_eq_top_of_summable J K hK hJ⟩

end PercLib.Models.LongRange
