/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for examples in the infinite-cluster-zero-one and criticality
articles: the decorated ray, the unattained threshold and finite vertex sets.
Every statement is assembled from lemmas proved in the imported modules; no new
definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.DecoratedRay
public import PercLib.Models.UnattainedThreshold
public import PercLib.Models.ZeroOneExamples

/-!
# Zero-one examples and finite vertex sets: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `exists_decoratedRay_sInf`
* `exists_unattainedThreshold`
* `finite_vertexSet_thresholds`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-- There is a connected host graph on a countable set, of maximum degree at most
three, with finite nonnegative intensities supported on its edges, such that every cluster is
a.s. finite at every finite `β`, while `E_β|K_o| < ∞ ↔ β < log 2`; all rooted and global
thresholds are `∞`, and the infimum of the parameters with infinite root susceptibility is
`log 2`. -/
@[tag "SA9P"]
theorem exists_decoratedRay_sInf :
    ∃ (G : SimpleGraph (ℕ × ℕ)) (J : Sym2 (ℕ × ℕ) → ℝ≥0) (o : ℕ × ℕ),
      G.Connected ∧ (∀ v, (G.neighborSet v).encard ≤ 3) ∧
      (∀ e, J e ≠ 0 → e ∈ G.edgeSet) ∧
      (∀ β : ℝ≥0, ∀ᵐ ω ∂law (intensityProfile J β), ∀ x, (cluster ω x).Finite) ∧
      (∀ x, rootCriticalIntensity J x = ⊤) ∧ globalCriticalIntensity J = ⊤ ∧
      (∀ β : ℝ≥0, chi (intensityProfile J β) o < ⊤ ↔ (β : ℝ) < Real.log 2) ∧
      ((sInf {β : ℝ≥0 | chi (intensityProfile J β) o = ⊤} : ℝ≥0) : ℝ) = Real.log 2 := by
  obtain ⟨G, J, o, h1, h2, h3, h4, h5, h6, h7⟩ := DecoratedRay.exists_decoratedRay
  exact ⟨G, J, o, h1, h2, h3, h4, h5, h6, h7,
    DecoratedRay.sInf_setOf_chi_eq_top_eq J o (Real.log_nonneg one_le_two) h7⟩

/-- There is a countable independent-bond intensity model with global threshold
`1` and every rooted threshold strictly greater than `1`. -/
@[tag "AHY3"]
theorem exists_unattainedThreshold :
    ∃ J : Sym2 (ℕ × List (Fin 2)) → ℝ≥0,
      globalCriticalIntensity J = 1 ∧ ∀ v, 1 < rootCriticalIntensity J v :=
  exists_globalCriticalIntensity_eq_one_lt_rootCriticalIntensity

/-- On a finite vertex set every cluster is finite in every configuration, and for
every kernel the root and global critical intensities are `∞`. -/
@[tag "KB1L"]
theorem finite_vertexSet_thresholds (V : Type*) [Finite V] :
    (∀ (ω : Config V) (v : V), (cluster ω v).Finite) ∧
    (∀ (J : Sym2 V → ℝ≥0) (x : V), rootCriticalIntensity J x = ⊤) ∧
    (∀ J : Sym2 V → ℝ≥0, globalCriticalIntensity J = ⊤) :=
  ⟨ZeroOneExamples.cluster_finite, ZeroOneExamples.rootCriticalIntensity_eq_top_of_finite,
    ZeroOneExamples.globalCriticalIntensity_eq_top_of_finite⟩

end PercLib.Models
