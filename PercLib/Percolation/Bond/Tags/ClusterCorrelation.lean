/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the cluster correlation gap. All mathematical inputs are proved in the
imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClusterCorrelation.Inequalities

/-!
# Cluster correlation gap: correspondence

Wiki correspondence for the support of the correlation gap of increasing cluster functionals.

## Main results

* `correlation_gap_on_common_cluster`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- The correlation gap of increasing cluster functionals is supported on the event
`x ↔ y`: the distinct-cluster expectation is at most the product of expectations
(extended values allowed), and when the expectations are finite the covariance lies
between zero and the common-cluster contribution. No finiteness of `K_x` is needed. -/
@[tag "1AC7"]
theorem correlation_gap_on_common_cluster [Countable V] (q : Sym2 V → unitInterval)
    (x y : V) (F G : Set V → ℝ≥0∞) (hF : Monotone F) (hG : Monotone G)
    (hFm : Measurable (fun ω : Config V => F (cluster ω x)))
    (hGm : Measurable (fun ω : Config V => G (cluster ω y))) :
    ∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q ≤
        (∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q ∧
    ((∫⁻ ω, F (cluster ω x) ∂law q) ≠ ⊤ → (∫⁻ ω, G (cluster ω y) ∂law q) ≠ ⊤ →
      (∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q) ≠ ⊤ →
      0 ≤ (∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q).toReal -
          ((∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q).toReal ∧
        (∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q).toReal -
          ((∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q).toReal ≤
        (∫⁻ ω, (conn x y).indicator
          (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q).toReal) := by
  refine ⟨disjointClusterBK q x y F G hF hG hFm hGm, fun hEF hEG hEFG => ?_⟩
  have hprod : (∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) ≠ ⊤ :=
    ENNReal.mul_ne_top hEF hEG
  have hI : (∫⁻ ω, (conn x y).indicator
      (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q) ≠ ⊤ :=
    ne_top_of_le_ne_top hEFG (lintegral_mono fun ω => indicator_le_self _ _ ω)
  have hH := clusterFunctionalHarris q x y F G hF hG hFm hGm
  have hU := clusterCovarianceUpper q x y F G hF hG hFm hGm
  constructor
  · exact sub_nonneg.mpr (ENNReal.toReal_mono hEFG hH)
  · have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hprod, hI⟩) hU
    rw [ENNReal.toReal_add hprod hI] at h
    linarith

end PercLib.Percolation.Bond
