/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for convex order under weak limits. All mathematical inputs come from
the imported modules; no source proof is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.ConvexOrder

/-!
# Convex order under weak limits: correspondence

Wiki correspondence for the preservation of convex order under weak limits with uniform
integrability, and the identification of the limit laws by a vanishing second-moment gap.
Random variables enter through their laws on `ℝ`, so the two sequences need not live on a
common probability space.

## Main results

* `convexOrder_and_eq_of_tendsto_of_unifIntegrableAlong`
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PercLib.Probability

/-- Let `μs n ≤cx νs n` be laws on `ℝ` in convex order with `μs n → μ` and `νs n → ν` weakly.
If the first moments are uniformly integrable along `νs`, then they are uniformly integrable
along `μs`, `μ` and `ν` have first moments with equal means, and `μ ≤cx ν`. If moreover the
squares are uniformly integrable along `νs` and `∫ x² dνs n - ∫ x² dμs n → 0`, then the squares
are uniformly integrable along `μs` and `μ = ν`. -/
@[tag "MDB8"]
theorem convexOrder_and_eq_of_tendsto_of_unifIntegrableAlong
    {μs νs : ℕ → ProbabilityMeasure ℝ} {μ ν : ProbabilityMeasure ℝ}
    (hcx : ∀ n, ConvexOrder (μs n) (νs n)) (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν))
    (hUI : UnifIntegrableAlong (fun x => x) fun n => (νs n : Measure ℝ)) :
    UnifIntegrableAlong (fun x => x) (fun n => (μs n : Measure ℝ)) ∧
      Integrable (fun x => x) (μ : Measure ℝ) ∧ Integrable (fun x => x) (ν : Measure ℝ) ∧
      ∫ x, x ∂(μ : Measure ℝ) = ∫ x, x ∂(ν : Measure ℝ) ∧ ConvexOrder μ ν ∧
      (UnifIntegrableAlong (fun x => x ^ 2) (fun n => (νs n : Measure ℝ)) →
        Tendsto (fun n => ∫ x, x ^ 2 ∂(νs n : Measure ℝ) - ∫ x, x ^ 2 ∂(μs n : Measure ℝ))
          atTop (𝓝 0) →
        UnifIntegrableAlong (fun x => x ^ 2) (fun n => (μs n : Measure ℝ)) ∧ μ = ν) := by
  have hUIμ : UnifIntegrableAlong (fun x => x) fun n => (μs n : Measure ℝ) :=
    ConvexOrder.unifIntegrableAlong hcx measurable_id' convexOn_abs_id hUI
  exact ⟨hUIμ, integrable_of_tendsto_of_unifIntegrableAlong hμ continuous_id' hUIμ,
    integrable_of_tendsto_of_unifIntegrableAlong hν continuous_id' hUI,
    ConvexOrder.integral_id_eq_of_tendsto hcx hμ hν hUI, ConvexOrder.of_tendsto hcx hμ hν hUI,
    fun hUI2 hgap => ConvexOrder.eq_of_tendsto_of_tendsto_sub hcx hμ hν hUI hUI2 hgap⟩

end PercLib.Probability
