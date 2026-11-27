/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper, proved from `PercLib/Percolation/Bond/PlanarVolumeTail.lean`.
No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.PlanarVolumeTail

/-!
# Conditional planar volume tail: correspondence

Wiki correspondence for the volume-tail bound of a random nearest-neighbour bond subgraph
of `ℤ²` from arm and two-point bounds, from
`PercLib/Percolation/Bond/PlanarVolumeTail.lean`.

## Main results

* `volume_tail_le_and_exponent_le_of_arm_of_two_point`
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter PercLib.Models.Site
open scoped ENNReal Topology

namespace PercLib.Percolation.Bond

/-- Let `μ` be the law of a random subgraph of `ℤ²` whose open pairs are almost surely
nearest-neighbour bonds, with root cluster `K_0`, and let `‖·‖` be the sup-norm, so that
`∂Λ_r = {x : ‖x‖ = r}`. If `0 < η < 2` and, for finite constants `C₁, C₂`,
`P(0 ↔ ∂Λ_r) ≤ C₁ r^{-η/2}` for every integer `r ≥ 1` and `P(0 ↔ x) ≤ C₂ (1+‖x‖)^{-η}` for
every `x`, then `P(|K_0| ≥ n) ≤ C n^{-η/(4-η)}` for `n ≥ 1` and a finite `C`; and if the
positive volume-tail exponent `δ` exists (`log P(|K_0| ≥ n)/log n → -1/δ`), then
`δ ≤ (4-η)/η`. -/
@[tag "0RX3"]
theorem volume_tail_le_and_exponent_le_of_arm_of_two_point
    (μ : Measure (Config (Fin 2 → ℤ))) [IsProbabilityMeasure μ]
    (hnn : ∀ᵐ ω ∂μ, ω ⊆ (zdGraph 2).edgeSet) {η C₁ C₂ : ℝ} (hη0 : 0 < η) (hη2 : η < 2)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ∃ x : Fin 2 → ℤ, ‖x‖ = r ∧ ω ∈ conn 0 x} ≤
      ENNReal.ofReal (C₁ * (r : ℝ) ^ (-η / 2)))
    (h2 : ∀ x : Fin 2 → ℤ, μ (conn 0 x) ≤ ENNReal.ofReal (C₂ * (1 + ‖x‖) ^ (-η))) :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → μ {ω | (n : ℕ∞) ≤ (cluster ω 0).encard} ≤
      ENNReal.ofReal (C * (n : ℝ) ^ (-η / (4 - η)))) ∧
    (∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => Real.log (μ {ω | (n : ℕ∞) ≤ (cluster ω 0).encard}).toReal /
        Real.log n) atTop (𝓝 (-1 / δ)) → δ ≤ (4 - η) / η) :=
  ⟨measure_encard_cluster_ge_le_of_arm_of_two_point μ hnn hη0 hη2 h1 h2,
    fun _ hδ hlim => le_of_log_tail_exponent_of_arm_of_two_point μ hnn hη0 hη2 h1 h2 hδ hlim⟩

end PercLib.Percolation.Bond
