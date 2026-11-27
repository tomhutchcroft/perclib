/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.Subcritical
public import PercLib.Percolation.Bond.Lace.Bootstrap.SusceptibilityTriangleBound
public import PercLib.Probability.Exploration.EndpointTail

/-!
# Critical nonpercolation for nearest-neighbour percolation

## Main results

At dimension at least `50000`, the actual subcritical bootstrap and boundary
susceptibility inequality give an inverse-gap susceptibility bound. Its constants
retain the dimension-dependent triangle bound `D = 1 + 4441 / (105 * d)` and
the actual finite critical intensity `b`: the numerator is
`max (D * b) (3 * b² * D²)`.

The proved exploration comparison then gives zero probability of an infinite
cluster at the critical intensity. Countability makes all root clusters finite
simultaneously almost surely. No finite critical susceptibility, uniqueness
theorem, or unproved differential inequality is assumed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set PercLib.Models.Site
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.Lace

/-- Susceptibility is finite below the actual nearest-neighbour critical intensity,
with its extended-real endpoint converted only after finiteness is proved. -/
theorem chi_nearestNeighborIntensity_ne_top_below_critical
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0)
    (hβ : β < (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal) :
    chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤ := by
  apply (chi_lt_top_of_lt_rootCriticalIntensity (nearestNeighborIntensity d)
    (nearestNeighborIntensity_transitive d) (summable_nearestNeighborIntensity d) ?_).ne
  have h := ENNReal.coe_lt_coe.mpr hβ
  rwa [ENNReal.coe_toNNReal (rootCriticalIntensity_nearestNeighbor_ne_top hd)] at h

private theorem triangle_nearestNeighborIntensity_le_of_finite_chi
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0)
    (hchi : chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤) :
    (∑' u, ∑' v, tau (intensityProfile (nearestNeighborIntensity d) β) 0 u *
      tau (intensityProfile (nearestNeighborIntensity d) β) u v *
      tau (intensityProfile (nearestNeighborIntensity d) β) v 0) ≤
        ENNReal.ofReal (1 + 4441 / (105 * (d : ℝ))) := by
  have hw := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi).trans
    (by norm_num : (17 : ℝ) / 10 ≤ 2)
  rw [intensityProfile_nearestNeighborIntensity] at hchi hw ⊢
  exact nn_triangle_le (by omega) (nearestNeighborProbability d β) hchi
    (nn_step_mass_le_of_fourierBootstrap_le _ hw)
    ((fourierBootstrap_le_iff _ _).mp hw).2.1

/-- The actual susceptibility below the nearest-neighbour critical intensity
has an inverse-gap bound with its exact dimension-dependent triangle constant.
The critical endpoint is excluded from the susceptibility hypotheses. -/
theorem chi_nearestNeighborIntensity_toReal_le_div_critical_gap
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0) (hβpos : 0 < β)
    (hβ : β < (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal) :
    let b : ℝ := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let D : ℝ := 1 + 4441 / (105 * (d : ℝ))
    (chi (intensityProfile (nearestNeighborIntensity d) β) 0).toReal ≤
      max (D * b) (3 * b ^ 2 * D ^ 2) / (b - β) := by
  let b : ℝ≥0 := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let D : ℝ := 1 + 4441 / (105 * (d : ℝ))
  have hfin (t : ℝ) (ht : t ∈ Ioo 0 (b : ℝ)) :
      chi (intensityProfile (nearestNeighborIntensity d) t.toNNReal) 0 ≠ ⊤ :=
    chi_nearestNeighborIntensity_ne_top_below_critical hd t.toNNReal
      ((Real.toNNReal_lt_iff_lt_coe ht.1.le).mpr ht.2)
  have htriangle (t : ℝ) (ht : t ∈ Ioo 0 (b : ℝ)) :
      (∑' u, ∑' v, tau (intensityProfile (nearestNeighborIntensity d) t.toNNReal) 0 u *
        tau (intensityProfile (nearestNeighborIntensity d) t.toNNReal) u v *
        tau (intensityProfile (nearestNeighborIntensity d) t.toNNReal) v 0) ≤
          ENNReal.ofReal D :=
    triangle_nearestNeighborIntensity_le_of_finite_chi hd t.toNNReal (hfin t ht)
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_right (by positivity)
  have h := chi_le_triangle_cap_div_gap (nearestNeighborIntensity d)
    (nearestNeighborIntensity_add d) (rowSum_nearestNeighborIntensity_le_one d)
    (a := 0) (b := (b : ℝ)) le_rfl hfin D hD htriangle
    (β := (β : ℝ)) ⟨NNReal.coe_pos.mpr hβpos, NNReal.coe_lt_coe.mpr hβ⟩
  simpa only [Real.toNNReal_coe] using h

/-- The inverse-gap estimate is an actual extended susceptibility bound at every
root, with the same finite constant and no endpoint-finiteness premise. -/
theorem chi_nearestNeighborIntensity_le_div_critical_gap
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0) (hβpos : 0 < β)
    (hβ : β < (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal)
    (x : Fin d → ℤ) :
    let b : ℝ := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    let D : ℝ := 1 + 4441 / (105 * (d : ℝ))
    chi (intensityProfile (nearestNeighborIntensity d) β) x ≤
      ENNReal.ofReal (max (D * b) (3 * b ^ 2 * D ^ 2) / (b - β)) := by
  dsimp only
  rw [chi_eq_of_transitive (nearestNeighborIntensity d)
    (nearestNeighborIntensity_transitive d) β x 0]
  have hgap : 0 <
      ((rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal : ℝ) - β :=
    sub_pos.mpr (NNReal.coe_lt_coe.mpr hβ)
  apply (ENNReal.le_ofReal_iff_toReal_le
    (chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ) (by positivity)).mpr
  exact chi_nearestNeighborIntensity_toReal_le_div_critical_gap hd β hβpos hβ

/-- At the actual nearest-neighbour critical intensity, an infinite cluster has
probability zero at every root. The entropy comparison uses finite susceptibility
only at smaller intensities. -/
theorem law_infinite_cluster_nearestNeighbor_critical_eq_zero
    {d : ℕ} (hd : 50000 ≤ d) (x : Fin d → ℤ) :
    law (intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal)
        {ω | (cluster ω x).Infinite} = 0 := by
  let b : ℝ≥0 := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let D : ℝ := 1 + 4441 / (105 * (d : ℝ))
  let C : ℝ≥0 := ⟨max (D * b) (3 * (b : ℝ) ^ 2 * D ^ 2), by positivity⟩
  have hb : 0 < b := ENNReal.toNNReal_pos
    (ne_of_gt (zero_lt_one.trans_le (one_le_rootCriticalIntensity_nearestNeighbor d)))
    (rootCriticalIntensity_nearestNeighbor_ne_top hd)
  refine law_infinite_cluster_intensity_eq_zero_of_chi_le_on_Ioo x
    (nearestNeighborIntensity d) (a := 0) (b := b) hb 1 C
    (rowSum_nearestNeighborIntensity_le_one d) ?_
  intro β hβ
  exact chi_nearestNeighborIntensity_le_div_critical_gap hd β hβ.1 hβ.2 x

/-- Every fixed root has an almost surely finite cluster at the actual critical
intensity, despite the infinite critical susceptibility. -/
theorem ae_finite_cluster_nearestNeighbor_critical
    {d : ℕ} (hd : 50000 ≤ d) (x : Fin d → ℤ) :
    ∀ᵐ ω ∂law (intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal),
        (cluster ω x).Finite := by
  rw [ae_iff]
  exact law_infinite_cluster_nearestNeighbor_critical_eq_zero hd x

/-- Countability gives simultaneous finiteness of all nearest-neighbour critical
clusters on one probability-one event. -/
theorem ae_forall_finite_cluster_nearestNeighbor_critical
    {d : ℕ} (hd : 50000 ≤ d) :
    ∀ᵐ ω ∂law (intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal),
        ∀ x : Fin d → ℤ, (cluster ω x).Finite :=
  ae_all_iff.mpr (ae_finite_cluster_nearestNeighbor_critical hd)

end PercLib.Percolation.Bond.Lace
