/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.Subcritical
public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.EndpointDiagrams

/-!
# Actual nearest-neighbour diagrams at criticality

## Main results

The actual continuation diagrams retain their dimension-dependent bounds at the
usual critical intensity. Nonnegative partial-sum limits require no finite
critical susceptibility. The origin bound retains its smaller constant.
-/

@[expose] public section
noncomputable section

open Set Filter DiscreteConvolution
open scoped ENNReal NNReal Topology DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

private theorem critical_continuation_bound {d : ℕ} (hd : 50000 ≤ d)
    (x : Fin d → ℤ) (C : ℝ≥0∞)
    (hbound : ∀ β : ℝ≥0,
      chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤ →
      let q := intensityProfile (nearestNeighborIntensity d) β
      (offDiagonal (fun u v : Fin d → ℤ =>
        (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ C) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (offDiagonal (fun u v : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ C := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have hbfinite := rootCriticalIntensity_nearestNeighbor_ne_top hd
  have hbone : (1 : ℝ≥0) ≤ b := by
    apply ENNReal.coe_le_coe.mp
    simpa only [b, ENNReal.coe_one, ENNReal.coe_toNNReal hbfinite] using
      one_le_rootCriticalIntensity_nearestNeighbor d
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le (by norm_num) hbone
  have hclosure : b ∈ closure (Ioo 0 b) := by
    rw [closure_Ioo hb.ne]
    exact ⟨hb.le, le_rfl⟩
  obtain ⟨β, hβ, hlim⟩ := mem_closure_iff_seq_limit.mp hclosure
  apply step_tau_three_intensity_endpoint_le (nearestNeighborIntensity d) β b
    (fun n => (hβ n).2.le) hlim x C
  intro n
  apply hbound
  apply (chi_lt_top_of_lt_rootCriticalIntensity (nearestNeighborIntensity d)
    (nearestNeighborIntensity_transitive d) (summable_nearestNeighborIntensity d) ?_).ne
  have hlt : (β n : ℝ≥0∞) < (b : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr (hβ n).2
  simpa only [b, ENNReal.coe_toNNReal hbfinite] using hlt

/-- The actual critical continuation diagram has a uniform explicit bound. -/
theorem nn_critical_step_tau_three_le {d : ℕ} (hd : 50000 ≤ d) (x : Fin d → ℤ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (offDiagonal (fun u v : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤
      ENNReal.ofReal (9197 / (315 * (d : ℝ))) := by
  apply critical_continuation_bound hd x
  intro β hchi
  have hw := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi).trans
    (by norm_num : (17 : ℝ) / 10 ≤ 2)
  rw [intensityProfile_nearestNeighborIntensity] at hchi hw ⊢
  exact nn_step_tau_three_le (by omega) _ hchi
    (nn_step_mass_le_of_fourierBootstrap_le _ hw) ((fourierBootstrap_le_iff _ _).mp hw).2.1 x

/-- At the origin the critical continuation bound saves the direct-step term. -/
theorem nn_critical_step_tau_three_zero_le {d : ℕ} (hd : 50000 ≤ d) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (offDiagonal (fun u v : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0 ≤
      ENNReal.ofReal (8882 / (315 * (d : ℝ))) := by
  apply critical_continuation_bound hd 0
  intro β hchi
  have hw := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi).trans
    (by norm_num : (17 : ℝ) / 10 ≤ 2)
  rw [intensityProfile_nearestNeighborIntensity] at hchi hw ⊢
  exact nn_step_tau_three_zero_le (by omega) _ hchi
    (nn_step_mass_le_of_fourierBootstrap_le _ hw) ((fourierBootstrap_le_iff _ _).mp hw).2.1

/-- The actual critical triangle obeys the same explicit dimension-dependent cap. -/
theorem nn_critical_triangle_le {d : ℕ} (hd : 50000 ≤ d) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤
      ENNReal.ofReal (1 + 4441 / (105 * (d : ℝ))) := by
  let q := intensityProfile (nearestNeighborIntensity d)
    (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have hq : ∀ x y g : Fin d → ℤ, q s(x + g, y + g) = q s(x, y) := by
    dsimp only [q]
    rw [intensityProfile_nearestNeighborIntensity]
    exact homogeneous_zdGraph_add _
  refine (triangle_le_one_add_three_halves_step_tau_three q hq).trans ?_
  refine (add_le_add le_rfl (mul_le_mul' le_rfl
    (nn_critical_step_tau_three_zero_le hd))).trans_eq ?_
  have hc : (3 / 2 : ℝ≥0∞) = ENNReal.ofReal (3 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  ring

end PercLib.Percolation.Bond.Lace
