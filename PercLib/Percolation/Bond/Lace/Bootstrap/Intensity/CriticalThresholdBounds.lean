/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original consequences of the proved nearest-neighbour bootstrap and existing
self-avoiding-path bounds. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.Criticality
public import PercLib.Percolation.Bond.SelfAvoiding

/-!
# Explicit bounds on the actual critical edge probability

## Main results

In dimension at least `50000`, the edge probability at the actual critical
intensity lies between `1/(2d-1)` and `1/(2d-88)`. The lower bound uses the
existing self-avoiding-path estimate and positive percolation above the actual
threshold. The upper bound passes the proved subcritical step-mass estimate
to the endpoint by continuity. Root and global intensity thresholds agree.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory PercLib.Models.Site
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond.Lace

/-- Transitivity identifies every rooted nearest-neighbour intensity threshold
with the global threshold, including dimension zero. -/
theorem rootCriticalIntensity_nearestNeighbor_eq_global (d : ℕ) (x : Fin d → ℤ) :
    rootCriticalIntensity (nearestNeighborIntensity d) x =
      globalCriticalIntensity (nearestNeighborIntensity d) :=
  rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive
    (nearestNeighborIntensity d) (nearestNeighborIntensity_transitive d) x

/-- The actual critical edge probability retains the elementary nonbacktracking
lower bound, using positive percolation just above the threshold. -/
theorem nearestNeighbor_critical_probability_ge_inv_degree_sub_one
    {d : ℕ} (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    1 / (2 * (d : ℝ) - 1) ≤ (nearestNeighborProbability d b : ℝ) := by
  classical
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let : (zdGraph d).LocallyFinite := fun x => (zdGraph_finite_neighborSet x).fintype
  have hcont : Continuous (fun β : ℝ≥0 => (nearestNeighborProbability d β : ℝ)) :=
    continuous_intensityProfile (fun _ : Sym2 Unit => (2 * (d : ℝ≥0))⁻¹) s((), ())
  have hclosure : b ∈ closure (Ioi b) := by
    rw [closure_Ioi]
    exact le_rfl
  apply ContinuousWithinAt.closure_le hclosure continuousWithinAt_const hcont.continuousWithinAt
  intro β hβ
  by_contra h
  have hp : (nearestNeighborProbability d β : ℝ) < 1 / (2 * (d : ℝ) - 1) :=
    lt_of_not_ge h
  have hzero := law_lattice_cluster_infinite_eq_zero_of_degree_bound d (by omega)
    (fun x => (zdGraph_degree d x).le)
    (homogeneousProfile (zdGraph d) (nearestNeighborProbability d β))
    (nearestNeighborProbability d β)
    (fun _ _ he => homogeneousProfile_of_notMem _ he)
    (fun _ he => (homogeneousProfile_of_mem _ he).le) hp 0
  rw [← intensityProfile_nearestNeighborIntensity] at hzero
  have hβ' : rootCriticalIntensity (nearestNeighborIntensity d) 0 < (β : ℝ≥0∞) := by
    have h := ENNReal.coe_lt_coe.mpr hβ
    simpa only [b, ENNReal.coe_toNNReal (rootCriticalIntensity_nearestNeighbor_ne_top hd)] using h
  exact (ne_of_gt (law_cluster_infinite_pos_of_rootCriticalIntensity_lt
    (nearestNeighborIntensity d) 0 hβ')) hzero

/-- The exact subcritical step-mass bound extends to the actual critical intensity. -/
theorem nearestNeighbor_critical_step_mass_le {d : ℕ} (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    2 * d * (nearestNeighborProbability d b : ℝ) ≤ (d : ℝ) / (d - 44) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  change 2 * d * (nearestNeighborProbability d b : ℝ) ≤ (d : ℝ) / (d - 44)
  by_cases hb : b = 0
  · simp only [hb, nearestNeighborProbability_zero]
    change 2 * (d : ℝ) * 0 ≤ d / (d - 44)
    rw [mul_zero]
    apply div_nonneg (by positivity)
    have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hbpos : (0 : ℝ≥0) < b := pos_iff_ne_zero.mpr hb
  have : NeBot (𝓝[<] b) := nhdsLT_neBot_of_exists_lt ⟨0, hbpos⟩
  have hprob : Continuous (fun β : ℝ≥0 => (nearestNeighborProbability d β : ℝ)) :=
    continuous_intensityProfile (fun _ : Sym2 Unit => (2 * (d : ℝ≥0))⁻¹) s((), ())
  have hlim : Tendsto (fun β : ℝ≥0 => 2 * d * (nearestNeighborProbability d β : ℝ))
      (𝓝[<] b) (𝓝 (2 * d * (nearestNeighborProbability d b : ℝ))) :=
    (hprob.const_mul (2 * (d : ℝ))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  exact eventually_nhdsWithin_of_forall fun β hβ =>
    step_mass_nearestNeighborIntensity_le_of_chi_ne_top hd β
      (chi_nearestNeighborIntensity_ne_top_below_critical hd β hβ)

/-- In particular, the actual critical mean open degree is at least one. -/
theorem one_le_nearestNeighbor_critical_step_mass {d : ℕ} (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    1 ≤ 2 * d * (nearestNeighborProbability d b : ℝ) := by
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hp := (div_le_iff₀ (by linarith : (0 : ℝ) < 2 * d - 1)).mp
    (nearestNeighbor_critical_probability_ge_inv_degree_sub_one hd)
  have hp0 := (nearestNeighborProbability d b).2.1
  nlinarith

/-- The critical edge probability has the explicit upper bound `1/(2d-88)`. -/
theorem nearestNeighbor_critical_probability_le {d : ℕ} (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (nearestNeighborProbability d b : ℝ) ≤ 1 / (2 * (d : ℝ) - 88) := by
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hs := (le_div_iff₀ (by linarith : (0 : ℝ) < d - 44)).mp
    (nearestNeighbor_critical_step_mass_le hd)
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * d - 88)).mpr
  apply (mul_le_mul_iff_right₀ (by linarith : (0 : ℝ) < d)).mp
  nlinarith

/-- Both explicit bounds concern the canonical edge probability at the actual
critical intensity, with no assumed weak bootstrap or finite critical susceptibility. -/
@[tag "LI2P"]
theorem nearestNeighbor_critical_probability_bounds {d : ℕ} (hd : 50000 ≤ d) :
    let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    1 / (2 * (d : ℝ) - 1) ≤ (nearestNeighborProbability d b : ℝ) ∧
      (nearestNeighborProbability d b : ℝ) ≤ 1 / (2 * (d : ℝ) - 88) :=
  ⟨nearestNeighbor_critical_probability_ge_inv_degree_sub_one hd,
    nearestNeighbor_critical_probability_le hd⟩

end PercLib.Percolation.Bond.Lace
